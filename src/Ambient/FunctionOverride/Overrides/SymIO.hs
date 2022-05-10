{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

-- | This contains cargo-culted versions of functions from @crucible-llvm@'s
-- "Lang.Crucible.LLVM.SymIO" module (licensed under the 3-Clause BSD license)
-- that have been tweaked to work with the verifier's memory model.
module Ambient.FunctionOverride.Overrides.SymIO
  ( callOpenFile
  ) where

import           Control.Monad.IO.Class ( liftIO )
import qualified Data.BitVector.Sized as BVS
import qualified Data.ByteString as BS
import qualified Data.Map.Strict as Map

import qualified Data.Macaw.CFG as DMC
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.SymIO as LCLS
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.SymIO as LCSym
import qualified Lang.Crucible.Types as LCT
import qualified What4.Expr as WE
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO

import qualified Ambient.Extensions as AExt
import qualified Ambient.Memory as AM

-- | This is identical to @crucible-llvm@'s 'LCLS.callOpenFile' function,
-- except that its internals use the verifier's 'AExt.loadString' function
-- instead of @crucible-llvm@'s own 'LCLM.loadString' function.
callOpenFile ::
  ( LCB.IsSymBackend sym bak
  , LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , ?memOpts :: LCLM.MemOptions
  , sym ~ WE.ExprBuilder scope st fs
  , bak ~ LCBO.OnlineBackend solver scope st fs
  , p ~ AExt.AmbientSimulatorState sym arch
  , DMC.MemWidth w
  , w ~ DMC.ArchAddrWidth arch
  , WPO.OnlineSolver solver
  ) =>
  bak ->
  AM.InitialMemory sym w ->
  -- ^ Initial memory state for symbolic execution
  Map.Map (DMC.MemWord w) String ->
  -- ^ Mapping from unsupported relocation addresses to the names of the
  -- unsupported relocation types.
  LCLS.LLVMFileSystem w ->
  LCS.RegEntry sym (LCLM.LLVMPointerType w) ->
  LCS.RegEntry sym (LCT.BVType 32) ->
  LCS.OverrideSim p sym ext rtp args ret (LCS.RegValue sym (LCT.BVType 32))
callOpenFile bak initialMem unsupportedRelocs fsVars filename_ptr _flags =
  do fileIdent <- loadFileIdent bak initialMem unsupportedRelocs filename_ptr
     LCSym.openFile (LCLS.llvmFileSystem fsVars) fileIdent $ \case
       Left LCSym.FileNotFound -> returnIOError32
       Right fileHandle -> LCLS.allocateFileDescriptor fsVars fileHandle

-- | This is identical to @crucible-llvm@'s @loadFileIdent@ function,
-- except that it uses the verifier's 'AExt.loadString' function instead of
-- @crucible-llvm@'s own 'LCLM.loadString' function.
loadFileIdent ::
  ( LCB.IsSymBackend sym bak
  , LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , ?memOpts :: LCLM.MemOptions
  , sym ~ WE.ExprBuilder scope st fs
  , bak ~ LCBO.OnlineBackend solver scope st fs
  , p ~ AExt.AmbientSimulatorState sym arch
  , DMC.MemWidth w
  , w ~ DMC.ArchAddrWidth arch
  , WPO.OnlineSolver solver
  ) =>
  bak ->
  AM.InitialMemory sym w ->
  -- ^ Initial memory state for symbolic execution
  Map.Map (DMC.MemWord w) String ->
  -- ^ Mapping from unsupported relocation addresses to the names of the
  -- unsupported relocation types.
  LCS.RegEntry sym (LCLM.LLVMPointerType w) ->
  LCS.OverrideSim p sym ext r args ret (LCSym.FileIdent sym)
loadFileIdent bak initialMem unsupportedRelocs filename_ptr =
  do let mvar = AM.imMemVar initialMem
     mem <- LCS.readGlobal mvar
     filename_bytes <- AExt.loadString bak mem initialMem unsupportedRelocs filename_ptr Nothing
     liftIO $ WI.stringLit (LCB.backendGetSym bak) (WI.Char8Literal (BS.pack filename_bytes))

-- | This is taken directly from @crucible-llvm@ with no changes. (We could
-- reexport it from "Lang.Crucible.LLVM.SymIO", but its implementation is so
-- small that it's probably not worth the bother.)
returnIOError32 ::
  LCB.IsSymInterface sym =>
  LCS.OverrideSim p sym ext r args ret (WI.SymBV sym 32)
returnIOError32 = do
  sym <- LCS.getSymInterface
  liftIO $ WI.bvLit sym (WI.knownNat @32) (BVS.mkBV (WI.knownNat @32) (-1))
