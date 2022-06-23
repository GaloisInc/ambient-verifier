{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Ambient.FunctionOverride.Overrides.ForwardDeclarations
  ( mkForwardDeclarationOverride
  ) where

import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( MonadIO(liftIO) )
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as PC

import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified What4.Expr as WE
import qualified What4.FunctionName as WF
import qualified What4.Protocol.Online as WPO

import qualified Ambient.Exception as AE
import qualified Ambient.FunctionOverride as AF
import qualified Ambient.FunctionOverride.ArgumentMapping as AFA
import qualified Ambient.Override as AO

-- | Construct an 'LCS.Override' to use when a forward declaration is invoked
-- from a syntax override. See @Note [Resolving forward declarations]@.
mkForwardDeclarationOverride ::
  forall sym bak arch p ext args ret solver scope st fs.
  ( LCB.IsSymBackend sym bak
  , sym ~ WE.ExprBuilder scope st fs
  , bak ~ LCBO.OnlineBackend solver scope st fs
  , ext ~ DMS.MacawExt arch
  , WPO.OnlineSolver solver
  ) =>
  bak ->
  Map.Map WF.FunctionName (AF.SomeFunctionOverride p sym ext) ->
  -- ^ Map of syntax overrides and built-in overrides
  WF.FunctionName ->
  -- ^ The name of the forward declaration
  LCF.FnHandle args ret ->
  -- ^ The forward declaration's handle
  IO (LCS.Override p sym ext args ret)
mkForwardDeclarationOverride bak fnNameMapping fwdDecName fwdDecHandle = do
  -- First, make sure that there is an override with the same name as the
  -- forward declaration.
  case Map.lookup fwdDecName fnNameMapping of
    -- If there is such a function, construct an override that pipe-fits the
    -- arguments of the forward declaration to the arguments of the override.
    -- We will mark which steps of Note [Resolving forward declarations] each
    -- part corresponds to.
    Just (AF.SomeFunctionOverride resolvedFnOv) ->
      let ovSim ::
            forall r.
            LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym ret)
          ovSim = do
            args0 <- LCS.getOverrideArgs
            -- Step (1)
            args1 <- liftIO $ AFA.buildForwardDecOverrideArgs bak $ LCS.regMap args0
            -- Step (2)
            args2 <- liftIO $ extendToRegisterAssignment (AF.functionArgTypes resolvedFnOv) args1
            -- Step (3)
            resValue <- AF.functionOverride resolvedFnOv bak args2
            let resEntry0 = LCS.RegEntry (AF.functionReturnType resolvedFnOv) resValue
            -- Step (4)
            resEntry1 <- liftIO $
              AO.narrowPointerType bak fwdDecRetType resEntry0
            -- Step (5)
            resEntry2 <- liftIO $
              AFA.convertBitvector bak (LCF.handleReturnType fwdDecHandle) resEntry1
            pure $ LCS.regValue resEntry2

      in pure $ LCS.mkOverride' fwdDecName
                  (LCF.handleReturnType fwdDecHandle)
                  ovSim
    -- If no such function can be found, bail out.
    Nothing -> CMC.throwM $ AE.ForwardDeclarationNameNotFound fwdDecName
  where
    fwdDecRetType = AFA.promoteBVToPtr $ LCF.handleReturnType fwdDecHandle

    -- | Zero-extend the types (if necessary) of the pointer arguments in a
    -- forward declaration override to match the types used in the resolved
    -- function. This corresponds to step (2) in
    -- @Note [Resolving forward declarations]@.
    --
    -- If there is a mismatch in the number of arguments, we throw an exception
    -- here. It is also possible for there to be mismatches in the types of
    -- individual arguments, but that is checked separately in
    -- 'AO.extendPointerType'.
    extendToRegisterAssignment ::
      forall narrowTps regTps.
      LCT.CtxRepr regTps ->
      Ctx.Assignment (LCS.RegEntry sym) narrowTps ->
      IO (Ctx.Assignment (LCS.RegEntry sym) regTps)
    extendToRegisterAssignment regTys narrowEs = go regTys narrowEs
      where
        go :: forall regTps' narrowTps'.
              LCT.CtxRepr regTps' ->
              Ctx.Assignment (LCS.RegEntry sym) narrowTps' ->
              IO (Ctx.Assignment (LCS.RegEntry sym) regTps')
        go Ctx.Empty Ctx.Empty = pure Ctx.Empty
        go (regTypeReprs Ctx.:> regTypeRepr) (narrowEntries Ctx.:> narrowEntry) = do
          regEntry <- AO.extendPointerType bak regTypeRepr narrowEntry
          regEntries <- go regTypeReprs narrowEntries
          pure (regEntries Ctx.:> regEntry)
        go _ _ = CMC.throwM $ AE.ForwardDeclarationArgumentNumberMismatch
                                fwdDecName regTys narrowTys

        narrowTys = PC.fmapFC LCS.regType narrowEs

{-
Note [Resolving forward declarations]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Forward declarations (as detailed in the "Functions" section of the README) are
surprisingly tricky to get right. After parsing a syntax override file
containing forward declarations, the verifier must take each declarations'
Handle (stored in the `functionForwardDeclarations` field of the
`FunctionOverride` and register it to an appropriate `Override`. Let's use this
as a running example:

  (defun @foo ((x (Bitvector 8))) (Bitvector 8)
    (start start:
      (let res (funcall @bar x))
      (return res)))

  (declare @bar ((x (Bitvector 8))) (Bitvector 8))

When the simulator invokes @bar from @foo, it has an argument of (Bitvector 8)
in hand. But the corresponding override for @bar will _not_ have (Bitvector 8)
as its argument type. The actual argument type depends on what kind of override
is provided for @bar:

* If @bar is another syntax override, then the corresponding `Override` will
  have an `LLVMPointerType 8` argument, due to the pipe-fitting code used in
  A.FunctionOverride.Extension.acfgToFunctionOverride. See
  Note [Bitvector Argument Mapping] in A.FunctionOverride.ArgumentMapping.

* If @bar is a built-in Haskell override, then the corresponding `Override`
  will have an `LLVMPointerType ?ptrWidth` argument by convention.

Either way, we will have to perform some type conversions for the arguments,
and similarly for the result. We proceed as follows:

1. First, convert the (Bitvector 8) argument to an `LLVMPointer 8` using
   A.FunctionOverride.ArgumentMapping.buildForwardDecOverrideArgs.

2. Next, zero-extend the `LLVMPointer 8` argument if necessary using
   `extendToRegisterAssignment`. If @bar is another syntax override, this is a
   no-op, but if @bar is a Haskell override, then this will zero-extend the
   argument to be of type `LLVMPointer ?ptrWidth`.

3. Now that the argument type matches the override for @bar, invoke the
   override.

4. Next, take the result and truncate it if necessary using
   A.Override.narrowPointerType. If @bar is another syntax override, this is
   a no-op but if @bar is a Haskell override, then this will truncate the
   argument from an `LLVMPointer ?ptrWidth` to an `LLVMPointer 8`.

5. Finally, convert the `LLVMPointer 8`-typed result to a (Bitvector 8)
   using A.FunctionOverride.ArgumentMapping.convertBitvector.

This process bears a resemblance to the pipe-fitting code used to implement
`functionIntegerArguments` and `functionIntegerReturnRegisters` in a
FunctionABI, but the pipe-fitting used for forward declarations does not have
to worry about explicitly passing values to/from `macaw` register structs.
(At the moment, forward declarations cannot be used to invoke functions defined
in binaries, which is how we are able to get away with not caring about
register structs for forward declarations.)

The pipe-fitting used for forward declarations could likely be made much
simpler with a design like the one put forth in #76.

Both the `verify` and `test-overrides` commands must register overrides for
forward declarations, but the `verify` command does so lazily (see
Note [Lazily registering overrides] in A.Extensions) while the `test-overrides`
command registers everything upfront.
-}
