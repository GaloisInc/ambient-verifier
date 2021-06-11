module Main ( main ) where

import qualified Options.Applicative as OA

import qualified Options as O

main :: IO ()
main = verify =<< OA.execParser opts
  where
    opts = OA.info (O.parser OA.<**> OA.helper)
             ( OA.fullDesc
               <> OA.progDesc "Verify that the given binary with inputs terminates cleanly"
               <> OA.header "A verifier for programs containing weird machines"
             )

verify :: O.Options -> IO ()
verify o = do
  return ()
