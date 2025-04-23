module Main (main) where

import Test.QuickCheck (isSuccess)
import System.Exit (exitSuccess, exitFailure)
import QuickCheckTests (qc_main)

main :: IO ()
main = do
    res <- qc_main
    case all isSuccess res of
        True -> exitSuccess
        False -> exitFailure
