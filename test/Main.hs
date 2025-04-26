module Main (main) where

import Test.QuickCheck (isSuccess)
import Test.HUnit (Counts(..))
import System.Exit (exitSuccess, exitFailure)

import QuickCheckTests (qc_main)
import ChurchNumberTests (chTestAll)

main :: IO ()
main = do
    res <- qc_main
    cnt@(Counts _cases _tried errs fails) <- chTestAll
    putStrLn $ show $ cnt
    if all isSuccess res && errs == 0 && fails == 0
        then exitSuccess
        else exitFailure
