module Main (main) where

import QuickCheckTests (qc_main)

main :: IO ()
main = do
    qc_main
