module HUnitTests where

import Test.HUnit

import LamCalcCore (reductInf, toLambda, readLazyK)
import LamCalcParts (getChNum)
import ShortChurchNum (shortChNum)

hUnitAll :: IO Counts
hUnitAll = do
    runTestTT tests
  where
    tests = TestList $ map (\n ->
        let title = ("Church number Test :" ++ show n)
        in TestLabel title (churchNumberTest title n)
        ) [0..256]

churchNumberTest :: String -> Int -> Test
churchNumberTest title n = TestCase(assertEqual title (Right n) (calc title n))

calc :: String -> Int -> Either String Int
calc title n = case readLazyK title . (shortChNum!!) $ n of
            Right e  -> getChNum . reductInf . toLambda $ e
            Left msg -> Left msg
