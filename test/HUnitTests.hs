module HUnitTests where

import Test.HUnit

import LazyKCore (reductInf, toLambda, readLazyK)
import LamCalcParts (shortChNum, getChNum)

hUnitAll :: IO Counts
hUnitAll = do
    runTestTT tests
  where
    tests = TestList $ map (\n ->
        let title = ("Church number Test :" ++ show n)
        in TestLabel title (churchNumberTest title n)
        ) [0..256]

churchNumberTest :: String -> Int -> Test
churchNumberTest title n = TestCase(assertEqual title (Just n) (calc title n))

calc :: String -> Int -> Maybe Int
calc title n = case readLazyK title . (shortChNum!!) $ n of
            Right e -> getChNum . reductInf . toLambda $ e
            _       -> Nothing
