module ChurchNumberTests where

import Test.HUnit

import LazyKCore (betaRedInf, toLambda, readLazyK)
import LazyKParts (shortChNum, getChNum)

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
            Right e -> getChNum . betaRedInf . toLambda $ e
            _       -> Nothing
