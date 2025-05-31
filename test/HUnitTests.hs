module HUnitTests where

import Test.HUnit
import Data.Char (ord)
import Data.Default (Default(..))
import Data.Either (fromRight)

import LamCalcCore (LamExpr(..), IoInfo(..)
                  , (%:), reductInf, toLambda, readLazyK)
import LamCalcParts (getChNum)
import LazyKParts (deconsLoopCc, deconsLoopLc)
import GoedelNum (expr_to_goedel)
import ShortChurchNum (shortChNum)

hUnitAll :: IO Counts
hUnitAll = do
    runTestTT $ TestList
        [ test_lazy, test_add_A_B_Cc, test_add_A_B_Lc, test_goedel_err
        , test_church]

test_church :: Test
test_church = TestList $ map (\n ->
    let title = ("Church number Test :" ++ show n)
    in TestLabel title (churchNumberTest title n)
    ) [0..256]

churchNumberTest :: String -> Int -> Test
churchNumberTest title n = TestCase(assertEqual title (Right n) (calc title n))

calc :: String -> Int -> Either String Int
calc title n = case readLazyK title . (shortChNum!!) $ n of
            Right e  -> getChNum . reductInf . toLambda $ e
            Left msg -> Left msg

test_lazy :: Test
test_lazy = TestCase $ do
    src <- readFile "lazy/prime_numbers.lazy"
    let expr = fromRight (Nm "dummy") . readLazyK "doctest" $ src
    (_, out) <- deconsLoopCc def def (Just 6) $ expr %: In(0)
    assertEqual "lazy deconsLoopCc" out $ map ord "2 3 5 "

test_add_A_B_Cc :: Test
test_add_A_B_Cc = TestCase $ do
    src <- readFile "lazy/add_A_B.lazy"
    let expr = fromRight (Nm "dummy") . readLazyK "doctest" $ src
    let ioInf = def {inEof = True, inHist = [7, 11]}
    (_, out) <- deconsLoopCc ioInf def Nothing $ expr %: In(0)
    assertEqual "add_A_B deconsLoopCc" out [18]

test_add_A_B_Lc :: Test
test_add_A_B_Lc = TestCase $ do
    src <- readFile "lazy/add_A_B.lazy"
    let expr = fromRight (Nm "dummy") . readLazyK "doctest" $ src
    let ioInf = def {inEof = True, inHist = [7, 11]}
    (_, out) <- deconsLoopLc ioInf def Nothing $ toLambda expr %: In(0)
    assertEqual "add_A_B deconsLoopCc" out [18]

test_goedel_err :: Test
test_goedel_err = TestCase $ do
    assertEqual "geodel error case" (expr_to_goedel (Nm "X")) (-1, -1)
