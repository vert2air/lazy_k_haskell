module HUnitTests where

import Test.HUnit
import Data.Char (ord)
import Data.Default (Default(..))
import Data.Either (fromRight)
import qualified Data.Map as M (fromList)

import LamCalcCore (LamExpr(..), IoInfo(..)
                  , (%:), reductInf, toLambda, readLazyK)
import LamCalcParts (Stat(..), getChNum, stat)
import LazyKParts (deconsLoopCc, deconsLoopLc)
import GoedelNum (expr_to_goedel)
import ShortChurchNum (shortChNum)

hUnitAll :: IO Counts
hUnitAll = do
    runTestTT $ TestList
        [ test_lazy, test_add_A_B_Cc, test_add_A_B_Lc, test_goedel_err
        , test_church, test_stat
        ]

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
    res <- flip mapM [True, False] $ \eof -> do
        let ioInf = def {inEof = eof, inHist = [7, 11]}
        (_, out) <- deconsLoopCc ioInf def Nothing $ expr %: In(0)
        return out
    assertEqual "add_A_B deconsLoopCc" res [[18], [18]]

test_add_A_B_Lc :: Test
test_add_A_B_Lc = TestCase $ do
    src <- readFile "lazy/add_A_B.lazy"
    let expr = fromRight (Nm "dummy") . readLazyK "doctest" $ src
    res <- flip mapM [True, False] $ \eof -> do
        let ioInf = def {inEof = eof, inHist = [7, 11]}
        (_, out) <- deconsLoopLc ioInf def Nothing $ toLambda expr %: In(0)
        return out
    assertEqual "add_A_B deconsLoopCc" res [[18], [18]]

test_goedel_err :: Test
test_goedel_err = TestCase $ do
    assertEqual "geodel error case" (expr_to_goedel (Nm "X")) (-1, -1)

test_stat :: Test
test_stat = TestCase $ do
    let src = "IKS*ii01_4M(λxy.xxy)<0%5"
    let expr = fromRight (Nm "dummy") . readLazyK "doctest" $ src
    let stt = Stat
          { maxDepth = 9
          , maxLamDepth = 2
          , maxAppDepth = 9
          , cnt_lambda = 2
          , cnt_var = 3
          , cnt_I = 1
          , cnt_K = 1
          , cnt_S = 1
          , cnt_Iota = 2
          , cnt_Jot_0 = 1
          , cnt_Jot_1 = 1
          , freeVar_index = M.fromList [(4,1)]
          , freeVar_named = M.fromList [('M',1)]
          , input_promise = M.fromList [(0,1)]
          , church_number = M.fromList [(5,1)]
          }
    assertEqual "stat" stt $ stat 0 expr
