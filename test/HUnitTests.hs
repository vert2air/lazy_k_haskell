module HUnitTests where

import Test.HUnit
import Data.Char (ord)
import Data.Default (Default(..))
import Data.Either (fromRight)
import qualified Data.Map as M (fromList)
import System.Exit (ExitCode(..))
import System.IO (stderr)
import System.IO.Silently (hCapture)

import LamCalcCore (LamExpr(..), IoInfo(..), NameManager(..), ProgDot(..)
                  , (%:), la, reductInf, toLambda, readLazyK, toNamedString
                  , takeStringified, applyN
                  )
import LamCalcParts (Stat(..), getChNum, stat)
import LazyKParts (deconsLoopCc, deconsLoopLc)
import GoedelNum (expr_to_goedel)
import ShortChurchNum (shortChNum)

hUnitAll :: IO Counts
hUnitAll = do
    runTestTT $ TestList
        [ test_lazy, test_add_A_B , test_goedel_err
        , test_church, test_stat
        , test_show_lamExpr
        , test_show_NameManager
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
    assertEqual "lazy deconsLoopCc" (ExitSuccess, map ord "2 3 5 ")
                        =<< deconsLoopCc def def (Just 6) (expr %: In(0))

test_add_A_B :: Test
test_add_A_B = TestCase $ do
    src <- readFile "lazy/add_A_B.lazy"
    let expr = fromRight (Nm "dummy") . readLazyK "doctest" $ src
    flip mapM_ [True, False] $ \eof -> do
        let ioInf = def {inEof = eof, inHist = [7, 11]}
        assertEqual "add_A_B deconsLoopCc" (ExitSuccess, [18])
                =<< deconsLoopCc ioInf def Nothing (expr %: In(0))
        assertEqual "add_A_B deconsLoopLc" (ExitSuccess, [18])
                =<< deconsLoopLc ioInf def Nothing (toLambda expr %: In(0))
        res <- hCapture [stderr] $
                deconsLoopCc ioInf {optV = True} def Nothing (expr %: In(0))
        let outLines = lines . fst $ res
            line0_start = "18(=0x12)--'"
        assertEqual "add_A_B deconsLoopCc -v [0]" line0_start
                                (take (length line0_start) $ (outLines !! 0))
        assertEqual "add_A_B deconsLoopCc -v [1]" "Reach EOF (256)"
                                                                (outLines !! 1)
        (progPrintCc, _) <- hCapture [stderr] $
                deconsLoopCc ioInf {progDot = ProgDot [100,100]}
                            def Nothing (expr %: In(0))
        assertEqual "add_A_B deconsLoopCc -d 100,100"
                                                progPrintCc ".**..........."
        (progPrintLc, _) <- hCapture [stderr] $
                deconsLoopLc ioInf {progDot = ProgDot [500,500]}
                            def Nothing (toLambda expr %: In(0))
        assertEqual "add_A_B deconsLoopLc -d 500,500"
                                        progPrintLc ".*.*.*.*.*.*.*.*.*.*.*.*"


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

test_show_NameManager :: Test
test_show_NameManager = TestCase $ do
    assertEqual "NameManager show" (show (def :: NameManager)) $
        "NameManager {nmPolicy = PK_minimum"
        ++ ", nmPool = \"xyzabcdefghjlmnopqrtuvwXYZABCDEFGHJLMNOPQRTUVW\""
        ++ ", nmStack = \"\", nmUnlamStyle = False, nmLamSign = '\\955'}"

test_show_lamExpr :: Test
test_show_lamExpr = TestCase $ do
    assertEqual "lamExpr show" "λ X(_1Z)" $ show $
                la $ Nm "X" %: (V 1 %: Nm "Z")
    assertEqual "lamExpr show" "S(*Ii)" $ show $ Nm "S" %: (Nm "I" %: Nm "iota")
    assertEqual "lamExpr show" "*iIS" $ show $ (Nm "iota" %: Nm "I") %: Nm "S"
    assertEqual "lamExpr show" "*ii" $ show $ Nm "iota" %: Nm "iota"
    assertEqual "lamExpr show" "*i(*iS)" $ show $ Nm "iota" %: (Nm "iota" %: Nm "S")
    assertEqual "lamExpr show" "*(*iS)i" $ show $ (Nm "iota" %: Nm "S") %: Nm "iota"
    assertEqual "lamExpr show" "*i*i*is" $
                takeStringified $ toNamedString def {nmUnlamStyle = True} $
                            Nm "iota" %: (Nm "iota" %: (Nm "iota" %: Nm "S"))
    assertEqual "lamExpr show" "***siii" $
                takeStringified $ toNamedString def {nmUnlamStyle = True} $
                            ((Nm "S" %: Nm "iota") %: Nm "iota") %: Nm "iota"
    assertEqual "lamExpr show" "`*iis" $
                takeStringified $ toNamedString def {nmUnlamStyle = True} $
                    (Nm "iota" %: Nm "iota") %: Nm "S"
    assertEqual "lamExpr show" "`s*ii" $
                takeStringified $ toNamedString def {nmUnlamStyle = True} $
                    Nm "S" %: (Nm "iota" %: Nm "iota")
    assertEqual "lamExpr show" "λx.(λx.x)(λx.x)" $
                takeStringified $ toNamedString def $
                la $ (la (V 1) %: la (V 1))
    assertEqual "lamExpr show"
        ("λxyzabcdefghjlmnopqrtuvwXYZABCDEFGHJLMNOPQRTUVW."
        ++ "xyzabcdefghjlmnopqrtuvwXYZABCDEFGHJLMNOPQRTUVW") $
            takeStringified . toNamedString def .
                applyN ((26 - 3) * 2) la .
                    foldl1 (\acc e -> acc %: e) . map V $
                        [(26 - 3) * 2, (26 - 3) * 2 -1 .. 1]
