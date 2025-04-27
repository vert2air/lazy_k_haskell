module QuickCheckTests where

import Test.QuickCheck (Result(..), Property, (==>), quickCheckResult)
import Data.Default (Default(..))

import LazyKCore (LamExpr(..), NameManager(..), RedResult(..)
                , IoInfo(..), ProgDot(..), Stringifying(..)
                , betaRed, isPdMature, toNamedString, readLazyK, toLambda)

qc_main :: IO [Result]
qc_main = do
    res <- quickCheckResult prop_toNamedString_readLazyK
    res_b <- quickCheckResult prop_beta_reduction
    return [res, res_b]

-- | toNamedString の結果が readLazyK で元に戻ること。
prop_toNamedString_readLazyK :: NameManager -> LamExpr -> Bool
-- Iota のみは、Lazy Kの仕様上表記出来ない。除外する。
prop_toNamedString_readLazyK _ (Nm "iota") = True
prop_toNamedString_readLazyK mng e = case toNamedString mng e of
    Stringifying e' _ _ -> case readLazyK "DummyTitle" e' of
        Right e'' -> e == e''
        Left _ -> False

-- | beta簡約が止まるなら、2回目の簡約は同じ値になること。
prop_beta_reduction :: LamExpr -> Property
prop_beta_reduction expr =
    (red_expr /= Nothing) ==> case redFin red_1st of
        Nothing      -> False  -- beta簡約2回目は成功する筈。でなければtest失敗。
        Just red_2nd -> red_1st == red_2nd  -- 2回簡約しても同じ値。試験成功。
  where
    limitInf = IoInfo False [] False (ProgDot [0, 50000]) -- beta簡約の制限値。
    redFin e = case betaRed limitInf def . toLambda $ e of
        RedProg pdot inIx e'
            | isPdMature 1 limitInf pdot -> Nothing -- 収束が見えない。スルー。
            | inIx >= 0           -> Nothing -- 入力promiseに当たった。スルー。
            | otherwise           -> Just e'  -- betaReductionが止まった。
        RedStop pdot inIx e'
            | isPdMature 1 limitInf pdot -> Nothing -- 収束が見えない。スルー。
            | inIx >= 0           -> Nothing -- 入力promiseに当たった。スルー。
            | otherwise           -> Just e'  -- betaReductionが止まった。
    red_expr = redFin expr
    red_1st = maybe (error "Internal Error @ prop_beta_reduction") id red_expr
