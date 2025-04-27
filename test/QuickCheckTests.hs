module QuickCheckTests where

import Test.QuickCheck (Args(..), Result(..), Property,
                        (==>), quickCheckWithResult, stdArgs)

import LazyKCore (LamExpr(..), NameManager(..) , Stringifying(..)
                , betaRedLimit, toNamedString, readLazyK)

qc_main :: IO [Result]
qc_main = do
    let args = stdArgs { maxSuccess = 1000, maxSize = 1000 }
    res <- quickCheckWithResult args prop_toNamedString_readLazyK
    res_b <- quickCheckWithResult args prop_beta_reduction
    return [res, res_b]

-- | toNamedString の結果が readLazyK で元に戻ること。
prop_toNamedString_readLazyK :: NameManager -> LamExpr -> Property
prop_toNamedString_readLazyK mng e =
    e /= Nm "iota" ==> -- Iota のみは、Lazy Kの仕様上表記出来ない。除外する。
    case toNamedString mng e of
        Stringifying e' _ _ -> case readLazyK "DummyTitle" e' of
            Right e'' -> e == e''
            Left _ -> False

-- | beta簡約が止まるなら、2回目の簡約は同じ値になること。
prop_beta_reduction :: LamExpr -> Property
prop_beta_reduction expr =
    (red_expr /= Nothing) ==> case betaRedLimit 50000 red_1st of
        Nothing      -> False  -- beta簡約2回目は成功する筈。でなければtest失敗。
        Just red_2nd -> red_1st == red_2nd  -- 2回簡約しても同じ値。試験成功。
  where
    red_expr = betaRedLimit 50000 expr
    red_1st = maybe (error "Internal Error @ prop_beta_reduction") id red_expr
