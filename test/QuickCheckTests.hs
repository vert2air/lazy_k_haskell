module QuickCheckTests where

import Test.QuickCheck (Args(..), Result(..), Property,
                        (==>), quickCheckWithResult, stdArgs)

import LazyKCore (LamExpr(..), NameManager(..) , Stringifying(..)
                , abstElim, reductLimit, toNamedString, readLazyK, comple)

qc_main :: IO [Result]
qc_main = do
    let args = stdArgs { maxSuccess = 1000, maxSize = 1000 }
    res_rw <- quickCheckWithResult args prop_toNamedString_readLazyK
    res_b <- quickCheckWithResult args prop_reduction
    res_a <- quickCheckWithResult args prop_abst_elim
    return [res_rw, res_b, res_a]

-- | toNamedString の結果が readLazyK で元に戻ること。
prop_toNamedString_readLazyK :: NameManager -> LamExpr -> Property
-- Iota のみは、Lazy Kの仕様上表記出来ない。除外する。
prop_toNamedString_readLazyK mng e = (e /= Nm "iota") ==>
    case toNamedString mng e of
        Stringifying e' _ _ -> case readLazyK "DummyTitle" e' of
            Right e'' -> e == e''
            Left _ -> False

redLimit :: Int
redLimit = 10000

-- | beta/eta簡約が止まるなら、2回目の簡約は同じ値になること。
prop_reduction :: LamExpr -> Property
prop_reduction expr = (red_expr /= Nothing) ==>
    case reductLimit redLimit red_1st of
        Nothing      -> False  -- 簡約2回目も成功する筈。でなければtest失敗。
        Just red_2nd -> red_1st == red_2nd  -- 2回簡約しても同じ値。試験成功。
  where
    red_expr = reductLimit redLimit expr
    red_1st = maybe (error "Internal Error @ prop_reduction") id red_expr

-- | beta/eta簡約が止まるなら、抽象化除去後に簡約しても値は同一であること。
prop_abst_elim :: LamExpr -> Property
prop_abst_elim expr = (red_expr /= Nothing) ==>
    case reductLimit redLimit $ comple abstElim expr of
        Nothing      -> False -- 抽象化除去して簡約出来るなくなればtest失敗。
        Just red_2nd -> red_1st == red_2nd  -- 抽象化除去後も同じ値。試験成功。
  where
    red_expr = reductLimit redLimit expr
    red_1st = maybe (error "Internal Error @ prop_abst_elim") id red_expr
