{-# LANGUAGE NumericUnderscores #-}

module QuickCheckTests where

import Data.Default (Default(..))
import Test.QuickCheck (Args(..), Result(..), Property,
                        (==>), quickCheckWithResult, stdArgs, within)

import LamCalcCore (LamExpr(..), NameManager(..), Stringifying(..), IoInfo(..)
                    , ProgDot(..), RedResult(..)
                    , reduct, buildInputLc, buildInputCc, isPdMature, toLambda
                    , abstElim, toNamedString, readLazyK, comple)
import LazyKParts (toIotaStyle, toCcStyle, toJotStyle)
import GoedelNum (goedel_to_expr, expr_to_goedel)

-- | QuickCheck の実行時間上限。[マイクロ秒]
-- 簡約により式が膨らみ続けるケースに備え、時間で打ち切る。
timeLimit :: Int
timeLimit = 10_000_000

-- | beta簡約の上限回数。この回数に達した場合、収束しない式と判断する。
redLimit :: Int
redLimit = 10000

qc_main :: IO [Result]
qc_main = do
    let args = stdArgs { maxSuccess = 1000, maxSize = 1000 }
    res_rw <- quickCheckWithResult args prop_toNamedString_readLazyK
    res_b <- quickCheckWithResult args $ within timeLimit $ prop_reduction
    res_a <- quickCheckWithResult args $ within timeLimit $ prop_abst_elim
    res_goedel <- quickCheckWithResult args prop_goedel
    res_iota <- quickCheckWithResult args prop_cc_iota
    res_jot <- quickCheckWithResult args prop_cc_jot
    return [res_rw, res_b, res_a, res_goedel, res_iota, res_jot]

-- | toNamedString の結果が readLazyK で元に戻ること。
prop_toNamedString_readLazyK :: NameManager -> LamExpr -> Property
-- Iota のみは、Lazy Kの仕様上表記出来ない。除外する。
prop_toNamedString_readLazyK mng e = (e /= Nm "iota") ==>
    case toNamedString mng e of
        Stringifying e' _ _ -> case readLazyK "DummyTitle" e' of
            Right e'' -> e == e''
            Left _ -> False

-- | beta/eta簡約が止まるなら、2回目の簡約は同じ値になること。
prop_reduction :: Bool -> IoInfo -> LamExpr -> Property
prop_reduction isLc ioInf expr = (red_expr /= Nothing) ==>
    case reductInputLimit isLc ioInf redLimit red_1st of
        Nothing      -> False  -- 簡約2回目も成功する筈。でなければtest失敗。
        Just red_2nd -> red_1st == red_2nd  -- 2回簡約しても同じ値。試験成功。
  where
    red_expr = reductInputLimit isLc ioInf redLimit expr
    red_1st = maybe (error "Internal Error @ prop_reduction") id red_expr

-- | beta/eta簡約が止まるなら、抽象化除去後に簡約しても値は同一であること。
prop_abst_elim :: Bool -> IoInfo -> LamExpr -> Property
prop_abst_elim isLc ioInf expr = (red_expr /= Nothing) ==>
    case reductInputLimit isLc ioInf redLimit $ comple abstElim expr of
        Nothing      -> False -- 抽象化除去して簡約出来るなくなればtest失敗。
        Just red_2nd -> red_1st == red_2nd  -- 抽象化除去後も同じ値。試験成功。
  where
    red_expr = reductInputLimit isLc ioInf redLimit expr
    red_1st = maybe (error "Internal Error @ prop_abst_elim") id red_expr

prop_goedel :: Integer -> Bool
prop_goedel n = let gn = abs n
                    expr = goedel_to_expr gn
                in gn == fst (expr_to_goedel expr)

prop_cc_iota :: Integer -> Bool
prop_cc_iota n = let gn = abs n
                     cc = goedel_to_expr gn
                     iota = toIotaStyle cc
                 in toCcStyle iota == cc

prop_cc_jot :: Integer -> Bool
prop_cc_jot n = let gn = abs n
                    cc = goedel_to_expr gn
                    jot = toJotStyle cc
                in toCcStyle jot == cc

-- | 指定回数を上限に、変化しなくなるまで、beta/eta簡約を行う。toLambdaを含む。
reductInputLimit :: Bool    -- ^ buildInput で、Lc を使うか。(Falseは Cc)
                -> IoInfo   -- ^ Input履歴
                -> Int      -- ^ beta簡約の上限回数
                -> LamExpr  -- ^ beta/eta簡約を行うラムダ式
                -> Maybe LamExpr  -- ^ beta/eta簡約の結果。
                        -- 以下のいずれかの場合、Nothing を返す。
                        -- - beta簡約の上限回数に達しても 簡約の余地がある。
                        -- - 入力promiseに当たりbete簡約が進まなくなった。
reductInputLimit isLc ioInf n e = reductLimitAux isLc limitInf def $ toLambda e
  where
    limitInf = ioInf {progDot = ProgDot [0, n]}

-- | reductInputLimit から呼ばれるのみ。
reductLimitAux :: Bool -> IoInfo -> ProgDot -> LamExpr -> Maybe LamExpr
reductLimitAux isLc limit pdot e = case reduct buildInput limit pdot e of
    RedProg pdot' inIx e'
        | isPdMature 1 limit pdot -> Nothing -- 収束が見えない。スルー。
        | inIx >= 0 -> Nothing -- 入力promiseに当たった。スルー。
        | otherwise -> reductLimitAux isLc limit pdot' e' -- 前進した。継続。
    RedStop _pdot' inIx e'
        | isPdMature 1 limit pdot -> Nothing -- 収束が見えない。スルー。
        | inIx >= 0 -> Nothing -- 入力promiseに当たった。スルー。
        | otherwise -> Just e'  -- 簡約が止まった。
  where
    buildInput = if isLc then buildInputLc else buildInputCc
