{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE FlexibleInstances #-}

module QuickCheckTests where

import Data.Default (Default(..))
import Test.QuickCheck (Arbitrary(..), Args(..), Gen, Result(..), Property
                        , (==>), listOf1, oneof, vectorOf, suchThat, shuffle
                        , quickCheckWithResult, stdArgs, within)

import LamCalcCore (LamExpr(..), NameManager(..), Stringifying(..), IoInfo(..)
                    , PolicyKind(..), ProgDot(..), RedResult(..)
                    , (%:), la, reduct, buildInputLc, buildInputCc, isPdMature
                    , toLambda, abstElim, toNamedString, readLazyK, comple)
import LazyKParts (toIotaStyle, toCcStyle, toJotStyle)
import GoedelNum (goedel_to_expr, expr_to_goedel)

-- | QuickCheck の実行時間上限。[マイクロ秒]
-- 簡約により式が膨らみ続けるケースに備え、時間で打ち切る。
timeLimit :: Int
timeLimit = 10_000_000

-- | beta簡約の上限回数。この回数に達した場合、収束しない式と判断する。
redLimit :: Int
redLimit = 10000

newtype ArbitLamExpr a = ArbitLamExpr { getLE :: a } deriving (Show)

instance Arbitrary (ArbitLamExpr LamExpr) where
    arbitrary = ArbitLamExpr <$> oneof [
          -- De Bruijn index はラムダの深さなので、
          -- 大き過ぎると自由変数ばかりになってしまう。
          -- ラムダの深さは、対数スケールで増加する筈なので、log で圧縮する。
          V . (+1) . floor . log . (+1) . abs <$> (arbitrary :: Gen Float)
        , do
            ArbitLamExpr lexp <- arbitrary
            case lexp of
                -- '*' が無いと Iotaスタイルは表現できない。やり直す。
                Nm "iota" -> getLE <$> arbitrary
                _         -> return $ la lexp
        , (%:) <$> (getLE <$> arbitrary) <*> (getLE <$> arbitrary)
        , (Nm <$>) . oneof $
            -- SKI および、iota を多めに。
            [ pure [ch] | ch <- "SKISKISKISKISKI" ++ "SKSKSKSKSK" ++ "SSSSS"
                            ++ "abcdefgh" ++ "j" ++ "lmnopqr" ++ "tuvwxyz"
                            ++ "ABCDEFGH" ++ "J" ++ "LMNOPQR" ++ "TUVWXYZ" ]
            ++ [pure "iota", pure "iota", pure "iota"]

        , do
            jotexp <- listOf1 . oneof . map pure $ "01"
            return $ Jot (length jotexp) jotexp
        -- , In . abs <$> arbitrary
        , Num . abs <$> arbitrary
        ]

newtype ArbitNameManager a = ArbitNameManager { getNM :: a } deriving (Show)

instance Arbitrary (ArbitNameManager NameManager) where
    arbitrary = (ArbitNameManager <$>) $ NameManager <$> (getPK <$> arbitrary)
        <*> shuffle ("abcdefgh" ++ "j" ++ "lmnopqr" ++ "tuvwxyz_ _ _"
                ++ "ABCDEFGH" ++ "J" ++ "LMNOPQR" ++ "TUVWXYZ_ _ _")
        <*> pure ""
        <*> arbitrary
        <*> oneof [pure 'λ', pure '\\']

newtype ArbitPolicyKind a = ArbitPolicyKind { getPK :: a }

instance Arbitrary (ArbitPolicyKind PolicyKind) where
    -- arbitrary = ArbitPolicyKind $ oneof $ map return [
    arbitrary = (ArbitPolicyKind <$>) $ oneof $ map return [
          PK_index, PK_single_use, PK_level, PK_minimum
        ]

newtype ArbitIoInfo a = ArbitIoInfo a deriving (Show)

instance Arbitrary (ArbitIoInfo IoInfo) where
    arbitrary = (ArbitIoInfo <$>) $ IoInfo
        <$> arbitrary
        <*> (map (`mod` 256) <$> arbitrary)
        <*> arbitrary
        <*> (getPD <$> arbitrary)
        <*> oneof [pure 'λ', pure '\\']
        <*> arbitrary

newtype ArbitProgDot a = ArbitProgDot { getPD :: a }

instance Arbitrary (ArbitProgDot ProgDot) where
    arbitrary = (ArbitProgDot <$>) $ ProgDot
                        <$> vectorOf 2 (arbitrary `suchThat` (>= 0))

qc_main :: IO [Result]
qc_main = do
    let args = stdArgs { maxSuccess = 1000, maxSize = 1000 }
    res_rw <- quickCheckWithResult args prop_toNamedString_readLazyK
    res_b <- quickCheckWithResult args $ within timeLimit $ prop_reduction
    res_Integer <- mapM (quickCheckWithResult args)
            [ prop_goedel
            , prop_cc_iota
            , prop_cc_jot
            ]
    res_LamExpr <- mapM (quickCheckWithResult args)
            [ prop_abst_elem_twice
            , prop_expr_cc_twice
            , prop_expr_iota_twice
            , prop_expr_jot_twice
            ]
    return $ res_rw : res_b : (res_LamExpr ++ res_Integer)

-- | toNamedString の結果が readLazyK で元に戻ること。
prop_toNamedString_readLazyK :: ArbitNameManager NameManager
                            -> ArbitLamExpr LamExpr
                            -> Property
-- Iota のみは、Lazy Kの仕様上表記出来ない。除外する。
prop_toNamedString_readLazyK (ArbitNameManager mng) (ArbitLamExpr e) =
    (e /= Nm "iota") ==>
    case toNamedString mng e of
        Stringifying e' _ _ -> case readLazyK "DummyTitle" e' of
            Right e'' -> e == e''
            Left _ -> False

-- | beta/eta簡約が止まるなら、2回目の簡約は同じ値になること。
prop_reduction :: Bool                  -- ^ TrueならLc、FalseならCcをtest
                -> ArbitIoInfo IoInfo
                -> ArbitLamExpr LamExpr
                -> Property
prop_reduction isLc (ArbitIoInfo ioInf) (ArbitLamExpr expr) =
    (red_expr /= Nothing) ==>
    case reductInputLimit isLc ioInf redLimit red_1st of
        Nothing      -> False  -- 簡約2回目も成功する筈。でなければtest失敗。
        Just red_2nd -> red_1st == red_2nd  -- 2回簡約しても同じ値。試験成功。
  where
    red_expr = reductInputLimit isLc ioInf redLimit expr
    red_1st = maybe (error "Internal Error @ prop_reduction") id red_expr

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

-- | abstElimを2回適用しても同じ値になること。
prop_abst_elem_twice :: ArbitLamExpr LamExpr -> Bool
prop_abst_elem_twice (ArbitLamExpr expr) = ae_1time == ae_2time
  where
    ae_1time = comple abstElim expr
    ae_2time = comple abstElim ae_1time

-- | CCスタイルへの変更を2回適用しても同じ値になること。
prop_expr_cc_twice :: ArbitLamExpr LamExpr -> Bool
prop_expr_cc_twice (ArbitLamExpr expr) = toCcStyle e_1 == e_1
  where e_1 = toCcStyle expr

-- | Iotaスタイルへの変更を2回適用しても同じ値になること。
prop_expr_iota_twice :: ArbitLamExpr LamExpr -> Bool
prop_expr_iota_twice (ArbitLamExpr expr) = toIotaStyle e_1 == e_1
  where e_1 = toIotaStyle expr

-- | Jotスタイルへの変更を2回適用しても同じ値になること。
prop_expr_jot_twice :: ArbitLamExpr LamExpr -> Bool
prop_expr_jot_twice (ArbitLamExpr expr) = toJotStyle e_1 == e_1
  where e_1 = toJotStyle expr

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
