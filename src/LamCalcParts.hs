{- |
  Module      : LamCalcParts
  Description : ラムダ計算で頻出のデータや処理。
                Lazy Kコード作成時のパーツ群
-}

module LamCalcParts where

import           Data.Default (Default(..))
import           Data.Either (fromRight)
import qualified Data.Map as M (Map, empty, singleton)
import Data.Map.Merge.Lazy (merge, preserveMissing, zipWithMatched)

import LamCalcCore (LamExpr(..), IoInfo(..), ProgDot(..), RedResult(..)
                    , la, (%:), readLazyK, forceProg, incPd, takeStringified
                    , toNamedString)

data Stat = Stat
    { maxDepth :: !Int
    , maxLamDepth :: !Int -- Lambda抽象のみの最大の深さ
    , maxAppDepth :: !Int -- Appのみの最大の深さ
    , cnt_lambda :: !Int
    , cnt_var :: !Int     -- de Bruijn Index
    , cnt_I :: !Int
    , cnt_K :: !Int
    , cnt_S :: !Int
    , cnt_Iota :: !Int
    , cnt_Jot_0 :: !Int
    , cnt_Jot_1 :: !Int
    , freeVar_index :: M.Map Int  Int
    , freeVar_named :: M.Map Char Int
    , input_promise :: M.Map Int  Int
    } deriving (Show)

instance Default Stat where
    def = Stat
        { maxDepth = 0
        , maxLamDepth = 0
        , maxAppDepth = 0
        , cnt_lambda = 0
        , cnt_var = 0
        , cnt_I = 0
        , cnt_K = 0
        , cnt_S = 0
        , cnt_Iota = 0
        , cnt_Jot_0 = 0
        , cnt_Jot_1 = 0
        , freeVar_index = M.empty
        , freeVar_named = M.empty
        , input_promise = M.empty
        }

(%) :: Stat -> Stat -> Stat
a % b = Stat
    { maxDepth      = max (maxDepth    a) (maxDepth    b)
    , maxLamDepth   = max (maxLamDepth a) (maxLamDepth b)
    , maxAppDepth   = max (maxAppDepth a) (maxAppDepth b)
    , cnt_lambda    = cnt_lambda a + cnt_lambda b
    , cnt_var       = cnt_var    a + cnt_var    b
    , cnt_I         = cnt_I      a + cnt_I      b
    , cnt_K         = cnt_K      a + cnt_K      b
    , cnt_S         = cnt_S      a + cnt_S      b
    , cnt_Iota      = cnt_Iota   a + cnt_Iota   b
    , cnt_Jot_0     = cnt_Jot_0  a + cnt_Jot_0  b
    , cnt_Jot_1     = cnt_Jot_1  a + cnt_Jot_1  b
    , freeVar_index = freeVar_index a `addEach` freeVar_index b
    , freeVar_named = freeVar_named a `addEach` freeVar_named b
    , input_promise = input_promise a `addEach` input_promise b
    }

-- | 補助関数(内部用) : M.Map k Int で、キー毎に値を加算
addEach :: (Ord k) => M.Map k Int -> M.Map k Int -> M.Map k Int
ma `addEach` mb = merge preserveMissing preserveMissing
                    (zipWithMatched $ \ _key a b -> a + b) ma mb

-- | 補助関数(内部用) : 抽象化の深さを1増加
incAbst :: Stat -> Stat
incAbst st = st
    { maxDepth    = maxDepth    st + 1
    , maxLamDepth = maxLamDepth st + 1
    , cnt_lambda  = cnt_lambda  st + 1
    }

-- | 補助関数(内部用) : 関数適用の深さを1増加
incApp :: Stat -> Stat
incApp st = st
    { maxDepth    = maxDepth    st + 1
    , maxAppDepth = maxAppDepth st + 1
    }

-- | ラムダ式の統計情報を取得
--
-- Intは再帰用で使う。外部からの呼び出し時は 0 を設定すること。
stat :: Int -> LamExpr -> Stat
stat lDep (V idx)
    | idx <= lDep     = def { cnt_var = 1 }
    | otherwise       = def { freeVar_index = M.singleton (idx - lDep) 1 }
stat lDep (L _ lexp)  = incAbst $ stat (lDep + 1) lexp
stat lDep (App _ x y) = incApp  $ stat lDep x % stat lDep y
stat _    (Nm "I")    = def { cnt_I = 1 }
stat _    (Nm "K")    = def { cnt_K = 1 }
stat _    (Nm "S")    = def { cnt_S = 1 }
stat _    (Nm "iota") = def { cnt_Iota = 1 }
stat _    (Nm n)      = def { freeVar_named = M.singleton (n !! 0) 1 }
stat _    (Jot _ jot) = def { cnt_Jot_0 = s0, cnt_Jot_1 = s1 }
  where
    aux (c0, c1) '0' = (c0 + 1, c1)
    aux (c0, c1) _   = (c0    , c1 + 1)
    (s0, s1) = foldl aux (0, 0) jot
stat _    (In idx)    = def { input_promise = M.singleton idx 1 }

lc_true, lc_false, if_then_else, lc_and, lc_or, lc_not :: LamExpr
lc_true = la . la $ V 2
lc_false = la . la $ V 1
if_then_else = la . la . la $ V 3 %: V 2 %: V 1
lc_and = la . la $ V 2 %: V 1 %: lc_false
lc_or  = la . la $ V 2 %: lc_true %: V 1
lc_not = la $ V 1 %: lc_false %: lc_true

readStr :: String -> LamExpr
readStr = fromRight (error "internal") . readLazyK ""

-- | Church encode の自然数 (0, 1, 10=(ASCIIコードの LF), 256)
ch_0, ch_1, ch_LF, ch_256 :: LamExpr
ch_0 = readStr $ shortChNum !! 0
ch_1 = readStr $ shortChNum !! 1
ch_LF = readStr $ shortChNum !! 10
ch_256 = readStr $ shortChNum !! 256

is_zero, cn_succ, cn_plus, cn_mult, cn_pred, cn_minus, is_eq :: LamExpr
is_zero = la $ V 1 %: la lc_false %: lc_true
cn_succ = readStr "`s``s`ksk"
cn_plus = la . la . la . la $ V 4 %: V 2 %: (V 3 %: V 2 %: V 1)
cn_mult = la . la . la $ V 3 %: (V 2 %: V 1)
cn_pred = la . la . la $ ((V 3 %: (la . la $ V 1 %: (V 2 %: V 4)))) %: la (V 2) %: la (V 1)
cn_minus = la . la $ V 1 %: cn_pred %: V 2
is_eq = la . la $ (
    lc_and
        %: (is_zero %: (cn_minus %: V 1 %: V 2))
        %: (is_zero %: (cn_minus %: V 2 %: V 1))
    )

-- | Scott encode のリスト構造データ
lc_nil, cons, car, cdr, is_nil :: LamExpr
lc_nil = la . la $ V 1
cons = la . la . la $ V 1 %: V 3 %: V 2
car = la $ V 1 %: lc_true
cdr = la $ V 1 %: lc_false
-- | nilかconsかを判定するコード。
is_nil = la $ (V 1) %: (la . la . la $ lc_false) %: lc_true

{- | 引数が Church数で ASCIIコードの LF (=0x0a) であるかを判定

  結局遅いのは、引き算。引き算をする代わりに、テーブルを持つ。
  ASCIIコードの話なので、入力終了の 256 を含めても 257個のテーブルで済む。
  is_eq_r2 と比べても劇的に速い。その代わりに、Lazy Kコードが大きくなる。
-}
is_eq_LF :: LamExpr
is_eq_LF = la . (car %:) . (%:) ((V 1) %: cdr) $
        foldr (\a d -> cons %: a %: d) lc_nil $
               (map (const lc_false) [(0 :: Int) .. 9])
            ++ [lc_true]           -- 10
            ++ (map (const lc_false) [(11 :: Int) .. 256])

diff_1_pair, cn_pred_r2, cn_minus_r2, is_eq_r2 :: LamExpr
diff_1_pair = la ( cons
    %: (cn_plus %: (car %: V 1) %: ch_1)
    %: (car %: V 1)
    )
cn_pred_r2 = la( cdr %: (
    V 1 %: diff_1_pair %: (cons %: ch_0 %: ch_1)
    ))
cn_minus_r2 = la(la( V 1 %: cn_pred_r2 %: V 2 ))
is_eq_r2 = la(la( lc_and %:
    (is_zero %: (cn_minus_r2 %: V 1 %: V 2)) %:
    (is_zero %: (cn_minus_r2 %: V 2 %: V 1))
    ))

y_comb :: LamExpr
y_comb = la $ (la (V 2 %: (V 1 %: V 1))) %: (la (V 2 %: (V 1 %: V 1)))

-- | 引数にbeta/eta簡約済みの Church encoding の自然数を受取り、値を返す。
getChNum :: LamExpr  -- ^ 簡約済みの Church encoding の自然数。
        -> Either String Int -- ^ ラムダ式が表す自然数。errorは式の文字列返却。
getChNum (L _ (L _ llexp)) = countF llexp
  where
    countF (V 1) = Right 0
    countF (App _ (V 2) e) = (+1) <$> countF e
    countF e = Left . takeStringified . toNamedString def $ e
-- 1 = λfx.fx = λf.f (eta変換より) なので、個別に処理。
getChNum (L _ (V 1)) = Right 1
getChNum e = Left . takeStringified . toNamedString def $ e

-- | コンビネータ表現からchurch数を取り出す。
--
-- Nm "+1" と 数値 n を表す V n が使われていることが前提。
-- 通常の LamExpr とは、意味が異なっている。
red_ccN :: IoInfo
        -> ProgDot
        -> LamExpr
        -> RedResult LamExpr
red_ccN ioInf d e = case once of
    -- 停止したのなら、続けても無駄。
    s@(RedStop _d _ _)                                  -> s
    -- 既に入力promiseに当たったのなら、続けても無駄。
    p@(RedProg _d ix   _)                   | ix >= 0   -> p
    -- 次に入力promiseに当たるのが分かっているのなら、続けても無駄。
    p@(RedProg _d _    (In _))                          -> p
    p@(RedProg _d _    (App _ (In _) _))                -> p
    -- red_ccN 特有処理。Nm "+1" の簡約。
    RedProg    d' _ e'@(App _ (Nm "+1")  _)             -> red_ccN ioInf d' e'
    RedProg    d' _ e'@(App _ (Nm "I") _)               -> red_ccN ioInf d' e'
    p@(RedProg _  _    (App _ (Nm _) _))                -> p
    RedProg    d' _ e'@(App _ (App _ (Nm "K") _x) _y)   -> red_ccN ioInf d' e'
    RedProg    d' _ e'@(App _ (App _ (Nm "S") (Nm "K")) _y)
                                                        -> red_ccN ioInf d' e'
    p@(RedProg _  _    (App _ (App _ (Nm _) _x) _y))    -> p
    RedProg    d' _ e'@(App _ (App _ (App _ (Nm "S") _x) _y) _z)
                                                        -> red_ccN ioInf d' e'
    -- 戻って簡約出来るパターンはチェック済みなので、一旦、return
    p@(RedProg _  _ _)                                 -> p
  where
    once = red_ccN_1 ioInf d e

-- | コンビネータ表現からchurch数を取り出す。1 stepのみ。
--
-- Nm "+1" と 数値 n を表す V n が使われていることが前提。
-- 通常の LamExpr とは、意味が異なっている。
red_ccN_1 :: IoInfo
        -> ProgDot
        -> LamExpr
        -> RedResult LamExpr
red_ccN_1 ioInf d e@(In ix)
    | inEof ioInf || ix < length (inHist ioInf)
        = forceProg $ red_ccN_1 ioInf d $ buildInputCC ioInf ix
    | otherwise                                 = RedStop d ix e
red_ccN_1 ioInf d e@(App _ (In ix) oprd)
    | inEof ioInf || ix < length (inHist ioInf)
        = forceProg $ red_ccN_1 ioInf d $ buildInputCC ioInf ix %: oprd
    | otherwise                                 = RedStop d ix e
red_ccN_1 _io d (App _ (Nm "+1") (V v))         = RedProg d (-1) . V $ v + 1
red_ccN_1 _io d (App _ (Nm "I") x)              = RedProg d (-1) x
red_ccN_1 _io d (App _ (App _ (Nm "K") x) _y)   = RedProg d (-1) x
red_ccN_1 _io d (App _ (App _ (Nm "S") (Nm "K")) _y) = RedProg d (-1) $ Nm "I"
red_ccN_1 _io d (App _ (App _ (App _ (Nm "S") (Nm "K")) _y) z)
                                                = RedProg d (-1) z
-- CCの簡約でより複雑になるのは、このパターンだけ。ここだけ incPd する。
red_ccN_1 _io d (App _ (App _ (App _ (Nm "S") x) y) z)
                                = incPd 1 . RedProg d (-1) $ x %: z %: (y %: z)
red_ccN_1 ioInf d (App _ f o) = case f' of
    e@(RedStop _ i _)
        | i >= 0 -> (%: o) <$> e    -- ToDo ここから
    RedStop d' _i _   -> (f %:) <$> red_ccN_1 ioInf d' o
    RedProg d' i  f'' -> RedProg d' i $ f'' %: o
  where
    f' = red_ccN_1 ioInf d f
red_ccN_1 _io d e = RedStop d (-1) e

buildInputCC :: IoInfo  -- ^ 標準入力の履歴と進捗Dotの表示頻度
            -> Int      -- ^ beta簡約に必要なinputのインデックス
            -> LamExpr  -- ^ 判明しているinputを展開したラムダ式
buildInputCC (IoInfo eof input _ _ _ _) ix
    | ix < length input = foldr makeCons (In (length input)) $ drop ix input
    | eof = foldr makeCons (In (length compInput)) $ drop ix compInput
    | otherwise = error "buildInput: called under unexpected condition"
  where
    -- ToDo
    makeCons a d = Nm "S"
            %: (Nm "S" %: Nm "I" %: (Nm "K" %: ccNum a))
            %: (Nm "K" %: d)
    ccNum num = fromRight (error "ccNum in buildInputCC")
                $ readLazyK "buildInputCC" (shortChNum !! num)
    compInput
        | eof = input ++ take (ix - length input + 1) [256, 256 ..]
        | otherwise = input

-- | コンパクトにChurch encodeした自然数 (0～256)
shortChNum :: [String]
shortChNum = [
      "`ki"                                                              --   0
    , "i"                                                                --   1
    , "` `s``s`ksk i"                                                    --   2
    , "``s`k```ss`s`sisk"                                                --   3
    , "` ``sii ` `s``s`ksk i"                                            --   4
    , "` `s``s`ksk ` ``sii ` `s``s`ksk i"                                --   5
    , "` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"                    --   6
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"        --   7
    , "` ``s`k```ss`s`sisk ` `s``s`ksk i"                                --   8
    , "` ` `s``s`ksk i ``s`k```ss`s`sisk"                                --   9
    , "` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"                    --  10
    , "` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"        --  11
    , "`` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"               --  12
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"   --  13
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"   --  15
    , "```s`sii``s``s`kski"                                              --  16
    , "` `s``s`ksk ```s`sii``s``s`kski"                                  --  17
    , "` `s``s`ksk ` `s``s`ksk ```s`sii``s``s`kski"                      --  18
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ```s`sii``s``s`kski"          --  19
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` ``s`k```ss`s`sisk ` `s``s`ksk i"   --  24
    , "` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"                --  25
    , "` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"    --  26
    , "` ``sii ``s`k```ss`s`sisk"                                        --  27
    , "` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"                            --  28
    , "` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"                --  29
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"    --  30
    , "`` ``si`k`s``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "` ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk i"                --  32
    , "` `s``s`ksk ` ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk i"    --  33
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"         --  34
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"    --  36
    , "` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``si`k`s``s`ksk ```s`sii``s``s`kski ` ``sii ``s`k```ss`s`sisk" --  43
    , "` `s``s`ksk `` ``si`k`s``s`ksk ```s`sii``s``s`kski ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ``s`k```ss`s`sisk ```s`sii``s``s`kski"                 --  48
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ```s`sii``s``s`kski"     --  49
    , "`` ``s`ksk ` `s``s`ksk i ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"     --  51
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"               --  54
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"   --  55
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"   --  56
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i `` ``si`k`s``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"                        --  64
    , "` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"            --  65
    , "` `s``s`ksk ` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski" --  68
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ```s`sii``s``s`kski" --  80
    , "` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"                        --  81
    , "` `s``s`ksk ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"            --  82
    , "` `s``s`ksk ` `s``s`ksk ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``si`k`s``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk i ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``si`k`s``s`ksk ` ``sii ``s`k```ss`s`sisk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``si`k`s``s`ksk ` ``sii ``s`k```ss`s`sisk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ``s`k```ss`s`sisk `` ``si`k`s``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk `` ``si`k`s``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk ```s`sii``s``s`kski"
    , "`` ``si`k`s``s`ksk ```s`sii``s``s`kski ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ```s`sii``s``s`kski"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk i"
    , "` ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"    -- 100
    , "` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``si`k`s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``si`k`s``s`ksk ` ``sii ``s`k```ss`s`sisk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ```s`sii``s``s`kski"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"       -- 108
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i `` ``si`k`s``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "` ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"            -- 125
    , "` `s``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` `s``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` `s``s`ksk i ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``si`k`s``s`ksk ` ``sii ` `s``s`ksk i `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``si`k`s``s`ksk ` ``sii ``s`k```ss`s`sisk ` ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk i ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i `` ``si`k`s``s`ksk ```s`sii``s``s`kski ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i `` ``si`k`s``s`ksk ```s`sii``s``s`kski ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ```s`sii``s``s`kski"
    , "`` ``si`k`s``s`ksk ```s`sii``s``s`kski `` ``s`ksk ` `s``s`ksk i ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``si`k`s``s`ksk ```s`sii``s``s`kski `` ``s`ksk ` `s``s`ksk i ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` `s``s`ksk i `` ``si`k`s``s`ksk ` ``sii ``s`k```ss`s`sisk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i `` ``si`k`s``s`ksk ` ``sii ``s`k```ss`s`sisk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk `` ``si`k`s``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` `s``s`ksk i ` ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ``s`k```ss`s`sisk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``si`k`s``s`ksk ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk ` ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i ```s`sii``s``s`kski"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i ```s`sii``s``s`kski"
    , "`` ``si`k`s``s`ksk ```s`sii``s``s`kski `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk i `` ``si`k`s``s`ksk ` ``sii ``s`k```ss`s`sisk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i `` ``si`k`s``s`ksk ```s`sii``s``s`kski ` ``sii ``s`k```ss`s`sisk"
    , "` ``s`k```ss`s`sisk ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` `s``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk i"
    , "`` ``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ``s`k```ss`s`sisk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk i ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` ` `s``s`ksk ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"            -- 243
    , "` `s``s`ksk ` ` `s``s`ksk ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``si`k`s``s`ksk ` ``sii ` `s``s`ksk i ` ` `s``s`ksk ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``si`k`s``s`ksk ` ``sii ` `s``s`ksk i ` ` `s``s`ksk ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` `s``s`ksk ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i ` ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ``s`k```ss`s`sisk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "```sii```sii``s``s`kski"                                          -- 256
    ]
