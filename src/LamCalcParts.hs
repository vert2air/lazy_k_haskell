module LamCalcParts where

import Data.Char (ord)
import Data.Either (fromRight)

import LamCalcCore (LamExpr(..), la, (%:), readLazyK)

lc_true, lc_false, if_then_else, lc_and, lc_or, lc_not :: LamExpr
lc_true = la . la $ V 2
lc_false = la . la $ V 1
if_then_else = la . la . la $ V 3 %: V 2 %: V 1
lc_and = la . la $ V 2 %: V 1 %: lc_false
lc_or  = la . la $ V 2 %: lc_true %: V 1
lc_not = la $ V 1 %: lc_false %: lc_true

readStr :: String -> LamExpr
readStr = fromRight (error "internal") . readLazyK ""

ch_0, ch_1, ch_CR, ch_H, ch_e, ch_l, ch_o, ch_256 :: LamExpr
ch_0 = readStr $ shortChNum !! 0
ch_1 = readStr $ shortChNum !! 1
ch_LF = readStr $ shortChNum !! 10
ch_CR = readStr $ shortChNum !! 13
ch_H = readStr $ shortChNum !! (ord 'H')
ch_e = readStr $ shortChNum !! (ord 'e')
ch_l = readStr $ shortChNum !! (ord 'l')
ch_o = readStr $ shortChNum !! (ord 'o')
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

lc_nil, cons, car, cdr :: LamExpr
lc_nil = la . la $ V 2
cons = la . la . la $ V 1 %: V 3 %: V 2
car = la $ V 1 %: lc_true
cdr = la $ V 1 %: lc_false

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
        -> Maybe Int -- ^ ラムダ式が表す自然数。想定外は全て Nothing。
getChNum (L _ (L _ llexp)) = countF llexp
  where
    countF (V 1) = Just 0
    countF (App _ (V 2) e) = (+1) <$> countF e
    countF _ = Nothing
-- 1 = λfx.fx = λf.f (eta変換より) なので、個別に処理。
getChNum (L _ (V 1)) = Just 1
getChNum _ = Nothing

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
