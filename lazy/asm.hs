import Data.Char (ord)
import Data.Default (Default(def))
import Data.Either (fromRight)

import LazyKCore (LamExpr(..), (%:), la, readLazyK, abstElim, toNamedString,
                  comple, takeStringified)
-- import LazyKParts (shortChNum)
import LamCalcParts (lc_true, lc_false, if_then_else, lc_and, lc_or, lc_not
          , ch_0, ch_1, ch_CR, ch_H, ch_e, ch_l, ch_o, ch_256
          , is_zero, cn_succ, cn_plus, cn_mult, cn_pred, cn_minus, is_eq
          , lc_nil, cons, car, cdr
          , diff_1_pair, cn_pred_r2, cn_minus_r2, is_eq_r2
          , y_comb, shortChNum)

-- getPutLine input
getPutLine = y_comb %:
    (la
        (la $
            if_then_else
                %: (eq_r2 %: (car %: V 1) %: ch_CR)
                %: ch_256
                %: (cons
                    %: (car %: V 1)
                    %: (V 2 %: (cdr %: V 1))
                    )
        )
    )

{-
foo (buf:input) =
    if_then_else
        %: (car input == ch_CR)
        %: ("Hello, " + buf + "!\n\256")
        %: (foo (buf + car input : cdr input))

foo args = if_then_else %: is_eq (car %: (cdr %: args))
    (cons %: ch_H %: (cons %: ch_e %: (cons %: ch_l %: (cons %: ch_l %: (cons %: ch_o %: lc_nil)))))

hello = 
    (cons %: ch_H %: (cons %: ch_e %: (cons %: ch_l %: (cons %: ch_l %: (cons %: ch_o %: lc_nil)))))
-}
{-
foo 'Your name?\n>\n' input
prompt_resp
-}

-- 入力の 1 byte目と 2 byte目を足したものを出力
add = la (
    cons
        %: ( cn_plus %: (car%:V(1)) %: (car%:(cdr%:V(1))) )
        %: ( cons %: ch_256 %: lc_nil)
    )


-- 入力の 1 byte目と 2 byte目が等しいなら 1、でなければ 0 を出力
-- 7, 7 で、5分掛かった。ここまでは、1増やすと約3倍になる感じ。
eq = la ( cons
            %: ( if_then_else %:
                (is_eq %: (car%:V(1)) %: (car%:(cdr%:V(1)))) %:
                ch_1 %: ch_0
              )
            %: ( cons %: ch_256 %: lc_nil)
            )


-- 入力の 1 byte目と 2 byte目が等しいなら 1、でなければ 0 を出力
-- 7, 7 ぐらいだと、eq より大分速い。
eq_r2 = la( cons %:
              ( if_then_else %:
                (is_eq_r2 %: (car%:V(1)) %: (car%:(cdr%:V(1)))) %:
                ch_1 %: ch_0
              ) %:
              ( cons %: ch_256 %: lc_nil)
              )

-- 入力byteの累積和を求める。途中に0が出た時点で止める。
sum_to_0 = la(
    (y_comb %:
      la(
        la(
          if_then_else %: (is_zero %: (car %: (cdr %: V(1)))) %:
            (cons %: (car %: V(1)) %: (cons %: ch_256 %: lc_nil)) %:
            (V(2) %:
              (cons %:
                (cn_plus %: (car %: V(1)) %: (car %: (cdr %: V(1)))) %:
                (cdr %: (cdr %: V(1)))
              )
            )
        )
      )
    ) %:
    (cons %: ch_0 %: V(1))
  )

asm :: LamExpr -> IO ()
asm input = do
    takeStringified . toNamedString def $ input
    takeStringified . toNamedString def . comple abstElim $ input
    takeStringified . toNamedString def . comple abstElim . comple abstElim $ input

-- echo add.abst_elim.toCC
-- echo eq.abst_elim.toCC
-- echo eq_r2.abst_elim.toCC
-- echo sum_to_0.abst_elim.toCC
main :: IO ()
main = do
    asm getPutLine
