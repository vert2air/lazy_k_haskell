import Data.Char (ord)
import Data.Default (Default(def))

import LamCalcCore (LamExpr(..), (%:), la, abstElim, toNamedString, comple
            , takeStringified)
import LamCalcParts (if_then_else
            , ch_0, ch_1, ch_256, is_zero, cn_plus, cn_mult, is_eq
            , lc_nil, cons, car, cdr, is_eq_LF, is_eq_r2
            , y_comb, shortChNum, readStr)

{- |
  Description : Lazy K ファイルの作成のサンプルコード
-}
getPutLine :: LamExpr
getPutLine =
    y_comb %:
    (la
        (la $
            if_then_else
                %: (is_eq_LF %: (car %: V 1))
                %: (cons %: ch_256 %: lc_nil)
                %: (cons
                    %: (car %: V 1)
                    %: (V 2 %: (cdr %: V 1))
                    )
        )
    )

addStrHead :: String -> LamExpr -> LamExpr
addStrHead str expr = foldr addChHead expr str

addChHead :: Char -> LamExpr -> LamExpr
addChHead ch expr = cons %: (readStr $ shortChNum !! (ord ch)) %: expr

-- | stdinのLF判定高速化と、stdin入力前にprefixが表示されるのを抑止する例。
promptResp_faster_prefix :: LamExpr
promptResp_faster_prefix = la $
    addStrHead "What's your name?\n>" $
    cons
        %: (cn_plus
            %: (readStr $ shortChNum !! (ord 'H'))
            %: (cn_mult %: (car %: (V 1)) %: ch_0)) -- 無理矢理 input参照
        %: ((addStrHead "i, ") $
            y_comb %: (la . la $
                if_then_else
                    %: (is_eq_LF %: (car %: V 1))   -- 高速比較
                    %: addStrHead "!\n" (cons %: ch_256 %: lc_nil)
                    %: (cons
                        %: (car %: V 1)
                        %: (V 2 %: (cdr %: V 1))
                        )
            )
            %: (V 1))

-- 入力の 1 byte目と 2 byte目を足したものを出力
add :: LamExpr
add = la (
    cons
        %: ( cn_plus %: (car%:V(1)) %: (car%:(cdr%:V(1))) )
        %: ( cons %: ch_256 %: lc_nil)
    )


-- 入力の 1 byte目と 2 byte目が等しいなら 1、でなければ 0 を出力
-- 7, 7 で、5分掛かった。ここまでは、1増やすと約3倍になる感じ。
eq :: LamExpr
eq = la ( cons
            %: ( if_then_else %:
                (is_eq %: (car%:V(1)) %: (car%:(cdr%:V(1)))) %:
                ch_1 %: ch_0
              )
            %: ( cons %: ch_256 %: lc_nil)
            )


-- 入力の 1 byte目と 2 byte目が等しいなら 1、でなければ 0 を出力
-- 7, 7 ぐらいだと、eq より大分速い。
eq_r2 :: LamExpr
eq_r2 = la( cons %:
              ( if_then_else %:
                (is_eq_r2 %: (car%:V(1)) %: (car%:(cdr%:V(1)))) %:
                ch_1 %: ch_0
              ) %:
              ( cons %: ch_256 %: lc_nil)
              )

-- 入力byteの累積和を求める。途中に0が出た時点で止める。
-- sum_to_0 = (init : array-of-input)
sum_to_0 :: LamExpr
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
    -- takeStringified . toNamedString def $ input
    -- takeStringified . toNamedString def . comple abstElim $ input
    putStrLn . takeStringified . toNamedString def
        . comple abstElim . comple abstElim $ input

main :: IO ()
main = do
    -- asm getPutLine
    asm promptResp_faster_prefix
