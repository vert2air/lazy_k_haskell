module GoedelNum where

import Debug.Trace (trace)
import qualified Data.Map as M (Map, fromList, lookupLE)

import LamCalcCore (LamExpr(..), (%:))

mk_rank_sum :: Int -> Integer
mk_rank_sum k
    | k < 2     = [0, 3] !! k
    | otherwise = let k_1 = map mk_rank_sum [1..k-1]
                  in sum . zipWith (*) k_1 . reverse $ k_1

{- | 変数の個数毎のGoedel数の個数

含まれる変数の個数が n 個のCCスタイルの式の
最初の式のGoedel数が `rank_sum !! n`

変数が0個の場合、goedel数の個数も 0個。
変数が1個の場合、goedel数は 1 から 3 までの 3個。

>>> take 10 rank_sum
[0,3,9,54,405,3402,30618,288684,2814669,28146690]
-}
rank_sum :: [Integer]
rank_sum = map mk_rank_sum [0..]

{- | 変数の個数毎のgoedel番号の個数を累積和にしたもの

>>> take 10 rank_cum
[0,3,12,66,471,3873,34491,323175,3137844,31284534]
-}
rank_cum :: [Integer]
rank_cum = (0:) $ zipWith (+) rank_cum $ drop 1 rank_sum

-- gn_struct :: [(Integer, (Int, Int))]
-- gn_struct = zip gn_struct_bound gn_struct_pair

gn_struct :: [(Integer, (Integer, Int, Int))]
gn_struct = zip gn_struct_ix_bound gn_struct_ix_pair

{- | gn_struct_bound と対応して、変数の個数の組合せ

0番目は、変数が 1 個で、まだ関数適用がないので、取り合えず (1, 0) としておく。
-}
gn_struct_pair :: [(Int, Int)]
gn_struct_pair = ((1, 0):) . concat $
        map (\r -> map (\n -> (n, r - n)) [1..r - 1]) [1..]

{- | gn_struct_ix_bound と対応して、以下のtripleのリストを生成
  (関数適用の関数部が何番目か, 関数部の変数数, 引数部の変数数)

0番目は、変数が 1 個で、まだ関数適用がないので、取り合えず (0, 1, 0) としておく。

>>> gn_struct_ix_pair !! 0  -- 足して1は分解できないが、形式上置いておく。
(0,1,0)
>>> gn_struct_ix_pair !! 1  -- 足して2は、(1,1) のみ。1個は、3パターン
(0,1,1)
>>> gn_struct_ix_pair !! 2
(1,1,1)
>>> gn_struct_ix_pair !! 3
(2,1,1)
>>> gn_struct_ix_pair !! 4  -- 足して3は、(1,2) と (2,1)。
(0,1,2)
>>> gn_struct_ix_pair !! 5  -- 足して3は、(1,2) と (2,1)。
(1,1,2)
>>> gn_struct_ix_pair !! 6  -- 足して3は、(1,2) と (2,1)。
(2,1,2)
>>> gn_struct_ix_pair !! 7  --   (2,1) は、f側が 9個 のバリエーション。
(0,2,1)
>>> gn_struct_ix_pair !! 8
(1,2,1)
>>> gn_struct_ix_pair !! 9
(2,2,1)
>>> gn_struct_ix_pair !! 10
(3,2,1)
>>> gn_struct_ix_pair !! 11
(4,2,1)
>>> gn_struct_ix_pair !! 12
(5,2,1)
>>> gn_struct_ix_pair !! 13
(6,2,1)
>>> gn_struct_ix_pair !! 14
(7,2,1)
>>> gn_struct_ix_pair !! 15
(8,2,1)

>>> gn_struct_ix_pair !! 16  -- 足して4は、(1,3), (2,2), (3,1)。
(0,1,3)
>>> gn_struct_ix_pair !! 17
(1,1,3)
>>> gn_struct_ix_pair !! 18
(2,1,3)

>>> gn_struct_ix_pair !! 19  --   (2,2) は、f側が 9個 のバリエーション。
(0,2,2)
>>> gn_struct_ix_pair !! 20
(1,2,2)

>>> gn_struct_ix_pair !! 28 --   (3,1) は、f側が 0, 1, 2 のバリエーション。
(0,3,1)
>>> gn_struct_ix_pair !! 29
(1,3,1)
>>> gn_struct_ix_pair !! 30
(2,3,1)
-}
gn_struct_ix_pair :: [(Integer, Int, Int)]
gn_struct_ix_pair = ((0, 1, 0):) . concat . concat $
    flip map [1..] $ \r ->
        flip map [1..r-1] $ \n ->
            flip map [1..(rank_sum !! n)] $ \i ->
                (i - 1, n, r - n)


{- | 最上位の関数適用の関数と引数に含まれる変数の個数の組み合わせが変わる境界値

最初の要素は、ゲーデル数が 0　オリジンなので 0。
2番目の要素は、変数が 1 個の場合の組み合わせ数 3。
-}
gn_struct_bound :: [Integer]
gn_struct_bound = (0:) . (rank_sum!!1:) $
                                    map (calc . (gn_struct_pair !!)) [1..]
  where
    calc (f, a) = rank_cum !! (f + a - 1) + off f (f + a)
    off f r = let r_1 = drop 1 . take r $ rank_sum
              in sum . take f . zipWith (*) r_1 . reverse $ r_1

{- | 最上位の関数適用の関数と引数に含まれる変数の個数の組み合わせが変わる境界値

最初の要素は、ゲーデル数が 0　オリジンなので 0。
2番目の要素は、変数が 1 個の場合の組み合わせ数 3。

>>> gn_struct_ix_bound !! 0  -- (0,1,0)足して1は分解できないが、形式上置いておく。
0
>>> gn_struct_ix_bound !! 1  -- (0,1,1)足して2は、(1,1) のみ。3～
3
>>> gn_struct_ix_bound !! 2 -- (1,1,1)
6
>>> gn_struct_ix_bound !! 3 -- (2,1,1)
9
>>> gn_struct_ix_bound !! 4  -- (0,1,2)足して3は、(1,2) と (2,1)。
12
>>> gn_struct_ix_bound !! 5  -- (1,1,2)足して3は、(1,2) と (2,1)。
21
>>> gn_struct_ix_bound !! 6  -- (2,1,2)足して3は、(1,2) と (2,1)。
30
>>> gn_struct_ix_bound !! 7  -- (0,2,1)  (2,1) は、f側が 9個 のバリエーション。
39
>>> gn_struct_ix_bound !! 8 -- (1,2,1)
42
>>> gn_struct_ix_bound !! 9 -- (2,2,1)
45
>>> gn_struct_ix_bound !! 14 -- (7,2,1)
60
>>> gn_struct_ix_bound !! 15 -- (8,2,1)
63
>>> gn_struct_ix_bound !! 16  -- (0,1,3)足して4は、(1,3), (2,2), (3,1)。
66
>>> gn_struct_ix_bound !! 17 -- (1,1,3)
120
>>> gn_struct_ix_bound !! 18 -- (2,1,3)
174
>>> gn_struct_ix_bound !! 19  -- (0,2,2)  (2,2) は、f側が 9個 のバリエーション。
228
-}
gn_struct_ix_bound :: [Integer]
-- gn_struct_ix_bound = (0:) . (rank_sum!!1:) $
--                                    map (calc . (gn_struct_ix_pair !!)) [1..]
gn_struct_ix_bound = map (calc . (gn_struct_ix_pair !!)) [0..]
  where
    calc (i, f, a) = rank_cum !! (f + a - 1)  -- f+a個の変数を使うGoedel数の先頭。
                  + off f (f + a)   -- (1,f+a-1),(2,f+a-2)..(f-1,a+1)までの個数。
                  + (rank_sum !! a) * fromIntegral i  -- (f,a) の中で、i対応
    off f r = let r_1 = drop 1 . take r $ rank_sum
              in sum . take (f - 1) . zipWith (*) r_1 . reverse $ r_1

{- | Goedel数 gn の式が何個の変数から成るか

r は再帰用なので、呼出し時は、0 or 1 を指定すること。

>>> cover_rank 0 2
1
>>> cover_rank 1 2
1
>>> cover_rank 0 11
2
>>> cover_rank 0 65
3
-}
cover_rank :: Int -> Integer -> Int
cover_rank r gn = if gn < rank_cum !! r
                    then r
                    else cover_rank (r + 1) gn

{- | 変数 r 個の式の処理に必要な、gn_struct の個数

Goedel数からCC式への変換は、
-g 323_174 (=``````sssssss)なら、そこそこのレスポンスだが、
-g 323_175 (=`i`i`i`i`i`i`ii)でも返事が来なくなる。
binSearch で M.Map を組み上げる処理が重過ぎるようになるのか？
feature_fast_goedel は設計に無理があるようだ。

>>> map cover_struct [1..8]
[1,4,16,82,553,4426,38917,362092]
-}
cover_struct :: Int -> Integer
cover_struct n = (1+) $ sum $ flip map [1..n] $ \r ->
                          sum $ flip map [1..r-1] $ \f ->
                              rank_sum !! f

goedel_to_expr :: Integer -> LamExpr
goedel_to_expr gn = g2e_aux (decomp_map gn) gn

decomp_map :: Integer -> M.Map Integer (Integer, Int, Int)
decomp_map gn = binSearch o_struct
  where
    o_rank = cover_rank 1 gn
    o_struct = cover_struct o_rank

binSearch :: Integer -> M.Map Integer (Integer, Int, Int)
binSearch os = M.fromList $ take (fromIntegral os) gn_struct

g2e_aux :: M.Map Integer (Integer, Int, Int) -> Integer -> LamExpr
g2e_aux _ 0 = Nm "I"
g2e_aux _ 1 = Nm "K"
g2e_aux _ 2 = Nm "S"
g2e_aux decomp gn = g2e_aux decomp f_gn %: g2e_aux decomp o_gn
  where
    (f_gn, o_gn) = decomp_gn decomp gn

{- | Goedel数を、最上位の関数適用の位置で分割

>>> let decomp = M.fromList $ take 500 gn_struct
>>> decomp_gn decomp 12   -- `i`ii を i と `ii に分割
(0,3)
>>> decomp_gn decomp 39   -- ``iii を `ii と i に分割
(3,0)
>>> decomp_gn decomp 66   -- `i`i`ii を i と `i`ii に分割
(0,12)
-}
decomp_gn :: M.Map Integer (Integer, Int, Int) -> Integer -> (Integer, Integer)
decomp_gn decomp gn = (f_gn, o_gn)
  where
    (top, (f_ord, f_cnt, o_cnt)) = maybe (error "Inner Error: decomp_gn") id $
                                    M.lookupLE gn decomp
    o_ord = gn - top
    f_gn = fromIntegral f_ord + rank_cum !! (f_cnt - 1)
    o_gn = o_ord              + rank_cum !! (o_cnt - 1)

expr_to_goedel :: LamExpr -> (Integer, Int)
expr_to_goedel (Nm "I") = (0, 1)
expr_to_goedel (Nm "K") = (1, 1)
expr_to_goedel (Nm "S") = (2, 1)
expr_to_goedel (App _ f o) = (f_ord_in_same_len * rank_sum !! o_cnt
                            + o_ord_in_same_len + gn_struct_bound !! grp_idx
                            , e_cnt)
  where
    (f_gn, f_cnt) = expr_to_goedel f
    (o_gn, o_cnt) = expr_to_goedel o
    f_ord_in_same_len = f_gn - rank_cum !! (f_cnt - 1)
    o_ord_in_same_len = o_gn - rank_cum !! (o_cnt - 1)
    e_cnt = f_cnt + o_cnt
    grp_idx = (e_cnt - 1) * (e_cnt - 2) `div` 2 + f_cnt
expr_to_goedel _ = (-1, -1)
