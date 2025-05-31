module GoedelNum where

import Control.Monad (forM_)
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
-}
rank_sum :: [Integer]
rank_sum = map mk_rank_sum [0..]

-- | 変数の個数毎のgoedel番号の個数を累積和にしたもの
rank_cum :: [Integer]
rank_cum = (0:) $ zipWith (+) rank_cum $ drop 1 rank_sum

gn_struct :: [(Integer, (Int, Int))]
gn_struct = zip gn_struct_bound gn_struct_pair

{- | gn_struct_bound と対応して、変数の個数の組合せ

0番目は、変数が 1 個で、まだ関数適用がないので、取り合えず (1, 0) としておく。
-}
gn_struct_pair :: [(Int, Int)]
gn_struct_pair = ((1, 0):) . concat $
        map (\r -> map (\n -> (n, r - n)) [1..r - 1]) [1..]

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

-- | Goedel数 gn の式が何個の変数から成るか
--
-- r は再帰用なので、呼出し時は、0 or 1 を指定すること。
cover_rank :: Int -> Integer -> Int
cover_rank r gn = if gn < rank_sum !! r
                    then r
                    else cover_rank (r + 1) gn

-- | 変数 r 個の式の処理に必要な、gn_struct の個数
cover_struct :: Int -> Int
cover_struct r = foldl (+) 0 [0..r]

goedel_to_expr :: Integer -> LamExpr
goedel_to_expr gn = g2e_aux (decomp_map gn) gn

decomp_map :: Integer -> M.Map Integer (Int, Int)
decomp_map gn = binSearch o_struct
  where
    o_rank = cover_rank 1 gn
    o_struct = cover_struct o_rank

binSearch :: Int -> M.Map Integer (Int, Int)
binSearch os = M.fromList $ take os gn_struct

g2e_aux :: M.Map Integer (Int, Int) -> Integer -> LamExpr
g2e_aux _ 0 = Nm "I"
g2e_aux _ 1 = Nm "K"
g2e_aux _ 2 = Nm "S"
g2e_aux decomp gn = g2e_aux decomp f_gn %: g2e_aux decomp o_gn
  where
    (f_gn, o_gn) = decomp_gn decomp gn

decomp_gn :: M.Map Integer (Int, Int) -> Integer -> (Integer, Integer)
decomp_gn decomp gn = (f_gn, o_gn)
  where
    (top, (f_cnt, o_cnt)) = maybe (error "Inner Error: decomp_gn") id $
                                    M.lookupLE gn decomp
    renum = gn - top
    (f_ord, o_ord) = renum `divMod` (rank_sum !! o_cnt)
    f_gn = f_ord + rank_cum !! (f_cnt - 1)
    o_gn = o_ord + rank_cum !! (o_cnt - 1)

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

main :: IO ()
main = do
    forM_ [0..10] $ \n -> do
        putStrLn $ show (n, rank_sum !! n)
        putStrLn $ show (n, rank_cum !! n)
    forM_ [0..25] $ \n -> do
        putStrLn $ show (n, gn_struct !! n)
    forM_ [0..50] $ \n -> do
        putStrLn $ show (n, goedel_to_expr n)
