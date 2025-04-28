module LazyKParts where

import Data.Char (chr, ord)
import Data.Default (Default(..))
import System.IO (isEOF, hFlush, hPutStr, hPutStrLn, stderr, stdout)

import LazyKCore (LamExpr(..), RedResult(..), IoInfo(..), ProgDot(..),
                  betaRed, forceProg, isPdMature, clearPd)

-- | expr を Scott encoding のリストとして扱い、全要素を出力 (遅延入力対応)
deconsLoop :: ProgDot   -- ^ 進捗dot用。beta簡約を実行した回数。
        -> Maybe Int    -- ^ 出力するbyte数を指定。Nothingなら無限。
        -> IoInfo       -- ^ 入力情報と出力関係のオプション
        -> LamExpr      -- ^ 出力すべき Scott encoding のリスト
        -> IO ()
deconsLoop _  (Just 0)  _     _    = return ()
deconsLoop pd countdown ioInf expr = do
    (car, cdr, pd', ioInf') <- decons ioInf pd expr
    (car_lam, pd'', ioInf'') <- infinit ioInf' pd' car
    let num = getChNum car_lam
    case num of
        Just n
            | n < 256 -> do
                onlyV ioInf'' $
                    hPutStrLn stderr $ show n ++ "(='" ++ [chr n] ++ "')"
                putChar $ chr n
                hFlush stdout
                deconsLoop pd'' (fmap (+(-1)) countdown) ioInf'' cdr
            | otherwise -> do
                onlyV ioInf'' $
                    hPutStrLn stderr $ "Reach EOF (" ++ show n ++ ")"
        _ -> hPutStrLn stderr $ "car is not number"

-- | expr を Scott encoding のリストとして扱い、car/cdrに分割 (遅延入力対応)
decons :: IoInfo     -- ^ 入力情報と出力関係のオプション
        -> ProgDot   -- ^ 進捗dot用。beta簡約を実行した回数。
        -> LamExpr   -- ^ 分割すべき Scott encoding のリスト
        -> IO (LamExpr, LamExpr, ProgDot, IoInfo)
decons ioInf d expr =
  case expr of
    L _ (App _ (App _ (V 1) car) cdr) -> return (car, cdr, d, ioInf)
    _ -> do
        reded <- betaRedInput ioInf d expr
        case reded of
            (RedProg d' _ expr', ioInf') -> decons ioInf' d' expr'
            ret@(RedStop d' ix expr', ioInf')
                -- 進捗dotの表示タイミングか、inputブロック。再帰で処理。
                | isPdMature 1 ioInf' d' || ix >= 0 ->
                    decons ioInf' d' expr'
                -- Lazy Kプログラムなら、scott encode の list を出力する筈。
                -- cons の形でなく、beta簡約も進まないのなら、エラー。
                | otherwise -> error $ "Invalid program: ret=" ++ show ret

-- | Beta簡約 (遅延入力対応)
betaRedInput :: IoInfo   -- ^ 入力情報と出力関係のオプション
            -> ProgDot   -- ^ 進捗dot用。beta簡約を実行した回数。
            -> LamExpr   -- ^ beta簡約対象のラムダ式
            -> IO (RedResult LamExpr, IoInfo)
betaRedInput ioInf d expr = do
    let ret = betaRed ioInf d expr
    -- case betaRedPar expr of
    case ret of
        RedProg pd ix expr'
            | isPdMature 1 ioInf pd -> do
                -- 返ってきた理由は、beta簡約の回数が基準に達したからだった。
                hPutStr stderr "."  -- 進捗dotの表示
                hFlush stderr
                -- 他の条件は、再帰の中でチェックする。
                (red, ioInf'') <- betaRedInput ioInf (clearPd 1 pd) expr'
                return (forceProg red, ioInf'')
            | ix < 0 -> do
                -- 遅延入力に当たらず、beta簡約が進んだ。
                -- putStrLn "---------------> RedProg minus"
                return (ret, ioInf)
            | otherwise -> do
                -- beta簡約が進んだが、遅延入力で止まった。
                -- putStrLn "---------------> RedProg Plus"
                ioInf' <- pollInput ix ioInf
                (red, ioInf'') <- betaRedInput ioInf' pd expr'
                return (forceProg red, ioInf'')
        RedStop pd ix _
            | isPdMature 1 ioInf pd -> do
                -- 返ってきた理由は、beta簡約の回数が基準に達したからだった。
                hPutStr stderr "."  -- 進捗dotの表示
                hFlush stderr
                betaRedInput ioInf (clearPd 1 pd) expr
            | ix < 0 -> do
                -- putStrLn "---------------> RedStop minus"
                return (RedStop pd ix expr, ioInf) -- 元のexprを使用。
            | otherwise -> do
                -- putStrLn "---------------> RedStop Plus"
                -- putStrLn . show $ ret
                ioInf' <- pollInput ix ioInf
                betaRedInput ioInf' pd expr    -- 元のexprを使用。

-- | 標準入力から指定番目まで取得 (blocking処理)
pollInput :: Int     -- ^ 何番目のbyteまで取得するか。0オリジン。
        -> IoInfo    -- ^ 入力情報と出力関係のオプション
        -> IO IoInfo -- ^ 新たに入力されたbyteを反映した IoInfo
pollInput ix (IoInfo _ input _ pd) = do
    IoInfo eof' add _ _ <- getNchar [] $ ix - length input + 1
    -- putStrLn $ "------> getNchar !! " ++ show (length input) ++ ".. = " ++ show add
    -- putStrLn $ "                " ++ show (input ++ add)
    return $ IoInfo eof' (input ++ add) False pd

-- | pollInput の補助関数。指定byte数を取得する。
getNchar :: [Int]     -- ^ pollInputでここまでに受信したbyte列。
        -> Int        -- ^ 取得すべき残りのbyte数。
        -> IO IoInfo
getNchar acc n
    | n <= 0 = return $ IoInfo False acc False def
    | otherwise = do
        eof <- isEOF
        if eof then return $ IoInfo True acc False def
              else do
                  c <- getChar  -- 実際の読込み。それまではblocking。
                  getNchar (acc ++ [ord c]) (n - 1)

-- | expr に可能な限りbeta簡約を再帰実行 (遅延入力対応)
infinit :: IoInfo -> ProgDot -> LamExpr -> IO (LamExpr, ProgDot, IoInfo)
infinit ioInf pd expr = do
    -- putStrLn $ "infinit : " ++ show ioInf ++ " : " ++ show expr ++ " <<<<<<"
    ret <- betaRedInput ioInf pd expr
    case ret of
        (RedProg pd' _  expr', ioInf') -> do
            -- putStrLn ("Prog: " ++ show ret)
            infinit ioInf' pd' expr'
        (RedStop pd' ix _   , ioInf')
            | isPdMature 1 ioInf' pd' ->
                error $ "Not Chuch Number" ++ show pd'
            | ix < 0 -> return (expr, pd', ioInf')
            | otherwise -> infinit ioInf' pd' expr

-- | 引数にbeta簡約済みの Church encoding の自然数を受取り、値を返す。
getChNum :: LamExpr  -- ^ beta簡約済みの Church encoding の自然数。
        -> Maybe Int -- ^ ラムダ式が表す自然数。想定外は全て Nothing。
getChNum (L _ (L _ llexp)) = countF llexp
  where
    countF (V 1) = Just 0
    countF (App _ (V 2) e) = (+1) <$> countF e
    countF _ = Nothing
-- 1 = λfx.fx = λf.f (eta変換より) なので、個別に処理。
getChNum (L _ (V 1)) = Just 1
getChNum _ = Nothing

-- | -vオプション指定時のみactを実行し、最後にstderrをflush
onlyV :: IoInfo -> IO () -> IO ()
onlyV ioInf act = if optV ioInf
    then do
        act
        hFlush stderr
    else return ()

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
