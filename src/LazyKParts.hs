module LazyKParts where

import Data.Char (chr, ord)
import Data.Default (Default(..))
import System.IO (isEOF, hFlush, hPutStr, hPutStrLn, stderr, stdout)

import LamCalcCore (LamExpr(..), RedResult(..), IoInfo(..), ProgDot(..)
                , reduct, forceProg, isPdMature, incPd, clearPd, toNamedString)
import LamCalcParts (getChNum)

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
        reded <- reductInput ioInf d expr
        case reded of
            (RedProg d' _ expr', ioInf') -> decons ioInf' d' expr'
            ret@(RedStop d' ix expr', ioInf')
                -- 進捗dotの表示タイミングか、inputブロック。再帰で処理。
                | isPdMature 1 ioInf' d' || ix >= 0 ->
                    decons ioInf' d' expr'
                -- Lazy Kプログラムなら、scott encode の list を出力する筈。
                -- cons の形でなく、beta簡約も進まないのなら、エラー。
                | otherwise -> error $ "Invalid program: ret="
                                        ++ show (toNamedString def expr')
                                        ++ " = " ++ show ret

-- | Beta/Eta簡約 (遅延入力対応)
reductInput :: IoInfo   -- ^ 入力情報と出力関係のオプション
            -> ProgDot   -- ^ 進捗dot用。beta簡約を実行した回数。
            -> LamExpr   -- ^ 簡約対象のラムダ式
            -> IO (RedResult LamExpr, IoInfo)
reductInput ioInf d expr = do
    let ret' = reduct ioInf d expr
    let ret'' = incPd 0 ret'
    ret <- case ret'' of
        op@(RedProg pd ixp ep)
            | isPdMature 0 ioInf pd -> do
                hPutStr stderr "*"  -- 進捗dotの表示
                hFlush stderr
                return $ RedProg (clearPd 0 pd) ixp ep
            | otherwise -> return op
        os@(RedStop pd ixs es)
            | isPdMature 0 ioInf pd -> do
                hPutStr stderr "*"  -- 進捗dotの表示
                hFlush stderr
                return $ RedStop (clearPd 0 pd) ixs es
            | otherwise -> return os
    case ret of
        RedProg pd ix expr'
            | isPdMature 1 ioInf pd -> do
                -- 返ってきた理由は、beta簡約の回数が基準に達したからだった。
                hPutStr stderr "."  -- 進捗dotの表示
                hFlush stderr
                -- 他の条件は、再帰の中でチェックする。
                (red, ioInf'') <- reductInput ioInf (clearPd 1 pd) expr'
                return (forceProg red, ioInf'')
            | ix < 0 -> do
                -- 遅延入力に当たらず、簡約が進んだ。
                -- putStrLn "---------------> RedProg minus"
                return (ret, ioInf)
            | otherwise -> do
                -- 簡約が進んだが、遅延入力で止まった。
                -- putStrLn "---------------> RedProg Plus"
                ioInf' <- pollInput ix ioInf
                (red, ioInf'') <- reductInput ioInf' pd expr'
                return (forceProg red, ioInf'')
        RedStop pd ix _
            | isPdMature 1 ioInf pd -> do
                -- 返ってきた理由は、beta簡約の回数が基準に達したからだった。
                hPutStr stderr "."  -- 進捗dotの表示
                hFlush stderr
                reductInput ioInf (clearPd 1 pd) expr
            | ix < 0 -> do
                -- putStrLn "---------------> RedStop minus"
                return (RedStop pd ix expr, ioInf) -- 元のexprを使用。
            | otherwise -> do
                -- putStrLn "---------------> RedStop Plus"
                -- putStrLn . show $ ret
                ioInf' <- pollInput ix ioInf
                reductInput ioInf' pd expr    -- 元のexprを使用。

-- | 標準入力から指定番目まで取得 (blocking処理)
pollInput :: Int     -- ^ 何番目のbyteまで取得するか。0オリジン。
        -> IoInfo    -- ^ 入力情報と出力関係のオプション
        -> IO IoInfo -- ^ 新たに入力されたbyteを反映した IoInfo
pollInput ix (IoInfo _ input _ pd sgn) = do
    IoInfo eof' add _ _ _ <- getNchar [] $ ix - length input + 1
    -- putStrLn $ "------> getNchar !! " ++ show (length input) ++ ".. = " ++ show add
    -- putStrLn $ "                " ++ show (input ++ add)
    return $ IoInfo eof' (input ++ add) False pd sgn

-- | pollInput の補助関数。指定byte数を取得する。
--
-- 入力に関するフィールド以外は呼び出し側で上書きするので、
-- ここではdefault値等を設定しておけばよ良い。
getNchar :: [Int]     -- ^ pollInputでここまでに受信したbyte列。
        -> Int        -- ^ 取得すべき残りのbyte数。
        -> IO IoInfo
getNchar acc n
    | n <= 0 = return $ IoInfo False acc False def 'λ'
    | otherwise = do
        eof <- isEOF
        if eof then return $ IoInfo True acc False def 'λ'
              else do
                  c <- getChar  -- 実際の読込み。それまではblocking。
                  getNchar (acc ++ [ord c]) (n - 1)

-- | expr に可能な限りbeta/eta簡約を再帰実行 (遅延入力対応)
infinit :: IoInfo -> ProgDot -> LamExpr -> IO (LamExpr, ProgDot, IoInfo)
infinit ioInf pd expr = do
    -- putStrLn $ "infinit : " ++ show ioInf ++ " : " ++ show expr ++ " <<<<<<"
    ret <- reductInput ioInf pd expr
    case ret of
        (RedProg pd' _  expr', ioInf') -> do
            -- putStrLn ("Prog: " ++ show ret)
            infinit ioInf' pd' expr'
        (RedStop pd' ix _   , ioInf')
            | isPdMature 1 ioInf' pd' ->
                error $ "Not Chuch Number" ++ show pd'
            | ix < 0 -> return (expr, pd', ioInf')
            | otherwise -> infinit ioInf' pd' expr

-- | -vオプション指定時のみactを実行し、最後にstderrをflush
onlyV :: IoInfo -> IO () -> IO ()
onlyV ioInf act = if optV ioInf
    then do
        act
        hFlush stderr
    else return ()
