{- |
  Module      : LazyKParts
  Description : Lazy K特有の処理。IO周りの処理。
-}

module LazyKParts where

import Data.Char (chr, ord)
import Data.Default (Default(..))
import Numeric (showHex)
import System.CPUTime (getCPUTime)
import System.Exit (ExitCode(..))
import System.IO (isEOF, hFlush, hPutStr, hPutStrLn, stderr, stdout)
import Text.Parsec ((<|>), Parsec, char, many1, oneOf, parse)

import LamCalcCore (LamExpr(..), RedResult(..), IoInfo(..), ProgDot(..)
                , (%:), la, reduct, forceProg, isPdMature, incPd, clearPd
                , toNamedString, takeStringified
                , NameManager(..), PolicyKind(..)
                )
import LamCalcParts (getChNum, red_ccN)

-- | 純粋なラムダ式と、コンビネータ表現、それぞれの deconsLoop のsetup
deconsLoopLc, deconsLoopCc ::
               IoInfo       -- ^ 入力情報と出力関係のオプション
            -> ProgDot      -- ^ 進捗dot用。beta簡約を実行した回数。
            -> Maybe Int    -- ^ 出力するbyte数を指定。Nothingなら無限。
            -> LamExpr      -- ^ 出力すべき Scott encoding のリスト
            -> IO ExitCode  -- ^ プログラムの終了コード
deconsLoopLc = deconsLoop deconsLc toIntLc
deconsLoopCc = deconsLoop deconsCc toIntCc

{- | expr を Scott encoding のリストとして扱い、全要素を出力 (遅延入力対応)

リストを先頭からscanしながら表示する。以下のいずれの条件まで繰り返す。

* 256以上の数が現れる。(終了コードは、数値 - 256)
* scanした個数が出力最大数に達する。(終了コードは 0)

但し、consを分解する関数と、carを数値に変換する関数は、
入力として与えられるので、式の表現や、もっと言えば式であるかさえも
この関数は感知しない。
-}
deconsLoop :: (IoInfo -> ProgDot -> e -> IO (e, e, ProgDot, IoInfo))
                            -- ^ 式を car/cdr に分割する関数
            -> (IoInfo -> ProgDot -> e -> IO (Either String Int, ProgDot, IoInfo))
                            -- ^ 式(car)を数値に変換する関数
            -> IoInfo       -- ^ 入力情報と出力関係のオプション
            -> ProgDot      -- ^ 進捗dot用。beta簡約を実行した回数。
            -> Maybe Int    -- ^ 出力するbyte数を指定。Nothingなら無限。
            -> e            -- ^ 出力すべき Scott encoding のリスト
            -> IO ExitCode  -- ^ プログラムの終了コード
deconsLoop _      _     _     _  (Just 0)  _    = return ExitSuccess
deconsLoop decons toInt ioInf pd countdown expr = do
    (car, cdr, pd', ioInf') <- decons ioInf pd expr
    (num, pd'', ioInf'') <- toInt ioInf' pd' car
    case num of
        Right n
            | n < 256 -> do
                onlyV ioInf'' $ do
                    curTime <- getCPUTime
                    let sec = fromIntegral (curTime - startCPUTime ioInf)
                                                        / 1e12 :: Double
                    hPutStrLn stderr $
                        show n ++ "(=0x" ++ showHex n ")--'" ++ [chr n]
                         ++ "'  "++ show sec ++ " sec"
                putChar $ chr n
                hFlush stdout
                deconsLoop decons toInt ioInf'' pd''
                                                (fmap (+(-1)) countdown) cdr
            | otherwise -> do
                onlyV ioInf'' $
                    hPutStrLn stderr $ "Reach EOF (" ++ show n ++ ")"
                return $ if n == 256 then ExitSuccess
                                     else ExitFailure (n - 256)
        Left e -> do
            hPutStrLn stderr $ "car is not number : " ++ e
            return $ ExitFailure 1

-- | expr を Scott encoding のリストとして扱い、car/cdrに分割 (遅延入力対応)
deconsLc :: IoInfo   -- ^ 入力情報と出力関係のオプション
        -> ProgDot   -- ^ 進捗dot用。beta簡約を実行した回数。
        -> LamExpr   -- ^ 分割すべき Scott encoding のリスト
        -> IO (LamExpr, LamExpr, ProgDot, IoInfo)
deconsLc ioInf d expr =
  case expr of
    L _ (App _ (App _ (V 1) car) cdr) -> return (car, cdr, d, ioInf)
    _ -> do
        reded <- careIoInfo reduct ioInf d expr
        case reded of
            (RedProg d' _ expr', ioInf') -> deconsLc ioInf' d' expr'
            ret@(RedStop d' ix expr', ioInf')
                -- 進捗dotの表示タイミングか、inputブロック。再帰で処理。
                | isPdMature 1 ioInf' d' || ix >= 0 ->
                    deconsLc ioInf' d' expr'
                -- Lazy Kプログラムなら、scott encode の list を出力する筈。
                -- cons の形でなく、beta簡約も進まないのなら、エラー。
                | otherwise -> error $ "Invalid program: ret="
                                        ++ show (toNamedString def expr')
                                        ++ " = " ++ show ret

-- | 純粋なラムダ式(=App, V, L のみから成る)のChurch数から整数取得
toIntLc :: IoInfo
        -> ProgDot
        -> LamExpr
        -> IO (Either String Int, ProgDot, IoInfo)
toIntLc ioInf pd expr = do
    (car_lam, pd', ioInf') <- untilStopInput reduct ioInf pd expr
    return (getChNum car_lam, pd', ioInf')

-- | deconsLc のコンビネータ版。
-- expr を Scott encoding のリストとして扱い、car/cdrに分割 (遅延入力対応)
deconsCc :: IoInfo   -- ^ 入力情報と出力関係のオプション
        -> ProgDot   -- ^ 進捗dot用。beta簡約を実行した回数。
        -> LamExpr   -- ^ 分割すべき Scott encoding のリスト
        -> IO (LamExpr, LamExpr, ProgDot, IoInfo)
deconsCc ioInf d expr = return (car %: expr, cdr %: expr, d, ioInf)
  where
    car = Nm "S" %: Nm "I" %: (Nm "K" %: Nm "K")
    cdr = Nm "S" %: Nm "I" %: (Nm "K" %: (Nm "K" %: Nm "I"))

-- | コンビネータ表現のChurch数から、整数取得。
toIntCc :: IoInfo
        -> ProgDot
        -> LamExpr
        -> IO (Either String Int, ProgDot, IoInfo)
toIntCc ioInf pd expr = do
    -- (car_cc, pd', ioInf') <- untilStopInput red_ccN ioInf pd $ expr %: Nm "+1" %: V 0
    (car_cc, pd', ioInf') <- untilStopInput reduct ioInf pd $ expr %: Nm "+1" %: Num 0
    case car_cc of
        Num n -> return (Right n, pd', ioInf')
        V n -> return (Right n, pd', ioInf')
        e   -> return (Left $
                takeStringified $ toNamedString def{nmPolicy=PK_index} e
                        , pd', ioInf')

-- | RedResult を返す関数のIO周りの対応 (遅延入力対応)
--
-- 基本的には、RedResult を返す関数を1回だけ呼出すが、
-- 以下の場合には、対処の処理を実施後、再度呼出すことで処理を継続する。
--
--   - case-1. 入力プロミスの不足が発生: 補充の為のblockingと補充。
--   - case-2. 進捗dotの表示の為の中断が発生: 進捗dotを表示。
careIoInfo :: (Show e)
            => (IoInfo -> ProgDot -> e -> RedResult e)
            -> IoInfo   -- ^ 入力情報と出力関係のオプション
            -> ProgDot   -- ^ 進捗dot用。beta簡約を実行した回数。
            -> e   -- ^ 簡約対象のラムダ式
            -> IO (RedResult e, IoInfo)
careIoInfo f ioInf d expr = do
    ret <- case incPd 0 $ f ioInf d expr of
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
                (red, ioInf'') <- careIoInfo f ioInf (clearPd 1 pd) expr'
                return (forceProg red, ioInf'')
            | ix < 0 -> do
                -- 遅延入力に当たらず、簡約が進んだ。
                -- putStrLn $ "---------------> RedProg minus " ++ show expr'
                return (ret, ioInf)
            | otherwise -> do
                -- 簡約が進んだが、遅延入力で止まった。
                -- putStrLn $ "---------------> RedProg Plus " ++ show expr'
                ioInf' <- pollInput ix ioInf
                (red, ioInf'') <- careIoInfo f ioInf' pd expr'
                return (forceProg red, ioInf'')
        RedStop pd ix expr'
            | isPdMature 1 ioInf pd -> do
                -- 返ってきた理由は、beta簡約の回数が基準に達したからだった。
                hPutStr stderr "."  -- 進捗dotの表示
                hFlush stderr
                careIoInfo f ioInf (clearPd 1 pd) expr
            | ix < 0 -> do
                -- putStrLn $ "---------------> RedStop minus " ++ show expr'
                return (RedStop pd ix expr, ioInf) -- 元のexprを使用。
            | otherwise -> do
                -- putStrLn $ "---------------> RedStop Plus " ++ show expr'
                ioInf' <- pollInput ix ioInf
                careIoInfo f ioInf' pd expr    -- 元のexprを使用。

-- | 変化しなくなるまで、指定された関数の適用を繰り返す (遅延入力対応)
untilStopInput :: (Show e)
                => (IoInfo -> ProgDot -> e -> RedResult e)
                -> IoInfo   -- ^ 入力情報と出力関係のオプション
                -> ProgDot   -- ^ 進捗dot用。beta簡約を実行した回数。
                -> e   -- ^ 簡約対象のラムダ式
                -> IO (e, ProgDot, IoInfo)
untilStopInput f ioInf pd expr = do
    ret <- careIoInfo f ioInf pd expr
    case ret of
        (RedProg pd' _  expr', ioInf') -> do
            -- putStrLn ("Prog: " ++ show ret)
            untilStopInput f ioInf' pd' expr'
        (RedStop pd' ix _   , ioInf')
            | isPdMature 1 ioInf' pd' ->
                error $ "Not Chuch Number" ++ show pd'
            | ix < 0 -> return (expr, pd', ioInf')
            | otherwise -> untilStopInput f ioInf' pd' expr

-- | 標準入力から指定番目まで取得 (blocking処理)
pollInput :: Int     -- ^ 何番目のbyteまで取得するか。0オリジン。
        -> IoInfo    -- ^ 入力情報と出力関係のオプション
        -> IO IoInfo -- ^ 新たに入力されたbyteを反映した IoInfo
pollInput ix ioInf = do
    onlyV ioInf $
        hPutStrLn stderr $ "pollInput ix=" ++ show ix
    let lack = ix - length (inHist ioInf) + 1
    (eof', add) <- getNchar [] lack
    let newHist = if eof' && length add < lack
        then inHist ioInf ++ add ++ take (lack - length add) [256, 256..]
        else inHist ioInf ++ add
    onlyV ioInf $
        hPutStrLn stderr $ "  pollInput: eof =" ++ show eof'
                        ++ ", got len=" ++ show (length add)
                        ++ ", ix=" ++ show ix
    return $ ioInf { inEof = eof', inHist = newHist }

-- | pollInput の補助関数。指定byte数を取得する。
-- inputが EOF に達したかの情報も合わせて返却する。
getNchar :: [Int]     -- ^ getNcharでここまでに受信したbyte列。
        -> Int        -- ^ 取得すべき残りのbyte数。
        -> IO (Bool, [Int])
getNchar acc n
    | n <= 0 = return (False, acc)
    | otherwise = do
        eof <- isEOF
        if eof then return (True, acc)
              else do
                  c <- getChar  -- 実際の読込み。それまではblocking。
                  getNchar (acc ++ [ord c]) (n - 1)

-- | -vオプション指定時のみactを実行し、最後にstderrをflush
onlyV :: IoInfo -> IO () -> IO ()
onlyV ioInf act = if optV ioInf
    then do
        act
        hFlush stderr
    else return ()

jotI, jotK, jotS :: String
jotI = "11111111100000"
jotK = "11100"
jotS = "11111000"

-- | CCスタイルへの変換
--
-- 変換の対象は、IotaとJotスタイルの部分のみ
toCcStyle :: LamExpr -> LamExpr
toCcStyle (L _ lexp) = la $ toCcStyle lexp
toCcStyle (Nm "iota") = la $ V 1 %: Nm "S" %: Nm "K"
toCcStyle (App _ (Nm "iota") (Nm "iota")) = Nm "I"
toCcStyle (App _ (Nm "iota")
            (App _ (Nm "iota")
                (App _ (Nm "iota") (Nm "iota")))) = Nm "K"
toCcStyle (App _ (Nm "iota")
            (App _ (Nm "iota")
                (App _ (Nm "iota")
                    (App _ (Nm "iota") (Nm "iota"))))) = Nm "S"
toCcStyle (App _ x y) = toCcStyle x %: toCcStyle y
toCcStyle (Jot _ j) = jotToCcStyle j
toCcStyle expr = expr

jotToCcStyle :: String -> LamExpr
jotToCcStyle jot = case parse jexprs "jotToCcStyle" $ jotToCcStr jot of
    Left _ -> foldl jotToCc (Nm "I") jot
    Right e -> e

-- | Jotスタイルの式をCCの予約関数とラムダ抽象に変換
--
-- jotToCcStr で Left の場合、ラムダ抽象混じりで変換する。
jotToCc :: LamExpr -> Char -> LamExpr
jotToCc e '0' = e %: Nm "S" %: Nm "K"
jotToCc e '1' = la . la $ e %: V 2 %: V 1
jotToCc e _   = error $ "Internal Error: Invalid Jot: " ++ show e

jexprs, jexpr :: Parsec String u LamExpr

jexprs = foldl1 (%:) <$> many1 jexpr

jexpr = Nm . (:[]) <$> oneOf "SKI"
    <|> char '1' *> return (%:) <*> jexpr <*> jexpr

-- | Jotスタイルの文字列をCCスタイルの文字列に変換を試行。
--
-- 変換できればRight値、出来なければLeft値を返す。
jotToCcStr :: String -> String
jotToCcStr jot = case jot of
    '1':('1':('1':('1':('1':('1':('1':('1':('1':
            ('0':('0':('0':('0':('0':x))))))))))))) -> ('I':) $ jotToCcStr x
    '1':('1':('1':('0':('0':x))))                   -> ('K':) $ jotToCcStr x
    '1':('1':('1':('1':('1':('0':('0':('0':x))))))) -> ('S':) $ jotToCcStr x
    '1':y -> '1' : jotToCcStr y
    x:y -> x : jotToCcStr y  -- Errorだが、error処理はparse側に押し付ける
    "" -> ""

-- | Iotaスタイルへの変換
--
-- 変換するのは、あくまで、S, K, I のみ。
-- Jotスタイルや、変数、入力promise等は、変更しない。
toIotaStyle :: LamExpr -> LamExpr
toIotaStyle (L _ lexp) = la $ toIotaStyle lexp
toIotaStyle (App _ x y) = toIotaStyle x %: toIotaStyle y
toIotaStyle (Nm "I") = Nm "iota" %: Nm "iota"
toIotaStyle (Nm "K") = Nm "iota" %: (Nm "iota" %: (Nm "iota" %: Nm "iota"))
toIotaStyle (Nm "S") = Nm "iota" %: (Nm "iota" %: (Nm "iota" %:
                                                   (Nm "iota" %: Nm "iota")))
toIotaStyle expr = expr

-- | Jotスタイルへの変換
--
-- 変換するのは、あくまで、S, K, I のみ。
-- Iotaスタイルや、変数、入力promise等は、変更しない。
toJotStyle :: LamExpr -> LamExpr
toJotStyle (L _ lexp) = la $ toJotStyle lexp
toJotStyle (App _ x y) = case (jotX, jotY) of
    (Jot lx jx, Jot ly jy) -> Jot (1 + lx + ly) $ '1':(jx ++ jy)
    _ -> jotX %: jotY
  where
    jotX = toJotStyle x
    jotY = toJotStyle y
toJotStyle (Nm "I") = Jot (length jotI) jotI
toJotStyle (Nm "K") = Jot (length jotK) jotK
toJotStyle (Nm "S") = Jot (length jotS) jotS
toJotStyle expr = expr
