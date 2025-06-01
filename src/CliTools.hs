module CliTools where

import Data.Default (Default(..))
import Data.Maybe (mapMaybe)
import System.Console.GetOpt (OptDescr(..), ArgDescr(..), ArgOrder(..)
                            , getOpt, usageInfo)
import System.Environment (getArgs, lookupEnv)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

import LamCalcCore (LamExpr(..), NameManager(..), PolicyKind(..), readLazyK)

data CommonFlag = ArgExpr String
            | ArgStyleUnlam Bool
            | ArgPolicy PolicyKind
            | ArgPool String
            | ArgLamSign Char
            | ArgCmdSpecNo  Int -- ^ 何番目のコマンド特有オプションか(引数無し)
            | ArgCmdSpecReq Int String          -- ^ ArgCmdSpecNoの引数必須版
            | ArgCmdSpecOpt Int (Maybe String)  -- ^ ArgCmdSpecNoの引数任意版
    deriving (Show)

-- | コマンド共通オプション
commonOptions :: [OptDescr CommonFlag]
commonOptions = 
    -- 出力に関するoption
    [ Option ['c'] ["CC"]    (NoArg (ArgStyleUnlam False)) "CC style (default)"
    , Option ['u'] ["Unlambda"] (NoArg (ArgStyleUnlam True)) "Unlambda style"
    , Option ['i'] ["policy-index"]      (NoArg (ArgPolicy PK_index))
                                    "Use de Bruijn Index instead of name"
    , Option ['l'] ["policy-level"]      (NoArg (ArgPolicy PK_level))
                                    "Assign names depending on Lambda depth"
    , Option ['m'] ["policy-minimum"]    (NoArg (ArgPolicy PK_minimum))
                                    "Use minimum names (default)"
    , Option ['s'] ["policy-single-use"] (NoArg (ArgPolicy PK_single_use))
                                    "Assign unique name for each lambda"
    , Option ['p'] ["pool"] (ReqArg ArgPool "var. names")
                                    "Pool of named var. (default='xyzabcd...')"
    , Option ['S'] ["lambda-sign"] (ReqArg (ArgLamSign . (!!0)) "char")
                                    "Abstraction sign (default=Greek lambda)"
    -- 入力の式の直接指定
    , Option ['e'] ["expr"] (ReqArg ArgExpr "Expression")
                                    "Lambda expression to operate"
    ]

-- | コマンド個別のオプション情報を、CommonFlag型に変換
toCmnFlag :: [OptDescr a] -> [OptDescr CommonFlag]
toCmnFlag = map (\(i, opt) -> case opt of
    Option s l (NoArg  _   ) d -> Option s l (NoArg  (ArgCmdSpecNo  i)   ) d
    Option s l (ReqArg _ od) d -> Option s l (ReqArg (ArgCmdSpecReq i) od) d
    Option s l (OptArg _ od) d -> Option s l (OptArg (ArgCmdSpecOpt i) od) d
    ) . zip [0..]

-- | コマンド個別のオプション情報のみを抽出
fromCmnFlag :: [OptDescr a]  -- ^ コマンド特有のオプション情報
            -> [CommonFlag]  -- ^ コマンド特有のものも含む全オプションの情報
            -> [a]
fromCmnFlag commandSpecOpts flags = mapMaybe f2a . zip [0..] $ flags
  where
    -- f2a :: (Int, CommonFlag) -> Maybe a
    f2a (ix, flag) = case (commandSpecOpts !!) <$> (optIdx ix) of
        Just (Option _ _ (NoArg  c   ) _) -> Just c
        Just (Option _ _ (ReqArg f  _) _) ->
            Just . f . maybe (error "Inner Error: fromCmnFlag.f2a") id $
                                                                sOpt flag
        Just (Option _ _ (OptArg mf _) _) -> Just . mf $ sOpt flag
        Nothing                           -> Nothing
    optIdx :: Int -> Maybe Int
    optIdx ix = case flags !! ix of
        ArgCmdSpecNo  i   -> Just i
        ArgCmdSpecReq i _ -> Just i
        ArgCmdSpecOpt i _ -> Just i
        _                 -> Nothing
    sOpt :: CommonFlag -> Maybe String
    sOpt flag = case flag of
        ArgCmdSpecReq _ v  -> Just v
        ArgCmdSpecOpt _ mv -> mv
        _                  -> error "Inner Error: fromCmnFlag.sOpt"

-- | コマンドラインオプションの解析
compileOpts :: String         -- ^ コマンドUsage説明(一行バージョン)
    -> [OptDescr a]           -- ^ コマンド特有オプション
    -> [OptDescr CommonFlag]  -- ^ 使用したい共通オプション
    -> IO (NameManager, Maybe LamExpr, [String], [a])
compileOpts header commandSpecOpts cmnOptions = do
    args <- getArgs
    case getOpt Permute allOptions args of
        (fs, names, []) -> do
            case maybe Nothing (Just . readLazyK "") $ argExpr fs of
                Just (Left msg) -> do
                    hPutStrLn stderr $
                        "Invalid -e option value: " ++ msg ++ usage
                    exitFailure
                maybeEitherExpr -> do
                    finalSign <- lamSign usage $ argSign fs
                    return (
                        def { nmPolicy     = argPolicy fs
                            , nmPool       = argPool fs
                            , nmStack      = nmStack def
                            , nmUnlamStyle = argStyle fs
                            , nmLamSign = finalSign
                            }
                        , case maybeEitherExpr of
                                Just (Right e) -> Just e
                                Nothing         -> Nothing
                        , names
                        , fromCmnFlag commandSpecOpts fs
                        )
        (_,     _, errs) -> do
            hPutStrLn stderr $ concat errs ++ usage
            exitFailure
  where
    allOptions = cmnOptions ++ toCmnFlag commandSpecOpts
    for = flip map
    usage = usageInfo header allOptions
    argStyle flags = maybe (nmUnlamStyle def) id . maximum . (Nothing:) $
                        for flags $ \op -> case op of
                            (ArgStyleUnlam e) -> Just e
                            _ -> Nothing
    argPolicy flags = maybe (nmPolicy def) id . maximum . (Nothing:) $
                        for flags $ \op -> case op of
                            (ArgPolicy e) -> Just e
                            _ -> Nothing
    argPool flags = maybe (nmPool def) id . maximum . (Nothing:) $
                        for flags $ \op -> case op of
                            (ArgPool e) -> Just e
                            _ -> Nothing
    argSign flags = maximum . (Nothing:) $
                        for flags $ \op -> case op of
                            (ArgLamSign e) -> Just e
                            _ -> Nothing
    argExpr flags = maximum . (Nothing:) $ for flags $ \op -> case op of
                    (ArgExpr e) -> Just e
                    _ -> Nothing

-- | 表示で使用するラムダ抽象記号の算出。
--
-- CLI指定、環境変数、NameManager のdefault値を考慮する。
-- エラー検出時は、エラー表示とプログラムの終了も行う。
lamSign :: String      -- ^ エラー表示用のコマンドusage
        -> Maybe Char  -- ^ CLI引数中のラムダ記号指定
        -> IO Char
lamSign usage argSign = do
    case argSign of
        Just a  -> return a
        Nothing -> do
            envRawSign <- lookupEnv "LAMBDA_SIGN"
            case envRawSign of
                Nothing  -> return $ nmLamSign def
                Just [e] -> return e   -- 抽象化記号は 1文字限定
                _ -> do
                    hPutStrLn stderr
                            "Error: Env. var. LAMBDA_SIGN has multi-charactors"
                    hPutStrLn stderr $ usage
                    exitFailure
