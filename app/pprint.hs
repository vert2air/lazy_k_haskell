module Main where

import Data.Default (Default(..))
import Data.Either (fromRight)
import System.Console.GetOpt (OptDescr(..), ArgDescr(..), ArgOrder(..),
                              getOpt, usageInfo)
import System.Environment (getArgs)

import LamCalcCore (Stringifying(..), NameManager(..), PolicyKind(..),
                    readLazyK, toNamedString)

data Flag = ArgExpr String
            | ArgStyleUnlam Bool
            | ArgPolicy PolicyKind
            | ArgPool String
            | ArgLamSign Char

-- | コマンドラインオプションの定義
options :: [OptDescr Flag]
options =
    [ Option ['c'] ["CC"]       (NoArg (ArgStyleUnlam False)) "CC style"
    , Option ['u'] ["Unlambda"] (NoArg (ArgStyleUnlam True)) "Unlambda style"
    , Option ['i'] ["policy-index"]      (NoArg (ArgPolicy PK_index)) "Unlambda style"
    , Option ['l'] ["policy-level"]      (NoArg (ArgPolicy PK_level)) "Unlambda style"
    , Option ['m'] ["policy-minimum"]    (NoArg (ArgPolicy PK_minimum)) "Unlambda style"
    , Option ['s'] ["policy-single-use"] (NoArg (ArgPolicy PK_single_use)) "Unlambda style"
    , Option ['p'] ["pool"] (ReqArg ArgPool "変数名") "名前付き変数名のプール"
    , Option ['s'] ["lambda-sign"] (ReqArg (ArgLamSign . (!!0)) "ラムダ抽象記号") "ラムダ抽象記号の文字"
    , Option ['e'] ["expr"] (ReqArg ArgExpr  "Lambda Expression") "Lambda expression to pprint"
    ]

-- | コマンドラインオプションの解析
compileOpts :: [String] -> IO ([Flag], [String])
compileOpts args = do
    case getOpt Permute options args of
        (o, n, []) -> return (o, n)
        (_, _, errs) -> ioError $ userError
                                $ concat errs ++ usageInfo header options
  where header = "Usage: cat [OPTION...] {-e expr|FILE}"

main :: IO ()
main = do
    (opts, srcFiles) <- compileOpts =<< getArgs
    -- putStrLn . show $ opts
    let for = flip map
        argStyle = maximum . (Nothing:) $ for opts $ \op -> case op of
                        (ArgStyleUnlam e) -> Just e
                        _ -> Nothing
        argPolicy = maximum . (Nothing:) $ for opts $ \op -> case op of
                        (ArgPolicy e) -> Just e
                        _ -> Nothing
        argPool = maximum . (Nothing:) $ for opts $ \op -> case op of
                        (ArgPool e) -> Just e
                        _ -> Nothing
        argSign = maximum . (Nothing:) $ for opts $ \op -> case op of
                        (ArgLamSign e) -> Just e
                        _ -> Nothing
        argExpr = maximum . (Nothing:) $ for opts $ \op -> case op of
                        (ArgExpr e) -> Just e
                        _ -> Nothing
    target <- case (argExpr, srcFiles) of
        (Just expr, []) -> do
            return expr
        (Nothing, srcFile:[]) -> do
            readFile srcFile
        _ -> error "Invalid arguments. Use -e expr or FILE."
    let toCat = fromRight (error "Illegal express") . readLazyK "" $ target
    let mng = def { nmPolicy = maybe (nmPolicy def) id argPolicy
                  , nmPool = maybe (nmPool def) id argPool
                  , nmStack = nmStack def
                  , nmUnlamStyle = maybe (nmUnlamStyle def) id argStyle
                  , nmLamSign = maybe (nmLamSign def) id argSign
                  }
    let Stringifying ret _ _ = toNamedString mng toCat
    putStrLn ret
