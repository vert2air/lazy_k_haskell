module Main where

import Data.Default (Default(..))
import Data.Either (fromRight)
import GHC.Data.Maybe (firstJust)
import System.Console.GetOpt (OptDescr(..), ArgDescr(..), ArgOrder(..),
                              getOpt, usageInfo)
import System.Environment (getArgs, lookupEnv)

import LamCalcCore (Stringifying(..), NameManager(..), PolicyKind(..)
                    , readLazyK, toNamedString, abstElim
                    , reductInf, toLambda)
import LazyKParts (toCcStyle, toIotaStyle, toJotStyle)

data Flag = ArgExpr String
            | ArgStyleUnlam Bool
            | ArgPolicy PolicyKind
            | ArgPool String
            | ArgLamSign Char

            | ArgToLambda
            | ArgReduction
            | ArgAbstElim
            | ArgReduct1
            | ArgStyleCC
            | ArgStyleIota
            | ArgStyleJot deriving (Show)

-- | コマンドラインオプションの定義
options :: [OptDescr Flag]
options =
    [ Option ['c'] ["CC"]       (NoArg (ArgStyleUnlam False)) "CC style (default)"
    , Option ['u'] ["Unlambda"] (NoArg (ArgStyleUnlam True)) "Unlambda style"
    , Option ['i'] ["policy-index"]      (NoArg (ArgPolicy PK_index)) "Use de Bruijn Index instead of name"
    , Option ['l'] ["policy-level"]      (NoArg (ArgPolicy PK_level)) "Assign names depending on Lambda depth"
    , Option ['m'] ["policy-minimum"]    (NoArg (ArgPolicy PK_minimum)) "Use minimum names (default)"
    , Option ['s'] ["policy-single-use"] (NoArg (ArgPolicy PK_single_use)) "Assign unique name for each lambda"
    , Option ['p'] ["pool"] (ReqArg ArgPool "var. names") "Pool of named var. (default='xyzabcd...')"
    , Option ['s'] ["lambda-sign"] (ReqArg (ArgLamSign . (!!0)) "char") "Abstraction sign (default=Greek lambda)"
    , Option ['e'] ["expr"] (ReqArg ArgExpr "Expression") "Lambda expression to pprint"

    , Option ['L'] ["to-lambda"]   (NoArg ArgToLambda)  "Command to lambda"
    , Option ['r'] ["reduction"]   (NoArg ArgReduction) "Command to reduct infinitely"
    , Option ['a'] ["abst-elim"]   (NoArg ArgAbstElim)  "Command to abst. elim."
    , Option ['1'] ["reduction_1"] (NoArg ArgReduct1)   "Command to reduct Just 1 time"
    , Option ['C'] ["style-cc"]    (NoArg ArgStyleCC)   "Command to CC style"
    , Option ['I'] ["style-iota"]  (NoArg ArgStyleIota) "Command to Iota style"
    , Option ['J'] ["style-jot"]   (NoArg ArgStyleJot)  "Command to Jot style"
    ]

-- | コマンドラインオプションの解析
compileOpts :: [String] -> IO ([Flag], [String])
compileOpts args = do
    case getOpt Permute options args of
        (o, n, []) -> return (o, n)
        (_, _, errs) -> ioError $ userError
                                $ concat errs ++ usageInfo header options
  where header = "Usage: pprint [OPTION...] {-e expr|FILE}"

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
    envRawSign <- lookupEnv "LAMBDA_SIGN"
    let envSign = case envRawSign of
            Nothing -> Nothing
            Just [a] -> Just a   -- 抽象化記号は 1文字限定
            _ -> error "Error : Env. var. LAMBDA_SIGN has multi-charactors"
    let finalSign = maybe (nmLamSign def) id $ argSign `firstJust` envSign
    let mng = def { nmPolicy = maybe (nmPolicy def) id argPolicy
                  , nmPool = maybe (nmPool def) id argPool
                  , nmStack = nmStack def
                  , nmUnlamStyle = maybe (nmUnlamStyle def) id argStyle
                  , nmLamSign = finalSign
                  }
    let oped = foldl aux toCat opts
        aux acc op = case op of
            ArgToLambda -> toLambda acc
            ArgReduction -> reductInf acc
            ArgAbstElim -> maybe acc id $ abstElim acc
            -- ArgReduct1
            ArgStyleCC   -> toCcStyle acc
            ArgStyleIota -> toIotaStyle acc
            ArgStyleJot  -> toJotStyle acc
            _ -> acc
    let Stringifying ret _ _ = toNamedString mng oped
    putStrLn ret
