module Main where

import           Control.Monad (forM_)
import           Data.Either (fromRight)
import qualified Data.Map as M (Map, toList)
import System.Console.GetOpt (OptDescr(..), ArgDescr(..), ArgOrder(..),
                              getOpt, usageInfo)
import System.Environment (getArgs)

import LamCalcCore (readLazyK)
import LamCalcParts (Stat(..), stat)

data Flag = ArgExpr String

-- | コマンドラインオプションの定義
options :: [OptDescr Flag]
options =
    [ Option ['e'] ["expr"] (ReqArg ArgExpr "Expression") "Lambda expression to get stat"
    ]

-- | コマンドラインオプションの解析
compileOpts :: [String] -> IO ([Flag], [String])
compileOpts args = do
    case getOpt Permute options args of
        (o, n, []) -> return (o, n)
        (_, _, errs) -> ioError $ userError
                                $ concat errs ++ usageInfo header options
  where header = "Usage: stat {-e expr|FILE}"

outputStat :: Stat -> IO ()
outputStat st = do
    print1Item "Max Depth     : " w $ maxDepth st
    print1Item "  Abst. Depth : " w $ maxLamDepth st
    print1Item "  App. Depth  : " w $ maxAppDepth st
    putStrLn   "Count:"
    print1Item "  Abst.       : " w $ cnt_lambda st
    print1Item "  Index var.  : " w $ cnt_var st
    print1Item "  I           : " w $ cnt_I st
    print1Item "  K           : " w $ cnt_K st
    print1Item "  S           : " w $ cnt_S st
    print1Item "  iota        : " w $ cnt_Iota st
    print1Item "  Jot         : " w $ cnt_Jot_0 st + cnt_Jot_1 st
    print1Item "    0         : " w $ cnt_Jot_0 st
    print1Item "    1         : " w $ cnt_Jot_1 st
    putStrLn   "  Free Variables:"
    printMap   "    index _" w $ freeVar_index st
    printMap   "    named " w $ freeVar_named st
    putStrLn   "  Input Promise (0 origin):"
    printMap   "    input <" w $ input_promise st
  where w = 10

print1Item :: String -> Int -> Int -> IO ()
print1Item title len val = putStrLn $
    title
    ++ take (len - length sVal) [' ', ' '..]
    ++ sVal
  where
    sVal = show val

printMap :: (Show k) => String -> Int -> M.Map k Int -> IO ()
printMap title len mp = do
    forM_ (M.toList mp) $ \ (k, v) -> do
        let kVal = show k
            vVal = show v
        putStrLn $
            title
            ++ kVal
            ++ take (2 - length kVal) [' ', ' '..]
            ++ " : "
            ++ take (len - length vVal) [' ', ' '..]
            ++ vVal

main :: IO ()
main = do
    (opts, srcFiles) <- compileOpts =<< getArgs
    let for = flip map
        argExpr = maximum . (Nothing:) $ for opts $ \op -> case op of
                        (ArgExpr e) -> Just e
    target <- case (argExpr, srcFiles) of
        (Just expr, []) -> do
            return expr
        (Nothing, srcFile:[]) -> do
            readFile srcFile
        _ -> error "Invalid arguments. Use -e expr or FILE."
    let toCat = fromRight (error "Illegal express") . readLazyK "" $ target
    outputStat $ stat 0 toCat
