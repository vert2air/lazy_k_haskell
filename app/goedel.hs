module Main where

import Data.Either (fromRight)
import System.Console.GetOpt (OptDescr(..), ArgDescr(..))

import LamCalcCore (readLazyK, toNamedString, takeStringified)
import CliTools (commonOptions, compileOpts)
import GoedelNum (expr_to_goedel, goedel_to_expr)

data Flag = ArgGoedel Integer

-- | コマンドラインオプションの定義
options :: [OptDescr Flag]
options =
    [ Option ['g'] ["input-goedel-number"]
            (ReqArg (ArgGoedel . read . filter (/='_')) "Number")
            "Goedel Number to input"
    ]

main :: IO ()
main = do
    let header = "Usage: goedel [OPTINOS...] {-e expr|FILE|-g goedelNumber}"
    (mng, argExpr, srcFiles, opts) <- compileOpts header options commonOptions
    case (argExpr, srcFiles, opts) of
        (Just expr, [], []) -> do
            putStrLn . show . fst . expr_to_goedel $ expr
        (Nothing, srcFile:[], []) -> do
            target <- readFile srcFile
            putStrLn . show . fst . expr_to_goedel $
                fromRight (error "Illegal express") . readLazyK "" $ target
        (Nothing, [], [ArgGoedel gn]) -> do
            putStrLn . takeStringified . toNamedString mng $ goedel_to_expr gn
        _ -> error "Invalid arguments. Use -e expr or FILE."
