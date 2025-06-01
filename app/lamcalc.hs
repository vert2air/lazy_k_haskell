module Main where

import Data.Default (Default(..))
import Data.Either (fromRight)
import System.Console.GetOpt (OptDescr(..), ArgDescr(..))

import LamCalcCore (Stringifying(..), RedResult(..)
                    , readLazyK, toNamedString, abstElim
                    , reductInf, red_1, toLambda, buildInputLc)
import LazyKParts (toCcStyle, toIotaStyle, toJotStyle)
import CliTools (commonOptions, compileOpts)

data Flag = ArgToLambda
            | ArgReduction
            | ArgAbstElim
            | ArgReduct1
            | ArgStyleCC
            | ArgStyleIota
            | ArgStyleJot deriving (Show)

-- | コマンドラインオプションの定義
options :: [OptDescr Flag]
options =
    -- 式へのoperation
    [ Option ['L'] ["to-lambda"]   (NoArg ArgToLambda)  "Command to lambda"
    , Option ['r'] ["reduction"]   (NoArg ArgReduction) "Command to reduct infinitely"
    , Option ['a'] ["abst-elim"]   (NoArg ArgAbstElim)  "Command to abst. elim."
    , Option ['1'] ["reduction_1"] (NoArg ArgReduct1)   "Command to reduct Just 1 time"
    , Option ['C'] ["style-cc"]    (NoArg ArgStyleCC)   "Command to CC style"
    , Option ['I'] ["style-iota"]  (NoArg ArgStyleIota) "Command to Iota style"
    , Option ['J'] ["style-jot"]   (NoArg ArgStyleJot)  "Command to Jot style"
    ]

main :: IO ()
main = do
    let header = "Usage: lamcalc [OPTION...] {-e expr|FILE}"
    (mng, argExpr, srcFiles, opts) <- compileOpts header options commonOptions
    toCat <- case (argExpr, srcFiles) of
        (Just expr, []) -> do
            return expr
        (Nothing, srcFile:[]) -> do
            target <- readFile srcFile
            return $ fromRight (error "Illegal express") $ readLazyK "" target
        _ -> error "Invalid arguments. Use -e expr or FILE."
    let oped = foldl aux toCat opts
        aux acc op = case op of
            ArgToLambda -> toLambda acc
            ArgReduction -> reductInf acc
            ArgAbstElim -> maybe acc id $ abstElim acc
            ArgReduct1   -> case red_1 buildInputLc def def acc of
                                RedStop _ _ s -> s
                                RedProg _ _ p -> p
            ArgStyleCC   -> toCcStyle acc
            ArgStyleIota -> toIotaStyle acc
            ArgStyleJot  -> toJotStyle acc
    let Stringifying ret _ _ = toNamedString mng oped
    putStrLn ret
