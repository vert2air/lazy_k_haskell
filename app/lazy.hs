-- {-# LANGUAGE DeriveDataTypeable #-}
-- {-# OPTIONS_GHC -fno-cse #-}

import Debug.Trace (trace)
-- import Data.Char (ord)
import Data.Default (Default(..))
import Data.List.Split (splitOn)
-- import System.Console.CmdArgs ((&=), Data, Typeable, cmdArgs, help, args, name, typ, typFile)
import Numeric (readDec)
import System.Console.GetOpt (OptDescr(..), ArgDescr(..), ArgOrder(..),
                              getOpt, usageInfo)
import System.CPUTime (getCPUTime)
-- import System.IO (isEOF, hFlush, stdout)
import System.Environment (getArgs)
import LazyKCore ((%:), LamExpr(..), IoInfo(..), ProgDot(..),
                  readLazyK, toLambda)
import LazyKParts (deconsLoop)

data Flag = MaxOut Int
          | Verbose Bool
          | DotFreq ProgDot
          deriving (Show)

options :: [OptDescr Flag]
options =
    [ Option [] ["max"] (ReqArg (MaxOut . readInt) "COUNT") "Max output count"
    , Option ['v'] [] (NoArg (Verbose True)) "Verbose output"
    , Option ['d'] [] (ReqArg (DotFreq . ProgDot . map readInt . splitOn ",")
                       "d0,d1") "Progress dot frequency"
    ]

-- | 文字列から、10進数取り出し
readInt :: String -> Int
readInt a = case readDec a of
    [(b, _)] -> b
    [] -> error $ "In parse argument, readInt: " ++ show a

compileOpts :: [String] -> IO ([Flag], [String])
compileOpts args = do
    case getOpt Permute options args of
        (o, n, []) -> return (o, n)
        (_, _, errs) -> ioError $ userError
                                $ concat errs ++ usageInfo header options
  where header = "Usage: lazy [OPTION...] FILE"
{-
data Argument = Argument
    { maxOut :: Int
    , verbose :: Bool
    , progDotFreq :: [Int]
    , lazykFile :: String
    } deriving (Show, Data, Typeable)

argv :: Argument
argv = Argument
    { maxOut = 0 &= help "Max output count if > 0" &= typ "INT" &= name "max"
    , verbose = False       &= help "Verbose output" &= name "v"
    , progDotFreq = []  &= help "Progress dot" &= name "d" &= typ "[Int]"
    -- , lazykFile = " "       &= help "LazyK source file" &= args &= typ "FILE"
    , lazykFile = " "       &= args &= typFile
    }
-}
main :: IO ()
-- main = print =<< cmdArgs argv
main = do
    (opts, [srcFile]) <- compileOpts =<< getArgs
    -- print res
    putStrLn . show $ opts
    lazy srcFile

lazy :: String -> IO ()
lazy srcFile = do
    -- srcFile <- getArgs >>= return . (!! 0)
    lazySrc <- readFile srcFile
    startTime <- getCPUTime
    case readLazyK srcFile lazySrc of
        Right a -> do
            deconsLoop def 10 (IoInfo False [] (ProgDot [0, 20000]))
                                                . toLambda $ a %: In(0)
            endTime <- getCPUTime
            putStrLn $ "Time: "
                    ++ show (fromIntegral (endTime - startTime) / 1e12)
                    ++ " sec"
        Left err -> do
            putStrLn $ "Error: " ++ show err

