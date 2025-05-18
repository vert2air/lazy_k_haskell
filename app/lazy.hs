-- {-# LANGUAGE DeriveDataTypeable #-}
-- {-# OPTIONS_GHC -fno-cse #-}

-- import Prelude hiding (readFile, putStrLn, getArgs)
-- import System.IO.Encoding (readFile, putStrLn, getArgs)
-- import Data.Char (ord)
import Data.Default (Default(..))
import Data.List.Split (splitOn)
-- import System.Console.CmdArgs ((&=), Data, Typeable, cmdArgs, help, args, name, typ, typFile)
import Numeric (readDec)
import System.Console.GetOpt (OptDescr(..), ArgDescr(..), ArgOrder(..),
                              getOpt, usageInfo)
import System.CPUTime (getCPUTime)
import System.IO (hPutStrLn, stderr)
import System.Environment (getArgs)
import System.Exit (ExitCode(..), exitWith)
import LamCalcCore ((%:), LamExpr(..), IoInfo(..), ProgDot(..),
                    readLazyK, toLambda)
import LazyKParts (deconsLoopLc, deconsLoopCc, onlyV)

data Flag = MaxOut Int
          | ToLam Bool
          | Verbose Bool
          | DotFreq ProgDot
          deriving (Show)

options :: [OptDescr Flag]
options =
    [ Option [] ["max"] (ReqArg (MaxOut . readInt) "COUNT") "Max output count"
    , Option ['l'] [] (NoArg (ToLam False)) "Process as lambda calculus"
    , Option ['v'] [] (NoArg (Verbose True)) "Verbose output"
    , Option ['d'] [] (ReqArg
            (DotFreq . ProgDot . map readInt . splitOn "," . filter (/='_'))
                                "d0,d1") "Progress dot frequency"
    ]

-- | 文字列から、10進数取り出し
readInt :: String -> Int
readInt a = case readDec a of
    [(b, _)] -> b
    _        -> error $ "In parse argument, readInt: " ++ show a

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
    -- let ?enc = UTF8
    -- Windows では、Shellコマンド chcp で、UTF-8にしておく。
    -- /c/Windows/System32/chcp.com 65001
    (opts, [srcFile]) <- compileOpts =<< getArgs
    -- putStrLn . show $ opts
    startTime <- getCPUTime
    let for = flip map
        forAny = flip any
        maxOut = maximum . (Nothing:) $ for opts $ \op -> case op of
                        (MaxOut n) -> Just n
                        _ -> Nothing
        toLam = forAny opts $ \op -> case op of
                        (ToLam _) -> True
                        _ -> False
        verbose = forAny opts $ \op -> case op of
                        (Verbose _) -> True
                        _ -> False
        dotFreq = maximum . (ProgDot [0, 0]:) $ for opts $ \op -> case op of
                        (DotFreq d) -> d
                        _ -> ProgDot [0, 0]
        -- lazyの出力にラムダ記号は含まれない。適当にdefault値を設定しておく。
        ioInf = IoInfo False [] verbose dotFreq 'λ' startTime
    onlyV ioInf $
        hPutStrLn stderr $ "Start time : " ++ show startTime
    exitCode <- lazy toLam ioInf maxOut srcFile
    endTime <- getCPUTime
    onlyV ioInf $ do
        let sec = fromIntegral (endTime - startTime) / 1e12 :: Double
        hPutStrLn stderr $ "Time: " ++ show sec ++ " sec"
    exitWith exitCode

lazy :: Bool -> IoInfo -> Maybe Int -> String -> IO ExitCode
lazy toLam ioInf maxOut srcFile = do
    lazySrc <- readFile srcFile
    case readLazyK srcFile lazySrc of
        Right a -> do
            if toLam
                then deconsLoopLc ioInf def maxOut . toLambda $ a %: In(0)
                else deconsLoopCc ioInf def maxOut $ a %: In(0)
        Left err -> do
            hPutStrLn stderr $ "Error: " ++ show err
            return $ ExitFailure 1
