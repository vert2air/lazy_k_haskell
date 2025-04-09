import Debug.Trace (trace)
import Data.Char (ord)
import Data.Default (Default(..))
import System.CPUTime (getCPUTime)
import System.IO (isEOF, hFlush, stdout)
import System.Environment (getArgs)
import LazyKCore ((%:), betaRed, forceProg,
    LamExpr(..), RedResult(..), IoInfo(..), ProgDot(..),
    isPdMature, clearPd, readLazyK, toLambda)

decons :: IoInfo
        -> ProgDot
        -> LamExpr
        -> IO (LamExpr, LamExpr, ProgDot, IoInfo)
decons ioInf d expr =
  case expr of
    L _ (App _ (App _ (V 1) car) cdr) -> return (car, cdr, d, ioInf)
    _ -> do
        reded <- betaRedInput ioInf d expr
        case reded of
            (RedProg d' _ expr', ioInf') -> decons ioInf' d' expr'
            ret@(RedStop d' ix expr', ioInf')
                -- 進捗dotの表示タイミングか、inputブロック。再帰で処理。
                | isPdMature 1 ioInf' d' || ix >= 0 ->
                    decons ioInf' d' expr'
                -- Lazy Kプログラムなら、scott encode の list を出力する筈。
                -- cons の形でなく、beta簡約も進まないのなら、エラー。
                | otherwise -> error $ "Invalid program: ret=" ++ show ret

betaRedInput :: IoInfo
            -> ProgDot
            -> LamExpr
            -> IO (RedResult LamExpr, IoInfo)
betaRedInput ioInf d expr = do
    let ret = betaRed ioInf d expr
    -- case betaRedPar expr of
    case ret of
        RedProg d' _ expr'
            | isPdMature 1 ioInf d' -> do
                putStr "."
                hFlush stdout
                (red, ioInf'') <- betaRedInput ioInf (clearPd 1 d') expr'
                return (forceProg red, ioInf'')
        RedStop d' _ _
            | isPdMature 1 ioInf d' -> do
                putStr "."
                hFlush stdout
                betaRedInput ioInf (clearPd 1 d') expr
        RedProg pd ix expr'
            | ix < 0 && not (isPdMature 1 ioInf pd) -> do
                -- putStrLn "---------------> RedProg minus"
                return (ret, ioInf)
            | otherwise -> do
                -- putStrLn "---------------> RedProg Plus"
                ioInf' <- pollInput ix ioInf
                (red, ioInf'') <- betaRedInput ioInf' pd expr'
                return (forceProg red, ioInf'')
        RedStop pd ix _
            | ix < 0 -> do
                -- putStrLn "---------------> RedStop minus"
                return (RedStop pd ix expr, ioInf) -- 元のexprを使用。
            | otherwise -> do
                -- putStrLn "---------------> RedStop Plus"
                -- putStrLn . show $ ret
                ioInf' <- pollInput ix ioInf
                betaRedInput ioInf' pd expr    -- 元のexprを使用。

pollInput :: Int -> IoInfo -> IO IoInfo
pollInput ix (IoInfo _ input pd) = do
    IoInfo eof' add _ <- getNchar [] $ ix - length input + 1
    -- putStrLn $ "---------------> getNchar !! " ++ show (length input) ++ ".. = " ++ show add
    -- putStrLn $ "                " ++ show (input ++ add)
    return $ IoInfo eof' (input ++ add) pd

getNchar :: [Int] -> Int -> IO IoInfo
getNchar acc n
    | n <= 0 = return $ IoInfo False acc def
    | otherwise = do
        eof <- isEOF
        if eof then return $ IoInfo True acc def
              else do
                  c <- getChar
                  getNchar (acc ++ [ord c]) (n - 1)

infinit :: IoInfo -> ProgDot -> LamExpr -> IO (LamExpr, ProgDot, IoInfo)
infinit ioInf pd expr = do
    -- putStrLn $ "infinit : " ++ show ioInf ++ " : " ++ show expr ++ " <<<<<<"
    ret <- betaRedInput ioInf pd expr
    case ret of
        (RedProg pd' _  expr', ioInf') -> do
            -- putStrLn ("Prog: " ++ show ret)
            infinit ioInf' pd' expr'
        (RedStop pd' ix _   , ioInf')
            | isPdMature 1 ioInf' pd' ->
                error $ "Not Chuch Number" ++ show pd'
            | ix < 0 -> return (expr, pd', ioInf')
            | otherwise -> infinit ioInf' pd' expr

getChNum :: LamExpr -> Maybe Int
getChNum (L _ (L _ e)) = countF e
getChNum _ = Nothing

countF :: LamExpr -> Maybe Int
countF (V 1) = Just 0
countF (App _ (V 2) e) = (+1) <$> countF e
countF _ = Nothing

deconsLoop :: Integer -> ProgDot -> Int -> IoInfo -> LamExpr -> IO ()
deconsLoop startTime pd countdown ioInf expr = do
  (car, cdr, pd', ioInf') <- decons ioInf pd expr
  (car_lam, pd'', ioInf'') <- infinit ioInf' pd' car
  let num = getChNum car_lam
  putStrLn "car info ----------"
  -- putStrLn . show $ car_lam
  putStrLn . show $ num
  case num of
    Just n
        | n >= 256 -> do
            -- putStrLn $ "Reach EOF"
            return ()
    _ -> case countdown of
            0 -> do
                endTime <- getCPUTime
                putStrLn $ "Time: " ++ show (fromIntegral (endTime - startTime) / 1e12) ++ " sec"
            _ -> do
                case (car, cdr) of
                    (L _ (V 1), L _ (V 1)) -> return ()
                    _ -> deconsLoop startTime pd'' (countdown - 1) ioInf'' cdr

lazy :: IO ()
lazy = do
    srcFile <- getArgs >>= return . (!! 0)
    lazySrc <- readFile srcFile
    startTime <- getCPUTime
    case readLazyK srcFile lazySrc of
        Right a -> do
            deconsLoop startTime def 10 (IoInfo False [] (ProgDot [0, 20000]))
                                                . toLambda $ a %: In(0)
        Left err -> do
            putStrLn $ "Error: " ++ show err

main :: IO ()
main = lazy
