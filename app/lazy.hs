import Debug.Trace (trace)
import Data.Char (ord)
import System.CPUTime (getCPUTime)
import System.IO (isEOF)
import System.Environment (getArgs)
import LazyKCore ((%:), betaRed, RedResult(..), InHist(..),
    LamExpr(..), readLazyK, toLambda)

decons :: InHist
        -> LamExpr
        -> IO (LamExpr, LamExpr, InHist)
decons hist expr =
  case expr of
    L _ (App _ (App _ (V 1) car) cdr) -> return (car, cdr, hist)
    _ -> do
        reded <- betaRedInput hist expr
        case reded of
            (RedProg _ expr', hist') -> decons hist' expr'
            ret@(RedStop ix expr', hist') -> do
                if ix < 0 then error $ show ret
                          else decons hist' expr'

betaRedInput :: InHist
            -> LamExpr
            -> IO (RedResult LamExpr, InHist)
betaRedInput hist expr = do
    let ret = betaRed hist expr
    -- putStr "." -- ToDo 頻度調整
    -- case betaRedPar expr of
    case ret of
        RedProg ix expr'
            | ix < 0 -> do
                -- putStrLn "---------------> RedProg minus"
                return (ret, hist)
            | otherwise -> do
                -- putStrLn "---------------> RedProg Plus"
                hist' <- pollInput ix hist
                betaRedInput hist' expr'
        RedStop ix _
            | ix < 0 -> do
                -- putStrLn "---------------> RedStop minus"
                return (RedStop ix expr, hist) -- 元のexprを使用。
            | otherwise -> do
                -- putStrLn "---------------> RedStop Plus"
                -- putStrLn . show $ ret
                hist' <- pollInput ix hist
                betaRedInput hist' expr    -- 元のexprを使用。

pollInput :: Int -> InHist -> IO InHist
pollInput ix (InHist _ input) = do
    InHist eof' add <- getNchar [] $ ix - length input + 1
    -- putStrLn $ "---------------> getNchar !! " ++ show (length input) ++ ".. = " ++ show add
    -- putStrLn $ "                " ++ show (input ++ add)
    return $ InHist eof' $ input ++ add

getNchar :: [Int] -> Int -> IO InHist
getNchar acc n
    | n <= 0 = return $ InHist False acc
    | otherwise = do
        eof <- isEOF
        if eof then return $ InHist True acc
              else do
                  c <- getChar
                  getNchar (acc ++ [ord c]) (n - 1)

infinit :: InHist -> LamExpr -> IO (LamExpr, InHist)
infinit hist expr = do
    -- putStrLn $ "infinit : " ++ show hist ++ " : " ++ show expr ++ " <<<<<<<<<<<<<<<<<<<<<<<<<<<"
    ret <- betaRedInput hist expr
    case ret of
        (RedProg _  expr', hist') -> do
            -- putStrLn ("Prog: " ++ show ret)
            infinit hist' expr'
        (RedStop ix _   , hist') -> do
            -- putStrLn ("Stop: " ++ show ret)
            if ix < 0 then return (expr, hist')
                        else infinit hist' expr

getChNum :: LamExpr -> Maybe Int
getChNum (L _ (L _ e)) = countF e
getChNum _ = Nothing

countF :: LamExpr -> Maybe Int
countF (V 1) = Just 0
countF (App _ (V 2) e) = (+1) <$> countF e
countF _ = Nothing

deconsLoop :: Integer -> Int -> InHist -> LamExpr -> IO ()
deconsLoop startTime countdown hist expr = do
  (car, cdr, hist') <- decons hist expr
  (car_lam, hist'') <- infinit hist' car
  -- (car_lam2, hist'') <- infinit hist' car
  -- putStrLn . show $ car_lam2
  -- (car_lam, hist''') <- infinit hist'' car_lam2
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
                    _ -> deconsLoop startTime (countdown - 1) hist'' cdr

lazy :: IO ()
lazy = do
    srcFile <- getArgs >>= return . (!! 0)
    lazySrc <- readFile srcFile
    startTime <- getCPUTime
    case readLazyK srcFile lazySrc of
        Right a -> do
            deconsLoop startTime 10 (InHist False []) . toLambda $ a %: In(0)
        Left err -> do
            putStrLn $ "Error: " ++ show err

main :: IO ()
main = lazy
