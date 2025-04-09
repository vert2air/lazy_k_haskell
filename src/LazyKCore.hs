{-# LANGUAGE TupleSections #-}

module LazyKCore where

import Debug.Trace (trace)
import           Data.Default (Default(..))
import           Data.Char (isAlpha, isDigit, isSpace, toUpper, toLower)
import           Data.List (elemIndex)
import qualified Data.Map as M (Map, empty, insert, lookup)
import qualified Data.Set as S (Set, empty, insert,
                                notMember, singleton, toList, union)
import           Text.Parsec ((<|>), (<?>), Parsec, char, digit, many1, oneOf,
                              parse, spaces)
import           Text.Printf (printf)

{- | ラムダ式
 -}
data LamExpr = V !Int           -- ^ De Bruijn index表現の変数。
            | L !Int LamExpr    -- ^ Lambda抽象。
            | App !Int LamExpr LamExpr  -- ^ 関数適用。
            | Nm String         -- ^ 名前付き変数。Iota は、"iota"。
                                --   S, K, I は、大文字。s, k, i は使わない。
                                --   それ以外の英字一文字は、
                                --   大文字小文字を区別し自由変数。
            | Jot !Int String   -- ^ Jot式。"0" "1" からなる文字列。
            | In  !Int          -- ^ Inputプロミスの何byte目か。0から始まる。
        deriving (Eq)

{- | Lazy K の標準入力の履歴と状態
標準入力が End of File に達していれば、Bool が True。
これまでの入力を [Int] に保持。
標準入力で 256 を受けると EOF と見なされる。
それ以降の入力は、256 が続く扱いになる。
[Int] も 有効な入力以降に 256 が続くケースがありうる。
標準入力は、0～255 の数値と、EOF の 256 を取りうるので、
[Char] でなく [Int] にしている。
-}
data InHist = InHist Bool [Int] deriving (Show)

lamSize :: LamExpr -> Int
lamSize (App s _ _) = s
lamSize (L s _)     = s
lamSize (Jot s _)   = s
lamSize _           = 1

infixl 5 %:
(%:) :: LamExpr -> LamExpr -> LamExpr
a %: b = App (1 + lamSize a + lamSize b) a b

la :: LamExpr -> LamExpr
la a = L (1 + lamSize a) a


{-
 - Show Functions
 -}
instance Show LamExpr where
    show e = ret
      where Stringifying ret _ _ = toNamedString def e

instance Default NameManager where
    def = NameManager {
          nmPolicy = PK_minimum
        , nmPool = ['x','y','z']
                    ++ ['a'..'h'] ++ ['j'] ++ ['l'..'r'] ++ ['t'..'w']
                ++ ['X','Y','Z']
                    ++ ['A'..'H'] ++ ['J'] ++ ['L'..'R'] ++ ['T'..'W']
        , nmStack = ""
        , nmUnlamStyle = False
        }

{- | NameMamager の命名ポリシー
 -}
data PolicyKind = PK_index      -- ^ 名前を付けず、De Bruijn index で表示。
                | PK_single_use -- ^ 全てのラムダ抽象に、異なる名前を付ける。
                | PK_level      -- ^ ラムダ抽象の深さに応じて、名前を付ける。
                | PK_minimum    -- ^ 自由変数として使用されている名前を調べ、
                                -- Poolの消費が最小になるように名前を付ける。
    deriving (Eq, Ord, Show)

data NameManager = NameManager
    { nmPolicy :: PolicyKind -- ^ Policy for name management
    , nmPool  :: String  -- ^ 払い出す名前のプール。
                         -- PK_index の場合、参照しない。
                         -- PK_single_use の場合、払い出す度に一文字ずつ短くなる。
    , nmStack  :: String -- ^ 命名した変数のスタック。文字列の1個ずつが払い出した名前。
                         -- 先頭が de Bruij Index = 1 に対応。
                         -- 空白は、名前を与えず、de Bruijn index で表示することを示す。
    , nmUnlamStyle :: Bool -- ^ 真なら、S, K, I を Unlambdaスタイルで表示する。
    } deriving (Show)

{- | ラムダ抽象への名前の付与
 - ラムダ式を文字列化する際に、ラムダ抽象された変数に名前を付ける。
 - 付けた名前は、返り値に含めるとともに、nmStackの先頭に積む。
 -}
enterLambda :: NameManager -> LamExpr -> (String, NameManager)
enterLambda mng@NameManager{nmPolicy = PK_index} _ = (" ", mng)
enterLambda mng@NameManager{nmPolicy = PK_single_use, nmPool = ""} _
        = (" ", mng{nmStack = ' ' : nmStack mng})
enterLambda mng@NameManager{nmPolicy = PK_single_use, nmPool = car : cdr} _
        = ([car], mng{nmStack = car : nmStack mng, nmPool = cdr})
enterLambda mng@NameManager{nmPolicy = PK_level} _
    | length (nmStack mng) < length (nmPool mng)
        = ([next_ch], mng{nmStack = next_ch : nmStack mng})
    | otherwise
        = (" ", mng{nmStack = ' ' : nmStack mng})
  where next_ch = nmPool mng !! length (nmStack mng)
enterLambda mng@NameManager{nmPolicy = PK_minimum} expr
        = ([newName], mng{nmStack = newName : nmStack mng})
  where
    -- digLamAbstから呼出され、ラムダ抽象の本体が渡ってくるので、
    -- 1 はbindされている。1を検出できるよう 0 を渡す。
    (names, idxes) = getFreeVars expr 0
    allname = foldl foldStep names . S.toList $ idxes
      where foldStep set ix = S.insert [nmStack mng !! (ix - 1)] set
    newName = (!!0) . filter (\nm -> S.notMember [nm] allname) $ nmPool mng

leaveLambda :: NameManager -> NameManager
leaveLambda mng@NameManager{nmStack = (_ : cdr)} = mng{nmStack = cdr}
leaveLambda     NameManager{nmStack = _} = error "leaveLambda: empty nmStack"

{- | 自由変数の一覧取得 (入力プロミスを含む)
 -}
getFreeVars :: LamExpr  -- ^ 取得対象のラムダ式
        -> Int
        -> (S.Set String, S.Set Int)
getFreeVars (V v) dep
    | v > dep = (S.empty, S.singleton (v - dep))
    | otherwise = (S.empty, S.empty)
getFreeVars (L _ lexp) dep = getFreeVars lexp (dep + 1)
getFreeVars (App _ fun oprd) dep
    = (f_name `S.union` o_name, f_idx `S.union` o_idx)
  where
    (f_name, f_idx) = getFreeVars fun (dep)
    (o_name, o_idx) = getFreeVars oprd (dep)
getFreeVars (Nm name) _
    | (name !! 0) `elem` "iksIKS" = (S.empty, S.empty)
    | otherwise                   = (S.singleton [name !! 0], S.empty)
-- 入力プロミスは、自由変数として取得できるようにしておく。
getFreeVars (In ix) _ = (S.singleton $ "In(" ++ show ix ++ ")", S.empty)
getFreeVars _       _ = (S.empty, S.empty)

data StyleInfoKind = SK_PureIota | SK_IotaUnlam | SK_General | SK_Error

data Stringifying = Stringifying String StyleInfoKind NameManager

-- Input : Any LamExpr
toNamedString :: NameManager -> LamExpr -> Stringifying
toNamedString mng (V v) = Stringifying name SK_General mng
  where
    name = case v <= length (nmStack mng) of
            True
                | (nmStack mng !! (v - 1)) /= ' ' -> [nmStack mng !! (v - 1)]
            _                                     -> '_' : show v
toNamedString mng e@(L _ _) = Stringifying ('\\':str_ret) style_ret mng_ret
  where
    Stringifying str_ret style_ret mng_ret = digLamAbst mng e
toNamedString mng (App _ (Nm "I") (Nm "iota"))
                                        = Stringifying "(i)(iota)" SK_Error mng
toNamedString mng (App _ (Nm "iota") (Nm "I"))
                                        = Stringifying "(iota)(i)" SK_Error mng
toNamedString mng (App _ fun oprd) =
    Stringifying (concat [appOp, par_fun, pad, par_oprd]) newStyle mng_oprd
  where
    Stringifying str_fun  style_fun  mng_fun  = toNamedString mng     fun
    Stringifying str_oprd style_oprd mng_oprd = toNamedString mng_fun oprd
    (appOp, newStyle) = case (fun, style_fun, oprd, style_oprd) of
        (_,  SK_PureIota,  _, SK_PureIota) -> ("*", SK_PureIota)
        (Nm "iota", _,     _, SK_IotaUnlam) -> ("*", SK_IotaUnlam)
        (Nm "iota", _,     _, _           ) -> ("*", SK_General)
        (_,  SK_IotaUnlam, Nm "iota", _) -> ("*", SK_IotaUnlam)
        (_,  _,            Nm "iota", _) -> ("*", SK_General)
        _ -> (if nmUnlamStyle mng then "`" else "", SK_General)
    par_fun = case fun of
        L _ _ -> "(" ++ str_fun ++ ")"
        _     -> str_fun
    par_oprd = case (oprd, style_oprd) of
        (L _ _, _)              -> "(" ++ str_oprd ++ ")"
        (App _ _ _, SK_General) -> "(" ++ str_oprd ++ ")"
        _                       -> str_oprd
    pad = if isDigit (par_fun !! (length par_fun - 1))
            && isDigit (par_oprd !! 0)
          then " " else ""
toNamedString mng (Nm nm)
    | nm == "iota" = Stringifying "i" SK_PureIota mng
    | nm `elem` ["I", "K", "S"] = if nmUnlamStyle mng
        then         Stringifying (map toLower nm) SK_IotaUnlam mng
        else         Stringifying nm SK_General mng
    | otherwise    = Stringifying nm SK_General mng
toNamedString mng (Jot _ j) = Stringifying j SK_General mng
toNamedString mng (In ix)
                    = Stringifying ("In(" ++ show ix ++ ")") SK_General mng

-- | 連続するラムダ抽象を考慮した文字列化
digLamAbst :: NameManager -> LamExpr -> Stringifying
digLamAbst mng e@(L _ lexp@(L _ _)) = case (newName, ret) of
    (' ':_, _    ) -> Stringifying (' ':'\\':ret) SK_General mng_ret
    (n:_  , ' ':_) -> Stringifying (n:'.':' ':'\\':ret) SK_General mng_ret
    (n:_  , _    ) -> Stringifying (n:ret) SK_General mng_ret
    ("", _    ) -> error $ "Internal Error : enterLambda cannot assign name"
  where
    (newName, mng_ent) = enterLambda mng e
    Stringifying ret _ mng_new = digLamAbst mng_ent lexp
    mng_ret = leaveLambda mng_new
digLamAbst mng e@(L _ lexp) = case newName of
    ' ':_ -> Stringifying (' ':ret) SK_General mng_ret
    n:_   -> Stringifying (n:'.':ret) SK_General mng_ret
    ""    -> error $ "Internal Error : enterLambda cannot assign name"
  where
    (newName, mng_ent) = enterLambda mng e
    Stringifying ret _ mng_new = toNamedString mng_ent lexp
    mng_ret = leaveLambda mng_new

readLazyK :: String -> String -> Either String LamExpr
readLazyK title input = case parse exprs title . trimComment $ input of
    Left err  -> Left $ show err
    Right val -> Right val
  where
    trimComment = unlines . map untilHash . lines
    untilHash = \ln -> maybe ln (\ix -> take ix ln) $ '#' `elemIndex` ln

bindIdx :: [String] -> LamExpr -> LamExpr
bindIdx names expr = applyN (length names) la $ bindAux bindTab 0 expr
  where
    insertAux tab (nm, ridx) = M.insert nm (length names - ridx) tab
    bindTab = foldl insertAux M.empty $ zip names [0..]

applyN :: Int -> (a -> a) -> a -> a
applyN 0 _ x = x
applyN n f x = applyN (n - 1) f (f x)

bindAux :: M.Map String Int -> Int -> LamExpr -> LamExpr
bindAux tab dep (Nm nm) = case M.lookup nm tab of
                                    Just n  -> V (n + dep)
                                    Nothing -> Nm nm
bindAux tab dep (L _ lexpr)      = la $ bindAux tab (dep + 1) lexpr
bindAux tab dep (App _ fun oprd) = bindAux tab dep fun %: bindAux tab dep oprd
bindAux _   _   expr             = expr

exprs, unlamExpr, iotaExpr, expr' :: Parsec String u LamExpr
absts, abst, abst' :: Parsec String u [String]

-- spaces は、文字列が空白から始まっている場合に空白を除去。
exprs = foldl1 (%:) <$> (spaces *> many1 unlamExpr) <?> "Seq. of CC"

unlamExpr = char 'i' *> spaces *> return (Nm "I")
    <|> expr'
    <?> "CC expr. except Iota"

iotaExpr = char 'i' *> spaces *> return (Nm "iota")
    <|> expr'
    <?> "Iota expr."

expr' = Nm . (:[]) . toUpper <$> oneOf ("IKSiks") <* spaces
    <|> Nm . (:[]) <$> oneOf ("ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                           ++ "abcdefghijklmnopqrstuvwxyz") <* spaces
    <|> V . read <$> (char '_' *> many1 digit) <* spaces
    <|> char '`' *> spaces *> return (%:) <*> unlamExpr <*> unlamExpr
    <|> char '*' *> spaces *> return (%:) <*> iotaExpr <*> iotaExpr
    <|> (\s -> Jot (length s) s) . filter (not . isSpace) <$>
                                                many1 (oneOf "01" <* spaces)
    <|> bindIdx <$> absts <*> exprs
    <|> char '(' *> spaces *> exprs <* char ')' <* spaces

absts = fmap concat $ many1 abst

abst = char '\\' *> spaces *> abst'

abst' = ( (map (\a -> [a])) <$>
        (many1 (oneOf ("ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                       ++ "abcdefghijklmnopqrstuvwxyz") <* spaces)
        <* char '.' <* spaces ))
    <|> return [""]

{-
 - Transform functions
 -     to Lambda calcuration Expression
 -     beta Reduction
 -     Abstraction Elimination
 -}

{-
 - Transform to Lambda calcuration Expression
 - Resolve any reference by names
 -}
toLambda :: LamExpr -> LamExpr
toLambda v@(V _)     = v
toLambda (Nm "I")    = ccI
toLambda (Nm "K")    = ccK
toLambda (Nm "S")    = ccS
toLambda (Nm "iota") = iota
toLambda e@(Nm _)    = e  -- 変換できないので、そのまま。
toLambda (Jot _ j)   = foldl jotToLam ccI j
toLambda (L _ le)    = la $ toLambda le
toLambda (App _ m n) = toLambda m %: toLambda n
toLambda e@(In _)    = e  -- 変換できないので、そのまま。

ccI, ccK, ccS, iota :: LamExpr
ccI  = la $ V 1
ccK  = la $ la $ V 2
ccS  = la $ la $ la $ V 3 %: V 1 %: (V 2 %: V 1)
iota = la $ V 1 %: ccS %: ccK

jotToLam :: LamExpr -> Char -> LamExpr
jotToLam e '0' = e %: ccS %: ccK
jotToLam e '1' = la $ la $ e %: (V 2 %: V 1)
jotToLam _ x   = error $ "Internal Error: jotToLam detect: " ++ [x]

{-
 - beta Reduction
 -     Normal beta Reduction
 -     beta Reduction for CC expression
 -}

-- | Beta簡約の結果
data RedResult e = RedStop Int e
    -- ^ Intが負なら、簡約出来る箇所が無かった。
    --   Intが0以上なら、簡約出来る箇所を見付ける前に
    --   Inputプロミスにぶつかり、indexがIntの値だった。
                | RedProg Int e
    -- ^ Intが負なら、簡約出来た。
    --   Intが0以上なら、一部簡約出来たが、その後、
    --   Inputプロミスにぶつかり、indexがIntの値だった。
    deriving (Show)

instance Functor RedResult where
    fmap f (RedStop i e) = RedStop i (f e)
    fmap f (RedProg i e) = RedProg i (f e)

instance Applicative RedResult where
    pure = RedStop (-1)
    RedStop i f <*> RedStop j e = RedStop (max i j) (f e)
    RedStop i f <*> RedProg j e = RedProg (max i j) (f e)
    RedProg i f <*> RedStop j e = RedProg (max i j) (f e)
    RedProg i f <*> RedProg j e = RedProg (max i j) (f e)

instance Monad RedResult where
    RedStop i e >>= f = case f e of
        RedStop j e' -> RedStop (max i j) e'
        RedProg j e' -> RedProg (max i j) e'
    RedProg i e >>= f = case f e of
        RedStop j e' -> RedProg (max i j) e'
        RedProg j e' -> RedProg (max i j) e'

{- | Beta簡約の実行 (入力の遅延評価対応)

 入力が遅延評価される前提で、可能な範囲でbeta簡約を行う。
 入力プロミスを評価する必要が出た時点で、評価を停止し、
 返り値に何byte目の入力が必要かの情報を含める。
 -}
betaRed :: InHist
        -> LamExpr
        -> RedResult LamExpr
betaRed hist                (L _ le)    = la <$> betaRed hist le
betaRed hist                (App _ (L _ le) e) = case once of
    -- beta簡約の結果が、再び関数適用だった。
    -- ここまで簡約出来る箇所が無かった結果ここで簡約を行ったので、
    -- 先頭から見直しても結局ここに戻ってくる。
    -- それは無駄なので、ここから betaRed を継続する。
    App _ _ _ -> betaRed hist once >>= RedProg (-1)
    _         -> RedProg (-1) once
  where
    once = comple (subst 1 e) le
betaRed hist@(InHist eof input) e@(App s (In ix) oprd)
    -- 現時点で展開可能な入力があるので、それを使って続行。
    | eof || ix < length input = do
        cont <- betaRed hist $ App s (buildInput hist ix) oprd
        RedProg (-1) cont  -- Inputプロミスを置換えたので必ずRedProg。
    -- Inputプロミスは外部情報が必要なので、一旦 betaRed を止める。
    | otherwise = RedStop ix e
betaRed hist              e@(App _ x y) = case betaRed hist x of
    RedStop i _
        | i >= 0     -> RedStop i e  -- Inputプロミスでblockした。
        | otherwise  -> RedStop i (x %:) <*> betaRed hist y
    -- x で進展があったものの、関数適用であることには変わりない。
    -- しかし、x が (L _ _) なら、beta還元可能。
    RedProg _ e'@(L _ _) -> betaRed hist (e' %: y)
    -- そうでなければ、一旦行けるところまで行ったので、戻る。
    x'                ->  (%:) <$> x' <*> pure y
betaRed hist@(InHist eof input) e@(In ix)
    -- 現時点で展開可能な入力がある。cons なので、beta還元は出来ない。
    -- In がリストに変わるので、RedProg を返す。
    | eof || ix < length input = RedProg (length input) $ buildInput hist ix
    -- Inputプロミスは外部情報が必要なので、一旦 betaRed を止める。
    | otherwise = RedStop ix e
betaRed _ e            = pure e    -- V and Nm

-- | Inputプロミスを置換える実リストを生成
buildInput :: InHist    -- ^ 標準入力の履歴
            -> Int      -- ^ beta還元に必要なinputのインデックス
            -> LamExpr  -- ^ 判明しているinputを展開したラムダ式
buildInput (InHist eof input) ix
    | ix < length input = foldr makeCons (In (length input)) $ drop ix input
    | eof = foldr makeCons (In (length compInput)) $ drop ix compInput
    | otherwise = error "buildInput: called under unexpected condition"
  where
    makeCons carNum cdr = la $ V 1 %: makeChuchNum carNum %: cdr
    compInput
        | eof = input ++ take (ix - length input + 1) [256, 256 ..]
        | otherwise = input

-- | Church encodingで、ix を表現するラムダ式を生成
makeChuchNum :: Int -> LamExpr
makeChuchNum ix = la . la . applyN ix (V 2 %:) $ V 1

-- |
-- Substitute the variable to the Lambda expression
--
-- >>> subst 1 (V 3) (V 1 %: V 2)
-- App 3 (V 3) (V 2)
-- >>> subst 1 (V 3) (V 1 %: la (v 2))
-- App 4 (V 3) (la (v 3))
-- >>> subst 2 (V 3) (V 1 %: V 5 %: V 2)
-- App 5 (App 3 (V 1) (V 4)) (V 3)
subst :: Int            -- ^ De Bruijn index of variable to be replaced
    -> LamExpr          -- ^ expression by which the variable is replaced
    -> LamExpr          -- ^ whole expression
    -> Maybe LamExpr    -- ^ if whole expresion is not changed, return Nothing
subst vIdx e (V v)
    | v == vIdx = Just e
    | v >  vIdx = Just $ V (v - 1)
    | otherwise = Nothing
subst vIdx e (L _ le)    = la <$> subst (vIdx + 1) (comple (deepen 1) e) le 
subst vIdx e (App _ m n) = mergeApp (subst vIdx e) m n
subst _    _ (Nm _)      = Nothing
subst _    _ (Jot _ _)   = Nothing
subst _    _ (In _)      = Nothing

deepen :: Int ->  LamExpr -> Maybe LamExpr
deepen vIdx (V v)
    | v >= vIdx = Just $ V (v + 1)
    | otherwise = Nothing
deepen vIdx (L _ le)    = la <$> deepen (vIdx + 1) le
deepen vIdx (App _ m n) = mergeApp (deepen vIdx) m n
deepen _    (Nm _)      = Nothing
deepen _    (Jot _ _)   = Nothing
deepen _    (In _)      = Nothing

-- |
-- Beta Reduction on Combinator-Calculus Level
betaRedCC :: LamExpr
          -> Maybe LamExpr -- ^ if cannot more reduction, this returns Nothing
betaRedCC (App _ (Nm "I") e)                     = Just e
betaRedCC (App _ (App _ (Nm "K") x) _)           = Just x
betaRedCC (App _ (App _ (App _ (Nm "S") x) y) z) = Just $ (x %: z) %: (y %: z)
betaRedCC (App _ x y) = maybe ((x %:) <$> betaRedCC y)
                               (Just . (%: y))        $ betaRedCC x
betaRedCC (Nm _) = Nothing
betaRedCC _      = Nothing

-- |
-- Abstraction Elimination
--
abstElim :: LamExpr
    -> Maybe LamExpr -- ^ if cannot more Elimination, this returns Nothing
abstElim (Nm _)      = Nothing   -- Rule 1
abstElim (V _)       = Nothing   -- Rule 1
abstElim (Jot _ _)   = Nothing   -- Rule 1
abstElim (In _)      = Nothing   -- Rule 1  内容は不明なので、そのままにする。
abstElim (App _ m n) = mergeApp abstElim m n    -- Rule 2
abstElim (L _ le)
    | not (hasVar 1 le)  =      -- 3. T[\x.E] => K T[E] if x is NOT free in E
                Just . (Nm "K" %:) . comple (shallow 1) . comple abstElim $ le
abstElim (L _ e@(Nm _))    = Just $ Nm "K" %: e -- variation of Rule 3
abstElim (L _ e@(Jot _ _)) = Just $ Nm "K" %: e -- variation of Rule 3
abstElim (L _ (V v))
    | v == 1      = Just $ Nm "I" -- Rule 4
    | otherwise   = error $ "out of rule 4: " ++ show (la $ V v)
abstElim (L _ inner@(L _ le))
    | hasVar 2 le = Just . comple abstElim . la . comple abstElim $ inner -- R.5
    | otherwise   = error $ "out of rule 5: " ++ show (la inner)
abstElim (L _ (App _ m (V 1)))
    | not (hasVar 1 m) = Just . comple (shallow 1) $ m  -- Eta reduction
abstElim (L _ (App _ m n)) =
    Just $ Nm "S" %: comple abstElim (la m) %: comple abstElim (la n) -- Rule 6

hasVar :: Int -> LamExpr -> Bool
hasVar _    (Nm _)      = False
hasVar vIdx (V v)       = vIdx == v
hasVar vIdx (L _ le)    = hasVar (vIdx + 1) le
hasVar vIdx (App _ m n) = hasVar vIdx m || hasVar vIdx n
hasVar _    (Jot _ _)   = False
hasVar _    (In _)      = False

shallow :: Int -> LamExpr -> Maybe LamExpr
shallow _ (Nm _) = Nothing
shallow vIdx (V v)
    | v > vIdx  = Just $ V (v - 1)
    | otherwise = Nothing
shallow vIdx (L _ le)    = la <$> shallow (vIdx + 1) le
shallow vIdx (App _ m n) = mergeApp (shallow vIdx) m n
shallow _    (Jot _ _)   = Nothing
shallow _    (In _)      = Nothing

{-
 - Lazy-K Interpreter
 -}
execLazyK :: LamExpr -> [Int]
execLazyK cc
    | isNil cc  = []
    | otherwise = case getNum $ car %: cc of
                    Just n
                        | n < 256 -> n : execLazyK (cdr %: cc)
                    _             -> []
  where
    car = Nm "S" %: Nm "I" %: (Nm "K" %: Nm "K") -- \ e -> e (\ a b -> a)
    cdr = Nm "S" %: Nm "I" %: (Nm "K" %: (Nm "K" %: Nm "I"))
                                                --  \ e -> e (\ a b -> a)

-- |
-- Check whether the list is nil or not directly
isNil :: LamExpr -> Bool
-- isNil cc = case evalCC $ aux cc of
isNil cc = case evalCC1 $ ChNumEval $ aux cc of
            Just (ChNumEval (Nm "True")) -> True
            _                            -> False
  where
    aux a = a %: (Nm "K" %: (Nm "K" %: (Nm "K" %: Nm "False"))) %: Nm "True"

{-
 - Common Utility Functions
 -}

-- |
-- Complement original value if it is evaluated to Nothing
comple :: (a -> Maybe a) -> a -> a
comple f a = maybe a id $ f a

isName :: Char -> Bool
isName a = isAlpha a || isDigit a || a == '_'

isInitChar :: Char -> Bool
isInitChar a = isAlpha a || a == '_'

mergeApp :: (LamExpr -> Maybe LamExpr) -> LamExpr -> LamExpr -> Maybe LamExpr
mergeApp f x y = case (f x, f y) of
    (Just x', Just y') -> Just $ x' %: y'
    (Just x', Nothing) -> Just $ x' %: y
    (Nothing, Just y') -> Just $ x  %: y'
    _                  -> Nothing

stepN :: (a -> Maybe a) -> Int -> a -> a
stepN _ 0 e = e
stepN f n e = case f e of
                Nothing -> e
                Just e' -> stepN f (n-1) e'

applyFully ::
    (a -> Maybe a)          -- ^ translation function
    -> (a -> Maybe String)  -- ^ function to check if it should be cont. or not
    -> Int                  -- ^ time limit to apply the translation function
    -> a                    -- ^ target value
    -> Either (a, Int, String) (a, Int)
applyFully _ _   0   a = Left (a, 0, "Time Limit")
applyFully f chk lmt a = case f a of
    Nothing -> Right (a, lmt)
    Just a' -> case chk a of
                Nothing  -> applyFully f chk (lmt - 1) a'
                Just msg -> Left (a', lmt, msg)

checkStyle :: LamExpr -> Maybe String
checkStyle (Nm "I")    = Just "CC"
checkStyle (Nm "K")    = Just "CC"
checkStyle (Nm "S")    = Just "CC"
checkStyle (Nm "iota") = Just "Iota"
checkStyle (Jot _ _)   = Just "Jot"
checkStyle (App _ x y) = do
    tx <- checkStyle x
    ty <- checkStyle y
    if tx == ty && tx /= "Jot"
        then Just tx
        else Nothing
checkStyle _ = Nothing

-- |
-- Get the value of Church Number directly
-- In this function, Nm "plus1" and V n are used in illegal way
-- because I don't want to make definition of LamExpr complicated.
getNum :: LamExpr -> Maybe Int
getNum cc = case stepN evalCC1 5000 $ toChNumEval cc of
                ChNumEval (V n) -> Just n
                _               -> Nothing

getNumN :: Int -> LamExpr -> Either String (Int, Int)
getNumN lmt cc = case applyFully evalCC1 chk lmt $ toChNumEval cc of
    Right (ChNumEval (V n), c) -> Right (n, c)
    Right _                    -> Left ""
    Left (ChNumEval e, c, msg) ->
            Left $ printf "%s : c = %d / %d : size = %d" msg c lmt (lamSize e)
  where
    chk (ChNumEval a)
        | lamSize a > 10*1000*1000 = Just "Space Limit"
        | otherwise                = Nothing

-- sl = 10 * 1000 * 1000

newtype ChNumEval = ChNumEval { getLamExpr :: LamExpr } deriving (Eq)

toChNumEval :: LamExpr -> ChNumEval
toChNumEval cc = ChNumEval $ cc %: Nm "plus1" %: V 0

evalCC :: Bool -> ChNumEval -> Maybe ChNumEval
evalCC _ (ChNumEval (App _ (Nm "I") x)) = Just $ comple evalCC2 $ ChNumEval x
evalCC _ (ChNumEval (App _ (App _ (Nm "K") x) _)) =
                                        Just $ comple evalCC2 $ ChNumEval x
-- evalCC _ (Nm "S" :% Nm "K" :% _ :% x) = Just $ comple evalCC2 $ ChNumEval x
-- evalCC _ (Nm "S" :% Nm "K" :% _)      = Just $ ChNumEval $ Nm "I"
evalCC b (ChNumEval (App _ (App _ (App _ (Nm "S") x) y) z))
    | b                       = Just $ ChNumEval $ x'' %: z'' %: (y'' %: z'')
    | x' == Nothing && y' == Nothing && z' == Nothing
                              = Nothing
    | otherwise               = Just $ ChNumEval $ Nm "S" %: x'' %: y'' %: z''
  where
    x' = evalCC2 $ ChNumEval x
    y' = evalCC2 $ ChNumEval y
    z' = evalCC2 $ ChNumEval z
    x'' = maybe x getLamExpr x'
    y'' = maybe y getLamExpr y'
    z'' = maybe z getLamExpr z'
evalCC _ (ChNumEval (App _ (Nm "plus1") (V n))) = Just $ ChNumEval $ V (n + 1)
evalCC b (ChNumEval (App _ (Nm "plus1") x))   =
        ChNumEval . (Nm "plus1" %:) . getLamExpr <$> evalCC b (ChNumEval x)
-- evalCC _ (Nm "iota"  :% x)       = Just $ comple evalCC2 x %: Nm "S" %: Nm "K"
evalCC True  (ChNumEval (App _ x y)) =
    case evalCC1 $ ChNumEval x of
        Just (ChNumEval a) -> Just $ ChNumEval $ a %: y
        _                  ->
            case evalCC1 $ ChNumEval y of
                Just (ChNumEval b) -> Just $ ChNumEval $ x %: b
                _                  -> Nothing

evalCC False (ChNumEval (App _ x y))
    | x' == Nothing && y' == Nothing = Nothing
    | otherwise                      =
        Just $ ChNumEval $ maybe x getLamExpr x' %: maybe y getLamExpr y'
  where
    x' = evalCC2 $ ChNumEval x
    y' = evalCC2 $ ChNumEval y
evalCC _    _        = Nothing

evalCC1, evalCC2 :: ChNumEval -> Maybe ChNumEval
evalCC1 = evalCC True
evalCC2 = evalCC False
