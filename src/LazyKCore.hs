{-# LANGUAGE TupleSections #-}

module LazyKCore where

import Debug.Trace (trace)
-- trace :: String -> a -> a
-- trace _ x = x
import           Data.Default (Default(..))
import           Data.Char (isDigit, isSpace, toUpper, toLower)
import           Data.List (elemIndex)
import qualified Data.Map as M (Map, empty, insert, lookup)
import qualified Data.Set as S (Set, empty, insert,
                                notMember, singleton, toList, union)
import Test.QuickCheck (Arbitrary(..), oneof, listOf1, shuffle)
import           Text.Parsec ((<|>), (<?>), Parsec, char, digit, many1, oneOf,
                              parse, spaces, try)


-- | ラムダ式
data LamExpr = V !Int           -- ^ De Bruijn index表現の変数。
            | L !Int LamExpr    -- ^ Lambda抽象。
            | App !Int LamExpr LamExpr  -- ^ 関数適用。
            | Nm String         -- ^ 名前付き変数。Iota は、"iota"。
                                --   S, K, I は、大文字。s, k, i は使わない。
                                --   それ以外の英字一文字は、
                                --   大文字小文字を区別し自由変数。
            | Jot !Int String   -- ^ Jot式。"0" "1" からなる文字列。
            | In  !Int          -- ^ Inputプロミスの何byte目か。0から始まる。
        deriving (Eq, Show)

instance Arbitrary LamExpr where
    arbitrary = oneof [
          V . (+1) . abs <$> arbitrary
        , do
            lexp <- arbitrary
            case lexp of
                -- '*' が無いと Iotaスタイルは表現できない。やり直す。
                Nm "iota" -> la <$> arbitrary
                _         -> return $ la lexp
        , (%:) <$> arbitrary <*> arbitrary
        , (Nm <$>) . oneof $
            [ pure [ch] | ch <- "abcdefgh" ++ "j" ++ "lmnopqr" ++ "tuvwxyz"
                                ++ "ABCDEFGHIJKLMNOPQRSTUVWXYZ" ]
            ++ [pure "iota"]

        , do
            jotexp <- listOf1 . oneof . map pure $ "01"
            return $ Jot (length jotexp) jotexp
        -- , In . abs <$> arbitrary
        ]

-- | Lazy Kプログラムの入力状態と、出力オプション
data IoInfo = IoInfo
    { inEof :: !Bool    -- ^ 標準入力が EOF に達したか。
    , inHist :: ![Int]  -- ^ 受信済みの標準入力データ。
                        -- EOF 到達後のインデックスを読み出した場合、
                        -- 256 が補完される。
    , optV :: !Bool      -- ^ 起動時に-vオプションが指定されているか。
    , progDot :: ProgDot -- ^ 進捗dotを表示すべきの出力頻度。
    } deriving (Eq, Ord, Show)

instance Default IoInfo where
    def = IoInfo False [] False def

lamSize :: LamExpr -> Int
lamSize (App s _ _) = s
lamSize (L s _)     = s
lamSize (Jot s _)   = s
lamSize _           = 1

-- | 関数適用の演算子
infixl 5 %:
(%:) :: LamExpr -> LamExpr -> LamExpr
a %: b = App (1 + lamSize a + lamSize b) a b

-- | ラムダ抽象の演算子
la :: LamExpr -> LamExpr
la a = L (1 + lamSize a) a


{-
 - Show Functions
instance Show LamExpr where
    show e = ret
      where Stringifying ret _ _ = toNamedString def e
 -}

-- | NameMamager の命名ポリシー
data PolicyKind = PK_index      -- ^ 名前を付けず、De Bruijn index で表示。
                | PK_single_use -- ^ 全てのラムダ抽象に、異なる名前を付ける。
                | PK_level      -- ^ ラムダ抽象の深さに応じて、名前を付ける。
                | PK_minimum    -- ^ 自由変数として使用されている名前を調べ、
                                -- Poolの消費が最小になるように名前を付ける。
    deriving (Eq, Ord, Show)

instance Arbitrary PolicyKind where
    arbitrary = oneof $ map return [
          PK_index, PK_single_use, PK_level, PK_minimum
        ]

-- | ラムダ式を表示する際に変数に名前を付けるための管理データ
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

instance Arbitrary NameManager where
    arbitrary = NameManager <$> arbitrary
        <*> shuffle ("abcdefgh" ++ "j" ++ "lmnopqr" ++ "tuvwxyz"
                ++ "ABCDEFGH" ++ "J" ++ "LMNOPQR" ++ "TUVWXYZ_")
        <*> pure ""
        <*> arbitrary

data StyleInfoKind = SK_PureIota | SK_IotaUnlam | SK_General | SK_Error
                    deriving (Eq, Show)

-- | ラムダ式を文字列化した結果の情報
data Stringifying = Stringifying String StyleInfoKind NameManager
                    deriving (Show)

-- | docstring用に、toNamedString から手早く LamExpr を取り出す。
takeStringified :: Stringifying -> String
takeStringified (Stringifying str _ _) = str

-- | ラムダ式を文字列化
-- De Bruijn index の変数は、'_'を付けて表示する。
-- 入力プロミスは、'<'を付けて表示する。
--
-- >>> takeStringified $ toNamedString def $ la . la $ V 2
-- "\\xy.x"
-- >>> takeStringified $ toNamedString def $ la . la $ V 1
-- "\\xx.x"
-- >>> takeStringified $ toNamedString def $ (Jot 1 "0" %: Nm "q") %: Nm "iota"
-- "*(0q)i"
-- >>> takeStringified $ toNamedString def $ la $ V 1 %: In 0 -- 入力プロミス
-- "\\x.x<0"
toNamedString :: NameManager -> LamExpr -> Stringifying
toNamedString mng (V v) = Stringifying name SK_General mng
  where
    name = case v <= length (nmStack mng) of
            True
                | (nmStack mng !! (v - 1)) /= ' ' -> [nmStack mng !! (v - 1)]
            -- De Bruijn index は先頭に'_'を付ける。
            _                                     -> '_' : show v
toNamedString mng (In ix) = Stringifying ("<" ++ show ix) SK_General mng
toNamedString mng e@(L _ _) = Stringifying ('\\':str_ret) style_ret mng_ret
  where
    Stringifying str_ret style_ret mng_ret = digLamAbst mng e
toNamedString mng (App _ (Nm "I") (Nm "iota"))
                                        -- "(I)(iota)" は、これなら表現できる。
                                        = Stringifying "*Ii" SK_General mng
toNamedString mng (App _ (Nm "iota") (Nm "I"))
                                        -- "(iota)(I)" は、これなら表現できる。
                                        = Stringifying "*iI" SK_General mng
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
    par_fun = case (fun, style_fun, appOp) of
        (L _ _, _, _) -> "(" ++ str_fun ++ ")"
        (App _ _ _, SK_General, "*") -> "(" ++ str_fun ++ ")"
        _     -> str_fun
    par_oprd = case (oprd, style_oprd) of
        (L _ _, _)              -> "(" ++ str_oprd ++ ")"
        (App _ _ _, SK_General) -> "(" ++ str_oprd ++ ")"
        (Jot _ _, _) -> case lastLeaf fun of
                            Jot _ _ -> "(" ++ str_oprd ++ ")"
                            _       -> str_oprd
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

lastLeaf :: LamExpr -> LamExpr
lastLeaf (App _ _ oprd) = lastLeaf oprd
lastLeaf (L _ lexp) = lastLeaf lexp
lastLeaf e = e

-- | 連続するラムダ抽象を考慮した文字列化
--
-- >>> takeStringified $ digLamAbst def $ la . la $ V 2
-- "xy.x"
-- >>> takeStringified $ digLamAbst (NameManager {nmPolicy = PK_minimum, nmPool = "xyzabcdefghjlmnopqrtuvwXYZABCDEFGHJLMNOPQRTUVW", nmStack = "x", nmUnlamStyle = False}) $ la $ V 2
-- "y.x"
-- >>> takeStringified $ digLamAbst def $ la . la $ V 1
-- "xx.x"
digLamAbst :: NameManager
        -> LamExpr
        -> Stringifying  -- ^ 文字列は、ラムダ抽象でbindされる名前。
                         -- λ xyz.XXX なら、"xyz"。indexの逆順。
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
digLamAbst _     _          = error $ "Internal Error : digLamAbst: not L"

-- | ラムダ抽象への名前の付与
--
-- ラムダ式を文字列化する際に、ラムダ抽象された変数に名前を付ける。
-- 付けた名前は、返り値に含めるとともに、nmStackの先頭に積む。
-- 
-- >>> enterLambda def $ la . la $ V 2
-- ("x",NameManager {nmPolicy = PK_minimum, nmPool = "xyzabcdefghjlmnopqrtuvwXYZABCDEFGHJLMNOPQRTUVW", nmStack = "x", nmUnlamStyle = False})
enterLambda :: NameManager -> LamExpr -> (String, NameManager)
enterLambda mng@NameManager{nmPolicy = PK_index} _
        = (" ", mng{nmStack = ' ' : nmStack mng}) -- leaveLambda用に空白追加。
enterLambda mng@NameManager{nmPolicy = PK_single_use, nmPool = ""} _
        = (" ", mng{nmStack = ' ' : nmStack mng})
enterLambda mng@NameManager{nmPolicy = PK_single_use, nmPool = car' : cdr} expr
    -- Poolの次候補が使用中の名前と被っていたらその名前は捨てて、再帰。
    | [car] `elem` usingNames mng expr = enterLambda mng{nmPool = cdr} expr
    | otherwise = ([car], mng{nmStack = car : nmStack mng, nmPool = cdr})
  where car = case car' of
            '_' -> ' '  -- 見易さの為、poolの設定に'_'を使うことを許容する。
            _   -> car'
enterLambda mng@NameManager{nmPolicy = PK_level} expr
    -- PK_level なら、他のパスではnext_chを使えるかもしれないが、
    -- そこまで厳密に判定するメリットは思いつかないので、破棄して再帰。
    | [next_ch] `elem` usingNames mng expr = enterLambda mng{nmPool = rem} expr
    | length (nmStack mng) < length (nmPool mng)
        = ([next_ch], mng{nmStack = next_ch : nmStack mng})
    | otherwise
        = (" ", mng{nmStack = ' ' : nmStack mng})
  where
    next_ch = case nmPool mng !! length (nmStack mng) of
            '_' -> ' '  -- 見易さの為、poolの設定に'_'を使うことを許容する。
            ch  -> ch
    rem = take (length (nmStack mng)) (nmPool mng) ++
          drop (length (nmStack mng) + 1) (nmPool mng)
enterLambda mng@NameManager{nmPolicy = PK_minimum} expr
        = ([newName], mng{nmStack = newName : nmStack mng})
  where
    allname = usingNames mng expr
    -- 他のpolicyと同じように、' ' と '_'を使うことを許容するが、
    -- PK_minimum では、pool順に変数が使われるとは限らない。
    -- poolの設定に従って de Bruijn index を使うユースケースが
    -- 重要とは思えないので、機能は実装しない。単に無視する。
    newName = (!!0) . filter (\nm -> nm `notElem` "_ "
                                    && S.notMember [nm] allname) $ nmPool mng

usingNames :: NameManager -> LamExpr -> S.Set String
usingNames mng expr = foldl foldStep names . S.toList $ idxes
  where
    foldStep set ix
        | ix <= length (nmStack mng) = S.insert [nmStack mng !! (ix - 1)] set
        | otherwise                 = set
    -- digLamAbstから呼出され、ラムダ抽象のLが渡される。
    -- 1 が新たにbindすべき変数。1を検出できるよう 0 を渡す。
    (names, idxes, _) = getFreeVars expr 0

leaveLambda :: NameManager -> NameManager
leaveLambda mng@NameManager{nmStack = (_ : cdr)} = mng{nmStack = cdr}
leaveLambda     NameManager{nmStack = _} = error "leaveLambda: empty nmStack"

-- | 自由変数の一覧取得 (入力プロミスを含む)
-- 指定のラムダ抽象の深さより大きいde Bruijn indexの変数と
-- 全ての名前付き変数をpickup。
-- getFreeVars expr 0 として使うことで、expr の中の自由変数を取り出せる。
--
-- >>> getFreeVars (V 1) 0
-- (fromList [],fromList [1],fromList [])
-- >>> getFreeVars (la $ V 1) 0   -- la中のV 1は束縛されているので対象外。
-- (fromList [],fromList [],fromList [])
-- >>> getFreeVars (la $ V 1 %: V 3) 0 -- V 3は自由変数。Lの外ではV 2に該当。
-- (fromList [],fromList [2],fromList [])
-- >>> getFreeVars (Nm "y" %: la (Nm "x")) 0  -- 名前付き変数は全て自由変数。
-- (fromList ["x","y"],fromList [],fromList [])
-- >>> getFreeVars (Nm "iota" %: Nm "S") 0  -- Lazy Kの変数は対象外とする。
-- (fromList [],fromList [],fromList [])
-- >>> getFreeVars (In 8) 0            -- 入力プロミスも取り出すことにする。
-- (fromList [],fromList [],fromList [8])
getFreeVars :: LamExpr  -- ^ 取得対象のラムダ式
        -> Int          -- ^ ラムダ抽象の深さ。ラムダ抽象が無ければ 0。
        -> (S.Set String, S.Set Int, S.Set Int)
getFreeVars (V v) dep
    | v > dep = (S.empty, S.singleton (v - dep), S.empty)
    | otherwise = (S.empty, S.empty, S.empty)
getFreeVars (L _ lexp) dep = getFreeVars lexp (dep + 1)
getFreeVars (App _ fun oprd) dep
    = (f_name `S.union` o_name, f_idx `S.union` o_idx, f_in `S.union` o_in)
  where
    (f_name, f_idx, f_in) = getFreeVars fun (dep)
    (o_name, o_idx, o_in) = getFreeVars oprd (dep)
getFreeVars (Nm name) _
    | (name !! 0) `elem` "iksIKS" = (S.empty, S.empty, S.empty)
    | otherwise                   = (S.singleton [name !! 0], S.empty, S.empty)
-- 入力プロミスは、自由変数として取得できるようにしておく。
getFreeVars (In ix) _ = (S.empty, S.empty, S.singleton ix)
getFreeVars _       _ = (S.empty, S.empty, S.empty)

-- | Lazy Kソースを含めたラムダ式の文字列の読み込み
-- De Bruijn index の変数は、'_'+数字 (1以上) で表示されている。
-- 入力プロミスは、'<'+数字 (0以上) で表示されている。
--
-- >>> readLazyK "dummy title" "\\ n" -- 無名ラムダと名前付き変数の組合せ
-- Right (L 2 (Nm "n"))
-- >>> readLazyK "dummy title" "\\xy.x"
-- Right (L 3 (L 2 (V 2)))
-- >>> readLazyK "dummy title" "\\xy.y"
-- Right (L 3 (L 2 (V 1)))
-- >>> readLazyK "dummy title" "\\xx.x"  -- シャドーイングされるケース
-- Right (L 3 (L 2 (V 1)))
readLazyK :: String -- ^ 読み込むソースのタイトル
        -> String   -- ^ 読み込むソースの内容
        -> Either String LamExpr
readLazyK title input = case parse exprs title . trimComment $ input of
    Left err  -> Left $ show err
    Right val -> Right val
  where
    trimComment = unlines . map untilHash . lines
    -- コメントの先頭(='#') まで、または全行を取り出す。
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
    <|> In . read <$> (char '<' *> many1 digit) <* spaces
    <|> char '`' *> spaces *> return (%:) <*> unlamExpr <*> unlamExpr
    <|> char '*' *> spaces *> return (%:) <*> iotaExpr <*> iotaExpr
    <|> (\s -> Jot (length s) s) . filter (not . isSpace) <$>
                                                many1 (oneOf "01" <* spaces)
    <|> bindIdx <$> absts <*> exprs
    <|> char '(' *> spaces *> exprs <* char ')' <* spaces

absts = fmap concat $ many1 abst

abst = char '\\' *> spaces *> abst'

abst' = try ( (map (\a -> [a])) <$>
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
data RedResult e = RedStop ProgDot Int e
    -- ^ Intが負なら、簡約出来る箇所が無かった。
    --   Intが0以上なら、簡約出来る箇所を見付ける前に
    --   Inputプロミスにぶつかり、indexがIntの値だった。
                | RedProg ProgDot Int e
    -- ^ Intが負なら、簡約出来た。
    --   Intが0以上なら、一部簡約出来たが、その後、
    --   Inputプロミスにぶつかり、indexがIntの値だった。
    deriving (Show)

forceProg :: RedResult e -> RedResult e
forceProg (RedStop d i e) = RedProg d i e
forceProg prog            = prog

data ProgDot = ProgDot ![Int] deriving (Eq, Ord, Show)

instance Default ProgDot where
    def = ProgDot [0, 0]

instance Num ProgDot where
    (+) (ProgDot d1) (ProgDot d2) = ProgDot (zipWith (+) d1 d2)
    (*) (ProgDot d1) (ProgDot d2) = ProgDot (zipWith (*) d1 d2)
    negate (ProgDot d) = ProgDot (map negate d)
    abs (ProgDot d) = ProgDot (map abs d)
    signum (ProgDot d) = ProgDot (map signum d)
    fromInteger n = ProgDot [fromInteger n, 0]

incPd :: Int -> RedResult e -> RedResult e
incPd 1 (RedStop d i e) = RedStop (d + ProgDot [0, 1]) i e
incPd 1 (RedProg d i e) = RedProg (d + ProgDot [0, 1]) i e
incPd 0 (RedStop d i e) = RedStop (d + ProgDot [1, 0]) i e
incPd 0 (RedProg d i e) = RedProg (d + ProgDot [1, 0]) i e
incPd _ r               = r

incPds :: ProgDot -> RedResult e -> RedResult e
incPds ds (RedStop d i e) = RedStop (d + ds) i e
incPds ds (RedProg d i e) = RedProg (d + ds) i e

isPdMature :: Int -> IoInfo -> ProgDot -> Bool
isPdMature n IoInfo{progDot = ProgDot mat} (ProgDot d)
    | mat !! n == 0            = False
    | n >= length mat || n < 0 = False
    | otherwise                = (d !! n) >= (mat !! n)

clearPd :: Int -> ProgDot -> ProgDot
clearPd n (ProgDot ioInf) = ProgDot $ zipWith setNto0 [0..] ioInf
  where
    setNto0 i x = if i == n then 0 else x

instance Functor RedResult where
    fmap f (RedStop pd i e) = RedStop pd i (f e)
    fmap f (RedProg pd i e) = RedProg pd i (f e)

instance Applicative RedResult where
    pure = RedStop def (-1)
    RedStop dF i f <*> RedStop dE j e = RedStop (dF + dE) (max i j) (f e)
    RedStop dF i f <*> RedProg dE j e = RedProg (dF + dE) (max i j) (f e)
    RedProg dF i f <*> RedStop dE j e = RedProg (dF + dE) (max i j) (f e)
    RedProg dF i f <*> RedProg dE j e = RedProg (dF + dE) (max i j) (f e)

instance Monad RedResult where
    RedStop dE i e >>= f = case f e of
        RedStop dF j e' -> RedStop (dE + dF) (max i j) e'
        RedProg dF j e' -> RedProg (dE + dF) (max i j) e'
    RedProg dE i e >>= f = case f e of
        RedStop dF j e' -> RedProg (dE + dF) (max i j) e'
        RedProg dF j e' -> RedProg (dE + dF) (max i j) e'

{- | Beta簡約の実行 (入力の遅延評価対応)

 入力が遅延評価される前提で、可能な範囲でbeta簡約を行う。
 入力プロミスを評価する必要が出た時点で、評価を停止し、
 返り値に何byte目の入力が必要かの情報を含める。
 -}
betaRed :: IoInfo
        -> ProgDot  -- ^ beta簡約を実行した回数。
        -> LamExpr
        -> RedResult LamExpr
betaRed ioInf d              (L _ le)    = la <$> betaRed ioInf d le
betaRed ioInf d            e@(App _ (L _ _) _)
    | isPdMature 1 ioInf d = RedStop d (-1) e
betaRed ioInf d              (App _ (L _ le) e) = case once of
    -- beta簡約の結果が、再び関数適用だった。
    -- ここまで簡約出来る箇所が無かった結果ここで簡約を行ったので、
    -- 先頭から見直しても結局ここに戻ってくる。
    -- それは無駄なので、ここから betaRed を継続する。
    App _ _ _ -> incPd 1 . forceProg $ betaRed ioInf d once
    _         -> incPd 1 . forceProg . incPds d $ pure once
  where
    once = comple (subst 1 e) le
betaRed ioInf@(IoInfo eof input _ _) d e@(App s (In ix) oprd)
    -- 現時点で展開可能な入力があるので、それを使って続行。
    | eof || ix < length input =
        forceProg $ betaRed ioInf d $ App s (buildInput ioInf ix) oprd 
    -- Inputプロミスは外部情報が必要なので、一旦 betaRed を止める。
    | otherwise = RedStop d ix e
betaRed ioInf            d e@(App _ x y) = case betaRed ioInf d x of
    RedStop d' i _
        | isPdMature 1 ioInf d' -> RedStop d' i e
        | i >= 0     -> RedStop d' i e  -- Inputプロミスでblockした。
        | otherwise  -> RedStop def i (x %:) <*> betaRed ioInf d' y
    -- x で進展があったものの、関数適用であることには変わりない。
    -- しかし、x が (L _ _) なら、beta還元可能。
    RedProg d' _ e'@(L _ _) -> forceProg $ betaRed ioInf d' (e' %: y)
    -- そうでなければ、一旦行けるところまで行ったので、戻る。
    x'                ->  (%:) <$> x' <*> pure y
betaRed ioInf@(IoInfo eof input _ _) d e@(In ix)
    -- 現時点で展開可能な入力がある。cons なので、beta還元は出来ない。
    -- In がリストに変わるので、RedProg を返す。
    | eof || ix < length input = RedProg d (length input) $ buildInput ioInf ix
    -- Inputプロミスは外部情報が必要なので、一旦 betaRed を止める。
    | otherwise = RedStop d ix e
betaRed _ d e            = incPds d $ return e     -- V and Nm

-- | Inputプロミスを置換える実リストを生成
buildInput :: IoInfo    -- ^ 標準入力の履歴と進捗Dotの表示頻度
            -> Int      -- ^ beta還元に必要なinputのインデックス
            -> LamExpr  -- ^ 判明しているinputを展開したラムダ式
buildInput (IoInfo eof input _ _) ix
    | ix < length input = foldr makeCons (In (length input)) $ drop ix input
    | eof = foldr makeCons (In (length compInput)) $ drop ix compInput
    | otherwise = error "buildInput: called under unexpected condition"
  where
    makeCons carNum cdr = la $ V 1 %: makeChuchNum carNum %: cdr
    compInput
        | eof = input ++ take (ix - length input + 1) [256, 256 ..]
        | otherwise = input

-- | 変化しなくなるまで、beta還元を繰り返す。
betaRedInf :: LamExpr -> LamExpr
betaRedInf e = case betaRed def def e of
    RedProg _ _ red -> betaRedInf red
    RedStop _ _ red -> red

-- | Church encodingで、ix を表現するラムダ式を生成
makeChuchNum :: Int -> LamExpr
makeChuchNum ix = la . la . applyN ix (V 2 %:) $ V 1

-- | 指定した de Bruijn index の変数を指定した式に置換
--
-- subst 1 e expr は、(λ expr)(e) を計算する。
-- つまり、expr の中の V 1 を e に置換する。
-- ラムダ抽象が消費されるので、expr 中の自由変数の index は -1 される。
-- expr の中で導入された変数は、影響を受けない。
-- expr の内容が変化する場合にのみ、Just で計算後の式を返す。
-- 変化しない場合は Nothing を返す。
--
-- >>> subst 1 (V 3) (V 1 %: V 2)    -- (λ _1_2)_3
-- Just (App 3 (V 3) (V 1))
-- >>> subst 1 (V 3) (V 1 %: la (V 2))
-- Just (App 4 (V 3) (L 2 (V 4)))
-- >>> subst 2 (V 3) (V 1 %: V 5 %: V 2)
-- Just (App 5 (App 3 (V 1) (V 4)) (V 3))
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
    | hasVar 2 le = Just . comple abstElim . la . comple abstElim $ inner --R.5
    | otherwise   = error $ "out of rule 5: " ++ show (la inner)
abstElim (L _ (App _ m (V 1)))
    | not (hasVar 1 m) = Just . comple (shallow 1) $ m  -- Eta reduction
abstElim (L _ (App _ m n)) =
    Just $ Nm "S" %: comple abstElim (la m) %: comple abstElim (la n) -- Rule 6
abstElim (L _ (In _)) = Nothing

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
 - Common Utility Functions
 -}

-- |
-- Complement original value if it is evaluated to Nothing
comple :: (a -> Maybe a) -> a -> a
comple f a = maybe a id $ f a

mergeApp :: (LamExpr -> Maybe LamExpr) -> LamExpr -> LamExpr -> Maybe LamExpr
mergeApp f x y = case (f x, f y) of
    (Just x', Just y') -> Just $ x' %: y'
    (Just x', Nothing) -> Just $ x' %: y
    (Nothing, Just y') -> Just $ x  %: y'
    _                  -> Nothing


{- 以降は使っていないが、後で速度比較をするために残しておく。

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
-}
