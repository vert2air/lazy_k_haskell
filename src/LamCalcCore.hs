{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedRecordDot #-}

{- |
  Module      : LamCalcCore
  Description : Lazy K と ラムダ式 のデータ構造と処理のcore部分
-}

module LamCalcCore where

import           Data.Default (Default(..))
import           Data.Char (isDigit, isSpace, toUpper, toLower)
import           Data.Either (fromRight)
import           Data.List (elemIndex)
import qualified Data.Map as M (Map, empty, insert, lookup)
import qualified Data.Set as S (Set, empty, insert,
                                notMember, singleton, toList, union)
import Test.QuickCheck (Arbitrary(..), Gen, oneof, listOf1, shuffle,
                        suchThat, vectorOf)
import           Text.Parsec ((<|>), (<?>), Parsec, char, digit, many1, oneOf,
                              parse, spaces, try)

import ShortChurchNum (shortChNum)

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
            | Num !Int          -- ^ 数値。整数。Church数を整数に変換時に使用。
        deriving (Eq)

instance Show LamExpr where
    -- red_ccN から呼ばれるケースでも使いたいので、PK_indexを採用。
    show = takeStringified . toNamedString def { nmPolicy = PK_index }

instance Arbitrary LamExpr where
    arbitrary = oneof [
          -- De Bruijn index はラムダの深さなので、
          -- 大き過ぎると自由変数ばかりになってしまう。
          -- ラムダの深さは、対数スケールで増加する筈なので、log で圧縮する。
          V . (+1) . floor . log . (+1) . abs <$> (arbitrary :: Gen Float)
        , do
            lexp <- arbitrary
            case lexp of
                -- '*' が無いと Iotaスタイルは表現できない。やり直す。
                Nm "iota" -> la <$> arbitrary
                _         -> return $ la lexp
        , (%:) <$> arbitrary <*> arbitrary
        , (Nm <$>) . oneof $
            -- SKI および、iota を多めに。
            [ pure [ch] | ch <- "SKISKISKISKISKI" ++ "SKSKSKSKSK" ++ "SSSSS"
                            ++ "abcdefgh" ++ "j" ++ "lmnopqr" ++ "tuvwxyz"
                            ++ "ABCDEFGH" ++ "J" ++ "LMNOPQR" ++ "TUVWXYZ" ]
            ++ [pure "iota", pure "iota", pure "iota"]

        , do
            jotexp <- listOf1 . oneof . map pure $ "01"
            return $ Jot (length jotexp) jotexp
        -- , In . abs <$> arbitrary
        ]

-- ラムダ式の長さを取得
--
-- Unlambdaスタイルで表示した時の文字列長を基準に算出。
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
                         -- PK_index では、参照しない。
                         -- PK_single_use では、払出す度に一文字ずつ短くなる。
    , nmStack  :: String -- ^ 命名した変数のスタック。
                         -- 文字列の1個ずつが払い出した名前。
                         -- 先頭が de Bruij Index = 1 に対応。
                         -- 空白なら、名前でなく、de Bruijn index で表示する。
    , nmUnlamStyle :: Bool -- ^ 真なら、S, K, I を Unlambdaスタイルで表示する。
    , nmLamSign :: Char -- ^ ラムダ抽象の記号。'λ'か'\\'を想定。
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
        , nmLamSign = 'λ'
        }

instance Arbitrary NameManager where
    arbitrary = NameManager <$> arbitrary
        <*> shuffle ("abcdefgh" ++ "j" ++ "lmnopqr" ++ "tuvwxyz"
                ++ "ABCDEFGH" ++ "J" ++ "LMNOPQR" ++ "TUVWXYZ_")
        <*> pure ""
        <*> arbitrary
        <*> oneof [pure 'λ', pure '\\']

data StyleInfoKind = SK_PureIota | SK_IotaUnlam | SK_General | SK_Error
                    deriving (Eq, Show)

-- | ラムダ式を文字列化した結果の情報
data Stringifying = Stringifying String StyleInfoKind NameManager
                    deriving (Show)

takeStringified :: Stringifying -> String
takeStringified (Stringifying str _ _) = str

-- | docstring用に、toNamedString から手早く LamExpr を取り出す。
-- また、putStrLn を使わないと、λ が \955 と表示されてしまう。
putExprLn :: Stringifying -> IO ()
putExprLn = putStrLn . takeStringified

-- | ラムダ式を文字列化
--
-- De Bruijn index の変数は、'_'を付けて表示する。
-- 入力プロミスは、'<'を付けて表示する。
-- Lazy Kのコードとの混在も対応。
--
-- >>> putExprLn $ toNamedString def $ la . la $ V 2
-- λxy.x
-- >>> putExprLn $ toNamedString def {nmLamSign='\\'} $ la . la $ V 2
-- \xy.x
-- >>> putExprLn $ toNamedString def $ la . la $ V 1
-- λxx.x
-- >>> putExprLn $ toNamedString def $ (Jot 1 "0" %: Nm "q") %: Nm "iota"
-- *(0q)i
-- >>> putExprLn $ toNamedString def $ la $ V 1 %: In 0 -- 入力プロミス
-- λx.x<0
-- >>> let expr = Nm "S" %: Nm "K" %: (Nm "I" %: Nm "K")
-- >>> putExprLn $ toNamedString def {nmUnlamStyle=True} expr
-- ``sk`ik
-- >>> putExprLn $ toNamedString def {nmUnlamStyle=False} expr
-- SK(IK)
toNamedString :: NameManager -> LamExpr -> Stringifying
toNamedString mng (V v) = Stringifying name SK_General mng
  where
    name = case v <= length (nmStack mng) of
            True
                | (nmStack mng !! (v - 1)) /= ' ' -> [nmStack mng !! (v - 1)]
            -- De Bruijn index は先頭に'_'を付ける。
            _                                     -> '_' : show v
toNamedString mng (In ix) = Stringifying ("<" ++ show ix) SK_General mng
toNamedString mng (Num n) = Stringifying ("%" ++ show n)  SK_General mng
toNamedString mng e@(L _ _) =
                    Stringifying ((nmLamSign mng):str_ret) style_ret mng_ret
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
        (_, SK_IotaUnlam, _, SK_IotaUnlam) -> ("`", SK_IotaUnlam)
        (_, SK_PureIota, _, SK_IotaUnlam) -> ("`", SK_IotaUnlam)
        (_, SK_IotaUnlam, _, SK_PureIota) -> ("`", SK_IotaUnlam)
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
-- >>> putExprLn $ digLamAbst def $ la . la $ V 2
-- xy.x
-- >>> putExprLn $ digLamAbst (NameManager {nmPolicy = PK_minimum, nmPool = "xyzabcdefghjlmnopqrtuvwXYZABCDEFGHJLMNOPQRTUVW", nmStack = "x", nmUnlamStyle = False, nmLamSign = 'λ'}) $ la $ V 2
-- y.x
-- >>> putExprLn $ digLamAbst def $ la . la $ V 1
-- xx.x
digLamAbst :: NameManager
        -> LamExpr
        -> Stringifying  -- ^ 文字列は、ラムダ抽象でbindされる名前。
                         -- λ xyz.XXX なら、"xyz"。indexの逆順。
digLamAbst mng e@(L _ lexp@(L _ _)) = case (newName, ret) of
    (' ':_, _    ) -> Stringifying (' ':nmLamSign mng:ret) SK_General mng_ret
    (n:_  , ' ':_) -> Stringifying (n:'.':' ':nmLamSign mng:ret)
                                                            SK_General mng_ret
    (n:_  , _    ) -> Stringifying (n:ret)                  SK_General mng_ret
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
-- >>> enterLambda def $ la . la $ V 2   -- '\955' は 'λ' のUnicodeコード。
-- ("x",NameManager {nmPolicy = PK_minimum, nmPool = "xyzabcdefghjlmnopqrtuvwXYZABCDEFGHJLMNOPQRTUVW", nmStack = "x", nmUnlamStyle = False, nmLamSign = '\955'})
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
    | [next_ch] `elem` usingNames mng expr = enterLambda mng{nmPool = rmn} expr
    | length (nmStack mng) < length (nmPool mng)
        = ([next_ch], mng{nmStack = next_ch : nmStack mng})
    | otherwise
        = (" ", mng{nmStack = ' ' : nmStack mng})
  where
    next_ch = case nmPool mng !! length (nmStack mng) of
            '_' -> ' '  -- 見易さの為、poolの設定に'_'を使うことを許容する。
            ch  -> ch
    rmn = take (length (nmStack mng)) (nmPool mng) ++
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
--
-- λ記号は、'λ'と'\\'の両方を許容する。
-- De Bruijn index の変数は、'_'+数字 (1以上) で表示されている。
-- 入力プロミスは、'<'+数字 (0以上) で表示されている。
--
-- >>> readLazyK "dummy title" "λ n" -- 無名ラムダと名前付き変数の組合せ
-- Right λ n
-- >>> readLazyK "dummy title" "λxy.x"
-- Right λ λ _2
-- >>> readLazyK "dummy title" "λxy.y"
-- Right λ λ _1
-- >>> readLazyK "dummy title" "\\xx.x"  -- シャドーイングされるケース
-- Right λ λ _1
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

-- | 関数を繰り返し適用
--
-- >>> show $ applyN 3 (Nm "f" %:) (Nm "x")
-- "f(f(fx))"
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
    <|> Num . read <$> (char '%' *> many1 digit) <* spaces
    <|> char '`' *> spaces *> return (%:) <*> unlamExpr <*> unlamExpr
    <|> char '*' *> spaces *> return (%:) <*> iotaExpr <*> iotaExpr
    <|> (\s -> Jot (length s) s) . filter (not . isSpace) <$>
                                                many1 (oneOf "01" <* spaces)
    <|> bindIdx <$> absts <*> exprs
    <|> char '(' *> spaces *> exprs <* char ')' <* spaces

absts = fmap concat $ many1 abst

-- ラムダは、バックスラッシュとギリシャ文字のラムダを許可。
abst = oneOf ['\\', 'λ'] *> spaces *> abst'

abst' = try ( (map (\a -> [a])) <$>
        (many1 (oneOf ("ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                       ++ "abcdefghijklmnopqrstuvwxyz") <* spaces)
        <* char '.' <* spaces ))
    <|> return [""]

-- | ラムダ式中のLazy Kの組み込み関数をラムダ式で置換
--
-- 自由変数や入力promise等は、そのまま変更しない。
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
toLambda e@(Num _)   = e  -- 変換できないので、そのまま。

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

-- | Beta/Eta簡約の結果
data RedResult e = RedStop ProgDot Int e
    -- ^ Intが負なら、簡約出来る箇所が無かった。
    --   Intが0以上なら、簡約出来る箇所を見付ける前に
    --   Inputプロミスにぶつかり、indexがIntの値だった。
                | RedProg ProgDot Int e
    -- ^ Intが負なら、簡約出来た。
    --   Intが0以上なら、一部簡約出来たが、その後、
    --   Inputプロミスにぶつかり、indexがIntの値だった。
    deriving (Show)

instance Functor RedResult where
    fmap f (RedStop pd i e) = RedStop pd i (f e)
    fmap f (RedProg pd i e) = RedProg pd i (f e)

instance Applicative RedResult where
    pure = RedStop def (-1)
    RedStop dF i f <*> RedStop dE j e = RedStop (dF + dE) (max i j) (f e)
    RedStop dF i f <*> RedProg dE j e = RedProg (dF + dE) (max i j) (f e)
    RedProg dF i f <*> RedStop dE j e = RedProg (dF + dE) (max i j) (f e)
    RedProg dF i f <*> RedProg dE j e = RedProg (dF + dE) (max i j) (f e)

-- | RedResult の中の式を取り出す。
takeExpr :: RedResult e -> e
takeExpr (RedStop _ _ e) = e
takeExpr (RedProg _ _ e) = e

-- | RedStop でも、RedProg に書き換え。
forceProg :: RedResult e -> RedResult e
forceProg (RedStop d i e) = RedProg d i e
forceProg prog            = prog

-- | 進捗Dot用のカウントデータ
data ProgDot = ProgDot ![Int] deriving (Eq, Ord, Show)

instance Default ProgDot where
    def = ProgDot [0, 0]

instance Arbitrary ProgDot where
    arbitrary = ProgDot <$> vectorOf 2 (arbitrary `suchThat` (>= 0))

instance Num ProgDot where
    (+) (ProgDot d1) (ProgDot d2) = ProgDot (zipWith (+) d1 d2)
    (*) (ProgDot d1) (ProgDot d2) = ProgDot (zipWith (*) d1 d2)
    negate (ProgDot d) = ProgDot (map negate d)
    abs (ProgDot d) = ProgDot (map abs d)
    signum (ProgDot d) = ProgDot (map signum d)
    fromInteger n = ProgDot [fromInteger n, 0]

-- | Lazy Kプログラムの入力状態と、出力オプション
data IoInfo = IoInfo
    { inEof :: !Bool    -- ^ 標準入力が EOF に達したか。
    , inHist :: ![Int]  -- ^ 受信済みの標準入力データ。
                        -- EOF 到達後のインデックスを読み出した場合、
                        -- 256 が補完される。
    , optV :: !Bool      -- ^ 起動時に-vオプションが指定されているか。
    , progDot :: ProgDot -- ^ 進捗dotを表示すべきの出力頻度。
    , lamSign :: Char -- ^ ラムダ抽象の記号。'λ'か'\\'を想定。
    , startCPUTime :: !Integer -- ^ 開始時の getCPUTime
    } deriving (Eq, Ord, Show)

instance Default IoInfo where
    def = IoInfo False [] False def 'λ' 0

instance Arbitrary IoInfo where
    arbitrary = IoInfo
        <$> arbitrary
        <*> (map (`mod` 256) <$> arbitrary)
        <*> arbitrary
        <*> arbitrary
        <*> oneof [pure 'λ', pure '\\']
        <*> arbitrary

-- | 指定レベルの進捗Dotのカウンタを加算
incPd :: Int -> RedResult e -> RedResult e
incPd 1 (RedStop d i e) = RedStop (d + ProgDot [0, 1]) i e
incPd 1 (RedProg d i e) = RedProg (d + ProgDot [0, 1]) i e
incPd 0 (RedStop d i e) = RedStop (d + ProgDot [1, 0]) i e
incPd 0 (RedProg d i e) = RedProg (d + ProgDot [1, 0]) i e
incPd _ r               = r

-- | 各レベルの進捗Dotのカウンタを加算
incPds :: ProgDot -> RedResult e -> RedResult e
incPds ds (RedStop d i e) = RedStop (d + ds) i e
incPds ds (RedProg d i e) = RedProg (d + ds) i e

-- | 進捗Dotを出力条件が満たされたか。
isPdMature :: Int -> IoInfo -> ProgDot -> Bool
isPdMature n IoInfo{progDot = ProgDot mat} (ProgDot d)
    | mat !! n == 0            = False
    | n >= length mat || n < 0 = False
    | otherwise                = (d !! n) >= (mat !! n)

-- | 進捗Dotのカウンタをクリア
clearPd :: Int -> ProgDot -> ProgDot
clearPd n (ProgDot ioInf) = ProgDot $ zipWith setNto0 [0..] ioInf
  where
    setNto0 i x = if i == n then 0 else x

-- | 変化しなくなるまで、指定された関数の適用を繰り返す。
untilStop :: (IoInfo -> ProgDot -> e -> RedResult e)
            -> IoInfo
            -> ProgDot
            -> e
            -> RedResult e
untilStop f ioInf d e = case f ioInf d e of
    r@(RedProg _io ix red)
        | ix >= 0              -> r
        | isPdMature 1 ioInf d -> r
        | otherwise            -> untilStop f ioInf d red
    r@(RedStop _ _ _) -> r

{- | Beta/Eta簡約の実行 (入力の遅延評価対応)

 入力が遅延評価される前提で、可能な範囲でbeta簡約およびeta簡約を行う。
 入力プロミスを評価する必要が出た時点で、評価を停止し、
 返り値に何byte目の入力が必要かの情報を含める。
 複雑さが増す可能性のある簡約実行時には ProgDot を更新する。
 -}
reduct :: (IoInfo -> Int -> LamExpr) -- ^ Inputプロミスを置換える実リスト生成
        -> IoInfo
        -> ProgDot  -- ^ beta簡約を実行した回数。
        -> LamExpr
        -> RedResult LamExpr
reduct bi ioInf d e = case once of
    -- 停止したのなら、続けても無駄。
    RedStop _  _  _                -> once
    -- 既に入力promiseに当たったのなら、続けても無駄。
    RedProg _  ix _    | ix >= 0    -> once
    -- 進捗Dotのカウンタが満たされたのなら、即return。
    RedProg d' _  _   | isPdMature 1 ioInf d' -> once
    -- 次に入力promiseに当たるのが分かっているのなら、続けても無駄。
    RedProg d' ix   (In _)
        -- 現時点で展開可能な入力がある。cons なので、beta簡約は出来ない。
        -- In がリストに変わるので、RedProg を返す。
        -- 先頭のInは解消されているので、indexは-1にしておく。
        | ioInf.inEof || ix < length ioInf.inHist ->
            RedProg d' (-1) $ bi ioInf ix
        -- Inputプロミスは外部情報が必要なので、一旦 reduct を止める。
        | otherwise                          -> once
    RedProg d' ix   (App _ (In _) oprd)
        -- 現時点で展開可能な入力があるので、それを使って続行。
        | ioInf.inEof || ix < length ioInf.inHist ->
            forceProg $ reduct bi ioInf d' $ bi ioInf ix %: oprd
        -- Inputプロミスは外部情報が必要なので、一旦 reduct を止める。
        | otherwise                          -> once

    RedProg d' _ e'@(App _ (Nm "+1")  _)            -> reduct bi ioInf d' e'
    RedProg d' _ e'@(App _ (Nm "I") _)              -> reduct bi ioInf d' e'
    -- 戻ったら簡約出来る可能性あり。戻る。
    RedProg _  _    (App _ (Nm _) _)                -> once
    RedProg d' _ e'@(App _ (App _ (Nm "K") _x) _y)  -> reduct bi ioInf d' e'
    RedProg d' _ e'@(App _ (App _ (Nm "S") (Nm "K")) _y)
                                                    -> reduct bi ioInf d' e'
    -- 戻ったら簡約出来る可能性あり。戻る。
    RedProg _  _    (App _ (App _ (Nm _) _x) _y)    -> once
    RedProg d' _ e'@(App _ (App _ (App _ (Nm "S") _x) _y) _z)
                                                    -> reduct bi ioInf d' e'
    -- β簡約が見えている。
    RedProg d' _  e'@(App _ (L _ _) _)              -> reduct bi ioInf d' e'
    RedProg _  _    _                               -> once
  where
    once = red_1 bi ioInf d e

{- | Beta/Eta簡約の実行 (入力の遅延評価対応)

 入力が遅延評価される前提で、可能な範囲でbeta簡約又はeta簡約を1回だけ行う。
 入力プロミスを評価する必要が出た時点で、評価を停止し、
 返り値に何byte目の入力が必要かの情報を含める。
 複雑さが増す可能性のある簡約実行時には ProgDot を更新する。
 -}
red_1 :: (IoInfo -> Int -> LamExpr) -- ^ Inputプロミスを置換える実リスト生成
        -> IoInfo
        -> ProgDot  -- ^ beta簡約を実行した回数。
        -> LamExpr
        -> RedResult LamExpr
-- 入力promiseの当たりをチェック
red_1 bi ioInf@(IoInfo eof input _ _ _ _) d e@(In ix)
    -- 現時点で展開可能な入力がある。cons なので、beta簡約は出来ない。
    -- In がリストに変わるので、RedProg を返す。
    | eof || ix < length input = RedProg d (length input) $ bi ioInf ix
    -- Inputプロミスは外部情報が必要なので、このままreturn。
    | otherwise = RedStop d ix e
red_1 bi ioInf@(IoInfo eof input _ _ _ _) d e@(App s (In ix) oprd)
    -- 現時点で展開可能な入力があるので、それを使って続行。
    | eof || ix < length input =
        forceProg $ red_1 bi ioInf d $ App s (bi ioInf ix) oprd
    -- Inputプロミスは外部情報が必要なので、このままreturn。
    | otherwise = RedStop d ix e

-- CC式の簡約
red_1 _b _io d (App _ (Nm "+1") (Num n))         = RedProg d (-1) . Num $ n + 1
red_1 _b _io d (App _ (Nm "I") x)                 = RedProg d (-1) x
red_1 _b _io d (App _ (App _ (Nm "K") x) _y)       = RedProg d (-1) x
red_1 _b _io d (App _ (App _ (Nm "S") (Nm "K")) _y) = RedProg d (-1) $ Nm "I"
red_1 _b _io d (App _ (App _ (App _ (Nm "S") (Nm "K")) _y) z)
                                                    = RedProg d (-1) z
-- CCの簡約でより複雑になるのは、このパターンだけ。ここだけ incPd する。
red_1 _b _io d (App _ (App _ (App _ (Nm "S") x) y) z)
                                = incPd 1 . RedProg d (-1) $ x %: z %: (y %: z)

-- eta簡約
red_1 _b _ioInf d (L _ (App _ fun (V 1)))
    | not (hasVar 1 fun) =
        RedProg d (-1) $ comple (shallow 1) fun

-- 以降は、beta簡約
red_1 bi ioInf d              (L _ le)    = la <$> red_1 bi ioInf d le
red_1 _b _ioInf d             (App _ (L _ le) e) =
    incPd 1 . RedProg d (-1) $ comple (subst 1 e) le

red_1 bi ioInf            d e@(App _ x y) = case red_1 bi ioInf d x of
    RedStop d' i _
        | isPdMature 1 ioInf d' -> RedStop d' i e
        | i >= 0     -> RedStop d' i e  -- Inputプロミスでblockした。
        | otherwise  -> (x %:) <$> red_1 bi ioInf d' y
    x'                ->  (%: y) <$> x'
red_1 _b _ d e            = RedStop d (-1) e -- V and Nm

-- | Inputプロミスを置換える実リストを生成
buildInputLc :: IoInfo    -- ^ 標準入力の履歴と進捗Dotの表示頻度
            -> Int      -- ^ beta簡約に必要なinputのインデックス
            -> LamExpr  -- ^ 判明しているinputを展開したラムダ式
buildInputLc (IoInfo eof input _ _ _ _) ix
    | ix < length input = foldr makeCons (In (length input)) $ drop ix input
    | eof = foldr makeCons (In (length compInput)) $ drop ix compInput
    | otherwise = error "buildInputLc: called under unexpected condition"
  where
    makeCons carNum cdr = la $ V 1 %: makeChuchNum carNum %: cdr
    compInput
        | eof = input ++ take (ix - length input + 1) [256, 256 ..]
        | otherwise = input

buildInputCc :: IoInfo  -- ^ 標準入力の履歴と進捗Dotの表示頻度
            -> Int      -- ^ beta簡約に必要なinputのインデックス
            -> LamExpr  -- ^ 判明しているinputを展開したラムダ式
buildInputCc (IoInfo eof input _ _ _ _) ix
    | ix < length input = foldr makeCons (In (length input)) $ drop ix input
    | eof = foldr makeCons (In (length compInput)) $ drop ix compInput
    | otherwise = error "buildInputCc: called under unexpected condition"
  where
    makeCons a d = Nm "S"
            %: (Nm "S" %: Nm "I" %: (Nm "K" %: ccNum a))
            %: (Nm "K" %: d)
    ccNum num = fromRight (error "ccNum in buildInputCC")
                $ readLazyK "buildInputCc" (shortChNum !! num)
    compInput
        | eof = input ++ take (ix - length input + 1) [256, 256 ..]
        | otherwise = input

-- | 変化しなくなるまで、beta/eta簡約を繰り返す。
--
-- 入力promiseは使わないので、buildInputは指定するが、使わない。
reductInf :: LamExpr -> LamExpr
reductInf = takeExpr . untilStop (reduct buildInputLc) def def

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
-- Just _3_1
-- >>> subst 1 (V 3) (V 1 %: la (V 2))
-- Just _3(λ _4)
-- >>> subst 2 (V 3) (V 1 %: V 5 %: V 2)
-- Just _1_4_3
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
subst _    _ (Num _)     = Nothing

deepen :: Int ->  LamExpr -> Maybe LamExpr
deepen vIdx (V v)
    | v >= vIdx = Just $ V (v + 1)
    | otherwise = Nothing
deepen vIdx (L _ le)    = la <$> deepen (vIdx + 1) le
deepen vIdx (App _ m n) = mergeApp (deepen vIdx) m n
deepen _    (Nm _)      = Nothing
deepen _    (Jot _ _)   = Nothing
deepen _    (In _)      = Nothing
deepen _    (Num _)     = Nothing

-- |
-- Abstraction Elimination
--
-- >>> abstElim (la $ Nm "t" %: V 1)  -- λx.tx eta簡約
-- Just t
-- >>> abstElim $ la . la $ (la $ V 2) %: V 1  -- λxy.(λz.y)y = λxy.y  K(SKI)
-- Just K(SKI)
abstElim :: LamExpr
    -> Maybe LamExpr -- ^ if cannot more Elimination, this returns Nothing
abstElim (Nm _)      = Nothing   -- Rule 1
abstElim (V _)       = Nothing   -- Rule 1
abstElim (Jot _ _)   = Nothing   -- Rule 1
abstElim (In _)      = Nothing   -- Rule 1  内容は不明なので、そのままにする。
abstElim (Num _)     = Nothing   -- Rule 1  内容は不明なので、そのままにする。
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
abstElim (L _ (Num _)) = Nothing

-- | 指定した de Bruijn index の変数が式の中に存在するか
hasVar :: Int -> LamExpr -> Bool
hasVar vIdx (V v)       = vIdx == v
hasVar vIdx (L _ le)    = hasVar (vIdx + 1) le
hasVar vIdx (App _ m n) = hasVar vIdx m || hasVar vIdx n
hasVar _    _           = False

-- | 指定した de Bruijn index のラムダ抽象を除去する際に、
-- それ以上の変数のindexを 1 詰める。
shallow :: Int -> LamExpr -> Maybe LamExpr
shallow vIdx (V v)
    | v > vIdx  = Just $ V (v - 1)
    | otherwise = Nothing
shallow vIdx (L _ le)    = la <$> shallow (vIdx + 1) le
shallow vIdx (App _ m n) = mergeApp (shallow vIdx) m n
shallow _    _           = Nothing

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
