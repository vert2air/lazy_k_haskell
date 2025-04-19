module QuickCheckTest where

import Test.QuickCheck (Arbitrary(..), oneof, listOf, quickCheck, shuffle)

import LazyKCore (LamExpr(..), PolicyKind(..), NameManager(..)
                , Stringifying(..), (%:), la, toNamedString, readLazyK)

prop_reverse :: [Int] -> Bool
prop_reverse xs = reverse (reverse xs) == xs

instance Arbitrary LamExpr where
    arbitrary = oneof [
          V . (+1) . abs <$> arbitrary
        , la <$> arbitrary
        , (%:) <$> arbitrary <*> arbitrary
        , (Nm <$>) . oneof $
            [ pure [ch] | ch <- "abcdefgh" ++ "j" ++ "lmnopqr" ++ "tuvwxyz"
                                ++ "ABCDEFGHIJKLMNOPQRSTUVWXYZ" ]
            ++ [pure "iota"]

        , do
            jotexp <- listOf . oneof . map pure $ "01"
            return $ Jot (length jotexp) jotexp
        , In . abs <$> arbitrary
        ]

instance Arbitrary PolicyKind where
    arbitrary = oneof $ map return [
          PK_index, PK_single_use, PK_level, PK_minimum
        ]

instance Arbitrary NameManager where
    arbitrary = NameManager <$> arbitrary
        <*> shuffle ("abcdefgh" ++ "j" ++ "lmnopqr" ++ "tuvwxyz"
                ++ "ABCDEFGHIJKLMNOPQRSTUVWXYZ_")
        <*> pure ""
        <*> arbitrary

qc_main :: IO ()
qc_main = do
    quickCheck prop_toNamedString_readLazyK

prop_toNamedString_readLazyK :: NameManager -> LamExpr -> Bool
prop_toNamedString_readLazyK mng e = case toNamedString mng e of
    Stringifying e' _ _ -> case readLazyK "DummyTitle" e' of
        Right e'' -> e == e''
        Left _ -> False
