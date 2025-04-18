import Test.QuickCheck

import LazyKCore (LamExpr(..), (%:))

prop_reverse :: [Int] -> Bool
prop_reverse xs = reverse (reverse xs) == xs

instance Arbitrary LamExpr where
    arbitrary = oneof [
          return $ V $ abs arbitrary + 1
        , return $ la $ arbitrary
        , return $ arbitrary %: arbitrary
        , return $ Nm $ oneof $
            [ [ch] for ch <- "abcdefgh" ++ "j" ++ "lmnopqr" ++ "tuvwxyz" ++ "ABCDEFGHIJKLMNOPQRSTUVWXYZ" ] ++ "iota"
        , do
            jotexp <- listof . oneof $ "01"
            return $ Jot (length jotexp) jotexp
        , return $ In $ abs arbitrary
    ]

instance Arbitrary PolicyKind where
    arbitrary = return $ oneof [
          PK_index, PK_single_use, PK_level, PK_minimum
        ]

instance Arbitrary NameMamager where
    arbitrary = NameMamager <$> arbitrary <*> arbitrary
            listof ("abcdefgh" ++ "j" ++ "lmnopqr" ++ "tuvwxyz"
                ++ "ABCDEFGHIJKLMNOPQRSTUVWXYZ")
        <*> arbitrary

main :: IO ()
main = do
    quickCheck 

prop_toNamedString_readLazyK :: LamExpr -> Bool
prop_toNamedString_readLazyK e =
    readLazyK . toNamedString e == e
