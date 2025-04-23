module QuickCheckTests where

import Test.QuickCheck (Result(..), quickCheckResult)

import LazyKCore (LamExpr(..), NameManager(..), Stringifying(..)
                , toNamedString, readLazyK)

qc_main :: IO [Result]
qc_main = do
    res <- quickCheckResult prop_toNamedString_readLazyK
    return [res]

prop_toNamedString_readLazyK :: NameManager -> LamExpr -> Bool
-- Iota のみは、Lazy Kの仕様上表記出来ない。除外する。
prop_toNamedString_readLazyK _ (Nm "iota") = True
prop_toNamedString_readLazyK mng e = case toNamedString mng e of
    Stringifying e' _ _ -> case readLazyK "DummyTitle" e' of
        Right e'' -> e == e''
        Left _ -> False
