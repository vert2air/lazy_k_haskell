module QuickCheckTests where

import Test.QuickCheck (quickCheck)

import LazyKCore (LamExpr(..), NameManager(..), Stringifying(..)
                , toNamedString, readLazyK)

qc_main :: IO ()
qc_main = do
    quickCheck prop_toNamedString_readLazyK

prop_toNamedString_readLazyK :: NameManager -> LamExpr -> Bool
prop_toNamedString_readLazyK mng e = case toNamedString mng e of
    Stringifying e' _ _ -> case readLazyK "DummyTitle" e' of
        Right e'' -> e == e''
        Left _ -> False
