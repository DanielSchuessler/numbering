{-# LANGUAGE TupleSections, TemplateHaskell, ScopedTypeVariables #-}
{-# OPTIONS -Wall -fno-warn-orphans -fno-warn-unused-imports -fno-warn-missing-signatures #-}
import Data.Numbering
import Test.QuickCheck
import Test.Framework.TH
import Test.Framework.Providers.QuickCheck2
import Control.Applicative
import qualified Data.Set as S
import Data.Set(Set)
import Control.Monad

valid :: Numbering a -> Property
valid nu
    | nuLength nu == 0 = property True
    | otherwise = forAll (choose (0,nuLength nu-1)) (\i -> i == toInt nu (fromInt nu i)) 

prop_valid_invalid :: Property
prop_valid_invalid = expectFailure (valid (UnsafeMkNumbering id (+1) 1)) 

validAndElementsEqual expectedElements nu =
    valid nu .&&. 
        (
        let
            actualElements =
                nuElements nu
        in
            printTestCase ("validAndElementsEqual: expectedElements = " ++ show expectedElements) $
            printTestCase ("validAndElementsEqual: actualElements = " ++ show actualElements) $
            actualElements == expectedElements
            )

prop_enumNu (a :: Char) b = 
    validAndElementsEqual [a..b] (enumNu a b)

prop_finiteTypeNu =
    validAndElementsEqual [False,True] finiteTypeNu

prop_idNu =
    let
        n = 10
    in
        validAndElementsEqual [0..n-1] (idNu n)

prop_emptyNu = validAndElementsEqual [] (emptyNu :: Numbering Char)

prop_nuFromList (l :: [Char]) =
    let
        nu = nuFromList l
    in
        valid nu .&&. S.fromList l == S.fromList (nuElements nu) 

instance (Ord a, Show a, Arbitrary a) => Arbitrary (Numbering a) where
    arbitrary = nuFromList <$> arbitrary

prop_Numbering_neq (l1 :: [Char]) l2 = 
    S.fromList l1 /= S.fromList l2 ==> nuFromList l1/= nuFromList l2 

prop_consolidateNu (nu :: Numbering Float) = nu == consolidateNu nu

prop_consolidateUnboxNu (nu :: Numbering Float) = nu == consolidateUnboxNu nu

prop_reverseNu (nu :: Numbering Char) = validAndElementsEqual (reverse (nuElements nu)) (reverseNu nu)

prop_mapNu (nu :: Numbering Char)
        = validAndElementsEqual (map f (nuElements nu)) (mapNu f g nu)

    where
        f = (,True)
        g = fst


prop_nuTake (nu :: Numbering Float) = validAndElementsEqual (take 3 (nuElements nu)) (nuTake 3 nu)

prop_nuDrop (nu :: Numbering Float) = validAndElementsEqual (drop 3 (nuElements nu)) (nuDrop 3 nu)

prop_pairNu (nu1 :: Numbering Bool) (nu2 :: Numbering Char) =
    validAndElementsEqual 
        (liftM2 (,) (nuElements nu1) (nuElements nu2))
        (pairNu nu1 nu2)

prop_eitherNu (nu1 :: Numbering Bool) (nu2 :: Numbering Char) =
    validAndElementsEqual 
        (map Left (nuElements nu1) ++ map Right (nuElements nu2))
        (eitherNu nu1 nu2)

main = $defaultMainGenerator
