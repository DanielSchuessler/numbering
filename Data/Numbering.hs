{-# LANGUAGE DeriveDataTypeable #-}
module Data.Numbering where

import Data.Map(Map)
import Data.Maybe
-- import PrettyUtil
-- import THUtil
-- import Util
import qualified Data.Map as M
import qualified Data.Vector as V
import Control.Monad
import qualified Data.Set as S
import Data.Set(Set)
import Data.Typeable(Typeable)
import Control.Exception


-- | Invariant: For all @i@ in @[ 0 .. 'nuLength' - 1 ]@, @'toInt' ('fromInt' i) == i@. 
--
-- This implies that for all @a@ of the form @'fromInt' i@ (with @i@ in @[ 0 .. 'nuLength' - 1 ]@), @'fromInt' ('toInt' a) = a@.
--
-- The behaviour of @fromInt@ for out-of-bounds indices and that of @toInt@ for elements not occuring in the numbering is undefined. 
data Numbering a = UnsafeMkNumbering {
    toInt :: a -> Int,
    fromInt :: Int -> a,
    nuLength :: Int
}

instance Show a => Show (Numbering a) where
    showsPrec prec nu = 
        showParen (prec > 10) 
            (showString "nuFromDistinctList " . showsPrec 11 (nuElements nu))

-- | @enumNu a b@ creates a numbering of the elements @[a .. b]@ (inclusively). 
enumNu :: (Enum a) => a -> a -> Numbering a
enumNu min_ max_ = enumNu' (fromEnum min_) (fromEnum max_)

-- | @enumNu' i j@ creates a numbering of the elements @[toEnum i .. toEnum j]@ (inclusively). 
enumNu' :: Enum a => Int -> Int -> Numbering a
enumNu' mini maxi =
    UnsafeMkNumbering {
        toInt = subtract mini . fromEnum
    ,   fromInt = toEnum . (+) mini
    ,   nuLength = maxi-mini+1

    }

-- | Creates a numbering for an 'Either'-like type, given numberings for the summand types.
sumNu
  ::    (a1 -> a)
     -> (a2 -> a)
     -> ((a1 -> Int) -> (a2 -> Int) -> a -> Int)
     -> Numbering a1
     -> Numbering a2
     -> Numbering a
sumNu left_ right_ either_ nu1 nu2 = 
    let
        n1 = nuLength nu1
    in
        UnsafeMkNumbering
            (either_ (toInt nu1) ((+ n1) . toInt nu2))
            (\i -> case i-n1 of
                        i' | i' < 0 -> left_ (fromInt nu1 i)
                           | otherwise -> right_ (fromInt nu2 i'))
            (n1+nuLength nu2)

eitherNu :: Numbering a -> Numbering b -> Numbering (Either a b)
eitherNu = sumNu Left Right either


-- | Creates a numbering for an pair-like type, given numberings for the component types.
prodNu
  :: (a -> a2)
     -> (a -> a1)
     -> (a2 -> a1 -> a)
     -> Numbering a2
     -> Numbering a1
     -> Numbering a
prodNu fst_ snd_ prod nu1 nu2 =
    let
        n2 = nuLength nu2
    in
        UnsafeMkNumbering
            (\a -> toInt nu1 (fst_ a) * n2 + toInt nu2 (snd_ a))
            (\i -> case divMod i n2 of
                        (i1,i2) -> prod (fromInt nu1 i1) (fromInt nu2 i2)
            
            )
            (n2*nuLength nu1)
    


pairNu :: Numbering a -> Numbering b -> Numbering (a, b)
pairNu = prodNu fst snd (,)

nuIndices :: Numbering a -> [Int]
nuIndices nu = [0.. nuLength nu-1]

nuElements :: Numbering a -> [a]
nuElements nu = fmap (fromInt nu) (nuIndices nu)

data NumberingBrokenInvariantException a = NumberingBrokenInvariantException {
    nbie_index :: Int,
    nbie_fromIntOfIndex :: a,
    nbie_toIntOfFromIntOfIndex :: Int
}
    deriving (Show,Typeable)

instance (Show a, Typeable a) => Exception (NumberingBrokenInvariantException a)

checkNu :: Numbering a -> Either (NumberingBrokenInvariantException a) ()
checkNu nu = 
    mapM_ (\i -> let a_i = fromInt nu i
                     i_a_i = toInt nu a_i
                 in
                    unless (i == i_a_i)
                        (Left (NumberingBrokenInvariantException i a_i i_a_i)))
          (nuIndices nu)

    
-- | "Data.Set" doesn't expose the necessary index-based API
nuFromSet :: Map Int ignored -> Numbering Int
nuFromSet m = 
    UnsafeMkNumbering
        (\i -> fst (M.elemAt i m))
        (\a -> fromMaybe
                    (error ("nuFromSet: Element not in Numbering: "++show a))
                    (M.lookupIndex a m)) 
        (M.size m)

-- | The distinctness precondition is checked (we have to create a map anyway).
nuFromDistinctVector :: (Show a, Ord a) => V.Vector a -> Numbering a
nuFromDistinctVector v =
    let
        m = V.ifoldl' (\r i a -> M.insertWithKey _err a i r) M.empty v

        _err a i1 i2 = error ("nuFromDistinctVector: duplicate: " ++ show a++ " at indices "++show (i1,i2))
    in
        UnsafeMkNumbering
            (\a -> fromMaybe
                        (error ("nuFromDistinctVector: Element not in Numbering: "++show a))
                        (M.lookup a m)) 
            (v V.!)
            (V.length v)

-- | See 'nuFromDistinctVector'.
nuFromDistinctList :: (Ord a, Show a) => [a] -> Numbering a
nuFromDistinctList = nuFromDistinctVector . V.fromList 

-- | Uniquifies the input first (resulting in an unspecified order).
nuFromList :: (Ord a, Show a) => [a] -> Numbering a
nuFromList = nuFromDistinctList . S.toList . S.fromList

finiteTypeNu :: (Enum a, Bounded a) => Numbering a
finiteTypeNu = enumNu minBound maxBound
