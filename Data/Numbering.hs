{-# LANGUAGE NoMonomorphismRestriction, DeriveDataTypeable #-}
{-# OPTIONS -Wall #-}
module Data.Numbering (
    Numbering(..),
    -- * Construction
    enumNu,
    enumNu',
    nuFromSet,
    nuFromDistinctVector,
    nuFromDistinctVectorG,
    finiteTypeNu,
    idNu,
    emptyNu,
    -- ** From a list
    nuFromDistinctList,
    nuFromDistinctUnboxList,
    nuFromDistinctIntList,
    nuFromList,
    nuFromUnboxList,
    nuFromIntList,
    -- * Transformation
    mapNu,
    reindexNu,
    consolidateNu,
    consolidateUnboxNu,
    nuTake,
    -- ** Particular reindexings
    reverseNu,
    nuDrop,
    -- * Combination
    sumNu,
    eitherNu,
    prodNu,
    pairNu,
    -- * Destruction
    nuIndices,
    nuElements,
    nuToList,
    nuToDistinctList,
    nuToVector,
    nuToDistinctVector,
    NumberingBrokenInvariantException(..),
    checkNu,
    )

    where

import Control.Exception
import Control.Monad
import Data.Map(Map)
import Data.Maybe
import Data.Monoid(mempty)
import Data.Typeable(Typeable)
import Data.Vector.Unboxed(Unbox)
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Vector as V
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Unboxed as VU
import Debug.Trace
import Data.Function


-- | Invariant: 
--
-- @
-- For all i in 0 .. 'nuLength' - 1, 
--     'toInt' ('fromInt' i) == i 
-- @
--
-- This implies that 
--
-- @
-- For all a of the form 'fromInt' i (with i in 0 .. 'nuLength' - 1), 
--     'fromInt' ('toInt' a) = a
-- @
--
-- The behaviour of @fromInt@ for out-of-bounds indices and that of @toInt@ for elements not occuring in the numbering is undefined. 
--
-- Thus, assuming the invariant holds, @toInt@ is uniquely determined by @fromInt@ (on valid inputs).
data Numbering a = UnsafeMkNumbering {
    toInt :: a -> Int,
    fromInt :: Int -> a,
    nuLength :: Int
}
    -- ^ \"Unsafe\" because the invariant isn't checked.

instance Show a => Show (Numbering a) where
    showsPrec prec nu = 
        showParen (prec > 10) 
            (showString "nuFromDistinctList " . showsPrec 11 (nuElements nu))

-- | Assumes that the invariant holds.
instance Eq a => Eq (Numbering a) where
    nu1 == nu2 =
        ((==) `on` nuLength) nu1 nu2
        &&
        all (\i -> fromInt nu1 i == fromInt nu2 i) (nuIndices nu1)

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
  ::    (a1 -> a) -- ^ 'Left' equivalent
     -> (a2 -> a) -- ^ 'Right' equivalent
     -> ((a1 -> Int) -> (a2 -> Int) -> a -> Int) -- ^ 'either' equivalent
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
  ::    (a -> a2) -- ^ 'fst' equivalent
     -> (a -> a1) -- ^ 'snd' equivalent
     -> (a2 -> a1 -> a) -- ^ @(,)@ equivalent
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

-- | = 'nuElements'.
nuToList :: Numbering a -> [a]
nuToList = nuElements 

-- | = 'nuElements'. Won't actually be distinct if the invariant is broken.
nuToDistinctList :: Numbering a -> [a]
nuToDistinctList = nuElements 

nuToVector :: VG.Vector v a => Numbering a -> v a
nuToVector nu = VG.generate (nuLength nu) (fromInt nu)

-- | = 'nuToVector'. Won't actually be distinct if the invariant is broken.
nuToDistinctVector :: VG.Vector v a => Numbering a -> v a
nuToDistinctVector nu = VG.generate (nuLength nu) (fromInt nu)

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

    
-- | (Uses a 'Map' because "Data.Set" doesn't expose the necessary index-based API)
nuFromSet :: Map Int ignored -> Numbering Int
nuFromSet m = 
    UnsafeMkNumbering
        (\i -> fst (M.elemAt i m))
        (\a -> fromMaybe
                    (error ("nuFromSet: Element not in Numbering: "++show a))
                    (M.lookupIndex a m)) 
        (M.size m)



-- | The distinctness precondition is checked (we have to create a map anyway).
nuFromDistinctVector
  :: (Ord a, Show a, VG.Vector v a) => v a -> Numbering a
nuFromDistinctVector = nuFromDistinctVectorG mempty M.insertWithKey M.lookup 

-- | Allows customization of the map type used.
nuFromDistinctVectorG
  :: (Show a, VG.Vector v a) =>

     map -- ^ 'M.empty' equivalent
     -> ((a -> Int -> Int -> t) -> a -> Int -> map -> map) -- ^ 'M.insertWithKey' equivalent 
     -> (a -> map -> Maybe Int) -- ^ 'M.lookup' equivalent 
     -> v a -> Numbering a
nuFromDistinctVectorG _empty _insertWithKey _lookup v =
    let
        m = VG.ifoldl' (\r i a -> _insertWithKey _err a i r) _empty v

        _err a i1 i2 = error ("nuFromDistinctVector: duplicate: " ++ show a++ " at indices "++show (i1,i2))
    in
        UnsafeMkNumbering
            (\a -> fromMaybe
                        (error ("nuFromDistinctVector: Element not in Numbering: "++show a))
                        (_lookup a m)) 
            (v VG.!)
            (VG.length v)

-- | See 'nuFromDistinctVector'.
nuFromDistinctList :: (Ord a, Show a) => [a] -> Numbering a
nuFromDistinctList = nuFromDistinctVector . V.fromList 

-- | See 'nuFromDistinctVector'.
nuFromDistinctUnboxList :: (Ord a, Show a, Unbox a) => [a] -> Numbering a
nuFromDistinctUnboxList = nuFromDistinctVector . VU.fromList 

nuFromDistinctIntList :: [Int] -> Numbering Int
nuFromDistinctIntList = nuFromDistinctVectorG mempty IM.insertWithKey IM.lookup . VU.fromList

-- | Uniquifies the input first (resulting in an unspecified order).
nuFromList :: (Ord a, Show a) => [a] -> Numbering a
nuFromList = nuFromDistinctList . S.toList . S.fromList

-- | Uniquifies the input first (resulting in an unspecified order).
nuFromUnboxList :: (Ord a, Show a, Unbox a) => [a] -> Numbering a
nuFromUnboxList = nuFromDistinctUnboxList . S.toList . S.fromList

-- | Uniquifies the input first (resulting in an unspecified order).
nuFromIntList :: [Int] -> Numbering Int
nuFromIntList = nuFromDistinctIntList . IS.toList . IS.fromList

-- | Numbering of all elements of a finite type.
finiteTypeNu :: (Enum a, Bounded a) => Numbering a
finiteTypeNu = enumNu minBound maxBound

-- | Identity numbering
idNu :: Int -- ^ The 'nuLength'  
    -> Numbering Int
idNu = UnsafeMkNumbering id id

emptyNu :: Numbering a
emptyNu = UnsafeMkNumbering {
    nuLength = 0,
    toInt = \_ -> error "emptyNu/toInt",
    fromInt = \i -> error ("emptyNu/fromInt "++show i)
}

-- | In @mapNu f g nu@, the arguments must satisfy
--
-- @
-- For all i in 0 .. 'nuLength' nu - 1, 
--     (g . f) a == a
--          where
--              a = 'fromInt' nu i
-- @
mapNu :: (a -> b) -> (b -> a) -> Numbering a -> Numbering b
mapNu toNew toOld nu =
    UnsafeMkNumbering {
        toInt = toInt nu . toOld,
        fromInt = toNew . fromInt nu,
        nuLength = nuLength nu
    }


-- | In @reindexNu k f g nu@, the arguments must satisfy
--
-- @
-- For all i in 0 .. k,
--     (g . f) i == i
-- @
--
-- Note: Decreasing the length with this function will /not/ release any memory retained
-- by the closures in the input numbering (e.g. the vector, for numberings created by 'nuFromDistinctVector'). Use 'consolidateNu' afterwards for that.
reindexNu
  :: Int -- ^ New 'nuLength'
     -> (Int -> Int) -- ^ Old index to new index 
     -> (Int -> Int) -- ^ New index to old index
     -> Numbering a -> Numbering a
reindexNu newLength toNewIndex toOldIndex nu =
   (if newLength > oldLength
    then trace ("reindexNu: Warning: newLength > oldLength "++show (newLength,oldLength)++
                    ". This implies that the new-to-old-index function is non-injective, or "++
                    "relies on the behaviour of the input numbering outside of its bounds.")
    else id)
        UnsafeMkNumbering {
            toInt = toNewIndex . toInt nu,
            fromInt = fromInt nu . toOldIndex,
            nuLength = newLength
        }

  where
    oldLength = nuLength nu

reverseNu :: Numbering a -> Numbering a
reverseNu nu = reindexNu n (n -) (n -) nu
    where
        n = nuLength nu

-- Identity for arg at least equal to the input length.
--
-- See the note in 'consolidateNu' about memory usage.
nuTake :: Int -> Numbering a -> Numbering a
nuTake k nu 
    | k >= nuLength nu = nu
    | k <= 0 = emptyNu
    | otherwise = nu { nuLength = k }



idBoxedVector :: V.Vector a -> V.Vector a
idBoxedVector = id

idUnboxedVector :: VU.Vector a -> VU.Vector a
idUnboxedVector = id

-- | Semantic 'id' (for in-bounds inputs), but backs the numbering with a new vector and map having just the required length (example: @consolidateNu ('nuTake' 1 ('nuFromDistinctVector' largeVector))@). 
consolidateNu :: (Ord a, Show a) => Numbering a -> Numbering a
consolidateNu = nuFromDistinctVector . idBoxedVector . nuToDistinctVector  

-- | Like 'consolidateNu', but uses unboxed vectors.
consolidateUnboxNu :: (Ord a, Show a, Unbox a) => Numbering a -> Numbering a
consolidateUnboxNu = nuFromDistinctVector . idUnboxedVector . nuToDistinctVector

-- | Identity for nonpositive arg.
nuDrop :: Int -> Numbering a -> Numbering a
nuDrop k nu | k <= 0 = nu
            | k >= n = emptyNu
            | otherwise = reindexNu (n - k) (subtract k) (+ k) nu 
    where
        n = nuLength nu
