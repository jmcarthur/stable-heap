{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Trustworthy #-}

-- |
-- Module      :  Data.Heap.Stable
-- Copyright   :  (C) Jake McArthur 2015-2016
-- License     :  MIT
-- Maintainer  :  Jake.McArthur@gmail.com
-- Stability   :  experimental
--
-- A simple implementation of stable heaps (fair priority queues),
-- modeled as a sequence of key-value pairs, allowing duplicates, with
-- efficient access to the leftmost key-value pair having the smallest
-- key.
--
-- The data structure is a modification of the lazy pairing heaps
-- described in Chris Okasaki's /Purely Functional Data Structures/.
--
-- A 'Heap' has both heap-like and sequence-like properties. Most of
-- the traversals defined in this module work in sequence order; those
-- that work in key order are explicitly documented as such.
--
-- Unless stated otherwise, the documented asymptotic efficiencies of
-- functions on 'Heap' assume that arguments are already in WHNF and
-- that the result is to be evaluated to WHNF.
module Data.Heap.Stable
       ( Heap ()
         -- * Query
       , Data.Heap.Stable.null
       , size
         -- * Construction
       , empty
       , singleton
       , append
       , appends
       , cons
       , snoc
         -- * Minimum view
       , minViewWithKey
         -- * Traversal
         -- ** Map
       , bimap
       , mapKeys
       , mapWithKey
       , traverseKeys
       , traverseWithKey
         -- ** Fold
       , foldrWithKey
       , foldMapWithKey
         -- * List operations
         -- ** Conversion from lists
       , fromList
         -- ** Conversion to lists
       , toList
       , toAscList
       ) where

import qualified Control.Applicative as Applicative
import Control.Applicative hiding (Alternative (..))
import Control.Monad
import Data.List (foldl', unfoldr)
import Data.Monoid

import qualified GHC.Exts

-- |
-- Denotationally, @Heap k a@ is equivalent to @[(k, a)]@, but its
-- operations have different efficiencies.
data Heap k a
  = Heap !Int !(Heap k a) (Heap k a) !k a (Heap k a) !(Heap k a)
  | Empty
  deriving (Functor, Foldable, Traversable)

-- |
-- 'True' if the 'Heap' is empty.
--
-- /O(1)/.
--
-- > null xs = Data.List.null (toList xs)
null :: Heap k a -> Bool
null Empty = True
null Heap {} = False

-- |
-- The number of key-value pairs in the heap.
--
-- /O(1)/.
--
-- > size xs = length (toList xs)
size :: Heap k a -> Int
size Empty = 0
size (Heap s _ _ _ _ _ _) = s

-- |
-- @toList empty = []@
empty :: Heap k a
empty = Empty

-- |
-- /O(1)/.
--
-- > toList (singleton k v) = [(k, v)]
singleton :: k -> a -> Heap k a
singleton k v = Heap 1 empty empty k v empty empty

-- |
-- /O(1)/.
--
-- > toList (xs `append` ys) = toList xs ++ toList ys
append :: Ord k => Heap k a -> Heap k a -> Heap k a
Empty `append` ys = ys
xs `append` Empty = xs
xs@(Heap sx l1 ls1 k1 v1 rs1 r1) `append` ys@(Heap sy l2 ls2 k2 v2 rs2 r2)
  | k1 <= k2 =
      case r1 of
        Empty   -> Heap (sx+sy) l1 ls1 k1 v1  rs1                     ys
        Heap {} -> Heap (sx+sy) l1 ls1 k1 v1 (rs1 `append` (r1 `append` ys)) Empty
  | otherwise =
      case l2 of
        Empty   -> Heap (sx+sy)        xs                     ls2  k2 v2 rs2 r2
        Heap {} -> Heap (sx+sy) Empty ((xs `append` l2) `append` ls2) k2 v2 rs2 r2

-- | /O(m)/, where /m/ is the length of the input list.
--
-- > toList (appends xss) = concatMap toList xss
appends :: Ord k => [Heap k a] -> Heap k a
appends = foldl' append empty

-- |
-- Split the 'Heap' at the leftmost occurrence of the smallest key
-- contained in the 'Heap'.
--
-- When the 'Heap' is empty, /O(1)/. When the 'Heap' is not empty,
-- finding the key and value is /O(1)/, and evaluating the remainder
-- of the heap to the left or right of the key-value pair is amortized
-- /O(log n)/.
--
-- > toList xs =
-- > case minViewWithKey xs of
-- >   Nothing -> []
-- >   Just (l, kv, r) -> toList l ++ [kv] ++ toList r
minViewWithKey :: Ord k => Heap k a -> Maybe (Heap k a, (k, a), Heap k a)
minViewWithKey Empty = Nothing
minViewWithKey (Heap _ l ls k v rs r) = Just (l `append` ls, (k, v), rs `append` r)

-- |
-- > mempty  = empty
-- > mappend = append
instance Ord k => Monoid (Heap k a) where
  mempty = empty
  mappend = append

-- |
-- Prepend a key-value pair to the beginning of a 'Heap'.
--
-- /O(1)/.
--
-- > toList (cons k v xs) = (k, v) : toList xs
cons :: Ord k => k -> a -> Heap k a -> Heap k a
cons k v = (singleton k v <>)

-- |
-- Append a key-value pair to the end of a 'Heap'.
--
-- /O(1)/.
--
-- > toList (snoc xs k v) = toList xs ++ [(k, v)]
snoc :: Ord k => Heap k a -> k -> a -> Heap k a
snoc xs k v = xs <> singleton k v

-- |
-- > foldrWithKey f z xs = foldr (uncurry f) z (toList xs)
foldrWithKey :: (k -> a -> b -> b) -> b -> Heap k a -> b
foldrWithKey f = flip go
  where
    go Empty z = z
    go (Heap _ l ls k v rs r) z = go l (go ls (f k v (go rs (go r z))))

-- |
-- List the key-value pairs in a 'Heap' in sequence order. This is the semantic
-- function for 'Heap'.
--
-- /O(n)/ when the spine of the result is evaluated fully.
toList :: Heap k a -> [(k, a)]
toList = foldrWithKey (\k v xs -> (k, v) : xs) []

-- |
-- List the key-value pairs in a 'Heap' in key order.
--
-- /O(n log n)/ when the spine of the result is evaluated fully.
toAscList :: Ord k => Heap k a -> [(k, a)]
toAscList = unfoldr f
  where
    f xs =
      case minViewWithKey xs of
        Nothing -> Nothing
        Just (l, kv, r) -> Just (kv, l <> r)

-- |
-- Construct a 'Heap' from a list of key-value pairs.
--
-- /O(n)/.
fromList :: Ord k => [(k, a)] -> Heap k a
fromList = foldl' (\acc (k, v) -> snoc acc k v) empty

-- |
-- > toList (bimap f g xs) = map (f *** g) (toList xs)
bimap :: Ord k2 => (k1 -> k2) -> (a -> b) -> Heap k1 a -> Heap k2 b
bimap f g = go
  where
    go Empty = Empty
    go (Heap _ l ls k v rs r) = go l <> go ls <> singleton (f k) (g v) <> go rs <> go r

-- |
-- > toList (mapKeys f xs) = map (first f) (toList xs)
mapKeys :: Ord k2 => (k1 -> k2) -> Heap k1 a -> Heap k2 a
mapKeys f = bimap f id

-- |
-- Map a function over all values in a heap.
--
-- /O(1)/ when evaluating to WHNF. /O(n)/ when evaluating to NF.
mapWithKey :: (k -> a -> b) -> Heap k a -> Heap k b
mapWithKey f = go
  where
    go Empty = Empty
    go (Heap n l ls k v rs r) = Heap n (go l) (go ls) k (f k v) (go rs) (go r)

-- |
-- Fold the keys and values in the heap using the given monoid, such that
--
-- > foldMapWithKey f = fold . mapWithKey f
--
-- /O(n)/.
foldMapWithKey :: Monoid b => (k -> a -> b) -> Heap k a -> b
foldMapWithKey f = go
  where
    go Empty = mempty
    go (Heap _ l ls k v rs r) = go l <> go ls <> f k v <> go rs <> go r

-- |
-- Behaves exactly like a regular traverse except that the traversing function
-- also has access to the key associated with a value, such that
--
-- > traverseWithKey f = fromList . traverse ((k, v) -> (,) k $ f k v) . toList
--
-- /O(n)/.
traverseWithKey :: Applicative f => (k -> a -> f b) -> Heap k a -> f (Heap k b)
traverseWithKey f = go
  where
    go Empty = pure Empty
    go (Heap n l ls k v rs r) = Heap n <$> go l <*> go ls <*> pure k <*> f k v <*> go rs <*> go r

-- |
-- Behaves exactly like a regular traverse except that it's over the keys
-- instead of the values.
--
-- /O(n log n)/.
traverseKeys :: (Applicative f, Ord k2) => (k1 -> f k2) -> Heap k1 a -> f (Heap k2 a)
traverseKeys f = go
  where
    go Empty = pure Empty
    go (Heap _ l ls k v rs r) = go l <.> go ls <.> ((`singleton` v) <$> f k) <.> go rs <.> go r
    (<.>) = liftA2 (<>)

-- |
-- Works like @WriterT k []@
instance (Monoid k, Ord k) => Applicative (Heap k) where
  pure = singleton mempty
  Empty <*> _ = Empty
  _ <*> Empty = Empty
  Heap _ fl fls fk f frs fr <*> xs
    =  (fl  <*>         xs)
    <> (fls <*>         xs)
    <>  bimap (fk <>) f xs
    <> (frs <*>         xs)
    <> (fr  <*>         xs)

-- |
-- Works like @WriterT k []@
instance (Monoid k, Ord k) => Monad (Heap k) where
  return = pure
  Empty >>= _ = Empty
  Heap _ xl xls xk x xrs xr >>= f
    =  (xl  >>= f)
    <> (xls >>= f)
    <>  mapKeys (xk <>) (f x)
    <> (xrs >>= f)
    <> (xr  >>= f)

instance (Show k, Show a) => Show (Heap k a) where
  showsPrec d h = showParen (d > 10) $ showString "fromList " . shows (toList h)

instance (Ord k, Read k, Read a) => Read (Heap k a) where
  readsPrec p = readParen (p > 10) $ \ r -> do
    ("fromList", s) <- lex r
    (xs, t) <- reads s
    return (fromList xs, t)

instance Ord k => GHC.Exts.IsList (Heap k a) where
  type Item (Heap k a) = (k, a)
  fromList = fromList
  toList   = toList

-- |
-- > xs == ys = toList xs == toList ys
instance (Eq k, Eq a) => Eq (Heap k a) where
  xs == ys = toList xs == toList ys

-- |
-- > compare xs ys = compare (toList xs) (toList ys)
instance (Ord k, Ord a) => Ord (Heap k a) where
  compare xs ys = compare (toList xs) (toList ys)

-- |
-- > empty = mempty
-- > (<|>) = mappend
instance (Monoid k, Ord k) => Applicative.Alternative (Heap k) where
  empty = mempty
  (<|>) = mappend

-- |
-- > mzero = empty
-- > mplus = append
instance (Monoid k, Ord k) => MonadPlus (Heap k) where
  mzero = mempty
  mplus = mappend
