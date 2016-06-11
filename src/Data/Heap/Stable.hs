{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Trustworthy #-}

-- |
--
-- Module      :  Data.Heap.Stable
-- Copyright   :  (C) 2015-2016 Jake McArthur
-- License     :  MIT
-- Maintainer  :  Jake.McArthur@gmail.com
-- Stability   :  experimental
--
-- A simple implementation of stable heaps (fair priority queues), modeled as a
-- sequence of key-value pairs, allowing duplicates, with efficient access to
-- the leftmost key-value pair having the smallest key.
--
-- The data structure is a modification of the lazy pairing heaps described in
-- Chris Okasaki's /Purely Functional Data Structures/.
--
-- A 'Heap' has both heap-like and sequence-like properties. Most of the
-- traversals defined in this module work in sequence order; those that work in
-- key order are explicitly documented as such.
--
-- Unless stated otherwise, the documented asymptotic efficiencies of functions
-- on 'Heap' assume that arguments are already in WHNF and that the result is to
-- be evaluated to WHNF.
module Data.Heap.Stable
       ( -- $setup
         Heap ()
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
       , MinView (..)
       , minView
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

import Prelude hiding (null)

import qualified Control.Applicative as Applicative
import Control.Applicative hiding (Alternative (..))
import Control.Monad
import Data.List (foldl', unfoldr)
import qualified Data.List
import Data.Monoid
import qualified Data.Foldable

import qualified GHC.Exts

-- |
--
-- @Heap k a@ is equivalent to @[(k, a)]@, but its operations have different
-- efficiencies.
data Heap k a
  = Heap !Int !(Heap k a) (Heap k a) !k a (Heap k a) !(Heap k a)
  | Empty
  deriving (Functor, Foldable, Traversable)

-- |
--
-- 'True' if the 'Heap' is empty and 'False' otherwise.
--
-- /O(1)/.
--
-- >>> any null [the, quick, brown, fox]
-- False
--
-- >>> null empty
-- True
--
-- prop> null xs == Data.List.null (toList xs)
null :: Heap k a -> Bool
null Empty = True
null Heap {} = False

-- |
--
-- The number of key-value pairs in the heap.
--
-- /O(1)/.
--
-- >>> map size [the, quick, brown, fox]
-- [3,5,5,3]
--
-- >>> size empty
-- 0
--
-- prop> size xs == length (toList xs)
size :: Heap k a -> Int
size Empty = 0
size (Heap s _ _ _ _ _ _) = s

-- |
-- An empty heap.
--
-- >>> empty
-- fromList []
empty :: Heap k a
empty = Empty

-- |
--
-- Construct a heap containing a single key-value pair.
--
-- /O(1)/.
--
-- >>> singleton "foo" 42
-- fromList [("foo",42)]
--
-- prop> toList (singleton k v) == [(k, v)]
singleton :: k -> a -> Heap k a
singleton k v = Heap 1 empty empty k v empty empty

-- |
--
-- Append two heaps, preserving sequential ordering.
--
-- /O(1)/.
--
-- >>> append empty the
-- fromList [('t',0),('h',1),('e',2)]
--
-- >>> append the empty
-- fromList [('t',0),('h',1),('e',2)]
--
-- >>> append the fox
-- fromList [('t',0),('h',1),('e',2),('f',0),('o',1),('x',2)]
--
-- prop> toList (xs `append` ys) == toList xs ++ toList ys
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
        Empty   -> Heap (sx+sy)        xs                        ls2  k2 v2 rs2 r2
        Heap {} -> Heap (sx+sy) Empty ((xs `append` l2) `append` ls2) k2 v2 rs2 r2

-- |
--
-- Sequentially append an arbitrary number of heaps.
--
-- /O(m)/, where /m/ is the length of the input list.
--
-- >>> appends [the, quick, fox]
-- fromList [('t',0),('h',1),('e',2),('q',0),('u',1),('i',2),('c',3),('k',4),('f',0),('o',1),('x',2)]
--
-- prop> toList (appends xss) == concatMap toList xss
appends :: Ord k => [Heap k a] -> Heap k a
appends = foldl' append empty

-- |
--
-- View of the minimum key of a heap, split out from everything occurring to its
-- left and to its right in the sequence.
data MinView k v
  = EmptyView
  | MinView (Heap k v) k v (Heap k v)
  deriving (Eq, Show)

-- |
--
-- Split the 'Heap' at the /leftmost/ occurrence of the smallest key contained
-- in the 'Heap'.
--
-- When the 'Heap' is empty, /O(1)/. When the 'Heap' is not empty, finding the
-- key and value is /O(1)/, and evaluating the remainder of the heap to the left
-- or right of the key-value pair is amortized /O(log n)/.
--
-- >>> minView empty
-- EmptyView
--
-- >>> minView the
-- MinView (fromList [('t',0),('h',1)]) 'e' 2 (fromList [])
--
-- >>> minView (append the the)
-- MinView (fromList [('t',0),('h',1)]) 'e' 2 (fromList [('t',0),('h',1),('e',2)])
--
-- >>> minView quick
-- MinView (fromList [('q',0),('u',1),('i',2)]) 'c' 3 (fromList [('k',4)])
--
-- >>> minView brown
-- MinView (fromList []) 'b' 0 (fromList [('r',1),('o',2),('w',3),('n',4)])
--
-- >>> minView fox
-- MinView (fromList []) 'f' 0 (fromList [('o',1),('x',2)])
--
-- Here is a model implementation of 'minView':
--
-- >>> :{
-- let { minViewModel xs =
--         case toList xs of
--           []        -> EmptyView
--           keyValues ->
--             let minKey          = minimum (map fst keyValues)
--                 (l, (k, v) : r) = break (\(key, _) -> key == minKey) keyValues
--             in MinView (fromList l) k v (fromList r)
--     }
-- :}
--
-- The following property looks different from the others in this module due to
-- working around a limitation of doctest.
--
-- >>> quickCheck $ \xs -> minView (xs :: Heap Integer Integer) == minViewModel xs
-- +++ OK, passed 100 tests.
minView :: Ord k => Heap k a -> MinView k a
minView Empty = EmptyView
minView (Heap _ l ls k v rs r) = MinView (l `append` ls) k v (rs `append` r)

-- |
--
-- Formed from 'empty' and 'append'
instance Ord k => Monoid (Heap k a) where
  mempty = empty
  mappend = append

-- |
--
-- Prepend a key-value pair to the beginning of a 'Heap'.
--
-- /O(1)/.
--
-- >>> cons 'a' 0 fox
-- fromList [('a',0),('f',0),('o',1),('x',2)]
--
-- prop> toList (cons k v xs) == (k, v) : toList xs
cons :: Ord k => k -> a -> Heap k a -> Heap k a
cons k v = (singleton k v <>)

-- |
--
-- Append a key-value pair to the end of a 'Heap'.
--
-- /O(1)/.
--
-- >>> snoc fox 'y' 0
-- fromList [('f',0),('o',1),('x',2),('y',0)]
--
-- prop> toList (snoc xs k v) == toList xs ++ [(k, v)]
snoc :: Ord k => Heap k a -> k -> a -> Heap k a
snoc xs k v = xs <> singleton k v

-- |
--
-- Like 'foldr', but provides access to the key for each value in the folding
-- function.
--
-- >>> foldrWithKey (\k v kvs -> (k, v) : kvs) [] fox
-- [('f',0),('o',1),('x',2)]
--
-- prop> let f k v acc = g `apply` k `apply` v `apply` acc in foldrWithKey f z xs == foldr (uncurry f) z (toList xs)
foldrWithKey :: (k -> a -> b -> b) -> b -> Heap k a -> b
foldrWithKey f = flip go
  where
    go Empty z = z
    go (Heap _ l ls k v rs r) z = go l (go ls (f k v (go rs (go r z))))

-- |
--
-- List the key-value pairs in a 'Heap' in sequence order. This is the semantic
-- function for 'Heap'.
--
-- >>> toList empty
-- []
--
-- >>> toList the
-- [('t',0),('h',1),('e',2)]
--
-- >>> toList quick
-- [('q',0),('u',1),('i',2),('c',3),('k',4)]
--
-- >>> toList brown
-- [('b',0),('r',1),('o',2),('w',3),('n',4)]
--
-- >>> toList fox
-- [('f',0),('o',1),('x',2)]
--
-- /O(n)/ when the spine of the result is evaluated fully.
--
-- prop> toList (fromList xs) == xs
-- prop> fromList (toList xs) == xs
toList :: Heap k a -> [(k, a)]
toList = foldrWithKey (\k v xs -> (k, v) : xs) []

-- |
--
-- List the key-value pairs in a 'Heap' in key order.
--
-- /O(n log n)/ when the spine of the result is evaluated fully.
--
-- >>> toAscList empty
-- []
--
-- >>> toAscList the
-- [('e',2),('h',1),('t',0)]
--
-- >>> toAscList quick
-- [('c',3),('i',2),('k',4),('q',0),('u',1)]
--
-- >>> toAscList brown
-- [('b',0),('n',4),('o',2),('r',1),('w',3)]
--
-- >>> toAscList fox
-- [('f',0),('o',1),('x',2)]
--
-- prop> toAscList xs == Data.List.sortOn fst (toList xs)
toAscList :: Ord k => Heap k a -> [(k, a)]
toAscList = unfoldr f
  where
    f xs =
      case minView xs of
        EmptyView -> Nothing
        MinView l k v r -> Just ((k, v), l <> r)

-- |
--
-- Construct a 'Heap' from a list of key-value pairs.
--
-- /O(n)/.
--
-- >>> fromList (zip [0..3] [4..])
-- fromList [(0,4),(1,5),(2,6),(3,7)]
--
-- prop> toList (fromList xs) == xs
-- prop> fromList (toList xs) == xs
fromList :: Ord k => [(k, a)] -> Heap k a
fromList = foldl' (\acc (k, v) -> snoc acc k v) empty

-- |
--
-- >>> bimap succ (*10) fox
-- fromList [('g',0),('p',10),('y',20)]
--
-- prop> toList (bimap (apply f) (apply g) xs) == map (\(k, v) -> (apply f k, apply g v)) (toList xs)
bimap :: Ord k2 => (k1 -> k2) -> (a -> b) -> Heap k1 a -> Heap k2 b
bimap f g = go
  where
    go Empty = Empty
    go (Heap _ l ls k v rs r) = go l <> go ls <> singleton (f k) (g v) <> go rs <> go r

-- |
--
-- >>> mapKeys succ fox
-- fromList [('g',0),('p',1),('y',2)]
--
-- prop> toList (mapKeys (apply f) xs) == map (\(k, v) -> (apply f k, v)) (toList xs)
mapKeys :: Ord k2 => (k1 -> k2) -> Heap k1 a -> Heap k2 a
mapKeys f = bimap f id

-- |
--
-- Map a function over all values in a heap.
--
-- /O(1)/ when evaluating to WHNF. /O(n)/ when evaluating to NF.
--
-- >>> mapWithKey (\k v -> (k,v)) fox
-- fromList [('f',('f',0)),('o',('o',1)),('x',('x',2))]
--
-- prop> let f k v = g `apply` k `apply` v in mapWithKey f xs == fromList (map (\(k, v) -> (k, f k v)) (toList xs))
mapWithKey :: (k -> a -> b) -> Heap k a -> Heap k b
mapWithKey f = go
  where
    go Empty = Empty
    go (Heap n l ls k v rs r) = Heap n (go l) (go ls) k (f k v) (go rs) (go r)

-- |
--
-- Fold the keys and values in the heap using the given monoid, such that
--
-- /O(n)/.
--
-- >>> foldMapWithKey (\k v -> [(k,v)]) fox
-- [('f',0),('o',1),('x',2)]
--
-- prop> let f k v = g `apply` k `apply` v :: [Integer] in foldMapWithKey f xs == Data.Foldable.fold (mapWithKey f xs)
foldMapWithKey :: Monoid b => (k -> a -> b) -> Heap k a -> b
foldMapWithKey f = go
  where
    go Empty = mempty
    go (Heap _ l ls k v rs r) = go l <> go ls <> f k v <> go rs <> go r

-- |
--
-- Behaves exactly like a regular traverse except that the traversing function
-- also has access to the key associated with a value, such that
--
-- /O(n)/.
--
-- >>> traverseWithKey (\k v -> print (k, v) >> return (succ k, v)) fox
-- ('f',0)
-- ('o',1)
-- ('x',2)
-- fromList [('f',('g',0)),('o',('p',1)),('x',('y',2))]
--
-- prop> let f k v = g `apply` k `apply` v :: ([Integer], Integer) in traverseWithKey f xs == (fromList <$> traverse (\(k, v) -> (,) k <$> f k v) (toList xs))

-- > traverseWithKey f = fromList . traverse ((k, v) -> (,) k $ f k v) . toList
traverseWithKey :: Applicative f => (k -> a -> f b) -> Heap k a -> f (Heap k b)
traverseWithKey f = go
  where
    go Empty = pure Empty
    go (Heap n l ls k v rs r) = Heap n <$> go l <*> go ls <*> pure k <*> f k v <*> go rs <*> go r

-- |
--
-- Behaves exactly like a regular traverse except that it's over the keys
-- instead of the values.
--
-- /O(n)/.
--
-- >>> traverseKeys (\k -> print k >> return (succ k)) fox
-- 'f'
-- 'o'
-- 'x'
-- fromList [('g',0),('p',1),('y',2)]
--
-- prop> traverseKeys (apply f) xs == (fromList <$> traverse (\(k, v) -> flip (,) v <$> (apply f k :: ([Integer], Integer))) (toList xs))
traverseKeys :: (Applicative f, Ord k2) => (k1 -> f k2) -> Heap k1 a -> f (Heap k2 a)
traverseKeys f = go
  where
    go Empty = pure Empty
    go (Heap _ l ls k v rs r) = go l <.> go ls <.> ((`singleton` v) <$> f k) <.> go rs <.> go r
    (<.>) = liftA2 (<>)

-- |
--
-- Equivalent to @WriterT k []@
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
--
-- Equivalent to @WriterT k []@
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
--
-- prop> (xs == ys) == (toList xs == toList ys)
instance (Eq k, Eq a) => Eq (Heap k a) where
  xs == ys = toList xs == toList ys

-- |
--
-- prop> compare xs ys == compare (toList xs) (toList ys)
instance (Ord k, Ord a) => Ord (Heap k a) where
  compare xs ys = compare (toList xs) (toList ys)

-- |
--
-- Formed from 'empty' and 'append'
instance (Monoid k, Ord k) => Applicative.Alternative (Heap k) where
  empty = mempty
  (<|>) = mappend

-- |
--
-- Formed from 'empty' and 'append'
instance (Monoid k, Ord k) => MonadPlus (Heap k) where
  mzero = mempty
  mplus = mappend

-- $setup
--
-- We use QuickCheck to verify the properties given in this documentation. Here
-- is the necessary setup code:
--
-- >>> import Test.QuickCheck
-- >>> import Test.QuickCheck.Function
-- >>> :{
-- instance (Arbitrary k, Arbitrary v, Ord k) => Arbitrary (Heap k v) where
--   arbitrary = fromList <$> arbitrary
--   shrink = map fromList . shrink . toList
-- :}
--
-- Here are some example values used in the documentation for this module:
--
-- >>> let the   = fromList (zip "the"   [0..])
-- >>> let quick = fromList (zip "quick" [0..])
-- >>> let brown = fromList (zip "brown" [0..])
-- >>> let fox   = fromList (zip "fox"   [0..])
--
-- >>> the
-- fromList [('t',0),('h',1),('e',2)]
--
-- >>> quick
-- fromList [('q',0),('u',1),('i',2),('c',3),('k',4)]
--
-- >>> brown
-- fromList [('b',0),('r',1),('o',2),('w',3),('n',4)]
--
-- >>> fox
-- fromList [('f',0),('o',1),('x',2)]
