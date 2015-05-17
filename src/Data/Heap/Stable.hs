{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveTraversable #-}

-- | This module provides an implementation of stable heaps, also known
-- as fair priority queues. Unless stated otherwise, the asymptotic
-- efficiencies of functions on 'Heap' assume that arguments are
-- already evaluated to WHNF and that the result will be evaluated to
-- WHNF.
module Data.Heap.Stable
       ( Heap ()
       , empty
       , singleton
       , union
       , splitMin
       , cons
       , snoc
       , foldrWithKey
       , toList
       , fromList
       , bimap
       , mapKeys
       ) where

import Data.Monoid
import qualified GHC.Exts

-- | Semantically, @Heap k a@ is equivalent to @[(k, a)]@, but its
-- operations have different efficiencies.
data Heap k a
  = Heap !(Heap k a) (Heap k a) !k a (Heap k a) !(Heap k a)
  | Empty
  deriving (Functor, Foldable, Traversable)

-- | @toList empty = []@
empty :: Heap k a
empty = Empty

-- | /O(1)/.
--
-- > toList (singleton k v) = [(k, v)]
singleton :: k -> a -> Heap k a
singleton k v = Heap empty empty k v empty empty

-- | /O(1)/.
--
-- > toList (xs `union` ys) = toList xs ++ toList ys
union :: Ord k => Heap k a -> Heap k a -> Heap k a
Empty `union` ys = ys
xs `union` Empty = xs
xs@(Heap l1 ls1 k1 v1 rs1 r1) `union` ys@(Heap l2 ls2 k2 v2 rs2 r2)
  | k1 <= k2 =
      case r1 of
        Empty            -> Heap l1 ls1 k1 v1  rs1                     ys
        Heap _ _ _ _ _ _ -> Heap l1 ls1 k1 v1 (rs1 `union` (r1 `union` ys)) Empty
  | otherwise =
      case l2 of
        Empty            -> Heap         xs                     ls2  k2 v2 rs2 r2
        Heap _ _ _ _ _ _ -> Heap Empty ((xs `union` l2) `union` ls2) k2 v2 rs2 r2

-- | Split the 'Heap' at the first occurrence of the smallest key
-- contained in the 'Heap'.
--
-- When the 'Heap' is empty, /O(1)/. When the 'Heap' is not empty,
-- finding the key and value is /O(1)/, and evaluating the remainder
-- of the heap to the left or right of the key-value pair is /O(log n)/.
--
-- > toList xs =
-- > case splitMin xs of
-- >   Nothing -> []
-- >   Just (l, k, v, r) -> toList l ++ [(k, v)] ++ toList r
splitMin :: Ord k => Heap k a -> Maybe (Heap k a, k, a, Heap k a)
splitMin Empty = Nothing
splitMin (Heap l ls k v rs r) = Just (l `union` ls, k, v, rs `union` r)

instance Ord k => Monoid (Heap k a) where
  mempty = empty
  mappend = union

-- | /O(1)/.
--
-- > toList (cons k v xs) = (k, v) : toList xs
cons :: Ord k => k -> a -> Heap k a -> Heap k a
cons k v = (singleton k v <>)

-- | /O(1)/.
--
-- > toList (snoc xs k v) = toList xs ++ [(k, v)]
snoc :: Ord k => Heap k a -> k -> a -> Heap k a
snoc xs k v = xs <> singleton k v

-- | > foldrWithKey f z xs = foldr (uncurry f) z (toList xs)
foldrWithKey :: (k -> a -> b -> b) -> b -> Heap k a -> b
foldrWithKey f = flip go
  where
    go Empty z = z
    go (Heap l ls k v rs r) z = go l (go ls (f k v (go rs (go r z))))

-- | List the key-value pairs in a 'Heap', in order. The semantic
-- function for 'Heap'.
--
-- /O(n)/.
toList :: Heap k a -> [(k, a)]
toList = foldrWithKey (\k v xs -> (k, v) : xs) []

-- | Construct a 'Heap' from a list of key-value pairs.
--
-- /O(n)/.
fromList :: Ord k => [(k, a)] -> Heap k a
fromList = foldMap (uncurry singleton)

-- | > toList (bimap f g xs) = map (f *** g) (toList xs)
bimap :: Ord k2 => (k1 -> k2) -> (a -> b) -> Heap k1 a -> Heap k2 b
bimap f g = go
  where
    go Empty = Empty
    go (Heap l ls k v rs r) = go l <> go ls <> singleton (f k) (g v) <> go rs <> go r

-- | > toList (mapKeys f xs) = map (first f) (toList xs)
mapKeys :: Ord k2 => (k1 -> k2) -> Heap k1 a -> Heap k2 a
mapKeys f = bimap f id

instance (Monoid k, Ord k) => Applicative (Heap k) where
  pure = singleton mempty
  Empty <*> _ = Empty
  _ <*> Empty = Empty
  fs@(Heap fl fls fk f frs fr) <*> xs
    =  (fl  <*>         xs)
    <> (fls <*>         xs)
    <> (bimap (fk <>) f xs)
    <> (frs <*>         xs)
    <> (fr  <*>         xs)

instance (Monoid k, Ord k) => Monad (Heap k) where
  return = pure
  Empty >>= _ = Empty
  Heap xl xls xk x xrs xr >>= f
    =  (xl  >>= f)
    <> (xls >>= f)
    <> (mapKeys (xk <>) (f x))
    <> (xrs >>= f)
    <> (xr  >>= f)

instance (Show k, Show a) => Show (Heap k a) where
  showsPrec d h = showParen (d > 10) $ showString "fromList " . shows (toList h)

instance Ord k => GHC.Exts.IsList (Heap k a) where
  type Item (Heap k a) = (k, a)
  fromList = fromList
  toList   = toList

instance (Eq k, Eq a) => Eq (Heap k a) where
  xs == ys = toList xs == toList ys

instance (Ord k, Ord a) => Ord (Heap k a) where
  compare xs ys = compare (toList xs) (toList ys)
