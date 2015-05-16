{-# LANGUAGE DeriveTraversable #-}
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

data Heap k a
  = Heap !(Heap k a) (Heap k a) !k a (Heap k a) !(Heap k a)
  | Empty
  deriving (Functor, Foldable, Traversable)

empty :: Heap k a
empty = Empty

singleton :: k -> a -> Heap k a
singleton k v = Heap empty empty k v empty empty

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

splitMin :: Ord k => Heap k a -> Maybe (Heap k a, k, a, Heap k a)
splitMin Empty = Nothing
splitMin (Heap l ls k v rs r) = Just (l `union` ls, k, v, rs `union` r)

instance Ord k => Monoid (Heap k a) where
  mempty = empty
  mappend = union

cons :: Ord k => k -> a -> Heap k a -> Heap k a
cons k v = (singleton k v <>)

snoc :: Ord k => Heap k a -> k -> a -> Heap k a
snoc xs k v = xs <> singleton k v

foldrWithKey :: (k -> a -> b -> b) -> b -> Heap k a -> b
foldrWithKey f = flip go
  where
    go Empty z = z
    go (Heap l ls k v rs r) z = go l (go ls (f k v (go rs (go r z))))

toList :: Heap k a -> [(k, a)]
toList = foldrWithKey (\k v xs -> (k, v) : xs) []

fromList :: Ord k => [(k, a)] -> Heap k a
fromList = foldMap (uncurry singleton)

bimap :: Ord k2 => (k1 -> k2) -> (a -> b) -> Heap k1 a -> Heap k2 b
bimap f g = go
  where
    go Empty = Empty
    go (Heap l ls k v rs r) = go l <> go ls <> singleton (f k) (g v) <> go rs <> go r

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
