{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
module Data.Heap.Stable (Heap (), empty, singleton, union, splitMin) where

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
