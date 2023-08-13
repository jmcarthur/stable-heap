{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

import Control.Arrow
import Control.Applicative
import Control.Monad.Trans.Writer
import Data.Heap.Stable (Heap)
import qualified Data.Heap.Stable as Heap
import Data.Foldable
import Data.List
import Data.Ord
import Data.Traversable
import Data.Tuple
import Test.QuickCheck.Function
import Test.Tasty
import Test.Tasty.QuickCheck

main :: IO ()
main = defaultMain tests

-- TODO Many of these tests are now redundant with doctests.
tests :: TestTree
tests =
  testGroup "toList"
  [ testProperty "null" $
    \(H h :: H Int Int) ->
      Heap.null h == (null . Heap.toList) h
  , testProperty "size" $
    \(H h :: H Int Int) ->
      Heap.size h == (length . Heap.toList) h
  , testProperty "empty" $
    (null . Heap.toList) Heap.empty
  , testProperty "singleton" $
    \(k :: Int) (v :: Int) ->
      Heap.toList (Heap.singleton k v) == [(k, v)]
  , testProperty "append" $
    \(H a :: H Int Int) (H b) ->
      Heap.toList (Heap.append a b) == Heap.toList a ++ Heap.toList b
  , testProperty "appends" $
    \(map toHeap -> hs :: [Heap Int Int]) ->
      (Heap.toList . Heap.appends) hs == concatMap Heap.toList hs
  , testProperty "minView" $
    \(H h :: H Int Int) ->
      (minViewToSemantics . Heap.minView) h
      == (minViewSemantics . Heap.toList) h
  , testProperty "cons" $
    \k v (H h :: H Int Int) ->
      (Heap.toList . Heap.cons k v) h == (k, v) : Heap.toList h
  , testProperty "snoc" $
    \(H h :: H Int Int) k v ->
      Heap.toList (Heap.snoc h k v) == Heap.toList h ++ [(k, v)]
  , testProperty "foldrWithKey" $
    \f (z :: Int) (H h :: H Int Int) ->
      let
        g k v acc = f `apply` k `apply` v `apply` acc
      in
        Heap.foldrWithKey g z h == foldr (\(k, v) acc -> g k v acc) z (Heap.toList h)
  , testProperty "toAscList" $
    \(H h :: H Int Int) ->
      Heap.toAscList h == sortBy (comparing fst) (Heap.toList h)
  , testProperty "fromList" $
    \(kvs :: [(Int, Int)]) ->
      (Heap.toList . Heap.fromList) kvs == kvs
  , testProperty "bimap" $
    \(f :: Fun Int Int) (g :: Fun Int Int) (H h) ->
      (Heap.toList . Heap.bimap (apply f) (apply g)) h
      == (map (apply f *** apply g) . Heap.toList) h
  , testProperty "mapKeys" $
    \(f :: Fun Int Int) (H h :: H Int Int) ->
      (Heap.toList . Heap.mapKeys (apply f)) h
      == ((map . first . apply) f . Heap.toList) h
  , testProperty "mapWithKey" $
    \f (H h :: H Int Int) ->
      let
        g k v = f `apply` k `apply` v :: Int
      in
        (Heap.toList . Heap.mapWithKey g) h
        == (map (\(k, v) -> (k, g k v)) . Heap.toList) h
  , testProperty "foldMapWithKey" $
    \f (H h :: H Int Int) ->
      let
        g k v = f `apply` k `apply` v :: [Int]
      in
        Heap.foldMapWithKey g h == ((foldMap . uncurry) g . Heap.toList) h
  , testProperty "traverseWithKey" $
    \f (H h :: H Int Int) ->
      let
        g k v = f `apply` k `apply` v :: ([Int], Int)
      in
        (fmap Heap.toList . Heap.traverseWithKey g) h
        == (traverse (\(k, v) -> (,) k <$> g k v) . Heap.toList) h
  , testProperty "traverseKeys" $
    \f (H h :: H Int Int) ->
      let
        g k = f `apply` k :: ([Int], Int)
      in
        (fmap Heap.toList . Heap.traverseKeys g) h
        == (traverse (\(k, v) -> flip (,) v <$> g k) . Heap.toList) h
  , testProperty "pure" $
    \(x :: Int) ->
      ((Heap.toList . pure) x :: [([Int], Int)]) == (fromWriterT . pure) x
  , testProperty "(<*>)" $
    \(H (fmap apply -> a) :: H [Int] (Fun Int Int)) (H b :: H [Int] Int) ->
      Heap.toList (a <*> b) == fromWriterT (toWriterT a <*> toWriterT b)
  , testProperty "(>>=)" $
    \(H a :: H [Int] Int) (fmap toHeap . apply -> f :: Int -> Heap [Int] Int) ->
      Heap.toList (a >>= f) == fromWriterT (toWriterT a >>= toWriterT . f)
  ]

minViewToSemantics :: Heap.MinView k a -> Maybe ([(k, a)], (k, a), [(k, a)])
minViewToSemantics Heap.EmptyView = Nothing
minViewToSemantics (Heap.MinView l k v r) = Just (Heap.toList l, (k, v), Heap.toList r)

minViewSemantics :: Ord k => [(k, a)] -> Maybe ([(k, a)], (k, a), [(k, a)])
minViewSemantics [] = Nothing
minViewSemantics kvs = Just (l, kv, r)
  where
    minKey = (minimum . map fst) kvs
    (l, kv : r) = break ((== minKey) . fst) kvs

fromWriterT :: WriterT k [] v -> [(k, v)]
fromWriterT = map swap . runWriterT

toWriterT :: Heap k v -> WriterT k [] v
toWriterT = WriterT . map swap . Heap.toList

newtype H k v = H { toHeap :: Heap k v }
  deriving Show

instance (Arbitrary k, Arbitrary v, Ord k) => Arbitrary (H k v) where
  arbitrary = H . Heap.fromList <$> arbitrary
  shrink = map (H . Heap.fromList . shrink) . Heap.toList . toHeap
