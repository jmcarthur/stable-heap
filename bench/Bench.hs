{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

import Control.Monad (replicateM)
import Criterion.Main
import qualified Data.Heap as Heap
import qualified Data.Heap.Stable as Stable
import Data.List (foldl')
import qualified Data.PQueue.Prio.Min as PQueue
import qualified Data.PriorityQueue.FingerTree as FingerTree
import System.Random.MWC (create, uniformR)

class BenchHeap h where
  heapName :: String
  insert :: h -> Int -> h
  empty :: h
  drain :: h -> Int

buildThenDrain :: forall h. (BenchHeap h) => [Int] -> Int
buildThenDrain = drain . foldl' insert (empty @h)

benchHeap :: forall h. (BenchHeap h) => [Int] -> Benchmark
benchHeap keys = bench (heapName @h) $ whnf (buildThenDrain @h) keys

instance BenchHeap (Stable.Heap Int Int) where
  heapName = "stable-heap"
  insert h k = Stable.snoc h k k
  empty = Stable.empty
  drain = go 0
    where
      go !acc h = case Stable.minView h of
        Stable.EmptyView -> acc
        Stable.MinView l k _ r -> go (acc + k) (Stable.append l r)

instance BenchHeap (FingerTree.PQueue Int Int) where
  heapName = "fingertree"
  insert h k = FingerTree.add k k h
  empty = FingerTree.empty
  drain = go 0
    where
      go !acc h = case FingerTree.minViewWithKey h of
        Nothing -> acc
        Just ((k, _), h') -> go (acc + k) h'

instance BenchHeap (PQueue.MinPQueue Int Int) where
  heapName = "pqueue"
  insert h k = PQueue.insert k k h
  empty = PQueue.empty
  drain = go 0
    where
      go !acc h = case PQueue.minViewWithKey h of
        Nothing -> acc
        Just ((k, _), h') -> go (acc + k) h'

instance BenchHeap (Heap.Heap (Heap.Entry Int Int)) where
  heapName = "heaps"
  insert h k = Heap.insert (Heap.Entry k k) h
  empty = Heap.empty
  drain = go 0
    where
      go !acc h = case Heap.viewMin h of
        Nothing -> acc
        Just (e, h') -> go (acc + Heap.priority e) h'

randomKeys :: Int -> IO [Int]
randomKeys n = do
  gen <- create
  replicateM n (uniformR (0, n * 10) gen)

ascendingKeys, descendingKeys, equalKeys :: Int -> [Int]
ascendingKeys n = [0 .. n - 1]
descendingKeys n = [n - 1, n - 2 .. 0]
equalKeys n = replicate n 0

main :: IO ()
main = do
  let sizes = [100, 1000, 10000]
  randomInputs <- traverse (\n -> (n,) <$> randomKeys n) sizes

  let allBenches keys =
        [ benchHeap @(Stable.Heap Int Int) keys,
          benchHeap @(FingerTree.PQueue Int Int) keys,
          benchHeap @(PQueue.MinPQueue Int Int) keys,
          benchHeap @(Heap.Heap (Heap.Entry Int Int)) keys
        ]

  defaultMain
    [ bgroup
        "by-size"
        [bgroup (show n) (allBenches keys) | (n, keys) <- randomInputs],
      bgroup "by-distribution" $
        let n = 1000
            random = snd (randomInputs !! 1)
         in [ bgroup "random" (allBenches random),
              bgroup "ascending" (allBenches (ascendingKeys n)),
              bgroup "descending" (allBenches (descendingKeys n)),
              bgroup "equal" (allBenches (equalKeys n))
            ]
    ]
