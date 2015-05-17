import Criterion.Main

import Data.List (unfoldr)
import Data.Vector.Unboxed (Vector)
import qualified Data.Vector.Unboxed as Vector
import System.Random.MWC
import qualified Data.Foldable as Foldable
import Control.Arrow

import qualified Data.Heap.Stable as Stable
import qualified Data.PQueue.Prio.Min as PQueue
import qualified Data.PriorityQueue.FingerTree as FingerTree
import qualified Data.Heap as Heap

createGroup :: Vector (Int, ()) -> String -> (a -> [(Int, ())]) -> (a -> Int -> () -> a) -> a -> Benchmark
createGroup xs name toListAsc snoc empty =
  bench name $ whnf (sum . map fst . toListAsc . Vector.foldl' (\acc (k, v) -> snoc acc k v) empty) xs

main :: IO ()
main = do
  xs <- withSystemRandom $ asGenST (`uniformVector` 1000) :: IO (Vector Int)
  let create = createGroup (Vector.zip xs (Vector.replicate 1000 ()))
  defaultMain
    [ bgroup "unstable"
      [ create "pqueue" PQueue.toAscList (\q k v -> PQueue.insert k v q) PQueue.empty
      , create "heap" (map (Heap.priority &&& Heap.payload) . Foldable.toList) (\h k v -> Heap.insert (Heap.Entry k v) h) Heap.empty
      ]
    , bgroup "stable"
      [ create "stable-heap" Stable.toListAsc Stable.snoc Stable.empty
      , create "fingertree" (unfoldr FingerTree.minViewWithKey) (\q k v -> FingerTree.add k v q) FingerTree.empty
      ]
    ]
