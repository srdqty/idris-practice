{-
Experiment with stuff from "Lazy Functional State Threads"
http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.50.3299
-}
namespace ST
  data State s = MkState

  ST : Type -> Type -> Type
  ST s a = State s -> (a, State s)

  pure : a -> ST s a
  pure x s = (x, s)

  (>>=) : ST s a -> (a -> ST s b) -> ST s b
  (>>=) {a} {s} m k s0 = k (fst xs1) (snd xs1)
    where
      xs1 : (a, State s)
      xs1 = m s0

  runST : ({s : Type} -> ST s a) -> a
  runST m = fst (m {s=Void} MkState)

  data MutArr s = MkMutArr
  data Array = MkArray

  newArr : (Int, Int) -> Int -> ST s (MutArr s)
  newArr _ _ = pure MkMutArr

  readArr : MutArr s -> Int -> ST s Int
  readArr _ _ = pure 42

  writeArr : MutArr s -> Int -> Int -> ST s ()
  writeArr _ _ _ = pure ()

  freezeArr : MutArr s -> ST s Array
  freezeArr _ = pure MkArray

f : ST s Int
f = do
  x <- pure 4
  pure (x + 3)

n : Int
n = runST f

x : Array
x = runST $ do
  arr <- newArr (1,1) 1
  writeArr arr 1 2
  i <- readArr arr 3
  writeArr arr i 42
  freezeArr arr

v : ST s (MutArr s)
v = newArr (1, 1) 1

-- Does not type check
-- v' : MutArr s
-- v' {s} = runST (v {s})

-- try f : MutVar  s a -> MutVar s a example on pg 4
