-- Local Variables:
-- idris-load-packages: ("prelude" "base" "contrib")
-- End:

import Control.ST

data BlockState = ReadWrite | ReadOnly

interface MutableByteBlock (m : Type -> Type) where
  ByteBlock : BlockState -> Type

  new : (capacity : Nat) -> ST m Var [add (ByteBlock ReadWrite)]
  update : (bb : Var) -> String -> ST m () [bb ::: ByteBlock ReadWrite]
  freeze : (bb : Var) -> ST m () [bb ::: ByteBlock ReadWrite :-> ByteBlock ReadOnly]
  escape : (bb : Var) -> ST m String [remove  bb (ByteBlock ReadOnly)]

implementation MutableByteBlock id where
  ByteBlock bs = State String
  new cap = new "" >>= pure
  update bb s = update bb (\x => s)
  freeze bb = update bb (\x => x)
  escape bb = do
    x <- read bb
    delete bb
    pure x

m : ST m String []
m = do
  x <- new 42
  update x "whatever"
  update x "dude"
  freeze x
  escape x

x : String
x = runPure m
