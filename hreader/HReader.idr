module HReader

{-
import Control.Monad.Reader
import Control.Monad.State

%default total

interface Monad m => MonadHReader r1 (m : Type -> Type) | m where
  SetEnv : Type -> (Type -> Type) -> Type -> Type
  hlocal : Monad (SetEnv r2 m) => (r1 -> r2) -> SetEnv r2 m a -> m a

implementation Monad m => MonadHReader r1 (ReaderT r1 m) where
  SetEnv r2 _ = ReaderT r2 m
  hlocal f action = RD (runReaderT action . f)

implementation MonadHReader r1 m => MonadHReader r1 (StateT s m) where
   SetEnv r2 _ = StateT s (SetEnv r2 m)
   hlocal f action = ?whatever
-}


{-
interface Example t where
  x : Int

implementation (cX : Example x, cY : Example y) => Example (x, y) where
  x = ?idk -- (T @{cX}, T @{cY})
-}

{-
interface Example t where
  X : Type

f : {cT : Example t} -> Type
f {cT} = X @{cT}

implementation (cA : Example a, cB : Example b) => Example (a, b) where
  X = (left, right) where
    left : {auto cT : Example a} -> Type
    left {cT} = X @{cT}

    right : {auto cT : Example b} -> Type
    right {cT} = X @{cT}

implementation Example Int where
  X = Char

implementation Example Char where
  X = String

y : {auto cX : Example (Int, Char)} -> X @{cX}
y = ?idk
-}

{-
interface Example t where
  X : Type

implementation Example Int where
  X = Char

implementation Example Char where
  X = String

implementation [pairExample] (Example a, Example b) => Example (a, b) where
  X = (left, right) where
    left : {auto cT : Example a} -> Type
    left {cT} = X @{cT}

    right : {auto cT : Example b} -> Type
    right {cT} = X @{cT}

pairExample2 : Example (Int, Char)
pairExample2 = pairExample
-}

-- y : X @{the (Example (Int, Char)) pairExample}
-- y = ('c', "ok")

-- z : X @{pairExample2}
-- z = ?idk

record Example (t : Type) where
  constructor MkExample
  X : Type

IntExample : Example Int
IntExample = MkExample Char

CharExample : Example Char
CharExample = MkExample String

PairExample : Example a -> Example b -> Example (a, b)
PairExample exA exB = MkExample (X exA, X exB)

y : X (PairExample IntExample CharExample)
y = ('c', "ok")
