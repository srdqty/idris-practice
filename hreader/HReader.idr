module HReader

import Control.Monad.Reader
import Control.Monad.State

%access public export
%default total

data Proxy : (t : k) -> Type where
  P : Proxy t

proxy : (t : k) -> Proxy t
proxy t = the (Proxy t) P

interface Monad m => MonadHReader r1 (m : Type -> Type) | m where
  -- Using the proxy so idris can find which SetEnv we mean when using it
  -- as an expression. See the StateT instance, for example
  SetEnv : (p : Proxy m) -> Type -> Type -> Type
  -- Unlike the Haskell version, we dropped Monad constraint for SetEnv P r2 a ...
  -- Too many problems with interface implementations not found ...
  -- Let's see how this goes ...
  -- I think this will let us use the interface methods on concrete types but we
  -- won't be able to write functions only in terms of the abstract classes :'(
  hlocal : {a : Type} -> (r1 -> r2) -> SetEnv P r2 a -> m a

implementation Monad m => MonadHReader r1 (ReaderT r1 m) where
  SetEnv _ r2 = ReaderT r2 m
  hlocal f action = RD (runReaderT action . f)

mapStateT : {m, n : Type -> Type} -> (m (a, s) -> n (b, s)) -> StateT s m a -> StateT s n b
mapStateT f m = ST $ f . runStateT m

implementation MonadHReader r1 m => MonadHReader r1 (StateT s m) where
   SetEnv _ r2 = StateT s (SetEnv (proxy m) r2)
   hlocal {a} {m} = mapStateT . hlocal {a=(a, s)} {m=m}

g : Monad m => ReaderT Integer m String
g = do
  i <- ask
  let j = i + 1
  hlocal f n
where
  f : Integer -> String
  f i = "abc"

  n : SetEnv (proxy (ReaderT Integer m)) String String
  n = do
    str <- ask
    pure (str ++ "def")

x : String
x = runIdentity $ runReaderT g 5
