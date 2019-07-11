module HReader

import Control.Monad.Reader
import Control.Monad.State

%access public export
%default total

data Proxy : (t : k) -> Type where
  P : Proxy t

proxy : (t : k) -> Proxy t
proxy t = the (Proxy t) P

mapStateT : {m, n : Type -> Type} -> (m (a, s) -> n (b, s)) -> StateT s m a -> StateT s n b
mapStateT f m = ST $ f . runStateT m

namespace MonadDict
  data MonadDict : (m : Type -> Type) -> Type where
    MkMonadDict : Monad m => MonadDict m

  (>>=) : MonadDict m -> m a -> (a -> m b) -> m b
  (>>=) MkMonadDict = Monad.(>>=)

  join : MonadDict m -> m (m a) -> m a
  join MkMonadDict = Monad.join

  pure : MonadDict m -> a -> m a
  pure MkMonadDict = Applicative.pure

interface Monad m => MonadHReader2 r1 (m : Type -> Type) | m where
  LocalM : (p : Proxy m) -> Type -> Type -> Type

  Dict : (p : Proxy m) -> MonadDict (LocalM P r2)

  hlocal2 : {a : Type} -> (r1 -> r2) -> LocalM P r2 a -> m a

implementation Monad m => MonadHReader2 r1 (ReaderT r1 m) where
  LocalM _ r2 = ReaderT r2 m
  Dict _ = MkMonadDict
  hlocal2 f action = RD (runReaderT action . f)

implementation MonadHReader2 r1 m => MonadHReader2 r1 (StateT s m) where
  LocalM _ r2 = StateT s (LocalM (proxy m) r2)
  Dict _ = MkMonadDict
  hlocal2 {a} {m} = mapStateT . hlocal2 {a=(a, s)} {m=m}

interface Monad m => MonadHReader r1 (m : Type -> Type) | m where
  -- Using the proxy so idris can find which SetEnv we mean when using it
  -- as an expression. See the StateT instance, for example
  SetEnv : (p : Proxy m) -> Type -> Type -> Type
  -- Unlike the Haskell version, we dropped Monad constraint for SetEnv P r2 a ...
  -- Too many problems with interface implementations not found ...
  -- Seems like trying to use interfaces in higher ranked types doesn't really
  -- work ... Let's see how this goes ...
  -- I think this will let us use the interface methods on concrete types but we
  -- won't be able to write functions only in terms of the abstract classes :'(
  hlocal : {a : Type} -> (r1 -> r2) -> SetEnv P r2 a -> m a

implementation Monad m => MonadHReader r1 (ReaderT r1 m) where
  SetEnv _ r2 = ReaderT r2 m
  hlocal f action = RD (runReaderT action . f)

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
