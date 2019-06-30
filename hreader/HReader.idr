module HReader

import Control.Monad.Reader
import Control.Monad.State

%access public export
%default total

data Proxy : (t : k) -> Type where
  P : Proxy t

interface Monad m => MonadHReader r1 (m : Type -> Type) | m where
  SetEnv : (p : Proxy m) -> Type -> Type -> Type
  -- Unlike the Haskell version, we dropped Monad constraint for SetEnv P r2 a ...
  -- Too many problems with interface implementations not found ...
  -- Let's see how this goes ...
  hlocal : {a : Type} -> (r1 -> r2) -> SetEnv P r2 a -> m a

implementation Monad m => MonadHReader r1 (ReaderT r1 m) where
  SetEnv _ r2 = ReaderT r2 m
  hlocal f action = RD (runReaderT action . f)

mapStateT : {m, n : Type -> Type} -> (m (a, s) -> n (b, s)) -> StateT s m a -> StateT s n b
mapStateT f m = ST $ f . runStateT m

implementation MonadHReader r1 m => MonadHReader r1 (StateT s m) where
   SetEnv _ r2 = StateT s (SetEnv (the (Proxy m) P) r2)
   hlocal {a} {m} = mapStateT . hlocal {a=(a, s)} {m=m}
