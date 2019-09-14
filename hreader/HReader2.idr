%default total

record MyMonad (m : Type -> Type) where
  constructor MkMyMonad
  pure : {a : Type} -> a -> m a
  bind : {a : Type} -> {b : Type} -> m a -> (a -> m b) -> m b

record MyMonadReader (r : Type) (m : Type -> Type) where
  constructor MkMyMonadReader
  ask : m r
  local : {a : Type} -> (r -> r) -> m a -> m a

record ReaderT (r : Type) (m : Type -> Type) (a : Type) where
  constructor RD
  runReaderT : r -> m a

liftReaderT : m a -> ReaderT r m a
liftReaderT m = RD (const m)

readerTMonad : MyMonad m -> MyMonad (ReaderT r m)
readerTMonad mdict = MkMyMonad pure' bind' where
  pure' : a -> ReaderT r m a
  pure' = RD . const . MyMonad.pure mdict

  bind' : ReaderT r m a -> (a -> ReaderT r m b) -> ReaderT r m b
  bind' (RD rma) f = RD (\r => MyMonad.bind mdict (rma r) (ramb r)) where
    ramb : r -> a -> m b
    ramb = flip (runReaderT . f)

readerTMonadReader : MyMonad m -> MyMonadReader r (ReaderT r m)
readerTMonadReader mdict = MkMyMonadReader ask' local' where
  ask' : ReaderT r m r
  ask' = RD (MyMonad.pure mdict)

  local' : (r -> r) -> ReaderT r m a -> ReaderT r m a
  local' f (RD rma) = RD (rma . f)

record MyMonadHReader (r1 : Type) (m : Type -> Type) where
  constructor MkMyMonadHReader
  SetEnv : (r2 : Type) -> Type -> Type
  SetEnvMonad : (r2 : Type) -> MyMonad (SetEnv r2)
  hlocal : {r2 : Type}
       -> {a : Type}
       -> (r1 -> r2)
       -> (MyMonad (SetEnv r2) -> SetEnv r2 a) -> m a

readerTMonadHReader : MyMonad m
                   -> ((r2 : Type) -> MyMonad (ReaderT r2 m))
                   -> MyMonadHReader r1 (ReaderT r1 m)
readerTMonadHReader mdict r2dict = MkMyMonadHReader setEnv' r2dict hlocal' where
  setEnv' : (r2 : Type) -> Type -> Type
  setEnv' r2 = ReaderT r2 m

  hlocal' : (r1 -> r2) -> (MyMonad (ReaderT r2 m) -> ReaderT r2 m a) -> ReaderT r1 m a
  hlocal' {r2} f action = RD (runReaderT (action (r2dict r2)) . f)


x : MyMonadHReader r1 (ReaderT r1 Maybe)
x = readerTMonadHReader maybeMonad (\r => readerTMonad {r} maybeMonad) where
  bind' : Maybe a -> (a -> Maybe b) -> Maybe b
  bind' (Just x) f = f x
  bind' Nothing _ = Nothing

  maybeMonad : MyMonad Maybe
  maybeMonad = MkMyMonad Just bind'
