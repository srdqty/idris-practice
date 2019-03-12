import Control.Monad.State

data Store i k v = MkStore i (k -> v)

initialise : i -> (k -> v) -> Store i k v
initialise = MkStore

getInfo : Store i k v -> i
getInfo (MkStore i _) = i

putInfo : i -> Store i k v -> Store i k v
putInfo i (MkStore _ f) = MkStore i f

getValue : k -> Store i k v -> v
getValue k (MkStore _ f) = f k

putValue : Eq k => k -> v -> Store i k v -> Store i k v
putValue k v (MkStore i f) = MkStore i (\k' => if k == k' then v else f k')

data Hash v = MkHash v

hash : v -> Hash v
hash v = MkHash v

getHash : k -> Store i k v -> Hash v
getHash k (MkStore _ f) = hash (f k)

Constraint : Type
Constraint = (Type -> Type) -> Type

data Task : Constraint -> Type -> Type -> Type where
  MkTask : {f : _} -> (c f => (k -> f v) -> f v) -> Task c k v

Tasks : Constraint -> Type -> Type -> Type
Tasks c k v = k -> Maybe (Task c k v)

Build : Constraint -> Type -> Type -> Type -> Type
Build c i k v = Tasks c k v -> k -> Store i k v -> Store i k v

Rebuilder : Constraint -> Type -> Type -> Type -> Type
Rebuilder c ir k v = k -> v -> Task c k v -> Task (MonadState ir) k v

Scheduler : Constraint -> Type -> Type -> Type -> Type -> Type
Scheduler c i ir k v = Rebuilder c ir k v -> Build c i k v

sprsh1 : Applicative g => Tasks Applicative String Integer
sprsh1 {g} "B1" = Just (MkTask {f=g} (\fetch => liftA2 (+) (fetch "A1") (fetch "A2")))
sprsh1 {g} "B2" = Just (MkTask {f=g} (\fetch => liftA (*2) (fetch "B1")))
sprsh1 _ = Nothing

busy : Eq k => Build Applicative () k v
busy {k} {v} tasks key store = execState (fetch key) store
  where
    fetch : k -> State (Store () k v) v
    fetch key = case tasks key of
      Nothing => gets (getValue key)
      Just (MkTask task) => do
        val <- task fetch
        modify (putValue key val)
        pure val

store : Store () String Integer
store = initialise () (\key => if key == "A1" then 10 else 20)

result : Store () String Integer
result = busy (sprsh1 {g=State (Store () String Integer)}) "B2" store

b1 : Integer
b1 = getValue "B1" result

b2 : Integer
b2 = getValue "B2" result
