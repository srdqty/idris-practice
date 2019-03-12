Constraint : Type
Constraint = (Type -> Type) -> Type

data Task : Constraint -> Type -> Type -> Type where
  MkTask : {f : _} -> (c f => (k -> f v) -> f v) -> Task c k v

Tasks : Constraint -> Type -> Type -> Type
Tasks c k v = k -> Maybe (Task c k v)

interface Something (f : Type -> Type) where

sprsh1 : {g : _} -> Something g => Tasks Applicative String Integer
sprsh1 {g} "B1" = Just (MkTask {f=g} (\fetch => liftA2 (+) (fetch "A1") (fetch "A2")))
sprsh1 {g} "B2" = Just (MkTask {f=g} (\fetch => liftA (*2) (fetch "B1")))
sprsh1 _ = Nothing
