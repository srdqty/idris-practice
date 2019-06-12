data Dict : Type -> Type where
  MkDict : a => Dict a

interface HasDict (c : Type) (e : Type) | e where
  evidence : e -> Dict c

-- Doesn't work
withDict : HasDict c e => e -> (c => r) -> r
withDict d r = case evidence d of
  MkDict => r
