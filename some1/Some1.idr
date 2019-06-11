-- https://reasonablypolymorphic.com/some1-like-you/#/title

data Value
  = VObject (List (String, Value))
  | VArray (List Value)
  | VString String
  | VNumber Double
  | VBool Bool
  | Null

interface FromJSON a where
  fromJSON : Value -> a

interface ToJSON a where
  toJSON : a -> Value
