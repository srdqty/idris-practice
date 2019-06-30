{-# LANGUAGE TypeFamilies #-}

class Example t where
  type X t :: *

instance Example Int where
  type X Int = Char

instance Example Char where
  type X Char = String

instance (Example a, Example b) => Example (a, b) where
  type X (a, b) = (X a, X b)

y :: X (Int, Char)
y = ('c', "ok")
