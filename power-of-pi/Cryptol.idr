import Data.Vect

data Bit : Type where
  O : Bit
  I : Bit

Word : Nat -> Type
Word n = Vect n Bit
