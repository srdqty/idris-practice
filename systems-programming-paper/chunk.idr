import Data.Fin
import Data.So

data Prop : Type where
  PLt : Nat -> Nat -> Prop
  PEq : Nat -> Nat -> Prop
  PBool : Bool -> Prop
  PAnd : Prop -> Prop -> Prop
  POr : Prop -> Prop -> Prop

data Chunk : Type where
  Bit : (width : Nat) -> Chunk
  Cstring : Chunk
  Lstring : Int -> Chunk
  ChunkProp : (P : Prop) -> Chunk

propTy : Prop -> Type
propTy (PLt x y) = LT x y
propTy (PEq x y) = x = y
propTy (PBool b) = So b
propTy (PAnd s t) = (propTy s, propTy t)
propTy (POr s t) = Either (propTy s) (propTy t)

chunkTy : Chunk -> Type
chunkTy (Bit width) = Fin (power width 2)
chunkTy Cstring = String
chunkTy (Lstring i) = String
chunkTy (ChunkProp p) = propTy p
