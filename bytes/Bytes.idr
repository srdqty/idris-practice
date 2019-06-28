import Data.Fin

-- Mutable array of bytes interface

-- Read only slices can escape?

data Byte = MkByte

-- The types
data Bytes : (size: Nat) -> Type where
  MkBytes : (size : Nat) -> Bytes size

set : Bytes size -> (i : Nat) -> Byte -> IO ()
set bytes j b = pure ()

get : Bytes size -> (i : Nat) -> IO Byte
get bytes j = pure MkByte

data Slice : (index : Nat) -> (len : Nat) -> (cap : Nat) -> Type where
  MkSlice : (index : Nat)
       -> (len : Nat)
       -> (cap : Nat)
       -> Bytes bsize
       -> {auto lenBound : LTE len cap}
       -> {auto capBound : LTE (index + cap) bsize }
       -> Slice index len cap

setByte : Slice i l c -> Fin l -> Byte -> IO ()
setByte (MkSlice i l c bytes) j b = set bytes (i + finToNat j) b

appendByte : {auto lt: LT l c} -> Slice i l c -> IO (Slice i (S l) c)
appendByte (MkSlice i l c bytes) = pure (MkSlice i (S l) c bytes)

x : Slice 2 3 7
x = MkSlice 2 3 7 (MkBytes 10)

{-
-- We want the underlying bytes to be equal
-- Should we use the ST vars to allocate bytes?
appendSlice : Slice i l c
           -> Slice j m d
           -> (i + l = j)
           -> Slice i (l + m) (l + d)

splitSlice : Slice i l c
          -> (j : Nat)
          -> LT j l
          -> (Slice i j c, Slice (j + 1) (l - j) (c - j))

truncate : Slice i l c -> Slice i l l
-}
