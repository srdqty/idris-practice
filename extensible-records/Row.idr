-- Experiments based on this paper:
-- https://www.microsoft.com/en-us/research/publication/extensible-records-with-scoped-labels/

infix 5 :=
infix 5 :::
infix 4 !!

namespace Row
    data RowField : lty -> ty -> Type where
      (:::) : (label : lty) -> (x : ty) -> RowField lty ty


    rfEq : (eqT : t = t') -> (eqL : l = l') -> (l ::: t) = (l' ::: t')
    rfEq Refl Refl = Refl

    lemma_neqT : (neqT : (t = t') -> Void)
              -> (eqL : l = l')
              -> ((l ::: t) = (l' ::: t') -> Void)
    lemma_neqT neqT Refl Refl = neqT Refl

    lemma_neqL : (neqL : l = l' -> Void)
              -> ((l ::: t) = (l' ::: t') -> Void)
    lemma_neqL neqL Refl = neqL Refl

    implementation (DecEq lty, DecEq ty) => DecEq (RowField lty ty) where
      decEq (l ::: t) (l' ::: t') = case decEq l l' of
        Yes eqL => case decEq t t' of
          Yes eqT => Yes (rfEq eqT eqL)
          No neqT => No (lemma_neqT neqT eqL)
        No neqL => No (lemma_neqL neqL)

    data Row : lty -> ty -> Type where
      Nil : Row lty ty
      (::) : RowField lty ty -> Row lty ty -> Row lty ty

    data RowElem : (label : lty) -> (x : ty) -> Row lty ty -> Type where
      Here : RowElem label ty ((label ::: ty) :: r)
      There : (later : RowElem label ty r) -> RowElem label ty (a :: r)

    data RowEq : Row lty ty -> Row lty ty -> Type where
      Base : RowEq [] []
      Head : RowEq xs ys -> RowEq ((l ::: t) :: xs) ((l ::: t) :: ys)
      Swap : (l = l' -> Void)
          -> RowEq ((l ::: t) :: (l' ::: t') :: xs)
                   ((l' ::: t') :: (l ::: t) :: xs)

    (!!) : Row lty ty -> Row lty ty -> Row lty ty
    (!!) [] [] = []
    (!!) [] ys = ys
    (!!) (x :: z) y = x :: (z !! y)


namespace Record
    data Field : lty -> Type -> Type where
      (:=) : (label : lty) -> (v : ty) -> Field label ty

    data Record : Row lty Type -> Type where
      Nil : Record []
      -- Extension
      (::) : Field l ty -> Record r -> Record ((l ::: ty) :: r)


-- Selection
select : Record r ->  RowElem l a r -> a
select ((l := v) :: z) Here = v
select (x :: z) (There later) = select z later

(.) : Record r -> (l : lty) -> { auto prf : RowElem l a r } -> a
(.) rec l {prf} = select rec prf

-- Restriction
-- TODO

-- Row Equality
-- TODO

a : RowField String Type
a = "a" ::: Char

x : Row String Type
x = ["a" ::: Char, "b" ::: Integer]

b : RowField String (Type -> Type)
b = "b" ::: Maybe

y : Row String (Type -> Type)
y = [b, "f" ::: Either String]

r : Record Main.x
r = ["a" := 'c', "b" := 5]

s : Record (("d" ::: String) :: Main.x)
s = ("d" := "yoyoyo") :: r

t : Record ["a" ::: Integer, "b" ::: Integer, "c" ::: Integer]
t = ["a" := 1, "b" := 2, "c" := 3]

q : Record ["b" ::: Integer]
q = ["b" := 7]

f : {auto prf: RowElem "b" Integer r} -> Record r -> Integer
f t = t . "b"

g : Integer
g = f q

h : {auto prf1: RowElem "c" Integer r}
 -> {auto prf2: RowElem "b" Integer r}
 -> Record r
 -> Integer
h t = t . "b" + t . "c"
