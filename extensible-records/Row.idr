infix 5 :=
infix 5 :::

namespace Row
    data RowField : lty -> ty -> Type where
      (:::) : (label : lty) -> (x : ty) -> RowField lty ty

    data Row : lty -> ty -> Type where
      Nil : Row lty ty
      (::) : RowField lty ty -> Row lty ty -> Row lty ty

namespace Record
    data Field : lty -> Type -> Type where
      (:=) : (label : lty) -> (v : ty) -> Field label ty

    data Record : Row lty Type -> Type where
      Nil : Record Nil
      (::) : Field l ty -> Record r -> Record ((l ::: ty) :: r)

a : RowField String Type
a = "a" ::: Char

x : Row String Type
x = ["a" ::: Char, "b" ::: Integer]

b : RowField String (Type -> Type)
b = "b" ::: Maybe

y : Row String (Type -> Type)
y = [b, "f" ::: Either String]

r : Record ["a" ::: Char, "b" ::: Integer]
r = ["a" := 'c', "b" := 5]
