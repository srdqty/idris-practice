module OpClassesRepro

-- Making this work by using implicit paramters instead:
-- https://gist.github.com/sellout/6a9a16230b4eef462832114eadb6bd7f#gistcomment-2967130


%default total

data Associative : (t -> t -> t) -> Type where
  MkAssociative : ({a : t} -> {b : t} -> {c : t} -> (op (op a b) c = op a (op b c)))
               -> Associative op

record SemigroupRec (t : Type) (op : t -> t -> t) where
    constructor SemigroupInfo
    associative : Associative op

resolveSemigroup
  :  {auto associative : Associative op}
  -> SemigroupRec t op
resolveSemigroup {associative} = SemigroupInfo associative

plusAssociative' : {left : Nat} -> left + (centre + right) = left + centre + right
plusAssociative' {left} {centre} {right} = plusAssociative left centre right

%hint
addAssoc : Associative Prelude.Nat.plus
addAssoc = MkAssociative (sym plusAssociative')

%hint
create : SemigroupRec Nat Prelude.Nat.plus
create = resolveSemigroup
