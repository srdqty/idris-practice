module OpClassesRepro

-- Making this work by using implicit paramters instead:
-- https://gist.github.com/sellout/6a9a16230b4eef462832114eadb6bd7f#gistcomment-2967130

record SemigroupRec (t : Type) (op : t -> t -> t) where
    constructor SemigroupInfo
    associative : {a : t} -> {b : t} -> {c : t} -> (op (op a b) c = op a (op b c))

resolveSemigroup
  :  {auto associative : {a : t} -> {b : t} -> {c : t} -> (op (op a b) c = op a (op b c))}
  -> SemigroupRec t op
resolveSemigroup {associative} = SemigroupInfo associative

%hint
addAssoc
  : {a : Nat} -> {b : Nat} -> {c : Nat} -> plus (plus a b) c = plus a (plus b c)
addAssoc {a} {b} {c} = sym (plusAssociative a b c)

%hint
create : SemigroupRec Nat Prelude.Nat.plus
create = resolveSemigroup
