%default total

-- TODO: intersection operator for lists?

data NotEq : (x : a) -> (y : b) -> Type where
  MkNotEq : Not (x = y) -> NotEq x y

%hint
notEq : DecEq t
     => {x1 : t}
     -> {x2 : t}
     -> {auto p : (decEq x1 x2) = No contra}
     -> NotEq x1 x2
notEq {contra} = MkNotEq contra

data Empty : List a -> Type where
  IsEmpty : Empty []

data Elem : a -> List a -> Type where
  Here : Elem x (x :: xs)
  There : (later : Elem x xs) -> Elem x (y :: xs)

data NotElem : a -> List a -> Type where
  NotHere : NotElem x []
  NotThere : {auto p : NotEq x y} -> NotElem x xs -> NotElem x (y :: xs)

namespace Quantifiers
  data Any : (p : a -> Type) -> List a -> Type where
    Here : p x -> Any p (x :: xs)
    There : Any p xs -> Any p (x :: xs)

  data All : (p : a -> Type) -> List a -> Type where
    Nil : All p []
    (::) : p x -> All p xs -> All p (x :: xs)

data Disjoint : List a -> List a -> Type where
  MkDisjoint : All (flip NotElem xs) ys -> All (flip NotElem ys) xs -> Disjoint xs ys


record Tau where
  constructor MkTau
  null : Bool
  first : List Char
  flast : List Char

data Separate : Tau -> Tau -> Type where
  MkSeparate : {t1 : Tau}
            -> {t2 : Tau}
            -> (p : Disjoint (flast t1) (first t2))
            -> (q : null t1 = False)
            -> Separate t1 t2

data Apart : Tau -> Tau -> Type where
  MkApart : {t1 : Tau}
         -> {t2 : Tau}
         -> (p : Disjoint (first t1) (first t2))
         -> (q : (null t1 && null t2) = False)
         -> Apart t1 t2

tauBot : Tau
tauBot = MkTau False [] []

tauAlt : Tau -> Tau -> Tau
tauAlt t1 t2 = MkTau
  (null t1 || null t2)
  (union (first t1) (first t2))
  (union (flast t1) (flast t2))

tauEps : Tau
tauEps = MkTau True [] []

tauChar : Char -> Tau
tauChar c = MkTau False [c] []

ifOrNil : Bool -> (Lazy (List a)) -> List a
ifOrNil b l = ifThenElse b l []

tauSeq : Tau -> Tau -> Tau
tauSeq Main.tauBot _ = tauBot
tauSeq _ Main.tauBot = tauBot
tauSeq t1 t2 = MkTau
  (null t1 && null t2)
  (union (first t1) (ifOrNil (null t1) (first t2)))
  (union (flast t2) (ifOrNil (null t2) (union (first t2) (flast t1))))

tauStar : Tau -> Tau
tauStar t = MkTau True (first t) (union (flast t) (first t))

Context : Type
Context = List (String, Tau)

data Expr
  = Bot
  | Alt Expr Expr
  | Eps
  | C Char
  | Seq Expr Expr
  | Var String
  | Fix String Expr

data Typing : Context -> Context -> Expr -> Tau -> Type where
  TEps : Typing gamma delta Eps Main.tauEps
  TChar : Typing gamma delta (C c) (Main.tauChar c)
  TBot : Typing gamma delta Bot Main.tauBot
  TVar : Elem (v, t) gamma
      -> Typing gamma delta (Var v) t
  TFix : Typing gamma ((x, t) :: delta) e t
      -> Typing gamma delta (Fix x e) t
  TCat : Typing gamma delta e t
      -> Typing (delta ++ gamma) [] e' t'
      -> Separate t t'
      -> Typing gamma delta (Seq e e') (tauSeq t t')
  TVee : Typing gamma delta e t
      -> Typing gamma delta e' t'
      -> Apart t t'
      -> Typing gamma delta (Alt e e') (tauAlt t t')
