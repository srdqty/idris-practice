import Data.Vect

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

namespace List
  data Empty : List a -> Type where
    IsEmpty : Empty []

  data Elem : a -> List a -> Type where
    Here : Main.List.Elem x (x :: xs)
    There : (later : Main.List.Elem x xs) -> Elem x (y :: xs)

  lookup' : (xs : List (a, t)) -> Main.List.Elem x xs -> t
  lookup' [] Here impossible
  lookup' [] (There _) impossible
  lookup' ((a, b) :: ys) Here = b
  lookup' (_ :: ys) (There later) = lookup' ys later

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

Context : Nat -> Type
Context n = Vect n Tau

-- Here ctx contains the types of the resulting parsers
data Grammar : (ctx: Vect n Type) -> (t : Type) -> Type where
  Eps : Grammar ctx ()
  Seq : Grammar ctx a -> Grammar ctx b -> Grammar ctx (a, b)
  Chr : Char -> Grammar ctx Char
  Bot : Grammar ctx a
  Alt : Grammar ctx a -> Grammar ctx a -> Grammar ctx a
  Map : (a -> b) -> Grammar ctx a -> Grammar ctx b
  Fix : {a : Type}
     -> Grammar (a :: ctx) a
     -> Grammar ctx a
  Var : (i : Fin k)
     -> Grammar ctx (index i ctx)

data Typing : {a : Type}
--           -> {ctx : Vect n Type}
           -> (gamma: Vect n Tau)
           -> (delta: Vect m Tau)
           -> (g: Grammar ctx a)
           -> (t: Tau)
           -> Type where
  TEps : Typing gamma delta Eps Main.tauEps
  TChar : {c : Char} -> Typing gamma delta (Chr c) (Main.tauChar c)
  TBot : Typing gamma delta Bot Main.tauBot
  TVar : {i : Fin k}
      -> Typing gamma delta (Var i) (index i gamma)
  TFix : {t : Tau}
      -> Typing gamma (t :: delta) g t
      -> Typing gamma delta (Fix g) t
  TCat : {t : Tau}
      -> {t' : Tau}
      -> Typing gamma delta g t
      -> Typing (delta ++ gamma) [] g' t'
      -> Separate t t'
      -> Typing gamma delta (Seq g g') (tauSeq t t')
  TVee : {t : Tau}
      -> {t' : Tau}
      -> Typing gamma delta e t
      -> Typing gamma delta e' t'
      -> Apart t t'
      -> Typing gamma delta (Alt e e') (tauAlt t t')

typeOf : {ctx : Vect n Type} -> (gamma : Vect n Tau) -> Grammar ctx a -> Typing gamma delta g t
{-
p : Typing gamma delta expr tau
 -> Env
 -> Env
 -> String
 -> Maybe String
p TEps _ _ s = Just s
p (TChar {c}) _ _ s with (strM s)
  p TChar _ _ _ | StrNil = Nothing
  p (TChar {c}) _ _ s@(strCons c' xs) | (StrCons c' xs) = if c == c' then Just s else Nothing
p TBot _ _ _ = Nothing
p (TVar {v} elem) env1 env2 s = case lookup v env1 of
  Nothing => Nothing
  Just f => f s
p (TFix _ ) env1 env2 s = ?idk
p (TCat typ typ' _) env1 env2 s = do
  s' <- p typ env1 env2 s
  p typ' (env1 ++ env2) [] s'
p (TVee {t} {t'} typ typ' _) env1 env2 s with (strM s)
  p (TVee {t} {t'} _ _ _) _ _ _ | StrNil = if null t || null t' then Just "" else Nothing
  p (TVee {t} {t'} typ typ' _) env1 env2 s@(strCons c xs) | (StrCons c xs) =
    if elem c (first t) then p typ env1 env2 s
    else if elem c (first t') then p typ' env1 env2 s
    else if null t then p typ env1 env2 s
    else if null t' then p typ' env1 env2 s
    else Nothing
-}
