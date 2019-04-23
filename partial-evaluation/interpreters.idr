import Data.Vect

-- %default total

data Ty = TyInt | TyBool | TyFun Ty Ty

interpTy : Ty -> Type
interpTy TyInt = Int
interpTy TyBool = Bool
interpTy (TyFun a t) = interpTy a -> interpTy t

data HasType : (i : Fin n) -> Vect n Ty -> Ty -> Type where
  Stop : HasType FZ (t :: gamma) t
  Pop : HasType k gamma t -> HasType (FS k) (u :: gamma) t

data Expr : Vect n Ty -> Ty -> Type where
  Var : HasType i gamma t -> Expr gamma t
  Val : (x : Int) -> Expr gamma TyInt
  Lam : Expr (a :: gamma) t -> Expr gamma (TyFun a t)
  App : Lazy (Expr gamma (TyFun a t)) -> Expr gamma a -> Expr gamma t
  Op : (interpTy a -> interpTy b -> interpTy c)
    -> Expr gamma a
    -> Expr gamma b
    -> Expr gamma c
  If : Expr gamma TyBool
    -> Expr gamma a
    -> Expr gamma a
    -> Expr gamma a

data Env : Vect n Ty -> Type where
  Nil : Env Nil
  (::) : interpTy a -> Env gamma -> Env (a :: gamma)

lookup : HasType i gamma t -> Env gamma -> interpTy t
lookup Stop (x :: _) = x
lookup (Pop k) (_ :: xs) = lookup k xs

interp : Env gamma -> %static (e : Expr gamma t) -> interpTy t
interp env (Var i) = lookup i env
interp env (Val x) = x
interp env (Lam sc) = \x => interp (x :: env) sc
interp env (App f s) = interp env f (interp env s)
interp env (Op op x y) = op (interp env x) (interp env y)
interp env (If x t e) = if interp env x then interp env t else interp env e

eMult : Expr gamma (TyFun TyInt (TyFun TyInt TyInt))
eMult = Lam (Lam (Op (*) (Var Stop) (Var (Pop Stop))))

eFac : Expr gamma (TyFun TyInt TyInt)
eFac = Lam (If (Op (==) (Var Stop) (Val 0))
  (Val 1)
  (App (App eMult (App eFac (Op (-) (Var Stop) (Val 1)))) (Var Stop)))

-- doesn't seem to be working :(
runFac : Int -> Int
runFac x = interp [] eFac x

runMult : Int -> Int
runMult x = interp [] (App (App eMult (Val x)) (Val 3))
