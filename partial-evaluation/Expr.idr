import Data.Vect

%default total

data Ty = TyInt | TyFun Ty Ty

interpTy : Ty -> Type
interpTy TyInt = Int
interpTy (TyFun a t) = interpTy a -> interpTy t

data Expr : (Vect n Ty) -> Ty -> Type where
  Var : (i : Fin n) -> Expr g (index i g)
  Val : (x : Int) -> Expr g TyInt
  Lam : Expr (a :: g) t -> Expr g (TyFun a t)
  App : Expr g (TyFun a t) -> Expr g a -> Expr g t
  Op : (interpTy a -> interpTy b -> interpTy c)
    -> Expr g a
    -> Expr g b
    -> Expr g c

data Env : Vect n Ty -> Type where
  Empty : Env Nil
  Extend : (res : interpTy t) -> Env g -> Env (t :: g)

envLookup : (i : Fin n) -> Env g -> interpTy (index i g)
envLookup FZ (Extend res x) = res
envLookup (FS x) (Extend res y) = envLookup x y

updateEnv : Env g -> (i : Fin n) -> interpTy t -> Env (replaceAt i t g)
updateEnv (Extend res x) FZ y = Extend y x
updateEnv (Extend res x) (FS z) y = Extend res (updateEnv x z y)

interp : Env g -> %static Expr g t -> interpTy t
interp env (Var i) = envLookup i env
interp env (Val x) = x
interp env (Lam sc) = \x => interp (Extend x env) sc
interp env (App f a) = interp env f (interp env a)
interp env (Op op l r) = op (interp env l) (interp env r)

add : Expr g (TyFun TyInt (TyFun TyInt TyInt))
add = Lam (Lam (Op (+) (Var (FS FZ)) (Var FZ)))
{-
*Expr> interp Empty add
\x, x1 => prim__addInt x x1 : Int -> Int -> Int
-}

double : Expr g (TyFun TyInt TyInt)
double = Lam (App (App add (Var FZ)) (Var FZ))
{-
*Expr> interp Empty double
\x => prim__addInt x x : Int -> Int
-}
