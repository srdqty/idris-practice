import Data.Vect

-- %default total

data Ty = TyInt | TyFun Ty Ty | TyBool | TyFix Ty Ty

data Fixed a t = MkFixed ((a -> t) -> a -> t)

fix : ((a -> b) -> a -> b) -> a -> b
fix f x = f (fix f) x

unFixed : Fixed a t -> a -> t
unFixed (MkFixed f) = fix f

interpTy : Ty -> Type
interpTy TyInt = Int
interpTy (TyFun a t) = interpTy a -> interpTy t
interpTy TyBool = Bool
interpTy (TyFix a t) = Fixed (interpTy a) (interpTy t)

data Expr : (Vect n Ty) -> Ty -> Type where
  Var : (i : Fin n) -> Expr g (index i g)
  Val : (x : Int) -> Expr g TyInt
  Lam : Expr (a :: g) t -> Expr g (TyFun a t)
  App : Expr g (TyFun a t) -> Expr g a -> Expr g t
  Op : (interpTy a -> interpTy b -> interpTy c)
    -> Expr g a
    -> Expr g b
    -> Expr g c
  If : Expr g TyBool -> Expr g a -> Expr g a -> Expr g a
  Fix : Expr (TyFun a t :: a :: g) t -> Expr g (TyFix a t)

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
interp env (If v t e) =
  if (interp env v) then (interp env t) else (interp env e)
interp env (Fix sc) = MkFixed (\f, x => interp (Extend f (Extend x env)) sc)

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

fac : Expr g (TyFix TyInt TyInt)
fac = Fix (If (Op (==) (Val 0) x)
               (Val 1)
               (Op (*) x
                       (App f (Op (-) x (Val 1)))))
  where
    Fn : Ty
    Fn = TyFun TyInt TyInt

    f : Expr (Fn :: _) Fn
    f = Var FZ

    x : Expr (a :: TyInt :: _) TyInt
    x = Var (FS FZ)
{-
*Expr> interp Empty fact
<infinite loop>
-}

fact' : Expr g (TyFun (TyFun TyInt TyInt) (TyFun TyInt TyInt))
fact' = Lam (Lam (If (Op (==) (Val 0) x)
               (Val 1)
               (Op (*) x
                       (App f (Op (-) x (Val 1))))))
  where
    Fn : Ty
    Fn = TyFun TyInt TyInt

    f : Expr (a :: Fn :: _) Fn
    f = Var (FS (FZ))

    x : Expr (TyInt :: _) TyInt
    x = Var FZ
{-
*ExprWithFix> interp Empty fact'
\f', x' =>
  if intToBool (prim__eqInt 0 x')
    then 1
    else prim__mulInt x' (f' (prim__subInt x' 1)) : (Int -> Int) ->
                                                    Int -> Int
-}

fact'' : Int -> Int
fact'' = fix (interp Empty fact')

x : Int
x = fact'' 20

main : IO ()
main = printLn x
