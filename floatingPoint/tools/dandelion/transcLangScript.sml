(**
  Define a simple "language" for describing elementary
  functions. For now we only allow combinations, i.e.
  exp (sin (cos ...) but no additional operators like +,-,*,/
**)
open realPolyTheory;
open preambleDandelion;

val _ = new_theory "transcLang";

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "option";

Datatype:
  binop = Add | Sub | Mul | Div
End

Datatype:
  unop = Neg | Inv
End

(* Log = natural logarithm *)
Datatype:
  trFun = Exp | Sin | Cos | Tan | Atn | Sqrt | Log
End

Datatype:
  transc =
    Fun trFun transc
    | Poly poly transc
    | Bop binop transc transc
    | Uop unop transc
    | Cst real
    | Var string
End

Datatype:
  approxAnn =
    FunAnn 'a trFun approxAnn
    | PolyAnn 'a poly approxAnn
    | BopAnn 'a binop approxAnn approxAnn
    | UopAnn 'a unop approxAnn
    | CstAnn 'a real
    | VarAnn 'a string
End

Definition getAnn_def:
  getAnn (FunAnn a _ _) = a ∧
  getAnn (PolyAnn a _ _) = a ∧
  getAnn (BopAnn a _ _ _) = a ∧
  getAnn (UopAnn a _ _) = a ∧
  getAnn (CstAnn a _) = a ∧
  getAnn (VarAnn a _) = a
End

Definition erase_def:
  erase (FunAnn _ f e) = Fun f (erase e) ∧
  erase (PolyAnn _ p e) = Poly p (erase e) ∧
  erase (BopAnn _ b e1 e2) = Bop b (erase e1) (erase e2) ∧
  erase (UopAnn _ u e) = Uop u (erase e) ∧
  erase (CstAnn _ r) = Cst r ∧
  erase (VarAnn _ s) = Var s
End


Definition getFun_def:
  getFun Exp = exp ∧
  getFun Sin = sin ∧
  getFun Cos = cos ∧
  getFun Tan = tan ∧
  getFun Atn = atn ∧
  getFun Sqrt = sqrt ∧
  getFun Log = ln
End

Definition appUop_def:
  appUop Neg r = - r ∧
  appUop Inv r = inv r
End

Definition appBop_def:
  appBop Add = realax$real_add ∧
  appBop Sub = $- ∧
  appBop Mul = $* ∧
  appBop Div = $/
End

Definition interp_def:
  interp (Var x) env =
    do v <- FIND (λ (y,r). y = x) env;
    return (SND v);
    od ∧
  interp (Cst c) env = SOME c ∧
  interp (Uop uop t) env =
    do
      r <- interp t env;
      assert (uop = Inv ⇒ r ≠ 0);
      return (appUop uop r)
    od ∧
  interp (Bop bop t1 t2) env =
    do
      r1 <- interp t1 env;
      r2 <- interp t2 env;
      assert (bop = Div ⇒ r2 ≠ 0);
      return (appBop bop r1 r2);
    od ∧
  interp (Fun s t) env =
    do
      r <- interp t env;
      return ((getFun s) r);
    od ∧
  interp (Poly p t) env =
    do
      r <- interp t env;
      return (evalPoly p r)
    od
End

Datatype:
  transcProg =
    Let string transc transcProg
    | Ret transc
End

Definition interpProg_def:
  interpProg (Let x e p) env =
    do
      r <- interp e env;
      interpProg p ((x, r)::env)
    od ∧
  interpProg (Ret e) env = interp e env
End

val _ = export_theory();
