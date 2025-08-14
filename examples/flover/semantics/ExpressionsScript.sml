(**
  Formalization of the base expression language for the flover framework
 **)
open realTheory realLib sptreeTheory
open AbbrevsTheory MachineTypeTheory
open preambleFloVer;

val _ = new_theory "Expressions";

Overload abs = “realax$abs”

(**
  expressions will use binary operators.
  Define them first
**)
Datatype:
  binop = Plus | Sub | Mult | Div
End

(**
  Next define an evaluation function for binary operators.
  Errors are added on the exprression evaluation level later
*)
Definition evalBinop_def:
  evalBinop Plus v1 v2 = v1 + v2 /\
  evalBinop Sub  v1 v2 = v1 - v2 /\
  evalBinop Mult v1 v2 = v1 * v2 /\
  evalBinop Div  v1 v2 = v1 / (v2:real)
End

(**
Expressions will use unary operators.
Define them first
**)
Datatype:
  unop = Neg | Inv | Sqrt
End

(**
Define evaluation for unary operators on reals.
Errors are added in the exprression evaluation level later
**)
Definition evalUnop_def:
  evalUnop Neg v = - v ∧
  evalUnop Inv v = inv(v:real) ∧
  evalUnop Sqrt v = sqrt v
End

(**
  Define Expressions parametric over some value type 'v.
  Will ease reasoning about different instantiations later.
**)
Datatype:
  expr = Var num
      | Const mType 'v
      | Unop unop expr
      | Binop binop expr expr
      | Fma expr expr expr
      | Downcast mType expr
End

(**
  Define evaluation of FMA (fused multiply-add) on reals
  Errors are added on the exprression evaluation level later
**)
Definition evalFma_def:
  evalFma v1 v2 v3 = evalBinop Plus (evalBinop Mult v1 v2) v3
End

Definition toREval_def:
  (toREval (Var n) = Var n) /\
  (toREval (Const m n) = Const REAL n) /\
  (toREval (Unop u e1) = Unop u (toREval e1)) /\
  (toREval (Binop b e1 e2) = Binop b (toREval e1) (toREval e2)) /\
  (toREval (Fma e1 e2 e3) = Fma (toREval e1) (toREval e2) (toREval e3)) /\
  (toREval (Downcast m e1) = toREval e1)
End

Definition toRMap_def:
  toRMap (d:num -> mType option) (n:num) : mType option =
    case d n of
      | SOME m => SOME REAL
      | NONE => NONE
End

(**
  Define the set of "used" variables of an exprression to be the set of variables
  occuring in it
**)
Definition usedVars_def:
  usedVars (e: 'a expr) :num_set =
    case e of
      | Var x => insert x () (LN)
      | Unop u e1 => usedVars e1
      | Binop b e1 e2 => union (usedVars e1) (usedVars e2)
      | Fma e1 e2 e3 => union (usedVars e1) (union (usedVars e2) (usedVars e3))
      | Downcast m e1 => usedVars e1
      | _ => LN
End

val _ = export_theory();
