(**
  Formalization of the base expression language for the flover framework
 **)
open realTheory realLib sptreeTheory
open AbbrevsTheory MachineTypeTheory
open preambleFloVer;

val _ = new_theory "Expressions";

val _ = temp_overload_on("abs",``real$abs``);
(**
  EXPRESSIONS WILL use binary operators.
  Define them first
**)
val _ = Datatype `
  binop = Plus | Sub | Mult | Div`;

(**
  Next define an evaluation function for binary operators.
  Errors are added on the exprression evaluation level later
*)
val evalBinop_def = Define `
  evalBinop Plus v1 v2 = v1 + v2 /\
  evalBinop Sub  v1 v2 = v1 - v2 /\
  evalBinop Mult v1 v2 = v1 * v2 /\
  evalBinop Div  v1 v2 = v1 / (v2:real)`;

(**
Expressions will use unary operators.
Define them first
**)
val _ = Datatype `
  unop = Neg | Inv | Sqrt`

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

(* (** *)
(*   Analogous lemma for unary exprressions *)
(* **) *)
(* val unary_unfolding = store_thm("unary_unfolding", *)
(* ``!(u:unop) (e1:(real)expr) (m:mType) E defVars (v:real). *)
(*        (eval_expr E defVars (Unop Inv e1) v m <=> *)
(*        (?(v1:real). *)
(*           eval_expr E defVars e1 v1 m /\ *)
(*           eval_expr (updEnv 1 v1 emptyEnv) (updDefVars 1 m defVars) (Unop Inv (Var 1)) v m))``, *)
(*   fs [updEnv_def, updDefVars_def, eval_expr_cases,APPLY_UPDATE_THM,PULL_EXISTS] *)
(*   \\ metis_tac []); *)

(*
  Using the parametric Expressions, define boolean Expressions for conditionals
*)
(* val _ = Datatype ` *)
(*   bexpr = Leq ('v expr) ('v expr) *)
(*        | Less ('v expr) ('v expr)` *)

(*
  Define evaluation of boolean exprressions
*)
(* val (bval_expr_rules, bval_expr_ind, bval_expr_cases) = Hol_reln ` *)
(*   (!E defVars e1 e2 v1 v2 m. *)
(*       eval_expr E defVars e1 v1 m /\ *)
(*       eval_expr E defVars e2 v2 m ==> *)
(*       bval E defVars m (Leq e1 e2) (v1 <= v2))/\ *)
(*   (!E defVars e1 e2 v1 v2 m. *)
(*       eval_expr E defVars e1 v1 m /\ *)
(*       eval_expr E defVars e2 v2 m ==> *)
(*       bval E defVars m (Less e1 e2) (v1 < v2))`; *)

(* val bval_expr_cases = *)
(*   map (GEN_ALL o SIMP_CONV (srw_ss()) [Once bval_expr_cases]) *)
(*     [``bval E defVars m (Leq e1 e2) res``, *)
(*      ``bval E defVars m (Less e1 e2) res``] *)
(*   |> LIST_CONJ |> curry save_thm "bval_expr_cases"; *)

(* (** *)
(*   Simplify arithmetic later by making > >= only abbreviations *)
(* **) *)
(* val _ = overload_on("Gr",``\(e1:('v)expr). \(e2:('v)expr). Less e2 e1``); *)
(* val _ = overload_on("Greq",``\(e1:('v)expr). \(e2:('v)expr). Leq e2 e1``); *)

val _ = export_theory();
