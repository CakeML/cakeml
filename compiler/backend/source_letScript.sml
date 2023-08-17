(*
  This is a source-to-source transformation that lifts Let/Letrec expressions
  that sit at the top of Dlet:s into their own Dlet/Dletrec:s.
 *)

open preamble evaluateTheory astTheory ;

val _ = new_theory "source_let";

val _ = set_grammar_ancestry ["ast", "evaluate", "misc"];

Overload string_size = “list_size char_size”;

Definition dest_Let_def[simp]:
  dest_Let (Let opt x y) = SOME (opt,x,y) ∧
  dest_Let _ = NONE
End

Theorem dest_Let_SOME:
  dest_Let z = SOME (opt,x,y) ⇔ z = Let opt x y
Proof
  Cases_on ‘z’ \\ gs []
QED

Theorem dest_Let_NONE:
  dest_Let z = NONE ⇔ ∀opt x y. z ≠ Let opt x y
Proof
  Cases_on ‘z’ \\ gs []
QED

Definition dest_Letrec_def[simp]:
  dest_Letrec (Letrec funs x) = SOME (funs, x) ∧
  dest_Letrec _ = NONE
End

Theorem dest_Letrec_SOME:
  dest_Letrec z = SOME (funs,x) ⇔ z = Letrec funs x
Proof
  Cases_on ‘z’ \\ gs []
QED

Theorem dest_Letrec_NONE:
  dest_Letrec z = NONE ⇔ ∀funs x. z ≠ Letrec funs x
Proof
  Cases_on ‘z’ \\ gs []
QED

Definition lift_let_def:
  (lift_let (Dlet l p x) =
    case dest_Let x of
    | SOME (NONE,x,y) => SOME (Dlet l Pany x, Dlet l p y)
    | SOME (SOME m,x,y) => SOME (Dlet l (Pvar m) x, Dlet l p y)
    | NONE =>
        case dest_Letrec x of
        | SOME (funs,x) => SOME (Dletrec l funs, Dlet l p x)
        | NONE => NONE) ∧
  (lift_let _ = NONE)
End

Definition lift_lets_def:
  lift_lets sofar d =
    case lift_let d of
    | NONE => (REVERSE sofar, d)
    | SOME (d1, d2) => lift_lets (d1::sofar) d2
Termination
  wf_rel_tac ‘measure (dec_size o SND)’
  \\ Cases_on ‘d’ \\ rw [lift_let_def]
  \\ gvs [CaseEqs ["option", "prod"], dec_size_def, exp_size_def,
          dest_Let_SOME, dest_Letrec_SOME]
End

Definition compile_decs_def:
  (compile_decs [] = []) ∧
  (compile_decs (d::ds) =
    let (pre, d) = lift_lets [] d in
    Dlocal pre [d] :: compile_decs ds)
End

(*
val test3 = EVAL “
  compile_decs [
    Dlet l (Pvar "foo")
      (Letrec [("bar", "x", App Opapp [Var (Short "baz"); Con NONE []])]
              (Var (Short "glob")))]”;
 *)

val _ = export_theory ();

