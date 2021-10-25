(*
  Correctness proof for clos_op
*)

open preamble;
open closLangTheory closSemTheory clos_opTheory;

val _ = new_theory "clos_opProof";

val _ = set_grammar_ancestry [ "closLang", "closSem", "clos_op"];

Theorem SmartOp_thm:
  evaluate ([Op t op xs], env, s) = (res,s1) ∧ res ≠ Rerr (Rabort Rtype_error) ⇒
  evaluate ([SmartOp t op xs], env, s) = (res,s1)
Proof
  cheat
QED

Theorem SmartOp_simp:
  set_globals (SmartOp t op xs) = set_globals (Op t op xs) ∧
  esgc_free (SmartOp t op xs) = esgc_free (Op t op xs) ∧
  pure (SmartOp t op xs) = pure (Op t op xs)
Proof
  cheat
QED

Theorem SmartOp_Const:
  SmartOp t (Const i) xs = Op t (Const i) xs
Proof
  cheat
QED

Theorem SmartOp_Cons:
  SmartOp t (Cons n) xs = Op t (Cons n) xs
Proof
  cheat
QED

Theorem fv_max_SmartOp:
  fv_max n [Op t op xs] ⇒ fv_max n [SmartOp t op xs]
Proof
  cheat
QED

Theorem SmartOp_Install:
  SmartOp t Install = Op t Install
Proof
  cheat
QED

Theorem code_locs_SmartOp:
  LIST_TO_BAG (code_locs [SmartOp t op xs]) =
  LIST_TO_BAG (code_locs [Op t op xs])
Proof
  cheat
QED

Theorem every_Fn_SOME_SmartOp:
  every_Fn_SOME [SmartOp t op xs] = every_Fn_SOME [Op t op xs]
Proof
  cheat
QED

Theorem every_Fn_vs_NONE_SmartOp:
  every_Fn_vs_NONE xs ⇒ every_Fn_vs_NONE [SmartOp t op xs]
Proof
  cheat
QED

Theorem no_Labels_SmartOp:
  EVERY no_Labels xs ⇒ no_Labels (SmartOp t op xs)
Proof
  cheat
QED

Theorem obeys_max_app_SmartOp:
  EVERY (obeys_max_app k) xs ⇒ obeys_max_app k (SmartOp t op xs)
Proof
  cheat
QED

val _ = export_theory();
