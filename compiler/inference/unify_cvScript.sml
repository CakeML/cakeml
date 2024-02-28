(*
  Translating unifyTheory to cv equations for use with cv_eval
*)
open preamble;
open cv_transLib unifyTheory;
open cv_stdTheory

val _ = new_theory "unify_cv";

val tcvwalk_pre_def = cv_trans_pre tcvwalk_thm;

val tcwalk_pre_def = cv_trans_pre tcwalk_def;

val tcocwl_pre_def = cv_trans_pre tcocwl_thm;

val tcunify_pre_def = cv_trans_pre tcunify_thm;

val cunify_pre_def = cv_trans_pre tcunify_correct;

Theorem cunify_pre[cv_pre]:
  cunify_pre s t1 t2 ⇔ cwfs s
Proof
  qsuff_tac ‘cwfs s ⇒ cunify_pre s t1 t2’
  >- metis_tac [cunify_pre_def]
  \\ gvs [cunify_pre_def]
  \\ cheat
QED

val _ = export_theory ();
