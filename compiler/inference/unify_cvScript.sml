(*
  Translating unifyTheory to cv equations for use with cv_eval
*)
open preamble;
open cv_transLib unifyTheory;
open cv_stdTheory

val _ = new_theory "unify_cv";

val tcvwalk_pre_def = cv_trans_pre tcvwalk_thm;

Theorem tcvwalk_pre:
  ∀s t. cwfs s ⇒ tcvwalk_pre s t
Proof
  rpt strip_tac >> drule_then assume_tac $ SRULE[FORALL_PROD]WF_cvwalkR >>
  ‘∀p. FST p = s ⇒ (λ(s0,n). tcvwalk_pre s0 n) p’
    suffices_by simp[FORALL_PROD] >>
  IMP_RES_THEN ho_match_mp_tac relationTheory.WF_INDUCTION_THM >>
  simp[FORALL_PROD] >> qx_gen_tac ‘n’ >>
  strip_tac >>
  simp[Once tcvwalk_pre_def] >> rw[] >>
  drule (SRULE[FORALL_PROD]cvwalk_ensures_decrease) >>
  simp[cvwalk_code_def, AllCaseEqs()]
QED

val tcwalk_pre_def = cv_trans_pre tcwalk_def;

Theorem tcwalk_pre:
  cwfs s ⇒ tcwalk_pre s t
Proof
  simp[tcwalk_pre_def, tcvwalk_pre]
QED

val tcocwl_pre_def = cv_trans_pre tcocwl_thm;

Theorem tcocwl_pre:
  ∀s n wl. cwfs s ⇒ tcocwl_pre s n wl
Proof
  rpt strip_tac >> drule_then assume_tac WF_kcocwlR >>
  ‘∀t. FST t = s ⇒ (λ(s,n,wl). tcocwl_pre s n wl) t’
    suffices_by simp[FORALL_PROD] >>
  IMP_RES_THEN ho_match_mp_tac relationTheory.WF_INDUCTION_THM >>
  simp[FORALL_PROD] >> qx_genl_tac [‘n’, ‘wl’] >> strip_tac >>
  simp[Once tcocwl_pre_def] >> rw[] >> simp[tcwalk_pre] >>
  drule (SRULE[FORALL_PROD]kcocwl_ensures_decrease) >>
  simp[kcocwl_code_def]
QED

val tcunify_pre_def = cv_trans_pre tcunify_thm;

val cunify_pre_def = cv_trans_pre tcunify_correct;

Theorem cunify_pre[cv_pre]:
  cunify_pre s t1 t2 ⇔ cwfs s
Proof
  qsuff_tac ‘cwfs s ⇒ cunify_pre s t1 t2’
  >- metis_tac [cunify_pre_def]
  \\ gvs [cunify_pre_def]
  \\ simp[Once tcunify_pre_def]
  \\ rpt strip_tac
  \\ cheat
QED

val _ = export_theory ();
