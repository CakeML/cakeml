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
  ‘∀t. tcvwalk_pre s t’ suffices_by simp[] >>
  IMP_RES_THEN ho_match_mp_tac relationTheory.WF_INDUCTION_THM >>
  qx_gen_tac ‘n’ >> strip_tac >>
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
  rpt strip_tac >> drule_then (qspec_then ‘n’ assume_tac) WF_kcocwlR >>
  ‘∀wl. tcocwl_pre s n wl’ suffices_by simp[] >>
  IMP_RES_THEN ho_match_mp_tac relationTheory.WF_INDUCTION_THM >>
  simp[] >> qx_gen_tac ‘wl’ >> strip_tac >>
  simp[Once tcocwl_pre_def] >> rw[] >> simp[tcwalk_pre] >>
  drule (SRULE[FORALL_PROD]kcocwl_ensures_decrease) >>
  simp[kcocwl_code_def]
QED

val tcunify_pre_def = cv_trans_pre tcunify_thm;

Theorem tcunify_pre_thm:
  cwfs s ⇒
  (tcunify_pre s wl ⇔
     ∀s' wl'. cunify_code (s,wl) = INL (s',wl') ⇒ tcunify_pre s' wl')
Proof
  strip_tac >> simp[SimpLHS, Once tcunify_pre_def] >>
  simp[cunify_code_def, AllCaseEqs(), PULL_EXISTS] >>
  iff_tac >> rw[] >> gvs[tcwalk_pre, tcocwl_pre]
QED

Theorem tcunify_pre:
  ∀s wl. cwfs s ⇒ tcunify_pre s wl
Proof
  assume_tac WF_kcunifywlR >>
  ‘∀p. cwfs (FST p) ⇒ tcunify_pre (FST p) (SND p)’
    suffices_by simp[FORALL_PROD] >>
  IMP_RES_THEN ho_match_mp_tac relationTheory.WF_INDUCTION_THM >>
  simp[FORALL_PROD] >> rpt strip_tac >> rename [‘(s,wl)’] >>
  simp[Once tcunify_pre_thm] >> rpt strip_tac >>
  first_x_assum irule >>
  simp[kcunifywl_ensures_decrease] >>
  irule (SRULE[FORALL_PROD]kcunifywl_preserves_precond) >>
  metis_tac[]
QED

val cunify_pre_def = cv_trans_pre tcunify_correct;

Theorem cunify_pre[cv_pre]:
  cunify_pre s t1 t2 ⇔ cwfs s
Proof
  simp[EQ_IMP_THM, cunify_pre_def, tcunify_pre]
QED

(*
  t_walkstar st.subst t
  t_unify st.subst t1 t2
*)

val _ = export_theory ();
