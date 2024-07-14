(*
  Translating unifyTheory to cv equations for use with cv_eval
*)
open preamble;
open cv_transLib unifyTheory;
open cv_stdTheory basis_cvTheory;

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

val tcwalkstar_pre_def = cv_trans_pre tcwalkstarwl_thm

Theorem tcwalkstar_p1_pre_thm:
  cwfs s ⇒ (tcwalkstar_p1_pre s its ks ⇔
              ∀v its' ks'. kcwalkstarwl_code s (F, its, ks) =
                           INL (v,its',ks') ⇒
                           (v ⇒ tcwalkstar_p2_pre s its' ks') ∧
                           (¬v ⇒ tcwalkstar_p1_pre s its' ks'))
Proof
  strip_tac >> simp[SimpLHS, Once tcwalkstar_pre_def] >>
  simp[kcwalkstarwl_code_def, AllCaseEqs(), PULL_EXISTS] >> iff_tac >> rw[] >>
  gvs[tcvwalk_pre]
QED

Theorem tcwalkstar_p2_pre_thm:
  cwfs s ⇒ (tcwalkstar_p2_pre s its ks ⇔
              ∀v its' ks'. kcwalkstarwl_code s (T, its, ks) =
                           INL (v,its',ks') ⇒
                           (v ⇒ tcwalkstar_p2_pre s its' ks') ∧
                           (¬v ⇒ tcwalkstar_p1_pre s its' ks'))
Proof
  strip_tac >> simp[SimpLHS, Once tcwalkstar_pre_def] >>
  simp[kcwalkstarwl_code_def, AllCaseEqs(), PULL_EXISTS] >> iff_tac >> rw[] >>
  gvs[tcvwalk_pre]
QED

Theorem tcwalkstar_pre:
  ∀s its ks. cwfs s ⇒
             tcwalkstar_p1_pre s its ks ∧ tcwalkstar_p2_pre s its ks
Proof
  rpt gen_tac >> strip_tac >> drule_then assume_tac WF_kcwalkstarwlR >>
  ‘∀t. (¬FST t ⇒ tcwalkstar_p1_pre s (FST (SND t)) (SND (SND t))) ∧
       (FST t ⇒ tcwalkstar_p2_pre s (FST (SND t)) (SND (SND t)))’
    suffices_by simp[FORALL_PROD] >>
  IMP_RES_THEN ho_match_mp_tac relationTheory.WF_INDUCTION_THM >>
  simp[FORALL_PROD, IMP_CONJ_THM, FORALL_AND_THM] >> rpt strip_tac
  >- (simp[Once tcwalkstar_p1_pre_thm] >> rpt strip_tac >>
      first_x_assum irule >>
      gvs[kcwalkstarwl_ensures_decrease]) >>
  simp[Once tcwalkstar_p2_pre_thm] >> rpt strip_tac >>
  first_x_assum irule >>
  gvs[kcwalkstarwl_ensures_decrease]
QED

Theorem tcwalkstar_pre_def = cv_trans_pre tcwalkstarwl_correct

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

Overload from_infer_t[local] = “from_infer_t_infer_t_infer_t”;

Theorem from_option_OPTION_MAP:
  from_option f (OPTION_MAP g x) = from_option (f o g) x
Proof
  Cases_on ‘x’ \\ gvs [cv_typeTheory.from_option_def]
QED

Triviality to_encode_infer_t_o_f[simp]:
  sp2fm (map encode_infer_t (fromAList (fmap_to_alist s))) =
  encode_infer_t o_f s
Proof
  gvs [TO_FLOOKUP,FUN_EQ_THM,lookup_map,lookup_fromAList]
  \\ gvs [finite_mapTheory.FLOOKUP_o_f]
  \\ rw [] \\ Cases_on ‘FLOOKUP s x’ \\ gvs []
QED

Theorem t_wfs_IMP_cwfs:
  t_wfs s ⇒ cwfs (fromAList (fmap_to_alist s))
Proof
  gvs [cwfs_def,t_wfs_def,rmfmapTheory.swfs_def,sptreeTheory.wf_fromAList]
QED

Theorem cv_rep_t_unify[cv_rep]:
  t_wfs s ⇒
  from_option (from_fmap from_infer_t) (t_unify s t1 t2) =
  cv_cunify (from_fmap from_infer_t s) (from_infer_t t1) (from_infer_t t2)
Proof
  strip_tac \\ imp_res_tac t_wfs_IMP_cwfs \\ gvs [from_fmap_def]
  \\ dep_rewrite.DEP_REWRITE_TAC [GSYM (fetch "-" "cv_cunify_thm")]
  \\ gvs [cunify_pre,cunify_def,t_unify_def,rmfmapTheory.sunify_def]
  \\ gvs [from_option_OPTION_MAP]
  \\ AP_THM_TAC \\ AP_TERM_TAC \\ gvs [FUN_EQ_THM,from_fmap_def]
  \\ rw [] \\ AP_TERM_TAC
  \\ dep_rewrite.DEP_REWRITE_TAC [spt_eq_thm]
  \\ gvs [wf_map,wf_fromAList,lookup_fromAList,lookup_map]
  \\ gvs [finite_mapTheory.FLOOKUP_o_f]
  \\ rw [] \\ Cases_on ‘FLOOKUP x n’ \\ gvs []
QED

Theorem cv_rep_t_walkstar[cv_rep]:
  t_wfs s ⇒
  from_infer_t (t_walkstar s t) =
  cv_cwalkstar (from_fmap from_infer_t s) (from_infer_t t)
Proof
  strip_tac \\ imp_res_tac t_wfs_IMP_cwfs \\ gvs [from_fmap_def]
  \\ dep_rewrite.DEP_REWRITE_TAC
           [GSYM (fetch "-" "cv_cwalkstar_thm")]
  \\ simp[tcwalkstar_pre_def]
  \\ rpt conj_tac
  >- (irule $ cj 1 tcwalkstar_pre >> simp[])
  >- (simp[tcwalkstar_p1_def, GSYM tcwalkstarwl_correct0,
           kcwalkstarwl_def, dfkcwalkstarl_def,
           kcwalkstarl_def] >>
      simp[cpsTheory.cwc_def]) >>
  simp[t_walkstar_cwalkstar] >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  gvs[spt_eq_thm, cwfs_def, lookup_fromAList]
QED

val _ = export_theory ();
