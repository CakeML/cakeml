(*
    Abstract specification and soundness of distributed inference
 *)
Theory distInfer
Ancestors
  finite_map list pred_set relation
Libs
  bossLib

Datatype:
  message =
  | Produce 'id 'fact
  | Delete ('id list)
  | Import 'id 'fact
  | Validate 'fact
End

Datatype:
  state = <| procs  : 'name |-> ('id |-> 'fact) option;
             facts  : 'fact list;
             validated  : 'fact set
           |>
End

val state_component_equality = fetch "-" "state_component_equality"

Datatype:
  label = Tau | Act 'name (('id,'fact) message)
End

Inductive step:
[~produce_succeed:]
  (∀name n fact facts infer st.
     FLOOKUP st.procs name = SOME(SOME facts) ∧
     infer (FRANGE facts) fact ⇒
     step infer R st (Act name (Produce n fact))
          (st with
              <|procs := st.procs |+ (name, SOME(facts |+ (n,fact)));
                facts := fact::st.facts
               |>
              ))
[~produce_fail:]
  (∀name n fact facts infer st.
     FLOOKUP st.procs name = SOME(SOME facts) ⇒
     step infer R st (Act name (Produce n fact))
          (st with procs := st.procs |+ (name, NONE)))
[~delete:]
  (∀name ids facts infer st.
     FLOOKUP st.procs name = SOME(SOME facts) ⇒
     step infer R st (Act name (Delete ids))
          (st with procs := st.procs |+ (name, SOME(DRESTRICT facts (COMPL (set ids))))))
[~import:]
  (∀name n fact facts infer st.
     FLOOKUP st.procs name = SOME(SOME facts) ∧
     MEM fact st.facts ⇒
     step infer R st (Act name (Import n fact))
          (st with
              <|procs := st.procs |+ (name, SOME(facts |+ (n,fact)))|>
              ))
[~import_fail:]
  (∀name n fact facts infer st.
     FLOOKUP st.procs name = SOME(SOME facts) ∧
     ¬MEM fact st.facts ⇒
     step infer R st (Act name (Import n fact))
          (st with procs := st.procs |+ (name, NONE)))
[~validate:]
  (∀name fact facts infer st.
     FLOOKUP st.procs name = SOME(SOME facts) ∧
     fact ∈ FRANGE facts ⇒
     step infer R st (Act name (Validate fact))
          (st with
              <|validated := fact INSERT st.validated|>
              ))
[~validate_fail:]
  (∀name fact facts infer st.
     FLOOKUP st.procs name = SOME(SOME facts) ∧
     fact ∉ FRANGE facts ⇒
     step infer R st (Act name (Validate fact))
          (st with procs := st.procs |+ (name, NONE)))
[~spin:]
  (∀name act infer st.
     FLOOKUP st.procs name = SOME NONE ⇒
     step infer R st (Act name act) st)
[~drop:]
  (∀st facts fact facts'.
     st.facts = facts ++ fact :: facts' ⇒
     step infer R st Tau (st with facts := facts ++ facts'))
[~conjure:]
  (∀st fact.
     R fact ⇒
     step infer R st Tau (st with facts := fact::st.facts))
End

Definition reduce_def:
  reduce infer R st st' = ∃l. step infer R st l st'
End

Definition step_rel_def:
  step_rel infer oprems st ⇔
  (∀name facts.
     FLOOKUP st.procs name = SOME(SOME facts) ⇒
     FRANGE(facts) ⊆ infer oprems) ∧
  (∀fact. MEM fact st.facts ⇒ infer oprems fact) ∧
  (∀fact. fact ∈ st.validated ⇒ infer oprems fact)
End

Definition cut_elimination_def:
  cut_elimination infer ⇔
    (∀facts facts' fact fact'.
       infer facts fact ∧ infer (fact INSERT facts') fact' ⇒
       infer (facts ∪ facts') fact')
End

Definition assumption_def:
  assumption infer ⇔ (∀fact. infer {fact} fact)
End

Definition monotonic_def:
  monotonic infer ⇔
    (∀facts facts' fact.
       infer facts fact ⇒ infer (facts ∪ facts') fact)
End

Theorem cut_elim_lemma1:
  ∀oprems facts infer fact.
    FINITE facts ∧ facts ⊆ infer oprems ∧
    infer (oprems ∪ facts) fact ∧
    cut_elimination infer ∧ monotonic infer ⇒
    infer oprems fact
Proof
  ntac 3 strip_tac >> Induct_on ‘FINITE’ >>
  rw[] >> gvs[IN_DEF] >>
  first_x_assum irule >>
  gvs[monotonic_def] >>
  first_x_assum rev_dxrule >>
  strip_tac >>
  gvs[cut_elimination_def] >>
  first_x_assum $ qspecl_then [‘oprems ∪ facts’,‘oprems ∪ facts’] assume_tac >>
  gvs[] >>
  first_x_assum irule >>
  first_x_assum $ irule_at $ Pos last >>
  pop_assum mp_tac >>
  match_mp_tac EQ_IMPLIES >>
  AP_THM_TAC >> AP_TERM_TAC >>
  rw[SET_EQ_SUBSET,SUBSET_DEF]
QED

Theorem cut_elim_lemma2:
  ∀oprems facts infer fact.
    FINITE facts ∧ facts ⊆ infer oprems ∧ infer facts fact ∧
    cut_elimination infer ∧ monotonic infer ⇒
    infer oprems fact
Proof
  ntac 3 strip_tac >> Induct_on ‘FINITE’ >>
  rw[]
  >- (gvs[monotonic_def] >> res_tac >> fs[]) >>
  gvs[IN_DEF] >>
  irule cut_elim_lemma1 >>
  gvs[] >>
  first_assum $ irule_at $ Pos hd >>
  gvs[cut_elimination_def] >>
  first_assum $ rev_drule_then drule >>
  strip_tac
QED

Theorem step_rel_inv:
  ∀infer R st l st' oprems.
    step infer R st l st' ∧
    step_rel infer oprems st ∧
    cut_elimination infer ∧ monotonic infer ∧
    (∀fact. R fact ⇒ infer oprems fact)
    ⇒
    step_rel infer oprems st'
Proof
  Induct_on ‘step’ >>
  rw[step_rel_def,FLOOKUP_UPDATE,AllCaseEqs(),IN_INSERT] >>
  res_tac >> gvs[IN_DEF]
  >- (conj_tac
      >- (irule cut_elim_lemma2 >>
          simp[] >>
          first_assum $ irule_at $ Pos last >>
          simp[]) >>
      metis_tac[FRANGE_DOMSUB_SUBSET,SUBSET_TRANS])
  >- (irule cut_elim_lemma2 >>
      simp[] >>
      first_assum $ irule_at $ Pos last >>
      simp[])
  >- metis_tac[FRANGE_DRESTRICT_SUBSET,SUBSET_TRANS]
  >- metis_tac[FRANGE_DOMSUB_SUBSET,SUBSET_TRANS] >>
  gvs[SUBSET_DEF,IN_DEF]
QED

Theorem step_sound:
  (reduce infer R)꙳ st st' ∧
  (∀name facts. FLOOKUP st.procs name = SOME(SOME facts) ⇒ FRANGE facts ⊆ oprems) ∧
  set st.facts ⊆ oprems ∧
  st.validated = ∅ ∧
  fact ∈ st'.validated ∧
  monotonic infer ∧
  cut_elimination infer ∧
  assumption infer ∧
  (∀fact. R fact ⇒ infer oprems fact)
  ⇒
  infer oprems fact
Proof
  rpt strip_tac >>
  Q.SUBGOAL_THEN ‘step_rel infer oprems st’ assume_tac
  >- (gvs[step_rel_def] >> rw[] >>
      res_tac >>
      gvs[assumption_def,SUBSET_DEF,monotonic_def,IN_DEF] >>
      rpt strip_tac >>
      rename [‘_ _ fact’] >>
      qpat_x_assum ‘∀fact. infer {_} _’ $ qspec_then ‘fact’ assume_tac >>
      qpat_x_assum ‘∀fact facts' fact. _’ drule >>
      disch_then $ qspec_then ‘oprems’ mp_tac >>
      match_mp_tac EQ_IMPLIES >>
      AP_THM_TAC >> AP_TERM_TAC >>
      rw[SET_EQ_SUBSET,SUBSET_DEF,IN_DEF]) >>
  drule_at (Pat ‘_꙳’) RTC_lifts_invariants >>
  disch_then $ drule_at $ Pos last >>
  impl_tac >- metis_tac[reduce_def,step_rel_inv] >>
  simp[step_rel_def]
QED

Definition areduce_def:
  areduce ns infer R st st' ⇔
    (∃msg n. n ∈ ns ∧ step infer R st (Act n msg) st') ∨
    step infer R st Tau st'
End

Definition pres_inv_def:
  pres_inv i tr = ∀st st'. i st ∧ tr st st' ⇒ i st'
End

Theorem pres_inv_subset:
  pres_inv i tr ∧ UNCURRY tr' ⊆ UNCURRY tr ⇒
  pres_inv i tr'
Proof
  rw[pres_inv_def,SUBSET_DEF,pairTheory.FORALL_PROD] >>
  res_tac
QED

Theorem compose_inv:
  pres_inv i (areduce ns infer Rn) ∧
  pres_inv i (areduce ms infer Rm) ⇒
  pres_inv i (areduce (ns ∪ ms) infer (Rn ∪ Rm))
Proof
  rw[pres_inv_def,areduce_def] >>
  gvs[SF DNF_ss]
  >- (first_x_assum $ drule_at $ Pat ‘_ ∈ _’ >>
      disch_then irule >>
      first_x_assum $ irule_at $ Pos hd >>
      qexists ‘msg’ >>
      rpt $ PRED_ASSUM is_forall kall_tac >>
      gvs[step_cases] >>
      metis_tac[])
  >- (first_x_assum $ drule_at $ Pat ‘_ ∈ _’ >>
      disch_then irule >>
      first_x_assum $ irule_at $ Pos hd >>
      qexists ‘msg’ >>
      rpt $ PRED_ASSUM is_forall kall_tac >>
      gvs[step_cases] >>
      metis_tac[])
  >- (first_x_assum drule >>
      rename1 ‘_ ⇒ _ st'’ >>
      disch_then $ qspec_then ‘st'’ mp_tac >>
      strip_tac >>
      PRED_ASSUM is_forall kall_tac >>
      first_x_assum drule >>
      rename1 ‘_ ⇒ _ st'’ >>
      disch_then $ qspec_then ‘st'’ mp_tac >>
      strip_tac >>
      PRED_ASSUM is_forall kall_tac >>
      gvs[step_cases,SF DNF_ss,IN_DEF])
QED

Theorem areduce_frame:
  areduce ns infer R st st' ∧
  n ∉ ns ⇒
  areduce ns infer R
          (st with procs := st.procs |+ (n,facts))
          (st' with procs := st'.procs |+ (n,facts))
Proof
  rpt strip_tac >>
  reverse $ gvs[areduce_def,reduce_def]
  >- (disj2_tac >> gvs[step_cases] >>
      metis_tac[]) >>
  disj1_tac >>
  first_assum $ irule_at $ Pos hd >>
  rename1 ‘nn ∈ _’ >>
  ‘n ≠ nn’ by metis_tac[] >>
  qhdtm_x_assum ‘step’ $ strip_assume_tac o PURE_REWRITE_RULE[step_cases] >>
  gvs[FUPDATE_COMMUTES] >>
  gvs[step_cases,state_component_equality,FLOOKUP_UPDATE] >>
  metis_tac[]
QED
