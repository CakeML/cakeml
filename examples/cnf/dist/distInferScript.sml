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
  (∀id n fact facts infer st.
     FLOOKUP st.procs id = SOME(SOME facts) ∧
     infer (FRANGE facts) fact ⇒
     step infer st (Act id (Produce n fact))
          (st with
              <|procs := st.procs |+ (id, SOME(facts |+ (n,fact)));
                facts := fact::st.facts
               |>
              ))
[~produce_fail:]
  (∀id n fact facts infer st.
     FLOOKUP st.procs id = SOME(SOME facts) ⇒
     step infer st (Act id (Produce n fact))
          (st with procs := st.procs |+ (id, NONE)))
[~delete:]
  (∀id ids facts infer st.
     FLOOKUP st.procs id = SOME(SOME facts) ⇒
     step infer st (Act id (Delete ids))
          (st with procs := st.procs |+ (id, SOME(DRESTRICT facts (COMPL (set ids))))))
[~import:]
  (∀id n fact facts infer st.
     FLOOKUP st.procs id = SOME(SOME facts) ∧
     MEM fact st.facts ⇒
     step infer st (Act id (Import n fact))
          (st with
              <|procs := st.procs |+ (id, SOME(facts |+ (n,fact)))|>
              ))
[~import_fail:]
  (∀id n fact facts infer st.
     FLOOKUP st.procs id = SOME(SOME facts) ∧
     ¬MEM fact st.facts ⇒
     step infer st (Act id (Import n fact))
          (st with procs := st.procs |+ (id, NONE)))
[~validate:]
  (∀id fact facts infer st.
     FLOOKUP st.procs id = SOME(SOME facts) ∧
     fact ∈ FRANGE facts ⇒
     step infer st (Act id (Validate fact))
          (st with
              <|validated := fact INSERT st.validated|>
              ))
[~validate_fail:]
  (∀id fact facts infer st.
     FLOOKUP st.procs id = SOME(SOME facts) ∧
     fact ∉ FRANGE facts ⇒
     step infer st (Act id (Validate fact))
          (st with procs := st.procs |+ (id, NONE)))
[~spin:]
  (∀id act infer st.
     FLOOKUP st.procs id = SOME NONE ⇒
     step infer st (Act id act) st)
End

Definition reduce_def:
  reduce infer st st' = ∃l. step infer st l st'
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
  ∀infer st l st' oprems.
    step infer st l st' ∧
    step_rel infer oprems st ∧
    cut_elimination infer ∧ monotonic infer
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
  (reduce infer)꙳ st st' ∧
  (∀name facts. FLOOKUP st.procs name = SOME(SOME facts) ⇒ FRANGE facts ⊆ oprems) ∧
  set st.facts ⊆ oprems ∧
  st.validated = ∅ ∧
  fact ∈ st'.validated ∧
  monotonic infer ∧
  cut_elimination infer ∧
  assumption infer
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
