(*
  Formalization of HWMCC certificates
*)
Theory aig_cert
Ancestors
  aig
Libs
  preamble

(* Soundness ******************************************************************)

Theorem set_QSORT[local,simp]:
  ∀R ls. set (QSORT R ls) = set ls
Proof
  metis_tac [QSORT_PERM, PERM_LIST_TO_SET]
QED

(* NOTE We use R{L} and F{L} on the left-hand side of implications
   instead of R{K} and F{K}, allowing us to prove soundness a bit easier. *)

Definition is_witness_reset_def:
  is_witness_reset
    mcirc mreset mnext mpreds mcnstrs mlatches
    wcirc wreset wnext wpreds wcnstrs wlatches
  ⇔
  ∀ss.
    (is_reset ss mcirc mreset mlatches ∧
     preds_hold ss mcirc mcnstrs
     ⇒
     is_reset ss wcirc wreset (mlatches ∩ wlatches) ∧
     preds_hold ss wcirc wcnstrs)
End

Definition is_witness_transition_def:
  is_witness_transition
    mcirc mreset mnext mpreds mcnstrs mlatches
    wcirc wreset wnext wpreds wcnstrs wlatches
  ⇔
  ∀ss₀ ss₁.
    (is_next ss₀ mcirc mnext mlatches (SND ss₁) ∧
     preds_hold ss₀ mcirc mcnstrs ∧
     preds_hold ss₁ mcirc mcnstrs ∧
     preds_hold ss₀ wcirc wcnstrs)
    ⇒
    (is_next ss₀ wcirc wnext (mlatches ∩ wlatches) (SND ss₁) ∧
     preds_hold ss₁ wcirc wcnstrs)
End

Definition is_witness_property_def:
  is_witness_property
    mcirc mreset mnext mpreds mcnstrs mlatches
    wcirc wreset wnext wpreds wcnstrs wlatches
  ⇔
  ∀ss.
    (preds_hold ss mcirc mcnstrs ∧
     preds_hold ss wcirc wcnstrs) ⇒
    preds_hold ss wcirc wpreds ⇒
    preds_hold ss mcirc mpreds
End

Definition is_witness_base_def:
  is_witness_base
    wcirc wreset wnext wpreds wcnstrs wlatches
  ⇔
    ∀ss.
      (is_reset ss wcirc wreset wlatches ∧
       preds_hold ss wcirc wcnstrs)
      ⇒
      preds_hold ss wcirc wpreds
End

Definition is_witness_step_def:
  is_witness_step
    wcirc wreset wnext wpreds wcnstrs wlatches
  ⇔
    ∀ss₀ ss₁.
      (preds_hold ss₀ wcirc wpreds ∧
       is_next ss₀ wcirc wnext wlatches (SND ss₁) ∧
       preds_hold ss₀ wcirc wcnstrs ∧
       preds_hold ss₁ wcirc wcnstrs)
      ⇒
      preds_hold ss₁ wcirc wpreds
End


Definition is_witness_liveness_def:
  is_witness_liveness
    mcirc mreset mnext mpreds mcnstrs mqcirc mlive mlatches
    wcirc wreset wnext wpreds wcnstrs wqcirc wlive wlatches
  ⇔
    (* This LENGTH property is not strictly necessary but makes the proof a bit
       neater *)
    LIST_REL (λms ws. LENGTH ms = LENGTH ws) mlive wlive ∧
    ∀ss₀ ss₁.
      (preds_hold ss₀ mcirc mcnstrs ∧
       preds_hold ss₀ wcirc wcnstrs ∧
       preds_hold ss₀ wcirc wpreds ∧
       preds_hold ss₁ mcirc mcnstrs ∧
       preds_hold ss₁ wcirc wcnstrs ∧
       preds_hold ss₁ wcirc wpreds ∧
       is_next ss₀ wcirc wnext wlatches (SND ss₁))
      ⇒
      lives_imply (pair_state ss₀ ss₁) (pair_state ss₀ ss₁) wqcirc mqcirc
        wlive mlive
End


Definition is_witness_decrease_def:
  is_witness_decrease
    wcirc wreset wnext wpreds wcnstrs wqcirc wlive wlatches
  ⇔
    ∀ss₀ ss₁.
      (preds_hold ss₀ wcirc wcnstrs ∧
       preds_hold ss₀ wcirc wpreds ∧
       preds_hold ss₁ wcirc wcnstrs ∧
       preds_hold ss₁ wcirc wpreds ∧
       is_next ss₀ wcirc wnext wlatches (SND ss₁))
       ⇒
       lives_hold (pair_state ss₁ ss₀) wqcirc wlive
End

Definition is_witness_closure_def:
  is_witness_closure
    wcirc wreset wnext wpreds wcnstrs wqcirc wlive wlatches
  ⇔
    ∀ss₀ ss₁ ss₂.
      (preds_hold ss₀ wcirc wcnstrs ∧
       preds_hold ss₀ wcirc wpreds ∧
       preds_hold ss₁ wcirc wcnstrs ∧
       preds_hold ss₁ wcirc wpreds ∧
       preds_hold ss₂ wcirc wcnstrs ∧
       preds_hold ss₂ wcirc wpreds ∧
       is_next ss₀ wcirc wnext wlatches (SND ss₁) ∧
       lives_hold (pair_state ss₀ ss₂) wqcirc wlive)
      ⇒
      lives_hold (pair_state ss₁ ss₂) wqcirc wlive
End

Definition is_witness_consistent_def:
  is_witness_consistent
    wcirc wreset wnext wpreds wcnstrs wqcirc wlive wlatches
  ⇔
    ∀ss₀ ss₁ ss₂.
      (preds_hold ss₀ wcirc wcnstrs ∧
       preds_hold ss₀ wcirc wpreds ∧
       preds_hold ss₁ wcirc wcnstrs ∧
       preds_hold ss₁ wcirc wpreds ∧
       preds_hold ss₂ wcirc wcnstrs ∧
       preds_hold ss₂ wcirc wpreds ∧
       is_next ss₀ wcirc wnext wlatches (SND ss₁) ∧
       is_next ss₁ wcirc wnext wlatches (SND ss₂) ∧
       lives_hold (pair_state ss₀ ss₁) wqcirc wlive ∧
       lives_hold (pair_state ss₁ ss₂) wqcirc wlive)
       ⇒
       lives_imply (pair_state ss₀ ss₁) (pair_state ss₁ ss₂) wqcirc wqcirc
         wlive wlive
End

Definition is_witness_def:
  is_witness
    mcirc mreset mnext mpreds mcnstrs mqcirc mlive mlatches
    wcirc wreset wnext wpreds wcnstrs wqcirc wlive wlatches
  ⇔
  is_witness_reset
    mcirc mreset mnext mpreds mcnstrs mlatches
    wcirc wreset wnext wpreds wcnstrs wlatches
  ∧
  is_witness_transition
    mcirc mreset mnext mpreds mcnstrs mlatches
    wcirc wreset wnext wpreds wcnstrs wlatches
  ∧
  is_witness_property
    mcirc mreset mnext mpreds mcnstrs mlatches
    wcirc wreset wnext wpreds wcnstrs wlatches
  ∧
  is_witness_base
    wcirc wreset wnext wpreds wcnstrs wlatches
  ∧
  is_witness_step
    wcirc wreset wnext wpreds wcnstrs wlatches
  ∧
  is_witness_liveness
    mcirc mreset mnext mpreds mcnstrs mqcirc mlive mlatches
    wcirc wreset wnext wpreds wcnstrs wqcirc wlive wlatches
  ∧
  is_witness_decrease
    wcirc wreset wnext wpreds wcnstrs wqcirc wlive wlatches
  ∧
  is_witness_closure
    wcirc wreset wnext wpreds wcnstrs wqcirc wlive wlatches
  ∧
  is_witness_consistent
    wcirc wreset wnext wpreds wcnstrs wqcirc wlive wlatches
End


(* Extends a trace for the model to a trace for the witness.
   This setup allows us to formulate the conclusion of
   extend_model_trace_to_witness as ∃tr'. ∀n. ... allowing us to use the lemma
   for both finite and infinite traces. *)
Definition mk_trace_def:
  (mk_trace lt mlatches wcirc wreset wnext wpreds wcnstrs wlatches tr 0 =
   let
     xs = QSORT lt (SET_TO_LIST (wlatches DIFF (mlatches ∩ wlatches)));
     (is, ls) = tr 0
   in
     (is, patch wcirc wreset is ls xs)) ∧
  (mk_trace lt mlatches wcirc wreset wnext wpreds wcnstrs wlatches tr (SUC n) =
   let
     prev = mk_trace lt mlatches wcirc wreset wnext wpreds wcnstrs wlatches tr n
   in
     @succ.
       is_next prev wcirc wnext wlatches (SND succ) ∧
       preds_hold succ wcirc wcnstrs ∧
       agree_on UNIV mlatches succ (tr (SUC n)))
End

Definition dep_model_def:
  dep_model
    circ reset next preds cnstrs inputs latches ⇔
  dep_circuit inputs latches circ ∧
  dep_reset inputs latches reset latches ∧
  dep_latch_lit inputs latches next latches ∧
  dep_lits inputs latches preds ∧
  dep_lits inputs latches cnstrs
End

Definition is_stratified_full_def:
  is_stratified_full lt circ reset latches ⇔
  FINITE latches ∧
  irreflexive lt ∧
  transitive lt ∧
  total lt ∧   (* for QSORT_SORTED *)
  is_stratified lt circ reset latches
End

Theorem agree_on_weaken_inputs[local]:
  agree_on inputs latches ss' ss ∧
  inputs' ⊆ inputs
  ⇒
  agree_on inputs' latches ss' ss
Proof
  metis_tac [SUBSET_DEF, agree_on_weaken]
QED

Theorem traces_agree_weaken_inputs[local]:
  traces_agree n inputs latches tr' tr ∧
  inputs' ⊆ inputs
  ⇒
  traces_agree n inputs' latches tr' tr
Proof
  metis_tac [traces_agree_def, agree_on_weaken_inputs]
QED

Theorem extend_model_trace_to_witness:
  is_witness_reset
    mcirc mreset mnext mpreds mcnstrs mlatches
    wcirc wreset wnext wpreds wcnstrs wlatches ∧
  is_witness_transition
    mcirc mreset mnext mpreds mcnstrs mlatches
    wcirc wreset wnext wpreds wcnstrs wlatches ∧
  dep_model mcirc mreset mnext mpreds mcnstrs minputs mlatches ∧
  is_stratified_full lt wcirc wreset wlatches
  ⇒
  ∃tr'. ∀n.
    is_trace mcirc mreset mnext mcnstrs mlatches tr n ⇒
    is_trace wcirc wreset wnext wcnstrs wlatches tr' n ∧
    traces_agree n UNIV mlatches tr' tr
Proof
  rw [dep_model_def, is_stratified_full_def]
  >> qexists ‘mk_trace lt mlatches wcirc wreset wnext wpreds wcnstrs wlatches tr’
  >> Induct_on ‘n’ >> strip_tac
  >-
   (fs [is_trace_def, is_witness_reset_def, traces_agree_def]
    >> first_assum $ drule_all_then assume_tac
    >> namedCases_on ‘tr 0’ ["is ls"] >> fs []
    >> gvs [mk_trace_def]
    >> qmatch_goalsub_abbrev_tac ‘patch _ _ _ _ xs’
    >> qmatch_goalsub_abbrev_tac ‘is_reset ss0’
    >> CONJ_TAC
      (* wlatches are in reset and wcnstrs
        are satisfied in patched state *)
    >- (
      first_x_assum (qspec_then ‘ss0’ mp_tac)
      >> impl_tac
      >- (
        CONJ_TAC
        >- (
          drule_then irule is_reset_dep_latch_lit>>
          last_assum $ irule_at (Pos hd)>>
          simp[Abbr`ss0`, agree_on_def]>>
          rw[]>>
          irule (GSYM not_mem_patch_eq)>>
          simp[Abbr`xs`])
        >>
          drule_then irule preds_hold_dep_circuit>>
          last_assum $ irule_at (Pos hd)>>
          simp[Abbr`ss0`, agree_on_def]>>
          rw[]>>
          irule (GSYM not_mem_patch_eq)>>
          simp[Abbr`xs`])
      >> rw[]
      >> ‘wlatches = (mlatches ∩ wlatches) ∪ (set xs)’ by
          (simp [Abbr ‘xs’, Req0 SET_TO_LIST_INV] >> SET_TAC [])
      >> pop_assum SUBST1_TAC
      >> simp [is_reset_union,Abbr`ss0`]
      >> irule subset_is_reset_patch
      >> first_assum $ irule_at (Pos last)  (* is_stratified *)
      >> simp [Abbr ‘xs’, Req0 SET_TO_LIST_INV, Req0 QSORT_SORTED])
    >> simp [traces_agree_def, agree_on_def, Abbr`ss0`]
    >-
     (rw []
      >> rename1 ‘patch _ _ _ _ _ l’ >> ‘¬MEM l xs’ by simp [Abbr ‘xs’]
      >> simp [not_mem_patch_eq]))
  >> gvs [is_trace_SUC, traces_agree_SUC]
  >> simp [GSYM ADD1, mk_trace_def]
  >> qmatch_goalsub_abbrev_tac ‘is_next tr'n’
  >> SELECT_ELIM_TAC
  >> conj_tac
  >-
   (qabbrev_tac ‘step =
                 (FST (tr (n + 1)),
                  λl. if l ∈ mlatches then (SND (tr (n + 1))) l
                      else eval_lit (tr'n) wcirc (wnext l))’
    >> qexists ‘step’
    >> ‘is_next (tr'n) mcirc mnext mlatches (SND step)’ by
      (drule is_next_dep_circuit
       >> disch_then irule
       >> qpat_x_assum ‘dep_circuit _ _ _’ $ irule_at Any
       >> gvs [traces_agree_def, agree_on_sym, Abbr ‘step’, Abbr‘tr'n’]
       >> irule agree_on_weaken_inputs
       >> first_assum $ irule_at (Pos last) >> simp [])
    >> ‘preds_hold (tr'n) mcirc mcnstrs’ by
      (‘preds_hold (tr n) mcirc mcnstrs’ by metis_tac [is_trace_preds_hold_n]
       >> drule preds_hold_dep_circuit
       >> disch_then drule >> disch_then irule
       >> gvs [traces_agree_def, agree_on_sym, Abbr‘tr'n’]
       >> irule agree_on_weaken_inputs
       >> first_assum $ irule_at (Pos last) >> simp [])
    >> ‘preds_hold step mcirc mcnstrs’ by
      (rev_drule preds_hold_dep_circuit
       >> disch_then drule >> disch_then irule
       >> Cases_on ‘tr (n + 1)’
       >> gvs [agree_on_def, Abbr ‘step’])
    >> ‘preds_hold (tr'n) wcirc wcnstrs’ by metis_tac [is_trace_preds_hold_n]
    (* Following the paper proof, we can now invoke the transition check
       and extend these two facts to the witness. *)
    >> fs [is_witness_transition_def]
    >> first_x_assum $ drule_all_then assume_tac >> fs []
    >> conj_tac
    >- (fs [is_next_def] >> rw [] >> Cases_on ‘l ∈ mlatches’ >> gvs [Abbr ‘step’])
    >> gvs [ADD1]
    >> Cases_on ‘tr (n + 1)’
    >> fs [agree_on_def, Abbr ‘step’])
  >> rw []
QED

Theorem is_witness_base_step_safe:
  is_trace circ reset next cnstrs latches tr n ∧
  is_witness_base
    circ reset next preds cnstrs latches ∧
  is_witness_step
    circ reset next preds cnstrs latches
  ⇒
  preds_hold (tr n) circ preds
Proof
  Induct_on`n`>>rw[]
  >-
    gvs[is_witness_base_def,is_trace_def]>>
  gvs[is_trace_SUC] >>
  gvs[is_witness_step_def,ADD1]>>
  first_x_assum irule>>
  rw[]>>
  first_x_assum (irule_at (Pos last))>>
  simp[]>>
  metis_tac[is_trace_preds_hold_n]
QED

Theorem is_inf_trace_is_witness_base_step_safe:
  is_inf_trace circ reset next cnstrs latches tr ∧
  is_witness_base
    circ reset next preds cnstrs latches ∧
  is_witness_step
    circ reset next preds cnstrs latches
  ⇒
  (∀n. preds_hold (tr n) circ preds)
Proof
  rw [is_inf_trace_eq] >> metis_tac [is_witness_base_step_safe]
QED

Theorem is_witness_is_safe:
  is_witness
    mcirc mreset mnext mpreds mcnstrs mqcirc mlive mlatches
    wcirc wreset wnext wpreds wcnstrs wqcirc wlive wlatches ∧
  dep_model
    mcirc mreset mnext mpreds mcnstrs minputs mlatches ∧
  is_stratified_full lt wcirc wreset wlatches
  ⇒
  is_safe
    mcirc mreset mnext mcnstrs mlatches mpreds
Proof
  rw [is_witness_def, is_safe_def]
  >> CCONTR_TAC
  >> fs [is_unsafe_def]
  >> pop_assum mp_tac >> simp[]
  >> rename1 ‘preds_hold (tr _)’
  >> drule_all extend_model_trace_to_witness
  >> disch_then $ qspec_then ‘tr’ mp_tac >> rw []
  >> first_assum drule >> strip_tac
  >> drule_all is_witness_base_step_safe
  >> strip_tac
  >> fs [dep_model_def]
  >> `is_trace mcirc mreset mnext mcnstrs mlatches tr' n` by
    (irule is_trace_dep_circuit >> fs []
     >> first_assum $ irule_at (Pos hd) >> simp []
     >> irule_at (Pos hd) traces_agree_weaken_inputs
     >> first_assum $ irule_at (Pos hd)
     >> simp [])
  >> drule_at_then Any irule preds_hold_dep_circuit
  >> rename1`traces_agree n _ mlatches tr' tr`
  >> fs[traces_agree_def]
  >> qexists_tac`tr' n`
  >> conj_tac
  >-
   (gvs[is_witness_property_def]
    >> first_x_assum irule
    >> gvs[]
    >> metis_tac[is_trace_preds_hold_n])
  >> irule agree_on_weaken_inputs
  >> first_assum $ irule_at (Pos last)
  >> simp []
QED

Theorem is_witness_closure_lives_hold[local]:
  ∀k.
    is_witness_closure
      circ reset next preds cnstrs qcirc live latches ∧
    lives_hold (pair_state (tr i) (tr j)) qcirc live ∧
    (∀n. preds_hold (tr n) circ preds) ∧
    (∀n. preds_hold (tr n) circ cnstrs) ∧
    (∀n. is_next (tr n) circ next latches (SND (tr (n + 1))))
    ⇒
    lives_hold (pair_state (tr (i + k)) (tr j)) qcirc live
Proof
  Induct >> rw [] >> fs []
  >> fs [is_witness_closure_def]
  >> first_assum irule >> simp []
  >> qexists ‘tr (i + k)’ >> fs [ADD1]
  >> rewrite_tac [ADD_ASSOC] >> simp[ADD_ASSOC]
  >> first_x_assum $ qspec_then ‘i + k’ mp_tac >> simp []
QED

Theorem matching_transition_live:
  is_witness_decrease
    circ reset next preds cnstrs qcirc live latches  ∧
  is_inf_trace circ reset next cnstrs latches tr ∧
  is_witness_closure
    circ reset next preds cnstrs qcirc live latches ∧
  matching_transition inputs' latches' tr i j ∧
  set (circuit_inputs circ) ⊆ inputs' ∧
  BIGUNION (IMAGE (set o lit_inputs o next) latches) ⊆ inputs' ∧
  set (circuit_inputs qcirc) ⊆ pair_set inputs' ∧
  BIGUNION (IMAGE (set o lit_inputs) (set (FLAT live))) ⊆ pair_set inputs' ∧
  latches ⊆ latches' ∧
  set (circuit_latches circ) ⊆ latches' ∧
  BIGUNION (IMAGE (set o lit_latches o next) latches) ⊆ latches' ∧
  set (circuit_latches qcirc) ⊆ pair_set latches' ∧
  BIGUNION (IMAGE (set o lit_latches) (set (FLAT live))) ⊆ pair_set latches' ∧
  (∀n. preds_hold (tr n) circ preds)
  ⇒
  lives_hold (pair_state (tr i) (tr (i + 1))) qcirc live
Proof
  rw []
  >> drule_then assume_tac is_inf_trace_cnstrs_hold
  >> Cases_on ‘j = i + 1’ >> gvs []
  >- (
    fs [matching_transition_def, is_witness_decrease_def]
    >> last_assum irule >> gvs [is_inf_trace_def]
    >> last_x_assum $ qspec_then ‘i’ assume_tac
    >> irule is_next_dep_circuit
    >> first_assum $ irule_at (Pos last)
    >> fs [agree_on_sym]
    >> first_assum $ irule_at (Pos (el 4)) >> simp []
    >> CONJ_TAC >-
      (Cases_on ‘tr i’ >> Cases_on ‘tr (i + 1)’
      >> fs [agree_on_def]
      >> metis_tac[])
    >> CONJ_TAC >- (
      irule dep_circuit_subset>>
      metis_tac[dep_circuit_inputs_latches])
    >>
      irule dep_latch_lit_next>>
      fs[])
  >> drule_then assume_tac is_inf_trace_is_next
  >> ‘lives_hold (pair_state (tr (i + 2)) (tr (i + 1))) qcirc live’ by
    (fs [is_witness_decrease_def]
     >> last_assum irule >> simp []
     >> first_x_assum $ qspec_then ‘i + 1’ mp_tac >> simp [])
  >> Cases_on ‘j = i + 2’ >> gvs []
  >-
   (irule lives_hold_matching_transition >> simp []
    >> qpat_x_assum ‘matching_transition _ _ _ _ _’ $ irule_at Any
    >> simp []
    >> CONJ_TAC >- (
      irule dep_circuit_subset>>
      metis_tac[dep_circuit_inputs_latches])
    >>
      metis_tac[dep_lits_lits])
  >> drule_all is_witness_closure_lives_hold
  >> disch_then $ qspec_then ‘j - i - 2’ assume_tac
  >> gvs [matching_transition_def]
  >> irule lives_hold_dep_circuit
  >> pop_assum (irule_at Any)
  >> qexists_tac`pair_set latches'`
  >> qexists_tac`pair_set inputs'`
  >> simp [agree_on_pair]
  >> CONJ_TAC >- (
    irule dep_circuit_subset>>
    metis_tac[dep_circuit_inputs_latches])
  >>
    metis_tac[dep_lits_lits]
QED

Theorem is_witness_consistent_preds_holds:
  is_witness_consistent wcirc wreset wnext wpreds wcnstrs wqcirc wlive
    wlatches ∧
  MEM q Q ∧ MEM Q wlive ∧
  preds_hold (pair_state (tr j) (tr (j + 1))) wqcirc {q} ∧
  (∀n. preds_hold (tr n) wcirc wcnstrs) ∧
  (∀n. preds_hold (tr n) wcirc wpreds) ∧
  (∀n. is_next (tr n) wcirc wnext wlatches (SND (tr (n + 1)))) ∧
  (∀i. j ≤ i ⇒
       lives_hold (pair_state (tr i) (tr (i + 1))) wqcirc wlive) ∧
  j ≤ i
  ⇒
  preds_hold (pair_state (tr i) (tr (i + 1))) wqcirc {q}
Proof
  Induct_on ‘i - j’ >> rw [] >> fs []
  >- (‘i = j’ by simp [] >> simp [])
  >> last_x_assum $ qspecl_then [‘i - 1’, ‘j’] assume_tac
  >> gvs []
  >> gvs [is_witness_consistent_def, MEM_EL]
  >> last_x_assum $ qspecl_then [‘tr (i - 1)’, ‘tr i’, ‘tr (i + 1)’] mp_tac
  >> simp []
  >> impl_tac >-
   (‘i - 1n + 1 = i’ by simp []
    >> ‘j ≤ i - 1’ by simp []
    >> metis_tac [])
  >> simp [lives_imply_def, signal_imply_def, LIST_REL_EL_EQN]
QED

Theorem is_witness_is_live:
  is_witness
    mcirc mreset mnext mpreds mcnstrs mqcirc mlive mlatches
    wcirc wreset wnext wpreds wcnstrs wqcirc wlive wlatches ∧
  dep_model
    mcirc mreset mnext mpreds mcnstrs minput mlatches ∧
  dep_qcirc minput mqcirc mlive mlatches ∧
  is_stratified_full lt wcirc wreset wlatches
  ⇒
  is_live
    mcirc mreset mnext mcnstrs mqcirc mlive mlatches
Proof
  rw []
  (* Get safety of model *)
  >> drule_all_then assume_tac is_witness_is_safe
  (* Extend trace on model to trace on witness *)
  >> fs [is_witness_def]
  >> rw [is_live_def]
  >> drule_all extend_model_trace_to_witness
  >> rename1 ‘is_inf_trace _ _ _ _ _ tr’
  >> disch_then $ qspec_then ‘tr’ mp_tac >> strip_tac
  >> dxrule is_inf_trace_traces_agree
  >> simp [] >> strip_tac
  (* Witness constraints and predicates hold on extended trace *)
  >> ‘∀n. preds_hold (tr' n) wcirc wpreds’ by
    metis_tac [is_inf_trace_is_witness_base_step_safe]
  >> ‘∀n. preds_hold (tr' n) wcirc wcnstrs’ by
    metis_tac [is_inf_trace_cnstrs_hold]
  (* Extended trace has valid steps for the witness *)
  >> ‘∀n. is_next (tr' n) wcirc wnext wlatches (SND (tr' (n + 1)))’ by
     metis_tac [is_inf_trace_is_next]
  (* Extended trace is also a trace for the model *)
  >> ‘is_inf_trace mcirc mreset mnext mcnstrs mlatches tr'’ by
    (irule is_inf_trace_dep_circuit
     >> first_assum $ irule_at (Pos last)
     >> fs [dep_model_def]
     >> first_assum $ irule_at (Pos last)
     >> rw []
     >> irule traces_agree_weaken_inputs
     >> qexists ‘UNIV’ >> simp [])
  (* Model constraints holds on the witness *)
  >> ‘∀n. preds_hold (tr' n) mcirc mcnstrs’ by
    metis_tac [is_inf_trace_cnstrs_hold]
  >> qabbrev_tac`inputs' =
    set (circuit_inputs wcirc) ∪
    BIGUNION (IMAGE (set o lit_inputs o wnext) wlatches) ∪
    (IMAGE OUTL (set (circuit_inputs wqcirc)) ∪
    IMAGE OUTR (set (circuit_inputs wqcirc))) ∪
    (IMAGE OUTL (BIGUNION (IMAGE (set o lit_inputs) (set (FLAT wlive)))) ∪
    IMAGE OUTR (BIGUNION (IMAGE (set o lit_inputs) (set (FLAT wlive)))))`
  >> qabbrev_tac`latches' =
    wlatches ∪
    set (circuit_latches wcirc) ∪
    BIGUNION (IMAGE (set o lit_latches o wnext) wlatches) ∪
    (IMAGE OUTL (set (circuit_latches wqcirc)) ∪
    IMAGE OUTR (set (circuit_latches wqcirc))) ∪
    (IMAGE OUTL (BIGUNION (IMAGE (set o lit_latches) (set (FLAT wlive)))) ∪
    IMAGE OUTR (BIGUNION (IMAGE (set o lit_latches) (set (FLAT wlive)))))`
  (* Infinite trace on witness repeats from k onwards *)
  >> qspecl_then [‘inputs'’, ‘latches'’, ‘tr'’] mp_tac matching_transition_exists
  >> impl_tac >-
    (unabbrev_all_tac>>fs[is_stratified_full_def,PULL_EXISTS])
  >> strip_tac
  >> rename1 ‘k < _ ⇒ _’ >> qexists ‘k+1’ >> rw []
  (* Model is live if model is live on extended trace *)
  >> ‘∃signal.
        MEM signal prop ∧
        ∀i. k + 1 ≤ i ⇒
            preds_hold (pair_state (tr' i) (tr' (i + 1))) mqcirc {signal}’ suffices_by
    (rw []
     >> qexists ‘signal’ >> rw []
     >> irule preds_hold_dep_circuit
     >> fs [dep_qcirc_def]
     >> first_assum $ irule_at (Pos hd)
     >> simp []
     >> qexists ‘pair_state (tr' i) (tr' (i + 1))’
     >> reverse conj_tac
     >-
      (fs [traces_agree_def, agree_on_pair]
       >> irule_at (Pos hd) agree_on_weaken_inputs
       >> qexists ‘UNIV’ >> simp []
       >> first_assum $ irule_at (Pos hd)
       >> qexists ‘i’ >> simp []
       >> irule agree_on_weaken_inputs
       >> qexists ‘UNIV’ >> simp []
       >> first_assum $ irule_at (Pos hd)
       >> qexists ‘i+1’ >> simp [])
     >> fs [dep_lits_def, MEM_FLAT]
     >> metis_tac [])
  >> gvs [MEM_EL, PULL_EXISTS]
  >> ‘LENGTH wlive = LENGTH mlive ∧
      ∀n. n < LENGTH wlive ⇒ LENGTH wlive❲n❳ = LENGTH mlive❲n❳’ by
    (fs [is_witness_liveness_def, LIST_REL_EL_EQN])
  >> ‘∃n'.
        n' < LENGTH wlive❲n❳ ∧
        ∀i. k + 1 ≤ i ⇒
              preds_hold (pair_state (tr' i) (tr' (i + 1))) wqcirc {wlive❲n❳❲n'❳}’
    suffices_by
    (rw []
     >> qexists ‘n'’
     >> gvs []
     >> rw []
     >> gvs [is_witness_liveness_def, lives_imply_def, signal_imply_def,
             LIST_REL_EL_EQN, PULL_FORALL])
  (* Witness is live *)
  >> ‘∀i. k + 1 ≤ i ⇒ lives_hold (pair_state (tr' i) (tr' (i + 1))) wqcirc wlive’
    by
    (rw []
     >> drule matching_transition_live >> simp []
     >> disch_then irule >> simp []
     >> qpat_x_assum ‘∀_. _ ⇒ ∃_. matching_transition _ _ _ _ _’ $
          qspec_then `i` mp_tac
     >> rw []
     >> pop_assum (irule_at Any)
     >> unabbrev_all_tac
     >> irule_at Any SUBSET_pair_set
     >> irule_at Any SUBSET_pair_set
     >> irule_at Any SUBSET_pair_set
     >> irule_at Any SUBSET_pair_set
     >> metis_tac[SUBSET_UNION,UNION_ASSOC,UNION_COMM])
  >> drule is_witness_consistent_preds_holds
  >> disch_then $ drule_at Any >> simp []
  >> gvs [lives_hold_def, EVERY_EL, PULL_FORALL]
  >> first_x_assum $ qspecl_then [‘k + 1’, ‘n’] mp_tac
  >> pure_rewrite_tac [some_signal_holds_def] >> rw [EXISTS_MEM, MEM_EL]
  >> simp [GSYM PULL_FORALL]
  >> first_assum $ irule_at (Pos hd)
  >> rw []
  >> first_assum irule
  >> simp [PULL_EXISTS]
  >> metis_tac []
QED

(* Implementation *************************************************************)

(* todo maybe some of this should be moved to aig? *)

Definition ileft_lit_def:
  ileft_lit = iext_lit ∘ left_name_lit
End

Definition iright_lit_def:
  iright_lit = iext_lit ∘ right_name_lit
End

Definition ileft_reset_def:
  ileft_reset mreset =
  λl. OPTION_MAP ileft_lit (mreset l)
End

Definition iright_reset_def:
  iright_reset wreset =
  λl. OPTION_MAP iright_lit (wreset l)
End

Definition ileft_lits_def:
  ileft_lits = MAP ileft_lit
End

Definition iright_lits_def:
  iright_lits = MAP iright_lit
End

Definition imerge_circuits_def:
  imerge_circuits mcirc wcirc = iext_circuit (merge_circuits mcirc wcirc)
End

Definition encode_is_witness_reset_def:
  encode_is_witness_reset
    (mcirc: ('a, 'i, 'l) circuit)
    (mreset: 'l -> ('a, 'i, 'l) lit option)
    (mcnstrs: ('a, 'i, 'l) lit list)
    (mlatches: 'l list)
    (wcirc: ('b, 'i, 'l) circuit)
    (wreset: 'l -> ('b, 'i, 'l) lit option)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wlatches: 'l list)
  =
  let
    circ = imerge_circuits mcirc wcirc;
    circ = encode_is_reset circ «mreset» (ileft_reset mreset) mlatches;
    circ = encode_preds_hold circ «mcnstrs» (ileft_lits mcnstrs);
    klatches = list_inter mlatches wlatches;
    circ = encode_is_reset circ «wreset» (iright_reset wreset) klatches;
    circ = encode_preds_hold circ «wcnstrs» (iright_lits wcnstrs);
    lhss = [(Name (INL (Ext «mreset»)), F); (Name (INL (Ext «mcnstrs»)), F)];
    rhss = [(Name (INL (Ext «wreset»)), F); (Name (INL (Ext «wcnstrs»)), F)];
  in
    encode_imply circ «reset» lhss rhss
End

Theorem is_reset_ileft:
  is_reset ss (imerge_circuits lcirc rcirc) (ileft_reset lreset) llatches ⇔
    is_reset ss lcirc lreset llatches
Proof
  cheat
QED

Theorem preds_hold_ileft:
  preds_hold ss (imerge_circuits lcirc rcirc) (set (ileft_lits preds)) ⇔
    preds_hold ss lcirc (set preds)
Proof
  cheat
QED

Theorem eval_lit_INL_iright[simp]:
  eval_lit ss ((INL (Ext name),lits)::circ) (iright_lit z) ⇔
    eval_lit ss circ (iright_lit z)
Proof
  simp [iright_lit_def]
QED

Theorem is_reset_encode_preds_hold_iright[local]:
  is_reset ss (encode_preds_hold circ name lits) (iright_reset reset) latches ⇔
    is_reset ss circ (iright_reset reset) latches
Proof
  simp [is_reset_def, encode_preds_hold_def, iright_reset_def, eval_circuit_def,
        PULL_EXISTS]
QED

Theorem preds_hold_encode_is_reset_ileft[local]:
  preds_hold ss (encode_is_reset circ name reset latches) (set (ileft_lits preds)) ⇔
    preds_hold ss circ (set (ileft_lits preds))
Proof
  cheat
QED

Theorem preds_hold_encode_is_reset_iright[local]:
  preds_hold ss (encode_is_reset circ name reset latches) (set (iright_lits preds)) ⇔
    preds_hold ss circ (set (iright_lits preds))
Proof
  cheat
QED

Theorem eval_circuit_encode_is_witness_reset_INL:
  (∀ss.
     (eval_circuit ss
       (encode_is_witness_reset
          mcirc mreset mcnstrs mlatches
          wcirc wreset wcnstrs wlatches)
       (INL (Ext «reset»)))) =
  is_witness_reset
    mcirc mreset mnext mpreds (set mcnstrs) (set mlatches)
    wcirc wreset wnext wpreds (set wcnstrs) (set wlatches)
Proof
  simp [encode_is_witness_reset_def, eval_circuit_encode_imply_INL,
        eval_circuit_encode_preds_hold_INL, eval_lit_encode_preds_hold_INL,
        eval_circuit_encode_is_reset_INL, eval_lit_encode_is_reset_INL,
        is_witness_reset_def, is_reset_ileft, is_reset_encode_preds_hold_iright,
        preds_hold_encode_is_reset_ileft, preds_hold_encode_is_reset_iright,
        preds_hold_ileft]
  >> cheat
QED
