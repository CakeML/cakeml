(*
  Formalization of HWMCC certificates
*)
Theory aig_cert
Ancestors
  aig
Libs
  preamble

(* TODO Add references to papers *)

(* Soundness ******************************************************************)

Definition signal_imply_def:
  signal_imply ss aig ss' aig' signals signals' =
  LIST_REL (λq q'. lits_hold ss aig {q} ⇒ lits_hold ss' aig' {q'})
    signals signals'
End

Definition lives_imply_def:
  lives_imply ss₀ ss₁ wqaig mqaig wlive mlive =
  LIST_REL (λQ Q'. signal_imply ss₀ wqaig ss₁ mqaig Q Q') wlive mlive
End

Definition some_signal_holds_def:
  some_signal_holds ss aig signals =
  EXISTS (λp. lits_hold ss aig {p}) signals
End

Definition lives_hold_def:
  lives_hold ss aig live = EVERY (some_signal_holds ss aig) live
End

(* TODO Use records for circuit *)

(* NOTE We use R{L} and F{L} on the left-hand side of implications
   instead of R{K} and F{K}, allowing us to prove soundness a bit easier. *)

Definition reset_cond_def:
  reset_cond
    maig mreset mcnstrs mlatches
    waig wreset wcnstrs wlatches
  ⇔
  ∀ss.
    (is_reset ss maig mreset mlatches ∧
     lits_hold ss maig mcnstrs
     ⇒
     is_reset ss waig wreset (mlatches ∩ wlatches) ∧
     lits_hold ss waig wcnstrs)
End

Definition transition_cond_def:
  transition_cond
    maig mnext mcnstrs mlatches
    waig wnext wcnstrs wlatches
  ⇔
  ∀ss₀ ss₁.
    (is_next ss₀ maig mnext mlatches (SND ss₁) ∧
     lits_hold ss₀ maig mcnstrs ∧
     lits_hold ss₁ maig mcnstrs ∧
     lits_hold ss₀ waig wcnstrs)
    ⇒
    (is_next ss₀ waig wnext (mlatches ∩ wlatches) (SND ss₁) ∧
     lits_hold ss₁ waig wcnstrs)
End

Definition safety_cond_def:
  safety_cond
    maig msafes mcnstrs
    waig wsafes wcnstrs
  ⇔
  ∀ss.
    (lits_hold ss maig mcnstrs ∧
     lits_hold ss waig wcnstrs) ⇒
    lits_hold ss waig wsafes ⇒
    lits_hold ss maig msafes
End

Definition liveness_cond_def:
  liveness_cond
    maig mcnstrs mqaig mlive
    waig wnext wsafes wcnstrs wqaig wlive wlatches
  ⇔
    (* This LENGTH property is not strictly necessary but makes the proof a bit
       neater *)
    LIST_REL (λms ws. LENGTH ms = LENGTH ws) mlive wlive ∧
    ∀ss₀ ss₁.
      (lits_hold ss₀ maig mcnstrs ∧
       lits_hold ss₀ waig wcnstrs ∧
       lits_hold ss₀ waig wsafes ∧
       lits_hold ss₁ maig mcnstrs ∧
       lits_hold ss₁ waig wcnstrs ∧
       lits_hold ss₁ waig wsafes ∧
       is_next ss₀ waig wnext wlatches (SND ss₁))
      ⇒
      lives_imply (state_pair ss₀ ss₁) (state_pair ss₀ ss₁) wqaig mqaig
        wlive mlive
End

Definition simulates_def:
  simulates
    maig mreset mnext msafes mcnstrs mqaig mlive mlatches
    waig wreset wnext wsafes wcnstrs wqaig wlive wlatches
  ⇔
  reset_cond
    maig mreset mcnstrs mlatches
    waig wreset wcnstrs wlatches
  ∧
  transition_cond
    maig mnext mcnstrs mlatches
    waig wnext wcnstrs wlatches
  ∧
  safety_cond
    maig msafes mcnstrs
    waig wsafes wcnstrs
  ∧
  liveness_cond
    maig mcnstrs mqaig mlive
    waig wnext wsafes wcnstrs wqaig wlive wlatches
End

Definition base_cond_def:
  base_cond
    aig reset safes cnstrs latches
  ⇔
    ∀ss.
      (is_reset ss aig reset latches ∧
       lits_hold ss aig cnstrs)
      ⇒
      lits_hold ss aig safes
End

Definition induction_cond_def:
  induction_cond
    aig next safes cnstrs latches
  ⇔
    ∀ss₀ ss₁.
      (lits_hold ss₀ aig safes ∧
       is_next ss₀ aig next latches (SND ss₁) ∧
       lits_hold ss₀ aig cnstrs ∧
       lits_hold ss₁ aig cnstrs)
      ⇒
      lits_hold ss₁ aig safes
End

Definition is_inductive_def:
  is_inductive
    aig reset next safes cnstrs latches
  ⇔
    base_cond aig reset safes cnstrs latches ∧
    induction_cond aig next safes cnstrs latches
End

Definition decrease_cond_def:
  decrease_cond
    aig next safes cnstrs qaig live latches
  ⇔
    ∀ss₀ ss₁.
      (lits_hold ss₀ aig cnstrs ∧
       lits_hold ss₀ aig safes ∧
       lits_hold ss₁ aig cnstrs ∧
       lits_hold ss₁ aig safes ∧
       is_next ss₀ aig next latches (SND ss₁))
       ⇒
       lives_hold (state_pair ss₁ ss₀) qaig live
End

Definition closure_cond_def:
  closure_cond
    aig next safes cnstrs qaig live latches
  ⇔
    ∀ss₀ ss₁ ss₂.
      (lits_hold ss₀ aig cnstrs ∧
       lits_hold ss₀ aig safes ∧
       lits_hold ss₁ aig cnstrs ∧
       lits_hold ss₁ aig safes ∧
       lits_hold ss₂ aig cnstrs ∧
       lits_hold ss₂ aig safes ∧
       is_next ss₀ aig next latches (SND ss₁) ∧
       lives_hold (state_pair ss₀ ss₂) qaig live)
      ⇒
      lives_hold (state_pair ss₁ ss₂) qaig live
End

Definition stable_cond_def:
  stable_cond
    aig next safes cnstrs qaig live latches
  ⇔
    ∀ss₀ ss₁ ss₂.
      (lits_hold ss₀ aig cnstrs ∧
       lits_hold ss₀ aig safes ∧
       lits_hold ss₁ aig cnstrs ∧
       lits_hold ss₁ aig safes ∧
       lits_hold ss₂ aig cnstrs ∧
       lits_hold ss₂ aig safes ∧
       is_next ss₀ aig next latches (SND ss₁) ∧
       is_next ss₁ aig next latches (SND ss₂) ∧
       lives_hold (state_pair ss₀ ss₁) qaig live ∧
       lives_hold (state_pair ss₁ ss₂) qaig live)
       ⇒
       lives_imply (state_pair ss₀ ss₁) (state_pair ss₁ ss₂) qaig qaig
         live live
End

Definition is_ranked_def:
  is_ranked
    waig wnext wsafes wcnstrs wqaig wlive wlatches
  ⇔
  decrease_cond
    waig wnext wsafes wcnstrs wqaig wlive wlatches
  ∧
  closure_cond
    waig wnext wsafes wcnstrs wqaig wlive wlatches
  ∧
  stable_cond
    waig wnext wsafes wcnstrs wqaig wlive wlatches
End

Definition is_witness_def:
  is_witness
    maig mreset mnext msafes mcnstrs mqaig mlive mlatches
    waig wreset wnext wsafes wcnstrs wqaig wlive wlatches
  ⇔
  simulates
    maig mreset mnext msafes mcnstrs mqaig mlive mlatches
    waig wreset wnext wsafes wcnstrs wqaig wlive wlatches
  ∧
  is_inductive
    waig wreset wnext wsafes wcnstrs wlatches
  ∧
  is_ranked
    waig wnext wsafes wcnstrs wqaig wlive wlatches
End

(* To show that we can find a state where the reset functions are all satisfied,
   we construct a topological order that we can pass to patch. *)

Definition is_minimal_def:
  is_minimal R s x ⇔ x ∈ s ∧ ∀y. y ∈ s ⇒ ¬R y x
End

Definition topo_sort_def:
  topo_sort R s =
  if FINITE s ∧ ∃x. is_minimal R s x then
    let m = @x. is_minimal R s x in
      m :: topo_sort R (s DELETE m)
  else []
Termination
  wf_rel_tac ‘measure (CARD ∘ SND)’ >> rw []
  >-
   (gvs [CARD_EQ_0, GSYM NOT_ZERO, is_minimal_def]
    >> metis_tac [MEMBER_NOT_EMPTY])
  >- metis_tac [is_minimal_def]
End

Theorem topo_sort_empty[local,simp]:
  topo_sort R ∅ = []
Proof
  simp [Once topo_sort_def, is_minimal_def]
QED

Theorem exists_is_minimal:
  irreflexive R ∧ transitive R ⇒
  FINITE s ∧ s ≠ ∅ ⇒ ∃x. is_minimal R s x
Proof
  strip_tac
  >> Induct_on ‘FINITE s’
  >> rw [is_minimal_def]
  >> Cases_on ‘s = ∅’
  >- fs [irreflexive_def]
  >> metis_tac [irreflexive_def, transitive_def]
QED

Theorem set_topo_sort_sub[local]:
  ∀R s. set (topo_sort R s) ⊆ s
Proof
  recInduct topo_sort_ind >> rw []
  >> simp [Once topo_sort_def]
  >> IF_CASES_TAC >> gvs []
  >> conj_tac
  >- metis_tac [is_minimal_def]
  >> irule SUBSET_TRANS
  >> metis_tac [DELETE_SUBSET]
QED

Theorem MEM_topo_sort[local]:
  ∀R s y. MEM y (topo_sort R s) ⇒ y ∈ s
Proof
  metis_tac [set_topo_sort_sub, SUBSET_DEF]
QED

Theorem set_topo_sort_eq[local]:
  ∀R s. irreflexive R ∧ transitive R ∧ FINITE s ⇒ set (topo_sort R s) = s
Proof
  recInduct topo_sort_ind >> rw []
  >> Cases_on ‘s = ∅’ >> gvs []
  >> simp [Once topo_sort_def]
  >> drule_all_then assume_tac exists_is_minimal >> simp []
  >> irule INSERT_DELETE
  >> metis_tac [is_minimal_def]
QED

Theorem ALL_DISTINCT_topo_sort[local]:
  ∀R s. ALL_DISTINCT (topo_sort R s)
Proof
  recInduct topo_sort_ind >> rw []
  >> simp [Once topo_sort_def]
  >> IF_CASES_TAC >> gvs []
  >> strip_tac
  >> drule MEM_topo_sort
  >> simp []
QED

Theorem no_inversions_topo_sort[local]:
  ∀R s. no_inversions R (topo_sort R s)
Proof
  recInduct topo_sort_ind >> rw []
  >> simp [Once topo_sort_def]
  >> IF_CASES_TAC >> gvs [no_inversions_def]
  >> rw []
  >> ‘is_minimal R s (@x. is_minimal R s x)’ by metis_tac [is_minimal_def]
  >> drule_then assume_tac MEM_topo_sort
  >> fs [is_minimal_def]
QED

(* Extends a trace for the model to a trace for the witness.
   This setup allows us to formulate the conclusion of
   extend_model_trace_to_witness as ∃steps'. ∀n. ... allowing us to use the lemma
   for both finite and infinite traces. *)
Definition mk_trace_def:
  (mk_trace lt mlatches waig wreset wnext wsafes wcnstrs wlatches steps 0 =
   let
     xs = topo_sort lt (wlatches DIFF (mlatches ∩ wlatches));
     (is, ls) = steps 0
   in
     (is, patch waig wreset is ls xs)) ∧
  (mk_trace lt mlatches waig wreset wnext wsafes wcnstrs wlatches steps (SUC n) =
   let
     prev = mk_trace lt mlatches waig wreset wnext wsafes wcnstrs wlatches steps n
   in
     @succ.
       is_next prev waig wnext wlatches (SND succ) ∧
       lits_hold succ waig wcnstrs ∧
       agree_on UNIV mlatches succ (steps (SUC n)))
End

Definition dep_model_def:
  dep_model
    aig reset next safes cnstrs inputs latches ⇔
  dep_aig inputs latches aig ∧
  dep_reset inputs latches reset latches ∧
  dep_latch_lit inputs latches next latches ∧
  dep_lits inputs latches safes ∧
  dep_lits inputs latches cnstrs
End

Theorem agree_on_weaken_inputs[local]:
  agree_on inputs latches ss' ss ∧
  inputs' ⊆ inputs
  ⇒
  agree_on inputs' latches ss' ss
Proof
  metis_tac [SUBSET_DEF, agree_on_weaken]
QED

Theorem steps_agree_weaken_inputs[local]:
  steps_agree n inputs latches steps' steps ∧
  inputs' ⊆ inputs
  ⇒
  steps_agree n inputs' latches steps' steps
Proof
  metis_tac [steps_agree_def, agree_on_weaken_inputs]
QED

Theorem extend_model_trace_to_witness:
  dep_model maig mreset mnext msafes mcnstrs minputs mlatches ∧
  reset_cond
    maig mreset mcnstrs mlatches
    waig wreset wcnstrs wlatches ∧
  transition_cond
    maig mnext mcnstrs mlatches
    waig wnext wcnstrs wlatches ∧
  is_stratified lt waig wreset wlatches ∧
  FINITE wlatches
  ⇒
  ∃steps'. ∀n.
    is_trace maig mreset mnext mcnstrs mlatches steps n ⇒
    is_trace waig wreset wnext wcnstrs wlatches steps' n ∧
    steps_agree n UNIV mlatches steps' steps
Proof
  rw [dep_model_def, is_stratified_def]
  >> qexists ‘mk_trace lt mlatches waig wreset wnext wsafes wcnstrs wlatches steps’
  >> Induct_on ‘n’ >> strip_tac
  >-
   (fs [is_trace_def, reset_cond_def, steps_agree_def]
    >> first_assum $ drule_all_then assume_tac
    >> namedCases_on ‘steps 0’ ["is ls"] >> fs []
    >> gvs [mk_trace_def]
    >> qmatch_goalsub_abbrev_tac ‘patch _ _ _ _ xs’
    >> sg ‘∀l. MEM l xs ⇔ l ∈ (wlatches DIFF mlatches ∩ wlatches)’
    >- (simp [Abbr ‘xs’, Req0 set_topo_sort_eq])
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
          drule_then irule lits_hold_dep_aig>>
          last_assum $ irule_at (Pos hd)>>
          simp[Abbr`ss0`, agree_on_def]>>
          rw[]>>
          irule (GSYM not_mem_patch_eq)>>
          simp[Abbr`xs`])
      >> rw[]
      >> sg ‘wlatches = (mlatches ∩ wlatches) ∪ (set xs)’
      >- (simp [Abbr ‘xs’, Req0 set_topo_sort_eq] >> SET_TAC [])
      >> pop_assum SUBST1_TAC
      >> simp [is_reset_union,Abbr`ss0`]
      >> irule subset_is_reset_patch
      >> first_assum $ irule_at (Pos last)
      >> simp [Abbr ‘xs’, Req0 set_topo_sort_eq, ALL_DISTINCT_topo_sort,
               no_inversions_topo_sort])
    >> simp [steps_agree_def, agree_on_def, Abbr`ss0`]
    >-
     (rw []
      >> rename1 ‘patch _ _ _ _ _ l’ >> ‘¬MEM l xs’ by simp [Abbr ‘xs’]
      >> simp [not_mem_patch_eq]))
  >> gvs [is_trace_SUC, steps_agree_SUC]
  >> simp [GSYM ADD1, mk_trace_def]
  >> qmatch_goalsub_abbrev_tac ‘is_next steps'n’
  >> SELECT_ELIM_TAC
  >> conj_tac
  >-
   (qabbrev_tac ‘step =
                 (FST (steps (n + 1)),
                  λl. if l ∈ mlatches then (SND (steps (n + 1))) l
                      else eval_lit (steps'n) waig (wnext l))’
    >> qexists ‘step’
    >> ‘is_next (steps'n) maig mnext mlatches (SND step)’ by
      (drule is_next_dep_aig
       >> disch_then irule
       >> qpat_x_assum ‘dep_aig _ _ _’ $ irule_at Any
       >> gvs [steps_agree_def, agree_on_sym, Abbr ‘step’, Abbr‘steps'n’]
       >> irule agree_on_weaken_inputs
       >> first_assum $ irule_at (Pos last) >> simp [])
    >> ‘lits_hold (steps'n) maig mcnstrs’ by
      (‘lits_hold (steps n) maig mcnstrs’ by metis_tac [is_trace_lits_hold_n]
       >> drule lits_hold_dep_aig
       >> disch_then drule >> disch_then irule
       >> gvs [steps_agree_def, agree_on_sym, Abbr‘steps'n’]
       >> irule agree_on_weaken_inputs
       >> first_assum $ irule_at (Pos last) >> simp [])
    >> ‘lits_hold step maig mcnstrs’ by
      (rev_drule lits_hold_dep_aig
       >> disch_then drule >> disch_then irule
       >> Cases_on ‘steps (n + 1)’
       >> gvs [agree_on_def, Abbr ‘step’])
    >> ‘lits_hold (steps'n) waig wcnstrs’ by metis_tac [is_trace_lits_hold_n]
    (* Following the paper proof, we can now invoke the transition check
       and extend these two facts to the witness. *)
    >> fs [transition_cond_def]
    >> first_x_assum $ drule_all_then assume_tac >> fs []
    >> conj_tac
    >- (fs [is_next_def] >> rw [] >> Cases_on ‘l ∈ mlatches’ >> gvs [Abbr ‘step’])
    >> gvs [ADD1]
    >> Cases_on ‘steps (n + 1)’
    >> fs [agree_on_def, Abbr ‘step’])
  >> rw []
QED

Theorem is_inductive_lits_hold[local]:
  is_trace aig reset next cnstrs latches steps n ∧
  is_inductive
    aig reset next safes cnstrs latches
  ⇒
  lits_hold (steps n) aig safes
Proof
  simp[is_inductive_def]>>
  Induct_on`n`>>rw[]
  >-
    gvs[base_cond_def,is_trace_def]>>
  gvs[is_trace_SUC] >>
  gvs[induction_cond_def,ADD1]>>
  first_x_assum irule>>
  rw[]>>
  first_x_assum (irule_at (Pos last))>>
  simp[]>>
  metis_tac[is_trace_lits_hold_n]
QED

Theorem inf_is_inductive_lits_hold[local]:
  is_inf_trace aig reset next cnstrs latches steps ∧
  is_inductive
    aig reset next safes cnstrs latches
  ⇒
  (∀n. lits_hold (steps n) aig safes)
Proof
  rw [is_inf_trace_eq] >> metis_tac [is_inductive_lits_hold]
QED

Theorem is_witness_is_safe:
  is_witness
    maig mreset mnext msafes mcnstrs mqaig mlive mlatches
    waig wreset wnext wsafes wcnstrs wqaig wlive wlatches ∧
  dep_model
    maig mreset mnext msafes mcnstrs minputs mlatches ∧
  is_stratified lt waig wreset wlatches ∧
  FINITE wlatches
  ⇒
  is_safe
    maig mreset mnext mcnstrs mlatches msafes
Proof
  rw [is_witness_def, is_safe_def, simulates_def]
  >> CCONTR_TAC
  >> fs [is_unsafe_def]
  >> pop_assum mp_tac >> simp[]
  >> rename1 ‘lits_hold (steps _)’
  >> drule_all extend_model_trace_to_witness
  >> disch_then $ qspec_then ‘steps’ mp_tac >> rw []
  >> first_assum drule >> strip_tac
  >> drule_all is_inductive_lits_hold
  >> strip_tac
  >> fs [dep_model_def]
  >> `is_trace maig mreset mnext mcnstrs mlatches steps' n` by
    (irule is_trace_dep_aig >> fs []
     >> first_assum $ irule_at (Pos hd) >> simp []
     >> irule_at (Pos hd) steps_agree_weaken_inputs
     >> first_assum $ irule_at (Pos hd)
     >> simp [])
  >> drule_at_then Any irule lits_hold_dep_aig
  >> rename1`steps_agree n _ mlatches steps' steps`
  >> fs[steps_agree_def]
  >> qexists_tac`steps' n`
  >> conj_tac
  >-
   (gvs[safety_cond_def]
    >> first_x_assum irule
    >> gvs[]
    >> metis_tac[is_trace_lits_hold_n])
  >> irule agree_on_weaken_inputs
  >> first_assum $ irule_at (Pos last)
  >> simp []
QED

Theorem closure_cond_lives_hold[local]:
  ∀k.
    closure_cond
      aig next safes cnstrs qaig live latches ∧
    lives_hold (state_pair (steps i) (steps j)) qaig live ∧
    (∀n. lits_hold (steps n) aig safes) ∧
    (∀n. lits_hold (steps n) aig cnstrs) ∧
    (∀n. is_next (steps n) aig next latches (SND (steps (n + 1))))
    ⇒
    lives_hold (state_pair (steps (i + k)) (steps j)) qaig live
Proof
  Induct >> rw [] >> fs []
  >> fs [closure_cond_def]
  >> first_assum irule >> simp []
  >> qexists ‘steps (i + k)’ >> fs [ADD1]
  >> rewrite_tac [ADD_ASSOC] >> simp[ADD_ASSOC]
  >> first_x_assum $ qspec_then ‘i + k’ mp_tac >> simp []
QED

Theorem lives_hold_dep_aig[local]:
  lives_hold ss aig ns ∧
  dep_aig inputs latches aig ∧
  dep_lits inputs latches (set (FLAT ns)) ∧
  agree_on inputs latches ss ss'
  ⇒
  lives_hold ss' aig ns
Proof
  rw [lives_hold_def, EVERY_MEM, dep_lits_def, some_signal_holds_def,
          EXISTS_MEM, MEM_FLAT, lits_hold_def]
  >> metis_tac [dep_eval_lit_eq]
QED

Theorem lives_hold_matching_transition[local]:
  lives_hold (state_pair (steps (i + 2)) (steps (i + 1))) qaig live ∧
  matching_transition inputs latches steps i (i + 2) ∧
  dep_aig (pair_set inputs) (pair_set latches) qaig ∧
  dep_lits (pair_set inputs) (pair_set latches) (set (FLAT live))
  ⇒
  lives_hold (state_pair (steps i) (steps (i + 1))) qaig live
Proof
  rw []
  >> irule lives_hold_dep_aig
  >> qpat_x_assum ‘lives_hold _ _ _’ $ irule_at Any
  >> first_assum $ irule_at (Pos hd) >> simp []
  >> fs [agree_on_pair, matching_transition_def]
QED

Theorem matching_transition_live[local]:
  decrease_cond
    aig next safes cnstrs qaig live latches  ∧
  is_inf_trace aig reset next cnstrs latches steps ∧
  closure_cond
    aig next safes cnstrs qaig live latches ∧
  matching_transition inputs' latches' steps i j ∧
  set (aig_inputs aig) ⊆ inputs' ∧
  BIGUNION (IMAGE (set o lit_inputs o next) latches) ⊆ inputs' ∧
  set (aig_inputs qaig) ⊆ pair_set inputs' ∧
  BIGUNION (IMAGE (set o lit_inputs) (set (FLAT live))) ⊆ pair_set inputs' ∧
  latches ⊆ latches' ∧
  set (aig_latches aig) ⊆ latches' ∧
  BIGUNION (IMAGE (set o lit_latches o next) latches) ⊆ latches' ∧
  set (aig_latches qaig) ⊆ pair_set latches' ∧
  BIGUNION (IMAGE (set o lit_latches) (set (FLAT live))) ⊆ pair_set latches' ∧
  (∀n. lits_hold (steps n) aig safes)
  ⇒
  lives_hold (state_pair (steps i) (steps (i + 1))) qaig live
Proof
  rw []
  >> drule_then assume_tac is_inf_trace_cnstrs_hold
  >> Cases_on ‘j = i + 1’ >> gvs []
  >- (
    fs [matching_transition_def, decrease_cond_def]
    >> last_assum irule >> gvs [is_inf_trace_def]
    >> last_x_assum $ qspec_then ‘i’ assume_tac
    >> irule is_next_dep_aig
    >> first_assum $ irule_at (Pos last)
    >> fs [agree_on_sym]
    >> first_assum $ irule_at (Pos (el 4)) >> simp []
    >> CONJ_TAC >-
      (Cases_on ‘steps i’ >> Cases_on ‘steps (i + 1)’
      >> fs [agree_on_def]
      >> metis_tac[])
    >> CONJ_TAC >- (
      irule dep_aig_subset>>
      metis_tac[dep_aig_inputs_latches])
    >>
      irule dep_latch_lit_next>>
      fs[])
  >> drule_then assume_tac is_inf_trace_is_next
  >> ‘lives_hold (state_pair (steps (i + 2)) (steps (i + 1))) qaig live’ by
    (fs [decrease_cond_def]
     >> last_assum irule >> simp []
     >> first_x_assum $ qspec_then ‘i + 1’ mp_tac >> simp [])
  >> Cases_on ‘j = i + 2’ >> gvs []
  >-
   (irule lives_hold_matching_transition >> simp []
    >> qpat_x_assum ‘matching_transition _ _ _ _ _’ $ irule_at Any
    >> simp []
    >> CONJ_TAC >- (
      irule dep_aig_subset>>
      metis_tac[dep_aig_inputs_latches])
    >>
      metis_tac[dep_lits_lits])
  >> drule_all closure_cond_lives_hold
  >> disch_then $ qspec_then ‘j - i - 2’ assume_tac
  >> gvs [matching_transition_def]
  >> irule lives_hold_dep_aig
  >> pop_assum (irule_at Any)
  >> qexists_tac`pair_set latches'`
  >> qexists_tac`pair_set inputs'`
  >> simp [agree_on_pair]
  >> CONJ_TAC >- (
    irule dep_aig_subset>>
    metis_tac[dep_aig_inputs_latches])
  >>
    metis_tac[dep_lits_lits]
QED

Theorem stable_cond_lits_hold[local]:
  stable_cond waig wnext wsafes wcnstrs wqaig wlive wlatches ∧
  MEM q Q ∧ MEM Q wlive ∧
  lits_hold (state_pair (steps j) (steps (j + 1))) wqaig {q} ∧
  (∀n. lits_hold (steps n) waig wcnstrs) ∧
  (∀n. lits_hold (steps n) waig wsafes) ∧
  (∀n. is_next (steps n) waig wnext wlatches (SND (steps (n + 1)))) ∧
  (∀i. j ≤ i ⇒
       lives_hold (state_pair (steps i) (steps (i + 1))) wqaig wlive) ∧
  j ≤ i
  ⇒
  lits_hold (state_pair (steps i) (steps (i + 1))) wqaig {q}
Proof
  Induct_on ‘i - j’ >> rw [] >> fs []
  >- (‘i = j’ by simp [] >> simp [])
  >> last_x_assum $ qspecl_then [‘i - 1’, ‘j’] assume_tac
  >> gvs []
  >> gvs [stable_cond_def, MEM_EL]
  >> last_x_assum $ qspecl_then [‘steps (i - 1)’, ‘steps i’, ‘steps (i + 1)’] mp_tac
  >> simp []
  >> impl_tac >-
   (‘i - 1n + 1 = i’ by simp []
    >> ‘j ≤ i - 1’ by simp []
    >> metis_tac [])
  >> simp [lives_imply_def, signal_imply_def, LIST_REL_EL_EQN]
QED

Theorem is_witness_is_live:
  is_witness
    maig mreset mnext msafes mcnstrs mqaig mlive mlatches
    waig wreset wnext wsafes wcnstrs wqaig wlive wlatches ∧
  dep_model
    maig mreset mnext msafes mcnstrs minput mlatches ∧
  (* TODO Does dep_qaig really need the same minput?
     If not, the proof of encoding_is_safe_and_live may become tidier *)
  dep_qaig minput mqaig mlive mlatches ∧
  is_stratified lt waig wreset wlatches ∧
  FINITE wlatches
  ⇒
  is_live
    maig mreset mnext mcnstrs mqaig (IMAGE set (set mlive)) mlatches
Proof
  rw []
  (* Get safety of model *)
  >> drule_all_then assume_tac is_witness_is_safe
  (* Extend trace on model to trace on witness *)
  >> fs [is_witness_def, simulates_def]
  >> rw [is_live_def]
  >> drule_all extend_model_trace_to_witness
  >> rename1 ‘is_inf_trace _ _ _ _ _ steps’
  >> disch_then $ qspec_then ‘steps’ mp_tac >> strip_tac
  >> dxrule is_inf_trace_steps_agree
  >> simp [] >> strip_tac
  (* Witness constraints and safety signals hold on extended trace *)
  >> ‘∀n. lits_hold (steps' n) waig wsafes’ by
    metis_tac [inf_is_inductive_lits_hold]
  >> ‘∀n. lits_hold (steps' n) waig wcnstrs’ by
    metis_tac [is_inf_trace_cnstrs_hold]
  (* Extended trace has valid steps for the witness *)
  >> ‘∀n. is_next (steps' n) waig wnext wlatches (SND (steps' (n + 1)))’ by
     metis_tac [is_inf_trace_is_next]
  (* Extended trace is also a trace for the model *)
  >> ‘is_inf_trace maig mreset mnext mcnstrs mlatches steps'’ by
    (irule is_inf_trace_dep_aig
     >> first_assum $ irule_at (Pos last)
     >> fs [dep_model_def]
     >> first_assum $ irule_at (Pos last)
     >> rw []
     >> irule steps_agree_weaken_inputs
     >> qexists ‘UNIV’ >> simp [])
  (* Model constraints holds on the witness *)
  >> ‘∀n. lits_hold (steps' n) maig mcnstrs’ by
    metis_tac [is_inf_trace_cnstrs_hold]
  >> qabbrev_tac`inputs' =
    set (aig_inputs waig) ∪
    BIGUNION (IMAGE (set o lit_inputs o wnext) wlatches) ∪
    (IMAGE OUTL (set (aig_inputs wqaig)) ∪
    IMAGE OUTR (set (aig_inputs wqaig))) ∪
    (IMAGE OUTL (BIGUNION (IMAGE (set o lit_inputs) (set (FLAT wlive)))) ∪
    IMAGE OUTR (BIGUNION (IMAGE (set o lit_inputs) (set (FLAT wlive)))))`
  >> qabbrev_tac`latches' =
    wlatches ∪
    set (aig_latches waig) ∪
    BIGUNION (IMAGE (set o lit_latches o wnext) wlatches) ∪
    (IMAGE OUTL (set (aig_latches wqaig)) ∪
    IMAGE OUTR (set (aig_latches wqaig))) ∪
    (IMAGE OUTL (BIGUNION (IMAGE (set o lit_latches) (set (FLAT wlive)))) ∪
    IMAGE OUTR (BIGUNION (IMAGE (set o lit_latches) (set (FLAT wlive)))))`
  (* Infinite trace on witness repeats from k onwards *)
  >> qspecl_then [‘inputs'’, ‘latches'’, ‘steps'’] mp_tac matching_transition_exists
  >> impl_tac >-
    (unabbrev_all_tac>>fs[is_stratified_def,PULL_EXISTS])
  >> strip_tac
  >> rename1 ‘k < _ ⇒ _’ >> qexists ‘k+1’ >> rw []
  >> rename1 ‘MEM prop mlive’
  (* Model is live if model is live on extended trace *)
  >> suff
       ‘∃signal.
          MEM signal prop ∧
            ∀i. k + 1 ≤ i ⇒
              lits_hold (state_pair (steps' i) (steps' (i + 1))) mqaig {signal}’
  >-
    (rw []
     >> qexists ‘signal’ >> rw []
     >> irule lits_hold_dep_aig
     >> fs [dep_qaig_def]
     >> first_assum $ irule_at (Pos hd)
     >> simp []
     >> qexists ‘state_pair (steps' i) (steps' (i + 1))’
     >> reverse conj_tac
     >-
      (fs [steps_agree_def, agree_on_pair]
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
    (fs [liveness_cond_def, LIST_REL_EL_EQN])
  >> ‘∃n'.
        n' < LENGTH wlive❲n❳ ∧
        ∀i. k + 1 ≤ i ⇒
              lits_hold (state_pair (steps' i) (steps' (i + 1))) wqaig {wlive❲n❳❲n'❳}’
    suffices_by
    (rw []
     >> qexists ‘n'’
     >> gvs []
     >> rw []
     >> gvs [liveness_cond_def, lives_imply_def, signal_imply_def,
             LIST_REL_EL_EQN, PULL_FORALL])
  (* Witness is live *)
  >> fs [is_ranked_def]
  >> have
       ‘∀i. k + 1 ≤ i ⇒
            lives_hold (state_pair (steps' i) (steps' (i + 1))) wqaig wlive’
  >-
    (rw []
     >> drule matching_transition_live >> simp []
     >> disch_then drule
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
  >> drule stable_cond_lits_hold
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

Theorem is_witness_is_safe_and_live:
  is_witness
    maig mreset mnext msafes mcnstrs mqaig mlive mlatches
    waig wreset wnext wsafes wcnstrs wqaig wlive wlatches ∧
  dep_model
    maig mreset mnext msafes mcnstrs minput mlatches ∧
  (* TODO See is_witness_is_live comment *)
  dep_qaig minput mqaig mlive mlatches ∧
  is_stratified lt waig wreset wlatches ∧
  FINITE wlatches
  ⇒
  is_safe
    maig mreset mnext mcnstrs mlatches msafes
  ∧
  is_live
    maig mreset mnext mcnstrs mqaig (IMAGE set (set mlive)) mlatches
Proof
  strip_tac
  >> drule_all_then assume_tac is_witness_is_safe
  >> drule_all_then assume_tac is_witness_is_live
  >> simp []
QED
