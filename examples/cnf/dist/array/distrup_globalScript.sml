(*
  Global view of distrup nodes
*)
Theory distrup_global
Libs
  preamble basis wordsLib
Ancestors
  distrup_list distrup_arrayProg words byte distrup_fullProg distInfer distInferRefine

Datatype:
  state = <| procs  : 'name |-> ((int vector option list # word8 list # word8) option);
             facts  :  int vector list;
             validated  : bool
           |>
End

Datatype:
  label = Tau | Act 'name distrup
End

Inductive step:
[~events_ok_delete:]
  FLOOKUP st.procs id = SOME lst ∧
  events_ok lst events' [Del hints] lst'
  ⇒
  step st (Act id (Del hints)) (st with procs := st.procs |+ (id,lst'))
[~events_ok_Import:]
  FLOOKUP st.procs id = SOME lst ∧
  events_ok lst events' [Import n c] lst' ∧
  MEM c st.facts
  ⇒
  step st (Act id (Import n c)) (st with procs := st.procs |+ (id,lst'))
[~events_ok_Produce:]
  FLOOKUP st.procs id = SOME(SOME vlst) ∧
  events_ok (SOME vlst) events' [Lrup n c hints] (SOME vlst') ∧
  MEM c st.facts
  ⇒
  step st (Act id (Lrup n c hints)) (st with <|procs := st.procs |+ (id,SOME vlst');
                                           facts := c::st.facts|>)
[~events_ok_Produce_fail:]
  FLOOKUP st.procs id = SOME lst ∧
  events_ok lst events' [Lrup n c hints] NONE
  ⇒
  step st (Act id (Lrup n c hints)) (st with <|procs := st.procs |+ (id,NONE)|>)
[~events_ok_Validate:]
  FLOOKUP st.procs id = SOME(SOME vlst) ∧
  events_ok (SOME vlst) events' [ValidateUnsat] (SOME vlst')
  ⇒
  step st (Act id (ValidateUnsat)) (st with <|procs := st.procs |+ (id,SOME vlst');
                                              validated := T|>)
[~events_ok_Validate_fail:]
  FLOOKUP st.procs id = SOME lst ∧
  events_ok lst events' [ValidateUnsat] NONE
  ⇒
  step st (Act id (ValidateUnsat)) (st with <|procs := st.procs |+ (id,NONE)|>)
End

Definition reduce_def:
  reduce st st' = ∃l. step st l st'
End

Definition state_rel_def:
  state_rel ast cst ⇔
    ast.validated = (if cst.validated then {Vector []} else {}) ∧
    ast.facts = cst.facts ∧
    fmap_rel (OPTREL (λfml (fmls,dml,b). fml_rel fml fmls ∧ (∃dm. dm_rel dm dml b))) ast.procs cst.procs
End

Inductive label_rel:
[~validate:]
  label_rel (Validate (Vector [])) ValidateUnsat
[~delete:]
  label_rel (Delete hints) (Del hints)
[~import:]
  label_rel (Import n fml) (Import n fml)
[~produce:]
  label_rel (Produce n fml) (Lrup n fml hints)
End

Inductive act_rel:
[~tau:]
  act_rel R distInfer$Tau distrup_global$Tau
[~lab:]
  R alpha beta ⇒ act_rel R (Act n alpha) (Act n beta)
End

Theorem events_ok_NIL:
  events_ok lst evs [] lst' ⇔ lst = lst' ∧ evs = []
Proof
  rw[Once events_ok_cases] >>
  metis_tac[]
QED

Theorem check_distrup_list_impossible[simp]:
  (check_distrup_list (Import n c) fmlls Clist b = NONE ⇔ F) ∧
  (check_distrup_list (Del hints) fmlls Clist b = NONE ⇔ F)
Proof
  rw[check_distrup_list_def]
QED

Theorem fmap_rel_FLOOKUP_imp2:
  fmap_rel R f1 f2 ⇒
     ∀k v2. FLOOKUP f2 k = SOME v2 ⇒ ∃v1. FLOOKUP f1 k = SOME v1 ∧ R v1 v2
Proof
  rw[fmap_rel_def,flookup_thm] >>
  gvs[] >>
  metis_tac[]
QED

Theorem fmap_rel_fdomsub:
  fmap_rel R a b ⇒ fmap_rel R (a \\ x) (b \\ x)
Proof
  rw[fmap_rel_def,DOMSUB_FAPPLY_THM]
QED

Theorem delete_ids_eq_DRESTRICT:
  delete_ids fml hints = DRESTRICT fml (COMPL (set hints))
Proof
  rw[cnfTheory.delete_ids_def] >>
  qid_spec_tac ‘fml’ >>
  Induct_on ‘hints’ >>
  rw[DRESTRICT_UNIV,compl_insert] >>
  rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
  rw[DOMSUB_FLOOKUP_THM] >>
  gvs[]
QED

Theorem state_rel_step:
  ∀cst clb cst' ast.
    state_rel ast cst ∧ distrup_global$step cst clb cst' ⇒
    ∃alb ast'. act_rel label_rel alb clb ∧ step sat_infer ast alb ast' ∧ state_rel ast' cst'
Proof
  strip_tac >>
  Induct_on ‘step’ >>
  rpt strip_tac
  >~ [‘[Import _ _]’]
  >- (qhdtm_x_assum ‘events_ok’ $ assume_tac o PURE_ONCE_REWRITE_RULE[events_ok_cases] >>
      gvs[events_ok_NIL] >>
      rw[act_rel_cases,label_rel_cases]
      >- (irule_at (Pos hd) step_import >>
          gvs[state_rel_def] >>
          drule_all fmap_rel_FLOOKUP_imp2 >>
          rw[OPTREL_SOME] >>
          rw[] >>
          irule fmap_rel_FUPDATE_I >>
          simp[] >>
          drule_all_then strip_assume_tac check_distrup_list >>
          gvs[distrupTheory.check_distrup_def] >>
          conj_tac >- metis_tac[] >>
          irule fmap_rel_fdomsub >>
          simp[])
      >- (irule_at (Pos hd) step_spin >>
          gvs[state_rel_def] >>
          drule_all fmap_rel_FLOOKUP_imp2 >>
          rw[OPTREL_SOME] >>
          rw[] >>
          ‘cst.procs |+ (id,NONE) = cst.procs’ suffices_by simp[] >>
          rw[fmap_eq_flookup,FLOOKUP_UPDATE] >> rw[] >> rw[])
      >- (irule_at (Pos hd) step_import >>
          gvs[state_rel_def] >>
          drule_all fmap_rel_FLOOKUP_imp2 >>
          rw[OPTREL_SOME] >>
          rw[] >>
          irule fmap_rel_FUPDATE_I >>
          simp[] >>
          drule_all_then strip_assume_tac check_distrup_list >>
          gvs[distrupTheory.check_distrup_def] >>
          conj_tac >- metis_tac[] >>
          irule fmap_rel_fdomsub >>
          simp[])
      >- (irule_at (Pos hd) step_spin >>
          gvs[state_rel_def] >>
          drule_all fmap_rel_FLOOKUP_imp2 >>
          rw[OPTREL_SOME] >>
          rw[] >>
          ‘cst.procs |+ (id,NONE) = cst.procs’ suffices_by simp[] >>
          rw[fmap_eq_flookup,FLOOKUP_UPDATE] >> rw[] >> rw[]))
  >~ [‘events_ok _ _ [Lrup _ _ _] (SOME _)’]
  >- (qhdtm_x_assum ‘events_ok’ $ assume_tac o PURE_ONCE_REWRITE_RULE[events_ok_cases] >>
      gvs[events_ok_NIL] >>
      rw[act_rel_cases,label_rel_cases]
      >- (irule_at (Pos hd) step_produce_succeed >>
          gvs[state_rel_def] >>
          drule_all fmap_rel_FLOOKUP_imp2 >>
          rw[OPTREL_SOME] >>
          simp[] >>
          drule_all_then strip_assume_tac check_distrup_list >>
          gvs[distrupTheory.check_distrup_def] >>
          conj_tac
          >- (drule ccnfTheory.is_rup_sound >>
              rw[sat_infer_def]) >>
          irule fmap_rel_FUPDATE_I >>
          simp[] >>
          conj_tac >- metis_tac[] >>
          irule fmap_rel_fdomsub >>
          simp[])
      >- (irule_at (Pos hd) step_produce_succeed >>
          gvs[state_rel_def] >>
          drule_all fmap_rel_FLOOKUP_imp2 >>
          rw[OPTREL_SOME] >>
          simp[] >>
          drule_all_then strip_assume_tac check_distrup_list >>
          gvs[distrupTheory.check_distrup_def] >>
          conj_tac
          >- (drule ccnfTheory.is_rup_sound >>
              rw[sat_infer_def]) >>
          irule fmap_rel_FUPDATE_I >>
          simp[] >>
          conj_tac >- metis_tac[] >>
          irule fmap_rel_fdomsub >>
          simp[]))
  >~ [‘events_ok _ _ [Lrup _ _ _] NONE’]
  >- (qhdtm_x_assum ‘events_ok’ $ assume_tac o PURE_ONCE_REWRITE_RULE[events_ok_cases] >>
      gvs[events_ok_NIL] >>
      rw[act_rel_cases,label_rel_cases]
      >- (irule_at (Pos hd) step_produce_fail >>
          gvs[state_rel_def] >>
          drule_all fmap_rel_FLOOKUP_imp2 >>
          rw[OPTREL_SOME] >>
          simp[] >>
          irule fmap_rel_FUPDATE_I >>
          simp[] >>
          irule fmap_rel_fdomsub >>
          simp[])
      >- (irule_at (Pos hd) step_spin >>
          gvs[state_rel_def] >>
          drule_all fmap_rel_FLOOKUP_imp2 >>
          rw[OPTREL_SOME] >>
          simp[] >>
          ‘cst.procs |+ (id,NONE) = cst.procs’ suffices_by simp[] >>
          rw[fmap_eq_flookup,FLOOKUP_UPDATE] >> rw[] >> rw[])
      >- (irule_at (Pos hd) step_produce_fail >>
          gvs[state_rel_def] >>
          drule_all fmap_rel_FLOOKUP_imp2 >>
          rw[OPTREL_SOME] >>
          simp[] >>
          irule fmap_rel_FUPDATE_I >>
          simp[] >>
          irule fmap_rel_fdomsub >>
          simp[])
      >- (irule_at (Pos hd) step_spin >>
          gvs[state_rel_def] >>
          drule_all fmap_rel_FLOOKUP_imp2 >>
          rw[OPTREL_SOME] >>
          simp[] >>
          ‘cst.procs |+ (id,NONE) = cst.procs’ suffices_by simp[] >>
          rw[fmap_eq_flookup,FLOOKUP_UPDATE] >> rw[] >> rw[]))
  >~ [‘events_ok _ _ [ValidateUnsat] (SOME _)’]
  >- (qhdtm_x_assum ‘events_ok’ $ assume_tac o PURE_ONCE_REWRITE_RULE[events_ok_cases] >>
      gvs[events_ok_NIL] >>
      rw[act_rel_cases,label_rel_cases] >>
      irule_at (Pos hd) step_validate >>
      gvs[state_rel_def] >>
      drule_all fmap_rel_FLOOKUP_imp2 >>
      rpt strip_tac >>
      gvs[OPTREL_SOME] >>
      simp[] >>
      drule_all_then strip_assume_tac check_distrup_list >>
      gvs[distrupTheory.check_distrup_def] >>
      gvs[ccnfTheory.contains_emp_def,MEM_MAP,MEM_fmap_to_alist_FLOOKUP,
          FRANGE_FLOOKUP] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- rw[] >>
      gvs[check_distrup_list_def] >>
      ‘(cst.procs |+ (id,SOME (fmlls,Clist,b))) = cst.procs’ suffices_by simp[] >>
      rw[fmap_eq_flookup,FLOOKUP_UPDATE] >> rw[] >> rw[])
  >~ [‘events_ok _ _ [ValidateUnsat] NONE’]
  >- (qhdtm_x_assum ‘events_ok’ $ assume_tac o PURE_ONCE_REWRITE_RULE[events_ok_cases] >>
      gvs[events_ok_NIL] >>
      rw[act_rel_cases,label_rel_cases]
      >- (irule_at (Pos hd) step_validate_fail >>
          gvs[state_rel_def] >>
          drule_all fmap_rel_FLOOKUP_imp2 >>
          rw[OPTREL_SOME] >>
          simp[] >>
          gvs[check_distrup_list_def] >>
          conj_tac
          >- (spose_not_then strip_assume_tac >>
              gvs[FRANGE_FLOOKUP] >>
              drule_then assume_tac ccnf_listTheory.fml_rel_contains_emp_list >>
              gvs[ccnfTheory.contains_emp_def,MEM_MAP,MEM_fmap_to_alist_FLOOKUP] >>
              metis_tac[FST,SND,PAIR]) >>
          irule fmap_rel_FUPDATE_I >>
          simp[] >>
          irule fmap_rel_fdomsub >>
          simp[]) >>
      irule_at (Pos hd) step_spin >>
      gvs[state_rel_def] >>
      drule_all fmap_rel_FLOOKUP_imp2 >>
      rw[OPTREL_SOME] >>
      simp[] >>
      ‘cst.procs |+ (id,NONE) = cst.procs’ suffices_by simp[] >>
      rw[fmap_eq_flookup,FLOOKUP_UPDATE] >> rw[] >> rw[]) >>
  qhdtm_x_assum ‘events_ok’ $ assume_tac o PURE_ONCE_REWRITE_RULE[events_ok_cases] >>
  gvs[events_ok_NIL] >>
  rw[act_rel_cases,label_rel_cases]
  >- (irule_at (Pos hd) step_delete >>
      gvs[state_rel_def] >>
      drule_all fmap_rel_FLOOKUP_imp2 >>
      rw[OPTREL_SOME] >>
      simp[] >>
      drule_all_then strip_assume_tac check_distrup_list >>
      gvs[distrupTheory.check_distrup_def] >>
      irule fmap_rel_FUPDATE_I >>
      simp[] >>
      gvs[delete_ids_eq_DRESTRICT] >>
      conj_tac >- metis_tac[] >>
      irule fmap_rel_fdomsub >>
      simp[])
  >- (irule_at (Pos hd) step_spin >>
      gvs[state_rel_def] >>
      drule_all fmap_rel_FLOOKUP_imp2 >>
      rw[OPTREL_SOME] >>
      simp[] >>
      ‘cst.procs |+ (id,NONE) = cst.procs’ suffices_by simp[] >>
      rw[fmap_eq_flookup,FLOOKUP_UPDATE] >> rw[] >> rw[])
  >- (irule_at (Pos hd) step_delete >>
      gvs[state_rel_def] >>
      drule_all fmap_rel_FLOOKUP_imp2 >>
      rw[OPTREL_SOME] >>
      simp[] >>
      drule_all_then strip_assume_tac check_distrup_list >>
      gvs[distrupTheory.check_distrup_def] >>
      irule fmap_rel_FUPDATE_I >>
      simp[] >>
      gvs[delete_ids_eq_DRESTRICT] >>
      conj_tac >- metis_tac[] >>
      irule fmap_rel_fdomsub >>
      simp[])
  >- (irule_at (Pos hd) step_spin >>
      gvs[state_rel_def] >>
      drule_all fmap_rel_FLOOKUP_imp2 >>
      rw[OPTREL_SOME] >>
      simp[] >>
      ‘cst.procs |+ (id,NONE) = cst.procs’ suffices_by simp[] >>
      rw[fmap_eq_flookup,FLOOKUP_UPDATE] >> rw[] >> rw[])
QED

Theorem state_rel_reduce:
  ∀cst cst' ast.
    state_rel ast cst ∧ distrup_global$reduce꙳ cst cst' ⇒
    ∃ast'. (reduce sat_infer)꙳ ast ast' ∧ state_rel ast' cst'
Proof
  Induct_on ‘RTC’ using RTC_strongind >>
  rw[reduce_def,distInferTheory.reduce_def]
  >- (first_x_assum $ irule_at Any >> simp[]) >>
  drule_all_then strip_assume_tac state_rel_step >>
  first_x_assum $ dxrule_then strip_assume_tac >>
  first_x_assum $ irule_at $ Pos last >>
  irule $ cj 2 RTC_rules >>
  first_x_assum $ irule_at $ Pos last >>
  simp[distInferTheory.reduce_def] >>
  metis_tac[]
QED

(* A good initial state *)
Definition init_def:
  init st fml ⇔
    FEVERY (λ(n,v).
      v = NONE ∨
      ∃n k. v = SOME (REPLICATE n NONE, REPLICATE k 0w, 1w))
      st.procs ∧
    set st.facts ⊆ fml ∧
    ¬st.validated
End

Theorem sat_step_sound_spec_aux:
  reduce꙳ st st' ∧
  init st fml ∧
  st'.validated
  ⇒
  sat_infer fml (Vector [])
Proof
  rpt strip_tac >>
  fs[init_def]>>
  irule $ INST_TYPE [alpha |-> “:num”, beta |-> alpha] sat_step_sound >>
  simp[] >>
  Q.SUBGOAL_THEN ‘∃ast. state_rel ast st’ strip_assume_tac
  >- (rw[state_rel_def] >>
      Q.REFINE_EXISTS_TAC ‘<| procs := _; facts := _; validated := _|>’ >>
      simp[] >>
      qexists_tac`(OPTION_MAP (λ_. FEMPTY)) o_f st.procs`>>
      rw[fmap_rel_def, oneline OPTREL_THM] >>
      TOP_CASE_TAC>>gvs[FEVERY_DEF]>>
      pairarg_tac>>gvs[]>>
      first_x_assum drule >>
      gvs[flookup_thm] >>
      rw[] >>
      gvs[ccnf_listTheory.fml_rel_def,any_el_ALT,EL_REPLICATE] >>
      irule_at Any ccnf_listTheory.dm_rel_FEMPTY_REPLICATE) >>
  drule_all state_rel_reduce >>
  rw[] >>
  first_assum $ irule_at $ Pos last >>
  gvs[state_rel_def] >>
  rw[] >>
  rev_drule $ cj 2 fmap_rel_FLOOKUP_imp >>
  disch_then drule >>
  rw[OPTREL_SOME,ELIM_UNCURRY] >>
  gvs[FDOM_FLOOKUP,SF DNF_ss,FEVERY_DEF] >>
  last_x_assum drule >>
  strip_tac>>gvs[flookup_thm]>>
  Q.SUBGOAL_THEN ‘facts = FEMPTY’ SUBST_ALL_TAC
  >- (rw[fmap_eq_flookup] >>
      gvs[ccnf_listTheory.fml_rel_def,any_el_ALT] >>
      rename1 ‘FLOOKUP _ m’ >>
      first_x_assum $ qspec_then ‘m’ mp_tac >>
      rw[EL_REPLICATE]) >>
  rw[]
QED

Definition satisfiable_def:
  satisfiable fml ⇔
  (∃w. satisfies_vcfml w fml)
End

Definition unsatisfiable_def:
  unsatisfiable fml ⇔ ¬ satisfiable fml
End

Theorem sat_step_sound_spec:
  reduce꙳ st st' ∧
  init st fml ∧
  st'.validated
  ⇒
  unsatisfiable fml
Proof
  rw[]>>
  drule_all sat_step_sound_spec_aux>>
  rw[sat_infer_def,unsatisfiable_def,satisfiable_def]>>
  CCONTR_TAC>>fs[]>>
  first_x_assum drule>>
  EVAL_TAC>>rw[]
QED

Theorem events_ok_append:
  ∀lst events' aevents' lst' events aevents.
    events_ok lst0 events aevents lst ∧
    events_ok lst events' aevents' lst' ⇒
    events_ok lst0 (events ++ events') (aevents ++ aevents') lst'
Proof
  strip_tac >>
  PURE_ONCE_REWRITE_TAC [CONJ_SYM] >>
  Induct_on ‘events_ok’ >>
  rw[] >>
  metis_tac[events_ok_rules]
QED

