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

Inductive resume_ok:
[~init:]
  resume_ok st [] [] st
[~produce:]
  resume_ok st events aevents (SOME (fmlls, Clist, b)) ∧
  is_produce_events n vc produce_events ∧
  is_output_event #"a" #"1" output_event ∧
  check_distrup_list (Lrup n vc hints) fmlls Clist b = SOME (fmlls', Clist', b')
  ⇒
  resume_ok st (events ++ produce_events ++ [output_event]) (aevents ++ [Lrup n vc hints]) (SOME (fmlls', Clist', b'))
[~produce_Fail:]
  resume_ok st events aevents (SOME (fmlls, Clist, b)) ∧
  is_produce_events n vc produce_events ∧
  is_output_event #"a" #"0" output_event ∧
  check_distrup_list (Lrup n vc hints) fmlls Clist b = NONE
  ⇒
  resume_ok st (events ++ produce_events ++ [output_event]) (aevents ++ [Lrup n vc hints]) NONE
[~produce_None:]
  resume_ok st events aevents NONE ∧
  is_produce_events n vc produce_events ∧
  is_output_event #"a" #"0" output_event
  ⇒
  resume_ok st (events ++ produce_events ++ [output_event]) (aevents ++ [Lrup n vc hints]) NONE
[~import:]
  resume_ok st events aevents (SOME (fmlls, Clist, b)) ∧
  is_import_events n vc import_events ∧
  is_output_event #"i" #"1" output_event ∧
  check_distrup_list (Import n vc) fmlls Clist b = SOME (fmlls', Clist', b')
  ⇒
  resume_ok st (events ++ import_events ++ [output_event]) (aevents ++ [Import n vc]) (SOME (fmlls', Clist', b'))
[~import_None:]
  resume_ok st events aevents NONE ∧
  is_import_events n vc import_events ∧
  is_output_event #"i" #"0" output_event
  ⇒
  resume_ok st (events ++ import_events ++ [output_event]) (aevents ++ [Import n vc]) NONE
[~delete:]
  resume_ok st events aevents (SOME (fmlls, Clist, b)) ∧
  is_delete_events delete_events ∧
  is_output_event #"d" #"1" output_event ∧
  check_distrup_list (Del hints) fmlls Clist b = SOME (fmlls', Clist', b')
  ⇒
  resume_ok st (events ++ delete_events ++ [output_event]) (aevents ++ [Del hints]) (SOME (fmlls', Clist', b'))
[~delete_None:]
  resume_ok st events aevents NONE ∧
  is_delete_events delete_events ∧
  is_output_event #"d" #"0" output_event
  ⇒
  resume_ok st (events ++ delete_events ++ [output_event]) (aevents ++ [Del hints]) NONE
[~validate:]
  resume_ok st events aevents (SOME (fmlls, Clist, b)) ∧
  is_validate_events validate_events ∧
  is_output_event #"V" #"1" output_event ∧
  check_distrup_list Validate_Unsat fmlls Clist b = SOME (fmlls', Clist', b')
  ⇒
  resume_ok st (events ++ validate_events ++ [output_event]) (aevents ++ [Validate_Unsat]) (SOME (fmlls', Clist', b'))
[~validate_Fail:]
  resume_ok st events aevents (SOME (fmlls, Clist, b)) ∧
  is_validate_events validate_events ∧
  is_output_event #"V" #"0" output_event ∧
  check_distrup_list Validate_Unsat fmlls Clist b = NONE
  ⇒
  resume_ok st (events ++ validate_events ++ [output_event]) (aevents ++ [Validate_Unsat]) NONE
[~validate_None:]
  resume_ok st events aevents NONE ∧
  is_validate_events validate_events ∧
  is_output_event #"V" #"0" output_event
  ⇒
  resume_ok st (events ++ validate_events ++ [output_event]) (aevents ++ [Validate_Unsat]) NONE
End

Inductive step:
[~events_ok_delete:]
  FLOOKUP st.procs id = SOME lst ∧
  events_ok events aevents lst ∧
  resume_ok lst events' [Del hints] lst'
  ⇒
  step st (Act id (Del hints)) (st with procs := st.procs |+ (id,lst'))
[~events_ok_Import:]
  FLOOKUP st.procs id = SOME lst ∧
  events_ok events aevents lst ∧
  resume_ok lst events' [Import n c] lst' ∧
  MEM c st.facts
  ⇒
  step st (Act id (Import n c)) (st with procs := st.procs |+ (id,lst'))
[~events_ok_Produce:]
  FLOOKUP st.procs id = SOME(SOME vlst) ∧
  events_ok events aevents (SOME vlst) ∧
  resume_ok (SOME vlst) events' [Lrup n c hints] (SOME vlst') ∧
  MEM c st.facts
  ⇒
  step st (Act id (Lrup n c hints)) (st with <|procs := st.procs |+ (id,SOME vlst');
                                           facts := c::st.facts|>)
[~events_ok_Produce_fail:]
  FLOOKUP st.procs id = SOME lst ∧
  events_ok events aevents lst ∧
  resume_ok lst events' [Lrup n c hints] NONE
  ⇒
  step st (Act id (Lrup n c hints)) (st with <|procs := st.procs |+ (id,NONE)|>)
[~events_ok_Validate:]
  FLOOKUP st.procs id = SOME(SOME vlst) ∧
  events_ok events aevents (SOME vlst) ∧
  resume_ok (SOME vlst) events' [ValidateUnsat] (SOME vlst')
  ⇒
  step st (Act id (ValidateUnsat)) (st with <|procs := st.procs |+ (id,SOME vlst');
                                              validated := T|>)
[~events_ok_Validate_fail:]
  FLOOKUP st.procs id = SOME lst ∧
  events_ok events aevents lst ∧
  resume_ok lst events' [ValidateUnsat] NONE
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

Theorem resume_ok_NIL:
  resume_ok lst evs [] lst' ⇔ lst = lst' ∧ evs = []
Proof
  rw[Once resume_ok_cases] >>
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
    ∃alb ast'. act_rel label_rel alb clb ∧ step sat_infer (K F) ast alb ast' ∧ state_rel ast' cst'
Proof
  strip_tac >>
  Induct_on ‘step’ >>
  rpt strip_tac
  >~ [‘[Import _ _]’]
  >- (qhdtm_x_assum ‘resume_ok’ $ assume_tac o PURE_ONCE_REWRITE_RULE[resume_ok_cases] >>
      gvs[resume_ok_NIL] >>
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
  >~ [‘resume_ok _ _ [Lrup _ _ _] (SOME _)’]
  >- (qhdtm_x_assum ‘resume_ok’ $ assume_tac o PURE_ONCE_REWRITE_RULE[resume_ok_cases] >>
      gvs[resume_ok_NIL] >>
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
  >~ [‘resume_ok _ _ [Lrup _ _ _] NONE’]
  >- (qhdtm_x_assum ‘resume_ok’ $ assume_tac o PURE_ONCE_REWRITE_RULE[resume_ok_cases] >>
      gvs[resume_ok_NIL] >>
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
  >~ [‘resume_ok _ _ [ValidateUnsat] (SOME _)’]
  >- (qhdtm_x_assum ‘resume_ok’ $ assume_tac o PURE_ONCE_REWRITE_RULE[resume_ok_cases] >>
      gvs[resume_ok_NIL] >>
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
  >~ [‘resume_ok _ _ [ValidateUnsat] NONE’]
  >- (qhdtm_x_assum ‘resume_ok’ $ assume_tac o PURE_ONCE_REWRITE_RULE[resume_ok_cases] >>
      gvs[resume_ok_NIL] >>
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
  qhdtm_x_assum ‘resume_ok’ $ assume_tac o PURE_ONCE_REWRITE_RULE[resume_ok_cases] >>
  gvs[resume_ok_NIL] >>
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
    ∃ast'. (reduce sat_infer (K F))꙳ ast ast' ∧ state_rel ast' cst'
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

Theorem sat_step_sound:
  reduce꙳ st st' ∧
  (∀name facts. name ∈ FDOM st.procs ⇒ ∃n k. FLOOKUP st.procs name = SOME(SOME (REPLICATE n NONE, REPLICATE k 0w, 1w))) ∧
  set st.facts = oprems ∧
  ¬st.validated ∧
  st'.validated
  ⇒
  sat_infer oprems (Vector [])
Proof
  rpt strip_tac >>
  irule $ INST_TYPE [alpha |-> “:num”, beta |-> alpha] sat_step_sound >>
  qexists ‘K F’ >>
  simp[] >>
  Q.SUBGOAL_THEN ‘∃ast. state_rel ast st’ strip_assume_tac
  >- (rw[state_rel_def] >>
      Q.REFINE_EXISTS_TAC ‘<| procs := _; facts := _; validated := _|>’ >>
      simp[] >>
      qexists ‘FUN_FMAP (K $ SOME FEMPTY) (FDOM st.procs)’ >>
      rw[fmap_rel_def,FUN_FMAP_DEF] >>
      gvs[flookup_thm] >>
      first_x_assum drule >>
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
  gvs[FDOM_FLOOKUP,SF DNF_ss] >>
  last_x_assum drule >>
  rw[] >>
  Q.SUBGOAL_THEN ‘facts = FEMPTY’ SUBST_ALL_TAC
  >- (rw[fmap_eq_flookup] >>
      gvs[ccnf_listTheory.fml_rel_def,any_el_ALT] >>
      rename1 ‘FLOOKUP _ m’ >>
      first_x_assum $ qspec_then ‘m’ mp_tac >>
      rw[EL_REPLICATE]) >>
  rw[]
QED
