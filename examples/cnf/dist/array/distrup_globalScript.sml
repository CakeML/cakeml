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
[~events_ok_step:]
  FLOOKUP st.procs id = SOME lst ∧
  events_ok events aevents lst ∧
  events_ok events' (aevents ++ [alpha]) lst' ∧
  (∀n c. alpha ≠ Import n c)
  ⇒
  step st (Act id alpha) (st with procs := st.procs |+ (id,lst'))
[~events_ok_Import:]
  FLOOKUP st.procs id = SOME lst ∧
  events_ok events aevents lst ∧
  events_ok events' (aevents ++ [Import n c]) lst' ∧
  MEM c st.facts
  ⇒
  step st (Act id (Import n c)) (st with procs := st.procs |+ (id,lst'))
[~events_ok_Produce:]
  FLOOKUP st.procs id = SOME(SOME vlst) ∧
  events_ok events aevents (SOME vlst) ∧
  events_ok events' (aevents ++ [Lrup n c hints]) (SOME vlst') ∧
  MEM c st.facts
  ⇒
  step st (Act id (Lrup n c hints)) (st with <|procs := st.procs |+ (id,SOME vlst');
                                           facts := c::st.facts|>)
End

Definition reduce_def:
  reduce st st' = ∃l. step st l st'
End

(*((int vector option list # word8 list # word8) option)*)
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

Theorem state_rel_step:
  ∀cst clb cst' ast.
    state_rel ast cst ∧ distrup_global$step cst clb cst' ⇒
    ∃alb ast'. act_rel label_rel alb clb ∧ step sat_infer (K F) ast alb ast' ∧ state_rel ast' cst'
Proof
  cheat
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
  (∀name facts. name ∈ FDOM st.procs ⇒ ∃n k. FLOOKUP st.procs name = SOME(SOME (REPLICATE n NONE, REPLICATE k 0w, b))) ∧
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
      cheat (* TODO: fix events_ok *)) >>
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
