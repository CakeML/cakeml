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

Definition label_rel_def:
  label_rel = ARB
End

Theorem state_rel_step:
  ∀ast cst alb.
    state_rel ast cst ∧ label_rel alb clb ∧ step cst clb cst' ⇒
    ∃ast'. step sat_infer (K F) ast alb ast' ∧ state_rel ast' cst'
Proof
  cheat
QED

Theorem sat_step_sound:
  reduce꙳ st st' ∧
  (∀name facts. ∃n k. FLOOKUP st.procs name = SOME(SOME (REPLICATE n NONE, REPLICATE k 0w, b))) ∧
  set st.facts = oprems ∧
  ¬st.validated ∧
  st'.validated
  ⇒
  sat_infer oprems (Vector [])
Proof
  cheat
QED
