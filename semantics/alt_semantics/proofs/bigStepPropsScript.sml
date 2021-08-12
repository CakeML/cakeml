(*
  A few properties about the relational big-step semantics.
*)
open preamble;
open semanticPrimitivesTheory;
open bigStepTheory;

val _ = new_theory "bigStepProps";

val st = ``st:'ffi state``

Theorem evaluate_no_new_types_exns:
  (∀ck env ^st e r.
     evaluate ck env st e r ⇒
     st.next_type_stamp = (FST r).next_type_stamp ∧
     st.next_exn_stamp = (FST r).next_exn_stamp ∧
     st.eval_state = (FST r).eval_state) ∧
  (∀ck env ^st es r.
     evaluate_list ck env st es r ⇒
     st.next_type_stamp = (FST r).next_type_stamp ∧
     st.next_exn_stamp = (FST r).next_exn_stamp ∧
     st.eval_state = (FST r).eval_state) ∧
  (∀ck env ^st v pes err_v r.
     evaluate_match ck env st v pes err_v r ⇒
     st.next_type_stamp = (FST r).next_type_stamp ∧
     st.next_exn_stamp = (FST r).next_exn_stamp ∧
     st.eval_state = (FST r).eval_state)
Proof
  ho_match_mp_tac bigStepTheory.evaluate_ind >>
  srw_tac[][]
QED

Theorem evaluate_ignores_types_exns:
  (∀ck env ^st e r.
     evaluate ck env st e r ⇒
     ∀x y. evaluate ck env (st with <| next_type_stamp := x; next_exn_stamp := y |>) e
                    ((FST r) with <| next_type_stamp := x; next_exn_stamp := y |>, SND r)) ∧
  (∀ck env ^st es r.
     evaluate_list ck env st es r ⇒
     ∀x y. evaluate_list ck env (st with <| next_type_stamp := x; next_exn_stamp := y |>) es
                         ((FST r) with <| next_type_stamp := x; next_exn_stamp := y |>, SND r)) ∧
  (∀ck env ^st v pes err_v r.
     evaluate_match ck env st v pes err_v r ⇒
     ∀x y. evaluate_match ck env (st with <| next_type_stamp := x; next_exn_stamp := y |>) v pes err_v
                          ((FST r) with <| next_type_stamp := x; next_exn_stamp := y |>, SND r))
Proof
  ho_match_mp_tac bigStepTheory.evaluate_ind >>
  srw_tac[][] >>
  srw_tac[][Once evaluate_cases, state_component_equality] >>
  metis_tac [state_accfupds, K_DEF]
QED

Theorem evaluate_dec_eval_state:
  (∀ck env ^st d r.
     evaluate_dec ck env st d r ⇒ st.eval_state = NONE ⇒ (FST r).eval_state = NONE) ∧
  (∀ck env ^st ds r.
     evaluate_decs ck env st ds r ⇒ st.eval_state = NONE ⇒ (FST r).eval_state = NONE)
Proof
  ho_match_mp_tac bigStepTheory.evaluate_dec_ind >> srw_tac[][] >>
  imp_res_tac evaluate_no_new_types_exns >> gvs [] >>
  gvs [declare_env_def,AllCaseEqs()]
QED

val _ = export_theory ();
