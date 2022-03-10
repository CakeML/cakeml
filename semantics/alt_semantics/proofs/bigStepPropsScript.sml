(*
  A few properties about the relational big-step semantics.
*)
open preamble;
open semanticPrimitivesTheory ffiTheory semanticPrimitivesPropsTheory;
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

Theorem evaluate_ignores_types_exns_eval:
  (∀ck env ^st e r.
     evaluate ck env st e r ⇒
     ∀x y z.
      evaluate ck env
        (st with <| next_type_stamp := x; next_exn_stamp := y; eval_state := z |>) e
        ((FST r) with <| next_type_stamp := x; next_exn_stamp := y; eval_state := z|>,
          SND r)) ∧
  (∀ck env ^st es r.
     evaluate_list ck env st es r ⇒
     ∀x y z. evaluate_list ck env
        (st with <| next_type_stamp := x; next_exn_stamp := y; eval_state := z |>) es
        ((FST r) with <| next_type_stamp := x; next_exn_stamp := y; eval_state := z|>,
          SND r)) ∧
  (∀ck env ^st v pes err_v r.
     evaluate_match ck env st v pes err_v r ⇒
     ∀x y z. evaluate_match ck env
        (st with <| next_type_stamp := x; next_exn_stamp := y; eval_state := z |>)
        v pes err_v
        ((FST r) with <| next_type_stamp := x; next_exn_stamp := y; eval_state := z|>,
          SND r))
Proof
  ho_match_mp_tac bigStepTheory.evaluate_ind >>
  rw[] >> rw[Once evaluate_cases, state_component_equality] >>
  metis_tac[state_accfupds, K_DEF]
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

Theorem evaluate_io_events_mono:
  (∀ck env ^st e r.
    evaluate ck env st e r ⇒
    st.ffi.io_events ≼ (FST r).ffi.io_events) ∧
  (∀ck env ^st es r.
    evaluate_list ck env st es r ⇒
    st.ffi.io_events ≼ (FST r).ffi.io_events) ∧
  (∀ck env ^st v pes err_v r.
    evaluate_match ck env st v pes err_v r ⇒
    st.ffi.io_events ≼ (FST r).ffi.io_events)
Proof
  ho_match_mp_tac evaluate_ind >> rw[]
  >~ [`do_app`]
  >- (
    Cases_on `∀s. op ≠ FFI s` >> gvs[]
    >- (drule_all do_app_ffi_unchanged >> rw[] >> gvs[]) >>
    gvs[do_app_def] >> every_case_tac >> gvs[] >>
    gvs[call_FFI_def] >> every_case_tac >> gvs[IS_PREFIX_APPEND]
    ) >>
  metis_tac[IS_PREFIX_TRANS]
QED


val _ = export_theory ();
