(*
  A few properties about the relational big-step semantics.
*)
open preamble;
open semanticPrimitivesTheory semanticPrimitivesPropsTheory;
open bigStepTheory evaluatePropsTheory;

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
     evaluate_dec ck env st d r ⇒ (st.eval_state = NONE ⇔ (FST r).eval_state = NONE)) ∧
  (∀ck env ^st ds r.
     evaluate_decs ck env st ds r ⇒ (st.eval_state = NONE ⇔ (FST r).eval_state = NONE))
Proof
  ho_match_mp_tac bigStepTheory.evaluate_dec_ind >> srw_tac[][] >>
  imp_res_tac evaluate_no_new_types_exns >> gvs [] >>
  gvs [declare_env_def,AllCaseEqs()]
QED

Theorem big_evaluate_io_events_mono:
  (∀ck env ^st e r.
    evaluate ck env st e r ⇒
    io_events_mono (st.ffi) (FST r).ffi) ∧
  (∀ck env ^st es r.
    evaluate_list ck env st es r ⇒
    io_events_mono (st.ffi) (FST r).ffi) ∧
  (∀ck env ^st v pes err_v r.
    evaluate_match ck env st v pes err_v r ⇒
    io_events_mono (st.ffi) (FST r).ffi)
Proof
  ho_match_mp_tac evaluate_ind >> rw[]
  >~ [`do_app`]
  >- (
    drule do_app_io_events_mono >> rw[] >>
    metis_tac[io_events_mono_trans]
    ) >>
  TRY (rename1 ‘opClass op Icing’ >>
       drule do_app_io_events_mono >> rw[]) >>
  TRY (rename1 ‘opClass op Reals’ >>
       drule do_app_io_events_mono >> rw[]) >>
  metis_tac[io_events_mono_trans]
QED

Theorem evaluate_dec_io_events_mono:
  (∀ck env ^st d r.
    evaluate_dec ck env st d r ⇒
    io_events_mono (st.ffi) (FST r).ffi) ∧
  (∀ck env ^st ds r.
    evaluate_decs ck env st ds r ⇒
    io_events_mono (st.ffi) (FST r).ffi)
Proof
  ho_match_mp_tac evaluate_dec_ind >> rw[] >>
  imp_res_tac big_evaluate_io_events_mono >> gvs[] >>
  metis_tac[io_events_mono_trans]
QED


val _ = export_theory ();
