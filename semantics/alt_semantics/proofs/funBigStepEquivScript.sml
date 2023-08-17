(*
  Relate functional big-step semantics with relational big-step
  semantics.
*)
open preamble evaluateTheory evaluatePropsTheory
     interpTheory semanticPrimitivesTheory fpSemPropsTheory;

val _ = new_theory"funBigStepEquiv"

val s = ``s:'ffi state``;

val prove_tac =
  every_case_tac >> fs[] >> rw[] >> gvs [] >>
  imp_res_tac evaluatePropsTheory.eval_no_eval_simulation >> gvs [] >>
  rpt (qpat_x_assum ‘∀x. _’ kall_tac) >>
  fs[] >> fs[result_raise_def,list_result_def] >> rw[] >>
  (TRY (
    qmatch_assum_rename_tac`get_store st = _` >>
    fs[get_store_def]>>rw[])) >>
  (TRY
   (CHANGED_TAC (imp_res_tac semanticPrimitivesPropsTheory.do_con_check_build_conv) >>
    TRY (
      qmatch_assum_abbrev_tac`build_conv _ _ vs = _` >>
      first_x_assum(qspec_then`vs`strip_assume_tac) >>
      unabbrev_all_tac >> fs[] ) >>
    rw[] >>
    fs[build_conv_def] >>
    rfs[] >> rw[] >>
    fs[do_con_check_def])) >>
  TRY(fs[do_con_check_def]>>NO_TAC) >>
  every_case_tac >> fs[dec_clock_def,evaluateTheory.dec_clock_def] >> rfs[] >>
  fs[state_transformerTheory.UNIT_DEF] >> rw[list_result_def] >>
  fs[set_store_def] >> rw[] >>
  fs[FST_triple] >>
  gvs [do_eval_res_def,do_eval_def] >>
  gvs [do_app_def,AllCaseEqs()];

Theorem evaluate_eq_run_eval_list:
  (∀^s env e.
    s.eval_state = NONE ⇒
    evaluate s env e = run_eval_list env e s) ∧
  (∀^s env v e errv.
    s.eval_state = NONE ⇒
    evaluate_match s env v e errv =
    (I ## list_result) (run_eval_match env v e errv s))
Proof
  ho_match_mp_tac evaluate_ind >>
  rw[evaluate_def,run_eval_def,
     result_return_def,result_bind_def, Excl"getOpClass_def"] >> gvs [Excl"getOpClass_def"]
  >~[‘getOpClass op’]
  >- (
    ntac 3 TOP_CASE_TAC >> gs[Excl"getOpClass_def"]
    >- prove_tac
    >- prove_tac
    >- prove_tac
    >- (gs[get_store_def] >>
        ntac 4 (TOP_CASE_TAC >>
                gs[result_raise_def, set_store_def, state_transformerTheory.UNIT_DEF, shift_fp_opts_def]) >>
        every_case_tac >> gs[]) >>
    gs[get_store_def, Excl"getOpClass_def"] >>
    imp_res_tac (INST_TYPE [alpha |-> “:'ffi”, beta |-> “:'ffi”] fpSemPropsTheory.realOp_determ) >>
    ntac 5 (TOP_CASE_TAC >>
            gs[result_raise_def, set_store_def, state_transformerTheory.UNIT_DEF, shift_fp_opts_def]) >>
    res_tac >> gs[state_component_equality]) >>
   TRY (rpt $ pop_assum mp_tac >>
        ntac 2 (TOP_CASE_TAC >> gs[do_fpoptimise_LENGTH]) >> NO_TAC) >>
  prove_tac
QED

Theorem functional_evaluate_list:
  s.eval_state = NONE ⇒
  (evaluate s env es = (s',r) ⇔ evaluate_list T env s es (s',r))
Proof
  rw[evaluate_run_eval_list,evaluate_eq_run_eval_list]
QED

Theorem functional_evaluate_match:
  s.eval_state = NONE ⇒
  (evaluate_match s env v pes errv = (s',list_result r) ⇔
     evaluate_match T env s v pes errv (s',r))
Proof
  rw[evaluate_run_eval_match,evaluate_eq_run_eval_list] >>
  Cases_on`run_eval_match env v pes errv s`>>rw[] >>
  Cases_on`r`>>Cases_on`r'`>>rw[list_result_def]
QED

Theorem evaluate_decs_eq_run_eval_decs:
  ∀s env decs r tds s'.
    (s.eval_state = NONE ⇒
     evaluate_decs s env decs = run_eval_decs env s decs)
Proof
  recInduct evaluate_decs_ind >>
  rw[evaluate_decs_def,run_eval_dec_def,run_eval_dec_def] >>
  every_case_tac >>
  fs[combine_dec_result_def,evaluate_eq_run_eval_list] >>
  TRY(
    fs[run_eval_def,result_bind_def,result_return_def] >>
    rw[] >> fs[FST_triple] >>
    rfs[] >> NO_TAC) >>
  every_case_tac >> fs[functional_evaluate_list] >>
  imp_res_tac evaluatePropsTheory.eval_no_eval_simulation >> gvs [] >>
  rpt (qpat_x_assum ‘∀x. _’ kall_tac) >>
  imp_res_tac evaluatePropsTheory.eval_no_eval_simulation >> gvs [] >>
  rpt (qpat_x_assum ‘∀x. _’ kall_tac) >>
  gvs [evaluate_eq_run_eval_list] >>
  gvs [run_eval_def,result_return_def,result_bind_def] >>
  gvs [EVERY_MEM,EXISTS_MEM]
QED

Theorem functional_evaluate_decs:
  s.eval_state = NONE ⇒
  (evaluate_decs s env decs = (s',r) ⇔
   evaluate_decs T env s decs (s',r))
Proof
  rw[evaluate_decs_eq_run_eval_decs,evaluate_decs_run_eval_decs]
QED

Theorem functional_evaluate:
  s.eval_state = NONE ⇒
  (evaluate T env s e (s',r) ⇔ evaluate s env [e] = (s',list_result r))
Proof
  functional_evaluate_list |> Q.GENL[`es`,`r`] |> qspec_then`[e]`mp_tac \\
  ntac 6 (simp[Once (CONJUNCT2 bigStepTheory.evaluate_cases)]) \\
  Cases_on`r` \\ fs[]
QED

val _ = export_theory()
