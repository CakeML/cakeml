open preamble funBigStepTheory interpTheory semanticPrimitivesTheory
open terminationTheory

val _ = new_theory"funBigStepEquiv"

(* TODO: move *)
val merge_alist_mod_env_empty = Q.store_thm("merge_alist_mod_env_empty[simp]",
  `merge_alist_mod_env ([],[]) x = x`,
  Cases_on`x`>>EVAL_TAC)
(* -- *)

val evaluate_eq_run_eval_list = Q.store_thm("evaluate_eq_run_eval_list",
  `(∀s env e. evaluate s env e = run_eval_list env e s) ∧
   (∀s env v e errv.
     evaluate_match s env v e errv =
     (I ## list_result) (run_eval_match env v e errv s))`,
  ho_match_mp_tac evaluate_ind >>
  rw[evaluate_def,run_eval_def,
     result_return_def,result_bind_def] >>
  every_case_tac >> fs[] >> rw[] >>
  fs[Bindv_def] >>
  fs[result_raise_def,list_result_def] >> rw[] >>
  (TRY (
    qmatch_assum_rename_tac`get_store st = _` >>
    fs[get_store_def]>>rw[])) >>
  (TRY
    (CHANGED_TAC (imp_res_tac evalPropsTheory.do_con_check_build_conv) >>
     TRY (
       qmatch_assum_abbrev_tac`build_conv _ _ vs = _` >>
       first_x_assum(qspec_then`vs`strip_assume_tac) >>
       unabbrev_all_tac >> fs[] ) >>
     rw[] >>
     fs[build_conv_def] >>
     rfs[] >> rw[] >>
     fs[do_con_check_def])) >>
   TRY(fs[do_con_check_def]>>NO_TAC) >>
   every_case_tac >> fs[dec_clock_def,funBigStepTheory.dec_clock_def] >> rfs[] >>
   fs[state_transformerTheory.UNIT_DEF] >> rw[list_result_def] >>
   fs[set_store_def] >> rw[] >>
   fs[FST_triple])

val functional_evaluate_list = Q.store_thm("functional_evaluate_list",
  `evaluate s env es = (s',r) ⇔ evaluate_list T env s es (s',r)`,
  rw[evaluate_run_eval_list,evaluate_eq_run_eval_list])

val evaluate_decs_eq_run_eval_decs = Q.store_thm("evaluate_decs_eq_run_eval_decs",
  `∀mn s env decs r tds s'.
      evaluate_decs mn s env decs = run_eval_decs mn env s decs`,
  recInduct evaluate_decs_ind >>
  rw[evaluate_decs_def,run_eval_decs_def,run_eval_dec_def] >>
  every_case_tac >>
  fs[combine_dec_result_def,evaluate_eq_run_eval_list] >>
  TRY(
    fs[run_eval_def,result_bind_def,result_return_def] >>
    rw[] >> fs[FST_triple,type_defs_to_new_tdecs_def] >>
    rfs[] >> NO_TAC) >>
  every_case_tac >> fs[functional_evaluate_list]);

val functional_evaluate_decs = Q.store_thm("functional_evaluate_decs",
  `evaluate_decs mn s env decs = (s',cenv,r) ⇒
   evaluate_decs T mn env s decs (s',cenv,r)`,
  rw[evaluate_decs_eq_run_eval_decs,run_eval_decs_spec])

(*
val evaluate_tops_eq_run_eval_prog = Q.store_thm("evaluate_tops_eq_run_eval_prog",
  `∀tops env s r cenv s' t' m'.
    evaluate_tops tops env s = (r,cenv,((s',t'),m')) ⇔
    run_eval_prog env (state_to_cst (FST(FST s)),(SND(FST s)),SND s) tops =
    ((state_to_cst s',t',m'),cenv,r)`,
  recInduct evaluate_tops_ind >>
  rw[evaluate_tops_def,run_eval_prog_def,run_eval_top_def] >-
    ( rw[EQ_IMP_THM,PAIR_FST_SND_EQ] )
  >- (
    every_case_tac >>
    fs[semanticPrimitivesTheory.combine_mod_result_def] >>
    every_case_tac >>
    fs[semanticPrimitivesTheory.all_env_to_menv_def,
       semanticPrimitivesTheory.all_env_to_cenv_def,
       semanticPrimitivesTheory.all_env_to_env_def,
       evalPropsTheory.merge_alist_mod_env_empty_assoc,
       evaluate_decs_eq_run_eval_decs,run_eval_decs_def,
       semanticPrimitivesTheory.combine_mod_result_def] >>
    metis_tac[PAIR,FST,SND,
              semanticPrimitivesTheory.merge_alist_mod_env_def,APPEND,APPEND_ASSOC,
              semanticPrimitivesTheory.result_11,
              semanticPrimitivesTheory.result_distinct])>>
  every_case_tac >>
  fs[evaluate_decs_eq_run_eval_decs,run_eval_decs_def] >>
  rw[] >>
  fs[semanticPrimitivesTheory.combine_dec_result_def,
     semanticPrimitivesTheory.merge_alist_mod_env_def] >>
  rw[EQ_IMP_THM]>>fs[])

val functional_evaluate_tops = Q.store_thm("functional_evaluate_tops",
  `evaluate_tops tops env ((s,tdecs),mdecs) = (r,cenv,((s',tdecs'),mdecs')) ⇒
   evaluate_prog T env (state_to_cst s,tdecs,mdecs) tops ((state_to_cst s',tdecs',mdecs'),cenv,r)`,
  rw[evaluate_tops_eq_run_eval_prog,run_eval_prog_spec])

val functional_evaluate_prog = Q.store_thm("functional_evaluate_prog",
  `evaluate_prog prog env s = (r,cenv,s') ⇒
   evaluate_whole_prog T env (convert_prog_state s) prog ((convert_prog_state s'),cenv,r)`,
  rw[evaluate_prog_def,bigStepTheory.evaluate_whole_prog_def] >>
  PairCases_on`s`>>PairCases_on`s'`>>
  imp_res_tac functional_evaluate_tops >>
  fs[convert_prog_state_def,state_to_cst_def])
*)

val _ = export_theory()
