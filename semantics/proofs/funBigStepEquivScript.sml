open preamble funBigStepTheory interpTheory
open terminationTheory

val _ = new_theory"funBigStepEquiv"

val cst_to_state_def = Define`
  cst_to_state ((c,s,t):v count_store_trace) =
    <| clock := c; refs := s; io := t |>`;
val state_to_cst_def = Define`
  state_to_cst s = (s.clock,s.refs,s.io)`;
val swap_result_def = Define`
  swap_result (s,r) = (r,cst_to_state s)`;

val cst_to_state_to_cst = Q.store_thm("cst_to_state_to_cst[simp]",
  `cst_to_state (state_to_cst s) = s`,
  EVAL_TAC >> simp[state_component_equality]);
val state_to_cst_to_state = Q.store_thm("state_to_cst_to_state[simp]",
  `state_to_cst (cst_to_state s) = s`,
  PairCases_on`s`>>EVAL_TAC)

val dec_clock_cst_to_state = Q.store_thm("dec_clock_cst_to_state[simp]",
  `dec_clock (cst_to_state s) = cst_to_state (FST (dec_clock s))`,
  PairCases_on`s`>> EVAL_TAC>>rw[cst_to_state_def]);

val get_store_state_to_cst = Q.store_thm("get_store_state_to_cst",
  `get_store (state_to_cst s) = (state_to_cst s,Rval (s.refs,s.io))`,
  EVAL_TAC)

val cst_to_state_components = Q.store_thm("cst_to_state_components[simp]",
  `(cst_to_state p).clock = FST p ∧
   (cst_to_state p).refs = FST(SND p) ∧
   (cst_to_state p).io = SND(SND p)`,
  PairCases_on`p`>>EVAL_TAC);

val all_env_with_env_thm = Q.store_thm("all_env_with_env_thm",
  `all_env_with_env env a = (all_env_to_menv env,all_env_to_cenv env,a)`,
  PairCases_on`env`>>EVAL_TAC)

val evaluate_eq_run_eval = Q.store_thm("evaluate_eq_run_eval",
  `(∀p. evaluate p = swap_result (run_eval_list (FST(SND p)) (FST p) (state_to_cst (SND(SND p))))) ∧
   (∀p. evaluate_match p = (list_result ## I) (swap_result
     (run_eval_match (FST(SND(SND(SND p)))) (FST(SND p)) (FST p) (FST(SND(SND p)))
       (state_to_cst (SND(SND(SND(SND p))))))))`,
  ho_match_mp_tac evaluate_ind >>
  rw[evaluate_def,run_eval_def,swap_result_def,
     result_return_def,result_bind_def,get_store_state_to_cst] >>
  every_case_tac >>
  fs[swap_result_def] >> rw[] >>
  fs[semanticPrimitivesTheory.Bindv_def] >>
  fs[swap_result_def,result_raise_def,list_result_def] >> rw[] >>
  (TRY (
    qmatch_assum_rename_tac`get_store st = _` >>
    PairCases_on`st`>>fs[get_store_def]>>rw[])) >>
  (TRY
    (CHANGED_TAC (imp_res_tac evalPropsTheory.do_con_check_build_conv) >>
     TRY (
       qmatch_assum_abbrev_tac`build_conv _ _ vs = _` >>
       first_x_assum(qspec_then`vs`strip_assume_tac) >>
       unabbrev_all_tac >> fs[] ) >>
     rw[] >>
     fs[semanticPrimitivesTheory.build_conv_def] >>
     rfs[] >> rw[] >>
     fs[semanticPrimitivesTheory.do_con_check_def])) >>
   TRY(fs[semanticPrimitivesTheory.do_con_check_def]>>NO_TAC) >>
   TRY(fs[dec_clock_def,swap_result_def]>>NO_TAC)>>
   every_case_tac >> fs[swap_result_def,dec_clock_def,all_env_with_env_thm] >> rfs[] >>
   fs[state_transformerTheory.UNIT_DEF] >> rw[list_result_def] >>
   fs[set_store_def] >> rw[] >>
   fs[cst_to_state_def,FST_triple])

val functional_evaluate_list = Q.store_thm("functional_evaluate_list",
  `evaluate (es,env,s) = (r,s') ⇔ evaluate_list T env (state_to_cst s) es (state_to_cst s',r)`,
  rw[evaluate_run_eval_list,evaluate_eq_run_eval] >>
  Cases_on`run_eval_list env es (state_to_cst s)` >>
  simp[swap_result_def] >>
  metis_tac[cst_to_state_to_cst,state_to_cst_to_state])

val _ = export_theory()
