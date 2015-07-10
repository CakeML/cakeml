open preamble closLangTheory closSemTheory closPropsTheory closRelationTheory;

val _ = new_theory "closOpt";

val rev_take_rev_all = Q.prove (
`n = LENGTH l ⇒ REVERSE (TAKE n (REVERSE l)) = l`,
 `LAST_N (LENGTH l) l = l` by simp [LAST_N_LENGTH] >>
 rfs [] >>
 simp [GSYM LAST_N_def, LAST_N_LENGTH]);

val rev_drop_rev_all = Q.prove (
`n = LENGTH l ⇒ REVERSE (DROP n (REVERSE l)) = []`,
 fs [DROP_REVERSE, BUTLASTN_LENGTH_NIL]);

val add_opt = Q.store_thm ("add_opt",
`!n1 n2. exp_rel [Op Add [Op (Const n1) []; Op (Const n2) []]] [Op (Const (n2 + n1)) []]`,
 rw [exp_rel_def, exec_rel_rw, evaluate_def, do_app_def, res_rel_rw, val_rel_rw] >>
 metis_tac [val_rel_mono]);

val sub_opt = Q.store_thm ("sub_opt",
`!n1 n2. exp_rel [Op Sub [Op (Const n1) []; Op (Const n2) []]] [Op (Const (n2 - n1)) []]`,
 rw [exp_rel_def, exec_rel_rw, evaluate_def, do_app_def, res_rel_rw, val_rel_rw] >>
 metis_tac [val_rel_mono]);

val mult_opt = Q.store_thm ("mult_opt",
`!n1 n2. exp_rel [Op Mult [Op (Const n1) []; Op (Const n2) []]] [Op (Const (n2 * n1)) []]`,
 rw [exp_rel_def, exec_rel_rw, evaluate_def, do_app_def, res_rel_rw, val_rel_rw] >>
 metis_tac [val_rel_mono]);

val div_opt = Q.store_thm ("div_opt",
`!n1 n2. exp_rel [Op Div [Op (Const n1) []; Op (Const n2) []]] [Op (Const (n2 / n1)) []]`,
 rw [exp_rel_def, exec_rel_rw, evaluate_def, do_app_def, res_rel_rw, val_rel_rw] >>
 rw [res_rel_rw, val_rel_rw] >>
 metis_tac [val_rel_mono]);

val mod_opt = Q.store_thm ("mod_opt",
`!n1 n2. exp_rel [Op Mod [Op (Const n1) []; Op (Const n2) []]] [Op (Const (n2 % n1)) []]`,
 rw [exp_rel_def, exec_rel_rw, evaluate_def, do_app_def, res_rel_rw, val_rel_rw] >>
 rw [res_rel_rw, val_rel_rw] >>
 metis_tac [val_rel_mono]);

val less_opt = Q.store_thm ("less_opt",
`!n1 n2. 
  exp_rel [Op Less [Op (Const n1) []; Op (Const n2) []]] 
          [Op (Cons (if n2 < n1 then true_tag else false_tag)) []]`,
 rw [exp_rel_def, exec_rel_rw, evaluate_def, do_app_def, res_rel_rw, val_rel_rw, Boolv_def] >>
 metis_tac [val_rel_mono]);

val leq_opt = Q.store_thm ("leq_opt",
`!n1 n2. 
  exp_rel [Op LessEq [Op (Const n1) []; Op (Const n2) []]] 
          [Op (Cons (if n2 ≤ n1 then true_tag else false_tag)) []]`,
 rw [exp_rel_def, exec_rel_rw, evaluate_def, do_app_def, res_rel_rw, val_rel_rw, Boolv_def] >>
 metis_tac [val_rel_mono]);

val greater_opt = Q.store_thm ("greater_opt",
`!n1 n2. 
  exp_rel [Op Greater [Op (Const n1) []; Op (Const n2) []]] 
          [Op (Cons (if n2 > n1 then true_tag else false_tag)) []]`,
 rw [exp_rel_def, exec_rel_rw, evaluate_def, do_app_def, res_rel_rw, val_rel_rw, Boolv_def] >>
 metis_tac [val_rel_mono]);

val geq_opt = Q.store_thm ("geq_opt",
`!n1 n2. 
  exp_rel [Op GreaterEq [Op (Const n1) []; Op (Const n2) []]] 
          [Op (Cons (if n2 ≥ n1 then true_tag else false_tag)) []]`,
 rw [exp_rel_def, exec_rel_rw, evaluate_def, do_app_def, res_rel_rw, val_rel_rw, Boolv_def] >>
 metis_tac [val_rel_mono]);

(* This cheat isn't true, because the theorem isn't right with respect to the vars *)
val fn_add_arg = Q.store_thm ("fn_add_arg",
`!vars num_args num_args' e.
  num_args ≠ 0 ∧ 
  num_args' ≠ 0 ∧
  num_args + num_args' ≤ max_app ⇒
  exp_rel [Fn NONE vars num_args (Fn NONE vars num_args' e)]
          [Fn NONE vars (num_args + num_args') e]`,
 rw [exp_rel_def, exec_rel_rw, evaluate_def] >>
 rw [res_rel_rw] >>
 Cases_on `clos_env s.restrict_envs vars env` >>
 fs [res_rel_rw] >>
 `s'.restrict_envs = s.restrict_envs` by fs [Once state_rel_rw] >>
 imp_res_tac val_rel_clos_env >>
 imp_res_tac val_rel_mono >>
 rw [val_rel_rw, is_closure_def, closure_to_num_args_def] >>
 imp_res_tac LIST_REL_LENGTH >>
 `args ≠ [] ∧ args' ≠ []` by (Cases_on `args` >> Cases_on `args'` >> fs []) >>
 rw [exec_rel_rw, evaluate_app_rw, dest_closure_def, res_rel_rw] >>
 rw [res_rel_rw] >>
 Cases_on `loc` >>
 fs [check_loc_def] >>
 rw [res_rel_rw] >>
 fs []
 >- metis_tac [val_rel_mono, ZERO_LESS_EQ] >> 
 simp [evaluate_def, rev_take_rev_all] >>
 CASE_TAC >>
 rw [res_rel_rw] >>
 simp [rev_drop_rev_all] >>
 simp [evaluate_def , res_rel_rw, dec_clock_def] >>
 `i''' - LENGTH args' ≤ i''` by decide_tac >>
 imp_res_tac val_rel_mono >>
 simp [] >>
 rw [val_rel_rw, is_closure_def, closure_to_num_args_def, exec_rel_rw] >>
 `args'' ≠ [] ∧ args''' ≠ []` by (Cases_on `args''` >> Cases_on `args'''` >> fs []) >>
 simp [evaluate_app_rw, dest_closure_def] >>
 Cases_on `loc` >>
 fs [check_loc_def] >>
 rw [res_rel_rw] >>
 fs [] >>
 imp_res_tac LIST_REL_LENGTH >>
 Cases_on `i''''' < LENGTH args''` >>
 simp [res_rel_rw]
 >- metis_tac [val_rel_mono, ZERO_LESS_EQ]
 >- (simp [rev_take_rev_all, rev_drop_rev_all, dec_clock_def] >>
     qabbrev_tac `l = LENGTH args'''` >>
     `LENGTH args'' = l` by metis_tac [] >>
     `exp_rel [e] [e]` by metis_tac [exp_rel_refl] >>
     fs [exp_rel_def] >>
     pop_assum (qspecl_then [`i''''' - l`,
                             `args''++x'`,
                             `args''' ++ args' ++ vs2'`,
                             `s''''`,
                             `s'''''`] mp_tac) >>
     `i''''' - l ≤ i''''` by decide_tac >>
     imp_res_tac val_rel_mono >>
     simp [] >>
     `LIST_REL (val_rel (i''''' − l)) (args'' ++ x') (args''' ++ args' ++ vs2')`
             by cheat >>
     simp [exec_rel_rw] >>
     DISCH_TAC >>
     pop_assum (qspec_then `i'''''-l` mp_tac) >>
     simp [] >>
     reverse (strip_assume_tac (Q.ISPEC `evaluate ([e],args'' ++ x',s'''' with clock := i''''' − l)`
                         result_store_cases)) >>
     simp [res_rel_rw] >>
     DISCH_TAC >>
     fs []
     >- metis_tac [] >>
     imp_res_tac evaluate_SING >>
     fs [] >>
     rw [evaluate_def, res_rel_rw])
 >- metis_tac [val_rel_mono, ZERO_LESS_EQ]
 >- metis_tac [val_rel_mono, ZERO_LESS_EQ]
 >- metis_tac [val_rel_mono, ZERO_LESS_EQ]
 >- metis_tac [val_rel_mono, ZERO_LESS_EQ]);


val _ = export_theory ();
