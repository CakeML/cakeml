open preamble closLangTheory closSemTheory closPropsTheory closRelationTheory;

val _ = new_theory "closOpt";

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

(* This isn't true because the relation requires the functions to be related for
 * all possible applications, including (App SOME). This is necessary in general since
 * there might be (App SOMEs) in the program. I'll probably have to add a
 * modality to the relation to handle this.
val fn_add_arg = Q.store_thm ("fn_add_arg",
`!loc vars num_args num_args' e.
  num_args ≠ 0 ∧ 
  num_args' ≠ 0 ∧
  num_args + num_args' ≤ max_app ⇒
  exp_rel [Fn loc vars num_args (Fn loc vars num_args' e)]
          [Fn loc vars (num_args + num_args') e]`,

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
 Cases_on `loc'` >>
 fs [check_loc_def] >>
 rw [res_rel_rw] >>
 fs []
 *)

val _ = export_theory ();
