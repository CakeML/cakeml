open preamble;
open clos_relationTheory clos_relationPropsTheory closPropsTheory clos_mtiTheory;

val _ = new_theory "clos_mtiProof";

val collect_args_correct = Q.prove (
`!num_args e num_args' e' e''.
  collect_args num_args e = (num_args', e') ∧
  exp_rel (:'ffi) [e'] [e'']
  ⇒
  exp_rel (:'ffi) [Fn NONE NONE num_args e] [Fn NONE NONE num_args' e'']`,
 ho_match_mp_tac collect_args_ind >>
 srw_tac[][collect_args_def]
 >- metis_tac [fn_add_arg, exp_rel_trans, exp_rel_refl] >>
 metis_tac [compat]);

val collect_apps_correct = Q.prove (
`!args e args' e' e''.
  collect_apps args e = (args', e') ∧
  exp_rel (:'ffi) [e'] [e''] ∧
  exp_rel (:'ffi) args' args''
  ⇒
  exp_rel (:'ffi) [App NONE e args] [App NONE e'' args'']`,
 ho_match_mp_tac collect_apps_ind >>
 srw_tac[][collect_apps_def]
 >- (
   `exp_rel (:'ffi) [App NONE (App NONE e es) args] [App NONE e (args++es)]`
   by (
     match_mp_tac app_combine >>
     simp [exp_rel_refl]) >>
   metis_tac [exp_rel_trans]) >>
 metis_tac [compat]);

val intro_multi_correct = Q.store_thm ("intro_multi_correct",
`!es. exp_rel (:'ffi) es (intro_multi es)`,
 ho_match_mp_tac intro_multi_ind >>
 srw_tac[][intro_multi_def, compat_nil, compat_var]
 >- metis_tac [compat_cons, intro_multi_sing, HD]
 >- metis_tac [compat_if, intro_multi_sing, HD]
 >- metis_tac [compat_let, intro_multi_sing, HD]
 >- metis_tac [compat_raise, intro_multi_sing, HD]
 >- metis_tac [compat_handle, intro_multi_sing, HD]
 >- metis_tac [compat_tick, intro_multi_sing, HD]
 >- metis_tac [compat_call, intro_multi_sing, HD]
 >- metis_tac [collect_apps_correct, intro_multi_sing, HD]
 >- metis_tac [compat_app, intro_multi_sing, HD]
 >- metis_tac [collect_args_correct, intro_multi_sing, HD]
 >- metis_tac [compat_fn, intro_multi_sing, HD]
 >- metis_tac [compat_fn, intro_multi_sing, HD]
 (* Letrec *)
 >- cheat
 >- metis_tac [compat_op, intro_multi_sing, HD]);

val HD_intro_multi = Q.prove(
  `[HD (intro_multi [e])] = intro_multi [e]`,
  metis_tac[intro_multi_sing,HD])

val contains_App_SOME_collect_args = Q.store_thm("contains_App_SOME_collect_args",
  `∀x y a b. collect_args x y = (a,b) ⇒
    (contains_App_SOME [y] ⇔ contains_App_SOME [b])`,
  ho_match_mp_tac collect_args_ind >>
  srw_tac[][collect_args_def,contains_App_SOME_def] >>
  srw_tac[][contains_App_SOME_def]);

val contains_App_SOME_collect_apps = Q.store_thm("contains_App_SOME_collect_apps",
  `∀x y a b. collect_apps x y = (a,b) ⇒
    (max_app < LENGTH x ∨ contains_App_SOME x ∨ contains_App_SOME [y] ⇔
     max_app < LENGTH a ∨ contains_App_SOME a ∨ contains_App_SOME [b])`,
  ho_match_mp_tac collect_apps_ind >>
  srw_tac[][collect_apps_def,contains_App_SOME_def] >>
  srw_tac[][contains_App_SOME_def] >> full_simp_tac(srw_ss())[] >>
  Cases_on`max_app < LENGTH x`>>full_simp_tac(srw_ss())[] >- DECIDE_TAC >>
  Cases_on`max_app < LENGTH es`>>full_simp_tac(srw_ss())[] >- DECIDE_TAC >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[] >> srw_tac[][] >>
  rpt (pop_assum mp_tac) >>
  ONCE_REWRITE_TAC[contains_App_SOME_EXISTS] >> srw_tac[][] >>
  metis_tac[]);

val contains_App_SOME_intro_multi = Q.store_thm("contains_App_SOME_intro_multi[simp]",
  `∀es. contains_App_SOME (intro_multi es) ⇔ contains_App_SOME es`,
  ho_match_mp_tac intro_multi_ind >>
  srw_tac[][intro_multi_def,contains_App_SOME_def] >>
  ONCE_REWRITE_TAC[CONS_APPEND] >>
  REWRITE_TAC[HD_intro_multi] >>
  full_simp_tac(srw_ss())[HD_intro_multi] >>
  full_simp_tac(srw_ss())[contains_App_SOME_def,HD_intro_multi,intro_multi_length]
  >- ( rpt (pop_assum mp_tac) >> ONCE_REWRITE_TAC[contains_App_SOME_EXISTS] >> srw_tac[][] )
  >- metis_tac[contains_App_SOME_collect_apps]
  >- metis_tac[contains_App_SOME_collect_args]
  >- (
    simp[MAP_MAP_o,UNCURRY,o_DEF] >>
    AP_THM_TAC >> AP_TERM_TAC >>
    pop_assum kall_tac >>
    Induct_on`funs`>>
    srw_tac[QUANT_INST_ss[pair_default_qp]][] >>
    ONCE_REWRITE_TAC[CONS_APPEND] >>
    REWRITE_TAC[HD_intro_multi] >>
    rpt(pop_assum mp_tac) >>
    ONCE_REWRITE_TAC[contains_App_SOME_EXISTS] >>
    srw_tac[QUANT_INST_ss[pair_default_qp]][] >>
    metis_tac[contains_App_SOME_collect_args,SND,PAIR]));

val every_Fn_vs_NONE_collect_apps = Q.prove(
  `∀es e x y. collect_apps es e = (x,y) ⇒
  (every_Fn_vs_NONE x ∧ every_Fn_vs_NONE [y] ⇔
   every_Fn_vs_NONE es ∧ every_Fn_vs_NONE [e])`,
  ho_match_mp_tac collect_apps_ind >>
  srw_tac[][collect_apps_def] >> full_simp_tac(srw_ss())[] >>
  ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] >>
  srw_tac[][] >> metis_tac[])

val every_Fn_vs_NONE_collect_args = Q.prove(
  `∀es e x y. collect_args es e = (x,y) ⇒
    (every_Fn_vs_NONE [y] ⇔ every_Fn_vs_NONE [e])`,
  ho_match_mp_tac collect_args_ind >>
  srw_tac[][collect_args_def] >> full_simp_tac(srw_ss())[])

val every_Fn_vs_NONE_intro_multi = Q.store_thm("every_Fn_vs_NONE_intro_multi[simp]",
  `∀es. every_Fn_vs_NONE (intro_multi es) = every_Fn_vs_NONE es`,
  ho_match_mp_tac intro_multi_ind >>
  srw_tac[][intro_multi_def] >>
  ONCE_REWRITE_TAC[CONS_APPEND] >>
  REWRITE_TAC[HD_intro_multi] >>
  full_simp_tac(srw_ss())[HD_intro_multi]
  >- ( rpt (pop_assum mp_tac) >> ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] >> srw_tac[][] )
  >- metis_tac[every_Fn_vs_NONE_collect_apps]
  >- metis_tac[every_Fn_vs_NONE_collect_args] >>
  simp[MAP_MAP_o,o_DEF,UNCURRY] >>
  AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  pop_assum kall_tac >>
  Induct_on`funs`>>
  srw_tac[QUANT_INST_ss[pair_default_qp]][] >>
  ONCE_REWRITE_TAC[CONS_APPEND] >>
  REWRITE_TAC[HD_intro_multi] >>
  rpt(pop_assum mp_tac) >>
  ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] >>
  srw_tac[QUANT_INST_ss[pair_default_qp]][] >>
  metis_tac[every_Fn_vs_NONE_collect_args,SND,PAIR]);

val _ = export_theory();
