open preamble;
open inferTheory inferSoundTheory inferPropsTheory unifyTheory ml_repl_stepTheory;
open ml_translatorTheory;

val _ = new_theory "side";

val add_constraints_side_thm = Q.prove (
`!ts1 ts2 st. t_wfs st.subst ⇒ add_constraints_side ts1 ts2 st`,
Induct >>
rw [] >>
rw [Once add_constraints_side_def, add_constraint_side_def] >>
fs [success_eqns] >>
imp_res_tac t_unify_wfs >>
qpat_assum `!ts2 st. P st ⇒ Q ts2 st` match_mp_tac >>
fs []);

val infer_p_side_thm = Q.store_thm ("infer_p_side_thm",
`(!cenv p st. t_wfs st.subst ⇒ infer_p_side cenv p st) ∧
 (!cenv ps st. t_wfs st.subst ⇒ infer_ps_side cenv ps st)`,
ho_match_mp_tac infer_p_ind >>
rw [] >>
rw [Once infer_p_side_def] >>
fs [success_eqns, rich_listTheory.LENGTH_COUNT_LIST] >>
rw [] >|
[PairCases_on `x4` >>
     match_mp_tac add_constraints_side_thm >>
     rw [] >>
     metis_tac [infer_p_wfs],
 PairCases_on `x1` >>
     metis_tac [infer_p_wfs]]);

val helper_tac =
  imp_res_tac infer_e_wfs >>
  imp_res_tac t_unify_wfs >>
  rw [] >>
  NO_TAC

val infer_e_side_thm = Q.store_thm ("infer_e_side_thm",
`(!menv cenv env e st. t_wfs st.subst ⇒ infer_e_side menv cenv env e st) /\
 (!menv cenv env es st. t_wfs st.subst ⇒ infer_es_side menv cenv env es st) /\
 (!menv cenv env pes t1 t2 st. t_wfs st.subst ⇒ infer_pes_side menv cenv env pes t1 t2 st) /\
 (!menv cenv env funs st. t_wfs st.subst ⇒ infer_funs_side menv cenv env funs st)`,
ho_match_mp_tac infer_e_ind >>
rw [] >>
rw [Once infer_e_side_def, add_constraint_side_def] >>
fs [success_eqns, rich_listTheory.LENGTH_COUNT_LIST] >>
rw [constrain_op_side_def, add_constraint_side_def,
    apply_subst_side_def, apply_subst_list_side_def] >>
fs [success_eqns, rich_listTheory.LENGTH_COUNT_LIST] >>
TRY (imp_res_tac infer_e_wfs >>
     imp_res_tac t_unify_wfs >>
     rw [] >>
     NO_TAC) >|
[match_mp_tac add_constraints_side_thm >>
     rw [] >>
     prove_tac [infer_e_wfs],
 match_mp_tac add_constraints_side_thm >>
     rw [] >>
     imp_res_tac infer_e_wfs >>
     fs [],
 imp_res_tac infer_e_wfs >>
     imp_res_tac t_unify_wfs >>
     imp_res_tac pure_add_constraints_wfs >>
     rw [],
 prove_tac [infer_p_side_thm],
 every_case_tac >>
     fs [] >>
     PairCases_on `x25` >>
     imp_res_tac infer_p_wfs >>
     fs [],
 every_case_tac >>
     fs [] >>
     PairCases_on `x25` >>
     imp_res_tac infer_p_wfs >>
     imp_res_tac t_unify_wfs >>
     fs [],
 every_case_tac >>
     fs [] >>
     imp_res_tac infer_e_wfs >>
     fs [] >>
     imp_res_tac t_unify_wfs >>
     PairCases_on `x25` >>
     imp_res_tac infer_p_wfs >>
     fs [],
 every_case_tac >>
     fs [] >>
     qpat_assum `!st. t_wfs st.subst ⇒ infer_pes_side a b c d f g st` match_mp_tac >>
     fs [] >>
     imp_res_tac infer_e_wfs >>
     fs [] >>
     imp_res_tac t_unify_wfs >>
     PairCases_on `x25` >>
     imp_res_tac infer_p_wfs >>
     fs []]);

val generalise_list_length = Q.prove (
`!min start s x.
  LENGTH x = LENGTH (SND (SND (generalise_list min start s (MAP f (MAP SND x)))))`,
induct_on `x` >>
rw [generalise_def] >>
rw [] >>
metis_tac [SND]);

val type_name_subst_side_thm = store_thm("type_name_subst_side_thm",
  ``∀a b. check_type_names a b
    ⇒ type_name_subst_side a b``,
  ho_match_mp_tac terminationTheory.type_name_subst_ind >>
  rw[Once type_name_subst_side_def] >>
  rw[Once type_name_subst_side_def] >>
  fs[terminationTheory.check_type_names_def,EVERY_MEM])

val build_ctor_tenv_side_thm = store_thm("build_ctor_tenv_side_thm",
  ``∀x y z. check_ctor_tenv x y z ⇒ build_ctor_tenv_side x y z``,
  rw[build_ctor_tenv_side_def] >>
  fs[typeSystemTheory.check_ctor_tenv_def] >>
  fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
  last_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >> simp[] >> strip_tac >>
  first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >> simp[] >> strip_tac >>
  first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >> simp[] >> strip_tac >>
  match_mp_tac type_name_subst_side_thm >>
  pop_assum ACCEPT_TAC);

val infer_d_side_thm = Q.store_thm ("infer_d_side_thm",
`!mn decls z menv cenv env d st. infer_d_side mn decls z menv cenv env d st`,
rw [infer_d_side_def] >>
fs [init_state_def, success_eqns] >>
rw [add_constraint_side_def, apply_subst_list_side_def] >>
`t_wfs init_infer_state.subst`
          by rw [init_infer_state_def, unifyTheory.t_wfs_def] >|
[match_mp_tac (hd (CONJUNCTS infer_e_side_thm)) >>
     rw [],
 match_mp_tac (hd (CONJUNCTS infer_p_side_thm)) >>
     rw [] >>
     imp_res_tac infer_e_wfs >>
     fs [],
 every_case_tac >>
     fs [] >>
     imp_res_tac infer_e_wfs >>
     fs [] >>
     PairCases_on `v20` >>
     imp_res_tac infer_p_wfs >>
     fs [] >>
     prove_tac [],
 every_case_tac >>
     fs [] >>
     imp_res_tac infer_e_wfs >>
     fs [] >>
     PairCases_on `v20` >>
     imp_res_tac infer_p_wfs >>
     fs [] >>
     prove_tac [t_unify_wfs],
 metis_tac [generalise_list_length],
 match_mp_tac (List.nth (CONJUNCTS infer_e_side_thm, 3)) >>
     rw [],
 match_mp_tac add_constraints_side_thm >>
     rw [] >>
     imp_res_tac infer_e_wfs >>
     fs [],
 imp_res_tac pure_add_constraints_wfs >>
     imp_res_tac infer_e_wfs >>
     fs [],
 match_mp_tac build_ctor_tenv_side_thm >>
 last_x_assum mp_tac >> rw[]]);

val infer_ds_side_thm = Q.store_thm ("infer_ds_side_thm",
`!mn decls z menv cenv env ds st. infer_ds_side mn decls z menv cenv env ds st`,
induct_on `ds` >>
rw [] >>
rw [Once infer_ds_side_def, infer_d_side_thm]);

val check_specs_side_thm = Q.store_thm ("check_specs_side_thm",
`!mn decls z y cenv env specs st. check_specs_side mn decls z y cenv env specs st`,
(check_specs_ind |> SPEC_ALL |> UNDISCH |> Q.SPEC`v`
  |> SIMP_RULE std_ss [GSYM FORALL_PROD] |> Q.GEN`v` |> DISCH_ALL
  |> Q.GEN`P` |> ho_match_mp_tac) >>
rw [] >>
rw [Once check_specs_side_def, rich_listTheory.LENGTH_COUNT_LIST] >>
match_mp_tac build_ctor_tenv_side_thm >>rw[]);

val check_weake_side_thm = Q.store_thm ("check_weake_side_thm",
`!env specs st. check_weake_side env specs st`,
induct_on `specs` >>
rw [] >>
rw [add_constraint_side_def, Once check_weake_side_def] >>
fs [success_eqns, init_state_def] >>
rw [] >>
fs [init_infer_state_def, unifyTheory.t_wfs_def]);

val check_signature_side_thm = Q.store_thm ("check_signature_side_thm",
`!mn decls cenv env specs st baz bar foo. check_signature_side mn decls cenv env specs st baz bar foo`,
rw [check_signature_side_def, check_specs_side_thm ,check_weake_side_thm]);

val infer_top_side_thm = Q.store_thm ("infer_top_side_thm",
`!menv cenv env top st bar foo. infer_top_side menv cenv env top st bar foo`,
rw [infer_top_side_def, infer_ds_side_thm, infer_d_side_thm,
    check_signature_side_thm]);

val inf_type_to_string_side_thm = Q.store_thm ("inf_type_to_string_side_thm",
`(!t. inf_type_to_string_side t) ∧
 (!ts. inf_types_to_string_side ts)`,
 ho_match_mp_tac infer_tTheory.infer_t_induction >>
 rw [] >>
 rw [Once inf_type_to_string_side_def, tc_to_string_side_def] >>
 fs [] >-
 fs [Once inf_type_to_string_side_def] >>
 pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once inf_type_to_string_side_def]) >>
 rw [] >>
 fs [Once inf_type_to_string_side_def]);

val compile_print_vals_side_thm = store_thm("compile_print_vals_side_thm",
  ``∀ls a b. compile_print_vals_side ls a b``,
  Induct >> simp[Once compile_print_vals_side_def,inf_type_to_string_side_thm])

val compile_top_side_thm = store_thm("compile_top_side_thm",
  ``∀x y z. compile_top_side x y z``,
  rw[compile_top_side_def,compile_print_top_side_def] >>
  simp[compile_print_dec_side_def] >> rpt gen_tac >>
  qmatch_abbrev_tac`(a ==> b) ∧ c` >>
  qsuff_tac`b`>-rw[]>> unabbrev_all_tac >>
  simp[compile_print_vals_side_thm])

val parse_infertype_compile_side_thm = Q.store_thm ("parse_infertype_compile_side_thm",
`!toks st. parse_infertype_compile_side toks st`,
 rw [parse_infertype_compile_side_def, infertype_top_side_def] >-
 metis_tac [infer_top_side_thm] >-
 metis_tac [compile_top_side_thm])

val unlabelled_repl_step_side_thm = store_thm("unlabelled_repl_step_side_thm",
  ``!x. unlabelled_repl_step_side x = T``,
  rw[unlabelled_repl_step_side_def,parse_infertype_compile_side_thm])

val basis_repl_step_side_thm = store_thm("basis_repl_step_side_thm",
  ``!x. basis_repl_step_side x = T``,
  rw[basis_repl_step_side_def,unlabelled_repl_step_side_thm])

val _ = export_theory ();
