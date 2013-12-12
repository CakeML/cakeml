open preamble;
open inferTheory inferSoundTheory ml_repl_stepTheory;
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
rw [constrain_op_side_def, constrain_uop_side_def, add_constraint_side_def,
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

val infer_d_side_thm = Q.store_thm ("infer_d_side_thm",
`!mn menv cenv env d st. infer_d_side mn menv cenv env d st`,
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
     fs []]);

val infer_ds_side_thm = Q.store_thm ("infer_ds_side_thm",
`!mn menv cenv env ds st. infer_ds_side mn menv cenv env ds st`,
induct_on `ds` >>
rw [] >>
rw [Once infer_ds_side_def, infer_d_side_thm]);

val check_specs_side_thm = Q.store_thm ("check_specs_side_thm",
`!mn cenv env specs st. check_specs_side mn cenv env specs st`,
ho_match_mp_tac check_specs_ind >>
rw [] >>
rw [Once check_specs_side_def, rich_listTheory.LENGTH_COUNT_LIST]);

val check_weake_side_thm = Q.store_thm ("check_weake_side_thm",
`!env specs st. check_weake_side env specs st`,
induct_on `specs` >>
rw [] >>
rw [add_constraint_side_def, Once check_weake_side_def] >>
fs [success_eqns, init_state_def] >>
rw [] >>
fs [init_infer_state_def, unifyTheory.t_wfs_def]);

val check_signature_side_thm = Q.store_thm ("check_signature_side_thm",
`!mn cenv env specs st. check_signature_side mn cenv env specs st`,
rw [check_signature_side_def, check_specs_side_thm ,check_weake_side_thm]);

val infer_top_side_thm = Q.store_thm ("infer_top_side_thm",
`!menv cenv env top st. infer_top_side menv cenv env top st`,
rw [infer_top_side_def, infer_ds_side_thm, infer_d_side_thm,
    check_signature_side_thm]);

val compile_decs_length_lemma1 = prove(
  ``!decs mn menv ct m env rsz cs.
     FST(SND(SND(compile_decs mn menv ct m env rsz cs decs))) =
     rsz + LENGTH (FST(SND(compile_decs mn menv ct m env rsz cs decs))).bvars - LENGTH m.bvars``,
Induct >> simp[compilerTheory.compile_decs_def,UNCURRY]);

val compile_decs_length_lemma2 = prove(
  ``!decs mn menv ct m env rsz cs v1 v2 v3 v4.
     ((compile_decs mn menv ct m env rsz cs decs) = (v1,v2,v3,v4)) ⇒
     (v3 = rsz + LENGTH v2.bvars - LENGTH m.bvars)``,
metis_tac [compile_decs_length_lemma1, pair_CASES, FST, SND]);

val compile_top_side_thm = Q.store_thm ("compile_top_side_thm",
`!types st top. compile_top_side types st top`,
 rw [compile_top_side_def, compile_decs_wrap_side_def] >|
 [qsuff_tac `v9' - 2 - st.rsz  ≤ LENGTH v11.bvars` >- rw [LENGTH_TAKE],
  qsuff_tac `v9 - 2 - st.rsz  ≤ LENGTH v11.bvars` >- rw [LENGTH_TAKE]] >>
 imp_res_tac compile_decs_length_lemma2 >>
 rw [] >>
 fs [] >>
 decide_tac);

val update_state_err_side_thm = Q.store_thm ("update_state_err_side_thm",
`∀st env cs. (LENGTH (FST st.rinferencer_state)) ≤ LENGTH (FST env) ⇒ update_state_err_side st env cs`,
 rw [update_state_err_side_def, replTheory.strip_mod_env_def] >>
 metis_tac [FST]);

val inf_type_to_string_side_thm = Q.store_thm ("inf_type_to_string_side_thm",
`(!t. inf_type_to_string_side t) ∧
 (!ts. inf_types_to_string_side ts)`,
 ho_match_mp_tac unifyTheory.infer_t_induction >>
 rw [] >>
 rw [Once inf_type_to_string_side_def, tc_to_string_side_def] >>
 fs [] >-
 fs [Once inf_type_to_string_side_def] >>
 pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once inf_type_to_string_side_def]) >>
 rw [] >>
 fs [Once inf_type_to_string_side_def]);

val inf_tenv_to_string_map_side_thm = Q.store_thm ("inf_tenv_to_string_map_side_thm",
`!tenv. inf_tenv_to_string_map_side tenv`,
 induct_on `tenv` >-
 rw [inf_tenv_to_string_map_side_def] >>
 rw [Once inf_tenv_to_string_map_side_def] >>
 metis_tac [inf_type_to_string_side_thm]);

val parse_elaborate_infertype_compile_side_thm = Q.store_thm ("parse_elaborate_infertype_compile_side_thm",
`!toks st. parse_elaborate_infertype_compile_side toks st`,
 rw [parse_elaborate_infertype_compile_side_def, infertype_top_side_def] >-
 metis_tac [infer_top_side_thm] >-
 metis_tac [inf_tenv_to_string_map_side_thm] >-
 metis_tac [compile_top_side_thm] >>
 match_mp_tac update_state_err_side_thm >>
 cases_on `st.rinferencer_state` >>
 PairCases_on `r` >>
 fs [repl_funTheory.infertype_top_def] >>
 every_case_tac >>
 fs [] >>
 rw []);

val repl_step_side_thm = Q.store_thm ("repl_step_side_thm",
`!x. repl_step_side x`,
 rw [repl_step_side_def, initial_repl_fun_state_side_def, compile_primitives_side_def] >>
 metis_tac [compile_top_side_thm, parse_elaborate_infertype_compile_side_thm]);

val _ = export_theory ();
