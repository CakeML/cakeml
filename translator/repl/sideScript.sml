open preamble;
open inferTheory inferSoundTheory ml_repl_stepTheory;

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
 cheat,
 cases_on `generalise st.next_uvar 0 (t_walkstar x60.subst x62)` >>
     fs [] >>
     imp_res_tac infer_e_wfs >>
     imp_res_tac t_unify_wfs >>
     rw [],
 match_mp_tac add_constraints_side_thm >>
     rw [] >>
     imp_res_tac infer_e_wfs >>
     fs [],
 cheat,
 qpat_assum `!env st. t_wfs st.subst ⇒ infer_e_side a b c d st` match_mp_tac >>
     rw [] >>
     imp_res_tac pure_add_constraints_wfs >>
     imp_res_tac infer_e_wfs >>
     fs [],
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

val _ = export_theory (); 
