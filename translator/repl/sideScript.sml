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
`!mn decls menv cenv env d st. infer_d_side mn decls menv cenv env d st`,
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
`!mn decls menv cenv env ds st. infer_ds_side mn decls menv cenv env ds st`,
induct_on `ds` >>
rw [] >>
rw [Once infer_ds_side_def, infer_d_side_thm]);

val check_specs_side_thm = Q.store_thm ("check_specs_side_thm",
`!mn decls cenv env specs st. check_specs_side mn decls cenv env specs st`,
(check_specs_ind |> SPEC_ALL |> UNDISCH |> Q.SPEC`v`
  |> SIMP_RULE std_ss [GSYM FORALL_PROD] |> Q.GEN`v` |> DISCH_ALL
  |> Q.GEN`P` |> ho_match_mp_tac) >>
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
`!mn decls cenv env specs st foo. check_signature_side mn decls cenv env specs st foo`,
rw [check_signature_side_def, check_specs_side_thm ,check_weake_side_thm]);

val infer_top_side_thm = Q.store_thm ("infer_top_side_thm",
`!menv cenv env top st foo. infer_top_side menv cenv env top st foo`,
rw [infer_top_side_def, infer_ds_side_thm, infer_d_side_thm,
    check_signature_side_thm]);

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
 metis_tac [inf_tenv_to_string_map_side_thm])

val repl_step_side_thm = Q.store_thm ("repl_step_side_thm",
`!x. repl_step_side x = T`,
 rw [repl_step_side_def] >>
 metis_tac [parse_elaborate_infertype_compile_side_thm]);

val _ = ml_translatorLib.translation_extends "ml_repl_step";
val _ = ml_translatorLib.update_precondition repl_step_side_thm;

fun add_Ref_NONE_decl name = let
  val decl_assum_x = ml_translatorLib.hol2deep ``(NONE:'a option)``
    |> DISCH_ALL
    |> ml_translatorLib.clean_lookup_cons
    |> Q.INST [`shaddow_env`|->`env`]
    |> REWRITE_RULE []
    |> UNDISCH_ALL
    |> MATCH_MP Eval_IMP_always_evaluates
    |> MATCH_MP always_evaluates_ref
    |> DISCH (ml_translatorLib.get_DeclAssum ())
    |> Q.GENL [`tys`,`env`]
    |> MATCH_MP DeclAssumExists_evaluate
    |> SPEC (stringSyntax.fromMLstring name)
  val tm = (ml_translatorLib.get_DeclAssum ())
  val x = tm |> rator |> rator |> rand
  val y = decl_assum_x |> concl |> rand
  val tm = subst [x|->rand y] tm
  val th = TRUTH |> DISCH tm |> UNDISCH
  val pres = []
  in ml_translatorLib.store_cert th pres decl_assum_x end;

val _ = add_Ref_NONE_decl "input";
val _ = add_Ref_NONE_decl "output";

val add_call_repl_step_decl = let
  val name = "call_repl_step"
  val exp =
    ``App Opassign (Var (Short "output"))
       (App Opapp (Var (Short "repl_step"))
         (Uapp Opderef (Var (Short "input"))))``
  val decl_assum_x = always_evaluates_fn
    |> Q.SPECL [`"u"`,`^exp`,`env`]
    |> DISCH (ml_translatorLib.get_DeclAssum ())
    |> Q.GENL [`tys`,`env`]
    |> MATCH_MP DeclAssumExists_evaluate
    |> SPEC (stringSyntax.fromMLstring name)
  val tm = (ml_translatorLib.get_DeclAssum ())
  val x = tm |> rator |> rator |> rand
  val y = decl_assum_x |> concl |> rand
  val tm = subst [x|->rand y] tm
  val th = TRUTH |> DISCH tm |> UNDISCH
  val pres = []
  in ml_translatorLib.store_cert th pres decl_assum_x end;

val module_thm = let
  val th = ml_translatorLib.finalise_module_translation ()
  val thms = th |> Q.SPEC `NONE` |> CONJUNCTS
  in CONJ (hd thms) (last thms) end;

val _ = save_thm("module_thm", module_thm);

val _ = Theory.delete_binding "side_translator_state_thm";

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = export_theory ();
