open preamble miscLib;
open inferTheory inferSoundTheory inferPropsTheory unifyTheory compilerMLTheory replMLTheory compilerSideTheory;
open ml_translatorLib ml_translatorTheory;

val _ = new_theory "replSide";

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
 last_x_assum mp_tac >> rw[],
 match_mp_tac type_name_subst_side_thm>> every_case_tac>>fs[],
 match_mp_tac type_name_subst_side_thm>> every_case_tac>>fs[EVERY_MEM]
 ]);

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
rw [Once check_specs_side_def, rich_listTheory.LENGTH_COUNT_LIST] >-
TRY (match_mp_tac build_ctor_tenv_side_thm >>rw[])>>
TRY (match_mp_tac type_name_subst_side_thm>>every_case_tac>>fs[EVERY_MEM])>>
metis_tac[]
);

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

val parse_infertype_compile_side_thm = Q.store_thm ("parse_infertype_compile_side_thm",
`!toks st. parse_infertype_compile_side toks st`,
 rw [parse_infertype_compile_side_def, infertype_top_side_def] >>
 metis_tac [infer_top_side_thm])

val _ = translation_extends"replML";

val unlabelled_repl_step_side_thm = store_thm("unlabelled_repl_step_side_thm",
  ``!x. unlabelled_repl_step_side x = T``,
  rw[unlabelled_repl_step_side_def,parse_infertype_compile_side_thm]) |> update_precondition

val basis_repl_step_side_thm = store_thm("basis_repl_step_side_thm",
  ``!x. basis_repl_step_side x = T``,
  rw[basis_repl_step_side_def,unlabelled_repl_step_side_thm]) |> update_precondition

local
  val ths = ml_translatorLib.eq_lemmas();
in
  fun find_equality_type_thm tm =
    first (can (C match_term tm) o rand o snd o strip_imp o concl) ths
end

(* properties of the refinement invariant for basis_repl_step *)
(* first, equality types to prove assumptions on the module thm *)

val EqualityType_CHAR = find_equality_type_thm``CHAR``
val EqualityType_INT = find_equality_type_thm``INT``
val EqualityType_NUM = find_equality_type_thm``NUM``
val EqualityType_BOOL = find_equality_type_thm``BOOL``
val EqualityType_WORD8 = find_equality_type_thm``WORD8``
val EqualityType_SUM_TYPE = find_equality_type_thm``SUM_TYPE a b``
val EqualityType_LIST_TYPE_CHAR = find_equality_type_thm``LIST_TYPE CHAR``
  |> Q.GEN`a` |> Q.ISPEC`CHAR` |> SIMP_RULE std_ss [EqualityType_CHAR]
val EqualityType_TOKENS_TOKEN_TYPE = find_equality_type_thm``TOKENS_TOKEN_TYPE``
  |> SIMP_RULE std_ss [EqualityType_LIST_TYPE_CHAR,EqualityType_INT,EqualityType_NUM]
val EqualityType_GRAM_MMLNONT_TYPE = find_equality_type_thm``GRAM_MMLNONT_TYPE``
  |> SIMP_RULE std_ss []
val EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR = find_equality_type_thm``AST_ID_TYPE a``
  |> Q.GEN`a` |> Q.ISPEC`LIST_TYPE CHAR` |> SIMP_RULE std_ss [EqualityType_LIST_TYPE_CHAR]
val EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR = find_equality_type_thm``OPTION_TYPE a``
  |> Q.GEN`a` |> Q.ISPEC`AST_ID_TYPE (LIST_TYPE CHAR)` |> SIMP_RULE std_ss [EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR]
val EqualityType_AST_LIT_TYPE = find_equality_type_thm``AST_LIT_TYPE``
  |> SIMP_RULE std_ss [EqualityType_CHAR,EqualityType_LIST_TYPE_CHAR,EqualityType_INT,EqualityType_BOOL,EqualityType_WORD8]
val EqualityType_AST_OPN_TYPE = find_equality_type_thm``AST_OPN_TYPE`` |> SIMP_RULE std_ss []
val EqualityType_AST_OPB_TYPE = find_equality_type_thm``AST_OPB_TYPE`` |> SIMP_RULE std_ss []
val EqualityType_AST_OP_TYPE = find_equality_type_thm``AST_OP_TYPE``
  |> SIMP_RULE std_ss [EqualityType_AST_OPB_TYPE,EqualityType_AST_OPN_TYPE]
val EqualityType_OPTION_TYPE_LIST_TYPE_CHAR = find_equality_type_thm``OPTION_TYPE a``
  |> Q.GEN`a` |> Q.ISPEC`LIST_TYPE CHAR` |> SIMP_RULE std_ss [EqualityType_LIST_TYPE_CHAR]
val EqualityType_AST_LOP_TYPE = find_equality_type_thm``AST_LOP_TYPE``
  |> SIMP_RULE std_ss []
val EqualityType_LIST_TYPE = find_equality_type_thm``LIST_TYPE a``
val EqualityType_GRAMMAR_SYMBOL_TYPE = prove(
  ``∀a b. EqualityType a ∧ EqualityType b ⇒ EqualityType (GRAMMAR_SYMBOL_TYPE a b)``,
  rw[EqualityType_def] >- (
    Cases_on`x1`>>fs[GRAMMAR_SYMBOL_TYPE_def]>>rw[]>>
    rw[no_closures_def] >- METIS_TAC[] >>
    METIS_TAC[EqualityType_SUM_TYPE,EqualityType_NUM,EqualityType_def] )
  >- (
    Cases_on`x1`>>Cases_on`x2`>>fs[GRAMMAR_SYMBOL_TYPE_def]>>
    rw[types_match_def] >>
    METIS_TAC[EqualityType_SUM_TYPE,EqualityType_NUM,EqualityType_def] )
  >- (
    Cases_on`x1`>>Cases_on`x2`>>fs[GRAMMAR_SYMBOL_TYPE_def]>>
    rw[types_match_def] >>
    METIS_TAC[EqualityType_SUM_TYPE,EqualityType_NUM,EqualityType_def] ))
val EqualityType_AST_TCTOR_TYPE = find_equality_type_thm``AST_TCTOR_TYPE``
val _ = temp_tight_equality();

val GRAMMAR_PARSETREE_TYPE_no_closures = prove(
  ``∀a b c d. EqualityType a ∧ EqualityType b ∧ GRAMMAR_PARSETREE_TYPE a b c d ⇒ no_closures d``,
  ho_match_mp_tac GRAMMAR_PARSETREE_TYPE_ind >>
  simp[GRAMMAR_PARSETREE_TYPE_def,PULL_EXISTS,no_closures_def] >>
  rw[] >- METIS_TAC[EqualityType_SUM_TYPE,EqualityType_NUM,EqualityType_def]
  >- (
    pop_assum mp_tac >>
    Q.ID_SPEC_TAC`v2_2` >>
    Induct_on`x_2` >> simp[LIST_TYPE_def,no_closures_def,PULL_EXISTS] >>
    rw[] >> METIS_TAC[]) >>
  METIS_TAC[EqualityType_GRAMMAR_SYMBOL_TYPE,EqualityType_def])

val GRAMMAR_PARSETREE_TYPE_types_match = prove(
  ``∀a b c d e f.
      EqualityType a ∧ EqualityType b ∧ GRAMMAR_PARSETREE_TYPE a b c d ∧
      GRAMMAR_PARSETREE_TYPE a b e f ⇒ types_match d f``,
  ho_match_mp_tac GRAMMAR_PARSETREE_TYPE_ind >>
  simp[GRAMMAR_PARSETREE_TYPE_def,PULL_EXISTS,types_match_def] >>
  rw[] >- (
    Cases_on`e`>>fs[GRAMMAR_PARSETREE_TYPE_def,types_match_def] >>
    conj_tac >- METIS_TAC[EqualityType_SUM_TYPE,EqualityType_NUM,EqualityType_def] >>
    rw[] >> rpt(rator_x_assum`LIST_TYPE`mp_tac) >>
    last_x_assum mp_tac >>
    map_every qid_spec_tac[`v2_2`,`v2_2'`,`x_2`,`l`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >> rw[] >>
    Cases_on`x_2`>>fs[LIST_TYPE_def,types_match_def] >>
    METIS_TAC[]) >>
  Cases_on`e`>>fs[GRAMMAR_PARSETREE_TYPE_def,types_match_def] >>
  METIS_TAC[EqualityType_GRAMMAR_SYMBOL_TYPE,EqualityType_def])

val GRAMMAR_PARSETREE_TYPE_11 = prove(
  ``∀a b c d e f.
      EqualityType a ∧ EqualityType b ∧ GRAMMAR_PARSETREE_TYPE a b c d ∧
      GRAMMAR_PARSETREE_TYPE a b e f ⇒ (c = e ⇔ d = f)``,
  ho_match_mp_tac GRAMMAR_PARSETREE_TYPE_ind >>
  simp[GRAMMAR_PARSETREE_TYPE_def,PULL_EXISTS] >>
  rw[] >- (
    Cases_on`e`>>fs[GRAMMAR_PARSETREE_TYPE_def] >>
    `x_3 = s ⇔ v2_1 = v2_1'` by METIS_TAC[EqualityType_SUM_TYPE,EqualityType_NUM,EqualityType_def] >>
    rw[] >> rpt(rator_x_assum`LIST_TYPE`mp_tac) >>
    last_x_assum mp_tac >>
    map_every qid_spec_tac[`v2_2`,`v2_2'`,`x_2`,`l`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >> rw[] >>
    Cases_on`x_2`>>fs[LIST_TYPE_def] >>
    METIS_TAC[]) >>
  Cases_on`e`>>fs[GRAMMAR_PARSETREE_TYPE_def] >>
  METIS_TAC[EqualityType_GRAMMAR_SYMBOL_TYPE,EqualityType_def])

val EqualityType_GRAMMAR_PARSETREE_TYPE_TOKENS_TOKEN_TYPE_GRAM_MMLNONT_TYPE = prove(
  ``EqualityType (GRAMMAR_PARSETREE_TYPE TOKENS_TOKEN_TYPE GRAM_MMLNONT_TYPE)``,
  simp[EqualityType_def] >>
  assume_tac EqualityType_TOKENS_TOKEN_TYPE >>
  assume_tac EqualityType_GRAM_MMLNONT_TYPE >>
  conj_tac >- METIS_TAC[GRAMMAR_PARSETREE_TYPE_no_closures] >>
  METIS_TAC[GRAMMAR_PARSETREE_TYPE_types_match,GRAMMAR_PARSETREE_TYPE_11])
  |> store_eq_thm

val AST_T_TYPE_no_closures = prove(
  ``∀a b. AST_T_TYPE a b ⇒ no_closures b``,
  ho_match_mp_tac AST_T_TYPE_ind >>
  simp[AST_T_TYPE_def,PULL_EXISTS,no_closures_def] >> rw[] >- (
    pop_assum kall_tac >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    map_every qid_spec_tac[`v3_1`,`x_4`] >>
    Induct >> simp[LIST_TYPE_def,no_closures_def,PULL_EXISTS] >>
    rw[] >> METIS_TAC[] ) >>
  METIS_TAC[EqualityType_AST_TCTOR_TYPE,EqualityType_def,EqualityType_NUM,EqualityType_LIST_TYPE_CHAR])

val AST_T_TYPE_types_match = prove(
  ``∀a b c d. AST_T_TYPE a b ∧ AST_T_TYPE c d ⇒ types_match b d``,
  ho_match_mp_tac AST_T_TYPE_ind >>
  simp[AST_T_TYPE_def,PULL_EXISTS,types_match_def] >> rw[] >- (
    Cases_on`c`>>fs[AST_T_TYPE_def,types_match_def] >>
    reverse conj_tac >- METIS_TAC[EqualityType_AST_TCTOR_TYPE,EqualityType_def] >> rw[] >>
    pop_assum kall_tac >>
    rator_x_assum`AST_TCTOR_TYPE`kall_tac >>
    rpt (pop_assum mp_tac) >>
    map_every qid_spec_tac[`v3_1'`,`v3_1`,`l`,`x_4`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >- (
      Cases >> simp[LIST_TYPE_def,types_match_def,PULL_EXISTS] ) >>
    rw[] >> Cases_on`l`>>fs[LIST_TYPE_def,types_match_def] >>
    METIS_TAC[] )
  >- (
    Cases_on`c`>>fs[AST_T_TYPE_def,types_match_def] >>
    METIS_TAC[EqualityType_NUM,EqualityType_def] )
  >- (
    Cases_on`c`>>fs[AST_T_TYPE_def,types_match_def] >>
    METIS_TAC[EqualityType_LIST_TYPE_CHAR,EqualityType_def] ))

val AST_T_TYPE_11 = prove(
  ``∀a b c d. AST_T_TYPE a b ∧ AST_T_TYPE c d ⇒ (a = c ⇔ b = d)``,
  ho_match_mp_tac AST_T_TYPE_ind >>
  simp[AST_T_TYPE_def,PULL_EXISTS] >> rw[] >- (
    Cases_on`c`>>fs[AST_T_TYPE_def] >>
    `x_3 = t ⇔ v3_2 = v3_2'` by METIS_TAC[EqualityType_AST_TCTOR_TYPE,EqualityType_def] >> rw[] >>
    rpt(rator_x_assum`AST_TCTOR_TYPE`kall_tac) >>
    pop_assum kall_tac >>
    rpt (pop_assum mp_tac) >>
    map_every qid_spec_tac[`v3_1'`,`v3_1`,`l`,`x_4`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >- (
      Cases >> simp[LIST_TYPE_def,PULL_EXISTS] ) >>
    rw[] >> Cases_on`l`>>fs[LIST_TYPE_def] >>
    METIS_TAC[] )
  >- (
    Cases_on`c`>>fs[AST_T_TYPE_def] >>
    METIS_TAC[EqualityType_NUM,EqualityType_def] )
  >- (
    Cases_on`c`>>fs[AST_T_TYPE_def] >>
    METIS_TAC[EqualityType_LIST_TYPE_CHAR,EqualityType_def] ))

val EqualityType_AST_T_TYPE = prove(
  ``EqualityType AST_T_TYPE``,
  simp[EqualityType_def] >>
  METIS_TAC[AST_T_TYPE_no_closures,AST_T_TYPE_types_match,AST_T_TYPE_11])
  |> store_eq_thm

val AST_PAT_TYPE_no_closures = prove(
  ``∀a b. AST_PAT_TYPE a b ⇒ no_closures b``,
  ho_match_mp_tac AST_PAT_TYPE_ind >>
  simp[AST_PAT_TYPE_def,PULL_EXISTS,no_closures_def] >>
  rw[] >>
  TRY (
    pop_assum mp_tac >>
    pop_assum kall_tac >>
    pop_assum mp_tac >>
    map_every qid_spec_tac[`v3_2`,`x_3`] >>
    Induct >> simp[LIST_TYPE_def,no_closures_def,PULL_EXISTS] >>
    rw[] >> METIS_TAC[] ) >>
  METIS_TAC[EqualityType_def,
            EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_AST_LIT_TYPE,
            EqualityType_LIST_TYPE_CHAR])

val AST_PAT_TYPE_types_match = prove(
  ``∀a b c d. AST_PAT_TYPE a b ∧ AST_PAT_TYPE c d ⇒ types_match b d``,
  ho_match_mp_tac AST_PAT_TYPE_ind >>
  simp[AST_PAT_TYPE_def,PULL_EXISTS,types_match_def] >> rw[] >>
  Cases_on`c`>>fs[AST_PAT_TYPE_def,types_match_def] >> rw[] >>
  TRY (
    rpt(rator_x_assum`LIST_TYPE`mp_tac) >>
    ntac 2 (pop_assum kall_tac) >> pop_assum mp_tac >>
    map_every qid_spec_tac[`v3_2`,`v3_2'`,`l`,`x_3`] >>
    Induct >> simp[LIST_TYPE_def] >- (
      Cases >> simp[LIST_TYPE_def,types_match_def,PULL_EXISTS] ) >>
    gen_tac >> Cases >> rw[LIST_TYPE_def] >> rw[types_match_def] >>
    METIS_TAC[] ) >>
  METIS_TAC[EqualityType_def,EqualityType_LIST_TYPE_CHAR,EqualityType_AST_LIT_TYPE,
            EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR])

val AST_PAT_TYPE_11 = prove(
  ``∀a b c d. AST_PAT_TYPE a b ∧ AST_PAT_TYPE c d ⇒ (a = c ⇔ b = d)``,
  ho_match_mp_tac AST_PAT_TYPE_ind >>
  simp[AST_PAT_TYPE_def,PULL_EXISTS] >> rw[] >>
  Cases_on`c`>>fs[AST_PAT_TYPE_def] >> rw[] >- (
    rpt(rator_x_assum`LIST_TYPE`mp_tac) >>
    `x_4 = o' ⇔ v3_1 = v3_1'` by METIS_TAC[EqualityType_def,EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR] >>
    simp[] >>
    ntac 3 (pop_assum kall_tac) >> pop_assum mp_tac >>
    map_every qid_spec_tac[`v3_2`,`v3_2'`,`l`,`x_3`] >>
    Induct >> simp[LIST_TYPE_def] >- (
      Cases >> simp[LIST_TYPE_def,PULL_EXISTS] ) >>
    gen_tac >> Cases >> rw[LIST_TYPE_def] >> rw[] >>
    METIS_TAC[] ) >>
  METIS_TAC[EqualityType_def,EqualityType_LIST_TYPE_CHAR,EqualityType_AST_LIT_TYPE,
            EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR])

val EqualityType_AST_PAT_TYPE = prove(
  ``EqualityType AST_PAT_TYPE``,
  METIS_TAC[EqualityType_def,AST_PAT_TYPE_no_closures,AST_PAT_TYPE_types_match,AST_PAT_TYPE_11])
  |> store_eq_thm

val AST_EXP_TYPE_no_closures = prove(
  ``∀a b. AST_EXP_TYPE a b ⇒ no_closures b``,
  ho_match_mp_tac AST_EXP_TYPE_ind >>
  simp[AST_EXP_TYPE_def,PULL_EXISTS,no_closures_def] >> rw[] >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE R x1 y1`["R"] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    TRY(SIMP_RULE std_ss [EqualityType_def] EqualityType_LIST_TYPE_CHAR |> CONJUNCT1 |> MATCH_ACCEPT_TAC)>>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y1`,`x1`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS,no_closures_def] >>
    qx_gen_tac`p` >> TRY(PairCases_on`p`) >>
    simp[PAIR_TYPE_def,PULL_EXISTS,no_closures_def] >>
    rw[] >>
    METIS_TAC[EqualityType_def,EqualityType_LIST_TYPE_CHAR,EqualityType_AST_PAT_TYPE] ) >>
  METIS_TAC[EqualityType_def,EqualityType_OPTION_TYPE_LIST_TYPE_CHAR,
            EqualityType_AST_LOP_TYPE,EqualityType_AST_OP_TYPE,
            EqualityType_LIST_TYPE_CHAR,EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_AST_LIT_TYPE])

val AST_EXP_TYPE_types_match = prove(
  ``∀a b c d. AST_EXP_TYPE a b ∧ AST_EXP_TYPE c d ⇒ types_match b d``,
  ho_match_mp_tac AST_EXP_TYPE_ind >>
  simp[AST_EXP_TYPE_def,PULL_EXISTS] >> rw[] >>
  Cases_on`c`>>fs[AST_EXP_TYPE_def,types_match_def] >> rw[] >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE R x1 y1`["R"] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE R x2 y2`["R"] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y1`,`x1`,`y2`,`x2`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS,types_match_def] >- (
      Cases >> simp[LIST_TYPE_def,PULL_EXISTS,types_match_def] ) >>
    qx_gen_tac`p` >> TRY(PairCases_on`p`) >>
    simp[PAIR_TYPE_def,PULL_EXISTS] >>
    gen_tac >> Cases >> simp[PULL_EXISTS,LIST_TYPE_def] >>
    TRY(PairCases_on`h`)>>simp[PAIR_TYPE_def,PULL_EXISTS] >>
    rw[types_match_def] >>
    fs[FORALL_PROD] >>
    PROVE_TAC[EqualityType_def,EqualityType_LIST_TYPE_CHAR,EqualityType_AST_PAT_TYPE] ) >>
  METIS_TAC[EqualityType_def,EqualityType_OPTION_TYPE_LIST_TYPE_CHAR,
            EqualityType_AST_LOP_TYPE,EqualityType_AST_OP_TYPE,
            EqualityType_LIST_TYPE_CHAR,EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_AST_LIT_TYPE])

val AST_EXP_TYPE_11 = with_flag (metisTools.limit,{infs=SOME 1,time=NONE}) prove(
  ``∀a b c d. AST_EXP_TYPE a b ∧ AST_EXP_TYPE c d ⇒ (a = c ⇔ b = d)``,
  ho_match_mp_tac AST_EXP_TYPE_ind >>
  simp[AST_EXP_TYPE_def,PULL_EXISTS] >> rw[] >>
  Cases_on`c`>>fs[AST_EXP_TYPE_def] >> rw[] >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE R x1 y1`["R"] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE R x2 y2`["R"] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    REWRITE_TAC[AND_IMP_INTRO] >>
    last_x_assum mp_tac >>
    MATCH_MP_TAC SWAP_IMP >>
    REWRITE_TAC[GSYM AND_IMP_INTRO] >>
    TRY(
      qmatch_assum_rename_tac`R a1 b1`["R"] >>
      qpat_assum`R a1 b1`mp_tac >>
      qmatch_assum_rename_tac`R a2 b2`["R"] >>
      strip_tac >>
      `a2 = a1 ⇔ b2 = b1` by
        METIS_TAC[EqualityType_def,EqualityType_AST_OP_TYPE,
                  EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR] >>
      simp[] ) >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y1`,`x1`,`y2`,`x2`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >- (
      Cases >> simp[LIST_TYPE_def,PULL_EXISTS] ) >>
    qx_gen_tac`p` >> TRY(PairCases_on`p`) >>
    simp[PAIR_TYPE_def,PULL_EXISTS] >>
    Cases >> simp[PULL_EXISTS,LIST_TYPE_def] >>
    TRY(PairCases_on`h`)>>simp[PAIR_TYPE_def,PULL_EXISTS] >>
    rw[] >> fs[FORALL_PROD] >>
    first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
    disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
    TRY(discharge_hyps >- metis_tac[]) >>
    metis_tac[EqualityType_def,EqualityType_LIST_TYPE_CHAR,EqualityType_AST_PAT_TYPE] ) >>
  METIS_TAC[EqualityType_def,EqualityType_OPTION_TYPE_LIST_TYPE_CHAR,
            EqualityType_AST_LOP_TYPE,EqualityType_AST_OP_TYPE,
            EqualityType_LIST_TYPE_CHAR,EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_AST_LIT_TYPE])

val EqualityType_AST_EXP_TYPE = prove(
  ``EqualityType AST_EXP_TYPE``,
  METIS_TAC[EqualityType_def,AST_EXP_TYPE_no_closures,AST_EXP_TYPE_types_match,AST_EXP_TYPE_11])
  |> store_eq_thm

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = export_theory ();
