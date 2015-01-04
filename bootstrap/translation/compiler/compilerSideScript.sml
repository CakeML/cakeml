open HolKernel boolLib bossLib lcsymtacs miscLib;
open compilerMLTheory ml_translatorLib;

val _ = new_theory "compilerSide";

val _ = translation_extends"compilerML";

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

val pushanyint_side_thm = store_thm("pushanyint_side_thm",
  ``∀i. pushanyint_side i``,
  ho_match_mp_tac compilerTerminationTheory.PushAnyInt_ind >>
  rw[] >> rw[Once pushanyint_side_def] >>
  rw[toBytecodeTheory.maxPushInt_def])

val compile_envref_side_thm = store_thm("compile_envref_side_thm",
  ``∀a b c. compile_envref_side a b c``,
  rw[compile_envref_side_def,pushanyint_side_thm])

val compile_varref_side_thm = store_thm("compile_varref_side_thm",
  ``∀a b c. compile_varref_side a b c``,
  rw[compile_varref_side_def,compile_envref_side_thm])

val emit_ceenv_side_thm = store_thm("emit_ceenv_side_thm",
  ``∀a b c. emit_ceenv_side a b c``,
  rw[emit_ceenv_side_def,compile_varref_side_thm])

val cons_closure_side_thm = store_thm("cons_closure_side_thm",
  ``∀a b c d e. cons_closure_side a b c d e``,
  rw[cons_closure_side_def,pushanyint_side_thm,emit_ceenv_side_thm])

val compile_closures_side_thm = store_thm("compile_closures_side_thm",
  ``∀a b c d. compile_closures_side a b c d``,
  rw[compile_closures_side_def,cons_closure_side_thm])

val prim1_to_bc_side_thm = store_thm("prim1_to_bc_side_thm",
  ``∀x. prim1_to_bc_side x``,
  rw[prim1_to_bc_side_def,pushanyint_side_thm])

val compile_side_thm = store_thm("compile_side_thm",
  ``(∀a b c d e. compile_side a b c d e) ∧
    (∀a b c d e f g. compile_bindings_side a b c d e f g) ∧
    (∀a b c d. compile_nts_side a b c d)``,
  ho_match_mp_tac compilerTerminationTheory.compile_ind >> rw[] >>
  rw[Once compile_side_def,pushanyint_side_thm,
     compile_varref_side_thm,compile_closures_side_thm,
     prim1_to_bc_side_thm])

val cce_aux_side_thm = store_thm("cce_aux_side_thm",
  ``∀x y. cce_aux_side x y``,
  rw[cce_aux_side_def,compile_side_thm])

val compile_code_env_side_thm = store_thm("compile_code_env_side_thm",
  ``∀a b. compile_code_env_side a b``,
  rw[compile_code_env_side_def,cce_aux_side_thm])

val compile_cexp_side_thm = store_thm("compile_cexp_side_thm",
  ``∀a b c d. compile_cexp_side a b c d``,
  rw[compile_cexp_side_def,compile_side_thm,compile_code_env_side_thm])

val compile_top_side_thm = store_thm("compile_top_side_thm",
  ``∀x y z. compile_top_side x y z``,
  rw[compile_top_side_def,compile_print_top_side_def,compile_cexp_side_thm] >>
  simp[compile_print_dec_side_def] >> rpt gen_tac >>
  qmatch_abbrev_tac`(a ==> b) ∧ c` >>
  qsuff_tac`b`>-rw[]>> unabbrev_all_tac >>
  simp[compile_print_vals_side_thm])

val _ = update_precondition (EQT_INTRO(SPEC_ALL compile_top_side_thm));

local
  val ths = ml_translatorLib.eq_lemmas();
in
  fun find_equality_type_thm tm =
    first (can (C match_term tm) o rand o snd o strip_imp o concl) ths
end

val EqualityType_NUM = find_equality_type_thm``NUM``
val EqualityType_INT = find_equality_type_thm``INT``
val EqualityType_BOOL = find_equality_type_thm``BOOL``
val EqualityType_WORD8 = find_equality_type_thm``WORD8``
val EqualityType_CHAR = find_equality_type_thm``CHAR``
val EqualityType_LIST_TYPE_CHAR = find_equality_type_thm``LIST_TYPE CHAR``
  |> Q.GEN`a` |> Q.ISPEC`CHAR` |> SIMP_RULE std_ss [EqualityType_CHAR]
val EqualityType_AST_OPN_TYPE = find_equality_type_thm``AST_OPN_TYPE`` |> SIMP_RULE std_ss []
val EqualityType_AST_OPB_TYPE = find_equality_type_thm``AST_OPB_TYPE`` |> SIMP_RULE std_ss []
val EqualityType_AST_OP_TYPE = find_equality_type_thm``AST_OP_TYPE``
  |> SIMP_RULE std_ss [EqualityType_AST_OPB_TYPE,EqualityType_AST_OPN_TYPE]
val EqualityType_AST_LIT_TYPE = find_equality_type_thm``AST_LIT_TYPE``
  |> SIMP_RULE std_ss [EqualityType_CHAR,EqualityType_LIST_TYPE_CHAR,EqualityType_INT,EqualityType_BOOL,EqualityType_WORD8]
val EqualityType_CONLANG_OP_I2_TYPE = find_equality_type_thm``CONLANG_OP_I2_TYPE``
  |> SIMP_RULE std_ss [EqualityType_NUM,EqualityType_AST_OP_TYPE]
val EqualityType_PATLANG_OP_PAT_TYPE = find_equality_type_thm``PATLANG_OP_PAT_TYPE``
  |> SIMP_RULE std_ss [EqualityType_NUM,EqualityType_CONLANG_OP_I2_TYPE]
val EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR = find_equality_type_thm``AST_ID_TYPE a``
  |> Q.GEN`a` |> Q.ISPEC`LIST_TYPE CHAR` |> SIMP_RULE std_ss [EqualityType_LIST_TYPE_CHAR]

val PATLANG_EXP_PAT_TYPE_no_closures = prove(
  ``∀a b. PATLANG_EXP_PAT_TYPE a b ⇒ no_closures b``,
  ho_match_mp_tac PATLANG_EXP_PAT_TYPE_ind >>
  simp[PATLANG_EXP_PAT_TYPE_def,no_closures_def,PULL_EXISTS] >>
  rw[] >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE PATLANG_EXP_PAT_TYPE x1 y1`[] >>
    rator_x_assum`LIST_TYPE`mp_tac >> last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y1`,`x1`] >>
    Induct >> simp[LIST_TYPE_def,no_closures_def,PULL_EXISTS] >>
    rw[] >> METIS_TAC[] ) >>
  METIS_TAC[EqualityType_def,EqualityType_NUM,EqualityType_PATLANG_OP_PAT_TYPE,EqualityType_AST_LIT_TYPE])

val PATLANG_EXP_PAT_TYPE_types_match = prove(
  ``∀a b c d. PATLANG_EXP_PAT_TYPE a b ∧ PATLANG_EXP_PAT_TYPE c d ⇒ types_match b d``,
  ho_match_mp_tac PATLANG_EXP_PAT_TYPE_ind >>
  simp[PATLANG_EXP_PAT_TYPE_def,types_match_def,PULL_EXISTS] >> rw[] >>
  Cases_on`c`>>fs[PATLANG_EXP_PAT_TYPE_def,types_match_def] >> rw[] >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE PATLANG_EXP_PAT_TYPE x1 y1`[] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE PATLANG_EXP_PAT_TYPE x2 y2`[] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y2`,`y1`,`x1`,`x2`] >>
    Induct >> simp[LIST_TYPE_def] >- (
      Cases >> simp[LIST_TYPE_def,types_match_def,PULL_EXISTS] ) >>
    gen_tac >> Cases >> simp[LIST_TYPE_def,PULL_EXISTS] >> rw[] >>
    rw[types_match_def] >> METIS_TAC[] ) >>
  METIS_TAC[EqualityType_def,EqualityType_NUM,EqualityType_PATLANG_OP_PAT_TYPE,EqualityType_AST_LIT_TYPE])

val PATLANG_EXP_PAT_TYPE_11 = prove(
  ``∀a b c d. PATLANG_EXP_PAT_TYPE a b ∧ PATLANG_EXP_PAT_TYPE c d ⇒ (a = c ⇔ b = d)``,
  ho_match_mp_tac PATLANG_EXP_PAT_TYPE_ind >>
  simp[PATLANG_EXP_PAT_TYPE_def,PULL_EXISTS] >> rw[] >>
  Cases_on`c`>>fs[PATLANG_EXP_PAT_TYPE_def] >> rw[] >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE PATLANG_EXP_PAT_TYPE x1 y1`[] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE PATLANG_EXP_PAT_TYPE x2 y2`[] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    ((qmatch_assum_rename_tac`PATLANG_EXP_PAT_TYPE a1 b1`[] >>
      rator_x_assum`PATLANG_EXP_PAT_TYPE`mp_tac >>
      qmatch_assum_rename_tac`PATLANG_EXP_PAT_TYPE c1 d1`[] >>
      strip_tac) ORELSE
     (qmatch_assum_rename_tac`NUM a1 b1`[] >>
      rator_x_assum`NUM`mp_tac >>
      qmatch_assum_rename_tac`NUM c1 d1`[] >>
      strip_tac) ORELSE
     (qmatch_assum_rename_tac`PATLANG_OP_PAT_TYPE a1 b1`[] >>
      rator_x_assum`PATLANG_OP_PAT_TYPE`mp_tac >>
      qmatch_assum_rename_tac`PATLANG_OP_PAT_TYPE c1 d1`[] >>
      strip_tac)) >>
    `c1 = a1 ⇔ d1 = b1` by METIS_TAC[EqualityType_def,EqualityType_PATLANG_OP_PAT_TYPE,EqualityType_NUM] >> simp[] >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y2`,`y1`,`x1`,`x2`] >>
    Induct >> simp[LIST_TYPE_def] >- (
      Cases >> simp[LIST_TYPE_def,PULL_EXISTS] ) >>
    gen_tac >> Cases >> simp[LIST_TYPE_def,PULL_EXISTS] >> rw[] >>
    rw[] >> METIS_TAC[] ) >>
  METIS_TAC[EqualityType_def,EqualityType_NUM,EqualityType_PATLANG_OP_PAT_TYPE,EqualityType_AST_LIT_TYPE])

val EqualityType_PATLANG_EXP_PAT_TYPE = prove(
  ``EqualityType PATLANG_EXP_PAT_TYPE``,
  METIS_TAC[EqualityType_def,PATLANG_EXP_PAT_TYPE_no_closures,PATLANG_EXP_PAT_TYPE_types_match,PATLANG_EXP_PAT_TYPE_11])
  |> store_eq_thm

val EqualityType_AST_TCTOR_TYPE = prove(
  ``EqualityType AST_TCTOR_TYPE``,
  rw[EqualityType_def] >- (
    Cases_on`x1`>>fs[AST_TCTOR_TYPE_def,no_closures_def] >>
    METIS_TAC[EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR,EqualityType_def] )
  >- (
    Cases_on`x1`>>Cases_on`x2`>>fs[AST_TCTOR_TYPE_def,types_match_def]>>rw[]>>
    METIS_TAC[EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR,EqualityType_def])
  >- (
    Cases_on`x1`>>Cases_on`x2`>>fs[AST_TCTOR_TYPE_def,types_match_def]>>rw[]>>
    METIS_TAC[EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR,EqualityType_def]))
  |> store_eq_thm

val INFER_T_INFER_T_TYPE_no_closures = prove(
  ``∀a b. INFER_T_INFER_T_TYPE a b ⇒ no_closures b``,
  ho_match_mp_tac INFER_T_INFER_T_TYPE_ind >>
  simp[INFER_T_INFER_T_TYPE_def,no_closures_def,PULL_EXISTS] >> rw[] >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE R a b`["R"] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    map_every qid_spec_tac[`b`,`a`] >>
    rpt(pop_assum kall_tac) >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS,no_closures_def] >>
    rw[] >> METIS_TAC[]) >>
  METIS_TAC[EqualityType_def,EqualityType_NUM,EqualityType_AST_TCTOR_TYPE])

val INFER_T_INFER_T_TYPE_types_match = prove(
  ``∀a b c d. INFER_T_INFER_T_TYPE a b ∧ INFER_T_INFER_T_TYPE c d ⇒ types_match b d``,
  ho_match_mp_tac INFER_T_INFER_T_TYPE_ind >>
  simp[INFER_T_INFER_T_TYPE_def,PULL_EXISTS] >> rw[] >>
  Cases_on`c`>>fs[INFER_T_INFER_T_TYPE_def] >> rw[types_match_def] >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE R a b`["R"] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE R c d`["R"] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    map_every qid_spec_tac[`b`,`a`,`d`,`c`] >>
    rpt(pop_assum kall_tac) >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >> rw[] >>
    Cases_on`a`>>fs[LIST_TYPE_def] >>
    rw[types_match_def] >> METIS_TAC[]) >>
  METIS_TAC[EqualityType_def,EqualityType_NUM,EqualityType_AST_TCTOR_TYPE])

val INFER_T_INFER_T_TYPE_11 = prove(
  ``∀a b c d. INFER_T_INFER_T_TYPE a b ∧ INFER_T_INFER_T_TYPE c d ⇒ (a = c ⇔ b = d)``,
  ho_match_mp_tac INFER_T_INFER_T_TYPE_ind >>
  simp[INFER_T_INFER_T_TYPE_def,PULL_EXISTS] >> rw[] >>
  Cases_on`c`>>fs[INFER_T_INFER_T_TYPE_def] >> rw[] >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE R a b`["R"] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE R c d`["R"] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    qmatch_assum_rename_tac`R u v`["R"] >> pop_assum mp_tac >>
    qmatch_assum_rename_tac`R w x`["R"] >> strip_tac >>
    `w = u ⇔ x = v` by METIS_TAC[EqualityType_def,EqualityType_AST_TCTOR_TYPE] >> simp[] >>
    map_every qid_spec_tac[`b`,`a`,`d`,`c`] >>
    rpt(pop_assum kall_tac) >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >> rw[] >>
    Cases_on`a`>>fs[LIST_TYPE_def] >>
    rw[types_match_def] >> METIS_TAC[]) >>
  METIS_TAC[EqualityType_def,EqualityType_NUM,EqualityType_AST_TCTOR_TYPE])

val EqualityType_INFER_T_INFER_T_TYPE = prove(
  ``EqualityType INFER_T_INFER_T_TYPE``,
  METIS_TAC[EqualityType_def,INFER_T_INFER_T_TYPE_no_closures,INFER_T_INFER_T_TYPE_types_match,INFER_T_INFER_T_TYPE_11])
  |> store_eq_thm

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = export_theory ();
