open preamble miscLib;
open inferTheory inferSoundTheory inferPropsTheory unifyTheory ml_repl_stepTheory;
open ml_translatorTheory sideTheory;

val _ = new_theory "ml_repl_module";

val _ = ml_translatorLib.translation_extends "ml_repl_step";
val _ = ml_translatorLib.update_precondition basis_repl_step_side_thm;

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
    ``App Opassign [Var (Short "output");
        App Opapp [Var (Short "basis_repl_step");
          App Opderef [Var (Short "input")]]]``
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

local
  val ths = ml_translatorLib.eq_lemmas();
in
  fun find_equality_type_thm tm =
    first (can (C match_term tm) o rand o snd o strip_imp o concl) ths
end

val EqualityType_thm = prove(
  ``EqualityType abs ⇔
      (!x1 v1. abs x1 v1 ==> no_closures v1) /\
      (!x1 v1 x2 v2. abs x1 v1 /\ abs x2 v2 ==> types_match v1 v2 /\
                                                ((v1 = v2) ⇔ (x1 = x2)))``,
  SIMP_TAC std_ss [EqualityType_def] \\ METIS_TAC []);
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
  |> SIMP_RULE std_ss [EqualityType_LIST_TYPE_CHAR,EqualityType_INT,EqualityType_BOOL,EqualityType_WORD8]
val EqualityType_AST_OPN_TYPE = find_equality_type_thm``AST_OPN_TYPE`` |> SIMP_RULE std_ss []
val EqualityType_AST_OPB_TYPE = find_equality_type_thm``AST_OPB_TYPE`` |> SIMP_RULE std_ss []
val EqualityType_AST_OP_TYPE = find_equality_type_thm``AST_OP_TYPE``
  |> SIMP_RULE std_ss [EqualityType_AST_OPB_TYPE,EqualityType_AST_OPN_TYPE]
val EqualityType_CONLANG_OP_I2_TYPE = find_equality_type_thm``CONLANG_OP_I2_TYPE``
  |> SIMP_RULE std_ss [EqualityType_NUM,EqualityType_AST_OP_TYPE]
val EqualityType_PATLANG_OP_PAT_TYPE = find_equality_type_thm``PATLANG_OP_PAT_TYPE``
  |> SIMP_RULE std_ss [EqualityType_NUM,EqualityType_CONLANG_OP_I2_TYPE]
val EqualityType_OPTION_TYPE_LIST_TYPE_CHAR = find_equality_type_thm``OPTION_TYPE a``
  |> Q.GEN`a` |> Q.ISPEC`LIST_TYPE CHAR` |> SIMP_RULE std_ss [EqualityType_LIST_TYPE_CHAR]
val EqualityType_AST_LOP_TYPE = find_equality_type_thm``AST_LOP_TYPE``
  |> SIMP_RULE std_ss []
val EqualityType_PAIR_TYPE = find_equality_type_thm``PAIR_TYPE a b``
val EqualityType_OPTION_TYPE = (find_equality_type_thm``OPTION_TYPE a``)
val EqualityType_SEMANTICPRIMITIVES_TID_OR_EXN_TYPE = find_equality_type_thm``SEMANTICPRIMITIVES_TID_OR_EXN_TYPE``
  |> SIMP_RULE std_ss [EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR]
val EqualityType_SPTREE_SPT_TYPE_UNIT_TYPE = find_equality_type_thm``SPTREE_SPT_TYPE a``
  |> Q.GEN`a` |> Q.ISPEC`UNIT_TYPE` |> SIMP_RULE std_ss [find_equality_type_thm``UNIT_TYPE``]
val EqualityType_LIST_TYPE = find_equality_type_thm``LIST_TYPE a``
val EqualityType_GRAMMAR_SYMBOL_TYPE = prove(
  ``∀a b. EqualityType a ∧ EqualityType b ⇒ EqualityType (GRAMMAR_SYMBOL_TYPE a b)``,
  rw[EqualityType_thm] >- (
    Cases_on`x1`>>fs[ml_repl_stepTheory.GRAMMAR_SYMBOL_TYPE_def]>>rw[]>>
    rw[no_closures_def] >- METIS_TAC[] >>
    METIS_TAC[EqualityType_SUM_TYPE,EqualityType_NUM,EqualityType_thm] )
  >- (
    Cases_on`x1`>>Cases_on`x2`>>fs[ml_repl_stepTheory.GRAMMAR_SYMBOL_TYPE_def]>>
    rw[types_match_def] >- METIS_TAC[] >>
    METIS_TAC[EqualityType_SUM_TYPE,EqualityType_NUM,EqualityType_thm] )
  >- (
    Cases_on`x1`>>Cases_on`x2`>>fs[ml_repl_stepTheory.GRAMMAR_SYMBOL_TYPE_def]>>
    rw[] >>
    METIS_TAC[EqualityType_SUM_TYPE,EqualityType_NUM,EqualityType_thm] ))

val _ = temp_tight_equality();

val GRAMMAR_PARSETREE_TYPE_no_closures = prove(
  ``∀a b c d. EqualityType a ∧ EqualityType b ∧ GRAMMAR_PARSETREE_TYPE a b c d ⇒ no_closures d``,
  ho_match_mp_tac ml_repl_stepTheory.GRAMMAR_PARSETREE_TYPE_ind >>
  simp[ml_repl_stepTheory.GRAMMAR_PARSETREE_TYPE_def,PULL_EXISTS,no_closures_def] >>
  rw[] >- METIS_TAC[EqualityType_SUM_TYPE,EqualityType_NUM,EqualityType_thm]
  >- (
    pop_assum mp_tac >>
    Q.ID_SPEC_TAC`v2_2` >>
    Induct_on`x_2` >> simp[ml_repl_stepTheory.LIST_TYPE_def,no_closures_def,PULL_EXISTS] >>
    rw[] >> METIS_TAC[]) >>
  METIS_TAC[EqualityType_GRAMMAR_SYMBOL_TYPE,EqualityType_thm])

val GRAMMAR_PARSETREE_TYPE_types_match = prove(
  ``∀a b c d e f.
      EqualityType a ∧ EqualityType b ∧ GRAMMAR_PARSETREE_TYPE a b c d ∧
      GRAMMAR_PARSETREE_TYPE a b e f ⇒ types_match d f``,
  ho_match_mp_tac ml_repl_stepTheory.GRAMMAR_PARSETREE_TYPE_ind >>
  simp[ml_repl_stepTheory.GRAMMAR_PARSETREE_TYPE_def,PULL_EXISTS,types_match_def] >>
  rw[] >- (
    Cases_on`e`>>fs[ml_repl_stepTheory.GRAMMAR_PARSETREE_TYPE_def,types_match_def] >>
    conj_tac >- METIS_TAC[EqualityType_SUM_TYPE,EqualityType_NUM,EqualityType_thm] >>
    rw[] >> rpt(rator_x_assum`LIST_TYPE`mp_tac) >>
    last_x_assum mp_tac >>
    map_every qid_spec_tac[`v2_2`,`v2_2'`,`x_2`,`l`] >>
    Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def,PULL_EXISTS] >> rw[] >>
    Cases_on`x_2`>>fs[ml_repl_stepTheory.LIST_TYPE_def,types_match_def] >>
    METIS_TAC[]) >>
  Cases_on`e`>>fs[ml_repl_stepTheory.GRAMMAR_PARSETREE_TYPE_def,types_match_def] >>
  METIS_TAC[EqualityType_GRAMMAR_SYMBOL_TYPE,EqualityType_thm])

val GRAMMAR_PARSETREE_TYPE_11 = prove(
  ``∀a b c d e f.
      EqualityType a ∧ EqualityType b ∧ GRAMMAR_PARSETREE_TYPE a b c d ∧
      GRAMMAR_PARSETREE_TYPE a b e f ⇒ (c = e ⇔ d = f)``,
  ho_match_mp_tac ml_repl_stepTheory.GRAMMAR_PARSETREE_TYPE_ind >>
  simp[ml_repl_stepTheory.GRAMMAR_PARSETREE_TYPE_def,PULL_EXISTS] >>
  rw[] >- (
    Cases_on`e`>>fs[ml_repl_stepTheory.GRAMMAR_PARSETREE_TYPE_def] >>
    `x_3 = s ⇔ v2_1 = v2_1'` by METIS_TAC[EqualityType_SUM_TYPE,EqualityType_NUM,EqualityType_thm] >>
    rw[] >> rpt(rator_x_assum`LIST_TYPE`mp_tac) >>
    last_x_assum mp_tac >>
    map_every qid_spec_tac[`v2_2`,`v2_2'`,`x_2`,`l`] >>
    Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def,PULL_EXISTS] >> rw[] >>
    Cases_on`x_2`>>fs[ml_repl_stepTheory.LIST_TYPE_def] >>
    METIS_TAC[]) >>
  Cases_on`e`>>fs[ml_repl_stepTheory.GRAMMAR_PARSETREE_TYPE_def] >>
  METIS_TAC[EqualityType_GRAMMAR_SYMBOL_TYPE,EqualityType_thm])

val EqualityType1 = prove(
  ``EqualityType (GRAMMAR_PARSETREE_TYPE TOKENS_TOKEN_TYPE GRAM_MMLNONT_TYPE)``,
  simp[EqualityType_thm] >>
  assume_tac EqualityType_TOKENS_TOKEN_TYPE >>
  assume_tac EqualityType_GRAM_MMLNONT_TYPE >>
  conj_tac >- METIS_TAC[GRAMMAR_PARSETREE_TYPE_no_closures] >>
  METIS_TAC[GRAMMAR_PARSETREE_TYPE_types_match,GRAMMAR_PARSETREE_TYPE_11])

val EqualityType_AST_TCTOR_TYPE = prove(
  ``EqualityType AST_TCTOR_TYPE``,
  rw[EqualityType_thm] >- (
    Cases_on`x1`>>fs[ml_repl_stepTheory.AST_TCTOR_TYPE_def,no_closures_def] >>
    METIS_TAC[EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR,EqualityType_thm] )
  >- (
    Cases_on`x1`>>Cases_on`x2`>>fs[ml_repl_stepTheory.AST_TCTOR_TYPE_def,types_match_def]>>rw[]>>
    METIS_TAC[EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR,EqualityType_thm])
  >- (
    Cases_on`x1`>>Cases_on`x2`>>fs[ml_repl_stepTheory.AST_TCTOR_TYPE_def]>>rw[]>>
    METIS_TAC[EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR,EqualityType_thm]))

val AST_T_TYPE_no_closures = prove(
  ``∀a b. AST_T_TYPE a b ⇒ no_closures b``,
  ho_match_mp_tac ml_repl_stepTheory.AST_T_TYPE_ind >>
  simp[ml_repl_stepTheory.AST_T_TYPE_def,PULL_EXISTS,no_closures_def] >> rw[] >- (
    pop_assum kall_tac >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    map_every qid_spec_tac[`v3_1`,`x_4`] >>
    Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def,no_closures_def,PULL_EXISTS] >>
    rw[] >> METIS_TAC[] ) >>
  METIS_TAC[EqualityType_AST_TCTOR_TYPE,EqualityType_thm,EqualityType_NUM,EqualityType_LIST_TYPE_CHAR])

val AST_T_TYPE_types_match = prove(
  ``∀a b c d. AST_T_TYPE a b ∧ AST_T_TYPE c d ⇒ types_match b d``,
  ho_match_mp_tac ml_repl_stepTheory.AST_T_TYPE_ind >>
  simp[ml_repl_stepTheory.AST_T_TYPE_def,PULL_EXISTS,types_match_def] >> rw[] >- (
    Cases_on`c`>>fs[ml_repl_stepTheory.AST_T_TYPE_def,types_match_def] >>
    reverse conj_tac >- METIS_TAC[EqualityType_AST_TCTOR_TYPE,EqualityType_thm] >> rw[] >>
    pop_assum kall_tac >>
    rator_x_assum`AST_TCTOR_TYPE`kall_tac >>
    rpt (pop_assum mp_tac) >>
    map_every qid_spec_tac[`v3_1'`,`v3_1`,`l`,`x_4`] >>
    Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def,PULL_EXISTS] >- (
      Cases >> simp[ml_repl_stepTheory.LIST_TYPE_def,types_match_def,PULL_EXISTS] ) >>
    rw[] >> Cases_on`l`>>fs[ml_repl_stepTheory.LIST_TYPE_def,types_match_def] >>
    METIS_TAC[] )
  >- (
    Cases_on`c`>>fs[ml_repl_stepTheory.AST_T_TYPE_def,types_match_def] >>
    METIS_TAC[EqualityType_NUM,EqualityType_thm] )
  >- (
    Cases_on`c`>>fs[ml_repl_stepTheory.AST_T_TYPE_def,types_match_def] >>
    METIS_TAC[EqualityType_LIST_TYPE_CHAR,EqualityType_thm] ))

val AST_T_TYPE_11 = prove(
  ``∀a b c d. AST_T_TYPE a b ∧ AST_T_TYPE c d ⇒ (a = c ⇔ b = d)``,
  ho_match_mp_tac ml_repl_stepTheory.AST_T_TYPE_ind >>
  simp[ml_repl_stepTheory.AST_T_TYPE_def,PULL_EXISTS] >> rw[] >- (
    Cases_on`c`>>fs[ml_repl_stepTheory.AST_T_TYPE_def] >>
    `x_3 = t ⇔ v3_2 = v3_2'` by METIS_TAC[EqualityType_AST_TCTOR_TYPE,EqualityType_thm] >> rw[] >>
    rpt(rator_x_assum`AST_TCTOR_TYPE`kall_tac) >>
    pop_assum kall_tac >>
    rpt (pop_assum mp_tac) >>
    map_every qid_spec_tac[`v3_1'`,`v3_1`,`l`,`x_4`] >>
    Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def,PULL_EXISTS] >- (
      Cases >> simp[ml_repl_stepTheory.LIST_TYPE_def,PULL_EXISTS] ) >>
    rw[] >> Cases_on`l`>>fs[ml_repl_stepTheory.LIST_TYPE_def] >>
    METIS_TAC[] )
  >- (
    Cases_on`c`>>fs[ml_repl_stepTheory.AST_T_TYPE_def] >>
    METIS_TAC[EqualityType_NUM,EqualityType_thm] )
  >- (
    Cases_on`c`>>fs[ml_repl_stepTheory.AST_T_TYPE_def] >>
    METIS_TAC[EqualityType_LIST_TYPE_CHAR,EqualityType_thm] ))

val EqualityType2 = prove(
  ``EqualityType AST_T_TYPE``,
  simp[EqualityType_thm] >>
  METIS_TAC[AST_T_TYPE_no_closures,AST_T_TYPE_types_match,AST_T_TYPE_11])

val AST_PAT_TYPE_no_closures = prove(
  ``∀a b. AST_PAT_TYPE a b ⇒ no_closures b``,
  ho_match_mp_tac ml_repl_stepTheory.AST_PAT_TYPE_ind >>
  simp[ml_repl_stepTheory.AST_PAT_TYPE_def,PULL_EXISTS,no_closures_def] >>
  rw[] >>
  TRY (
    pop_assum mp_tac >>
    pop_assum kall_tac >>
    pop_assum mp_tac >>
    map_every qid_spec_tac[`v3_2`,`x_3`] >>
    Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def,no_closures_def,PULL_EXISTS] >>
    rw[] >> METIS_TAC[] ) >>
  METIS_TAC[EqualityType_thm,
            EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_AST_LIT_TYPE,
            EqualityType_LIST_TYPE_CHAR])

val AST_PAT_TYPE_types_match = prove(
  ``∀a b c d. AST_PAT_TYPE a b ∧ AST_PAT_TYPE c d ⇒ types_match b d``,
  ho_match_mp_tac ml_repl_stepTheory.AST_PAT_TYPE_ind >>
  simp[ml_repl_stepTheory.AST_PAT_TYPE_def,PULL_EXISTS,types_match_def] >> rw[] >>
  Cases_on`c`>>fs[ml_repl_stepTheory.AST_PAT_TYPE_def,types_match_def] >> rw[] >>
  TRY (
    rpt(rator_x_assum`LIST_TYPE`mp_tac) >>
    ntac 2 (pop_assum kall_tac) >> pop_assum mp_tac >>
    map_every qid_spec_tac[`v3_2`,`v3_2'`,`l`,`x_3`] >>
    Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def] >- (
      Cases >> simp[ml_repl_stepTheory.LIST_TYPE_def,types_match_def,PULL_EXISTS] ) >>
    gen_tac >> Cases >> rw[ml_repl_stepTheory.LIST_TYPE_def] >> rw[types_match_def] >>
    METIS_TAC[] ) >>
  METIS_TAC[EqualityType_thm,EqualityType_LIST_TYPE_CHAR,EqualityType_AST_LIT_TYPE,
            EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR])

val AST_PAT_TYPE_11 = prove(
  ``∀a b c d. AST_PAT_TYPE a b ∧ AST_PAT_TYPE c d ⇒ (a = c ⇔ b = d)``,
  ho_match_mp_tac ml_repl_stepTheory.AST_PAT_TYPE_ind >>
  simp[ml_repl_stepTheory.AST_PAT_TYPE_def,PULL_EXISTS] >> rw[] >>
  Cases_on`c`>>fs[ml_repl_stepTheory.AST_PAT_TYPE_def] >> rw[] >>
  TRY (
    rpt(rator_x_assum`LIST_TYPE`mp_tac) >>
    `x_4 = o' ⇔ v3_1 = v3_1'` by METIS_TAC[EqualityType_thm,EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR] >>
    simp[] >>
    ntac 3 (pop_assum kall_tac) >> pop_assum mp_tac >>
    map_every qid_spec_tac[`v3_2`,`v3_2'`,`l`,`x_3`] >>
    Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def] >- (
      Cases >> simp[ml_repl_stepTheory.LIST_TYPE_def,PULL_EXISTS] ) >>
    gen_tac >> Cases >> rw[ml_repl_stepTheory.LIST_TYPE_def] >> rw[] >>
    METIS_TAC[] ) >>
  METIS_TAC[EqualityType_thm,EqualityType_LIST_TYPE_CHAR,EqualityType_AST_LIT_TYPE,
            EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR])

val EqualityType3 = prove(
  ``EqualityType AST_PAT_TYPE``,
  METIS_TAC[EqualityType_thm,AST_PAT_TYPE_no_closures,AST_PAT_TYPE_types_match,AST_PAT_TYPE_11])

val PATLANG_EXP_PAT_TYPE_no_closures = prove(
  ``∀a b. PATLANG_EXP_PAT_TYPE a b ⇒ no_closures b``,
  ho_match_mp_tac ml_repl_stepTheory.PATLANG_EXP_PAT_TYPE_ind >>
  simp[ml_repl_stepTheory.PATLANG_EXP_PAT_TYPE_def,no_closures_def,PULL_EXISTS] >>
  rw[] >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE PATLANG_EXP_PAT_TYPE x1 y1`[] >>
    rator_x_assum`LIST_TYPE`mp_tac >> last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y1`,`x1`] >>
    Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def,no_closures_def,PULL_EXISTS] >>
    rw[] >> METIS_TAC[] ) >>
  METIS_TAC[EqualityType_thm,EqualityType_NUM,EqualityType_PATLANG_OP_PAT_TYPE,EqualityType_AST_LIT_TYPE])

val PATLANG_EXP_PAT_TYPE_types_match = prove(
  ``∀a b c d. PATLANG_EXP_PAT_TYPE a b ∧ PATLANG_EXP_PAT_TYPE c d ⇒ types_match b d``,
  ho_match_mp_tac ml_repl_stepTheory.PATLANG_EXP_PAT_TYPE_ind >>
  simp[ml_repl_stepTheory.PATLANG_EXP_PAT_TYPE_def,types_match_def,PULL_EXISTS] >> rw[] >>
  Cases_on`c`>>fs[ml_repl_stepTheory.PATLANG_EXP_PAT_TYPE_def,types_match_def] >> rw[] >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE PATLANG_EXP_PAT_TYPE x1 y1`[] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE PATLANG_EXP_PAT_TYPE x2 y2`[] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y2`,`y1`,`x1`,`x2`] >>
    Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def] >- (
      Cases >> simp[ml_repl_stepTheory.LIST_TYPE_def,types_match_def,PULL_EXISTS] ) >>
    gen_tac >> Cases >> simp[ml_repl_stepTheory.LIST_TYPE_def,PULL_EXISTS] >> rw[] >>
    rw[types_match_def] >> METIS_TAC[] ) >>
  METIS_TAC[EqualityType_thm,EqualityType_NUM,EqualityType_PATLANG_OP_PAT_TYPE,EqualityType_AST_LIT_TYPE])

val PATLANG_EXP_PAT_TYPE_11 = prove(
  ``∀a b c d. PATLANG_EXP_PAT_TYPE a b ∧ PATLANG_EXP_PAT_TYPE c d ⇒ (a = c ⇔ b = d)``,
  ho_match_mp_tac ml_repl_stepTheory.PATLANG_EXP_PAT_TYPE_ind >>
  simp[ml_repl_stepTheory.PATLANG_EXP_PAT_TYPE_def,PULL_EXISTS] >> rw[] >>
  Cases_on`c`>>fs[ml_repl_stepTheory.PATLANG_EXP_PAT_TYPE_def] >> rw[] >>
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
    `c1 = a1 ⇔ d1 = b1` by METIS_TAC[EqualityType_thm,EqualityType_PATLANG_OP_PAT_TYPE,EqualityType_NUM] >> simp[] >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y2`,`y1`,`x1`,`x2`] >>
    Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def] >- (
      Cases >> simp[ml_repl_stepTheory.LIST_TYPE_def,PULL_EXISTS] ) >>
    gen_tac >> Cases >> simp[ml_repl_stepTheory.LIST_TYPE_def,PULL_EXISTS] >> rw[] >>
    rw[] >> METIS_TAC[] ) >>
  METIS_TAC[EqualityType_thm,EqualityType_NUM,EqualityType_PATLANG_OP_PAT_TYPE,EqualityType_AST_LIT_TYPE])

val EqualityType4 = prove(
  ``EqualityType PATLANG_EXP_PAT_TYPE``,
  METIS_TAC[EqualityType_thm,PATLANG_EXP_PAT_TYPE_no_closures,PATLANG_EXP_PAT_TYPE_types_match,PATLANG_EXP_PAT_TYPE_11])

val AST_EXP_TYPE_no_closures = prove(
  ``∀a b. AST_EXP_TYPE a b ⇒ no_closures b``,
  ho_match_mp_tac ml_repl_stepTheory.AST_EXP_TYPE_ind >>
  simp[ml_repl_stepTheory.AST_EXP_TYPE_def,PULL_EXISTS,no_closures_def] >> rw[] >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE R x1 y1`["R"] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y1`,`x1`] >>
    Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def,PULL_EXISTS,no_closures_def] >>
    qx_gen_tac`p` >> TRY(PairCases_on`p`) >>
    simp[ml_repl_stepTheory.PAIR_TYPE_def,PULL_EXISTS,no_closures_def] >>
    rw[] >>
    METIS_TAC[EqualityType_thm,EqualityType_LIST_TYPE_CHAR,EqualityType3] ) >>
  METIS_TAC[EqualityType_thm,EqualityType_OPTION_TYPE_LIST_TYPE_CHAR,
            EqualityType_AST_LOP_TYPE,EqualityType_AST_OP_TYPE,
            EqualityType_LIST_TYPE_CHAR,EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_AST_LIT_TYPE])

val AST_EXP_TYPE_types_match = prove(
  ``∀a b c d. AST_EXP_TYPE a b ∧ AST_EXP_TYPE c d ⇒ types_match b d``,
  ho_match_mp_tac ml_repl_stepTheory.AST_EXP_TYPE_ind >>
  simp[ml_repl_stepTheory.AST_EXP_TYPE_def,PULL_EXISTS] >> rw[] >>
  Cases_on`c`>>fs[ml_repl_stepTheory.AST_EXP_TYPE_def,types_match_def] >> rw[] >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE R x1 y1`["R"] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE R x2 y2`["R"] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y1`,`x1`,`y2`,`x2`] >>
    Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def,PULL_EXISTS,types_match_def] >- (
      Cases >> simp[ml_repl_stepTheory.LIST_TYPE_def,PULL_EXISTS,types_match_def] ) >>
    qx_gen_tac`p` >> TRY(PairCases_on`p`) >>
    simp[ml_repl_stepTheory.PAIR_TYPE_def,PULL_EXISTS] >>
    gen_tac >> Cases >> simp[PULL_EXISTS,ml_repl_stepTheory.LIST_TYPE_def] >>
    TRY(PairCases_on`h`)>>simp[ml_repl_stepTheory.PAIR_TYPE_def,PULL_EXISTS] >>
    rw[types_match_def] >>
    fs[FORALL_PROD] >>
    PROVE_TAC[EqualityType_thm,EqualityType_LIST_TYPE_CHAR,EqualityType3] ) >>
  METIS_TAC[EqualityType_thm,EqualityType_OPTION_TYPE_LIST_TYPE_CHAR,
            EqualityType_AST_LOP_TYPE,EqualityType_AST_OP_TYPE,
            EqualityType_LIST_TYPE_CHAR,EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_AST_LIT_TYPE])

val AST_EXP_TYPE_11 = prove(
  ``∀a b c d. AST_EXP_TYPE a b ∧ AST_EXP_TYPE c d ⇒ (a = c ⇔ b = d)``,
  ho_match_mp_tac ml_repl_stepTheory.AST_EXP_TYPE_ind >>
  simp[ml_repl_stepTheory.AST_EXP_TYPE_def,PULL_EXISTS] >> rw[] >>
  Cases_on`c`>>fs[ml_repl_stepTheory.AST_EXP_TYPE_def] >> rw[] >>
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
        METIS_TAC[EqualityType_thm,EqualityType_AST_OP_TYPE,
                  EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR] >>
      simp[] ) >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y1`,`x1`,`y2`,`x2`] >>
    Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def,PULL_EXISTS] >- (
      Cases >> simp[ml_repl_stepTheory.LIST_TYPE_def,PULL_EXISTS] ) >>
    qx_gen_tac`p` >> TRY(PairCases_on`p`) >>
    simp[ml_repl_stepTheory.PAIR_TYPE_def,PULL_EXISTS] >>
    Cases >> simp[PULL_EXISTS,ml_repl_stepTheory.LIST_TYPE_def] >>
    TRY(PairCases_on`h`)>>simp[ml_repl_stepTheory.PAIR_TYPE_def,PULL_EXISTS] >>
    rw[] >> fs[FORALL_PROD] >>
    first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
    disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
    TRY(discharge_hyps >- metis_tac[]) >>
    metis_tac[EqualityType_thm,EqualityType_LIST_TYPE_CHAR,EqualityType3] ) >>
  METIS_TAC[EqualityType_thm,EqualityType_OPTION_TYPE_LIST_TYPE_CHAR,
            EqualityType_AST_LOP_TYPE,EqualityType_AST_OP_TYPE,
            EqualityType_LIST_TYPE_CHAR,EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_AST_LIT_TYPE])

val EqualityType5 = prove(
  ``EqualityType AST_EXP_TYPE``,
  METIS_TAC[EqualityType_thm,AST_EXP_TYPE_no_closures,AST_EXP_TYPE_types_match,AST_EXP_TYPE_11])

val INFER_T_INFER_T_TYPE_no_closures = prove(
  ``∀a b. INFER_T_INFER_T_TYPE a b ⇒ no_closures b``,
  ho_match_mp_tac ml_repl_stepTheory.INFER_T_INFER_T_TYPE_ind >>
  simp[ml_repl_stepTheory.INFER_T_INFER_T_TYPE_def,no_closures_def,PULL_EXISTS] >> rw[] >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE R a b`["R"] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    map_every qid_spec_tac[`b`,`a`] >>
    rpt(pop_assum kall_tac) >>
    Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def,PULL_EXISTS,no_closures_def] >>
    rw[] >> METIS_TAC[]) >>
  METIS_TAC[EqualityType_thm,EqualityType_NUM,EqualityType_AST_TCTOR_TYPE])

val INFER_T_INFER_T_TYPE_types_match = prove(
  ``∀a b c d. INFER_T_INFER_T_TYPE a b ∧ INFER_T_INFER_T_TYPE c d ⇒ types_match b d``,
  ho_match_mp_tac ml_repl_stepTheory.INFER_T_INFER_T_TYPE_ind >>
  simp[ml_repl_stepTheory.INFER_T_INFER_T_TYPE_def,PULL_EXISTS] >> rw[] >>
  Cases_on`c`>>fs[ml_repl_stepTheory.INFER_T_INFER_T_TYPE_def] >> rw[types_match_def] >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE R a b`["R"] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE R c d`["R"] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    map_every qid_spec_tac[`b`,`a`,`d`,`c`] >>
    rpt(pop_assum kall_tac) >>
    Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def,PULL_EXISTS] >> rw[] >>
    Cases_on`a`>>fs[ml_repl_stepTheory.LIST_TYPE_def] >>
    rw[types_match_def] >> METIS_TAC[]) >>
  METIS_TAC[EqualityType_thm,EqualityType_NUM,EqualityType_AST_TCTOR_TYPE])

val INFER_T_INFER_T_TYPE_11 = prove(
  ``∀a b c d. INFER_T_INFER_T_TYPE a b ∧ INFER_T_INFER_T_TYPE c d ⇒ (a = c ⇔ b = d)``,
  ho_match_mp_tac ml_repl_stepTheory.INFER_T_INFER_T_TYPE_ind >>
  simp[ml_repl_stepTheory.INFER_T_INFER_T_TYPE_def,PULL_EXISTS] >> rw[] >>
  Cases_on`c`>>fs[ml_repl_stepTheory.INFER_T_INFER_T_TYPE_def] >> rw[] >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE R a b`["R"] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE R c d`["R"] >>
    rator_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    qmatch_assum_rename_tac`R u v`["R"] >> pop_assum mp_tac >>
    qmatch_assum_rename_tac`R w x`["R"] >> strip_tac >>
    `w = u ⇔ x = v` by METIS_TAC[EqualityType_thm,EqualityType_AST_TCTOR_TYPE] >> simp[] >>
    map_every qid_spec_tac[`b`,`a`,`d`,`c`] >>
    rpt(pop_assum kall_tac) >>
    Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def,PULL_EXISTS] >> rw[] >>
    Cases_on`a`>>fs[ml_repl_stepTheory.LIST_TYPE_def] >>
    rw[types_match_def] >> METIS_TAC[]) >>
  METIS_TAC[EqualityType_thm,EqualityType_NUM,EqualityType_AST_TCTOR_TYPE])

val EqualityType6 = prove(
  ``EqualityType INFER_T_INFER_T_TYPE``,
  METIS_TAC[EqualityType_thm,INFER_T_INFER_T_TYPE_no_closures,INFER_T_INFER_T_TYPE_types_match,INFER_T_INFER_T_TYPE_11])

val EqualityTypes = [EqualityType1, EqualityType2, EqualityType3, EqualityType4, EqualityType5, EqualityType6]

val evaluate_repl_decs = DISCH_ALL module_thm |> REWRITE_RULE EqualityTypes

val INPUT_TYPE_def = Define `
  INPUT_TYPE =
  ^(find_term (can (match_term ``OPTION_TYPE xx``)) (concl evaluate_repl_decs))`;

val OUTPUT_TYPE_def = Define `
  OUTPUT_TYPE =
  ^(find_term (can (match_term ``SUM_TYPE xx yy``)) (concl evaluate_repl_decs))`;

val OPTION_TYPE_no_closures = prove(
  ``(∀a b. A a b ⇒ no_closures b) ⇒ ∀a b. OPTION_TYPE A a b ⇒ no_closures b``,
  strip_tac >> Cases >> simp[ml_repl_stepTheory.OPTION_TYPE_def,no_closures_def,PULL_EXISTS] >> METIS_TAC[])

val PAIR_TYPE_no_closures = prove(
  ``(∀a b. A a b ⇒ no_closures b) ∧ (∀a b. B a b ⇒ no_closures b) ⇒ ∀a b. PAIR_TYPE A B a b ⇒ no_closures b``,
  strip_tac >> Cases >> simp[ml_repl_stepTheory.PAIR_TYPE_def,no_closures_def,PULL_EXISTS] >> METIS_TAC[])

val LIST_TYPE_no_closures = prove(
  ``(∀a b. A a b ⇒ no_closures b) ⇒ ∀a b. LIST_TYPE A a b ⇒ no_closures b``,
  strip_tac >> Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def,no_closures_def,PULL_EXISTS] >>
  METIS_TAC[] )

val FMAP_TYPE_no_closures = prove(
  ``(∀a b. A a b ⇒ no_closures b) ∧ (∀a b. B a b ⇒ no_closures b) ⇒ ∀a b. FMAP_TYPE A B a b ⇒ no_closures b``,
  strip_tac >>
  Induct >> simp[ml_repl_stepTheory.FMAP_TYPE_def,PULL_EXISTS] >> rw[] >>
  METIS_TAC[LIST_TYPE_no_closures,PAIR_TYPE_no_closures])

val COMPILER_COMPILER_STATE_TYPE_no_closures = prove(
  ``∀a b. COMPILER_COMPILER_STATE_TYPE a b ⇒ no_closures b``,
  Cases >>
  simp[ml_repl_stepTheory.COMPILER_COMPILER_STATE_TYPE_def,PULL_EXISTS,no_closures_def] >>
  rw[] >>
  rpt (
    qmatch_rename_tac`ml_translator$no_closures z`[] >>
    qmatch_assum_abbrev_tac`A a z` >>
    qpat_assum`A a z`mp_tac >>
    unabbrev_all_tac >>
    (( match_mp_tac PAIR_TYPE_no_closures ) ORELSE
     ( match_mp_tac FMAP_TYPE_no_closures ) ORELSE
     ( match_mp_tac OPTION_TYPE_no_closures )
    ) >> rw[]) >>
  METIS_TAC[EqualityType_thm,EqualityType_NUM,EqualityType_LIST_TYPE_CHAR,
            EqualityType_SEMANTICPRIMITIVES_TID_OR_EXN_TYPE,
            EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_SPTREE_SPT_TYPE_UNIT_TYPE])

val LIST_TYPE_CHAR_no_closures =
  EqualityType_LIST_TYPE_CHAR |> REWRITE_RULE[EqualityType_thm] |> CONJUNCT1

val REPL_FUN_REPL_FUN_STATE_TYPE_no_closures = prove(
  ``∀a b. REPL_FUN_REPL_FUN_STATE_TYPE a b ⇒ no_closures b``,
  Cases >>
  simp[ml_repl_stepTheory.REPL_FUN_REPL_FUN_STATE_TYPE_def,PULL_EXISTS,no_closures_def] >>
  rw[] >>
  rpt (
    qmatch_rename_tac`ml_translator$no_closures z`[] >>
    qmatch_assum_abbrev_tac`A a z` >>
    qpat_assum`A a z`mp_tac >>
    unabbrev_all_tac >>
    (( match_mp_tac PAIR_TYPE_no_closures ) ORELSE
     ( match_mp_tac FMAP_TYPE_no_closures ) ORELSE
     ( MATCH_ACCEPT_TAC LIST_TYPE_CHAR_no_closures) ORELSE
     ( match_mp_tac LIST_TYPE_no_closures ) ORELSE
     ( match_mp_tac OPTION_TYPE_no_closures ) ORELSE
     ( MATCH_ACCEPT_TAC COMPILER_COMPILER_STATE_TYPE_no_closures )
    ) >> rw[]) >>
  METIS_TAC[EqualityType_thm,EqualityType_NUM,
            EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType2, EqualityType6,
            EqualityType_SEMANTICPRIMITIVES_TID_OR_EXN_TYPE])

val INPUT_TYPE_no_closures = store_thm("INPUT_TYPE_no_closures",
  ``∀a b. INPUT_TYPE a b ⇒ no_closures b``,
  simp[INPUT_TYPE_def] >>
  match_mp_tac OPTION_TYPE_no_closures >>
  match_mp_tac PAIR_TYPE_no_closures >>
  conj_tac >- (
    METIS_TAC[
      EqualityType_LIST_TYPE,
      EqualityType_thm,
      find_equality_type_thm``LEXER_FUN_SYMBOL_TYPE``,
      EqualityType_LIST_TYPE_CHAR,
      EqualityType_INT] ) >>
  match_mp_tac PAIR_TYPE_no_closures >>
  conj_tac >- ( METIS_TAC[EqualityType_thm, EqualityType_BOOL] ) >>
  match_mp_tac PAIR_TYPE_no_closures >>
  conj_tac >- (
    match_mp_tac PAIR_TYPE_no_closures >>
    conj_tac >- ( METIS_TAC[EqualityType_thm, EqualityType_NUM] ) >>
    match_mp_tac FMAP_TYPE_no_closures >>
    METIS_TAC[EqualityType_thm, EqualityType_NUM] ) >>
  match_mp_tac PAIR_TYPE_no_closures >>
  reverse conj_asm1_tac >- (pop_assum ACCEPT_TAC) >>
  MATCH_ACCEPT_TAC REPL_FUN_REPL_FUN_STATE_TYPE_no_closures)

val _ = save_thm("evaluate_repl_decs",evaluate_repl_decs
  |> REWRITE_RULE [GSYM INPUT_TYPE_def, GSYM OUTPUT_TYPE_def])

val _ = Theory.delete_binding "side_translator_state_thm";

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = export_theory ();
