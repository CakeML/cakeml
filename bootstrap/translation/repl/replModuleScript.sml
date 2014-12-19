open preamble miscLib;
open inferTheory inferSoundTheory inferPropsTheory unifyTheory compilerMLTheory replMLTheory;
open ml_translatorTheory replSideTheory;

val _ = new_theory "replModule";

val _ = ml_translatorLib.translation_extends "replSide";

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

(* define abbreviations for the input and output types *)

val eq_lemmas = ml_translatorLib.eq_lemmas();

fun find_equality_type_thm tm =
  first (can (C match_term tm) o rand o snd o strip_imp o concl) eq_lemmas

val evaluate_replModule = DISCH_ALL module_thm |> REWRITE_RULE eq_lemmas

val INPUT_TYPE_def = Define `
  INPUT_TYPE =
  ^(find_term (can (match_term ``OPTION_TYPE xx``)) (concl evaluate_replModule))`;

val OUTPUT_TYPE_def = Define `
  OUTPUT_TYPE =
  ^(find_term (can (match_term ``SUM_TYPE xx yy``)) (concl evaluate_replModule))`;

val evaluate_replModule = save_thm("evaluate_replModule",evaluate_replModule
  |> REWRITE_RULE [GSYM INPUT_TYPE_def, GSYM OUTPUT_TYPE_def])

(* and prove properties about these types *)

val EqualityType_CHAR = find_equality_type_thm``CHAR``
val EqualityType_INT = find_equality_type_thm``INT``
val EqualityType_NUM = find_equality_type_thm``NUM``
val EqualityType_BOOL = find_equality_type_thm``BOOL``
val EqualityType_LIST_TYPE = find_equality_type_thm``LIST_TYPE a``
val EqualityType_LIST_TYPE_CHAR = EqualityType_LIST_TYPE
  |> Q.GEN`a` |> Q.ISPEC`CHAR` |> SIMP_RULE std_ss [EqualityType_CHAR]
val EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR = find_equality_type_thm``AST_ID_TYPE a``
  |> Q.GEN`a` |> Q.ISPEC`LIST_TYPE CHAR` |> SIMP_RULE std_ss [EqualityType_LIST_TYPE_CHAR]
val EqualityType_SEMANTICPRIMITIVES_TID_OR_EXN_TYPE = find_equality_type_thm``SEMANTICPRIMITIVES_TID_OR_EXN_TYPE``
  |> SIMP_RULE std_ss [EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR]
val EqualityType_SPTREE_SPT_TYPE_UNIT_TYPE = find_equality_type_thm``SPTREE_SPT_TYPE a``
  |> Q.GEN`a` |> Q.ISPEC`UNIT_TYPE` |> SIMP_RULE std_ss [find_equality_type_thm``UNIT_TYPE``]
val EqualityType_AST_EXP_TYPE = find_equality_type_thm``AST_EXP_TYPE``
val EqualityType_AST_T_TYPE = find_equality_type_thm``AST_T_TYPE``
val EqualityType_INFER_T_INFER_T_TYPE = find_equality_type_thm``INFER_T_INFER_T_TYPE``

val OPTION_TYPE_no_closures = prove(
  ``(∀a b. A a b ⇒ no_closures b) ⇒ ∀a b. OPTION_TYPE A a b ⇒ no_closures b``,
  strip_tac >> Cases >> simp[OPTION_TYPE_def,no_closures_def,PULL_EXISTS] >> METIS_TAC[])

val PAIR_TYPE_no_closures = prove(
  ``(∀a b. A a b ⇒ no_closures b) ∧ (∀a b. B a b ⇒ no_closures b) ⇒ ∀a b. PAIR_TYPE A B a b ⇒ no_closures b``,
  strip_tac >> Cases >> simp[PAIR_TYPE_def,no_closures_def,PULL_EXISTS] >> METIS_TAC[])

val LIST_TYPE_no_closures = prove(
  ``(∀a b. A a b ⇒ no_closures b) ⇒ ∀a b. LIST_TYPE A a b ⇒ no_closures b``,
  strip_tac >> Induct >> simp[LIST_TYPE_def,no_closures_def,PULL_EXISTS] >>
  METIS_TAC[] )

val FMAP_TYPE_no_closures = prove(
  ``(∀a b. A a b ⇒ no_closures b) ∧ (∀a b. B a b ⇒ no_closures b) ⇒ ∀a b. FMAP_TYPE A B a b ⇒ no_closures b``,
  strip_tac >>
  Induct >> simp[FMAP_TYPE_def,PULL_EXISTS] >> rw[] >>
  METIS_TAC[LIST_TYPE_no_closures,PAIR_TYPE_no_closures])

val COMPILER_COMPILER_STATE_TYPE_no_closures = prove(
  ``∀a b. COMPILER_COMPILER_STATE_TYPE a b ⇒ no_closures b``,
  Cases >>
  simp[COMPILER_COMPILER_STATE_TYPE_def,PULL_EXISTS,no_closures_def] >>
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
  METIS_TAC[EqualityType_def,EqualityType_NUM,EqualityType_LIST_TYPE_CHAR,
            EqualityType_SEMANTICPRIMITIVES_TID_OR_EXN_TYPE,
            EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_SPTREE_SPT_TYPE_UNIT_TYPE])

val LIST_TYPE_CHAR_no_closures =
  EqualityType_LIST_TYPE_CHAR |> REWRITE_RULE[EqualityType_def] |> CONJUNCT1

val REPL_FUN_REPL_FUN_STATE_TYPE_no_closures = prove(
  ``∀a b. REPL_FUN_REPL_FUN_STATE_TYPE a b ⇒ no_closures b``,
  Cases >>
  simp[REPL_FUN_REPL_FUN_STATE_TYPE_def,PULL_EXISTS,no_closures_def] >>
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
  METIS_TAC[EqualityType_def,EqualityType_NUM,
            EqualityType_AST_ID_TYPE_LIST_TYPE_CHAR,
            EqualityType_INFER_T_INFER_T_TYPE,
            EqualityType_AST_T_TYPE, EqualityType_AST_EXP_TYPE,
            EqualityType_SEMANTICPRIMITIVES_TID_OR_EXN_TYPE])

val INPUT_TYPE_no_closures = store_thm("INPUT_TYPE_no_closures",
  ``∀a b. INPUT_TYPE a b ⇒ no_closures b``,
  simp[INPUT_TYPE_def] >>
  match_mp_tac OPTION_TYPE_no_closures >>
  match_mp_tac PAIR_TYPE_no_closures >>
  conj_tac >- (
    METIS_TAC[
      EqualityType_LIST_TYPE,
      EqualityType_def,
      find_equality_type_thm``LEXER_FUN_SYMBOL_TYPE``,
      EqualityType_LIST_TYPE_CHAR,
      EqualityType_INT] ) >>
  match_mp_tac PAIR_TYPE_no_closures >>
  conj_tac >- ( METIS_TAC[EqualityType_def, EqualityType_BOOL] ) >>
  match_mp_tac PAIR_TYPE_no_closures >>
  conj_tac >- (
    match_mp_tac PAIR_TYPE_no_closures >>
    conj_tac >- ( METIS_TAC[EqualityType_def, EqualityType_NUM] ) >>
    match_mp_tac FMAP_TYPE_no_closures >>
    METIS_TAC[EqualityType_def, EqualityType_NUM] ) >>
  match_mp_tac PAIR_TYPE_no_closures >>
  reverse conj_asm1_tac >- (pop_assum ACCEPT_TAC) >>
  MATCH_ACCEPT_TAC REPL_FUN_REPL_FUN_STATE_TYPE_no_closures)

val LIST_TYPE_exists = prove(
  ``∀x. (∀a. MEM a x ⇒ ∃v. A a v) ⇒ ∃l. LIST_TYPE A x l``,
  Induct >>
  simp[LIST_TYPE_def] >>
  METIS_TAC[])

val FMAP_TYPE_exists = prove(
  ``∀x. (∀a'. MEM a' (fmap_to_alist x) ⇒ ∃v. PAIR_TYPE a b a' v) ⇒
        ∃l. FMAP_TYPE a b x l``,
  REPEAT STRIP_TAC \\ fs [FMAP_TYPE_def]
  \\ HO_MATCH_MP_TAC (METIS_PROVE [] ``(?y x. P x y) ==> (?x y. P x y)``)
  \\ Q.EXISTS_TAC `fmap_to_alist x`
  \\ fs [GSYM PULL_EXISTS]
  \\ REPEAT STRIP_TAC
  \\ fs [FMAP_EQ_ALIST_def]
  \\ MATCH_MP_TAC LIST_TYPE_exists \\ METIS_TAC []);

val SPTREE_SPT_TYPE_exists = prove(
  ``∀p. ∃v. SPTREE_SPT_TYPE UNIT_TYPE p v``,
  Induct >>
  simp[SPTREE_SPT_TYPE_def,
       ml_translatorTheory.UNIT_TYPE_def] >>
  METIS_TAC[])

val STATE_TYPE_def = Define`
  STATE_TYPE = ^(INPUT_TYPE_def |> concl |> rhs |> rand |> rand)`

val tac =
    qx_gen_tac`p`>>PairCases_on`p` >>
    simp[PAIR_TYPE_def,PULL_EXISTS] >>
    simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def]

val ltchartac =
  MATCH_MP_TAC LIST_TYPE_exists >>
  simp[ml_translatorTheory.CHAR_def] >>
  simp[PAIR_TYPE_def,PULL_EXISTS] >>
  simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def]

val infer_t_ind =
  (TypeBase.induction_of``:infer_t``)
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE (srw_ss())[]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> Q.GEN`P`

val INFER_T_INFER_T_TYPE_exists = prove(
  ``∀a. ∃v. INFER_T_INFER_T_TYPE a v``,
  HO_MATCH_MP_TAC infer_t_ind >>
  simp[INFER_T_INFER_T_TYPE_def] >>
  simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  simp[GSYM PULL_EXISTS,EVERY_MEM] >> rw[] >>
  TRY(Cases_on`t`)>>
  simp[AST_TCTOR_TYPE_def,PULL_EXISTS] >>
  TRY(Cases_on`i`)>>simp[AST_ID_TYPE_def]>>
  simp[GSYM PULL_EXISTS] >> rw[] >> ltchartac )

val t_ind =
  (TypeBase.induction_of``:t``)
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE (srw_ss())[]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> Q.GEN`P`

val AST_T_TYPE_exists = prove(
  ``∀a. ∃v. AST_T_TYPE a v``,
  HO_MATCH_MP_TAC t_ind >>
  simp[AST_T_TYPE_def] >>
  simp[NUM_def,ml_translatorTheory.INT_def] >>
  rw[] >- ltchartac >>
  Cases_on`a`>>
  simp[AST_TCTOR_TYPE_def,PULL_EXISTS] >>
  TRY(Cases_on`i`>>simp[AST_ID_TYPE_def]>>
      simp[GSYM PULL_EXISTS] >> rw[] >> ltchartac ) >>
  TRY (MATCH_MP_TAC LIST_TYPE_exists) >>
  fs[EVERY_MEM])

val COMPILER_COMPILER_STATE_TYPE_exists = prove(
  ``∀s. ∃v. COMPILER_COMPILER_STATE_TYPE s v``,
  Cases >> PairCases_on`p` >>
  simp[COMPILER_COMPILER_STATE_TYPE_def] >>
  simp[PAIR_TYPE_def,PULL_EXISTS] >>
  simp[FMAP_TYPE_def,PULL_EXISTS,FMAP_EQ_ALIST_def] >>
  simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
  qexists_tac`fmap_to_alist f` >>
  qexists_tac`fmap_to_alist p1` >> simp[] >>
  qexists_tac`fmap_to_alist p0'` >> simp[] >>
  simp[GSYM PULL_EXISTS] >>
  conj_tac >- (
    MATCH_MP_TAC LIST_TYPE_exists >> tac >> rw[] >>
    simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
    simp[FMAP_TYPE_def,PULL_EXISTS,FMAP_EQ_ALIST_def] >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    qexists_tac`fmap_to_alist p1` >> simp[] >>
    MATCH_MP_TAC LIST_TYPE_exists >> tac >> rw[] >>
    ltchartac ) >>
  conj_tac >- (
    MATCH_MP_TAC LIST_TYPE_exists >> tac >> rw[] >>
    ltchartac ) >>
  conj_tac >- (
    PairCases_on`p0` >>
    simp[PAIR_TYPE_def,PULL_EXISTS] >>
    simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    simp[FMAP_TYPE_def,PULL_EXISTS,FMAP_EQ_ALIST_def] >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    qexists_tac`fmap_to_alist p03` >>
    qexists_tac`fmap_to_alist p02` >> simp[] >>
    qexists_tac`fmap_to_alist p01` >> simp[] >>
    simp[GSYM PULL_EXISTS] >>
    rw[] >> MATCH_MP_TAC LIST_TYPE_exists >> tac >> rw[] >>
    simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
    TRY(Cases_on`p2`)>>
    simp[SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_def] >>
    simp[OPTION_TYPE_def,FMAP_TYPE_def,FMAP_EQ_ALIST_def] >>
    TRY (
      Cases_on`x`>>simp[SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_def] ) >>
    TRY (
      Cases_on`i`>>simp[AST_ID_TYPE_def] >>
      simp[GSYM PULL_EXISTS] >> rw[] >> ltchartac ) >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    qexists_tac`fmap_to_alist p1` >> simp[] >>
    MATCH_MP_TAC LIST_TYPE_exists >> tac >> rw[] >>
    simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
    Cases_on`p2`>>
    simp[OPTION_TYPE_def] >>
    Cases_on`x`>>simp[SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_def] >>
    Cases_on`i`>>simp[AST_ID_TYPE_def] >>
    simp[GSYM PULL_EXISTS] >> rw[] >> ltchartac ) >>
  MATCH_MP_TAC LIST_TYPE_exists >> tac >>
  rw[] >>
  Cases_on`p0`>>simp[AST_ID_TYPE_def] >>
  simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
  simp[SPTREE_SPT_TYPE_exists])

val REPL_FUN_REPL_FUN_STATE_TYPE_exists = prove(
  ``∀s. ∃v. REPL_FUN_REPL_FUN_STATE_TYPE s v``,
  Cases >>
  PairCases_on`p` >>
  Cases_on`c`>>
  PairCases_on`p` >>
  simp[REPL_FUN_REPL_FUN_STATE_TYPE_def] >>
  simp[PAIR_TYPE_def,PULL_EXISTS] >>
  simp[GSYM PULL_EXISTS] >>
  rpt conj_tac >>
  TRY ( ltchartac >> rw[] >> ltchartac >> NO_TAC) >>
  TRY (
    MATCH_MP_TAC LIST_TYPE_exists >>
    strip_tac >> simp[GSYM PULL_EXISTS] >> rw[] >>
    Cases_on`a`>>simp[AST_ID_TYPE_def]>>
    simp[GSYM PULL_EXISTS] >> rw[] >> ltchartac >> NO_TAC) >>
  TRY (
    MATCH_MP_TAC LIST_TYPE_exists >>
    tac >>
    strip_tac >>
    simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
    tac >> simp[PAIR_TYPE_def] >>
    simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
    rw[] >> TRY ltchartac >> simp[AST_T_TYPE_exists] >>
    Cases_on`p3`>>simp[SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_def]>>
    TRY(Cases_on`i`>>simp[AST_ID_TYPE_def,PULL_EXISTS])>>
    simp[GSYM PULL_EXISTS] >> rw[] >>
    TRY ltchartac >> rw[] >> TRY ltchartac >> NO_TAC) >>
  TRY (
    MATCH_MP_TAC LIST_TYPE_exists >>
    tac >>
    strip_tac >>
    simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
    rw[] >> TRY ltchartac >> simp[AST_T_TYPE_exists] >>
    Cases_on`p3`>>simp[SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_def]>>
    TRY(Cases_on`i`>>simp[AST_ID_TYPE_def,PULL_EXISTS])>>
    simp[GSYM PULL_EXISTS] >> rw[] >>
    TRY ltchartac >> rw[] >> TRY ltchartac >> NO_TAC) >>
  TRY (
    MATCH_MP_TAC LIST_TYPE_exists >>
    tac >> simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
    tac >> simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
    simp[INFER_T_INFER_T_TYPE_exists] ) >>
  TRY (
    MATCH_MP_TAC LIST_TYPE_exists >>
    tac >> simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
    simp[INFER_T_INFER_T_TYPE_exists] ) >>
  TRY (
    MATCH_MP_TAC FMAP_TYPE_exists >>
    tac >> simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
    TRY (MATCH_MP_TAC FMAP_TYPE_exists >>
         tac >> simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac) >>
    fs [FORALL_PROD,PAIR_TYPE_def] >>
    REPEAT STRIP_TAC >>
    fs [GSYM PULL_EXISTS] >> REPEAT STRIP_TAC >>
    TRY (MATCH_MP_TAC LIST_TYPE_exists) >>
    TRY (fs [CHAR_def,NUM_def,INT_def] >> NO_TAC) >>
    simp[AST_T_TYPE_exists,INFER_T_INFER_T_TYPE_exists] >> NO_TAC) >>
  simp[COMPILER_COMPILER_STATE_TYPE_exists])

val INPUT_TYPE_exists = store_thm("INPUT_TYPE_exists",
  ``STATE_TYPE s v ⇒ ∃w. INPUT_TYPE (SOME (ts,s)) (Conv(SOME("SOME",TypeId(Short"option")))[Conv(NONE)[w;v]])``,
  simp[STATE_TYPE_def,INPUT_TYPE_def,OPTION_TYPE_def,PULL_EXISTS] >>
  PairCases_on`s` >>
  simp[PAIR_TYPE_def,PULL_EXISTS] >>
  simp[ml_translatorTheory.BOOL_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  simp[FMAP_TYPE_def,PULL_EXISTS,FMAP_EQ_ALIST_def] >>
  simp[GSYM PULL_EXISTS] >> rw[REPL_FUN_REPL_FUN_STATE_TYPE_exists] >>
  MATCH_MP_TAC LIST_TYPE_exists >>
  Cases >>
  simp[LEXER_FUN_SYMBOL_TYPE_def] >> rw[] >>
  simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  ltchartac )

val LIST_TYPE_closed = prove(
  ``∀x. (∀a v. MEM a x ∧ A a v ⇒ closed v) ⇒ ∀l. LIST_TYPE A x l ⇒ closed l``,
  Induct >>
  simp[LIST_TYPE_def] >>
  simp[PULL_EXISTS] >> METIS_TAC[])

val PAIR_TYPE_closed = prove(
  ``∀a. (∀x y. A x y ⇒ closed y) ∧
    (∀x y. B x y ⇒ closed y) ∧
    PAIR_TYPE A B a b ⇒
    closed b``,
  gen_tac >>
  PairCases_on`a` >>
  simp[PAIR_TYPE_def] >>
  rw[] >>
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (SPEC_ALL free_varsTheory.closed_rules))) >>
  rw[] >> METIS_TAC[])

val FMAP_TYPE_closed = prove(
  ``∀x. (∀a v. A a v ⇒ closed v) /\ (∀b v. B b v ⇒ closed v) ⇒
        ∀l. FMAP_TYPE A B x l ⇒ closed l``,
  rw[FMAP_TYPE_def] >>
  match_mp_tac(MP_CANON (Q.ISPEC`PAIR_TYPE A B`(Q.GEN`A`LIST_TYPE_closed))) >>
  ONCE_REWRITE_TAC[CONJ_COMM] >>
  first_assum(match_exists_tac o concl) >> rw[] >>
  METIS_TAC[PAIR_TYPE_closed]);

val OPTION_TYPE_closed = prove(
  ``∀a. (∀x y. A x y ⇒ closed y) ∧ OPTION_TYPE A a b ⇒ closed b``,
  Cases >> simp[OPTION_TYPE_def] >> rw[] >>
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (SPEC_ALL free_varsTheory.closed_rules))) >>
  rw[] >> METIS_TAC[])

val AST_ID_TYPE_closed = prove(
  ``∀a. (∀x y. A x y ⇒ closed y) ∧ AST_ID_TYPE A a b ⇒ closed b``,
  Cases >> simp[AST_ID_TYPE_def] >> rw[] >>
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (SPEC_ALL free_varsTheory.closed_rules))) >>
  rw[] >> TRY(METIS_TAC[]) >>
  qmatch_abbrev_tac`closed z` >>
  qmatch_assum_rename_tac`B c d`[] >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) LIST_TYPE_closed >>
  simp[Abbr`A`,ml_translatorTheory.CHAR_def] >>
  rw[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def])

val AST_TCTOR_TYPE_closed = prove(
  ``∀a. AST_TCTOR_TYPE a b ⇒ closed b``,
  Cases >>
  simp[AST_TCTOR_TYPE_def] >>
  rw[] >>
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (SPEC_ALL free_varsTheory.closed_rules))) >>
  rw[] >>
  qmatch_abbrev_tac`closed x` >>
  qmatch_assum_abbrev_tac`AST_ID_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) AST_ID_TYPE_closed >>
  simp[Abbr`A`] >>
  rw[] >>
  unabbrev_all_tac >>
  qmatch_abbrev_tac`closed x` >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) LIST_TYPE_closed >>
  simp[Abbr`A`] >>
  rw[ml_translatorTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] )

val INFER_T_INFER_T_TYPE_closed = prove(
  ``∀a b. INFER_T_INFER_T_TYPE a b ⇒ closed b``,
  HO_MATCH_MP_TAC infer_t_ind >>
  simp[INFER_T_INFER_T_TYPE_def] >>
  rw[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (SPEC_ALL free_varsTheory.closed_rules))) >>
  rw[] >>
  TRY (MATCH_MP_TAC (GEN_ALL AST_TCTOR_TYPE_closed) >> HINT_EXISTS_TAC >> rw[]) >>
  qmatch_abbrev_tac`closed x` >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) LIST_TYPE_closed >>
  simp[Abbr`A`] >>
  fs[EVERY_MEM] >> METIS_TAC[])

val AST_T_TYPE_closed = prove(
  ``∀a b. AST_T_TYPE a b ⇒ closed b``,
  HO_MATCH_MP_TAC t_ind >>
  simp[AST_T_TYPE_def] >>
  rw[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (SPEC_ALL free_varsTheory.closed_rules))) >>
  rw[] >>
  TRY (MATCH_MP_TAC (GEN_ALL AST_TCTOR_TYPE_closed) >> HINT_EXISTS_TAC >> rw[]) >>
  qmatch_abbrev_tac`closed x` >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) LIST_TYPE_closed >>
  simp[Abbr`A`] >>
  rw[ml_translatorTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  fs[EVERY_MEM] >> METIS_TAC[])

val SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_closed = prove(
  ``∀a b. SEMANTICPRIMITIVES_TID_OR_EXN_TYPE a b ⇒ closed b``,
  Cases >> simp[SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_def] >>
  rw[] >>
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (SPEC_ALL free_varsTheory.closed_rules))) >>
  rw[] >>
  qmatch_abbrev_tac`closed x` >>
  qmatch_assum_abbrev_tac`AST_ID_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) AST_ID_TYPE_closed >>
  simp[Abbr`A`] >>
  rw[] >> unabbrev_all_tac >>
  qmatch_abbrev_tac`closed x` >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) LIST_TYPE_closed >>
  simp[Abbr`A`] >>
  rw[ml_translatorTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def])

val SPTREE_SPT_TYPE_UNIT_TYPE_closed = prove(
  ``∀a b. SPTREE_SPT_TYPE UNIT_TYPE a b ⇒ closed b``,
  Induct >>
  simp[SPTREE_SPT_TYPE_def,PULL_EXISTS,
       ml_translatorTheory.UNIT_TYPE_def])

val COMPILER_COMPILER_STATE_TYPE_closed = prove(
  ``COMPILER_COMPILER_STATE_TYPE x y ⇒ closed y``,
  Cases_on`x` >>
  PairCases_on`p` >>
  simp[COMPILER_COMPILER_STATE_TYPE_def] >>
  simp[PAIR_TYPE_def,PULL_EXISTS] >>
  simp[FMAP_TYPE_def,PULL_EXISTS,FMAP_EQ_ALIST_def] >>
  simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  rw[] >>
  rpt (
    qmatch_abbrev_tac`closed x` >>
    ((
      qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) LIST_TYPE_closed >>
      simp[Abbr`A`]
    ) ORELSE (
      qmatch_assum_abbrev_tac`PAIR_TYPE A B ll x` >>
      Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) PAIR_TYPE_closed >>
      simp[Abbr`A`,Abbr`B`]
    ) ORELSE (
      qmatch_assum_abbrev_tac`OPTION_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) OPTION_TYPE_closed >>
      simp[Abbr`A`]
    ) ORELSE (
      qmatch_assum_abbrev_tac`SEMANTICPRIMITIVES_TID_OR_EXN_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_closed >>
      simp[]
    ) ORELSE (
      qmatch_assum_abbrev_tac`SPTREE_SPT_TYPE UNIT_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) SPTREE_SPT_TYPE_UNIT_TYPE_closed >>
      simp[]
    ) ORELSE (
      qmatch_assum_abbrev_tac`AST_ID_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) AST_ID_TYPE_closed >>
      simp[Abbr`A`]
    )) >>
    fs[FMAP_TYPE_def,FMAP_EQ_ALIST_def] >>
    rw[ml_translatorTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    unabbrev_all_tac ))

val REPL_FUN_REPL_FUN_STATE_TYPE_closed = prove(
  ``REPL_FUN_REPL_FUN_STATE_TYPE a v ⇒ closed v``,
  Cases_on`a`>>simp[REPL_FUN_REPL_FUN_STATE_TYPE_def,PULL_EXISTS] >>
  PairCases_on`p` >>
  simp[PAIR_TYPE_def,PULL_EXISTS] >>
  rw[] >>
  TRY(MATCH_MP_TAC (GEN_ALL COMPILER_COMPILER_STATE_TYPE_closed) >>
      HINT_EXISTS_TAC >> rw[] ) >>
  rpt (
    TRY (MATCH_MP_TAC (GEN_ALL AST_TCTOR_TYPE_closed) >> HINT_EXISTS_TAC >> rw[]) >>
    TRY (MATCH_MP_TAC (GEN_ALL INFER_T_INFER_T_TYPE_closed) >> HINT_EXISTS_TAC >> rw[]) >>
    TRY (MATCH_MP_TAC (GEN_ALL AST_T_TYPE_closed) >> HINT_EXISTS_TAC >> rw[]) >>
    TRY (MATCH_MP_TAC (GEN_ALL SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_closed) >> HINT_EXISTS_TAC >> rw[]) >>
    qmatch_abbrev_tac`closed x` >>
    ((
      qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) LIST_TYPE_closed >>
      simp[Abbr`A`]
    ) ORELSE (
      qmatch_assum_abbrev_tac`PAIR_TYPE A B ll x` >>
      Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) PAIR_TYPE_closed >>
      simp[Abbr`A`,Abbr`B`]
    ) ORELSE (
      qmatch_assum_abbrev_tac`OPTION_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) OPTION_TYPE_closed >>
      simp[Abbr`A`]
    ) ORELSE (
      qmatch_assum_abbrev_tac`AST_ID_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) AST_ID_TYPE_closed >>
      simp[Abbr`A`]
    ) ORELSE (
      qmatch_assum_abbrev_tac`FMAP_TYPE A B ll x` >>
      Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) FMAP_TYPE_closed >>
      simp[Abbr`A`,Abbr`B`]
    )) >>
    rw[ml_translatorTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    unabbrev_all_tac ));

val INPUT_TYPE_closed = store_thm("INPUT_TYPE_closed",
  ``INPUT_TYPE x y ⇒ closed y``,
  simp[INPUT_TYPE_def] >>
  Cases_on`x` >>
  simp[OPTION_TYPE_def] >>
  rw[] >> simp[] >>
  qmatch_assum_rename_tac `PAIR_TYPE X Y s p`["X","Y"] >>
  PairCases_on`s` >>
  fs[PAIR_TYPE_def] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[ml_translatorTheory.BOOL_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  fs[FMAP_TYPE_def] >>
  rw[] >- (
    qmatch_rename_tac`closed ls`[] >>
    qmatch_assum_abbrev_tac`LIST_TYPE A vv ls` >>
    Q.ISPECL_THEN[`A`,`vv`](match_mp_tac o MP_CANON) (GEN_ALL LIST_TYPE_closed) >>
    simp[Abbr`A`] >>
    Cases >> simp[LEXER_FUN_SYMBOL_TYPE_def,PULL_EXISTS] >>
    simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    rw[] >>
    qmatch_assum_abbrev_tac`LIST_TYPE B s bb` >>
    Q.ISPECL_THEN[`B`,`s`](match_mp_tac o MP_CANON) (GEN_ALL LIST_TYPE_closed) >>
    simp[Abbr`B`,ml_translatorTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] )
  >- (
    qmatch_rename_tac`closed ls`[] >>
    qmatch_assum_abbrev_tac`LIST_TYPE A vv ls` >>
    Q.ISPECL_THEN[`A`,`vv`](match_mp_tac o MP_CANON) (GEN_ALL LIST_TYPE_closed) >>
    simp[Abbr`A`] >>
    Cases >> simp[PAIR_TYPE_def,PULL_EXISTS] >>
    simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] )
  >> METIS_TAC[REPL_FUN_REPL_FUN_STATE_TYPE_closed])

val _ = Theory.delete_binding "replSide_translator_state_thm";

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = export_theory ();
