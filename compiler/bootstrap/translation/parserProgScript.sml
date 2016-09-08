open preamble
     cmlParseTheory cmlPEGTheory lexerProgTheory
     ml_translatorLib ml_translatorTheory
     semanticPrimitivesTheory

val _ = new_theory "parserProg"

val _ = translation_extends "lexerProg";

(* translator setup *)

val RW = REWRITE_RULE
val RW1 = ONCE_REWRITE_RULE
fun list_dest f tm =
  let val (x,y) = f tm in list_dest f x @ list_dest f y end
  handle HOL_ERR _ => [tm];
val dest_fun_type = dom_rng
val mk_fun_type = curry op -->;
fun list_mk_fun_type [ty] = ty
  | list_mk_fun_type (ty1::tys) =
      mk_fun_type ty1 (list_mk_fun_type tys)
  | list_mk_fun_type _ = fail()

val _ = add_preferred_thy "-";
val _ = add_preferred_thy "termination";

val NOT_NIL_AND_LEMMA = store_thm("NOT_NIL_AND_LEMMA",
  ``(b <> [] /\ x) = if b = [] then F else x``,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy "termination" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> RW (!extra_preprocessing)
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

(* parsing: peg_exec and cmlPEG *)

val res = register_type``:(token,MMLnonT) parsetree``;
val res = register_type``:MMLnonT``;

local
  val ths = ml_translatorLib.eq_lemmas();
in
  fun find_equality_type_thm tm =
    first (can (C match_term tm) o rand o snd o strip_imp o concl) ths
end

val EqualityType_CHAR = find_equality_type_thm``CHAR``
val EqualityType_INT = find_equality_type_thm``INT``
val EqualityType_NUM = find_equality_type_thm``NUM``

val EqualityType_LIST_TYPE_CHAR = find_equality_type_thm``LIST_TYPE CHAR``
  |> Q.GEN`a` |> Q.ISPEC`CHAR` |> SIMP_RULE std_ss [EqualityType_CHAR]

val EqualityType_SUM_TYPE = find_equality_type_thm``SUM_TYPE a b``

val EqualityType_TOKENS_TOKEN_TYPE = find_equality_type_thm``TOKENS_TOKEN_TYPE``
  |> SIMP_RULE std_ss [EqualityType_CHAR,EqualityType_LIST_TYPE_CHAR,EqualityType_INT,EqualityType_NUM]

val EqualityType_GRAM_MMLNONT_TYPE = find_equality_type_thm``GRAM_MMLNONT_TYPE``
  |> SIMP_RULE std_ss []

val GRAMMAR_SYMBOL_TYPE_def = theorem"GRAMMAR_SYMBOL_TYPE_def";

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
    rw[types_match_def,ctor_same_type_def] >>
    METIS_TAC[EqualityType_SUM_TYPE,EqualityType_NUM,EqualityType_def] ))

val GRAMMAR_PARSETREE_TYPE_def = theorem"GRAMMAR_PARSETREE_TYPE_def";
val GRAMMAR_PARSETREE_TYPE_ind = theorem"GRAMMAR_PARSETREE_TYPE_ind";

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
    Cases_on`e`>>fs[GRAMMAR_PARSETREE_TYPE_def,types_match_def,ctor_same_type_def] >>
    conj_tac >- METIS_TAC[EqualityType_SUM_TYPE,EqualityType_NUM,EqualityType_def] >>
    rw[] >> rpt(rator_x_assum`LIST_TYPE`mp_tac) >>
    last_x_assum mp_tac >>
    map_every qid_spec_tac[`v2_2`,`v2_2'`,`x_2`,`l`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >> rw[] >>
    Cases_on`x_2`>>fs[LIST_TYPE_def,types_match_def,ctor_same_type_def] >>
    METIS_TAC[]) >>
  Cases_on`e`>>fs[GRAMMAR_PARSETREE_TYPE_def,types_match_def,ctor_same_type_def] >>
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

val _ = translate (def_of_const ``cmlPEG``);

val INTRO_FLOOKUP = store_thm("INTRO_FLOOKUP",
  ``(if n IN FDOM G.rules
     then EV (G.rules ' n) i r y fk
     else Result NONE) =
    (case FLOOKUP G.rules n of
       NONE => Result NONE
     | SOME x => EV x i r y fk)``,
  SRW_TAC [] [finite_mapTheory.FLOOKUP_DEF]);

val _ = translate (def_of_const ``coreloop`` |> RW [INTRO_FLOOKUP]
                   |> SPEC_ALL |> RW1 [FUN_EQ_THM]);

val _ = translate (def_of_const ``peg_exec``);

(* parsing: cmlvalid *)

val monad_unitbind_assert = prove(
  ``!b x. monad_unitbind (assert b) x = if b then x else NONE``,
  Cases THEN EVAL_TAC THEN SIMP_TAC std_ss []);

val _ = translate grammarTheory.ptree_head_def

(* parsing: ptree converstion *)

val OPTION_BIND_THM = store_thm("OPTION_BIND_THM",
  ``!x y. OPTION_BIND x y = case x of NONE => NONE | SOME i => y i``,
  Cases THEN SRW_TAC [] []);

val _ = (extra_preprocessing :=
  [MEMBER_INTRO,MAP,OPTION_BIND_THM,monad_unitbind_assert]);

val _ = translate (def_of_const ``ptree_Expr``);

val _ = translate (def_of_const ``ptree_TopLevelDecs``);

(* parsing: top-level parser *)

val _ = translate (RW [monad_unitbind_assert] parse_prog_def);

val _ = ParseExtras.temp_tight_equality()

val parse_prog_side_lemma = store_thm("parse_prog_side_lemma",
  ``!x. parse_prog_side x = T``,
  SIMP_TAC std_ss [fetch "-" "parse_prog_side_def",
    fetch "-" "peg_exec_side_def", fetch "-" "coreloop_side_def"]
  THEN REPEAT STRIP_TAC
  THEN STRIP_ASSUME_TAC (Q.SPEC `x` owhile_TopLevelDecs_total)
  THEN FULL_SIMP_TAC std_ss [INTRO_FLOOKUP] THEN POP_ASSUM MP_TAC
  THEN CONV_TAC (DEPTH_CONV ETA_CONV) THEN FULL_SIMP_TAC std_ss [])
  |> update_precondition;

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = export_theory();
