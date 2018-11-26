open preamble
     cmlParseTheory cmlPEGTheory lexerProgTheory
     ml_translatorLib ml_translatorTheory
     semanticPrimitivesTheory

val _ = new_theory "parserProg"

val _ = translation_extends "lexerProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "parserProg");

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

val NOT_NIL_AND_LEMMA = Q.store_thm("NOT_NIL_AND_LEMMA",
  `(b <> [] /\ x) = if b = [] then F else x`,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_pmatch") handle HOL_ERR _ =>
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

val res = register_type``:(token,MMLnonT,locs) parsetree``;
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
val EqualityType_LOCN = find_equality_type_thm ``LOCATION_LOCN_TYPE``
val EqualityType_LOCS = find_equality_type_thm ``LOCATION_LOCS_TYPE``

val EqualityType_LIST_TYPE_CHAR = find_equality_type_thm``LIST_TYPE CHAR``
  |> Q.GEN`a` |> Q.ISPEC`CHAR` |> SIMP_RULE std_ss [EqualityType_CHAR]

val EqualityType_SUM_TYPE = find_equality_type_thm``SUM_TYPE a b``

val EqualityType_TOKENS_TOKEN_TYPE = find_equality_type_thm``TOKENS_TOKEN_TYPE``
  |> SIMP_RULE std_ss [EqualityType_CHAR,EqualityType_LIST_TYPE_CHAR,EqualityType_INT,EqualityType_NUM]

val EqualityType_GRAM_MMLNONT_TYPE = find_equality_type_thm``GRAM_MMLNONT_TYPE``
  |> SIMP_RULE std_ss []

val GRAMMAR_SYMBOL_TYPE_def = theorem"GRAMMAR_SYMBOL_TYPE_def";

val EqualityType_GRAMMAR_SYMBOL_TYPE = Q.prove(
  `∀a b. EqualityType a ∧ EqualityType b ⇒ EqualityType (GRAMMAR_SYMBOL_TYPE a b)`,
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

val EqualityType_PAIR_TYPE = find_equality_type_thm``PAIR_TYPE a b``;
val EqualityType_LOCATION_LOCN_TYPE = find_equality_type_thm``LOCATION_LOCN_TYPE`` |> SIMP_RULE std_ss[EqualityType_NUM]

val GRAMMAR_PARSETREE_TYPE_no_closures = Q.prove(
  `∀a b c d e.
     EqualityType a ∧ EqualityType b ∧ EqualityType c ∧
     GRAMMAR_PARSETREE_TYPE a b c d e ⇒
     no_closures e`,
  ho_match_mp_tac GRAMMAR_PARSETREE_TYPE_ind >>
  simp[GRAMMAR_PARSETREE_TYPE_def,PULL_EXISTS,no_closures_def] >>
  rw[] >- METIS_TAC[EqualityType_SUM_TYPE,EqualityType_NUM,EqualityType_def,EqualityType_PAIR_TYPE,EqualityType_LOCATION_LOCN_TYPE]
  >- (
    pop_assum mp_tac >>
    Q.ID_SPEC_TAC`v2_2` >>
    Induct_on`x_2` >> simp[LIST_TYPE_def,no_closures_def,PULL_EXISTS] >>
    rw[] >> METIS_TAC[]) >>
  METIS_TAC[EqualityType_GRAMMAR_SYMBOL_TYPE,EqualityType_def,EqualityType_LOCATION_LOCN_TYPE,EqualityType_PAIR_TYPE])

val GRAMMAR_PARSETREE_TYPE_types_match = Q.prove(
  `∀a b c d1 e1 d2 e2.
      EqualityType a ∧ EqualityType b ∧ EqualityType c ∧
      GRAMMAR_PARSETREE_TYPE a b c d1 e1 ∧
      GRAMMAR_PARSETREE_TYPE a b c d2 e2 ⇒ types_match e1 e2`,
  ho_match_mp_tac GRAMMAR_PARSETREE_TYPE_ind >>
  simp[GRAMMAR_PARSETREE_TYPE_def,PULL_EXISTS,types_match_def] >>
  rw[] >- (
    Cases_on`d2`>>fs[GRAMMAR_PARSETREE_TYPE_def,types_match_def,ctor_same_type_def] >>
    conj_tac >- METIS_TAC[EqualityType_SUM_TYPE,EqualityType_NUM,EqualityType_def,EqualityType_LOCATION_LOCN_TYPE,EqualityType_PAIR_TYPE] >>
    rw[] >> rpt(qhdtm_x_assum`LIST_TYPE`mp_tac) >>
    last_x_assum mp_tac >>
    rename [`MEM _ l1`, `LIST_TYPE _ l1 vl1`, `types_match vl1 vl2`,
            `LIST_TYPE _ l2 vl2`] >>
    map_every qid_spec_tac[`vl1`,`vl2`,`l1`,`l2`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >> rw[] >>
    Cases_on`l1`>>fs[LIST_TYPE_def,types_match_def,ctor_same_type_def] >>
    METIS_TAC[]) >>
  Cases_on`d2`>>fs[GRAMMAR_PARSETREE_TYPE_def,types_match_def,ctor_same_type_def] >>
  METIS_TAC[EqualityType_GRAMMAR_SYMBOL_TYPE,EqualityType_def,EqualityType_LOCATION_LOCN_TYPE,EqualityType_PAIR_TYPE])

val GRAMMAR_PARSETREE_TYPE_11 = Q.prove(
  `∀a b c d1 e1 d2 e2.
      EqualityType a ∧ EqualityType b ∧ EqualityType c ∧
      GRAMMAR_PARSETREE_TYPE a b c d1 e1 ∧
      GRAMMAR_PARSETREE_TYPE a b c d2 e2 ⇒ (d1 = d2 ⇔ e1 = e2)`,
  ho_match_mp_tac GRAMMAR_PARSETREE_TYPE_ind >>
  simp[GRAMMAR_PARSETREE_TYPE_def,PULL_EXISTS] >>
  rw[] >- (
    Cases_on`d2`>>fs[GRAMMAR_PARSETREE_TYPE_def] >>
    rename [`MEM _ ptl1`, `LIST_TYPE _ ptl1 vl1`, `ptl1 = ptl2`, `vl1 = vl2`,
           `_ = Conv _ [ntv2; locv2]`, `ntv1 = ntv2`, `locv1 = locv2`,
           `PAIR_TYPE _ _ ndp1 ntv1`, `PAIR_TYPE _ _ ndp2 ntv2`] >>
    `ndp1 = ndp2 ⇔ ntv1 = ntv2` by METIS_TAC[EqualityType_SUM_TYPE,EqualityType_NUM,EqualityType_def,EqualityType_LOCATION_LOCN_TYPE,EqualityType_PAIR_TYPE] >>
    rw[] >> rpt(qhdtm_x_assum`LIST_TYPE`mp_tac) >>
    last_x_assum mp_tac >>
    map_every qid_spec_tac[`locv1`,`locv2`,`ptl1`,`ptl2`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >> rw[] >>
    Cases_on`ptl1`>>fs[LIST_TYPE_def] >>
    METIS_TAC[]) >>
  Cases_on`d2`>>fs[GRAMMAR_PARSETREE_TYPE_def] >>
  METIS_TAC[EqualityType_GRAMMAR_SYMBOL_TYPE,EqualityType_def,EqualityType_LOCATION_LOCN_TYPE,EqualityType_PAIR_TYPE])

val EqualityType_GRAMMAR_PARSETREE_TYPE_TOKENS_TOKEN_TYPE_GRAM_MMLNONT_TYPE = Q.prove(
  `EqualityType (GRAMMAR_PARSETREE_TYPE TOKENS_TOKEN_TYPE GRAM_MMLNONT_TYPE
                                        LOCATION_LOCS_TYPE)`,
  simp[EqualityType_def] >>
  assume_tac EqualityType_TOKENS_TOKEN_TYPE >>
  assume_tac EqualityType_GRAM_MMLNONT_TYPE >>
  assume_tac EqualityType_LOCS >>
  assume_tac EqualityType_LOCN >>
  conj_tac >- METIS_TAC[GRAMMAR_PARSETREE_TYPE_no_closures, EqualityType_NUM] >>
  METIS_TAC[GRAMMAR_PARSETREE_TYPE_types_match,GRAMMAR_PARSETREE_TYPE_11,
            EqualityType_NUM])
  |> store_eq_thm

val _ = translate (def_of_const ``cmlPEG``);

val INTRO_FLOOKUP = Q.store_thm("INTRO_FLOOKUP",
  `(if n IN FDOM G.rules
     then EV (G.rules ' n) i r y fk
     else Result xx) =
    (case FLOOKUP G.rules n of
       NONE => Result xx
     | SOME x => EV x i r y fk)`,
  SRW_TAC [] [finite_mapTheory.FLOOKUP_DEF]);

(* val _ = translate (def_of_const ``coreloop`` |> RW [INTRO_FLOOKUP] *)
(*                    |> SPEC_ALL |> RW1 [FUN_EQ_THM]); *)

(* val _ = translate (def_of_const ``peg_exec``); *)

(* parsing: cmlvalid *)

val monad_unitbind_assert = Q.prove(
  `!b x. OPTION_IGNORE_BIND (OPTION_GUARD b) x = if b then x else NONE`,
  Cases THEN EVAL_TAC THEN SIMP_TAC std_ss []);

val _ = translate grammarTheory.ptree_head_def

(* parsing: ptree converstion *)

val OPTION_BIND_THM = Q.store_thm("OPTION_BIND_THM",
  `!x y. OPTION_BIND x y = case x of NONE => NONE | SOME i => y i`,
  Cases THEN SRW_TAC [] []);

val _ = (extra_preprocessing :=
  [MEMBER_INTRO,MAP,OPTION_BIND_THM,monad_unitbind_assert]);

val _ = translate (def_of_const ``ptree_Expr``);

val _ = translate (def_of_const ``ptree_TopLevelDecs``);

(* parsing: top-level parser *)

val _ = translate (RW [monad_unitbind_assert] parse_prog_def);

val parse_prog_side_lemma = Q.store_thm("parse_prog_side_lemma",
  `!x. parse_prog_side x = T`,
  SIMP_TAC std_ss [fetch "-" "parse_prog_side_def",
    ArgParseProgTheory.peg_exec_side_def, ArgParseProgTheory.coreloop_side_def]
  THEN REPEAT STRIP_TAC
  THEN STRIP_ASSUME_TAC (Q.SPEC `x` owhile_TopLevelDecs_total)
  THEN FULL_SIMP_TAC std_ss [INTRO_FLOOKUP] THEN POP_ASSUM MP_TAC
  THEN CONV_TAC (DEPTH_CONV ETA_CONV) THEN FULL_SIMP_TAC std_ss [])
  |> update_precondition;

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
