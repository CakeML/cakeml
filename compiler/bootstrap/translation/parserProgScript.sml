(*
  Translate the compiler's parser.
*)
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

fun EqualityType_conseq_conv dir tm = let
    val cc = ConseqConv.CONSEQ_REWRITE_CONV (eq_lemmas (), [], [])
  in cc dir tm end

val EqualityType_tac = ConseqConv.CONSEQ_CONV_TAC EqualityType_conseq_conv
    \\ simp_tac bool_ss [];

(* checking GRAMMAR_PARSETREE_TYPE etc is known to be an EqualityType *)
val EqualityType_GRAMMAR_PARSETREE_TYPE_TOKENS_TOKEN_TYPE_GRAM_MMLNONT_TYPE
    = Q.prove(
  `EqualityType (GRAMMAR_PARSETREE_TYPE TOKENS_TOKEN_TYPE GRAM_MMLNONT_TYPE
                                        LOCATION_LOCS_TYPE)`,
  EqualityType_tac);

val _ = translate (def_of_const ``cmlPEG``);

val INTRO_FLOOKUP = Q.store_thm("INTRO_FLOOKUP",
  `(if n IN FDOM G.rules
     then EV (G.rules ' n) i r y fk
     else Result xx) =
    (case FLOOKUP G.rules n of
       NONE => Result xx
     | SOME x => EV x i r y fk)`,
  SRW_TAC [] [finite_mapTheory.FLOOKUP_DEF]);

val _ = translate (def_of_const ``coreloop`` |> RW [INTRO_FLOOKUP]
                   |> SPEC_ALL |> RW1 [FUN_EQ_THM]);

val _ = translate (def_of_const ``peg_exec``);

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
    fetch "-" "peg_exec_side_def", fetch "-" "coreloop_side_def"]
  THEN REPEAT STRIP_TAC
  THEN STRIP_ASSUME_TAC (Q.SPEC `x` owhile_TopLevelDecs_total)
  THEN FULL_SIMP_TAC std_ss [INTRO_FLOOKUP] THEN POP_ASSUM MP_TAC
  THEN CONV_TAC (DEPTH_CONV ETA_CONV) THEN FULL_SIMP_TAC std_ss [])
  |> update_precondition;

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
