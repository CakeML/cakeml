open HolKernel Parse boolLib bossLib;
open preamble;
open cmlParseTheory cmlPEGTheory;
open terminationTheory
open ml_translatorLib ml_translatorTheory;
open std_preludeTheory;

val _ = new_theory "parserProg"

val _ = translation_extends "std_prelude";

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

val _ = register_type ``:lexer_fun$symbol``;

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

val _ = export_theory();
