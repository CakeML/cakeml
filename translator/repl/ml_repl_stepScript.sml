
open HolKernel Parse boolLib bossLib;

val _ = new_theory "ml_repl_step";

open repl_funTheory CompilerTheory CompilerLibTheory;
open ToIntLangTheory ToBytecodeTheory terminationTheory ElabTheory;
open compilerTerminationTheory inferTheory CompilerPrimitivesTheory;
open BytecodeTheory mmlParseTheory mmlPEGTheory;

open arithmeticTheory listTheory finite_mapTheory pred_setTheory;
open ml_translatorLib ml_translatorTheory std_preludeTheory;

val _ = translation_extends "std_prelude";

(* translator setup *)

val _ = add_preferred_thy "termination";
val _ = add_preferred_thy "compilerTermination";

val lemma = prove(
  ``(b <> [] /\ x) = if b = [] then F else x``,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy "termination" name handle HOL_ERR _ =>
            def_from_thy "compilerTermination" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> RW [MEMBER_INTRO,MAP]
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY] |> RW [lemma]
  in def end

val _ = (find_def_for_const := def_of_const);

(* compiler *)

val fapply_thm = prove(
  ``fapply d x f = case FLOOKUP f x of NONE => d | SOME y => y``,
  SRW_TAC [] [fapply_def,FLOOKUP_DEF]);

val _ = translate fapply_thm;
val _ = translate compile_top_def;

(* elaborator *)

val _ = translate (def_of_const ``elab_top``);

(* parser *)

val _ = translate (def_of_const ``mmlPEG``);

val INTRO_FLOOKUP = prove(
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

val _ = export_theory();
