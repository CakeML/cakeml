
open HolKernel Parse boolLib bossLib;

val _ = new_theory "ml_repl_step";

open repl_funTheory CompilerTheory CompilerLibTheory;
open ToIntLangTheory ToBytecodeTheory terminationTheory ElabTheory;
open compilerTerminationTheory inferTheory CompilerPrimitivesTheory;
open BytecodeTheory;

open arithmeticTheory listTheory finite_mapTheory;
open ml_translatorLib ml_translatorTheory std_preludeTheory;

val _ = translation_extends "std_prelude";



(* types *)

val _ = register_type ``:top``;     (* AstTheory *)
val _ = register_type ``:ast_top``; (* ElabTheory *)
val _ = register_type ``:Cexp``;    (* TntLangTheory *)
val _ = register_type ``:bc_inst``; (* bytecode instruction *)
val _ = register_type ``:compiler_state``;

(* compiler *)

val CCRef_expand =
  prove(``CCRef = \x. CCRef x``, SIMP_TAC std_ss [FUN_EQ_THM]);

val CTEnv_expand =
  prove(``CTEnv = \x. CTEnv x``, SIMP_TAC std_ss [FUN_EQ_THM]);

fun def_of_const tm = let
  val res = dest_thy_const tm
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
  val def = def |> RW1 [CCRef_expand,CTEnv_expand]
                |> RW [MEMBER_INTRO,MAP]
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
  in def end

val _ = (find_def_for_const := def_of_const);

val fapply_thm = prove(
  ``fapply d x f = case FLOOKUP f x of NONE => d | SOME y => y``,
  SRW_TAC [] [fapply_def,FLOOKUP_DEF]);

val _ = translate fapply_thm;
val _ = translate compile_top_def;


val _ = export_theory();
