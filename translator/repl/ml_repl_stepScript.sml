
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

fun def_of_const tm = let
  val res = dest_thy_const tm
  in DB.fetch (#Thy res) ((#Name res) ^ "_def") handle HOL_ERR _ =>
     DB.fetch (#Thy res) ((#Name res) ^ "_DEF") handle HOL_ERR _ =>
     DB.fetch (#Thy res) (#Name res) end

val CCRef_expand =
  prove(``CCRef = \x. CCRef x``, SIMP_TAC std_ss [FUN_EQ_THM]);

val CTEnv_expand =
  prove(``CTEnv = \x. CTEnv x``, SIMP_TAC std_ss [FUN_EQ_THM]);

val fapply_thm = prove(
  ``fapply d x f = case FLOOKUP f x of NONE => d | SOME y => y``,
  SRW_TAC [] [fapply_def,FLOOKUP_DEF]);

val _ = translate fapply_thm;

val _ = translate (lunion_def |> RW [MEMBER_INTRO]);
val _ = translate lshift_def;
val _ = translate number_constructors_def;
val _ = translate pat_bindings_def;
val _ = translate Cpat_vars_def;
val _ = translate mkshift_def;
val _ = translate shift_def;
val _ = translate remove_mat_vp_def;
val _ = translate remove_mat_var_def;
val _ = translate find_index_def;
val _ = translate cmap_def;
val _ = translate etC_def;
val _ = translate emit_def;
val _ = translate cbv_def;
val _ = translate get_label_def;
val _ = translate the_def;
val _ = translate free_vars_def;
val _ = translate (bind_fv_def |> RW1 [MEMBER_INTRO,CCRef_expand]);
val _ = translate free_labs_def;
val _ = translate pushret_def;
val _ = translate i0_def;
val _ = translate i1_def;
val _ = translate i2_def;
val _ = translate error_to_int_def;
val _ = translate compile_envref_def;
val _ = translate compile_varref_def;
val _ = translate unit_tag_def;
val _ = translate bool_to_tag_def;
val _ = translate block_tag_def;
val _ = translate closure_tag_def;
val _ = translate num_fold_def;
val _ = translate push_lab_def;
val _ = translate el_check_def;
val _ = translate emit_ceref_def;
val _ = translate emit_ceenv_def;
val _ = translate cons_closure_def;
val _ = translate update_refptr_def;
val _ = translate compile_closures_def;
val _ = translate prim1_to_bc_def;
val _ = translate prim2_to_bc_def;
val _ = translate compile_def;
val _ = translate (cce_aux_def |> RW1 [CTEnv_expand]);
val _ = translate compile_code_env_def;
val _ = translate label_closures_def;
val _ = translate compile_Cexp_def;
val _ = translate (compile_shadows_def |> RW [MAP]);
val _ = translate (compile_news_def |> RW [MAP]);
val _ = translate pat_to_Cpat_def;
val _ = translate exp_to_Cexp_def;
val _ = translate (compile_fake_exp_def |> RW [MEMBER_INTRO]);
val _ = translate compile_dec_def;
val _ = translate compile_top_def;


val _ = export_theory();
