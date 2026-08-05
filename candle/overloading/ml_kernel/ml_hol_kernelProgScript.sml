(*
  Close the kernel module from ml_hol_kernel_funsProg
*)
Theory ml_hol_kernelProg
Ancestors
  ml_hol_kernel_funsProg ml_pmatch holKernel
  holKernelPmatch[qualified]
Libs
  preamble ml_translatorLib ml_monad_translatorLib ml_progLib

val _ = m_translation_extends "ml_hol_kernel_funsProg"

(* Translation of functions used by e.g. the OpenTheory checker. *)

val def = m_translate mk_eq_def;
val res = translate aconv_def;
val res = translate holKernelPmatchTheory.is_eq_def;
val def = m_translate mk_fun_ty_def;

val _ = next_ml_names := ["SYM"];
val def = m_translate holKernelPmatchTheory.SYM_def;

val _ = next_ml_names := ["PROVE_HYP"];
val def = m_translate PROVE_HYP_def;

val _ = next_ml_names := ["ALPHA_THM"];
val def = m_translate ALPHA_THM_def;

val def = m_translate context_def;

val _ = ml_prog_update close_local_blocks;
val _ = ml_prog_update (close_module NONE);

(* extract the interesting theorem *)

val _ = Globals.max_print_depth := 10;

fun define_abbrev_conv name tm = let
  val def = define_abbrev true name tm
  in GSYM def |> SPEC_ALL end

Theorem candle_prog_thm =
  get_Decls_thm (get_ml_prog_state())
  |> CONV_RULE ((RATOR_CONV o RATOR_CONV o RAND_CONV)
                (EVAL THENC define_abbrev_conv "candle_code"))
  |> CONV_RULE ((RATOR_CONV o RAND_CONV)
                (EVAL THENC define_abbrev_conv "candle_init_env"))
  |> CONV_RULE ((RAND_CONV)
                (EVAL THENC define_abbrev_conv "candle_init_state"));

(* extract some other other theorems *)

Theorem EqualityType_TYPE_TYPE = EqualityType_rule [] “:type”;

Theorem EqualityType_TERM_TYPE = EqualityType_rule [] “:term”;

Theorem EqualityType_THM_TYPE = EqualityType_rule [] “:thm”;

Theorem EqualityType_UPDATE_TYPE = EqualityType_rule [] “:update”;

val _ = (print_asts := true);

