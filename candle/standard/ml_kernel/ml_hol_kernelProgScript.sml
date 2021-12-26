(*
  Close the kernel module from ml_hol_kernel_funsProg
*)
open preamble;
open ml_translatorLib ml_monad_translatorLib ml_progLib ml_hol_kernel_funsProgTheory;

val _ = new_theory "ml_hol_kernelProg";

val _ = m_translation_extends "ml_hol_kernel_funsProg"

val def = mk_eq_def |> check [‘l’,‘r’] |> m_translate
val res = translate (check [‘tm1’,‘tm2’] aconv_def);
val res = translate (check [‘tm’ ]holKernelPmatchTheory.is_eq_def);
val def = mk_fun_ty_def |> check [‘ty1’,‘ty2’] |> m_translate;

val _ = next_ml_names := ["SYM"];
val def = holKernelPmatchTheory.SYM_def |> m_translate

val _ = next_ml_names := ["PROVE_HYP"];
val def = PROVE_HYP_def |> m_translate

val _ = next_ml_names := ["ALPHA_THM"];
val def = ALPHA_THM_def |> check [‘h'’,‘c'’] |> m_translate

val def = axioms_def |> m_translate
val def = types_def |> m_translate
val def = constants_def |> m_translate
val def = context_def |> m_translate

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

val _ = export_theory();
