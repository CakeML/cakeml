(*
  A data-cost example of a non-terminating function (pureLoop)
*)

open preamble basis compilationLib;
open backendProofTheory backendPropsTheory;
open costLib costPropsTheory;
open dataSemTheory data_monadTheory dataLangTheory;

val _ = new_theory "pureLoopProg"


Overload monad_unitbind[local] = ``data_monad$bind``
Overload return[local] = ``data_monad$return``

val _ = monadsyntax.temp_add_monadsyntax()

(* ************ *)
(* * pureLoop * *)
(* ************ *)

(* A simple infinite loop that does nothing *)

val pureLoop2 = process_topdecs
  `fun pureLoop x = pureLoop (x+1);
   val _ = pureLoop 1`

Definition pureLoop2_ast_def:
  pureLoop2_ast = ^pureLoop2
End

val _ = intermediate_prog_prefix := "pureLoop2_"
val pureLoop2_thm = compile_x64 1000 1000 "pureLoop2" (REFL pureLoop2)
val _ = intermediate_prog_prefix := ""

val pureLoop2_data_code_def       = definition"pureLoop2_data_prog_def"
val pureLoop2_to_data_thm         = theorem"pureLoop2_to_data_thm"
val pureLoop2_config_def          = definition"pureLoop2_config_def"
val pureLoop2_to_data_updated_thm =
  MATCH_MP (GEN_ALL  to_data_change_config) pureLoop2_to_data_thm
  |> ISPEC ((rand o rator o lhs o concl) pureLoop2_thm)
  |> SIMP_RULE (srw_ss()) [];

val pureLoop = process_topdecs
  `fun pureLoop x = pureLoop x;
   val _ = pureLoop 1`;

Definition pureLoop_ast_def:
  pureLoop_ast = ^pureLoop
End

val _ = intermediate_prog_prefix := "pureLoop_";
Theorem pureLoop_thm = compile_x64 1000 1000 "pureLoop" (REFL pureLoop);
val _ = intermediate_prog_prefix := "";

val pureLoop_data_code_def       = definition"pureLoop_data_prog_def"
val pureLoop_to_data_thm         = theorem"pureLoop_to_data_thm"
val pureLoop_config_def          = definition"pureLoop_config_def"
val pureLoop_to_data_updated_thm =
  MATCH_MP (GEN_ALL  to_data_change_config) pureLoop_to_data_thm
  |> ISPEC ((rand o rator o lhs o concl) pureLoop_thm)
  |> SIMP_RULE (srw_ss()) [];

val (p1,p2) = diff_code pureLoop_data_code_def pureLoop2_data_code_def;

Definition pureLoop_fun_def:
  pureLoop_fun = ^p1
End

Theorem pureLoop_data_code_def = pureLoop_data_code_def;
Theorem pureLoop2_data_code_def = pureLoop2_data_code_def;
Theorem pureLoop_to_data_updated_thm = pureLoop_to_data_updated_thm;

val _ = export_theory();
