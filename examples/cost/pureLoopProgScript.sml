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

val pureLoop = process_topdecs
  `fun pureLoop x = pureLoop x;
   val _ = pureLoop 1`;

Definition pureLoop_ast_def:
  pureLoop_ast = ^pureLoop
End

val _ = intermediate_prog_prefix := "pureLoop_";
Theorem pureLoop_thm = compile_x64 "pureLoop" (REFL pureLoop);
val _ = intermediate_prog_prefix := "";

val pureLoop_data_code_def       = definition"pureLoop_data_prog_def"
val pureLoop_to_data_thm         = theorem"pureLoop_to_data_thm"
val pureLoop_config_def          = definition"pureLoop_config_def"
val pureLoop_to_data_updated_thm =
  MATCH_MP (GEN_ALL  to_data_change_config) pureLoop_to_data_thm
  |> ISPEC ((rand o rator o lhs o concl) pureLoop_thm)
  |> SIMP_RULE (srw_ss()) [];

Theorem pureLoop_data_code_def = pureLoop_data_code_def;
Theorem pureLoop_to_data_updated_thm = pureLoop_to_data_updated_thm;

val _ = export_theory();
