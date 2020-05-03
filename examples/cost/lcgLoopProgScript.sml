(*
  A data-cost example of a non-terminating function that generates
  entries of a Linear Congruential Generator (LCG) indefinitely.

  https://en.wikipedia.org/wiki/Linear_congruential_generator
*)

open preamble basis compilationLib;
(* open miniBasisProgTheory; *)

val _ = new_theory "lcgLoopProg"

(* val _ = translation_extends "miniBasisProg"; *)

(* X_{n+1} = (a X_n + c) mod m *)
val lcg_def = Define`
  lcg a c m x = (a * x + c) MOD m`

val _ = translate lcg_def;

val _ = (append_prog o process_topdecs) `
  fun lcgLoop a c m x =
  let
    val x1 = lcg a c m x
  in
    lcgLoop a c m x1
  end;`

val maincall = process_topdecs `val _ = lcgLoop 8121 28411 134456 42;`

local
  val prog = get_prog(get_ml_prog_state())
in
  val lcgLoop = (rhs o concl o EVAL) ``^prog ++ ^maincall``
end

Definition lcgLoop_ast_def:
  lcgLoop_ast = ^lcgLoop
End

val _ = intermediate_prog_prefix := "lcgLoop_";
Theorem lcgLoop_thm = compile_x64 1000 1000 "lcgLoop" (REFL lcgLoop);
val _ = intermediate_prog_prefix := "";

val lcgLoop_data_code_def       = definition"lcgLoop_data_prog_def"
val lcgLoop_to_data_thm         = theorem"lcgLoop_to_data_thm"
val lcgLoop_config_def          = definition"lcgLoop_config_def"
val lcgLoop_to_data_updated_thm =
  MATCH_MP (GEN_ALL  to_data_change_config) lcgLoop_to_data_thm
  |> ISPEC ((rand o rator o lhs o concl) lcgLoop_thm)
  |> SIMP_RULE (srw_ss()) [];

Theorem lcgLoop_data_code_def = lcgLoop_data_code_def;
Theorem lcgLoop_to_data_updated_thm = lcgLoop_to_data_updated_thm;

val _ = export_theory();
