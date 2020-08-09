(*
  A data-cost example of a list sum function using fold
*)

open preamble basis compilationLib;
open backendProofTheory backendPropsTheory
open costLib costPropsTheory
open dataSemTheory data_monadTheory dataLangTheory;
open x64_configProofTheory;

open preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = new_theory "sumProg"

val _ = reset_translation();

(* Int *)
val _ = ml_prog_update (open_module "Int");

val _ = trans "+" intSyntax.plus_tm;

val _ = ml_prog_update (close_module NONE);

(* List *)
val _ = ml_prog_update (open_module "List");

val result = translate FOLDL;

val _ = ml_prog_update (close_module NONE);

Overload monad_unitbind[local] = ``data_monad$bind``
Overload return[local] = ``data_monad$return``
val _ = monadsyntax.temp_add_monadsyntax()

(* sum (with mini-basis) *)

val _ = (append_prog o process_topdecs) `
  fun sum l = List.foldl Int.+ 0 l;
  `
val maincall = process_topdecs `val _ = sum [1,2,3,4,5]`

local
  val prog = get_prog(get_ml_prog_state())
in
  val sum = (rhs o concl o EVAL) ``^prog ++ ^maincall``
end

Theorem sum_prog_def = mk_abbrev "sum_prog" sum;

val _ = intermediate_prog_prefix := "sum_";
Theorem sum_thm = compile_x64 "sum" (REFL sum);
val _ = intermediate_prog_prefix := "";

val sum_data_code_def       = definition"sum_data_prog_def"
val sum_to_data_thm         = theorem"sum_to_data_thm"
val sum_config_def          = definition"sum_config_def"
val sum_x64_conf            = (rand o rator o lhs o concl) sum_thm
val sum_x64_conf_def        = mk_abbrev"sum_x64_conf" sum_x64_conf
Theorem sum_to_data_updated_thm =
  MATCH_MP (GEN_ALL  to_data_change_config) sum_to_data_thm
  |> ISPEC ((rand o rator o lhs o concl) sum_thm)
  |> SIMP_RULE (srw_ss()) [];

Theorem sum_data_code_def = sum_data_code_def;

val _ = export_theory();
