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

val _ = new_theory "appendProg"

val _ = reset_translation();

(* List *)
val _ = ml_prog_update (open_module "List");

val append_v_thm = trans "@" listSyntax.append_tm;
val _ = save_thm("append_v_thm",append_v_thm);

val _ = ml_prog_update (close_module NONE);

Overload monad_unitbind[local] = ``data_monad$bind``
Overload return[local] = ``data_monad$return``
val _ = monadsyntax.temp_add_monadsyntax()

(* sum (with mini-basis) *)

val _ = (append_prog o process_topdecs) `
fun app123 l = let val a = [1,2,3] in a @ l end;
`

val maincall = process_topdecs `val _ = app123 [5,6,7,8,9]`

local
  val prog = get_prog(get_ml_prog_state())
in
  val sum = (rhs o concl o EVAL) ``^prog ++ ^maincall``
end

Theorem sum_prog_def = mk_abbrev "app123_prog" sum;

val _ = intermediate_prog_prefix := "app123_";
Theorem app123_thm = compile_x64 "app123" (REFL sum);
val _ = intermediate_prog_prefix := "";

val app123_data_code_def       = definition"app123_data_prog_def"
val app123_to_data_thm         = theorem"app123_to_data_thm"
val app123_config_def          = definition"app123_config_def"
val app123_x64_conf            = (rand o rator o lhs o concl) app123_thm
val app123_x64_conf_def        = mk_abbrev"app123_x64_conf" app123_x64_conf
Theorem app123_to_data_updated_thm =
  MATCH_MP (GEN_ALL  to_data_change_config) app123_to_data_thm
  |> ISPEC ((rand o rator o lhs o concl) app123_thm)
  |> SIMP_RULE (srw_ss()) [];

Theorem app123_data_code_def = app123_data_code_def;

val _ = export_theory();
