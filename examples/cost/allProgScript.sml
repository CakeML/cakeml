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

val _ = new_theory "allProg"

val _ = reset_translation();

(* List *)
val _ = ml_prog_update (open_module "List");

val result = translate FOLDL;

val _ = ml_prog_update (close_module NONE);

Definition all_def:
  all l = FOLDL (λa b. a /\ b) T l
End

val _ = translate all_def;

val maincall = process_topdecs `val _ = all [True,False,True,True,False]`

Overload monad_unitbind[local] = ``data_monad$bind``
Overload return[local] = ``data_monad$return``
val _ = monadsyntax.temp_add_monadsyntax()

local
  val prog = get_prog(get_ml_prog_state())
in
  val all = (rhs o concl o EVAL) ``^prog ++ ^maincall``
end

Theorem all_prog_def = mk_abbrev "all_prog" all;

val _ = intermediate_prog_prefix := "all_";
Theorem all_thm = compile_x64 "all" (REFL all);
val _ = intermediate_prog_prefix := "";

val all_data_code_def       = definition"all_data_prog_def"
val all_to_data_thm         = theorem"all_to_data_thm"
val all_config_def          = definition"all_config_def"
val all_x64_conf            = (rand o rator o lhs o concl) all_thm
val all_x64_conf_def        = mk_abbrev"all_x64_conf" all_x64_conf
Theorem all_to_data_updated_thm =
  MATCH_MP (GEN_ALL  to_data_change_config) all_to_data_thm
  |> ISPEC ((rand o rator o lhs o concl) all_thm)
  |> SIMP_RULE (srw_ss()) [];

Theorem all_data_code_def = all_data_code_def;

val _ = export_theory();
