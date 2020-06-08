(*
  A data-cost example of a reverse
*)

open preamble basis compilationLib;
open backendProofTheory backendPropsTheory
open costLib costPropsTheory
open dataSemTheory data_monadTheory dataLangTheory;
open miniBasisProgTheory;
open x64_configProofTheory;

val _ = new_theory "reverseProg"

Overload monad_unitbind[local] = ``data_monad$bind``
Overload return[local] = ``data_monad$return``

val _ = monadsyntax.temp_add_monadsyntax()

val whole_prog = whole_prog ()

val reverse_term =
 “[Dletrec
       (Locs <|row := 1; col := 16; offset := 0|>
          <|row := 3; col := 42; offset := 0|>)
       [("reverse","l",
         Mat (Var (Short "l"))
           [(Pcon (SOME (Short "[]")) [],Con (SOME (Short "[]")) []);
            (Pcon (SOME (Short "::")) [Pvar "f"; Pvar "r"],
             (App ListAppend [App Opapp [Var (Short "reverse"); Var (Short "r")];
                              Con (SOME (Short "::"))
                              [Var (Short "f");
                               Con (SOME (Short "[]")) []]]))])]]”

val _ = append_prog reverse_term

val maincall = process_topdecs `val _ = reverse["x","y"]`

local
  val prog = get_prog(get_ml_prog_state())
in
  val reverse = (rhs o concl o EVAL) ``^prog ++ ^maincall``
end

Theorem reverse_prog_def = mk_abbrev "reverse_prog" reverse;

val _ = intermediate_prog_prefix := "reverse_";
Theorem reverse_thm = compile_x64 1000 1000 "reverse" (REFL reverse);
val _ = intermediate_prog_prefix := "";

val reverse_data_code_def       = definition"reverse_data_prog_def"
val reverse_to_data_thm         = theorem"reverse_to_data_thm"
val reverse_config_def          = definition"reverse_config_def"
val reverse_x64_conf            = (rand o rator o lhs o concl) reverse_thm
val reverse_x64_conf_def        = mk_abbrev"reverse_x64_conf" reverse_x64_conf
Theorem reverse_to_data_updated_thm =
  MATCH_MP (GEN_ALL  to_data_change_config) reverse_to_data_thm
  |> ISPEC ((rand o rator o lhs o concl) reverse_thm)
  |> SIMP_RULE (srw_ss()) [];

Theorem reverse_data_code_def = reverse_data_code_def;

val _ = export_theory();
