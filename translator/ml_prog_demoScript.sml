open preamble
open ml_progLib;

val _ = new_theory "ml_prog_demo";

val prog_tm = EVAL ``basis_program`` |> concl |> rand

fun pick_name str =
  if str = "<" then "lt" else
  if str = ">" then "gt" else
  if str = "<=" then "le" else
  if str = ">=" then "ge" else
  if str = "=" then "eq" else
  if str = "~" then "uminus" else
  if str = "+" then "plus" else
  if str = "-" then "minus" else
  if str = "*" then "times" else
  if str = "!" then "deref" else
  if str = ":=" then "update" else str (* name is fine *)

val th = get_thm (add_prog prog_tm pick_name init_state)
val th = REWRITE_RULE [GSYM (EVAL ``basis_program``)] th

val basis_program_env = save_thm("basis_program_env",
  th |> CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL THENC RAND_CONV EVAL));

val _ = export_theory();
