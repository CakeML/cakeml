(*
  Exports the target-independent 32-bit compiler S-expression.
*)
Theory sexpr32Export
Ancestors
  compiler32Prog
Libs
  preamble mlstringSyntax astSyntax astToSexprLib

val _ = write_program_def_to_file "cake-sexpr-32" compiler32_prog_def;
