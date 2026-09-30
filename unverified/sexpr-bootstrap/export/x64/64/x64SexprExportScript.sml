(*
  Exports the native x64 compiler S-expression.
*)
Theory x64SexprExport
Ancestors
  compiler64X64Prog
Libs
  preamble mlstringSyntax astSyntax astToSexprLib

val _ = write_program_def_to_file "cake-sexpr-x64-64"
            compiler64_x64_prog_def;
