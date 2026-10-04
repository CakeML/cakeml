(*
  Exports the native ARM8 compiler S-expression.
*)
Theory arm8SexprExport
Ancestors
  compiler64Arm8Prog
Libs
  preamble mlstringSyntax astSyntax astToSexprLib

val _ = write_program_def_to_file "cake-sexpr-arm8-64"
            compiler64_arm8_prog_def;
