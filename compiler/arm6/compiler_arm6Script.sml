open preamble;
open compilerTheory arm6_configTheory export_arm6Theory;

(* Temporary File *)

val _ = new_theory"compiler_arm6";

val compiler_arm6_def = Define`
  compiler_arm6 cl ls = compile_to_bytes arm6_backend_config arm6_export cl ls`

val _ = export_theory();
