open preamble;
open compilerTheory arm8_configTheory export_arm8Theory;

(* Temporary File *)

val _ = new_theory"compiler_arm8";

val compiler_arm8_def = Define`
  compiler_arm8 cl ls = compile_to_bytes arm8_backend_config arm8_export cl ls`

val _ = export_theory();
