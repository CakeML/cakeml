open preamble;
open compilerTheory x64_configTheory export_x64Theory;

(* Temporary File *)

val _ = new_theory"compiler_x64";

val compiler_x64_def = Define`
  compiler_x64 cl ls = compile_to_bytes x64_backend_config x64_export cl ls`

val sexp_compiler_x64_def = Define`
  sexp_compiler_x64 cl ls = sexp_compile_to_bytes x64_backend_config x64_export cl ls`;

val _ = export_theory();
