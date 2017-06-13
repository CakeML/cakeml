open preamble;
open compilerTheory riscv_configTheory export_riscvTheory;

(* Temporary File *)

val _ = new_theory"compiler_riscv";

val compiler_riscv_def = Define`
  compiler_riscv cl ls = compile_to_bytes riscv_backend_config riscv_export cl ls`

val _ = export_theory();
