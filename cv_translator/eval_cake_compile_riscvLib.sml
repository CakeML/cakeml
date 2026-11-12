(*
  Functions for in-logic evaluation of the CakeML compiler for RISC-V.
*)
structure eval_cake_compile_riscvLib =
struct

local

  open HolKernel Parse boolLib eval_cake_compileLib;

  val arch_spec = INST_TYPE [alpha |-> ``:64``];

  val riscv_arch_thms =
    { default_config_def       = riscv_configTheory.riscv_backend_config_def
    , to_livesets_def          = arch_spec backend_riscvTheory.to_livesets_riscv_def
    , compile_cake_def         = arch_spec backend_riscvTheory.compile_cake_riscv_def
    , compile_cake_imp         = arch_spec backend_riscvTheory.compile_cake_riscv_thm
    , compile_cake_explore_def = arch_spec backend_riscvTheory.compile_cake_explore_riscv_def
    , cv_export_def            = backend_riscv_cvTheory.cv_riscv_export_def } : arch_thms;

in

  val eval_cake_compile_riscv =
      eval_cake_compile riscv_arch_thms;

  val eval_cake_compile_riscv_with_conf =
      eval_cake_compile_with_conf riscv_arch_thms;

  val eval_cake_compile_explore_riscv =
      eval_cake_compile_explore riscv_arch_thms;

  val eval_cake_compile_explore_riscv_with_conf =
      eval_cake_compile_explore_with_conf riscv_arch_thms;

  val eval_cake_compile_riscv_general =
      eval_cake_compile_general riscv_arch_thms;

end

end
