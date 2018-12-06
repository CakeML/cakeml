(*
  Provides an eval for the RISC-V-specific parts of the backend
*)
structure riscv_compileLib =
struct

open HolKernel boolLib bossLib

open riscv_targetLib asmLib;
open backendComputeLib;
open riscv_configTheory

val cmp = wordsLib.words_compset ()
val () = computeLib.extend_compset
    [computeLib.Extenders
      [backendComputeLib.add_backend_compset
      ,riscv_targetLib.add_riscv_encode_compset
      ,asmLib.add_asm_compset
      ],
     computeLib.Defs
      [riscv_configTheory.riscv_backend_config_def
      ,riscv_configTheory.riscv_names_def]
    ] cmp

val eval = computeLib.CBV_CONV cmp

end
