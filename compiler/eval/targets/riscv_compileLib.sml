structure riscv_compileLib =
struct

open HolKernel boolLib bossLib

val _ = ParseExtras.temp_loose_equality()

open riscv_targetLib asmLib;
open compilerComputeLib;
open riscv_configTheory

val cmp = wordsLib.words_compset ()
val () = computeLib.extend_compset
    [computeLib.Extenders
      [compilerComputeLib.add_compiler_compset
      ,riscv_targetLib.add_riscv_encode_compset
      ,asmLib.add_asm_compset
      ],
     computeLib.Defs
      [riscv_configTheory.riscv_compiler_config_def]
    ] cmp

val eval = computeLib.CBV_CONV cmp

end
