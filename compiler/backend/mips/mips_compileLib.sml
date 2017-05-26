structure mips_compileLib =
struct

open HolKernel boolLib bossLib

val _ = ParseExtras.temp_loose_equality()

open mips_targetLib asmLib;
open backendComputeLib;
open configTheory

val cmp = wordsLib.words_compset ()
val () = computeLib.extend_compset
    [computeLib.Extenders
      [backendComputeLib.add_backend_compset
      ,mips_targetLib.add_mips_encode_compset
      ,asmLib.add_asm_compset
      ],
     computeLib.Defs
      [configTheory.mips_compiler_config_def
      ,configTheory.mips_names_def]
    ] cmp

val eval = computeLib.CBV_CONV cmp

end
