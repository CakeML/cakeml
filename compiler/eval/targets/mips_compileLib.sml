structure mips_compileLib =
struct

open HolKernel boolLib bossLib

val _ = ParseExtras.temp_loose_equality()

open mips_targetLib asmLib;
open compilerComputeLib;
open configTheory

val cmp = wordsLib.words_compset ()
val () = computeLib.extend_compset
    [computeLib.Extenders
      [compilerComputeLib.add_compiler_compset
      ,mips_targetLib.add_mips_encode_compset
      ,asmLib.add_asm_compset
      ],
     computeLib.Defs
      [configTheory.mips_compiler_config_def]
    ] cmp

val eval = computeLib.CBV_CONV cmp

end
