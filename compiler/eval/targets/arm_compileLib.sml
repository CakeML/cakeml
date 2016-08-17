structure arm_compileLib =
struct

open HolKernel boolLib bossLib

val _ = ParseExtras.temp_loose_equality()

open arm6_targetLib asmLib;
open compilerComputeLib;
open arm_configTheory

val cmp = wordsLib.words_compset ()
val () = computeLib.extend_compset
    [computeLib.Extenders
      [compilerComputeLib.add_compiler_compset
      ,arm6_targetLib.add_arm6_encode_compset
      ,asmLib.add_asm_compset
      ],
     computeLib.Defs
      [arm_configTheory.arm_compiler_config_def]
    ] cmp

val eval = computeLib.CBV_CONV cmp

end
