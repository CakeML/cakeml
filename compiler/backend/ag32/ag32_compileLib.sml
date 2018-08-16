structure ag32_compileLib =
struct

open HolKernel boolLib bossLib

val _ = ParseExtras.temp_loose_equality()

open ag32_targetLib asmLib;
open backendComputeLib;
open ag32_configTheory

val cmp = wordsLib.words_compset ()
val () = computeLib.extend_compset
    [computeLib.Extenders
      [backendComputeLib.add_backend_compset
      ,ag32_targetLib.add_ag32_encode_compset
      ,asmLib.add_asm_compset
      ],
     computeLib.Defs
      [ag32_configTheory.ag32_backend_config_def
      ,ag32_configTheory.ag32_names_def]
    ] cmp

val eval = computeLib.CBV_CONV cmp

end
