structure tiny_compileLib =
struct

open HolKernel boolLib bossLib

val _ = ParseExtras.temp_loose_equality()

open tiny_targetLib asmLib;
open backendComputeLib;
open tiny_configTheory

val cmp = wordsLib.words_compset ()
val () = computeLib.extend_compset
    [computeLib.Extenders
      [backendComputeLib.add_backend_compset
      ,tiny_targetLib.add_tiny_encode_compset
      ,asmLib.add_asm_compset
      ],
     computeLib.Defs
      [tiny_configTheory.tiny_backend_config_def
      ,tiny_configTheory.tiny_names_def]
    ] cmp

val eval = computeLib.CBV_CONV cmp

end
