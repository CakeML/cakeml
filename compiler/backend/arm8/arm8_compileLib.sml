(*
  Provides a compset for the ARMv8-specific parts of the backend
*)
structure arm8_compileLib =
struct

open HolKernel boolLib bossLib

open arm8_targetLib asmLib;
open backendComputeLib;
open arm8_configTheory

val cmp = wordsLib.words_compset ()
val () = computeLib.extend_compset
    [computeLib.Extenders
      [backendComputeLib.add_backend_compset
      ,arm8_targetLib.add_arm8_encode_compset
      ,asmLib.add_asm_compset
      ],
     computeLib.Defs
      [arm8_configTheory.arm8_backend_config_def
      ,arm8_configTheory.arm8_names_def]
    ] cmp

val eval = computeLib.CBV_CONV cmp

end
