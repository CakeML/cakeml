(*
  Provides a compset for the ARMv6-specific parts of the backend
*)
structure arm6_compileLib =
struct

open HolKernel boolLib bossLib

open arm6_targetLib asmLib;
open backendComputeLib;
open arm6_configTheory

val cmp = wordsLib.words_compset ()
val () = computeLib.extend_compset
    [computeLib.Extenders
      [backendComputeLib.add_backend_compset
      ,arm6_targetLib.add_arm6_encode_compset
      ,asmLib.add_asm_compset
      ],
     computeLib.Defs
      [arm6_configTheory.arm6_backend_config_def
      ,arm6_configTheory.arm6_names_def]
    ] cmp

val eval = computeLib.CBV_CONV cmp

end
