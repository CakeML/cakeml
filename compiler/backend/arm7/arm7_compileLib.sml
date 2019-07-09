(*
  Provides a compset for the ARMv7-specific parts of the backend
*)
structure arm7_compileLib =
struct

open HolKernel boolLib bossLib

open arm7_targetLib asmLib;
open backendComputeLib;
open arm7_configTheory

val cmp = wordsLib.words_compset ()
val () = computeLib.extend_compset
    [computeLib.Extenders
      [backendComputeLib.add_backend_compset
      ,arm7_targetLib.add_arm7_encode_compset
      ,asmLib.add_asm_compset
      ],
     computeLib.Defs
      [arm7_configTheory.arm7_backend_config_def
      ,arm7_configTheory.arm7_names_def]
    ] cmp

val eval = computeLib.CBV_CONV cmp

end
