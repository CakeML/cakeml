(*
  Provides a compset for the MIPS-specific parts of the backend
*)
structure mips_compileLib =
struct

open HolKernel boolLib bossLib

open mips_targetLib asmLib;
open backendComputeLib;
open mips_configTheory

val cmp = wordsLib.words_compset ()
val () = computeLib.extend_compset
    [computeLib.Extenders
      [backendComputeLib.add_backend_compset
      ,mips_targetLib.add_mips_encode_compset
      ,asmLib.add_asm_compset
      ],
     computeLib.Defs
      [mips_configTheory.mips_backend_config_def
      ,mips_configTheory.mips_names_def]
    ] cmp

val eval = computeLib.CBV_CONV cmp

end
