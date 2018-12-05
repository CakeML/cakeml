(*
  A compset for evaluating the ARMv6 instruction encoder and config.
*)
structure arm6_targetLib :> arm6_targetLib =
struct

open HolKernel boolLib bossLib
open armTheory arm6_targetTheory arm6_eval_encodeTheory utilsLib asmLib
open optionLib

structure Parse = struct
  open Parse
  val (Type, Term) =
    parse_from_grammars arm6_eval_encodeTheory.arm6_eval_encode_grammars
end
open Parse

val ERR = Feedback.mk_HOL_ERR "arm6_targetLib"

fun arm_type s = Type.mk_thy_type {Thy = "arm", Tyop = s, Args = []}

val aligned =
   let
      open alignmentTheory
   in
      SIMP_RULE std_ss [aligned_0, aligned_1_lsb, aligned_extract]
         arm_stepTheory.Aligned
   end

local
  fun dst tm = case Lib.total boolSyntax.dest_strip_comb tm of
                  SOME ("arm6_target$arm6_enc", [t]) => SOME t
                | _ => NONE
in
  val arm6_encode_conv =
   Conv.memoize dst (Redblackmap.mkDict Term.compare) listSyntax.is_list
     (ERR "arm6_encode_conv" "")
     (computeLib.compset_conv (wordsLib.words_compset())
      [computeLib.Defs
       [arm6_bop_def, arm6_sh_def, arm6_cmp_def, EncodeImmShift_def,
        EncodeARMImmediate_def, EncodeARMImmediate_aux_def,
        valid_immediate_def, aligned, alignmentTheory.aligned_extract,
        arm6_encode_rwts],
       computeLib.Tys
        (List.map arm_type ["instruction", "offset1", "SRType", "MachineCode"]),
       computeLib.Convs
        [(bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV)],
       computeLib.Extenders [optionLib.OPTION_rws]])
end

val add_arm6_encode_compset = computeLib.extend_compset
  [computeLib.Convs [(``arm6_target$arm6_enc``, 1, arm6_encode_conv)],
   computeLib.Defs [arm6_targetTheory.arm6_config,
                    EncodeARMImmediate_def, EncodeARMImmediate_aux_def,
                    valid_immediate_def]]

val arm6_encode_conv = computeLib.compset_conv (wordsLib.words_compset())
  [computeLib.Extenders
    [utilsLib.add_base_datatypes, asmLib.add_asm_compset,
     add_arm6_encode_compset]]

val () = asmLib.add_asm_ok_thm arm6_targetTheory.arm6_asm_ok

end
