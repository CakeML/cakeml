(*
  A compset for evaluating the ARMv7 instruction encoder and config.
*)
structure arm7_targetLib :> arm7_targetLib =
struct

open HolKernel boolLib bossLib
open armTheory arm7_targetTheory arm7_eval_encodeTheory utilsLib asmLib
open optionLib

structure Parse = struct
  open Parse
  val (Type, Term) =
    parse_from_grammars arm7_eval_encodeTheory.arm7_eval_encode_grammars
end
open Parse

val ERR = Feedback.mk_HOL_ERR "arm7_targetLib"

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
                  SOME ("arm7_target$arm7_enc", [t]) => SOME t
                | _ => NONE
in
  val arm7_encode_conv =
   Conv.memoize dst (Redblackmap.mkDict Term.compare) listSyntax.is_list
     (ERR "arm7_encode_conv" "")
     (computeLib.compset_conv (wordsLib.words_compset())
      [computeLib.Defs
       [arm7_bop_def, arm7_sh_def, arm7_cmp_def, EncodeImmShift_def,
        EncodeARMImmediate_def, EncodeARMImmediate_aux_def,
        valid_immediate_def, aligned, alignmentTheory.aligned_extract,
        arm7_encode_rwts],
       computeLib.Tys
        (List.map arm_type ["instruction", "offset1", "SRType", "MachineCode"]),
       computeLib.Convs
        [(bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV)],
       computeLib.Extenders [optionLib.OPTION_rws]])
end

val add_arm7_encode_compset = computeLib.extend_compset
  [computeLib.Convs [(``arm7_target$arm7_enc``, 1, arm7_encode_conv)],
   computeLib.Defs [arm7_targetTheory.arm7_config,
                    EncodeARMImmediate_def, EncodeARMImmediate_aux_def,
                    valid_immediate_def]]

val arm7_encode_conv = computeLib.compset_conv (wordsLib.words_compset())
  [computeLib.Extenders
    [utilsLib.add_base_datatypes, asmLib.add_asm_compset,
     add_arm7_encode_compset]]

val () = asmLib.add_asm_ok_thm arm7_targetTheory.arm7_asm_ok

end
