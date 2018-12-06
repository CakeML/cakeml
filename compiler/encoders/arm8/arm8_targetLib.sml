(*
  A compset for evaluating the ARMv8 instruction encoder and config.
*)
structure arm8_targetLib :> arm8_targetLib =
struct

open HolKernel boolLib bossLib
open arm8Theory arm8_targetTheory utilsLib asmLib
open optionLib

val ERR = Feedback.mk_HOL_ERR "arm8_targetLib"

fun arm_type s = Type.mk_thy_type {Thy = "arm8", Tyop = s, Args = []}

val arm8_ast = REWRITE_RULE [bop_enc_def, astTheory.shift_distinct] arm8_ast_def
val arm8_enc =
  SIMP_RULE (srw_ss()) [listTheory.LIST_BIND_def] (Q.AP_THM arm8_enc_def `x`)

val es =
  computeLib.Extenders
    [integer_wordLib.add_integer_word_compset, intReduce.add_int_compset,
     bitstringLib.add_bitstring_compset, asmLib.add_asm_compset,
     optionLib.OPTION_rws, pairLib.add_pair_compset]

local
  fun dst tm = case Lib.total boolSyntax.dest_strip_comb tm of
                  SOME ("arm8_target$arm8_enc", [t]) => SOME t
                | _ => NONE
in
  val arm8_encode_conv =
   Conv.memoize dst (Redblackmap.mkDict Term.compare) listSyntax.is_list
     (ERR "arm8_encode_conv" "")
     (computeLib.compset_conv (wordsLib.words_compset())
      [computeLib.Defs
       [arm8_enc, arm8_ast, arm8_load_store_ast_def, arm8_encode_def,
        bop_enc_def, cmp_cond_def, arm8_enc_mov_imm_def, CountTrailing_def,
        EncodeBitMaskAux_def, EncodeBitMask_def, Encode_def, e_data_def,
        e_branch_def, e_load_store_def, e_sf_def, e_LoadStoreImmediate_def,
        EncodeLogicalOp_def, NoOperation_def, ShiftType2num_thm,
        SystemHintOp2num_thm, ShiftType2num_thm, DecodeBitMasks_def,
        HighestSetBit_def, Ones_def, Replicate_def, pred_setTheory.IN_INSERT,
        pred_setTheory.NOT_IN_EMPTY],
       es,
       computeLib.Convs
       [(bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV)],
       computeLib.Tys
       (``:('a, 'b) sum`` ::
         List.map arm_type
          ["instruction", "Data", "Branch", "LoadStore", "SystemHintOp",
           "MoveWideOp", "LogicalOp", "MemOp", "BranchType", "ShiftType",
           "AccType", "MachineCode"])])
end

local
  fun dst tm = case Lib.total boolSyntax.dest_strip_comb tm of
                  SOME ("arm8_target$valid_immediate", [_, _]) => SOME tm
                | _ => NONE
in
  val valid_immediate_conv =
    Conv.memoize dst (Redblackmap.mkDict Term.compare)
      (fn tm => Teq tm orelse Feq tm)
      (ERR "valid_immediate_conv" "")
      (computeLib.compset_conv (wordsLib.words_compset())
        [computeLib.Defs
           [valid_immediate_def, EncodeBitMask_def, EncodeBitMaskAux_def,
            CountTrailing_def, DecodeBitMasks_def, HighestSetBit_def, Ones_def,
            Replicate_def,
            pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY],
         computeLib.Tys [``:('a, 'b) sum``], es])
end

val add_arm8_encode_compset = computeLib.extend_compset
  [computeLib.Convs
     [(``arm8_target$arm8_enc``, 1, arm8_encode_conv),
      (``arm8_target$valid_immediate``, 2, valid_immediate_conv)],
   computeLib.Defs [arm8_targetTheory.arm8_config]]

val arm8_encode_decode_conv = computeLib.compset_conv (wordsLib.words_compset())
  [computeLib.Extenders
     [utilsLib.add_base_datatypes, asmLib.add_asm_compset,
      add_arm8_encode_compset]]

val () = asmLib.add_asm_ok_thm arm8_targetTheory.arm8_asm_ok

end
