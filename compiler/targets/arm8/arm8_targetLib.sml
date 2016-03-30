structure arm8_targetLib :> arm8_targetLib =
struct

open HolKernel boolLib bossLib
open arm8Theory arm8_targetTheory utilsLib asmLib
open optionLib

val ERR = Feedback.mk_HOL_ERR "arm8_targetLib"

fun arm_type s = Type.mk_thy_type {Thy = "arm8", Tyop = s, Args = []}

val arm8_enc = REWRITE_RULE [bop_enc_def, asmTheory.shift_distinct] arm8_enc_def

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
       [arm8_enc, arm8_encode_def, bop_enc_def, bop_dec_def, cmp_cond_def,
        arm8_enc_mov_imm_def, CountTrailing_def, EncodeBitMaskAux_def,
        EncodeBitMask_def, Encode_def, e_data_def, e_branch_def,
        e_load_store_def, e_sf_def, e_LoadStoreImmediate_def,
        EncodeLogicalOp_def, NoOperation_def, ShiftType2num_thm,
        SystemHintOp2num_thm, ShiftType2num_thm, LSL_def, LSR_def,
        DecodeBitMasks_def, HighestSetBit_def, Ones_def, Replicate_def,
        pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY],
       es,
       computeLib.Convs
       [(bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV)],
       computeLib.Tys
       (``:('a, 'b) sum`` ::
         List.map arm_type
          ["instruction", "Data", "Branch", "LoadStore", "SystemHintOp",
           "MoveWideOp", "LogicalOp", "MemOp", "BranchType", "ShiftType",
           "MachineCode"])])
end

local
  fun dst tm = case Lib.total boolSyntax.dest_strip_comb tm of
                  SOME ("arm8_target$valid_immediate", [_, _]) => SOME tm
                | _ => NONE
in
  val valid_immediate_conv =
    Conv.memoize dst (Redblackmap.mkDict Term.compare)
      (fn tm => tm = boolSyntax.T orelse tm = boolSyntax.F)
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
   computeLib.Defs [arm8_targetTheory.arm8_config_def]]

val add_arm8_decode_compset = computeLib.extend_compset
   [computeLib.Defs
      [Decode_def, DecodeShift_def, DecodeLogicalOp_def, DecodeBitMasks_def,
       HighestSetBit_def, Ones_def, Replicate_def, LoadStoreImmediateN_def,
       LoadStoreImmediate_def, arm8_dec_def, arm8_dec_aux_def,
       decode_word_def, fetch_word_def, cond_cmp_def, boolify32_n2w,
       bop_dec_def],
    es,
    computeLib.Tys
      (List.map arm_type
        ["arm8_state", "AccType", "instruction", "Data", "Branch",
         "LoadStore", "MoveWideOp", "LogicalOp", "MemOp", "BranchType",
         "SystemHintOp", "ShiftType"]),
    computeLib.Convs [(bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV)]]

val arm8_encode_decode_conv = computeLib.compset_conv (wordsLib.words_compset())
  [computeLib.Extenders
     [utilsLib.add_base_datatypes, asmLib.add_asm_compset,
      add_arm8_encode_compset, add_arm8_decode_compset]]

(* Testing

open arm8_targetLib

Count.apply arm8_encode_decode_conv
   ``MAP (\i. let l = arm8_enc i in (asm_ok i arm8_config, l, arm8_dec l))
      [ Inst Skip
      ; Inst (Const 8 0w)
      ; Inst (Const 1 0x100000000w)
      ; Inst (Const 1 0x100000001w)
      ; Inst (Const 1 0x100100001w)
      ; Inst (Arith (Binop Add 0 0 (Imm 1w)))
      ; Inst (Arith (Binop Add 0 0 (Reg 1)))
      ; Inst (Arith (Binop Sub 0 0 (Imm 1w)))
      ; Inst (Arith (Binop Or 0 0 (Imm 0xFFFFFFw)))
      ; Inst (Arith (Shift Lsr 0 0 1))
      ; Inst (Arith (Shift Asr 1 1 2))
      ; Inst (Mem Load 0 (Addr 1 0w))
      ; Inst (Mem Load 0 (Addr 1 0x10w))
      ; Inst (Mem Load8 0 (Addr 1 0x10w))
      ; Inst (Mem Store 0 (Addr 1 0w))
      ; Inst (Mem Store 0 (Addr 1 0x10w))
      ; Inst (Mem Store8 0 (Addr 1 0x10w))
      ; Jump 12w
      ; JumpCmp Less 0 (Reg 1) 12w
      ; JumpCmp Less 0 (Imm 1w) 12w
      ; JumpReg 1
      ; Call 4w
      ; Loc 1 4w
      ]``

*)

end
