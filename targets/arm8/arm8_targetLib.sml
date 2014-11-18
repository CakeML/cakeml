structure arm8_targetLib :> arm8_targetLib =
struct

open HolKernel boolLib bossLib
open arm8Theory arm8_targetTheory sptreeSyntax utilsLib asmLib

(*

val ERR = Feedback.mk_HOL_ERR "arm8_targetLib"

val () = sptreeSyntax.temp_add_sptree_printer()

*)

fun arm_type s = Type.mk_thy_type {Thy = "arm8", Tyop = s, Args = []}

val arm8_enc = REWRITE_RULE [bop_enc_def, asmTheory.shift_distinct] arm8_enc_def

val lookup_CONV =
   RATOR_CONV (RAND_CONV wordsLib.WORD_EVAL_CONV)
   THENC RAND_CONV (fn t => if t = ``sptree_mask64``
                               then arm8_encodeTheory.sptree_mask64_def
                            else arm8_encodeTheory.sptree_mask32_def)
   THENC PURE_REWRITE_CONV [sptreeTheory.lookup_compute]

val EncodeBitMask_CONV =
   PURE_REWRITE_CONV [arm8_encodeTheory.EncodeBitMask_def] THENC lookup_CONV

fun add_arm8_encode_compset cmp =
   ( computeLib.add_thms
       [arm8_enc, arm8_encode_def, bop_enc_def, bop_dec_def, cmp_cond_def,
        arm8_enc_mov_imm_def, arm8_encodeTheory.InstructionEncode_def,
        Encode_def, e_data_def, e_branch_def, e_load_store_def, e_sf_def,
        e_LoadStoreImmediate_def, EncodeLogicalOp_def, NoOperation_def,
        ShiftType2num_thm, SystemHintOp2num_thm, ShiftType2num_thm,
        valid_immediate_def, LSL_def, LSR_def, arm8_config_def,
        pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY] cmp
   ; utilsLib.add_datatypes
       (``:('a, 'b) sum`` ::
        List.map arm_type
          ["instruction", "Data", "Branch", "LoadStore", "SystemHintOp",
           "MoveWideOp", "LogicalOp", "MemOp", "BranchType", "ShiftType",
           "MachineCode"]) cmp
   ; computeLib.add_conv
       (``arm8_encode$EncodeBitMask``, 1, EncodeBitMask_CONV) cmp
   )

fun add_arm8_decode_compset cmp =
   ( computeLib.add_thms
       [Decode_def, DecodeShift_def, DecodeLogicalOp_def, DecodeBitMasks_def,
        HighestSetBit_def, Ones_def, Replicate_def, LoadStoreImmediateN_def,
        LoadStoreImmediate_def, arm8_dec_def, arm8_dec_aux_def,
        decode_word_def, fetch_word_def, cond_cmp_def, boolify32_n2w] cmp
   ; utilsLib.add_datatypes
       (List.map arm_type ["arm8_state", "AccType"]) cmp
   ; computeLib.add_conv
       (bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV) cmp
   )

val arm8_encode_decode_conv =
   let
      val cmp = wordsLib.words_compset ()
   in
      List.app (fn f => f cmp)
          [bitstringLib.add_bitstring_compset,
           integer_wordLib.add_integer_word_compset,
           intReduce.add_int_compset,
           utilsLib.add_base_datatypes,
           asmLib.add_asm_compset,
           add_arm8_encode_compset,
           add_arm8_decode_compset]
    ; computeLib.CBV_CONV cmp
   end

(* Testing

open arm8_targetLib

arm8_encode_decode_conv
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
      ; Jump 12w NONE
      ; JumpCmp Less 0 (Reg 1) 12w NONE
      ; JumpCmp Less 0 (Imm 1w) 12w NONE
      ; JumpReg 1
      ; Call 4w
      ; Loc 1 4w
      ]``

*)

end
