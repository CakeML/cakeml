structure arm6_targetLib :> arm6_targetLib =
struct

open HolKernel boolLib bossLib
open armTheory arm6_targetTheory utilsLib asmLib

(*
val ERR = Feedback.mk_HOL_ERR "arm6_targetLib"
*)

fun arm_type s = Type.mk_thy_type {Thy = "arm", Tyop = s, Args = []}

fun add_arm6_encode_compset cmp =
   ( computeLib.add_thms
       [arm6_enc_def, arm6_bop_def, arm6_sh_def, arm6_cmp_def, arm6_encode_def,
        encode_def, e_branch_def, e_data_def, e_load_def, e_store_def,
        EncodeImmShift_def, EncodeARMImmediate_def, EncodeARMImmediate_aux_def,
        valid_immediate_def, arm6_config_def] cmp
   ; utilsLib.add_datatypes
       (List.map arm_type
           ["instruction", "Branch", "Data", "Load", "Store",
            "offset1", "SRType", "MachineCode"]) cmp
   )

fun add_arm6_decode_compset cmp =
   ( computeLib.add_thms
       [arm6_bop_dec_def, arm6_sh_dec_def, arm6_cmp_dec_def, decode_imm12_def,
        fetch_word_def, decode_word_def, arm6_dec_aux_def, arm6_dec_def,
        DecodeARM_def, DecodeImmShift_def, ARMExpandImm_C_def, Shift_C_def,
        ConditionPassed_def, CurrentCond_def, SetPassCondition_def, Take_def,
        boolify28_n2w, boolify4_n2w] cmp
   ; utilsLib.add_datatypes
       (List.map arm_type ["arm_state", "PSR", "Architecture"]) cmp
   ; computeLib.add_conv
       (bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV) cmp
   )

val arm6_encode_decode_conv =
   let
      val cmp = wordsLib.words_compset ()
      val () = utilsLib.add_base_datatypes cmp
      val () = asmLib.add_asm_compset cmp
      val () = add_arm6_encode_compset cmp
      val () = add_arm6_decode_compset cmp
   in
      computeLib.CBV_CONV cmp
   end

(* Testing

open arm6_targetLib

arm6_encode_decode_conv
   ``MAP (\i. let l = arm6_enc i in (asm_ok i arm6_config, l, arm6_dec l))
      [ Inst Skip
      ; Inst (Const 0 0w)
      ; Inst (Const 8 0w)
      ; Inst (Const 1 0x100000000w)
      ; Inst (Arith (Binop Add 0 0 (Imm 1w)))
      ; Inst (Arith (Binop Add 0 0 (Imm 0x100000000w)))
      ; Inst (Arith (Binop Add 1 1 (Imm 0x100000000w)))
      ; Inst (Arith (Binop Add 0 0 (Reg 1)))
      ; Inst (Arith (Binop Sub 0 0 (Imm 1w)))
      ; Inst (Arith (Shift Lsr 0 0 1))
      ; Inst (Arith (Shift Asr 1 1 2))
      ; Inst (Mem Load 0 (Addr 1 0w))
      ; Inst (Mem Load 0 (Addr 1 0x100w))
      ; Inst (Mem Load8 0 (Addr 1 0x100w))
      ; Inst (Mem Store 0 (Addr 1 0w))
      ; Inst (Mem Store 0 (Addr 1 0x100w))
      ; Inst (Mem Store8 0 (Addr 1 0x100w))
      ; Jump 12w NONE
      ; JumpCmp Less 0 (Reg 1) 12w NONE
      ; JumpCmp Less 0 (Imm 1w) 12w NONE
      ; JumpReg 1
      ; Loc 1 4w
      ]``

*)

end
