structure arm6_targetLib :> arm6_targetLib =
struct

open HolKernel boolLib bossLib
open armTheory arm6_targetTheory arm6_eval_encodeTheory utilsLib asmLib

structure Parse = struct
  open Parse
  val (Type, Term) =
    parse_from_grammars arm6_eval_encodeTheory.arm6_eval_encode_grammars
end
open Parse

(*
val ERR = Feedback.mk_HOL_ERR "arm6_targetLib"
*)

fun arm_type s = Type.mk_thy_type {Thy = "arm", Tyop = s, Args = []}

val aligned =
   let
      open alignmentTheory
   in
      SIMP_RULE std_ss [aligned_0, aligned_1_lsb, aligned_extract]
         arm_stepTheory.Aligned
   end

fun add_arm6_encode_compset cmp =
   ( computeLib.add_thms
       [arm6_bop_def, arm6_sh_def, arm6_cmp_def, EncodeImmShift_def,
        EncodeARMImmediate_def, EncodeARMImmediate_aux_def,
        valid_immediate_def, arm6_config_def, aligned, arm6_encode_rwts] cmp
   ; utilsLib.add_datatypes
       (List.map arm_type ["instruction", "offset1", "SRType", "MachineCode"])
       cmp
   ; computeLib.add_conv
       (bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV) cmp
   )

fun add_arm6_decode_compset cmp =
   ( computeLib.add_thms
       [arm6_bop_dec_def, arm6_sh_dec_def, arm6_cmp_dec_def, decode_imm12_def,
        fetch_word_def, decode_word_def, arm6_dec_aux_def, arm6_dec_def,
        DecodeARM_def, DecodeImmShift_def, ARMExpandImm_C_def, Shift_C_def,
        ConditionPassed_def, CurrentCond_def, SetPassCondition_def, Do_def,
        boolify28_n2w, boolify4_n2w] cmp
   ; utilsLib.add_datatypes
       (List.map arm_type
          ["arm_state", "PSR", "Architecture", "InstrSet", "Branch", "Data",
           "Load", "Store"]) cmp
   )

val arm6_encode_decode_conv =
   let
      val cmp = wordsLib.words_compset ()
   in
      utilsLib.add_base_datatypes cmp
    ; asmLib.add_asm_compset cmp
    ; add_arm6_encode_compset cmp
    ; add_arm6_decode_compset cmp
    ; computeLib.CBV_CONV cmp
   end

(* Testing

open arm6_targetLib

Count.apply arm6_encode_decode_conv
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
      ; Jump 12w
      ; JumpCmp Less 0 (Reg 1) 12w
      ; JumpCmp Less 0 (Imm 1w) 12w
      ; Call 100w
      ; JumpReg 1
      ; Loc 1 4w
      ]``

*)

end
