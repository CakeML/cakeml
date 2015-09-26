structure mips_targetLib :> mips_targetLib =
struct

open HolKernel boolLib bossLib
open mipsTheory mips_targetTheory utilsLib asmLib

(*
val ERR = Feedback.mk_HOL_ERR "mips_targetLib"
*)

fun mips_type s = Type.mk_thy_type {Thy = "mips", Tyop = s, Args = []}

fun add_mips_encode_compset cmp =
   ( computeLib.add_thms
       [mips_enc_def, encs_def, mips_encode_def, Encode_def, mips_config_def,
        mips_bop_r_def, mips_bop_i_def, mips_sh_def, mips_sh32_def,
        mips_memop_def, form1_def, form2_def, form3_def, form4_def, form5_def
        ] cmp
   ; utilsLib.add_datatypes
       (``:('a, 'b) sum`` ::
        List.map mips_type
          ["instruction", "Shift", "ArithI", "ArithR", "Branch",
           "Load", "Store"]) cmp
   )

fun add_mips_decode_compset cmp =
   ( computeLib.add_thms
       [Decode_def, mips_dec_def, fetch_decode_def, all_same_def, when_nop_def,
        boolify32_n2w] cmp
   ; computeLib.add_conv
       (bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV) cmp
   )

val mips_encode_decode_conv =
   let
      val cmp = wordsLib.words_compset ()
   in
      List.app (fn f => f cmp)
          [bitstringLib.add_bitstring_compset,
           integer_wordLib.add_integer_word_compset,
           intReduce.add_int_compset,
           utilsLib.add_base_datatypes,
           asmLib.add_asm_compset,
           add_mips_encode_compset,
           add_mips_decode_compset]
    ; computeLib.CBV_CONV cmp
   end

(* Testing

open mips_targetLib

mips_encode_decode_conv
   ``MAP (\i. let l = mips_enc i in (asm_ok i mips_config, l, mips_dec l))
      [ Inst Skip
      ; Inst (Const 8 0w)
      ; Inst (Const 1 0x100000000w)
      ; Inst (Const 1 0x100000001w)
      ; Inst (Const 1 0x100100001w)
      ; Inst (Arith (Binop Add 0 0 (Imm 1w)))
      ; Inst (Arith (Binop Add 0 0 (Reg 1)))
 (*   ; Inst (Arith (Binop Sub 0 0 (Imm 1w)))  not supported in MIPS *)
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
