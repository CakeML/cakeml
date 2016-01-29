structure riscv_targetLib :> riscv_targetLib =
struct

open HolKernel boolLib bossLib
open riscvTheory riscv_targetTheory utilsLib asmLib

(*
val ERR = Feedback.mk_HOL_ERR "riscv_targetLib"
*)

fun riscv_type s = Type.mk_thy_type {Thy = "riscv", Tyop = s, Args = []}

fun add_riscv_encode_compset cmp =
   ( computeLib.add_thms
       [riscv_enc_def, riscv_encode_def, riscv_const32_def, riscv_bop_r_def,
        riscv_bop_i_def, riscv_sh_def, riscv_memop_def, Encode_def, opc_def,
        Itype_def, Rtype_def, Stype_def, SBtype_def, Utype_def, UJtype_def,
        riscv_config_def] cmp
   ; utilsLib.add_datatypes
       (``:('a, 'b) sum`` ::
        List.map riscv_type
          ["instruction", "Shift", "ArithI", "ArithR", "Branch",
           "Load", "Store"]) cmp
   )

fun add_riscv_decode_compset cmp =
   ( computeLib.add_thms
       [Decode_def, riscv_dec_def, fetch_decode_def, riscv_dec_const32_def,
        boolify32_n2w] cmp
   ; computeLib.add_conv
       (bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV) cmp
   )

val riscv_encode_decode_conv =
   let
      val cmp = wordsLib.words_compset ()
   in
      List.app (fn f => f cmp)
          [bitstringLib.add_bitstring_compset,
           integer_wordLib.add_integer_word_compset,
           intReduce.add_int_compset,
           utilsLib.add_base_datatypes,
           asmLib.add_asm_compset,
           add_riscv_encode_compset,
           add_riscv_decode_compset]
    ; computeLib.CBV_CONV cmp
   end

(* Testing

open riscv_targetLib

riscv_encode_decode_conv
   ``MAP (\i. let l = riscv_enc i in (asm_ok i riscv_config, l, riscv_dec l))
      [ Inst Skip
      ; Inst (Const 8 0w)
      ; Inst (Const 2 0x100000000w)
      ; Inst (Const 2 0x100000001w)
      ; Inst (Const 2 0x100100001w)
      ; Inst (Arith (Binop Add 2 2 (Imm 1w)))
      ; Inst (Arith (Binop Add 2 2 (Reg 3)))
 (*   ; Inst (Arith (Binop Sub 0 0 (Imm 1w)))  not supported in RISC-V *)
      ; Inst (Arith (Binop Or 2 3 (Imm 0x7FFw)))
      ; Inst (Arith (Shift Lsr 2 2 1))
      ; Inst (Arith (Shift Asr 2 2 3))
      ; Inst (Mem Load 2 (Addr 3 0w))
      ; Inst (Mem Load 2 (Addr 3 0x10w))
      ; Inst (Mem Load8 2 (Addr 3 0x10w))
      ; Inst (Mem Store 2 (Addr 3 0w))
      ; Inst (Mem Store 2 (Addr 3 0x10w))
      ; Inst (Mem Store8 2 (Addr 3 0x10w))
      ; Jump 12w
      ; JumpCmp Less 2 (Reg 3) 12w
      ; JumpCmp Less 2 (Imm 1w) 12w
      ; JumpReg 2
      ; Call 4w
      ; Loc 2 4w
      ]``

*)

end
