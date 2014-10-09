structure x64_targetLib :> x64_targetLib =
struct

open HolKernel boolLib bossLib
open x64Theory x64_targetTheory utilsLib asmLib

(*
val ERR = Feedback.mk_HOL_ERR "x64_targetLib"
*)

fun x64_type s = Type.mk_thy_type {Thy = "x64", Tyop = s, Args = []}

fun add_x64_encode_compset cmp =
   ( computeLib.add_thms
        [x64_enc_def, x64_bop_def, x64_cmp_def, x64_sh_def, x64_encode_jcc_def,
         encode_def, e_rm_reg_def, e_gen_rm_reg_def, e_ModRM_def, e_opsize_def,
         rex_prefix_def, e_opc_def, e_rm_imm8_def, e_opsize_imm_def,
         not_byte_def, e_rax_imm_def, e_rm_imm_def, e_imm_8_32_def, e_imm_def,
         e_imm8_def, e_imm16_def, e_imm32_def, e_imm64_def, Zsize_width_def,
         is_rax_def, x64_config_def] cmp
   ; utilsLib.add_datatypes
       (List.map x64_type
          ["instruction", "Zcond", "Zdest_src", "Zrm", "Zsize", "Zbase",
           "Zreg", "Zbinop_name"]) cmp
   )

val x64_encode_conv =
   let
      val cmp = wordsLib.words_compset ()
      val () = utilsLib.add_base_datatypes cmp
      val () = asmLib.add_asm_compset cmp
      val () = add_x64_encode_compset cmp
   in
      computeLib.CBV_CONV cmp
   end

(* Testing

open x64_targetLib

x64_encode_conv
   ``MAP (\i. (asm_ok i x64_config, x64_enc i))
      [ Inst Skip
      ; Inst (Const 0 0w)
      ; Inst (Const 8 0w)
      ; Inst (Const 1 0x100000000w)
      ; Inst (Arith (Binop Add 0 0 (Imm 1w)))
      ; Inst (Arith (Binop Add 0 0 (Imm 100000000w)))
      ; Inst (Arith (Binop Add 1 1 (Imm 100000000w)))
      ; Inst (Arith (Binop Add 0 0 (Reg 1)))
      ; Inst (Arith (Binop Sub 0 0 (Imm 1w)))
      ; Inst (Arith (Shift Lsr 0 0 1))
      ; Inst (Arith (Shift Asr 1 1 2))
      ; Inst (Mem Load 0 (Addr 1 0w))
      ; Inst (Mem Load 0 (Addr 1 0x1000w))
      ; Inst (Mem Load32 0 (Addr 1 0x1000w))
      ; Inst (Mem Load8 0 (Addr 1 0x1000w))
      ; Inst (Mem Store 0 (Addr 1 0w))
      ; Inst (Mem Store 0 (Addr 1 0x1000w))
      ; Inst (Mem Store32 0 (Addr 1 0x1000w))
      ; Inst (Mem Store8 0 (Addr 1 0x1000w))
      ; Jump 12w NONE
      ; JumpCmp Less 0 (Reg 1) 12w NONE
      ; JumpCmp Less 0 (Imm 1w) 12w NONE
      ; JumpReg 1
      ; Loc 1 4w
      ; Cache
      ]``

*)

end
