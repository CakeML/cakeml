structure asmLib :> asmLib =
struct

open HolKernel boolLib bossLib
open asmTheory utilsLib

(*
val ERR = Feedback.mk_HOL_ERR "asmLib"
*)

fun asm_type a s = Type.mk_thy_type {Thy = "asm", Tyop = s, Args = a}
val asm_type0 = asm_type []
val asm_type = asm_type [``:64``]

fun add_asm_compset cmp =
   ( computeLib.add_thms
      [asm_ok_def, inst_ok_def, addr_ok_def, reg_ok_def, arith_ok_def,
       cmp_ok_def, reg_imm_ok_def, addr_offset_ok_def, jump_offset_ok_def,
       loc_offset_ok_def, upd_pc_def, upd_reg_def, upd_mem_def, read_reg_def,
       read_mem_def, assert_def, reg_imm_def, binop_upd_def, word_cmp_def,
       word_shift_def, arith_upd_def, addr_def, mem_load_def,
       write_mem_word_def, mem_store_def, read_mem_word_def, mem_op_def,
       inst_def, inst_opt_def, jump_to_offset_def, asm_def] cmp
   ; utilsLib.add_datatypes
        (asm_type0 "cmp" :: List.map asm_type ["asm_config", "asm"]) cmp
   )

end
