(*
  A compset for evaluating the x64 instruction encoder and config.
*)
structure x64_targetLib :> x64_targetLib =
struct

open HolKernel boolLib bossLib
open x64Theory x64_targetTheory x64_eval_encodeTheory utilsLib asmLib
open optionLib

structure Parse = struct
  open Parse
  val (Type, Term) =
    parse_from_grammars x64_eval_encodeTheory.x64_eval_encode_grammars
end
open Parse

val ERR = Feedback.mk_HOL_ERR "x64_targetLib"

fun x64_type s = Type.mk_thy_type {Thy = "x64", Tyop = s, Args = []}

val add_x64_datatypes =
  utilsLib.add_datatypes
    ([``:asm$cmp``, ``:asm$binop``] @
     List.map x64_type
       ["instruction", "Zcond", "Zdest_src", "Zrm", "Zsize", "Zbase",
        "Zreg", "Zbinop_name"])

local
  fun dst tm = case Lib.total boolSyntax.dest_strip_comb tm of
                  SOME ("x64_target$x64_enc", [t]) => SOME t
                | _ => NONE
in
  val x64_encode_conv =
   Conv.memoize dst (Redblackmap.mkDict Term.compare) listSyntax.is_list
     (ERR "x64_encode_conv" "")
     (computeLib.compset_conv (wordsLib.words_compset())
      [computeLib.Defs
         [x64_bop_def, x64_cmp_def, x64_sh_def, e_gen_rm_reg_def,
          e_ModRM_def, e_opsize_def, rex_prefix_def, e_opc_def, e_rm_imm8_def,
          e_opsize_imm_def, not_byte_def, e_rax_imm_def, e_rm_imm_def,
          e_imm_8_32_def, e_imm_def, e_imm8_def, e_imm16_def, e_imm32_def,
          e_imm64_def, Zsize_width_def, is_rax_def, x64_encode_rwts,
          asmSemTheory.is_test_def, total_num2Zreg_def],
       computeLib.Extenders
         [add_x64_datatypes, optionLib.OPTION_rws, pairLib.add_pair_compset]])
end

val add_x64_encode_compset = computeLib.extend_compset
  [computeLib.Convs [(``x64_target$x64_enc``, 1, x64_encode_conv)],
   computeLib.Defs [x64_targetTheory.x64_config]]

val x64_encode_conv = computeLib.compset_conv (wordsLib.words_compset())
  [computeLib.Extenders
     [utilsLib.add_base_datatypes, asmLib.add_asm_compset,
      add_x64_encode_compset]]

val () = asmLib.add_asm_ok_thm x64_targetTheory.x64_asm_ok

end
