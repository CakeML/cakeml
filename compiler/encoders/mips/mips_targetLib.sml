(*
  A compset for evaluating the MIPS instruction encoder and config.
*)
structure mips_targetLib :> mips_targetLib =
struct

open HolKernel boolLib bossLib
open mipsTheory mips_targetTheory utilsLib asmLib optionLib

val ERR = Feedback.mk_HOL_ERR "mips_targetLib"

fun mips_type s = Type.mk_thy_type {Thy = "mips", Tyop = s, Args = []}

val mips_tys = List.map mips_type
  ["instruction", "Shift", "ArithI", "ArithR", "Branch", "Load", "Store",
   "MultDiv"]

val mips_enc =
  SIMP_RULE (srw_ss()) [listTheory.LIST_BIND_def] (Q.AP_THM mips_enc_def `x`)

local
  fun dst tm = case Lib.total boolSyntax.dest_strip_comb tm of
                  SOME ("mips_target$mips_enc", [t]) => SOME t
                | _ => NONE
in
  val mips_encode_conv =
    Conv.memoize dst (Redblackmap.mkDict Term.compare) listSyntax.is_list
      (ERR "mips_encode_conv" "")
      (computeLib.compset_conv (wordsLib.words_compset())
        [computeLib.Defs
           [mips_enc, mips_ast_def, mips_encode_def, Encode_def, COP1Encode_def,
            mips_bop_r_def, mips_bop_i_def, mips_sh_def, mips_fp_cmp_def,
            mips_cmp_def, mips_sh32_def, mips_memop_def, form1_def, form2_def,
            form3_def, form4_def, form5_def],
         computeLib.Tys ([``:('a, 'b) sum``, ``:ast$shift``] @ mips_tys),
         computeLib.Extenders [optionLib.OPTION_rws, pairLib.add_pair_compset]])
end

val add_mips_encode_compset = computeLib.extend_compset
  [computeLib.Convs [(``mips_target$mips_enc``, 1, mips_encode_conv)],
   computeLib.Defs [mips_targetTheory.mips_config,
                    mips_targetTheory.mips_reg_ok_def]]

val mips_encode_decode_conv = computeLib.compset_conv (wordsLib.words_compset())
  [computeLib.Extenders
     [bitstringLib.add_bitstring_compset,
      integer_wordLib.add_integer_word_compset,
      intReduce.add_int_compset,
      utilsLib.add_base_datatypes,
      asmLib.add_asm_compset,
      add_mips_encode_compset]]

val () = asmLib.add_asm_ok_thm mips_targetTheory.mips_asm_ok

end
