(*
  A compset for evaluating the RISC-V instruction encoder and config.
*)
structure riscv_targetLib :> riscv_targetLib =
struct

open HolKernel boolLib bossLib
open riscvTheory riscv_targetTheory utilsLib asmLib

val ERR = Feedback.mk_HOL_ERR "riscv_targetLib"

fun riscv_type s = Type.mk_thy_type {Thy = "riscv", Tyop = s, Args = []}

val riscv_tys =
  List.map riscv_type
     ["instruction", "Shift", "ArithI", "ArithR", "MulDiv", "Branch", "Load", "Store"]

val riscv_enc =
  SIMP_RULE (srw_ss()) [listTheory.LIST_BIND_def] (Q.AP_THM riscv_enc_def `x`)

local
  fun dst tm = case Lib.total boolSyntax.dest_strip_comb tm of
                  SOME ("riscv_target$riscv_enc", [t]) => SOME t
                | _ => NONE
in
  val riscv_encode_conv =
   Conv.memoize dst (Redblackmap.mkDict Term.compare) listSyntax.is_list
     (ERR "riscv_encode_conv" "")
     (computeLib.compset_conv (wordsLib.words_compset())
      [computeLib.Defs
       [riscv_enc, riscv_ast_def, riscv_encode_def, riscv_const32_def,
        riscv_bop_r_def, riscv_bop_i_def, riscv_sh_def, riscv_memop_def,
        Encode_def, opc_def, Itype_def, Rtype_def, Stype_def, SBtype_def,
        Utype_def, UJtype_def],
       computeLib.Tys
         ([``:('a, 'b) sum``, ``:asm$cmp``, ``:ast$shift``] @ riscv_tys),
       computeLib.Convs
         [(bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV)],
       computeLib.Extenders [pairLib.add_pair_compset]])
end

val add_riscv_encode_compset = computeLib.extend_compset
  [computeLib.Convs [(``riscv_target$riscv_enc``, 1, riscv_encode_conv)],
   computeLib.Defs [riscv_targetTheory.riscv_config],
   computeLib.Tys [``:('a, 'b) sum``]]

val riscv_encode_decode_conv =
  computeLib.compset_conv (wordsLib.words_compset())
    [computeLib.Extenders
       [bitstringLib.add_bitstring_compset,
        integer_wordLib.add_integer_word_compset,
        intReduce.add_int_compset,
        utilsLib.add_base_datatypes,
        asmLib.add_asm_compset,
        add_riscv_encode_compset]]

val () = asmLib.add_asm_ok_thm riscv_targetTheory.riscv_asm_ok

end
