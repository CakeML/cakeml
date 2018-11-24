structure ag32_targetLib :> ag32_targetLib =
struct

open HolKernel boolLib bossLib
open ag32Theory ag32_targetTheory utilsLib asmLib
open optionLib

structure Parse = struct
  open Parse
  val (Type, Term) =
    parse_from_grammars ag32_targetTheory.ag32_target_grammars
end
open Parse

val ERR = Feedback.mk_HOL_ERR "ag32_targetLib"

fun ag32_type s = Type.mk_thy_type {Thy = "ag32", Tyop = s, Args = []}

val ag32_encode =
  SIMP_RULE (srw_ss()) [listTheory.LIST_BIND_def] (Q.AP_THM ag32_encode_def `x`)

local
  fun dst tm = case Lib.total boolSyntax.dest_strip_comb tm of
                  SOME ("ag32_target$ag32_enc", [t]) => SOME t
                | _ => NONE
in
  val ag32_encode_conv =
   Conv.memoize dst (Redblackmap.mkDict Term.compare) listSyntax.is_list
     (ERR "ag32_encode_conv" "")
     (computeLib.compset_conv (wordsLib.words_compset())
      [computeLib.Defs
       [ag32_enc_def, ag32_constant_def, ag32_jump_constant_def, ag32_cmp_def, ag32_sh_def,
        ag32_encode, ag32_encode1_def, Encode_def, enc_def, ag32_bop_def,
        ri2bits_def, funcT2num_thm, encShift_def, shiftT2num_thm],
       computeLib.Tys
        (List.map ag32_type ["funcT", "instruction", "reg_immT", "shiftT"]),
       computeLib.Convs
        [(bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV)],
       computeLib.Extenders [optionLib.OPTION_rws,
         utilsLib.add_base_datatypes, asmLib.add_asm_compset
       ]])
end

val add_ag32_encode_compset = computeLib.extend_compset
  [computeLib.Convs [(``ag32_target$ag32_enc``, 1, ag32_encode_conv)],
   computeLib.Defs [ag32_targetTheory.ag32_config]]

val ag32_encode_conv = computeLib.compset_conv (wordsLib.words_compset())
  [computeLib.Extenders
    [utilsLib.add_base_datatypes, asmLib.add_asm_compset,
     add_ag32_encode_compset]]

val () = asmLib.add_asm_ok_thm ag32_targetTheory.ag32_asm_ok

end
