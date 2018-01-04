structure tiny_targetLib :> tiny_targetLib =
struct

open HolKernel boolLib bossLib
open tinyTheory tiny_targetTheory utilsLib asmLib
open optionLib

structure Parse = struct
  open Parse
  val (Type, Term) =
    parse_from_grammars tiny_targetTheory.tiny_target_grammars
end
open Parse

val ERR = Feedback.mk_HOL_ERR "tiny_targetLib"

fun tiny_type s = Type.mk_thy_type {Thy = "tiny", Tyop = s, Args = []}



local
  fun dst tm = case Lib.total boolSyntax.dest_strip_comb tm of
                  SOME ("tiny_target$tiny_enc", [t]) => SOME t
                | _ => NONE
in
  val tiny_encode_conv =
   Conv.memoize dst (Redblackmap.mkDict Term.compare) listSyntax.is_list
     (ERR "tiny_encode_conv" "")
     (computeLib.compset_conv (wordsLib.words_compset())
      [computeLib.Defs
       [tiny_enc_def, tiny_constant_def, tiny_cmp_def, tiny_sh_def,
        tiny_encode_def, tiny_encode1_def, Encode_def, enc_def,
        ri2bits_def, funcT2num_thm, encShift_def, shiftT2num_thm],
       computeLib.Tys
        (List.map tiny_type ["funcT", "instruction", "reg_immT", "shiftT"]),
       computeLib.Convs
        [(bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV)],
       computeLib.Extenders [optionLib.OPTION_rws]])
end

val add_tiny_encode_compset = computeLib.extend_compset
  [computeLib.Convs [(``tiny_target$tiny_enc``, 1, tiny_encode_conv)],
   computeLib.Defs
       [tiny_enc_def, tiny_constant_def, tiny_cmp_def, tiny_sh_def,
        tiny_encode_def, tiny_encode1_def, Encode_def, enc_def,
        ri2bits_def, funcT2num_thm, encShift_def, shiftT2num_thm]]

val tiny_encode_conv = computeLib.compset_conv (wordsLib.words_compset())
  [computeLib.Extenders
    [utilsLib.add_base_datatypes, asmLib.add_asm_compset,
     add_tiny_encode_compset]]

val () = asmLib.add_asm_ok_thm tiny_targetTheory.tiny_asm_ok

end
