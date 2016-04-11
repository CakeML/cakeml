structure riscv_targetLib :> riscv_targetLib =
struct

open HolKernel boolLib bossLib
open riscvTheory riscv_targetTheory utilsLib asmLib

val ERR = Feedback.mk_HOL_ERR "riscv_targetLib"

fun riscv_type s = Type.mk_thy_type {Thy = "riscv", Tyop = s, Args = []}

val riscv_tys =
  List.map riscv_type
     ["instruction", "Shift", "ArithI", "ArithR", "Branch", "Load", "Store"]

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
       [riscv_enc_def, riscv_encode_def, riscv_const32_def, riscv_bop_r_def,
        riscv_bop_i_def, riscv_sh_def, riscv_memop_def, Encode_def, opc_def,
        Itype_def, Rtype_def, Stype_def, SBtype_def, Utype_def, UJtype_def],
       computeLib.Tys ([``:('a, 'b) sum``, ``:asm$cmp``] @ riscv_tys),
       computeLib.Convs
         [(bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV)],
       computeLib.Extenders [pairLib.add_pair_compset]])
end

val add_riscv_encode_compset = computeLib.extend_compset
  [computeLib.Convs [(``riscv_target$riscv_enc``, 1, riscv_encode_conv)],
   computeLib.Defs [riscv_targetTheory.riscv_config_def],
   computeLib.Tys [``:('a, 'b) sum``]]

val add_riscv_decode_compset = computeLib.extend_compset
  [computeLib.Defs
     [Decode_def, riscv_dec_def, fetch_decode_def, riscv_dec_const32_def,
      asImm12_def, asImm20_def, asSImm12_def, boolify32_n2w],
   computeLib.Tys riscv_tys,
   computeLib.Convs [(bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV)]]

val riscv_encode_decode_conv =
  computeLib.compset_conv (wordsLib.words_compset())
    [computeLib.Extenders
       [bitstringLib.add_bitstring_compset,
        integer_wordLib.add_integer_word_compset,
        intReduce.add_int_compset,
        utilsLib.add_base_datatypes,
        asmLib.add_asm_compset,
        add_riscv_encode_compset,
        add_riscv_decode_compset]]

(* Testing

open riscv_targetLib

Count.apply riscv_encode_decode_conv
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
