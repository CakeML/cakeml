structure asmLib :> asmLib =
struct

open HolKernel boolLib bossLib
open lcsymtacs asmTheory utilsLib

(*
val ERR = Feedback.mk_HOL_ERR "asmLib"
*)

(* compset support -------------------------------------------------------- *)

fun asm_type a s = Type.mk_thy_type {Thy = "asm", Tyop = s, Args = a}
val asm_type0 = asm_type []
val asm_type = asm_type [``:64``]

fun add_asm_compset cmp =
   ( computeLib.add_thms
      [asm_ok_def, inst_ok_def, addr_ok_def, reg_ok_def, arith_ok_def,
       cmp_ok_def, reg_imm_ok_def, addr_offset_ok_def, jump_offset_ok_def,
       cjump_offset_ok_def, loc_offset_ok_def, upd_pc_def, upd_reg_def,
       upd_mem_def, read_reg_def, read_mem_def, assert_def, reg_imm_def,
       binop_upd_def, word_cmp_def, word_shift_def, arith_upd_def, addr_def,
       mem_load_def, write_mem_word_def, mem_store_def, read_mem_word_def,
       mem_op_def, inst_def, jump_to_offset_def, asm_def] cmp
   ; utilsLib.add_datatypes
        (List.map asm_type0 ["cmp", "mem_op", "binop", "cmp", "shift"] @
         List.map asm_type  ["asm_config", "asm"])
        cmp
   )

(* some rewrites ---------------------------------------------------------- *)

fun read_mem_word n =
   EVAL ``(read_mem_word (b: 'a word) ^n s): 'a word # 'a asm_state``
   |> SIMP_RULE (srw_ss()) []

fun write_mem_word n =
   EVAL ``(write_mem_word (b: 'a word) ^n (d:'b word) s): 'a asm_state``
   |> SIMP_RULE (srw_ss()) []

val asm_ok_rwts =
   [asm_ok_def, inst_ok_def, addr_ok_def, reg_ok_def, arith_ok_def, cmp_ok_def,
    reg_imm_ok_def, addr_offset_ok_def, jump_offset_ok_def, cjump_offset_ok_def,
    loc_offset_ok_def]

val asm_rwts =
   [upd_pc_def, upd_reg_def, upd_mem_def, read_reg_def, read_mem_def,
    assert_def, reg_imm_def, binop_upd_def, word_cmp_def, word_shift_def,
    arith_upd_def, addr_def, mem_load_def, write_mem_word_def, mem_store_def,
    read_mem_word ``1n``, read_mem_word ``4n``, read_mem_word ``8n``,
    write_mem_word ``1n``, write_mem_word ``4n``, write_mem_word ``8n``,
    mem_op_def, inst_def, jump_to_offset_def, asm_def]

(* some custom tools/tactics ---------------------------------------------- *)

fun using_first n thms_tac =
   POP_ASSUM_LIST
      (fn thms =>
          let
             val x = List.rev (List.take (thms, n))
             val y = List.rev (List.drop (thms, n))
          in
             MAP_EVERY assume_tac y
             \\ thms_tac x
             \\ MAP_EVERY assume_tac x
          end)

local
   fun dest5 c e tm =
      case Lib.with_exn boolSyntax.strip_comb tm e of
         (t, [t1, t2, t3, t4, t5]) =>
          if Term.same_const t c then (t1, t2, t3, t4, t5) else raise e
       | _ => raise e
   fun mk5 tm (a, b, c, d, e) = boolSyntax.list_mk_icomb (tm, [a, b, c, d, e])
in
   val (_, mk_bytes_in_memory, dest_bytes_in_memory, _) =
      HolKernel.syntax_fns {n = 5, dest = dest5, make = mk5}
        "asm" "bytes_in_memory"
end

val strip_bytes_in_memory =
   Option.map (fn (_, l, _, _, _) => fst (listSyntax.dest_list l)) o
   Lib.total dest_bytes_in_memory

local
   val bytes_in_memory_concat =
      Q.GENL [`l2`, `l1`]
         (fst (Thm.EQ_IMP_RULE (Drule.SPEC_ALL bytes_in_memory_concat)))
   val w8 = ``:word8``
   val pc = Term.mk_var ("pc", ``:'a word``)
   val icache = Term.mk_var ("icache", ``: ('a word -> word8) option``)
   val mem = Term.mk_var ("mem", ``: 'a word -> word8``)
   val mem_domain = Term.mk_var ("mem_domain", ``: 'a word -> bool``)
in
   fun split_bytes_in_memory_tac n (asl, g) =
      (case List.mapPartial strip_bytes_in_memory asl of
          [] => NO_TAC
        | l :: _ =>
            let
               val l1 = listSyntax.mk_list (List.take (l, n), w8)
               val l2 = listSyntax.mk_list (List.drop (l, n), w8)
               val l = listSyntax.mk_list (l, w8)
               val th =
                  bytes_in_memory_concat
                  |> Drule.ISPECL [l1, l2]
                  |> Conv.CONV_RULE
                       (Conv.LAND_CONV
                          (Conv.RATOR_CONV
                             (Conv.RATOR_CONV
                                (Conv.RATOR_CONV
                                   (Conv.RAND_CONV listLib.APPEND_CONV))))
                        THENC Conv.RAND_CONV
                                (Conv.RAND_CONV
                                   (Conv.RATOR_CONV
                                      (Conv.RATOR_CONV
                                         (Conv.RATOR_CONV
                                            (Conv.RATOR_CONV
                                               (Conv.RAND_CONV
                                                  (Conv.DEPTH_CONV
                                                     listLib.LENGTH_CONV))))))))
            in
               qpat_assum `asm$bytes_in_memory ^pc ^l ^icache ^mem ^mem_domain`
                  (fn thm =>
                      let
                         val (th1, th2) =
                            Drule.CONJ_PAIR (Drule.MATCH_MP th thm)
                      in
                         assume_tac th1
                         \\ assume_tac th2
                      end)
            end) (asl, g)
end

local
   fun bit_mod_thm n m =
      let
         val th = bitTheory.BITS_ZERO3 |> Q.SPEC n |> numLib.REDUCE_RULE
         val M = Parse.Term m
         val N = Parse.Term n
      in
         Tactical.prove (
             ``BIT ^M n = BIT ^M (n MOD 2 ** (^N + 1))``,
             simp [bitTheory.BIT_def, GSYM th, bitTheory.BITS_COMP_THM2])
         |> numLib.REDUCE_RULE
      end
   fun nq i = [QUOTE (Int.toString i ^ "n")]
   val th = GSYM wordsTheory.n2w_mod
   fun bit_mod_thms n =
      (th |> Thm.INST_TYPE [Type.alpha |-> fcpSyntax.mk_int_numeric_type n]
          |> CONV_RULE (DEPTH_CONV wordsLib.SIZES_CONV)) ::
      List.tabulate (n, fn j => bit_mod_thm (nq (n - 1)) (nq j))
in
   fun v2w_BIT_n2w i =
      let
         val n = Term.mk_var ("n", numLib.num)
         val ty = fcpSyntax.mk_int_numeric_type i
         val r = wordsSyntax.mk_n2w (n, ty)
         val l = List.tabulate
                    (i, fn j => bitSyntax.mk_bit (numSyntax.term_of_int j, n))
         val v = bitstringSyntax.mk_v2w
                    (listSyntax.mk_list (List.rev l, Type.bool), ty)
         val s =
            numSyntax.mk_numeral (Arbnum.pow (Arbnum.two, Arbnum.fromInt i))
      in
         Tactical.prove(boolSyntax.mk_eq (v, r),
            once_rewrite_tac (bit_mod_thms i)
            \\ qabbrev_tac `m = n MOD ^s`
            \\ `m < ^s` by simp [Abbr `m`]
            \\ fs [wordsTheory.NUMERAL_LESS_THM]
            \\ EVAL_TAC
            ) |> GEN_ALL
      end
end

local
   fun dest_v2w_or_n2w tm =
      bitstringSyntax.dest_v2w tm handle HOL_ERR _ => wordsSyntax.dest_n2w tm
   val is_byte_eq =
      Lib.can ((wordsSyntax.dest_word_extract ## dest_v2w_or_n2w) o
               boolSyntax.dest_eq)
   val conv =
      Conv.DEPTH_CONV
         (fn tm => if is_byte_eq tm
                      then blastLib.BBLAST_CONV tm
                   else Conv.NO_CONV tm)
      THENC Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV
in
   val byte_eq_tac =
      rule_assum_tac
        (Conv.CONV_RULE
           (fn tm =>
               if boolSyntax.is_imp_only tm orelse boolSyntax.is_forall tm
                  then conv tm
               else ALL_CONV tm))
end

end
