(*
  Prove `encoder_correct` for RISC-V
*)
open HolKernel Parse boolLib bossLib
open asmLib riscv_stepLib riscv_targetTheory;

val () = new_theory "riscv_targetProof"

val () = wordsLib.guess_lengths()

(* some lemmas ---------------------------------------------------------- *)

val bytes_in_memory_thm = Q.prove(
   `!w s state a b c d.
      target_state_rel riscv_target s state /\
      bytes_in_memory s.pc [a; b; c; d] s.mem s.mem_domain ==>
      (state.exception = NoException) /\
      ((state.c_MCSR state.procID).mstatus.VM = 0w) /\
      ((state.c_MCSR state.procID).mcpuid.ArchBase = 2w) /\
      (state.c_NextFetch state.procID = NONE) /\
      aligned 2 (state.c_PC state.procID) /\
      (state.MEM8 (state.c_PC state.procID) = a) /\
      (state.MEM8 (state.c_PC state.procID + 1w) = b) /\
      (state.MEM8 (state.c_PC state.procID + 2w) = c) /\
      (state.MEM8 (state.c_PC state.procID + 3w) = d) /\
      state.c_PC state.procID + 3w IN s.mem_domain /\
      state.c_PC state.procID + 2w IN s.mem_domain /\
      state.c_PC state.procID + 1w IN s.mem_domain /\
      state.c_PC state.procID IN s.mem_domain`,
   rw [asmPropsTheory.target_state_rel_def, riscv_target_def, riscv_config_def,
       riscv_ok_def, miscTheory.bytes_in_memory_def,
       alignmentTheory.aligned_extract, set_sepTheory.fun2set_eq]
   \\ fs []
   )

val bytes_in_memory_thm2 = Q.prove(
   `!w s state a b c d.
      target_state_rel riscv_target s state /\
      bytes_in_memory (s.pc + w) [a; b; c; d] s.mem s.mem_domain ==>
      (state.MEM8 (state.c_PC state.procID + w) = a) /\
      (state.MEM8 (state.c_PC state.procID + w + 1w) = b) /\
      (state.MEM8 (state.c_PC state.procID + w + 2w) = c) /\
      (state.MEM8 (state.c_PC state.procID + w + 3w) = d) /\
      state.c_PC state.procID + w + 3w IN s.mem_domain /\
      state.c_PC state.procID + w + 2w IN s.mem_domain /\
      state.c_PC state.procID + w + 1w IN s.mem_domain /\
      state.c_PC state.procID + w IN s.mem_domain`,
   rw [asmPropsTheory.target_state_rel_def, riscv_target_def, riscv_config_def,
       riscv_ok_def, miscTheory.bytes_in_memory_def,
       alignmentTheory.aligned_extract, set_sepTheory.fun2set_eq]
   \\ fs []
   )

val lem1 = asmLib.v2w_BIT_n2w 5
val lem2 = asmLib.v2w_BIT_n2w 6

val lem4 = blastLib.BBLAST_PROVE
  ``0xFFFFFFFFFFFFF800w <= c /\ c <= 0x7FFw ==>
    (sw2sw
      (v2w [c ' 11; c ' 10; c ' 9; c ' 8; c ' 7; c ' 6; c ' 5;
            c ' 4; c ' 3; c ' 2; c ' 1; c ' 0] : word12) = c : word64)``


val lem5 = Q.prove(
  `aligned 2 (c: word64) ==> ~c ' 1`,
  simp [alignmentTheory.aligned_extract]
  \\ blastLib.BBLAST_TAC
  )

val lem6 = blastLib.BBLAST_PROVE
  ``(((31 >< 0) (c: word64) : word32) ' 11 = c ' 11) /\
    (((63 >< 32) c : word32) ' 11 = c ' 43) /\
    (~(63 >< 32) c : word32 ' 11 = ~c ' 43) ``

val lem7 = CONJ (bitstringLib.v2w_n2w_CONV ``v2w [F] : word64``)
                (bitstringLib.v2w_n2w_CONV ``v2w [T] : word64``)

val lem8 = Q.prove(
  `((if b then 1w else 0w : word64) = (v2w [x] || v2w [y])) = (b = (x \/ y))`,
  rw [] \\ blastLib.BBLAST_TAC)

val lem9 = Q.prove(
  `!r2 : word64 r3 : word64.
    (18446744073709551616 <= w2n r2 + (w2n r3 + 1) <=>
     18446744073709551616w <=+ w2w r2 + w2w r3 + 1w : 65 word) /\
    (18446744073709551616 <= w2n r2 + w2n r3 <=>
     18446744073709551616w <=+ w2w r2 + w2w r3 : 65 word)`,
   Cases
   \\ Cases
   \\ imp_res_tac wordsTheory.BITS_ZEROL_DIMINDEX
   \\ fs [wordsTheory.w2w_n2w, wordsTheory.word_add_n2w,
          wordsTheory.word_ls_n2w])

val lem10 =
  blastLib.BBLAST_CONV
    ``v2w [c11; c10; c9; c8; c7; c6; c5; c4; c3; c2; c1; c0] : word12 ' 1``

val lem11 =
  asmLib.mk_blast_thm
    ``(31 >< 12) (a - sw2sw ((11 >< 0) (a : word64) : word12))``

val lem12 = asmLib.mk_blast_thm ``(11 >< 0) (c : word64) && ~0b10w``

val lem12b =
  blastLib.BBLAST_PROVE
    ``0xFFFFFFFF80000000w <= c /\ c <= 0x7FFFF7FFw /\
      ((1 >< 0) c = 0w : word64) ==>
      (sw2sw (((31 >< 12) (c + -1w * sw2sw ((11 >< 0) c)) : word20) @@
              (0w : word12)) +
       sw2sw ((11 >< 0) c && ~2w) = c : word64)``

val mul_long = Q.prove(
  `!a : word64 b : word64.
    n2w ((w2n a * w2n b) DIV 18446744073709551616) =
    (127 >< 64) (w2w a * w2w b : word128) : word64`,
  Cases
  \\ Cases
  \\ fs [wordsTheory.w2w_n2w, wordsTheory.word_mul_n2w,
         wordsTheory.word_extract_n2w, bitTheory.BITS_THM]
  )

val riscv_overflow =
  REWRITE_RULE
    [blastLib.BBLAST_PROVE
      ``!x y : word64.
         ((word_msb x = word_msb y) /\ (word_msb x <> word_msb (x + y))) =
         ((~(x ?? y) && (y ?? (x + y))) >>> 63 = 1w)``]
    (Q.INST_TYPE [`:'a` |-> `:64`] integer_wordTheory.overflow)

val riscv_sub_overflow =
  SIMP_RULE (srw_ss())
    [blastLib.BBLAST_PROVE
      ``!x y : word64.
         ((word_msb x <> word_msb y) /\ (word_msb x <> word_msb (x - y))) =
         (((x ?? y) && ~(y ?? (x - y))) >>> 63 = 1w)``]
    (Q.INST_TYPE [`:'a` |-> `:64`] integer_wordTheory.sub_overflow)

val ror = Q.prove(
  `!w : word64 n. n < 64n ==> ((w << (64 - n) || w >>> n) = w #>> n)`,
  srw_tac [fcpLib.FCP_ss]
    [wordsTheory.word_or_def, wordsTheory.word_ror, wordsTheory.word_bits_def,
     wordsTheory.word_lsl_def, wordsTheory.word_lsr_def,
     GSYM arithmeticTheory.NOT_LESS]
  \\ `i - (64 - n) < 64` by decide_tac
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] []
  \\ Cases_on `i + n < 64`
  \\ simp []
  )

(* appears to not be relevant

Theorem DecodeAny_encode[simp]:
   !encode x. DecodeAny (Word (encode x)) = Decode (encode x)
Proof
  rw [riscv_stepTheory.Decode_IMP_DecodeAny]
QED

*)

(* some rewrites ---------------------------------------------------------- *)

val encode_rwts =
   let
      open riscvTheory
   in
      [riscv_enc_def, riscv_ast_def, riscv_encode_def, riscv_const32_def,
       riscv_bop_r_def, riscv_bop_i_def, riscv_sh_def, riscv_memop_def,
       Encode_def, opc_def, Itype_def, Rtype_def, Stype_def, SBtype_def,
       Utype_def, UJtype_def]
   end

val word_bit_0_add4 = prove(
  ``word_bit 0 (w +  4w:word64) = word_bit 0 w /\
    word_bit 0 (w +  8w:word64) = word_bit 0 w /\
    word_bit 0 (w + 12w:word64) = word_bit 0 w /\
    word_bit 0 (w + 16w:word64) = word_bit 0 w /\
    word_bit 0 (w + 20w:word64) = word_bit 0 w /\
    word_bit 0 (w + 24w:word64) = word_bit 0 w /\
    word_bit 0 (w + 28w:word64) = word_bit 0 w /\
    word_bit 0 (w + 32w:word64) = word_bit 0 w``,
  blastLib.BBLAST_TAC);

val enc_rwts =
  [riscv_config, riscv_asm_ok, lem6, word_bit_0_add4] @ encode_rwts @ asmLib.asm_rwts

val enc_ok_rwts =
  [asmPropsTheory.enc_ok_def, riscv_config, riscv_asm_ok] @ encode_rwts

(* some custom tactics ---------------------------------------------------- *)

local
   val bool1 = utilsLib.rhsc o blastLib.BBLAST_CONV o fcpSyntax.mk_fcp_index
   fun boolify n tm =
      List.tabulate (n, fn i => bool1 (tm, numLib.term_of_int (n - 1 - i)))
   val bytes = List.concat o List.map (boolify 8)
   val is_riscv_next = #4 (HolKernel.syntax_fns1 "riscv_target" "riscv_next")
   val (_, _, dest_NextRISCV, is_NextRISCV) =
      HolKernel.syntax_fns1 "riscv_step" "NextRISCV"
   val find_NextRISCV =
      dest_NextRISCV o List.hd o HolKernel.find_terms is_NextRISCV
   val s = ``s: riscv_state``
   val word_bit_0_lemmas = Q.store_thm("word_bit_0_lemmas",
     `!w. ¬word_bit 0 (0xFFFFFFFFFFFFFFFEw && w:word64) /\
          word_bit 0 ((0xFFFFFFFFFFFFFFFEw && w:word64) + v) = word_bit 0 v`,
     blastLib.BBLAST_TAC)
   fun post_process th =
     th |> REWRITE_RULE [word_bit_0_lemmas]
   fun step the_state l =
      let
         val v = listSyntax.mk_list (bytes l, Type.bool)
         val thm = Thm.INST [s |-> the_state] (riscv_stepLib.riscv_step v)
      in
         (Drule.DISCH_ALL thm |> post_process,
          optionSyntax.dest_some (boolSyntax.rand (Thm.concl thm)))
      end
   val ms = ``ms: riscv_state``
   fun new_state_var l =
     Term.variant (List.concat (List.map Term.free_vars l)) ms
   fun env (t, tm) =
     let
       (*
       val (t, tm) = Option.valOf (find_env g)
       *)
       val etm = ``env ^t ^tm : riscv_state``
     in
       (fn (asl, g) =>
         let
           val pc = fst (pred_setSyntax.dest_in (hd asl))
         in
           subgoal
           `(!a. a IN s1.mem_domain ==> ((^etm).MEM8 a = ms.MEM8 a)) /\
            ((^etm).exception = ms.exception) /\
            ((^etm).c_NextFetch (^etm).procID = ms.c_NextFetch ms.procID) /\
            (((^etm).c_MCSR (^etm).procID).mstatus.VM =
             (ms.c_MCSR ms.procID).mstatus.VM) /\
            (((^etm).c_MCSR (^etm).procID).mcpuid.ArchBase =
             (ms.c_MCSR ms.procID).mcpuid.ArchBase) /\
            ((^etm).c_PC (^etm).procID = ^pc)`
            >| [
              asm_simp_tac (srw_ss()++bitstringLib.v2w_n2w_ss)
               [combinTheory.UPDATE_APPLY, combinTheory.UPDATE_EQ, Abbr `^tm`],
              all_tac
            ]
         end (asl, g)
       , etm
       )
     end
in
   fun next_state_tac (asl, g) =
     (let
         val x as (pc, l, _, _) =
            List.last
              (List.mapPartial (Lib.total asmLib.dest_bytes_in_memory) asl)
         val x_tm = asmLib.mk_bytes_in_memory x
         val l = List.rev (fst (listSyntax.dest_list l))
         val th = case Lib.total wordsSyntax.dest_word_add pc of
                     SOME (_, w) => Thm.SPEC w bytes_in_memory_thm2
                   | NONE => bytes_in_memory_thm
         val (tac, the_state) =
           case asmLib.find_env is_riscv_next g of
              SOME x => env x
            | NONE => (all_tac, ms)
         val (step_thm, next_state) = step the_state l
         val next_state_var = new_state_var (g::asl)
      in
         imp_res_tac th
         \\ tac
         \\ assume_tac step_thm
         \\ qabbrev_tac `^next_state_var = ^next_state`
         \\ NO_STRIP_REV_FULL_SIMP_TAC (srw_ss())
              [lem1, lem4, lem5, lem10, lem11, bitstringTheory.word_lsb_v2w,
               alignmentTheory.aligned_numeric, riscv_stepTheory.Skip]
         \\ Tactical.PAT_X_ASSUM x_tm kall_tac
         \\ SUBST1_TAC (Thm.SPEC the_state riscv_next_def)
         \\ byte_eq_tac
         \\ NO_STRIP_REV_FULL_SIMP_TAC (srw_ss()++boolSimps.LET_ss) [lem1, lem5]
      end
      handle List.Empty => FAIL_TAC "next_state_tac: empty") (asl, g)
end

local
  val thm = CONJ (DECIDE ``~(n < 32n) ==> (n - 32 + 32 = n)``)
                 (DECIDE ``n <> 0n ==> (64 - n < 64)``)
  val cond_rand_thms =
    utilsLib.mk_cond_rand_thms
       (utilsLib.accessor_fns ``: riscv_state`` @
        utilsLib.accessor_fns ``: 64 asm_state``)
  fun drop_var_asms_tac var =
    let
      val var = mk_var (var, ``:riscv_state``)
    in
      rpt (WEAKEN_TAC (fn tm => not (markerSyntax.is_abbrev tm) andalso
                                free_in var tm))
    end
  val word_bit_0_mask = prove(
    ``!w. ¬word_bit 0 (0xFFFFFFFFFFFFFFFEw && w:word64)``,
    blastLib.BBLAST_TAC)
in
  fun state_tac asm (gs as (asl, _)) =
    let
      val l = List.mapPartial (Lib.total (fst o markerSyntax.dest_abbrev)) asl
      val (l, x) = Lib.front_last l
    in
      (
       NO_STRIP_FULL_SIMP_TAC (srw_ss())
         [riscv_ok_def, asmPropsTheory.sym_target_state_rel, riscv_target_def,
          riscv_config, lem2, cond_rand_thms,
          alignmentTheory.aligned_numeric, set_sepTheory.fun2set_eq]
       \\ (if not (List.null l) andalso
              (asmLib.isJump asm orelse asmLib.isCall asm) then
              (* Need to show that the register contents from the first
                 instruction are aligned *)
              NO_STRIP_FULL_SIMP_TAC (srw_ss()) [lem11]
              \\ TRY (qpat_assum `aligned 2 (_ : word64) ==> (NextRISCV _ = _)`
                (fn th => SUBGOAL_THEN (rand (rator (concl th)))
                             (fn lth => NO_STRIP_FULL_SIMP_TAC std_ss [lth])
                          >- (qpat_x_assum `aligned 2 _` mp_tac
                              \\ asm_simp_tac
                                   (srw_ss()++bitstringLib.v2w_n2w_ss)
                                   [Abbr [QUOTE x],
                                    combinTheory.APPLY_UPDATE_THM,
                                    alignmentTheory.aligned_extract]
                              \\ blastLib.BBLAST_TAC)))
              \\ qpat_x_assum `~(0xFFFFFFFFFFF00000w <= c) \/ ~(c <= 0xFFFFFw)`
                   kall_tac
           else
              all_tac)
       \\ MAP_EVERY (fn s =>
            drop_var_asms_tac s
            \\ qunabbrev_tac [QUOTE s]
            \\ asm_simp_tac (srw_ss()) [combinTheory.APPLY_UPDATE_THM,
                                        alignmentTheory.aligned_numeric]
            ) l
       \\ NO_STRIP_FULL_SIMP_TAC std_ss [word_bit_0_mask]
       \\ drop_var_asms_tac x
       \\ qunabbrev_tac [QUOTE x]
       \\ asm_simp_tac (srw_ss())
            [combinTheory.APPLY_UPDATE_THM, alignmentTheory.aligned_numeric]
       \\ CONV_TAC (Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV)
       \\ asm_simp_tac (srw_ss()) [asmPropsTheory.all_pcs]
       \\ (if asmLib.isAddCarry asm then
             qabbrev_tac `r2 = ms.c_gpr ms.procID (n2w n0)`
             \\ qabbrev_tac `r3 = ms.c_gpr ms.procID (n2w n1)`
             \\ REPEAT strip_tac
             \\ Cases_on `i = n2`
             \\ asm_simp_tac std_ss [wordsTheory.WORD_LO_word_0, lem8]
             >- (Cases_on `ms.c_gpr ms.procID (n2w n2) = 0w`
                 \\ asm_simp_tac (srw_ss())
                      [wordsTheory.WORD_LO_word_0, lem7, lem9]
                 \\ blastLib.BBLAST_TAC)
             \\ srw_tac [] [GSYM wordsTheory.word_add_n2w, lem7]
           else
             srw_tac []
                [combinTheory.APPLY_UPDATE_THM, alignmentTheory.aligned_numeric,
                 GSYM wordsTheory.word_mul_def, mul_long, riscv_overflow,
                 riscv_sub_overflow, ror, lem11, thm]
             \\ (if asmLib.isMem asm then
                   full_simp_tac
                      (srw_ss()++wordsLib.WORD_EXTRACT_ss++
                       wordsLib.WORD_CANCEL_ss) []
                 else
                   NO_STRIP_FULL_SIMP_TAC std_ss
                        [alignmentTheory.aligned_extract, lem12, lem12b]
                   \\ blastLib.FULL_BBLAST_TAC))
      ) gs
    end
end

val bytes_in_memory_IMP_all_pcs_MEM8 = Q.prove(
 `!env a xs m dm.
   bytes_in_memory a xs m dm /\
   (!(i:num) ms'. (∀a. a ∈ dm ⇒ (env i ms').MEM8 a = ms'.MEM8 a)) ==>
   (!i ms'. (∀pc. pc ∈ all_pcs (LENGTH xs) a 0 ==> (env i ms').MEM8 pc = ms'.MEM8 pc))`,
 Induct_on `xs`
 \\ rw [asmPropsTheory.all_pcs_def, miscTheory.bytes_in_memory_def]
 \\ metis_tac []);

local
   fun number_of_instructions asl =
      case asmLib.strip_bytes_in_memory (List.last asl) of
         SOME l => List.length l div 4
       | NONE => raise mk_HOL_ERR "riscv_targetProofTheory" "number_of_instructions" ""
   fun gen_next_tac (j, i) =
     exists_tac (numLib.term_of_int (j - 1))
     \\ simp [asmPropsTheory.asserts_eval,
              asmPropsTheory.asserts2_eval, set_sepTheory.fun2set_eq,
              asmPropsTheory.interference_ok_def, riscv_proj_def]
     \\ NTAC 2 strip_tac
     \\ drule bytes_in_memory_IMP_all_pcs_MEM8
     \\ disch_then (qspec_then `env` mp_tac)
     \\ simp []
     \\ strip_tac
     \\ NTAC i (split_bytes_in_memory_tac 4)
     \\ NTAC j next_state_tac
   fun next_tac_by_instructions gs =
      let
         val j = number_of_instructions (fst gs)
      in
         gen_next_tac (j, j - 1) gs
      end
   fun jc_next_tac_by_instructions gs =
      let
         val j = number_of_instructions (fst gs) - 1
      in
         gen_next_tac (j, j) gs
      end
   val (_, _, dest_riscv_enc, is_riscv_enc) =
     HolKernel.syntax_fns1 "riscv_target" "riscv_enc"
   fun get_asm tm = dest_riscv_enc (HolKernel.find_term is_riscv_enc tm)
   val aligned_imp_bit_0 = prove(
     ``aligned 2 w ==> ¬word_bit 0 (w:word64)``,
     fs [alignmentTheory.aligned_bitwise_and] \\ blastLib.BBLAST_TAC)
in
  fun next_tac gs =
    let
      val asm = get_asm (snd gs)
    in
      NO_STRIP_FULL_SIMP_TAC (srw_ss()++boolSimps.LET_ss) enc_rwts
      \\ next_tac_by_instructions
      \\ imp_res_tac aligned_imp_bit_0
      \\ NO_STRIP_FULL_SIMP_TAC (srw_ss()++boolSimps.LET_ss) enc_rwts
      \\ state_tac asm
    end gs
  fun jc_next_tac c =
    NO_STRIP_FULL_SIMP_TAC (srw_ss()++boolSimps.LET_ss) enc_rwts
    \\ Cases_on c
    >| [next_tac_by_instructions, jc_next_tac_by_instructions]
    \\ imp_res_tac aligned_imp_bit_0
    \\ NO_STRIP_FULL_SIMP_TAC (srw_ss()++boolSimps.LET_ss) enc_rwts
    \\ state_tac ``Inst Skip : 64 asm``
end

(* -------------------------------------------------------------------------
   riscv target_ok
   ------------------------------------------------------------------------- *)

val length_riscv_encode = Q.prove(
  `!i. LENGTH (riscv_encode i) = 4`,
  rw [riscv_encode_def])

val riscv_encode_not_nil = Q.prove(
  `!i. riscv_encode i <> []`,
  simp_tac std_ss [length_riscv_encode, GSYM listTheory.LENGTH_NIL])

val riscv_encoding = Q.prove (
   `!i. let l = riscv_enc i in (LENGTH l MOD 4 = 0) /\ l <> []`,
   strip_tac
   \\ asmLib.asm_cases_tac `i`
   \\ rw [riscv_enc_def, riscv_const32_def, riscv_encode_fail_def,
          length_riscv_encode, riscv_encode_not_nil, riscv_ast_def]
   \\ REPEAT CASE_TAC
   \\ rw [length_riscv_encode, riscv_encode_not_nil]
   )
   |> SIMP_RULE (srw_ss()++boolSimps.LET_ss) [riscv_enc_def]

val riscv_target_ok = Q.prove (
   `target_ok riscv_target`,
   rw ([asmPropsTheory.target_ok_def, asmPropsTheory.target_state_rel_def,
        riscv_proj_def, riscv_target_def, riscv_config, riscv_ok_def,
        set_sepTheory.fun2set_eq, riscv_encoding] @ enc_ok_rwts)
   >| [Cases_on `-0x100000w <= w1 /\ w1 <= 0xFFFFFw`
       \\ Cases_on `-0x100000w <= w2 /\ w2 <= 0xFFFFFw`,
       Cases_on `-0xFFCw <= w1 /\ w1 <= 0xFFFw`
       \\ Cases_on `-0xFFCw <= w2 /\ w2 <= 0xFFFw`
       \\ Cases_on `ri`
       \\ Cases_on `cmp`,
       Cases_on `-0x100000w <= w1 /\ w1 <= 0xFFFFFw`
       \\ Cases_on `-0x100000w <= w2 /\ w2 <= 0xFFFFFw`,
       all_tac
   ]
   \\ full_simp_tac (srw_ss()++boolSimps.LET_ss)
         (asmPropsTheory.offset_monotonic_def :: enc_ok_rwts)
   \\ DISCH_THEN kall_tac
   \\ blastLib.FULL_BBLAST_TAC
   )

(* -------------------------------------------------------------------------
   riscv encoder_correct
   ------------------------------------------------------------------------- *)

val print_tac = asmLib.print_tac "correct"

Theorem riscv_encoder_correct:
    encoder_correct riscv_target
Proof
   simp [asmPropsTheory.encoder_correct_def, riscv_target_ok]
   \\ qabbrev_tac `state_rel = target_state_rel riscv_target`
   \\ rw [riscv_target_def, riscv_config, asmSemTheory.asm_step_def]
   \\ qunabbrev_tac `state_rel`
   \\ Cases_on `i`
   >- (
      (*--------------
          Inst
        --------------*)
      Cases_on `i'`
      >- (
         (*--------------
             Skip
           --------------*)
         print_tac "Skip"
         \\ next_tac
         )
      >- (
         (*--------------
             Const
           --------------*)
         print_tac "Const"
         \\ Cases_on `c = sw2sw ((11 >< 0) c : word12)`
         >- next_tac
         \\ Cases_on `((63 >< 32) c = 0w: word32) /\ ~c ' 31 \/
                      ((63 >< 32) c = -1w: word32) /\ c ' 31`
         >- (Cases_on `c ' 11` \\ next_tac)
         \\ Cases_on `c ' 31`
         \\ Cases_on `c ' 43`
         \\ Cases_on `c ' 11`
         \\ next_tac
         )
      >- (
         (*--------------
             Arith
           --------------*)
         Cases_on `a`
         >- (
            (*--------------
                Binop
              --------------*)
            print_tac "Binop"
            \\ Cases_on `r`
            \\ Cases_on `b`
            \\ next_tac
            )
         >- (
            (*--------------
                Shift
              --------------*)
            print_tac "Shift"
            \\ Cases_on `s`
            \\ next_tac
            )
         >- (
            (*--------------
                Div
              --------------*)
            print_tac "Div"
            \\ next_tac
            )
         >- (
            (*--------------
                LongMul
              --------------*)
            print_tac "LongMul"
            \\ next_tac
            )
         >- (
            (*--------------
                LongDiv
              --------------*)
            print_tac "LongDiv"
            \\ next_tac
            )
         >- (
            (*--------------
                AddCarry
              --------------*)
            print_tac "AddCarry"
            \\ next_tac
            )
         >- (
            (*--------------
                AddOverflow
              --------------*)
            print_tac "AddOverflow"
            \\ next_tac
            )
         >- (
            (*--------------
                SubOverflow
              --------------*)
            print_tac "SubOverflow"
            \\ next_tac
            )
         )
         >- (
            (*--------------
                Mem
              --------------*)
            print_tac "Mem"
            \\ Cases_on `a`
            \\ Cases_on `m`
            \\ next_tac
            )
         (*--------------
             FP
           --------------*)
         \\ print_tac "FP"
         \\ Cases_on `f`
         \\ next_tac
      ) (* close Inst *)
      (*--------------
          Jump
        --------------*)
   >- (
      print_tac "Jump"
      \\ Cases_on `-0x100000w <= c /\ c <= 0xFFFFFw`
      \\ next_tac
      )
   >- (
      (*--------------
          JumpCmp
        --------------*)
      print_tac "JumpCmp"
      \\ Cases_on `-0xFFCw <= c0 /\ c0 <= 0xFFFw`
      >- (Cases_on `r`
          \\ Cases_on `c`
          \\ next_tac)
      \\ Cases_on `r`
      \\ Cases_on `c`
      >| [
        jc_next_tac `ms.c_gpr ms.procID (n2w n) = ms.c_gpr ms.procID (n2w n')`,
        jc_next_tac `ms.c_gpr ms.procID (n2w n) <+ ms.c_gpr ms.procID (n2w n')`,
        jc_next_tac `ms.c_gpr ms.procID (n2w n) < ms.c_gpr ms.procID (n2w n')`,
        jc_next_tac `(ms.c_gpr ms.procID (n2w n) &&
                      ms.c_gpr ms.procID (n2w n')) = 0w`,
        jc_next_tac `ms.c_gpr ms.procID (n2w n) <> ms.c_gpr ms.procID (n2w n')`,
        jc_next_tac `~(ms.c_gpr ms.procID (n2w n) <+
                       ms.c_gpr ms.procID (n2w n'))`,
        jc_next_tac `~(ms.c_gpr ms.procID (n2w n) <
                       ms.c_gpr ms.procID (n2w n'))`,
        jc_next_tac `(ms.c_gpr ms.procID (n2w n) &&
                      ms.c_gpr ms.procID (n2w n')) <> 0w`,
        jc_next_tac `ms.c_gpr ms.procID (n2w n) = c'`,
        jc_next_tac `ms.c_gpr ms.procID (n2w n) <+ c'`,
        jc_next_tac `ms.c_gpr ms.procID (n2w n) < c'`,
        jc_next_tac `(ms.c_gpr ms.procID (n2w n) && c') = 0w`,
        jc_next_tac `ms.c_gpr ms.procID (n2w n) <> c'`,
        jc_next_tac `~(ms.c_gpr ms.procID (n2w n) <+ c')`,
        jc_next_tac `~(ms.c_gpr ms.procID (n2w n) < c')`,
        jc_next_tac `(ms.c_gpr ms.procID (n2w n) && c') <> 0w`
      ]
      )
      (*--------------
          Call
        --------------*)
   >- (
      print_tac "Call"
      \\ Cases_on `-0x100000w <= c /\ c <= 0xFFFFFw`
      \\ next_tac
      )
   >- (
      (*--------------
          JumpReg
        --------------*)
      print_tac "JumpReg"
      \\ next_tac
      )
   >- (
      (*--------------
          Loc
        --------------*)
      print_tac "Loc"
      \\ next_tac
      )
QED

val () = export_theory ()
