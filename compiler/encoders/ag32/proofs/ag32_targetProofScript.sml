(*
  Prove `encoder_correct` for ag32, i.e. Silver ISA
*)
open HolKernel Parse boolLib bossLib
open asmLib ag32_targetTheory;

val () = new_theory "ag32_targetProof"

val () = wordsLib.guess_lengths()

(* some lemmas ---------------------------------------------------------- *)

val bytes_in_memory_thm = Q.prove(
   `!w s state a b c d.
      target_state_rel ag32_target s state /\
      bytes_in_memory s.pc [a; b; c; d] s.mem s.mem_domain ==>
      aligned 2 state.PC /\
      (state.MEM state.PC = a) /\
      (state.MEM (state.PC + 1w) = b) /\
      (state.MEM (state.PC + 2w) = c) /\
      (state.MEM (state.PC + 3w) = d) /\
      state.PC + 3w IN s.mem_domain /\
      state.PC + 2w IN s.mem_domain /\
      state.PC + 1w IN s.mem_domain /\
      state.PC IN s.mem_domain`,
   rw [asmPropsTheory.target_state_rel_def, ag32_target_def, ag32_config_def,
       ag32_ok_def, miscTheory.bytes_in_memory_def,
       alignmentTheory.aligned_extract, set_sepTheory.fun2set_eq,
       wordsTheory.WORD_LS_word_T]
   \\ fs []
   )

val bytes_in_memory_thm2 = Q.prove(
   `!w s state a b c d.
      target_state_rel ag32_target s state /\
      bytes_in_memory (s.pc + w) [a; b; c; d] s.mem s.mem_domain ==>
      (state.MEM (state.PC + w) = a) /\
      (state.MEM (state.PC + w + 1w) = b) /\
      (state.MEM (state.PC + w + 2w) = c) /\
      (state.MEM (state.PC + w + 3w) = d) /\
      state.PC + w + 3w IN s.mem_domain /\
      state.PC + w + 2w IN s.mem_domain /\
      state.PC + w + 1w IN s.mem_domain /\
      state.PC + w IN s.mem_domain`,
   rw [asmPropsTheory.target_state_rel_def, ag32_target_def, ag32_config_def,
       ag32_ok_def, miscTheory.bytes_in_memory_def, set_sepTheory.fun2set_eq]
   )

val add_carry_lem = Q.prove(
  `!w: word32. 0x100000000 <= w2n w + 0xFFFFFFFF <=> w <> 0w`,
  Cases \\ simp [])

val add_carry_lem2 = Q.prove(
  `!a b. n2w (w2n a + (w2n b + 1)) = a + b + 1w`,
  Cases
  \\ Cases
  \\ simp [wordsTheory.word_add_n2w]
  )

val shift_lem = Q.prove(
  `!n. n < 32 ==> (w2n (sw2sw (n2w n : word6) : word32) = n)`,
  rpt strip_tac
  \\ full_simp_tac std_ss [wordsTheory.NUMERAL_LESS_THM]
  \\ simp []
  )

val long_mul_lem = Q.prove(
  `!a : word32 b : word32.
    n2w ((w2n a * w2n b) DIV 4294967296) =
    (63 >< 32) (w2w a * w2w b : word64) : word32`,
  Cases
  \\ Cases
  \\ fs [wordsTheory.w2w_n2w, wordsTheory.word_mul_n2w,
         wordsTheory.word_extract_n2w, bitTheory.BITS_THM]
  )

val jump_lem =
  blastLib.BBLAST_PROVE
   ``!c: word32. 0xFFFFFFE0w <= c /\ c < 32w ==> (sw2sw (w2w c : word6) = c)``

val jump_lem2 =
  blastLib.BBLAST_PROVE
   ``!c: word32.
       0xFF800005w <= c /\ c <= 0x800003w /\
       0w <= c + 0xFFFFFFFCw ==>
       (w2w (w2w (c + 0xFFFFFFFCw) : 23 word) = c - 4w)``

val jump_lem3 =
  blastLib.BBLAST_PROVE
   ``!c: word32.
       0xFF800005w <= c /\ c <= 0x800003w /\
       ~(0w <= c + 0xFFFFFFFCw) ==>
       (-1w * w2w (w2w (-1w * (c + 0xFFFFFFFCw)) : 23 word) = c - 4w)``

val load_lem =
  blastLib.BBLAST_PROVE
   ``!c: word32.  0xFFFFFFE0w <= c /\ c <= 31w ==> (sw2sw (w2w c :word6) = c)``

val load_lem2 = Q.prove(
  `!c : word32. aligned 2 c ==> ((31 >< 2) c @@ (0w : word2) = c)`,
  simp [alignmentTheory.aligned_extract]
  \\ blastLib.BBLAST_TAC
  )

val load_lem3 =
  blastLib.BBLAST_PROVE
   ``!(c:word32). 0xFF800001w <= c /\ ~(0w <= c) ==>
      (-1w * w2w (w2w (-1w * c) : 23 word) = c)``

val store_lem =
  blastLib.BBLAST_PROVE
    ``(!a: word32. a <> a + 3w) /\
      (!a: word32. a <> a + 2w) /\
      (!a: word32. a <> a + 1w)``

val store_lem2 =
  blastLib.BBLAST_PROVE
   ``!(c:word32). 0w <= c /\ c <= 0x7FFFFFw ==>
      (w2w ((w2w c) : 23 word) = c)``

val mem_lem =
  blastLib.BBLAST_PROVE
   ``!(c:word32). bit_field_insert 31 23 ((31 >< 23) c) (w2w ((22 >< 0) c)) = c``;

(* some rewrites ---------------------------------------------------------- *)

local
  open ag32Theory
in
  val encode_rwts =
    [ag32_encode_def, ag32_enc_def, ag32_encode1_def, ag32_bop_def,
     ag32_sh_def, ag32_cmp_def, ag32_constant_def, ag32_jump_constant_def]
  val encode_extra_rwts = [ri2bits_def, enc_def, encShift_def, Encode_def]
end

val enc_rwts =
  [asmPropsTheory.offset_monotonic_def, ag32_config, ag32_asm_ok] @
  encode_rwts @ asmLib.asm_rwts

val enc_ok_rwts =
  [asmPropsTheory.enc_ok_def, ag32_config, ag32_asm_ok] @ encode_rwts

(* some custom tactics ---------------------------------------------------- *)

(* -------------------------------------------------------------------------
   ag32 target_ok
   ------------------------------------------------------------------------- *)

val length_ag32_encode = Q.prove(
  `!i. (LENGTH (ag32_encode1 i) = 4) /\ (ag32_encode1 i <> [])`,
  rw [ag32_encode1_def])

val ag32_encoding = Q.prove (
   `!i. let l = ag32_enc i in (LENGTH l MOD 4 = 0) /\ l <> []`,
   strip_tac
   \\ asmLib.asm_cases_tac `i`
   \\ simp [ag32_enc_def, ag32_constant_def, ag32_jump_constant_def,
            ag32_cmp_def, length_ag32_encode, ag32_encode_def]
   \\ REPEAT CASE_TAC
   \\ rw [length_ag32_encode]
   )
   |> SIMP_RULE (srw_ss()++boolSimps.LET_ss) [ag32_enc_def]

val ag32_target_ok = Q.prove (
   `target_ok ag32_target`,
   rw ([asmPropsTheory.target_ok_def, asmPropsTheory.target_state_rel_def,
        ag32_proj_def, ag32_target_def, ag32_config, ag32_ok_def,
        set_sepTheory.fun2set_eq, ag32_encoding] @ enc_ok_rwts)
   >| [ Cases_on `0w <= w1` \\ Cases_on `0w <= w2`,
        Cases_on `ri` \\ Cases_on `cmp`,
        Cases_on `0w <= w1` \\ Cases_on `0w <= w2`,
        Cases_on `0xFFFFFFE0w <= w1 + 0xFFFFFFFCw /\ w1 + 0xFFFFFFFCw < 32w`
        \\ Cases_on `0xFFFFFFE0w <= w2 + 0xFFFFFFFCw /\ w2 + 0xFFFFFFFCw < 32w`
   ]
   \\ lfs (enc_rwts @ encode_extra_rwts)
   \\ rw [length_ag32_encode]
   \\ blastLib.FULL_BBLAST_TAC
   )

val aligned_pc = Q.prove(
  `!a : word32. aligned 2 a ==> (((31 >< 2) a : word30) @@ (0w : word2) = a)`,
  simp [alignmentTheory.aligned_extract]
  \\ blastLib.BBLAST_TAC
  )

Theorem concat_bytes:
  !w: word32. (31 >< 24) w @@ (23 >< 16) w @@ (15 >< 8) w @@ (7 >< 0) w = w
Proof
  blastLib.BBLAST_TAC
QED

val funcT_thm = Q.prove(
  `!func.
     num2funcT
       (w2n (v2w
         [BIT 3 (funcT2num func); BIT 2 (funcT2num func);
          BIT 1 (funcT2num func); BIT 0 (funcT2num func)] : word4)) = func`,
  Cases \\ simp_tac (srw_ss()++bitstringLib.v2w_n2w_ss) [])

val shiftT_thm = Q.prove(
  `!shiftOp.
     num2shiftT
       (w2n ((1 >< 0) (v2w
         [BIT 3 (shiftT2num shiftOp); BIT 2 (shiftT2num shiftOp);
          BIT 1 (shiftT2num shiftOp); BIT 0 (shiftT2num shiftOp)] : word4))) =
     shiftOp`,
  Cases \\ simp_tac (srw_ss()++bitstringLib.v2w_n2w_ss) [])

fun tac q l = qmatch_goalsub_rename_tac q \\ MAP_EVERY Cases_on l

(* The encoder and decoder are well-behaved *)
Theorem Decode_Encode:
   !i. Decode (Encode i) = i
Proof
  Cases
  \\ TRY (pairLib.PairCases_on `p`)
  >| [
    tac `Accelerator (w, a)` [`a`],
    all_tac,
    all_tac,
    tac `Jump (func, w, a)` [`a`],
    tac `JumpIfNotZero (func, w, a, b)` [`w`, `a`, `b`],
    tac `JumpIfZero (func, w, a, b)` [`w`, `a`, `b`],
    tac `LoadConstant (reg, negate, imm)` [],
    tac `LoadMEM (w, a)` [`a`],
    tac `LoadMEMByte (w, a)` [`a`],
    tac `LoadUpperConstant (reg, imm)` [],
    tac `Normal (func, w, a, b)` [`w`, `a`, `b`],
    tac `Out (func, w, a, b)` [`w`, `a`, `b`],
    all_tac,
    tac `Shift (shiftOp, w, a, b)` [`w`, `a`, `b`],
    tac `StoreMEM (a, b)` [`a`, `b`],
    tac `StoreMEMByte (a, b)` [`a`, `b`]
  ]
  \\ simp [ag32Theory.Encode_def, ag32Theory.ri2bits_def, ag32Theory.enc_def,
           ag32Theory.encShift_def, ag32Theory.Decode_def,
           ag32Theory.DecodeReg_imm_def, ag32Theory.boolify32_def]
  \\ CONV_TAC blastLib.BBLAST_CONV
  \\ simp [funcT_thm, shiftT_thm]
  \\ CONV_TAC blastLib.BBLAST_CONV
QED

val ag32_run = Q.prove(
  `!i ms.
     (ms.MEM ms.PC = (7 >< 0) (Encode i)) /\
     (ms.MEM (ms.PC + 1w) = (15 >< 8) (Encode i)) /\
     (ms.MEM (ms.PC + 2w) = (23 >< 16) (Encode i)) /\
     (ms.MEM (ms.PC + 3w) = (31 >< 24) (Encode i)) /\
     aligned 2 ms.PC ==>
     (Next ms = Run i ms)`,
  simp [ag32Theory.Next_def, aligned_pc, concat_bytes, Decode_Encode,
        wordsTheory.WORD_LS_word_T]
  )

local
  val ms = ``ms: ag32_state``
  val thms =
    List.map (DB.fetch "ag32")
     (List.filter (fn s => not (Lib.mem s ["Next_def", "Encode_def"]))
        (#C (ag32Theory.inventory)))
  val is_ag32_next = #4 (HolKernel.syntax_fns1 "ag32" "Next")
in
  fun next_state_tac (asl, g) =
    let
      val x as (pc, l, _, _) =
        List.last (List.mapPartial (Lib.total asmLib.dest_bytes_in_memory) asl)
      val x_tm = asmLib.mk_bytes_in_memory x
      val l = fst (listSyntax.dest_list l)
      val th = case Lib.total wordsSyntax.dest_word_add pc of
                  SOME (_, w) => Thm.SPEC w bytes_in_memory_thm2
                | NONE => bytes_in_memory_thm
      val i = l |> hd |> rand |> rand
      val the_state =
        case asmLib.find_env is_ag32_next g of
           SOME (t, tm) => ``env ^t ^tm : ag32_state``
         | NONE => ms
    in
      imp_res_tac th
      \\ assume_tac (Drule.SPECL [i, the_state] ag32_run)
      \\ NO_STRIP_REV_FULL_SIMP_TAC (srw_ss()++boolSimps.LET_ss)
           ([set_sepTheory.fun2set_eq, alignmentTheory.aligned_numeric] @ thms)
      \\ pop_assum kall_tac
      \\ Tactical.PAT_X_ASSUM x_tm kall_tac
    end (asl, g)
end

val state_tac =
  NO_STRIP_FULL_SIMP_TAC (srw_ss())
     [asmPropsTheory.sym_target_state_rel, ag32_target_def,
      asmPropsTheory.all_pcs, ag32_ok_def, ag32_config,
      combinTheory.APPLY_UPDATE_THM, alignmentTheory.aligned_numeric,
      alignmentTheory.align_aligned, set_sepTheory.fun2set_eq,
      wordsTheory.WORD_LS_word_T, load_lem, load_lem3, store_lem2, mem_lem]
  \\ rw [alignmentTheory.aligned_numeric, combinTheory.APPLY_UPDATE_THM,
         wordsTheory.word_lsl_bv_def, wordsTheory.word_lsr_bv_def,
         wordsTheory.word_asr_bv_def, wordsTheory.word_ror_bv_def,
         shift_lem, add_carry_lem, add_carry_lem2,
         jump_lem, jump_lem2, jump_lem3, long_mul_lem,
         GSYM wordsTheory.word_add_def,
         GSYM wordsTheory.word_mul_def,
         ONCE_REWRITE_RULE [wordsTheory.WORD_ADD_COMM]
             alignmentTheory.aligned_add_sub]
  \\ full_simp_tac (srw_ss()++bitstringLib.v2w_n2w_ss) [load_lem2, store_lem]
  \\ blastLib.FULL_BBLAST_TAC

val bytes_in_memory_IMP_all_pcs_MEM = Q.prove(
 `!env a xs m dm.
   bytes_in_memory a xs m dm /\
   (*(!(i:num) ms'. (∀a. a ∈ dm ⇒ (env i ms').MEM a = ms'.MEM a)) ==>*)
   (!(i:num) ms'. fun2set ((env i ms').MEM, dm) = fun2set (ms'.MEM, dm)) ==>
   (!i ms'. (∀pc. pc ∈ all_pcs (LENGTH xs) a 0 ==> (env i ms').MEM pc = ms'.MEM pc))`,
 simp [set_sepTheory.fun2set_eq] \\ Induct_on `xs`
 \\ rw [asmPropsTheory.all_pcs_def, miscTheory.bytes_in_memory_def]
 \\ metis_tac []);

local
   fun number_of_instructions asl =
      case asmLib.strip_bytes_in_memory (List.last asl) of
         SOME l => List.length l div 4
       | NONE => raise mk_HOL_ERR "ag32_targetProofTheory" "number_of_instructions" ""
   fun next_tac' (gs as (asl, _)) =
      let
         val j = number_of_instructions asl
         val i = j - 1
         val n = numLib.term_of_int (j - 1)
      in
         exists_tac n
         \\ simp_tac (srw_ss()++boolSimps.CONJ_ss)
              [asmPropsTheory.asserts_eval,
               asmPropsTheory.asserts2_eval,
               asmPropsTheory.interference_ok_def, ag32_proj_def]
         \\ NTAC 2 strip_tac
         \\ drule bytes_in_memory_IMP_all_pcs_MEM
         \\ disch_then (qspec_then `env` mp_tac)
         \\ asm_simp_tac (srw_ss()) []
         \\ strip_tac
         \\ NTAC i (split_bytes_in_memory_tac 4)
         \\ NTAC j next_state_tac
      end gs
in
  val next_tac =
    Q.PAT_ABBREV_TAC `instr = ag32_enc _`
    \\ pop_assum mp_tac
    \\ ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss) enc_rwts
    \\ NO_STRIP_FULL_SIMP_TAC (srw_ss()++boolSimps.LET_ss) enc_rwts
    \\ strip_tac
    \\ qunabbrev_tac `instr`
    \\ NO_STRIP_FULL_SIMP_TAC (srw_ss()) []
    \\ next_tac'
    \\ state_tac
end

(* -------------------------------------------------------------------------
   ag32 encoder_correct
   ------------------------------------------------------------------------- *)

val print_tac = asmLib.print_tac "correct"

Theorem ag32_encoder_correct:
    encoder_correct ag32_target
Proof
   simp [asmPropsTheory.encoder_correct_def, ag32_target_ok]
   \\ qabbrev_tac `state_rel = target_state_rel ag32_target`
   \\ rw [ag32_target_def, ag32_config, asmSemTheory.asm_step_def]
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
         \\ Cases_on `-0x7FFFFFw <= c /\ c < 0x7FFFFFw`
         >| [Cases_on `0w <= c`, all_tac]
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
            >- (Cases_on `b` \\ next_tac)
            \\ Cases_on `(b = Xor) /\ (c = -1w)`
            >- next_tac
            \\ Cases_on `b`
            \\ (Cases_on `-32w <= c /\ c < 32w`
                >| [all_tac, Cases_on `0w <= c` \\ fs []]
                \\ next_tac)
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
            print_tac "LongMul"
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
         \\ (Cases_on `-32w <= c /\ c < 32w`
             >| [all_tac,
                 Cases_on `-0x7FFFFFw <= c /\ c < 0x7FFFFFw` >| [Cases_on `0w <= c`, all_tac]])
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
      \\ next_tac
      )
   >- (
      (*--------------
          JumpCmp
        --------------*)
      print_tac "JumpCmp"
      \\ Cases_on `r`
      \\ Cases_on `c`
      \\ next_tac
      )
      (*--------------
          Call
        --------------*)
   >- (
      print_tac "Call"
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
