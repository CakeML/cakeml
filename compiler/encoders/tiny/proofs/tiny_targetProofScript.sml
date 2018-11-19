open HolKernel Parse boolLib bossLib
open asmLib tiny_targetTheory;

val () = new_theory "tiny_targetProof"

val () = wordsLib.guess_lengths()

(* some lemmas ---------------------------------------------------------- *)

val bytes_in_memory_thm = Q.prove(
   `!w s state a b c d.
      target_state_rel tiny_target s state /\
      bytes_in_memory s.pc [a; b; c; d] s.mem s.mem_domain ==>
      ~state.Reset /\
      (state.lastMemAddr = UINT_MAXw) /\
      aligned 2 state.PC /\
      (state.MEM state.PC = a) /\
      (state.MEM (state.PC + 1w) = b) /\
      (state.MEM (state.PC + 2w) = c) /\
      (state.MEM (state.PC + 3w) = d) /\
      state.PC + 3w IN s.mem_domain /\
      state.PC + 2w IN s.mem_domain /\
      state.PC + 1w IN s.mem_domain /\
      state.PC IN s.mem_domain`,
   rw [asmPropsTheory.target_state_rel_def, tiny_target_def, tiny_config_def,
       tiny_ok_def, asmSemTheory.bytes_in_memory_def,
       alignmentTheory.aligned_extract, set_sepTheory.fun2set_eq,
       wordsTheory.WORD_LS_word_T]
   \\ fs []
   )

val bytes_in_memory_thm2 = Q.prove(
   `!w s state a b c d.
      target_state_rel tiny_target s state /\
      bytes_in_memory (s.pc + w) [a; b; c; d] s.mem s.mem_domain ==>
      (state.MEM (state.PC + w) = a) /\
      (state.MEM (state.PC + w + 1w) = b) /\
      (state.MEM (state.PC + w + 2w) = c) /\
      (state.MEM (state.PC + w + 3w) = d) /\
      state.PC + w + 3w IN s.mem_domain /\
      state.PC + w + 2w IN s.mem_domain /\
      state.PC + w + 1w IN s.mem_domain /\
      state.PC + w IN s.mem_domain`,
   rw [asmPropsTheory.target_state_rel_def, tiny_target_def, tiny_config_def,
       tiny_ok_def, asmSemTheory.bytes_in_memory_def, set_sepTheory.fun2set_eq]
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

val store_lem =
  blastLib.BBLAST_PROVE
    ``(!a: word32. a <> a + 3w) /\
      (!a: word32. a <> a + 2w) /\
      (!a: word32. a <> a + 1w)``

(* some rewrites ---------------------------------------------------------- *)

local
  open tinyTheory
in
  val encode_rwts =
    [tiny_encode_def, tiny_enc_def, tiny_encode1_def, tiny_bop_def,
     tiny_sh_def, tiny_cmp_def, tiny_constant_def]
  val encode_extra_rwts = [ri2bits_def, enc_def, encShift_def, Encode_def]
end

val enc_rwts =
  [asmPropsTheory.offset_monotonic_def, tiny_config, tiny_asm_ok] @
  encode_rwts @ asmLib.asm_rwts

val enc_ok_rwts =
  [asmPropsTheory.enc_ok_def, tiny_config, tiny_asm_ok] @ encode_rwts

(* some custom tactics ---------------------------------------------------- *)

(* -------------------------------------------------------------------------
   mips target_ok
   ------------------------------------------------------------------------- *)

val length_tiny_encode = Q.prove(
  `!i. (LENGTH (tiny_encode1 i) = 4) /\ (tiny_encode1 i <> [])`,
  rw [tiny_encode1_def])

val tiny_encoding = Q.prove (
   `!i. let l = tiny_enc i in (LENGTH l MOD 4 = 0) /\ l <> []`,
   strip_tac
   \\ asmLib.asm_cases_tac `i`
   \\ simp [tiny_enc_def, tiny_cmp_def, length_tiny_encode, tiny_encode_def]
   \\ REPEAT CASE_TAC
   \\ rw [length_tiny_encode]
   )
   |> SIMP_RULE (srw_ss()++boolSimps.LET_ss) [tiny_enc_def]

val tiny_target_ok = Q.prove (
   `target_ok tiny_target`,
   rw ([asmPropsTheory.target_ok_def, asmPropsTheory.target_state_rel_def,
        tiny_proj_def, tiny_target_def, tiny_config, tiny_ok_def,
        set_sepTheory.fun2set_eq, tiny_encoding] @ enc_ok_rwts)
   >| [ Cases_on `0w <= w1` \\ Cases_on `0w <= w2`,
        Cases_on `ri` \\ Cases_on `cmp`,
        Cases_on `0w <= w1` \\ Cases_on `0w <= w2`,
        Cases_on `0xFFFFFFE0w <= w1 + 0xFFFFFFFCw /\ w1 + 0xFFFFFFFCw < 32w`
        \\ Cases_on `0xFFFFFFE0w <= w2 + 0xFFFFFFFCw /\ w2 + 0xFFFFFFFCw < 32w`
   ]
   \\ lfs (enc_rwts @ encode_extra_rwts)
   \\ rw []
   \\ blastLib.FULL_BBLAST_TAC
   )

val aligned_pc = Q.prove(
  `!a : word32. aligned 2 a ==> (((31 >< 2) a : word30) @@ (0w : word2) = a)`,
  simp [alignmentTheory.aligned_extract]
  \\ blastLib.BBLAST_TAC
  )

val concat_bytes =
  blastLib.BBLAST_PROVE
    ``!w: word32.
         (31 >< 24) w @@ (23 >< 16) w @@ (15 >< 8) w @@ (7 >< 0) w = w``

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
       (w2n (v2w
         [BIT 3 (shiftT2num shiftOp); BIT 2 (shiftT2num shiftOp);
          BIT 1 (shiftT2num shiftOp); BIT 0 (shiftT2num shiftOp)] : word4)) =
     shiftOp`,
  Cases \\ simp_tac (srw_ss()++bitstringLib.v2w_n2w_ss) [])

fun tac q l = qmatch_goalsub_rename_tac q \\ MAP_EVERY Cases_on l

(* The encoder and decoder are well-behaved *)
val decode_encode = Q.prove(
  `!i. Decode (Encode i) = i`,
  Cases
  \\ TRY (pairLib.PairCases_on `p`)
  >| [
    tac `Accelerator (w, a)` [`a`],
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
    tac `StoreMEM (func, w, a, b)` [`w`, `a`, `b`],
    tac `StoreMEMByte (func, w, a, b)` [`w`, `a`, `b`]
  ]
  \\ simp [tinyTheory.Encode_def, tinyTheory.ri2bits_def, tinyTheory.enc_def,
           tinyTheory.encShift_def, tinyTheory.Decode_def,
           tinyTheory.DecodeReg_imm_def, tinyTheory.boolify32_def]
  \\ CONV_TAC blastLib.BBLAST_CONV
  \\ simp [funcT_thm, shiftT_thm]
  \\ CONV_TAC blastLib.BBLAST_CONV
  )

val tiny_run = Q.prove(
  `!i ms.
     (ms.MEM ms.PC = (7 >< 0) (Encode i)) /\
     (ms.MEM (ms.PC + 1w) = (15 >< 8) (Encode i)) /\
     (ms.MEM (ms.PC + 2w) = (23 >< 16) (Encode i)) /\
     (ms.MEM (ms.PC + 3w) = (31 >< 24) (Encode i)) /\
     ~ms.Reset /\ (ms.lastMemAddr = UINT_MAXw) /\ aligned 2 ms.PC ==>
     (Next ms = Run i ms)`,
  simp [tinyTheory.Next_def, aligned_pc, concat_bytes, decode_encode,
        wordsTheory.WORD_LS_word_T]
  )

local
  val ms = ``ms: tiny_state``
  val thms =
    List.map (DB.fetch "tiny")
     (List.filter (fn s => not (Lib.mem s ["Next_def", "Encode_def"]))
        (#C (tinyTheory.inventory)))
  val is_tiny_next = #4 (HolKernel.syntax_fns1 "tiny" "Next")
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
        case asmLib.find_env is_tiny_next g of
           SOME (t, tm) => ``env ^t ^tm : tiny_state``
         | NONE => ms
    in
      imp_res_tac th
      \\ assume_tac (Drule.SPECL [i, the_state] tiny_run)
      \\ NO_STRIP_REV_FULL_SIMP_TAC (srw_ss()++boolSimps.LET_ss)
           ([set_sepTheory.fun2set_eq, alignmentTheory.aligned_numeric] @ thms)
      \\ pop_assum kall_tac
      \\ Tactical.PAT_X_ASSUM x_tm kall_tac
    end (asl, g)
end

val state_tac =
  NO_STRIP_FULL_SIMP_TAC (srw_ss())
     [asmPropsTheory.sym_target_state_rel, tiny_target_def,
      asmPropsTheory.all_pcs, tiny_ok_def, tiny_config,
      combinTheory.APPLY_UPDATE_THM, alignmentTheory.aligned_numeric,
      alignmentTheory.align_aligned, set_sepTheory.fun2set_eq,
      wordsTheory.WORD_LS_word_T, load_lem, load_lem2]
  \\ rw [alignmentTheory.aligned_numeric, combinTheory.APPLY_UPDATE_THM,
         wordsTheory.word_lsl_bv_def, wordsTheory.word_lsr_bv_def,
         wordsTheory.word_asr_bv_def, wordsTheory.word_ror_bv_def,
         shift_lem, add_carry_lem, add_carry_lem2,
         jump_lem, jump_lem2, jump_lem3, long_mul_lem,
         GSYM wordsTheory.word_add_def,
         GSYM wordsTheory.word_mul_def,
         ONCE_REWRITE_RULE [wordsTheory.WORD_ADD_COMM]
             alignmentTheory.aligned_add_sub]
  \\ full_simp_tac (srw_ss()++bitstringLib.v2w_n2w_ss) [store_lem]
  \\ blastLib.FULL_BBLAST_TAC

local
   fun number_of_instructions asl =
      case asmLib.strip_bytes_in_memory (List.last asl) of
         SOME l => List.length l div 4
       | NONE => raise mk_HOL_ERR "tiny_targetProofTheory" "number_of_instructions" ""
   fun next_tac' (gs as (asl, _)) =
      let
         val j = number_of_instructions asl
         val i = j - 1
         val n = numLib.term_of_int (j - 1)
      in
         exists_tac n
         \\ simp_tac (srw_ss()++boolSimps.CONJ_ss)
              [asmPropsTheory.asserts_eval,
               asmPropsTheory.interference_ok_def, tiny_proj_def]
         \\ NTAC 2 strip_tac
         \\ NTAC i (split_bytes_in_memory_tac 4)
         \\ NTAC j next_state_tac
      end gs
in
  val next_tac =
    Q.PAT_ABBREV_TAC `instr = tiny_enc _`
    \\ pop_assum mp_tac
    \\ NO_STRIP_FULL_SIMP_TAC (srw_ss()++boolSimps.LET_ss) enc_rwts
    \\ strip_tac
    \\ qunabbrev_tac `instr`
    \\ NO_STRIP_FULL_SIMP_TAC (srw_ss()) []
    \\ next_tac'
    \\ state_tac
end

(* -------------------------------------------------------------------------
   tiny encoder_correct
   ------------------------------------------------------------------------- *)

val print_tac = asmLib.print_tac "correct"

val tiny_encoder_correct = Q.store_thm ("tiny_encoder_correct",
   `encoder_correct tiny_target`,
   simp [asmPropsTheory.encoder_correct_def, tiny_target_ok]
   \\ qabbrev_tac `state_rel = target_state_rel tiny_target`
   \\ rw [tiny_target_def, tiny_config, asmSemTheory.asm_step_def]
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
         \\ Cases_on `word_abs c <+ 0x800000w`
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
      \\ Cases_on `0xFFFFFFE0w <= c /\ c < 32w`
      >- next_tac
      \\ Cases_on `0w <= c + 0xFFFFFFFCw`
      \\ next_tac
      )
   >- (
      (*--------------
          JumpCmp
        --------------*)
      print_tac "JumpCmp"
      \\ Cases_on `r`
      \\ Cases_on `c`
      \\ Cases_on `0w <= c0 + 0xFFFFFFFCw`
      \\ next_tac
      )
      (*--------------
          Call
        --------------*)
   >- (
      print_tac "Call"
      \\ Cases_on `0xFFFFFFE0w <= c /\ c < 32w`
      >- next_tac
      \\ Cases_on `0w <= c + 0xFFFFFFFCw`
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
      \\ Cases_on `0xFFFFFFE0w <= c + 0xFFFFFFFCw /\ c + 0xFFFFFFFCw < 32w`
      >- next_tac
      \\ Cases_on `0w <= c + 0xFFFFFFFCw`
      \\ next_tac
      )
   )

val () = export_theory ()
