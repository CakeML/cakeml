open HolKernel Parse boolLib bossLib
open asmLib mips_stepLib mips_targetTheory;

val () = new_theory "mips_targetProof"

val () = wordsLib.guess_lengths()

(* some lemmas ---------------------------------------------------------- *)

val mips_asm_state =
   REWRITE_RULE [DECIDE ``1 < i = i <> 0n /\ i <> 1n``] mips_asm_state_def

val bytes_in_memory_thm = Q.prove(
   `!w s state a b c d.
      mips_asm_state s state /\
      bytes_in_memory s.pc [a; b; c; d] s.mem s.mem_domain ==>
      (state.exception = NoException) /\
      state.CP0.Config.BE /\
      ~state.CP0.Status.RE /\
      ~state.exceptionSignalled /\
      (state.BranchDelay = NONE) /\
      (state.BranchTo = NONE) /\
      ((1 >< 0) state.PC = 0w: word2) /\
      aligned 2 state.PC /\
      (state.MEM state.PC = a) /\
      (state.MEM (state.PC + 1w) = b) /\
      (state.MEM (state.PC + 2w) = c) /\
      (state.MEM (state.PC + 3w) = d) /\
      state.PC + 3w IN s.mem_domain /\
      state.PC + 2w IN s.mem_domain /\
      state.PC + 1w IN s.mem_domain /\
      state.PC IN s.mem_domain`,
   rw [mips_asm_state_def, mips_ok_def, asmSemTheory.bytes_in_memory_def,
       alignmentTheory.aligned_extract, set_sepTheory.fun2set_eq]
   \\ rfs []
   \\ blastLib.FULL_BBLAST_TAC
   )

val bytes_in_memory_thm2 = Q.prove(
   `!w s state a b c d.
      mips_asm_state s state /\
      bytes_in_memory (s.pc + w) [a; b; c; d] s.mem s.mem_domain ==>
      (state.MEM (state.PC + w) = a) /\
      (state.MEM (state.PC + w + 1w) = b) /\
      (state.MEM (state.PC + w + 2w) = c) /\
      (state.MEM (state.PC + w + 3w) = d) /\
      state.PC + w + 3w IN s.mem_domain /\
      state.PC + w + 2w IN s.mem_domain /\
      state.PC + w + 1w IN s.mem_domain /\
      state.PC + w IN s.mem_domain`,
   rw [mips_asm_state_def, mips_ok_def, asmSemTheory.bytes_in_memory_def,
       set_sepTheory.fun2set_eq]
   \\ rfs []
   )

val lem1 = asmLib.v2w_BIT_n2w 5

val lem4 =
   blastLib.BBLAST_CONV ``(1 >< 0) (x: word64) = 0w: word2``
   |> Thm.EQ_IMP_RULE |> fst

val lem5 = Q.prove(
   `!n s state.
     n <> 0 /\ n <> 1 /\ n < 32 /\ mips_asm_state s state ==>
     (s.regs n = state.gpr (n2w n))`,
   lrw [mips_asm_state]
   )

val lem6 =
   blastLib.BBLAST_PROVE
     ``!c: word64.
       0xFFFFFFFFFFFF8000w <= c /\ c <= 32767w ==>
       (sw2sw
          (v2w [c ' 15; c ' 14; c ' 13; c ' 12; c ' 11;
                c ' 10; c ' 9; c ' 8; c ' 7; c ' 6; c ' 5;
                c ' 4; c ' 3; c ' 2; c ' 1; c ' 0]: word16) = c)``

val lem7 = Q.prove(
   `(!c: word64. aligned 3 c ==> ((2 >< 0) c = 0w: word3)) /\
    (!c: word64. aligned 2 c ==> ((1 >< 0) c = 0w: word2))`,
   simp [alignmentTheory.aligned_extract]
   \\ blastLib.BBLAST_TAC
   )

val lem8 =
   blastLib.BBLAST_PROVE
     ``w2w (b7: word8) ||
       w2w (b0: word8) << 56 ||
       w2w (b1: word8) << 48 ||
       w2w (b3: word8) << 32 ||
       w2w (b5: word8) << 16 ||
       w2w (b2: word8) << 40 ||
       w2w (b4: word8) << 24 ||
       w2w (b6: word8) << 8 =
       b0 @@ b1 @@ b2 @@ b3 @@ b4 @@ b5 @@ b6 @@ b7``

val lem9 =
   blastLib.BBLAST_PROVE
     ``w2w (b3: word8) ||
       w2w (b0: word8) << 24 ||
       w2w (b1: word8) << 16 ||
       w2w (b2: word8) << 8 =
       w2w (b0 @@ b1 @@ b2 @@ b3) : word64``

val lem10 =
   blastLib.BBLAST_PROVE
     ``!c: word64.
       0x0w <= c /\ c <= 65535w ==>
       (w2w
          (v2w [c ' 15; c ' 14; c ' 13; c ' 12; c ' 11;
                c ' 10; c ' 9; c ' 8; c ' 7; c ' 6; c ' 5;
                c ' 4; c ' 3; c ' 2; c ' 1; c ' 0]: word16) = c)``

val adc_lem1 = Q.prove(
  `((if b then 1w else 0w) = v2w [x] || v2w [y] : word64) = (b = x \/ y)`,
  rw [] \\ blastLib.BBLAST_TAC)

val adc_lem2 = Q.prove(
  `!r2 : word64 r3 : word64.
    (18446744073709551616 <= w2n r2 + (w2n r3 + 1) =
     18446744073709551616w <=+ w2w r2 + w2w r3 + 1w : 65 word) /\
    (18446744073709551616 <= w2n r2 + w2n r3 =
     18446744073709551616w <=+ w2w r2 + w2w r3 : 65 word)`,
   Cases
   \\ Cases
   \\ imp_res_tac wordsTheory.BITS_ZEROL_DIMINDEX
   \\ fs [wordsTheory.w2w_n2w, wordsTheory.word_add_n2w,
          wordsTheory.word_ls_n2w])

(* some rewrites ---------------------------------------------------------- *)

val encode_rwts =
   let
      open mipsTheory
   in
      [mips_enc_def, encs_def, mips_encode_def, mips_bop_r_def, mips_bop_i_def,
       mips_sh_def, mips_sh32_def, mips_memop_def, mips_cmp_def,
       Encode_def, form1_def, form2_def, form3_def, form4_def, form5_def]
   end

val enc_rwts =
  [mips_config_def] @ encode_rwts @ asmLib.asm_ok_rwts @ asmLib.asm_rwts

val enc_ok_rwts =
  [asmPropsTheory.enc_ok_def, mips_config_def] @
  encode_rwts @ asmLib.asm_ok_rwts

val dec_rwts =
   [mips_dec_def, fetch_decode_def, all_same_def, when_nop_def]

(* some custom tactics ---------------------------------------------------- *)

local
   val bool1 = utilsLib.rhsc o blastLib.BBLAST_CONV o fcpSyntax.mk_fcp_index
   fun boolify n tm =
      List.tabulate (n, fn i => bool1 (tm, numLib.term_of_int (n - 1 - i)))
   val bytes = List.concat o List.map (boolify 8)
   val v2w_n2w_rule = CONV_RULE (Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV)
   fun dec tm =
      let
         val l = listSyntax.mk_list (boolify 32 tm, Type.bool)
         val w = bitstringSyntax.mk_v2w (l, fcpSyntax.mk_int_numeric_type 32)
         val th1 = blastLib.BBLAST_PROVE (boolSyntax.mk_eq (w, tm))
      in
         l |> mips_stepLib.mips_decode
           |> Drule.DISCH_ALL
           |> v2w_n2w_rule
           |> REWRITE_RULE [th1, lem1]
      end
   val s1 = HolKernel.syntax_fns1 "mips"
   val (_, _, dest_Decode, is_Decode) = s1 "Decode"
   val (_, mk_mips_state_BranchDelay, _, _) = s1 "mips_state_BranchDelay"
   val (_, _, dest_NextStateMIPS, is_NextStateMIPS) =
      HolKernel.syntax_fns1 "mips_step" "NextStateMIPS"
   val is_mips_next = #4 (HolKernel.syntax_fns1 "mips_target" "mips_next")
   val get_BranchDelay =
      (utilsLib.rhsc o Conv.QCONV (SIMP_CONV (srw_ss()) []) o
       mk_mips_state_BranchDelay)
   val find_Decode = HolKernel.bvk_find_term (is_Decode o snd) dest_Decode
   val find_NextStateMIPS =
      dest_NextStateMIPS o List.hd o HolKernel.find_terms is_NextStateMIPS
   val ev = mips_stepLib.mips_eval true
   val s = ``s: mips_state``
   val d = ``d: word64 option``
   fun step the_state bd l =
      let
         val v = listSyntax.mk_list (bytes l, Type.bool)
         val thms = ev v
         val _ = Lib.mem (List.length thms) [1, 2] orelse
                 ( List.app print_thm thms
                 ; raise ERR "next_state_tac" "expecting one or two theorems"
                 )
         val f = if optionSyntax.is_some bd
                    then Thm.INST [d |-> Term.rand bd] o List.last
                 else List.hd
      in
         (Thm.INST [s |-> the_state] o Drule.DISCH_ALL o f) thms
      end
in
   fun decode_tac' (asl, g) =
      (case find_Decode g of
          SOME tm =>
           let
              val dec_thm = dec tm
           (* val () = (print_thm dec_thm; print "\n") *)
           in
              simp [dec_thm]
           end
        | NONE => NO_TAC) (asl, g)
   fun next_state_tac (asl, g) =
     (let
         val x as (pc, l, _, _) =
            List.last
              (List.mapPartial (Lib.total asmLib.dest_bytes_in_memory) asl)
         val x_tm = asmLib.mk_bytes_in_memory x
         val l = fst (listSyntax.dest_list l)
         val th = case Lib.total wordsSyntax.dest_word_add pc of
                     SOME (_, w) => Thm.SPEC w bytes_in_memory_thm2
                   | NONE => bytes_in_memory_thm
         val (tac, bd, the_state) =
            case Lib.total find_NextStateMIPS g of
               SOME t => (all_tac, get_BranchDelay t, t)
             | NONE =>
              (case asmLib.find_env is_mips_next g of
                  SOME (t, tm) =>
                    let
                       val etm = ``env ^t ^tm : mips_state``
                    in
                       (`!a. a IN s1.mem_domain ==> ((^etm).MEM a = ms.MEM a)`
                        by (qpat_x_assum `!i:num s:mips_state. P`
                              (qspecl_then [`^t`, `^tm`]
                                 (strip_assume_tac o SIMP_RULE (srw_ss())
                                 [set_sepTheory.fun2set_eq]))
                               \\ simp []),
                        get_BranchDelay tm, etm)
                    end
                | NONE => (all_tac, ``ms.BranchDelay``, ``ms:mips_state``))
      in
         imp_res_tac th
         \\ tac
         \\ assume_tac (step the_state bd l)
         \\ NO_STRIP_REV_FULL_SIMP_TAC (srw_ss())
              [lem1, lem6, lem7, lem10,
               combinTheory.UPDATE_APPLY, combinTheory.UPDATE_EQ]
         \\ Tactical.PAT_X_ASSUM x_tm kall_tac
         \\ SUBST1_TAC (Thm.SPEC the_state mips_next_def)
         \\ asmLib.byte_eq_tac
         \\ NO_STRIP_REV_FULL_SIMP_TAC (srw_ss()++boolSimps.LET_ss)
               [lem1, lem4, combinTheory.UPDATE_APPLY, combinTheory.UPDATE_EQ]
         \\ TRY (Q.PAT_X_ASSUM `NextStateMIPS qq = qqq` kall_tac)
      end
      handle List.Empty => FAIL_TAC "next_state_tac: empty") (asl, g)
end

fun state_tac asm =
   NO_STRIP_FULL_SIMP_TAC (srw_ss())
      [asmPropsTheory.all_pcs, mips_ok_def, mips_asm_state,
       alignmentTheory.aligned_numeric, set_sepTheory.fun2set_eq, lem8, lem9]
   \\ (if asmLib.isAddCarry asm then
         REPEAT strip_tac
         \\ Cases_on `i = n2`
         \\ simp [combinTheory.UPDATE_APPLY, adc_lem1]
         >- (Cases_on `r4 = 0w` \\ simp [adc_lem2] \\ blastLib.BBLAST_TAC)
         \\ Cases_on `i = n`
         \\ simp [combinTheory.UPDATE_APPLY, GSYM wordsTheory.word_add_n2w]
         \\ rw [bitstringLib.v2w_n2w_CONV ``v2w [F] : word64``,
                bitstringLib.v2w_n2w_CONV ``v2w [T] : word64``]
       else
         rw [combinTheory.APPLY_UPDATE_THM,
             DECIDE ``~(n < 32n) ==> (n - 32 + 32 = n)``]
         \\ (if asmLib.isMem asm then
              rw [boolTheory.FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
              \\ full_simp_tac
                   (srw_ss()++wordsLib.WORD_EXTRACT_ss++wordsLib.WORD_CANCEL_ss)
                   []
            else
              NO_STRIP_FULL_SIMP_TAC std_ss [alignmentTheory.aligned_extract]
              \\ blastLib.FULL_BBLAST_TAC))

local
   fun number_of_instructions asl =
      case asmLib.strip_bytes_in_memory (hd asl) of
         SOME l => List.length l div 4
       | NONE => raise ERR "number_of_instructions" ""
   fun has_branch tm =
      case Lib.total (fst o boolSyntax.dest_strip_comb) tm of
         SOME s => Lib.mem s ["asm$Jump", "asm$JumpCmp", "asm$JumpReg",
                              "asm$Call", "asm$Loc"]
       | NONE => false
   fun next_tac' asm gs =
      let
         val j = number_of_instructions (fst gs)
         val i = j - 1
         val n = numLib.term_of_int (if has_branch asm then i - 1 else i)
      in
         exists_tac n
         \\ simp [asmPropsTheory.asserts_eval,
                  asmPropsTheory.interference_ok_def, mips_proj_def]
         \\ NTAC 2 strip_tac
         \\ NTAC i (split_bytes_in_memory_tac 4)
         \\ NTAC j next_state_tac
         \\ REPEAT (Q.PAT_X_ASSUM `ms.MEM qq = bn` kall_tac)
         \\ REPEAT (Q.PAT_X_ASSUM `!a. a IN s1.mem_domain ==> qqq` kall_tac)
         \\ state_tac asm
      end gs
   val (_, _, dest_mips_enc, is_mips_enc) =
      HolKernel.syntax_fns1 "mips_target" "mips_enc"
   fun get_asm tm = dest_mips_enc (HolKernel.find_term is_mips_enc tm)
in
   fun next_tac gs =
     (
      qpat_x_assum `bytes_in_memory aa bb cc dd` mp_tac
      \\ simp enc_rwts
      \\ NO_STRIP_REV_FULL_SIMP_TAC (srw_ss()++boolSimps.LET_ss) enc_rwts
      \\ imp_res_tac lem5
      \\ NO_STRIP_FULL_SIMP_TAC std_ss []
      \\ strip_tac
      \\ next_tac' (get_asm (snd gs))) gs
end

val decode_tac =
   simp enc_rwts
   \\ REPEAT strip_tac
   \\ simp dec_rwts
   \\ REPEAT decode_tac'
   \\ NO_STRIP_FULL_SIMP_TAC std_ss [alignmentTheory.aligned_extract]
   \\ blastLib.FULL_BBLAST_TAC

val enc_ok_tac =
   full_simp_tac (srw_ss()++boolSimps.LET_ss)
      (asmPropsTheory.offset_monotonic_def :: enc_ok_rwts)

(* -------------------------------------------------------------------------
   mips_asm_deterministic
   mips_backend_correct
   ------------------------------------------------------------------------- *)

val print_tac = asmLib.print_tac "encode"

val mips_encoding = Count.apply Q.prove (
   `!i. asm_ok i mips_config ==>
        let l = mips_enc i in
        let n = LENGTH l in
           (!x. mips_dec (l ++ x) = i) /\ (n MOD 4 = 0) /\ n <> 0`,
   Cases
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
         \\ decode_tac
         )
      >- (
         (*--------------
             Const
           --------------*)
         print_tac "Const"
         \\ Cases_on `((63 >< 32) c = 0w: word32) /\
                      ((31 >< 16) c = 0w: word16)`
         >- decode_tac
         \\ Cases_on `((63 >< 32) c = -1w: word32) /\
                      ((31 >< 16) c = -1w: word16) /\
                      ((15 >< 0) c : word16) ' 15`
         >- decode_tac
         \\ Cases_on `((63 >< 32) c = 0w: word32) /\
                      ~((31 >< 16) c : word16) ' 15 \/
                      ((63 >< 32) c = -1w: word32) /\
                      ((31 >< 16) c : word16) ' 15`
         \\ decode_tac
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
            \\ decode_tac
            \\ Cases_on `n0 = 31`
            \\ rw []
            \\ blastLib.FULL_BBLAST_TAC
            )
         >- (
            (*--------------
                Shift
              --------------*)
            print_tac "Shift"
            \\ Cases_on `s`
            \\ Cases_on `n1 < 32`
            \\ decode_tac
            )
            (*--------------
                AddCarry
              --------------*)
            \\ print_tac "AddCarry"
            \\ decode_tac
         )
      \\ print_tac "Mem"
      \\ Cases_on `a`
      \\ Cases_on `m`
      \\ decode_tac
      )
      (*--------------
          Jump
        --------------*)
   >- (
      print_tac "Jump"
      \\ decode_tac
      )
   >- (
      (*--------------
          JumpCmp
        --------------*)
      print_tac "JumpCmp"
      \\ Cases_on `r`
      \\ Cases_on `c`
      \\ decode_tac
      )
      (*--------------
          Call
        --------------*)
   >- (
      print_tac "Call"
      \\ decode_tac
      )
   >- (
      (*--------------
          JumpReg
        --------------*)
      print_tac "JumpReg"
      \\ decode_tac
      )
      (*--------------
          Loc
        --------------*)
   \\ print_tac "Loc"
   \\ Cases_on `n = 31`
   \\ decode_tac
   )

val enc_ok_rwts =
   SIMP_RULE (bool_ss++boolSimps.LET_ss) [mips_config_def] mips_encoding ::
   enc_ok_rwts

val print_tac = asmLib.print_tac "correct"

val mips_backend_correct = Count.apply Q.store_thm ("mips_backend_correct",
   `backend_correct mips_target`,
   simp [asmPropsTheory.backend_correct_def, asmPropsTheory.target_ok_def,
         mips_target_def]
   \\ REVERSE (REPEAT conj_tac)
   >| [
      rw [asmSemTheory.asm_step_def]
      \\ simp [mips_config_def]
      \\ Cases_on `i`,
      srw_tac [] [mips_asm_state_def, mips_config_def, set_sepTheory.fun2set_eq]
      \\  `1 < i` by decide_tac
      \\ simp [],
      srw_tac [] [mips_proj_def, mips_asm_state_def, mips_ok_def],
      srw_tac [boolSimps.LET_ss] enc_ok_rwts
   ]
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
         \\ Cases_on `((63 >< 32) c = 0w: word32) /\
                      ((31 >< 16) c = 0w: word16)`
         >- next_tac
         \\ Cases_on `((63 >< 32) c = -1w: word32) /\
                      ((31 >< 16) c = -1w: word16) /\
                      ((15 >< 0) c : word16) ' 15`
         >- next_tac
         \\ Cases_on `((63 >< 32) c = 0w: word32) /\
                      ~((31 >< 16) c : word16) ' 15 \/
                      ((63 >< 32) c = -1w: word32) /\
                      ((31 >< 16) c : word16) ' 15`
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
            \\ Cases_on `n1 < 32`
            \\ next_tac
            )
            (*--------------
                AddCarry
              --------------*)
            \\ print_tac "AddCarry"
            \\ qabbrev_tac `r2 = ms.gpr (n2w n0)`
            \\ qabbrev_tac `r3 = ms.gpr (n2w n1)`
            \\ qabbrev_tac `r4 = ms.gpr (n2w n2)`
            \\ next_tac
         )
         (*--------------
             Mem
           --------------*)
         \\ print_tac "Mem"
         \\ Cases_on `a`
         \\ Cases_on `m`
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
      >| [
         Cases_on `ms.gpr (n2w n) = ms.gpr (n2w n')`,
         Cases_on `ms.gpr (n2w n) <+ ms.gpr (n2w n')`,
         Cases_on `ms.gpr (n2w n) < ms.gpr (n2w n')`,
         Cases_on `ms.gpr (n2w n) && ms.gpr (n2w n') = 0w`,
         Cases_on `ms.gpr (n2w n) <> ms.gpr (n2w n')`,
         Cases_on `~(ms.gpr (n2w n) <+ ms.gpr (n2w n'))`,
         Cases_on `~(ms.gpr (n2w n) < ms.gpr (n2w n'))`,
         Cases_on `(ms.gpr (n2w n) && ms.gpr (n2w n')) <> 0w`,
         Cases_on `ms.gpr (n2w n) = c'`,
         Cases_on `ms.gpr (n2w n) <+ c'`,
         Cases_on `ms.gpr (n2w n) < c'`,
         Cases_on `ms.gpr (n2w n) && c' = 0w`,
         Cases_on `ms.gpr (n2w n) <> c'`,
         Cases_on `~(ms.gpr (n2w n) <+ c')`,
         Cases_on `~(ms.gpr (n2w n) < c')`,
         Cases_on `(ms.gpr (n2w n) && c') <> 0w`
      ]
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
      \\ Cases_on `n = 31`
      \\ next_tac
      )
   >- (
      (*--------------
          Jump enc_ok
        --------------*)
      print_tac "enc_ok: Jump"
      \\ enc_ok_tac
      )
   >- (
      (*--------------
          JumpCmp enc_ok
        --------------*)
      print_tac "enc_ok: JumpCmp"
      \\ Cases_on `ri`
      \\ Cases_on `cmp`
      \\ enc_ok_tac
      )
   >- (
      (*--------------
          Call enc_ok
        --------------*)
      enc_ok_tac
      )
   \\ (*--------------
          Loc enc_ok
        --------------*)
      print_tac "enc_ok: Loc"
   \\ Cases_on `r = 31`
   \\ enc_ok_tac
   )

val () = export_theory ()
