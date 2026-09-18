(*
  Various ML tools used in arm8_targetProofTheory.
*)
structure arm8_targetProofLib =
struct

open HolKernel Parse boolLib bossLib
open asmLib arm8_stepLib arm8_targetTheory;

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

val _ = wordsLib.guess_lengths ()

val ERR = mk_HOL_ERR "arm8_targetProofLib";



val word_log2_7 = arm8_targetProofLemmasTheory.word_log2_7

val DecodeBitMasks_SOME = arm8_targetProofLemmasTheory.DecodeBitMasks_SOME

val ShiftValue0 = arm8_targetProofLemmasTheory.ShiftValue0

val valid_immediate_thm = arm8_targetProofLemmasTheory.valid_immediate_thm

val lem1 = arm8_targetProofLemmasTheory.lem1

val lem2 =
   blastLib.BBLAST_PROVE
   ``(!n: word1. v2w [n ' 0] = n) /\
     (!w: word6. v2w [w ' 5; w ' 4; w ' 3; w ' 2; w ' 1; w ' 0] = w)``

val lem3 = bitstringLib.v2w_n2w_CONV ``v2w [T] : word1``

val lem5 = arm8_targetProofLemmasTheory.lem5

val lem6 = bitstringLib.v2w_n2w_CONV ``v2w [T; T; T; T; T; T] : word6``

val lem7 =
   blastLib.BBLAST_PROVE
     ``!c: word64.
        0xFFFFFFFFFFFFFF00w <= c /\ c <= 0xFFFw /\ word_msb c  ==>
        (c = sw2sw ((8 >< 0) c : word9))``

val lem7b =
   blastLib.BBLAST_PROVE
     ``!c: word64.
        0xFFFFFFFFFFFFFF00w <= c /\ c <= 0xFFFw /\
        c <> w2w ((11 >< 0) c : word12) ==>
        (c = sw2sw ((8 >< 0) c : word9))``

val lem8 = arm8_targetProofLemmasTheory.lem8

val align_prove =
   Drule.EQT_ELIM o
   (SIMP_CONV std_ss [alignmentTheory.aligned_extract]
    THENC blastLib.BBLAST_CONV)

val lem9 =
   align_prove
   ``!c: word64.
       0xFFFFFFFFF8000000w <= c /\ c <= 0x7FFFFFFw /\ aligned 2 c ==>
       (c = sw2sw ((((27 >< 2) c: 26 word) @@ (0w: word2)): word28))``

val lem10 =
   align_prove
   ``!c: word64.
       0xFFFFFFFFFFF80000w <= c /\ c <= 0x7FFFFw /\ aligned 2 c ==>
       (c = sw2sw ((((20 >< 2) c: 19 word) @@ (0w: word2)): 21 word))``

val lem11 =
   align_prove
   ``!c: word64.
       0xFFFFFFFFFFF00004w <= c /\ c <= 0x100003w /\ aligned 2 c ==>
       (c + 0xFFFFFFFFFFFFFFFCw =
        sw2sw ((((20 >< 2) (c + 0xFFFFFFFFFFFFFFFCw): 19 word) @@
                (0w: word2)): 21 word))``

val lem13 = arm8_targetProofLemmasTheory.lem13

val lem14 = arm8_targetProofLemmasTheory.lem14

val lem14b = arm8_targetProofLemmasTheory.lem14b


val lem14c = arm8_targetProofLemmasTheory.lem14c

val lem16 =
   blastLib.BBLAST_PROVE
    ``!c: word64.
       0xFFFFFFFFFFFFFF00w <= c /\ c <= 0xFFFw /\ word_msb c ==>
       (sw2sw (v2w
               [c ' 8; c ' 7; c ' 6; c ' 5; c ' 4; c ' 3; c ' 2; c ' 1;
                c ' 0] : word9) = c)``

val lem16b =
   blastLib.BBLAST_PROVE
    ``!c: word64.
       0xFFFFFFFFFFFFFF00w <= c /\ c <= 0xFFFw /\
       c <> w2w ((11 >< 0) c : word12) ==>
       (sw2sw (v2w
               [c ' 8; c ' 7; c ' 6; c ' 5; c ' 4; c ' 3; c ' 2; c ' 1;
                c ' 0] : word9) = c)``

val lem16c =
   blastLib.BBLAST_PROVE
    ``!c: word64.
       (c = sw2sw ((8 >< 0) c : word9)) ==>
       (sw2sw (v2w
               [c ' 8; c ' 7; c ' 6; c ' 5; c ' 4; c ' 3; c ' 2; c ' 1;
                c ' 0] : word9) = c)``

val lem17 = arm8_targetProofLemmasTheory.lem17

val lem18 = arm8_targetProofLemmasTheory.lem18

val lem18b = arm8_targetProofLemmasTheory.lem18b

val lem20 = blastLib.BBLAST_PROVE ``a <> b ==> (a + -1w * b <> 0w: word64)``

val lem21 =
   blastLib.BBLAST_PROVE
     ``a < b: word64 ==>
       (word_msb (a + -1w * b) <=/=> (word_msb (a) <=/=> word_msb (b)) /\
       (word_msb (a + -1w * b) <=/=> word_msb (a)))``

val lem22 =
   blastLib.BBLAST_PROVE
     ``~(a < b: word64) ==>
       (word_msb (a + -1w * b) <=> (word_msb (a) <=/=> word_msb (b)) /\
       (word_msb (a + -1w * b) <=/=> word_msb (a)))``

val lem23 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
         ((0xFFFFFFFFFF000FFFw && c) = 0w) ==>
         ((-1w *
          w2w (v2w [c ' 23; c ' 22; c ' 21; c ' 20; c ' 19; c ' 18;
                    c ' 17; c ' 16; c ' 15; c ' 14; c ' 13; c ' 12] : word12))
           << 12 = -c)``

val lem24 =
   blastLib.BBLAST_PROVE ``!c: word64 n. n <> c ==> (-1w * c + n <> 0w)``

val lem25 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
         ((0xFFFFFFFFFFFFF000w && c) = 0w) ==>
         (w2w (v2w [c ' 11; c ' 10; c ' 9; c ' 8; c ' 7; c ' 6; c ' 5;
                    c ' 4; c ' 3; c ' 2; c ' 1; c ' 0] : word12) = c)``

val lem26 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
         ((0xFFFFFFFFFF000FFFw && c) = 0w) ==>
         (w2w (v2w [c ' 23; c ' 22; c ' 21; c ' 20; c ' 19; c ' 18;
                    c ' 17; c ' 16; c ' 15; c ' 14; c ' 13; c ' 12] : word12)
           << 12 = c)``

val lem27 = arm8_targetProofLemmasTheory.lem27

val lem28 = arm8_targetProofLemmasTheory.lem28
val lem29 = arm8_targetProofLemmasTheory.lem29

val lem30 = DECIDE ``!a. a < 32n /\ a <> 31 <=> a < 31``

val lem31 =
  blastLib.BBLAST_PROVE
    ``!c : word64.
       0xFFFFFFFFFFFFEF01w <= c /\
       c <> sw2sw ((8 >< 0) c : word9) /\
       word_msb c ==>
       ((0xFFFFFFFFFFFFF000w && (-1w * c + 0xFFFFFFFFFFFFFF00w)) = 0w)``

val lem32 =
  blastLib.BBLAST_PROVE
    ``!c : word64.
      0xFFFFFFFFFFFFEF01w <= c /\ c <= 0x10FEw ==>
      (v2w [c ' 11 <=>
            c ' 10 /\ c ' 9 /\ c ' 8 /\
            (c ' 7 \/ c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3 \/ c ' 2 \/
             c ' 1 \/ c ' 0);
            c ' 10 <=>
            c ' 9 /\ c ' 8 /\
            (c ' 7 \/ c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3 \/ c ' 2 \/
             c ' 1 \/ c ' 0);
            c ' 9 <=>
            c ' 8 /\
            (c ' 7 \/ c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3 \/ c ' 2 \/
             c ' 1 \/ c ' 0);
            c ' 8 <=>
            c ' 7 \/ c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3 \/ c ' 2 \/
            c ' 1 \/ c ' 0;
            c ' 7 <=>
            ~c ' 6 /\ ~c ' 5 /\ ~c ' 4 /\ ~c ' 3 /\ ~c ' 2 /\
            ~c ' 1 /\ ~c ' 0;
            c ' 6 <=>
            ~c ' 5 /\ ~c ' 4 /\ ~c ' 3 /\ ~c ' 2 /\ ~c ' 1 /\
            ~c ' 0;
            c ' 5 <=>
            ~c ' 4 /\ ~c ' 3 /\ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0;
            c ' 4 <=> ~c ' 3 /\ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0;
            c ' 3 <=> ~c ' 2 /\ ~c ' 1 /\ ~c ' 0;
            c ' 2 <=> ~c ' 1 /\ ~c ' 0; ~c ' 1 <=> c ' 0; c ' 0] : word12 =
        (11 >< 0) (-1w * c - 0x100w))``

val lem33 =
  blastLib.BBLAST_PROVE
    ``!c : word64.
      0xFFFFFFFFFFFFEF01w <= c /\
      c <> sw2sw ((8 >< 0) c : word9) /\ word_msb c ==>
      (-1w * w2w ((11 >< 0) (-1w * c + 0xFFFFFFFFFFFFFF00w) : word12) =
       c + 0x100w)``

val lem35 =
  blastLib.BBLAST_PROVE
    ``!c : word64.
       c <= 0x10FEw /\
       c <> sw2sw ((8 >< 0) c : word9) /\
       ~word_msb c ==>
       ((0xFFFFFFFFFFFFF000w && (c + 0xFFFFFFFFFFFFFF01w)) = 0w)``

val lem36 =
  blastLib.BBLAST_PROVE
    ``!c : word64.
      0xFFFFFFFFFFFFEF01w <= c /\ c <= 0x10FEw ==>
      (v2w [c ' 11 <=>
            c ' 10 \/ c ' 9 \/ c ' 8 \/
            c ' 7 /\ c ' 6 /\ c ' 5 /\ c ' 4 /\ c ' 3 /\
            c ' 2 /\ c ' 1 /\ c ' 0;
            c ' 10 <=>
            c ' 9 \/ c ' 8 \/
            c ' 7 /\ c ' 6 /\ c ' 5 /\ c ' 4 /\ c ' 3 /\
            c ' 2 /\ c ' 1 /\ c ' 0;
            c ' 9 <=>
            c ' 8 \/
            c ' 7 /\ c ' 6 /\ c ' 5 /\ c ' 4 /\ c ' 3 /\
            c ' 2 /\ c ' 1 /\ c ' 0;
            c ' 8 <=>
            c ' 7 /\ c ' 6 /\ c ' 5 /\ c ' 4 /\ c ' 3 /\
            c ' 2 /\ c ' 1 /\ c ' 0;
            c ' 7 <=>
            ~c ' 6 \/ ~c ' 5 \/ ~c ' 4 \/ ~c ' 3 \/ ~c ' 2 \/
            ~c ' 1 \/ ~c ' 0;
            c ' 6 <=>
            ~c ' 5 \/ ~c ' 4 \/ ~c ' 3 \/ ~c ' 2 \/ ~c ' 1 \/
            ~c ' 0;
            c ' 5 <=>
            ~c ' 4 \/ ~c ' 3 \/ ~c ' 2 \/ ~c ' 1 \/ ~c ' 0;
            c ' 4 <=> ~c ' 3 \/ ~c ' 2 \/ ~c ' 1 \/ ~c ' 0;
            c ' 3 <=> ~c ' 2 \/ ~c ' 1 \/ ~c ' 0;
            c ' 2 <=> ~c ' 1 \/ ~c ' 0; c ' 1 <=> ~c ' 0;
            ~c ' 0] : word12 = (11 >< 0) (c - 0xFFw))``

val lem37 =
  blastLib.BBLAST_PROVE
    ``!c : word64.
       c <= 0x10FEw /\
       c <> sw2sw ((8 >< 0) c : word9) /\
       ~word_msb c ==>
       (w2w ((11 >< 0) (c + 0xFFFFFFFFFFFFFF01w) : word12) = c - 0xFFw)``


val ConditionTest_not_overflow =
  arm8_stepTheory.ConditionTest
  |> CONJUNCTS
  |> (fn l => List.nth (l, 7))
  |> Q.INST [`c` |-> `FST (SND (add_with_carry (a, b, F)))`,
             `v` |-> `SND (SND (add_with_carry (a, b, F)))`]
  |> REWRITE_RULE [pairTheory.PAIR]


val arm8_ast = REWRITE_RULE [bop_enc_def, astTheory.shift_distinct] arm8_ast_def
val arm8_enc =
  SIMP_RULE (srw_ss()) [listTheory.LIST_BIND_def] (Q.AP_THM arm8_enc_def `x`)

val encode_rwts =
   let
      open arm8Theory
   in
      [arm8_enc, arm8_ast, arm8_load_store_ast_def, arm8_load_store_ast32_def,
       arm8_load_store_ast16_def, arm8_shv_def,
       arm8_encode_def, Encode_def,
       e_data_def, e_branch_def, e_load_store_def, e_sf_def,
       e_LoadStoreImmediate_def, EncodeLogicalOp_def, NoOperation_def,
       ShiftType2num_thm, SystemHintOp2num_thm, ShiftType2num_thm,
       asmSemTheory.is_test_def
      ]
   end

val enc_rwts =
   [arm8_config, asmPropsTheory.offset_monotonic_def, cmp_cond_def,
    valid_immediate_thm, lem3, lem7, lem7b, lem8, lem9, lem10, lem11,
    arm8_asm_ok] @
   encode_rwts @ asmLib.asm_rwts

val enc_ok_rwts =
   [asmPropsTheory.enc_ok_def, arm8_config, arm8_asm_ok] @ encode_rwts

val arm8_fs = full_simp_tac (srw_ss());
val arm8_rfs = rev_full_simp_tac (srw_ss());

val bytes_in_memory_thm = arm8_targetProofLemmasTheory.bytes_in_memory_thm

val bytes_in_memory_thm2 = arm8_targetProofLemmasTheory.bytes_in_memory_thm2

local
   fun is_reg_31 tm =
      case Lib.total ((bitstringSyntax.dest_v2w ## wordsSyntax.uint_of_word) o
                      boolSyntax.dest_eq) tm of
         SOME ((_, ty), 31) => ty = ``:5``
       | _ => false
   fun P s = Lib.mem s ["imm", "x"]
   fun gen_v thm =
      let
         val vars = Term.free_vars (Thm.concl thm)
         val l = List.filter (P o fst o Term.dest_var) vars
      in
         Thm.GENL l thm
      end
   val bool1 = utilsLib.rhsc o blastLib.BBLAST_CONV o fcpSyntax.mk_fcp_index
   fun boolify n tm =
      List.tabulate (n, fn i => bool1 (tm, numLib.term_of_int (n - 1 - i)))
   val bytes = List.concat o List.rev o List.map (boolify 8)
   fun step fltr state l =
      let
         val v = listSyntax.mk_list (bytes l, Type.bool)
      in
         case fltr (arm8_stepLib.arm8_step v) of
            [] => raise ERR "next_state_tac" "no step theorem"
          | [th] => (gen_v o Q.INST [`s` |-> state] o Drule.DISCH_ALL) th
          | thms => ( List.app print_thm thms
                    ; raise ERR "next_state_tac" "more than one step theorem"
                    )
      end
   val arm8_state_rule =
      REWRITE_RULE (utilsLib.datatype_rewrites true "arm8" ["arm8_state"])
in
   val filter_reg_31 = List.filter (not o List.exists is_reg_31 o Thm.hyp)
   val filter_vacuous =
     List.filter
       (not o utilsLib.vacuous o
        utilsLib.ALL_HYP_CONV_RULE
          (SIMP_CONV (srw_ss()++bitstringLib.v2w_n2w_ss) []))
   fun next_state_tac pick fltr q (asl, g) =
      (case List.mapPartial asmLib.strip_bytes_in_memory asl of
          [] => NO_TAC
        | l => assume_tac (step fltr q (pick l))) (asl, g)
end

val comm = ONCE_REWRITE_RULE [wordsTheory.WORD_ADD_COMM]

fun next_state_tac0 imp_res pick fltr q =
   next_state_tac pick fltr q
   \\ (if imp_res then imp_res_tac bytes_in_memory_thm else all_tac)
   \\ arm8_rfs []
   \\ arm8_fs [lem1, lem2, lem3, lem5, lem6, GSYM wordsTheory.WORD_NOT_LOWER]
   \\ asmLib.byte_eq_tac
   \\ arm8_rfs [lem13, lem16, lem16b, lem16c, lem17, lem18, lem20, lem21, lem22,
           lem23, lem24, lem25, lem26, comm lem21, comm lem22, lem29, lem32,
           lem33, lem36, lem37, lem18b,
           combinTheory.UPDATE_APPLY, ShiftValue0,
           alignmentTheory.aligned_numeric,
           arm8_stepTheory.ConditionTest, wordsTheory.ADD_WITH_CARRY_SUB,
           ConditionTest_not_overflow, wordsTheory.WORD_NOT_LOWER_EQUAL]

val next_state_tac01 = next_state_tac0 true List.last filter_reg_31 `ms`

fun next_state_tacN (w, x) fltr (asl, g) =
   let
      val (t, tm) = Option.valOf (asmLib.find_env optionSyntax.is_the g)
      val tac =
         qpat_x_assum `!i:num s:arm8_state. P`
            (qspecl_then [`^t`, `^tm`]
               (strip_assume_tac o SIMP_RULE (srw_ss())
                  [set_sepTheory.fun2set_eq]))
   in
      simp [arm8_ok_def, combinTheory.APPLY_UPDATE_THM,
            alignmentTheory.aligned_numeric]
      \\ imp_res_tac (Q.SPEC w bytes_in_memory_thm2)
      \\ sg `!a. a IN s1.mem_domain ==> ((env ^t ^tm).MEM a = ms.MEM a)`
      >| [tac, all_tac]
      \\ next_state_tac0 false (fn l => List.nth (l, x)) fltr `env ^t ^tm`
   end (asl, g)

val next_state_tac1 = next_state_tacN (`4w`, 0)

fun state_tac thms =
  arm8_fs ([asmPropsTheory.sym_target_state_rel, arm8_target_def,
       arm8_config, asmPropsTheory.all_pcs, arm8_ok_def, lem30,
       set_sepTheory.fun2set_eq] @ thms)
  \\ rewrite_tac [combinTheory.APPLY_UPDATE_THM, alignmentTheory.aligned_numeric]
  \\ arm8_fs []
  \\ rw []
  \\ arm8_rfs []

val shift_cases_tac =
   Cases_on `s`
   >| [Q.SPECL_THEN
         [`n2w ((64 - n1) MOD 64)`,
          `n2w ((64 - n1) MOD 64) + 63w`]
         STRIP_ASSUME_TAC DecodeBitMasks_SOME
       \\ qabbrev_tac `r: word6 = n2w ((64 - n1) MOD 64)`
       \\ qabbrev_tac `q = r + 63w`
       \\ `~((w2n q = 63) /\ r <> 0w)`
       by (Cases_on `r = 0w`
           \\ simp []
           \\ MATCH_MP_TAC
                (wordsLib.WORD_DECIDE ``a <> 63w ==> w2n (a: word6) <> 63``)
           \\ qunabbrev_tac `q`
           \\ blastLib.FULL_BBLAST_TAC),
       Q.SPECL_THEN [`n2w n1`, `63w`] STRIP_ASSUME_TAC DecodeBitMasks_SOME,
       Q.SPECL_THEN [`n2w n1`, `63w`] STRIP_ASSUME_TAC DecodeBitMasks_SOME,
       all_tac
   ]
   \\ qpat_x_assum `Abbrev (instr = arm8_enc xx)` assume_tac

fun cmp_case_tac q =
   Cases_on q
   >| [
        next_state_tac1 List.tl,
        next_state_tac1 (fn l => [hd l])
   ]
   \\ state_tac [alignmentTheory.aligned_numeric]
   \\ arm8_fs [alignmentTheory.aligned_extract]
   \\ blastLib.FULL_BBLAST_TAC

fun next_tac n =
   qexists_tac n
   \\ simp_tac (srw_ss()++boolSimps.CONJ_ss)
        [arm8_next_def, asmPropsTheory.asserts_eval,
         asmPropsTheory.asserts2_eval,
         asmPropsTheory.interference_ok_def, arm8_proj_def]
   \\ NTAC 2 strip_tac
   \\ Q.PAT_ABBREV_TAC `instr = arm8_enc aa`

val enc_rwts_tac =
  NO_STRIP_REV_FULL_SIMP_TAC (srw_ss()++ARITH_ss++boolSimps.LET_ss) enc_rwts
  \\ qunabbrev_tac `instr`
  \\ simp_tac (std_ss++listSimps.LIST_ss) []


end
