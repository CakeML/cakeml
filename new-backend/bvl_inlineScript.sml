open HolKernel Parse boolLib bossLib; val _ = new_theory "bvl_inline";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open bytecodeTheory bvlTheory;

infix \\ val op \\ = op THEN;


(* A function that inlines a function body *)

val bInline_def = tDefine "bInline" `
  (bInline n code arity [] = []) /\
  (bInline n code arity (x::y::xs) =
     HD (bInline n code arity [x]) :: bInline n code arity (y::xs)) /\
  (bInline n code arity [bVar v] = [bVar v]) /\
  (bInline n code arity [bIf x1 x2 x3] =
     [bIf (HD (bInline n code arity [x1]))
          (HD (bInline n code arity [x2]))
          (HD (bInline n code arity [x3]))]) /\
  (bInline n code arity [bLet xs x2] =
     [bLet (bInline n code arity xs)
           (HD (bInline n code arity [x2]))]) /\
  (bInline n code arity [bRaise x1] =
     [bRaise (HD (bInline n code arity [x1]))]) /\
  (bInline n code arity [bHandle x1 x2] =
     [bHandle (HD (bInline n code arity [x1]))
              (HD (bInline n code arity [x2]))]) /\
  (bInline n code arity [bOp op xs] =
     [bOp op (bInline n code arity xs)]) /\
  (bInline n code arity [bTick x] =
     [bTick (HD (bInline n code arity [x]))]) /\
  (bInline n code arity [bCall dest xs] =
     let ys = bInline n code arity xs in
       if (dest = SOME n) /\ (LENGTH xs = arity)
       then [bLet ys (bTick code)]
       else [bCall dest ys])`
 (WF_REL_TAC `measure (bvl_exp1_size o SND o SND o SND)`);

(* Value length is same as expression length *)

val bEval_length_lemma = prove(
  ``!xs env s1. case bEval (xs,env,s1) of
                | (bResult vs,s2) => (LENGTH xs = LENGTH vs)
                | _ => T``,
  recInduct bEval_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [bEval_def] \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ REPEAT (BasicProvers.FULL_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ SRW_TAC [] []);

val bEval_length = store_thm("bEval_length",
  ``!xs env s1 vs s2.
       (bEval (xs,env,s1) = (bResult vs,s2)) ==> (LENGTH vs = LENGTH xs)``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL bEval_length_lemma) \\ SRW_TAC [] []);

(* Prove that the code stays unchanged *)

val bEval_code_lemma = prove(
  ``!xs env s1. (SND (bEval (xs,env,s1))).code = s1.code``,
  recInduct bEval_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [bEval_def] \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ REPEAT (BasicProvers.FULL_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ FULL_SIMP_TAC (srw_ss()) [dec_clock_def]
  \\ POP_ASSUM MP_TAC \\ SIMP_TAC std_ss [bEvalOp_def]
  \\ REPEAT (BasicProvers.FULL_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []);

val bEval_code = store_thm("bEval_code",
  ``!xs env s1 vs s2. (bEval (xs,env,s1) = (vs,s2)) ==> (s2.code = s1.code)``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL bEval_code_lemma) \\ SRW_TAC [] []);

(* length of bInline *)

val LENGTH_bInline = prove(
  ``!n code arity xs. LENGTH (bInline n code arity xs) = LENGTH xs``,
  recInduct (fetch "-" "bInline_ind") \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [Once bInline_def,LET_DEF] \\ SRW_TAC [] []);

val HD_bInline = prove(
  ``[HD (bInline n code arity [x])] = bInline n code arity [x]``,
  `LENGTH (bInline n code arity [x]) = LENGTH [x]` by
      SIMP_TAC std_ss [LENGTH_bInline]
  \\ Cases_on `bInline n code arity [x]` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,HD] \\ `F` by DECIDE_TAC);

(* function inlining preserves semantics *)

val bEval_bInline = store_thm("bEval_bInline",
  ``!n code arity xs s env.
      (FLOOKUP s.code n = SOME (loc,code,arity)) ==>
      (bEval (bInline n code arity xs,env,s) = bEval (xs,env,s))``,
  recInduct (fetch "-" "bInline_ind") \\ REVERSE (REPEAT STRIP_TAC) THEN1
   (SIMP_TAC std_ss [Once bInline_def,LET_DEF] \\ RES_TAC
    \\ REVERSE (Cases_on `(dest = SOME n) /\ (LENGTH xs = arity)`)
    \\ ASM_SIMP_TAC std_ss []
    THEN1 (ONCE_REWRITE_TAC [bEval_def] \\ FULL_SIMP_TAC std_ss [])
    \\ ONCE_REWRITE_TAC [bEval_def] \\ ASM_SIMP_TAC std_ss []
    \\ Cases_on `bEval (xs,env,s)` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
    \\ FULL_SIMP_TAC std_ss [find_code_def]
    \\ IMP_RES_TAC bEval_code
    \\ IMP_RES_TAC bEval_length
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SIMP_TAC std_ss [Once bEval_def])
  \\ SIMP_TAC std_ss [Once bInline_def,LET_DEF] \\ RES_TAC
  \\ ONCE_REWRITE_TAC [bEval_def] \\ ASM_SIMP_TAC std_ss [HD_bInline]
  \\ SRW_TAC [] []
  \\ TRY (FIRST_X_ASSUM MATCH_MP_TAC
          \\ FULL_SIMP_TAC (srw_ss()) [dec_clock_def] \\ NO_TAC)
  THEN1 (Cases_on `bEval ([x1],env,s)` \\ FULL_SIMP_TAC (srw_ss()) []
     \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
     \\ IMP_RES_TAC bEval_code \\ FULL_SIMP_TAC (srw_ss()) [])
  THEN1 (Cases_on `bEval (xs,env,s)` \\ FULL_SIMP_TAC (srw_ss()) []
     \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
     \\ IMP_RES_TAC bEval_code \\ FULL_SIMP_TAC (srw_ss()) [])
  THEN1 (Cases_on `bEval ([x1],env,s)` \\ FULL_SIMP_TAC (srw_ss()) []
     \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
     \\ IMP_RES_TAC bEval_code \\ FULL_SIMP_TAC (srw_ss()) [])
  THEN1 (Cases_on `bInline n code arity (y::xs)` THEN1
      (`LENGTH (bInline n code arity (y::xs)) = 0` by METIS_TAC [LENGTH]
       \\ FULL_SIMP_TAC std_ss [LENGTH_bInline,LENGTH] \\ `F` by DECIDE_TAC)
     \\ SIMP_TAC std_ss [Once bEval_def,HD_bInline]
     \\ POP_ASSUM (fn th => FULL_SIMP_TAC std_ss [GSYM th])
     \\ Cases_on `bEval ([x],env,s)` \\ FULL_SIMP_TAC (srw_ss()) []
     \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
     \\ IMP_RES_TAC bEval_code \\ FULL_SIMP_TAC (srw_ss()) []));


val _ = export_theory();
