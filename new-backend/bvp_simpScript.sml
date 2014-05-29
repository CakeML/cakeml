open HolKernel Parse boolLib bossLib; val _ = new_theory "bvp_simp";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open bytecodeTheory bvlTheory bvpTheory;
open sptreeTheory lcsymtacs;

infix \\ val op \\ = op THEN;

(* Simple clean up of BVP:

   The pSimp optimisation removes Skips and deteles some dead code
   created by Raise and Return, e.g.

     Seq (Seq Skip (Raise n)) anything_here

   translates into:

     Raise n

*)

val isSkip_def = Define `
  (isSkip Skip = T) /\
  (isSkip _ = F)`;

val pSeq_def = Define `
  pSeq c1 c2 =
    if isSkip c1 then c2 else
    if isSkip c2 then c1 else Seq c1 c2`;

val pSimp_def = Define `
  (pSimp (Return n) = (Return n,T)) /\
  (pSimp (Raise n) = (Raise n,T)) /\
  (pSimp (Seq c1 c2) =
        let (d1,r1) = pSimp c1 in
        let (d2,r2) = pSimp c2 in
          if r1 then (d1,r1) else (pSeq d1 d2,r2)) /\
  (pSimp (Handle c1 n1 n2 c2) =
     (Handle (FST (pSimp c1)) n1 n2 (FST (pSimp c2)),F)) /\
  (pSimp (If c1 n c2 c3) =
        let (d1,r1) = pSimp c1 in
        let (d2,r2) = pSimp c2 in
        let (d3,r3) = pSimp c3 in
          if r1 then (d1,r1) else
            (If d1 n d2 d3,r2 /\ r3)) /\
  (pSimp c = (c,F))`;

val isSkip_thm = prove(
  ``!c. isSkip c = (c = Skip)``,
  Cases \\ SRW_TAC [] [isSkip_def]);

val pEval_pSeq = prove(
  ``pEval (pSeq c1 c2, s) = pEval (Seq c1 c2, s)``,
  SRW_TAC [] [pSeq_def] \\ fs [isSkip_thm]
  \\ SIMP_TAC std_ss [pEval_def,LET_DEF]
  \\ Cases_on `pEval (c1,s)` \\ fs [] \\ SRW_TAC [] []);

val FST_LEMMA = prove(
  ``!foo. (foo = (x1,x2)) ==> (FST foo = x1)``,
  Cases \\ SRW_TAC [] []);

val lemma = METIS_PROVE [] ``(!x. P x /\ Q x) <=> (!x. P x) /\ (!x. Q x)``;

val pEval_pSimp = prove(
  ``(!c s. (pEval (FST (pSimp c),s) = pEval (c,s)) /\
           (SND (pSimp c) ==> (FST (pEval (c,s)) <> NONE)))``,
  HO_MATCH_MP_TAC (fetch "-" "pSimp_ind") \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [pSimp_def,pEval_def,pEval_pSeq]
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ fs []
  \\ SRW_TAC [] [pEval_pSeq,pEval_def]
  \\ fs [] \\ SRW_TAC [] [] \\ fs [pEval_pSeq,pEval_def,LET_DEF]
  \\ Cases_on `pSimp c` \\ fs []
  \\ Cases_on `pSimp c'` \\ fs []
  \\ Cases_on `pSimp c''` \\ fs [] \\ SRW_TAC [] []
  \\ Cases_on `pEval (c,s)` \\ fs []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ SRW_TAC [] [] \\ fs [lemma]
  \\ IMP_RES_TAC FST_LEMMA \\ fs []
  \\ METIS_TAC [optionTheory.NOT_SOME_NONE,FST]);

val pSimp_thm = store_thm("pSimp_thm",
  ``!c s. pEval (FST (pSimp c),s) = pEval (c,s)``,
  fs [pEval_pSimp]);

val _ = export_theory();
