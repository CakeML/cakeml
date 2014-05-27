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

val pSimp_def = tDefine "pSimp" `
  (pSimp (Return n) = (Return n,T)) /\
  (pSimp (Raise n) = (Raise n,T)) /\
  (pSimp (Seq c1 c2) =
        let (d1,r1) = pSimp c1 in
        let (d2,r2) = pSimp c2 in
          if r1 then (d1,r1) else (pSeq d1 d2,r2)) /\
  (pSimp (Handle c1 n1 n2 c2) =
     (Handle (FST (pSimp c1)) n1 n2 (FST (pSimp c2)),F)) /\
  (pSimp (If guards c1 c2) =
        let (d1,r1) = pSimp c1 in
        let (d2,r2) = pSimp c2 in
          (If (pSimpGuards guards) d1 d2,r1 /\ r2)) /\
  (pSimp c = (c,F)) /\
  (pSimpGuards [] = []) /\
  (pSimpGuards (Prog p :: guards) = Prog (FST (pSimp p)) :: pSimpGuards guards) /\
  (pSimpGuards (Assert t1 t2 :: guards) = Assert t1 t2 :: pSimpGuards guards)`
  (WF_REL_TAC `measure (\x. case x of
                            | INL p => bvp_prog_size p
                            | INR gs => bvp_prog1_size gs)`);

val isSkip_thm = prove(
  ``!c. isSkip c = (c = Skip)``,
  Cases \\ SRW_TAC [] [isSkip_def]);

val pEval_pSeq = prove(
  ``pEval (pSeq c1 c2, s) = pEval (Seq c1 c2, s)``,
  SRW_TAC [] [pSeq_def] \\ fs [isSkip_thm]
  \\ SIMP_TAC std_ss [pEval_def,LET_DEF]
  \\ Cases_on `pEval (c1,s)` \\ fs [] \\ SRW_TAC [] []);

val pEval_guards_NONE = prove(
  ``(!s. FST (pEval (c1,s)) <> NONE) /\
    (!s. FST (pEval (c2,s)) <> NONE) ==>
    !guards s. (FST (pEval (If guards c1 c2,s)) <> NONE)``,
  STRIP_TAC \\ Induct \\ fs [pEval_def] \\ Cases
  \\ fs [pEval_def] \\ REPEAT STRIP_TAC
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ fs []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ fs []
  \\ METIS_TAC []);

val pEval_guards_REPLACE = prove(
  ``(!s. pEval (c1,s) = pEval (d1,s)) /\
    (!s. pEval (c2,s) = pEval (d2,s)) ==>
    !guards s. (pEval (If guards c1 c2,s) = pEval (If guards d1 d2,s))``,
  STRIP_TAC \\ Induct \\ fs [pEval_def] \\ Cases
  \\ SIMP_TAC std_ss [pEval_def] \\ REPEAT STRIP_TAC
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ fs []);

val FST_LEMMA = prove(
  ``!foo. (foo = (x1,x2)) ==> (FST foo = x1)``,
  Cases \\ SRW_TAC [] []);

val lemma = METIS_PROVE [] ``(!x. P x /\ Q x) <=> (!x. P x) /\ (!x. Q x)``;

val pEval_pSimp = prove(
  ``(!c s. (pEval (FST (pSimp c),s) = pEval (c,s)) /\
           (SND (pSimp c) ==> (FST (pEval (c,s)) <> NONE))) /\
    (!guards c1 c2 s. pEval (If (pSimpGuards guards) c1 c2, s) =
                      pEval (If guards c1 c2, s))``,
  HO_MATCH_MP_TAC (fetch "-" "pSimp_ind") \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [pSimp_def,pEval_def,pEval_pSeq]
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ fs []
  \\ SRW_TAC [] [pEval_pSeq,pEval_def]
  \\ fs [] \\ SRW_TAC [] [] \\ fs [pEval_pSeq,pEval_def,LET_DEF]
  \\ Cases_on `pSimp c` \\ fs []
  \\ Cases_on `pSimp c'` \\ fs [] \\ SRW_TAC [] []
  \\ Cases_on `pEval (c,s)` \\ fs []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ SRW_TAC [] [] \\ fs [lemma]
  \\ IMP_RES_TAC pEval_guards_REPLACE \\ fs []
  \\ IMP_RES_TAC FST_LEMMA
  \\ METIS_TAC [pEval_guards_NONE]);

val pSimp_thm = store_thm("pSimp_thm",
  ``!c s. pEval (FST (pSimp c),s) = pEval (c,s)``,
  fs [pEval_pSimp]);

val _ = export_theory();
