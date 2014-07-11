open HolKernel Parse boolLib bossLib; val _ = new_theory "bvp_simp";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open bytecodeTheory bvlTheory bvpTheory;
open sptreeTheory lcsymtacs;

(* Simple clean up of BVP:

   The pSimp optimisation removes Skips and deteles some dead code
   created by Raise and Return, e.g.

     Seq (Seq Skip (Raise n)) anything_here

   translates into

     Raise n

   It also right-associates Seq, e.g.

     Seq (Seq x1 x2) x3 --> Seq x1 (Seq x2 x3)

*)

val isSkip_def = Define `
  (isSkip Skip = T) /\
  (isSkip _ = F)`;

val pSeq_def = Define `
  pSeq c1 c2 =
    if isSkip c2 then c1 else Seq c1 c2`;

val pSimp_def = Define `
  (pSimp Skip c = c) /\
  (pSimp (Return n) c = Return n) /\
  (pSimp (Raise n) c = Raise n) /\
  (pSimp (Seq c1 c2) c = pSimp c1 (pSimp c2 c)) /\
  (pSimp (Handle ns1 c1 n1 n2 ns2 c2) c =
     pSeq (Handle ns1 (pSimp c1 Skip) n1 n2 ns2 (pSimp c2 Skip)) c) /\
  (pSimp (If c1 n c2 c3) c =
     pSeq (If (pSimp c1 Skip) n (pSimp c2 Skip) (pSimp c3 Skip)) c) /\
  (pSimp c1 c2 = pSeq c1 c2)`;

val isSkip_thm = prove(
  ``!c. isSkip c = (c = Skip)``,
  Cases \\ SRW_TAC [] [isSkip_def]);

val pEval_Seq_Skip = prove(
  ``!c s. pEval (Seq c Skip,s) = pEval (c,s)``,
  fs [pEval_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ Cases_on `pEval (c,s)` \\ fs [] \\ SRW_TAC [] []);

val pEval_pSeq = prove(
  ``pEval (pSeq c1 c2, s) = pEval (Seq c1 c2, s)``,
  SRW_TAC [] [pSeq_def] \\ fs [isSkip_thm,pEval_Seq_Skip]);

val pEval_pSimp = prove(
  ``!c1 s c2. pEval (pSimp c1 c2,s) = pEval (Seq c1 c2,s)``,
  recInduct pEval_ind \\ REPEAT STRIP_TAC
  \\ fs [pSimp_def,pEval_def,LET_DEF,pEval_pSeq,pEval_pSeq]
  \\ Cases_on `pEval (c1,s)` \\ fs []
  \\ Cases_on `pEval (c2,r)` \\ fs []
  \\ Cases_on `pEval (c2,set_var n b r)` \\ fs []
  \\ Cases_on `pEval (g,s)` \\ fs []
  \\ REPEAT (BasicProvers.FULL_CASE_TAC \\ fs [pEval_def])
  \\ fs [EVAL ``bool_to_val F = bool_to_val T``]
  \\ CONV_TAC (DEPTH_CONV (PairRules.PBETA_CONV))
  \\ REPEAT (BasicProvers.FULL_CASE_TAC \\ fs [pEval_def]));

val pSimp_thm = store_thm("pSimp_thm",
  ``!c s. pEval (pSimp c Skip,s) = pEval (c,s)``,
  SIMP_TAC std_ss [pEval_pSimp,pEval_Seq_Skip]);

val _ = export_theory();
