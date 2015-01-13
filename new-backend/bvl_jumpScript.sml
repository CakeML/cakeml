open HolKernel Parse boolLib bossLib; val _ = new_theory "bvl_jump";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open bvlTheory lcsymtacs;

val SPLIT_LIST = prove(
  ``!xs:bvl_exp list.
      ?ys zs. (xs = ys ++ zs) /\
              (LENGTH xs DIV 2 = LENGTH ys)``,
  REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`TAKE (LENGTH xs DIV 2) xs`,`DROP (LENGTH xs DIV 2) xs`]
  \\ REPEAT STRIP_TAC \\ fs [TAKE_DROP]
  \\ MATCH_MP_TAC (GSYM LENGTH_TAKE)
  \\ fs [DIV_LE_X] \\ DECIDE_TAC);

val JumpList_def = tDefine "JumpList" `
  (JumpList n xs =
     let l = LENGTH xs in
       if l = 0 then Op (Const 0) [] else
       if l = 1 then HD xs else
         let k = l DIV 2 in
         let ys = TAKE k xs in
         let zs = DROP k xs in
           If (Op Less [Var 0; Op (Const (&(n+k))) []])
             (JumpList n ys) (JumpList (n + k) zs))`
  (WF_REL_TAC `measure (LENGTH o SND)` \\ REPEAT STRIP_TAC
   \\ STRIP_ASSUME_TAC (SPEC_ALL SPLIT_LIST) \\ FULL_SIMP_TAC std_ss []
   \\ REPEAT STRIP_TAC \\ fs [rich_listTheory.TAKE_LENGTH_APPEND,
        rich_listTheory.DROP_LENGTH_APPEND]
   \\ rfs [DIV_EQ_X] \\ DECIDE_TAC);

val JumpList_ind = theorem "JumpList_ind";

val Jump_def = Define `
  Jump x xs = Let [x] (JumpList 0 xs)`;

val bEval_JumpList = prove(
  ``!n xs k.
      k < LENGTH xs ==>
      (bEval ([JumpList n xs],Number (&(n+k))::env,s) =
       bEval ([EL k xs],Number (&(n+k))::env,s))``,
  recInduct JumpList_ind \\ REPEAT STRIP_TAC \\ fs []
  \\ SIMP_TAC std_ss [Once JumpList_def,LET_DEF]
  \\ SRW_TAC [] [] \\ fs []
  \\ fs [bEval_def,bEvalOp_def]
  \\ STRIP_ASSUME_TAC (SPEC_ALL SPLIT_LIST)
  \\ FULL_SIMP_TAC std_ss []
  \\ `(LENGTH ys = 0) ==> LENGTH zs <> 0` by (fs [] \\ DECIDE_TAC)
  \\ NTAC 2 (POP_ASSUM MP_TAC) \\ NTAC 3 (POP_ASSUM (K ALL_TAC))
  \\ REPEAT STRIP_TAC \\ fs [rich_listTheory.TAKE_LENGTH_APPEND,
       rich_listTheory.DROP_LENGTH_APPEND]
  \\ Cases_on `k < LENGTH ys` \\ fs []
  \\ fs [bytecodeTheory.bool_to_tag_def]
  \\ IMP_RES_TAC rich_listTheory.EL_APPEND1 \\ fs []
  \\ `k - LENGTH ys < LENGTH zs` by DECIDE_TAC \\ RES_TAC
  \\ `n + LENGTH ys + (k - LENGTH ys) = n + k` by DECIDE_TAC
  \\ fs [] \\ fs [NOT_LESS]
  \\ IMP_RES_TAC rich_listTheory.EL_APPEND2 \\ fs []);

val bEval_Jump = store_thm("bEval_Jump",
  ``(bEval ([x],env,s) = (Result [Number (&n)],t)) /\
    n < LENGTH xs ==>
    (bEval ([Jump x xs],env,s) =
     bEval ([EL n xs],Number (&n) :: env,t))``,
  fs [bEval_def,Jump_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC bEval_JumpList
  \\ POP_ASSUM (ASSUME_TAC o Q.SPECL [`t`,`0`]) \\ fs []);

val _ = export_theory();
