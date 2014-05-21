open HolKernel Parse boolLib bossLib; val _ = new_theory "bvl_to_bvp";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open bytecodeTheory bvlTheory;
open bvl_inlineTheory bvpTheory;

infix \\ val op \\ = op THEN;

(* translation of BVL to BVP *)

val index_of_def = Define `
  (index_of n [] = 0:num) /\
  (index_of n (x::xs) = if x = n then 0 else 1 + index_of n xs)`;

val bComp_def = tDefine "bComp" `
  (bComp (n:num) (env:num list) tail [] =
    (Skip,[]:num list,n)) /\
  (bComp n env tail (x::y::xs) =
     let (c1,v1,n1) = bComp n env F [x] in
     let (c2,vs,n2) = bComp n1 env F (y::xs) in
       (Seq c1 c2, HD v1 :: vs, n2)) /\
  (bComp n env tail [Var v] =
     if tail
     then (Return (EL v env), [n], n+1)
     else (Move n (EL v env), [n], n+1)) /\
  (bComp n env tail [If x1 x2 x3] =
     let (c1,v1,n1) = bComp n env F [x1] in
     let (c2,v2,n2) = bComp n1 env tail [x2] in
     let (c3,v3,n3) = bComp n2 env tail [x3] in
       if tail then
         (If [Prog c1; Assert (HD v1) T] c2 c3,[n3],n3+1)
       else
         (If [Prog c1; Assert (HD v1) T]
            (Seq c2 (Move n3 (HD v2)))
            (Seq c3 (Move n3 (HD v3))),
          [n3],n3+1)) /\
  (bComp n env tail [Let xs x2] =
     let (c1,vs,n1) = bComp n env F xs in
     let (c2,v2,n2) = bComp n1 vs tail [x2] in
       (Seq c1 c2, v2, n2)) /\
  (bComp n env tail [Raise x1] =
     let (c1,v1,n1) = bComp n env F [x1] in
       (Seq c1 (Raise (HD v1)), v1, n1)) /\
  (bComp n env tail [Handle x1 x2] =
     let (c1,v1,n1) = bComp n env F [x1] in
     let (c2,v2,n2) = bComp (n1+1) env F [x2] in
     let c3 = Handle (Seq c1 (Move n2 (HD v1))) n2 n1
                     (Seq c2 (Move n2 (HD v2))) in
       (if tail then Seq c3 (Return n2) else c3, [n2], n2+1)) /\
  (bComp n env tail [Op op xs] =
     let (c1,vs,n1) = bComp n env F xs in
     let c2 = Seq c1 (Assign n1 op vs) in
       (if tail then Seq c2 (Return n1) else c2, [n1], n1+1)) /\
  (bComp n env tail [Tick x1] =
     let (c1,v1,n1) = bComp n env F [x1] in
     let c2 = Seq Tick c1 in
       (if tail then Seq c2 (Return n1) else c2, v1, n1)) /\
  (bComp n env tail [Call dest xs] =
     let (c1,vs,n1) = bComp n env F xs in
     let ret = (if tail then NONE else SOME n1) in
       (Seq c1 (Call ret dest vs), [n1], n+1))`
 (WF_REL_TAC `measure (bvl_exp1_size o SND o SND o SND)`);

val bCompile_def = Define `
  bCompile arg_count exp =
    bComp arg_count (GENLIST I arg_count) T [exp]`;

val res_list_def = Define `
  (res_list (Result x) = Result [x]) /\
  (res_list (Exception y) = Exception y) /\
  (res_list TimeOut = TimeOut) /\
  (res_list Error = Error)`;

val vars_match_def = Define `
  vars_match vs t xs =
    EVERY2 (\v x. get_var v t = SOME x) vs xs`;

val var_corr_def = Define `
  var_corr env corr t <=>
    (LENGTH corr = LENGTH env) /\
    !k. k < LENGTH env ==>
        (get_var (EL k corr) t = SOME (EL k env))`;

val bComp_correct = prove(
  ``!xs env s1 res s2 t1 n corr tail.
      (bEval (xs,env,s1) = (res,s2)) /\ res <> Error /\
      var_corr env corr t1 /\ (LENGTH xs <> 1 ==> ~tail) ==>
      ?t2 prog pres vs next_var.
        (bComp n corr tail xs = (prog,vs,next_var)) /\
        (pEval (prog,t1) = (pres,t2)) /\
        (case pres of
         | SOME r => (res_list r = res) /\ (isResult res ==> tail)
         | NONE => ~tail /\ case res of
                            | Result xs => vars_match vs t2 xs
                            | _ => F)``,
  ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ recInduct bEval_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [bComp_def,pEval_def,bEval_def]
  THEN1 (* NIL *)
    (SRW_TAC [] [vars_match_def])
  THEN1 (* CONS *)
   (`?c1 v1 n1. bComp n corr F [x] = (c1,v1,n1)` by METIS_TAC [PAIR]
    \\ `?c2 vs n2. bComp n1 corr F (y::xs) = (c2,vs,n2)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,pEval_def]
    \\ Cases_on `bEval ([x],env,s)`
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
     (FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`])
      \\ FULL_SIMP_TAC std_ss []
      \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ REPEAT STRIP_TAC
      \\ Cases_on `pres` \\ FULL_SIMP_TAC std_ss [isResult_def]
      \\ Cases_on `bEval (y::xs,env,r)`
      \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [isResult_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n1`,`corr`,`F`])
      \\ `var_corr env corr t2` by cheat (* needs stronger ind hyp *)
      \\ FULL_SIMP_TAC std_ss []
      \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC std_ss []
      \\ cheat (* easy *))
    \\ RES_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`F`,`n`])
    \\ ASM_REWRITE_TAC [] \\ SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ REPEAT STRIP_TAC
    \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) [])
  THEN1 (* Var *)
   (Cases_on `tail` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `n < LENGTH env`
    \\ FULL_SIMP_TAC (srw_ss()) [pEval_def]
    \\ FULL_SIMP_TAC std_ss [var_corr_def,res_list_def]
    \\ FULL_SIMP_TAC std_ss [vars_match_def,LIST_REL_def]
    \\ FULL_SIMP_TAC (srw_ss()) [get_var_def,set_var_def])
  THEN1 (* If *) cheat (* missing case *)
  THEN1 (* Let *) cheat (* missing case *)
  THEN1 (* Raise *) cheat (* missing case *)
  THEN1 (* Handle *) cheat (* missing case *)
  THEN1 (* Op *) cheat (* missing case *)
  THEN1 (* Tick *) cheat (* missing case *)
  THEN1 (* Call *) cheat (* missing case *));

val _ = export_theory();
