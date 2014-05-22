open HolKernel Parse boolLib bossLib; val _ = new_theory "bvl_to_bvp";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open bytecodeTheory bvlTheory;
open bvl_inlineTheory bvpTheory;
open sptreeTheory;

infix \\ val op \\ = op THEN;

(*
infix THEN2
val op THEN2 = fn (x,y) => (x THEN1 y) THEN1 y;
*)

(* translation of BVL to BVP *)

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
     let (c2,v2,n2) = bComp n1 (REVERSE vs ++ env) tail [x2] in
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
     let (c1,v1,n1) = bComp n env tail [x1] in
       (Seq Tick c1, v1, n1)) /\
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

val var_corr_def = Define `
  var_corr env corr t <=>
    EVERY2 (\v x. get_var v t = SOME x) corr env`;

val bComp_LESS_EQ_lemma = prove(
  ``!n env tail xs.
      n <= SND (SND (bComp n env tail xs))``,
  HO_MATCH_MP_TAC (fetch "-" "bComp_ind") \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [bComp_def] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] [] \\ DECIDE_TAC);

val bComp_LESS_EQ = store_thm("bComp_LESS_EQ",
  ``!n env tail xs.
      (bComp n env tail xs = (c,vs,new_var)) ==> n <= new_var``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL bComp_LESS_EQ_lemma)
  \\ FULL_SIMP_TAC std_ss []);

val bComp_LENGTH_lemma = prove(
  ``!n env tail xs.
      (LENGTH (FST (SND (bComp n env tail xs))) = LENGTH xs)``,
  HO_MATCH_MP_TAC (fetch "-" "bComp_ind") \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [bComp_def] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] []);

val bComp_LENGTH = store_thm("bComp_LENGTH",
  ``!n env tail xs.
      (bComp n env tail xs = (c,vs,new_var)) ==> (LENGTH vs = LENGTH xs)``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL bComp_LENGTH_lemma)
  \\ FULL_SIMP_TAC std_ss []);

val bComp_SING_IMP = prove(
  ``(bComp n env tail [x] = (c,vs,new_var)) ==> ?t. vs = [t]``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC bComp_LENGTH
  \\ Cases_on `vs` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) []);

val bEval_SING_IMP = prove(
  ``(bEval ([x],env,s1) = (Result vs,s2)) ==> ?w. vs = [w]``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC bEval_length
  \\ Cases_on `vs` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) []);

val EL_LENGTH_APPEND = prove(
  ``!xs ys a. EL (LENGTH xs + a) (xs ++ ys) = EL a ys``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [ADD_CLAUSES]);

val LIST_REL_APPEND = prove(
  ``!xs ys xs1 ys1.
      LIST_REL P xs ys /\ LIST_REL P xs1 ys1 ==>
      LIST_REL P (xs ++ xs1) (ys ++ ys1)``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) []);

val LIST_REL_APPEND_IMP = prove(
  ``!xs ys xs1 ys1.
      LIST_REL P (xs ++ xs1) (ys ++ ys1) /\ (LENGTH xs = LENGTH ys) ==>
      LIST_REL P xs ys /\ LIST_REL P xs1 ys1``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC []);

val LIST_REL_SNOC = prove(
  ``!xs ys xs1 ys1.
      LIST_REL P (xs ++ [x]) (ys ++ [y]) <=>
      LIST_REL P xs ys /\ P x y``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC LIST_REL_LENGTH \\ FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC []);

val LIST_REL_REVERSE = prove(
  ``!xs ys. LIST_REL P (REVERSE xs) (REVERSE ys) <=> LIST_REL P xs ys``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  THEN1 (IMP_RES_TAC LIST_REL_LENGTH \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [LIST_REL_SNOC] \\ METIS_TAC []);

val IMP_IMP = METIS_PROVE [] ``b1 /\ (b2 ==> b3) ==> ((b1 ==> b2) ==> b3)``

val state_rel_def = Define `
  state_rel (s:bvl_state) (t:bvp_state) =
    (s.clock = t.clock)`;

val bComp_correct = prove(
  ``!xs env s1 res s2 t1 n corr tail.
      (bEval (xs,env,s1) = (res,s2)) /\ res <> Error /\
      var_corr env corr t1 /\ (LENGTH xs <> 1 ==> ~tail) /\
      (!k. n <= k ==> (lookup k t1.locals = NONE)) /\
      state_rel s1 t1 ==>
      ?t2 prog pres vs next_var.
        (bComp n corr tail xs = (prog,vs,next_var)) /\
        (pEval (prog,t1) = (pres,t2)) /\ state_rel s2 t2 /\
        (case pres of
         | SOME r => (res_list r = res) /\ (isResult res ==> tail)
         | NONE => ~tail /\ n <= next_var /\
                   EVERY (\v. n <= v /\ v < next_var) vs /\
                   (!k. next_var <= k ==> (lookup k t2.locals = NONE)) /\
                   var_corr env corr t2 /\
                   (!k x. (lookup k t2.locals = SOME x) ==> k < next_var) /\
                   (!k x. (lookup k t1.locals = SOME x) ==>
                          (lookup k t2.locals = SOME x)) /\
                   case res of
                   | Result xs => var_corr xs vs t2
                   | _ => F)``,
  SIMP_TAC std_ss [Once EQ_SYM_EQ]
  \\ recInduct bEval_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [bComp_def,pEval_def,bEval_def]
  THEN1 (* NIL *)
    (SRW_TAC [] [var_corr_def]
     \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss [NOT_LESS]
     \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
  THEN1 (* CONS *)
   (`?c1 v1 n1. bComp n corr F [x] = (c1,v1,n1)` by METIS_TAC [PAIR]
    \\ `?c2 vs n2. bComp n1 corr F (y::xs) = (c2,vs,n2)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,pEval_def]
    \\ Cases_on `bEval ([x],env,s)`
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`])
    \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ Cases_on `pres` \\ FULL_SIMP_TAC std_ss [isResult_def]
    \\ Cases_on `bEval (y::xs,env,r)`
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [isResult_def]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n1`,`corr`,`F`])
    \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [] \\ SRW_TAC [] []
    \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) [var_corr_def]
    \\ IMP_RES_TAC bEval_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC bComp_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC THEN1 DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM]
    THEN1 (REPEAT STRIP_TAC \\ RES_TAC \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [get_var_def])
  THEN1 (* Var *)
   (Cases_on `tail` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `n < LENGTH env`
    \\ FULL_SIMP_TAC (srw_ss()) [pEval_def]
    \\ FULL_SIMP_TAC std_ss [var_corr_def,res_list_def]
    \\ FULL_SIMP_TAC std_ss [var_corr_def,LIST_REL_def]
    \\ FULL_SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN]
    \\ FULL_SIMP_TAC (srw_ss()) [get_var_def,set_var_def,lookup_insert,res_list_def]
    \\ Q.MATCH_ASSUM_RENAME_TAC `k < LENGTH env` []
    \\ FULL_SIMP_TAC (srw_ss()) [state_rel_def,call_env_def]
    \\ REPEAT STRIP_TAC
    \\ SRW_TAC [] [] THEN1 DECIDE_TAC
    THEN1 (FIRST_X_ASSUM MATCH_MP_TAC \\ DECIDE_TAC)
    THEN1 (Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env` []
           \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `EL l corr`)
           \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `l`)
           \\ FULL_SIMP_TAC std_ss [])
    THEN1 (CCONTR_TAC \\ FULL_SIMP_TAC std_ss [NOT_LESS]
           \\ `n' < k' /\ n' <> k'` by DECIDE_TAC
           \\ FULL_SIMP_TAC (srw_ss()) []
           \\ `n' <= k'` by DECIDE_TAC
           \\ RES_TAC \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `k'`)
    \\ FULL_SIMP_TAC std_ss [])
  THEN1 (* If *)
   (`?c1 v1 n1. bComp n corr F [x1] = (c1,v1,n1)` by METIS_TAC [PAIR]
    \\ `?c2 v2 n2. bComp n1 corr tail [x2] = (c2,v2,n2)` by METIS_TAC [PAIR]
    \\ `?c3 v3 n3. bComp n2 corr tail [x3] = (c3,v3,n3)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,pEval_def]
    \\ Cases_on `tail` \\ FULL_SIMP_TAC std_ss [] THEN1
     (SIMP_TAC std_ss [pEval_def]
      \\ Cases_on `bEval ([x1],env,s)` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`])
      \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
      \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) [isResult_def]
      \\ IMP_RES_TAC bEval_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
      \\ IMP_RES_TAC bComp_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
      \\ SRW_TAC [] []
      \\ Q.MATCH_ASSUM_RENAME_TAC `var_corr [w] [n5] t2` []
      \\ `get_var n5 t2 = SOME w` by FULL_SIMP_TAC (srw_ss()) [var_corr_def]
      \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [LET_DEF]
      \\ CONV_TAC (DEPTH_CONV (DEPTH_CONV PairRules.PBETA_CONV))
      \\ IMP_RES_TAC bComp_LESS_EQ
      \\ Cases_on `w = bool_to_val T` \\ FULL_SIMP_TAC (srw_ss()) []
      THEN1
       (Q.PAT_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
        \\ FULL_SIMP_TAC std_ss []
        \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n1`,`corr`,`T`])
        \\ FULL_SIMP_TAC std_ss [])
      \\ Cases_on `w = bool_to_val F` \\ FULL_SIMP_TAC (srw_ss()) []
      THEN1
       (Q.PAT_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
        \\ FULL_SIMP_TAC std_ss []
        \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n2`,`corr`,`T`])
        \\ FULL_SIMP_TAC std_ss []
        \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
        THEN1 (REPEAT STRIP_TAC \\ FIRST_X_ASSUM MATCH_MP_TAC \\ DECIDE_TAC)
        \\ FULL_SIMP_TAC std_ss []))
    \\ SIMP_TAC std_ss [pEval_def]
    \\ Cases_on `bEval ([x1],env,s)` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`])
    \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
    \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) [isResult_def]
    \\ IMP_RES_TAC bEval_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC bComp_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SRW_TAC [] []
    \\ Q.MATCH_ASSUM_RENAME_TAC `var_corr [w] [n5] t2` []
    \\ `get_var n5 t2 = SOME w` by FULL_SIMP_TAC (srw_ss()) [var_corr_def]
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [LET_DEF]
    \\ CONV_TAC (DEPTH_CONV (DEPTH_CONV PairRules.PBETA_CONV))
    \\ IMP_RES_TAC bComp_LESS_EQ
    \\ Cases_on `w = bool_to_val T` \\ FULL_SIMP_TAC (srw_ss()) []
    THEN1
     (Q.PAT_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n1`,`corr`,`F`])
      \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
      \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ Cases_on `res` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ IMP_RES_TAC bEval_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
      \\ SRW_TAC [] []
      \\ Q.MATCH_ASSUM_RENAME_TAC `var_corr [w7] [n7] t7` []
      \\ `get_var n7 t7 = SOME w7` by FULL_SIMP_TAC (srw_ss()) [var_corr_def]
      \\ FULL_SIMP_TAC (srw_ss()) [set_var_def,state_rel_def,
           var_corr_def,get_var_def,lookup_insert]
      \\ REPEAT STRIP_TAC
      THEN1 DECIDE_TAC
      THEN1 DECIDE_TAC
      THEN1 (SRW_TAC [] [] THEN1 DECIDE_TAC
             \\ FIRST_X_ASSUM MATCH_MP_TAC \\  DECIDE_TAC)
      THEN1
       (FULL_SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN]
        \\ REPEAT STRIP_TAC
        \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env` []
        \\ `EL l corr <> n3` by ALL_TAC \\ FULL_SIMP_TAC std_ss []
        \\ `n2 <= n3 /\ l < LENGTH corr` by DECIDE_TAC
        \\ `lookup n3 t7.locals = NONE` by METIS_TAC []
        \\ RES_TAC \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss [])
      THEN1 (Cases_on `k = n3` \\ FULL_SIMP_TAC (srw_ss()) []
             \\ RES_TAC \\ DECIDE_TAC)
      THEN1 (Cases_on `k = n3` \\ FULL_SIMP_TAC (srw_ss()) []
             \\ SRW_TAC [] [] \\ `n1 <= k` by DECIDE_TAC
             \\ RES_TAC \\ FULL_SIMP_TAC std_ss []))
    \\ Cases_on `w = bool_to_val F` \\ FULL_SIMP_TAC (srw_ss()) []
    THEN1
     (Q.PAT_ASSUM `(res,s3) = bb` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n2`,`corr`,`F`])
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
        \\ FIRST_X_ASSUM MATCH_MP_TAC \\ DECIDE_TAC)
      \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ Cases_on `res` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ IMP_RES_TAC bEval_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
      \\ SRW_TAC [] []
      \\ Q.MATCH_ASSUM_RENAME_TAC `var_corr [w7] [n7] t7` []
      \\ `get_var n7 t7 = SOME w7` by FULL_SIMP_TAC (srw_ss()) [var_corr_def]
      \\ FULL_SIMP_TAC (srw_ss()) [set_var_def,state_rel_def,
           var_corr_def,get_var_def,lookup_insert]
      \\ REPEAT STRIP_TAC
      THEN1 DECIDE_TAC
      THEN1 DECIDE_TAC
      THEN1 (SRW_TAC [] [] THEN1 DECIDE_TAC
             \\ FIRST_X_ASSUM MATCH_MP_TAC \\  DECIDE_TAC)
      THEN1
       (FULL_SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN]
        \\ REPEAT STRIP_TAC
        \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env` []
        \\ `EL l corr <> n3` by ALL_TAC \\ FULL_SIMP_TAC std_ss []
        \\ `n3 <= n3 /\ l < LENGTH corr` by DECIDE_TAC
        \\ `lookup n3 t7.locals = NONE` by METIS_TAC []
        \\ RES_TAC \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss [])
      THEN1 (Cases_on `k = n3` \\ FULL_SIMP_TAC (srw_ss()) []
             \\ RES_TAC \\ DECIDE_TAC)
      THEN1 (Cases_on `k = n3` \\ FULL_SIMP_TAC (srw_ss()) []
             \\ SRW_TAC [] [] \\ `n1 <= k` by DECIDE_TAC
             \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])))
  THEN1 (* Let *)
   (`?c1 vs n1. bComp n corr F xs = (c1,vs,n1)` by METIS_TAC [PAIR]
    \\ `?c2 v2 n2. bComp n1 (REVERSE vs ++ corr) tail [x2] =
                   (c2,v2,n2)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,pEval_def]
    \\ Cases_on `bEval (xs,env,s)`
    \\ REVERSE (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`])
    \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
    \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) [isResult_def]
    \\ Q.PAT_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ `var_corr (REVERSE a ++ env) (REVERSE vs ++ corr) t2` by
     (FULL_SIMP_TAC (srw_ss()) [var_corr_def]
      \\ MATCH_MP_TAC LIST_REL_APPEND
      \\ FULL_SIMP_TAC std_ss [LIST_REL_REVERSE])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n1`,`(REVERSE vs ++ corr)`,`tail`])
    \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM]
    THEN1 (REPEAT STRIP_TAC \\ RES_TAC \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [var_corr_def]
    \\ IMP_RES_TAC LIST_REL_APPEND_IMP
    \\ IMP_RES_TAC LIST_REL_LENGTH
    \\ FULL_SIMP_TAC (srw_ss()) [])
  THEN1 (* Raise *) cheat (* missing case *)
  THEN1 (* Handle *) cheat (* missing case *)
  THEN1 (* Op *) cheat (* missing case *)
  THEN1 (* Tick *)
   (`?c1 v1 n1. bComp n corr tail [x] = (c1,v1,n1)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,pEval_def]
    \\ Cases_on `t1.clock = 0` \\ FULL_SIMP_TAC std_ss []
    THEN1 (FULL_SIMP_TAC std_ss [state_rel_def,res_list_def,isResult_def])
    \\ `s.clock <> 0` by ALL_TAC
    THEN1 (FULL_SIMP_TAC std_ss [state_rel_def,res_list_def,isResult_def])
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`dec_clock t1`,`n`,`corr`,`tail`])
    \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [var_corr_def,dec_clock_def,
         get_var_def,state_rel_def,bvlTheory.dec_clock_def])
  THEN1 (* Call *) cheat (* missing case *));

val option_case_NONE = prove(
  ``(case pres of NONE => F | SOME x => p x) <=> ?r. (pres = SOME r) /\ p r``,
  Cases_on `pres` \\ SRW_TAC [] []);

val bCompile_correct = save_thm("bCompile_correct",
  bComp_correct
  |> Q.SPECL [`[exp]`,`env`,`s1`,`res`,`s2`,`t1`,`n`,`GENLIST I n`,`T`]
  |> SIMP_RULE std_ss [LENGTH,GSYM bCompile_def,option_case_NONE,PULL_EXISTS]);

val _ = export_theory();
