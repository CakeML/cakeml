open HolKernel Parse boolLib bossLib; val _ = new_theory "bvl_to_bvi";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open bytecodeTheory bvlTheory bvl_constTheory bviTheory;
open sptreeTheory lcsymtacs;

(* compilation from BVL to BVI *)

val destLet_def = Define `
  (destLet ((Let xs b):bvl_exp) = (xs,b)) /\
  (destLet _ = ([],Var 0))`;

val bComp_def = tDefine "bComp" `
  (bComp n [] = ([],[],n)) /\
  (bComp n ((x:bvl_exp)::y::xs) =
     let (c1,aux1,n1) = bComp n [x] in
     let (c2,aux2,n2) = bComp n1 (y::xs) in
       (c1 ++ c2, aux1 ++ aux2, n2)) /\
  (bComp n [Var v] = ([(Var v):bvi_exp], [], n)) /\
  (bComp n [If x1 x2 x3] =
     let (c1,aux1,n1) = bComp n [x1] in
     let (c2,aux2,n2) = bComp n1 [x2] in
     let (c3,aux3,n3) = bComp n2 [x3] in
       ([If (HD c1) (HD c2) (HD c3)],aux1++aux2++aux3,n3)) /\
  (bComp n [Let xs x2] =
     let (c1,aux1,n1) = bComp n xs in
     let (c2,aux2,n2) = bComp n1 [x2] in
       ([Let c1 (HD c2)], aux1++aux2, n2)) /\
  (bComp n [Raise x1] =
     let (c1,aux1,n1) = bComp n [x1] in
       ([Raise (HD c1)], aux1, n1)) /\
  (bComp n [Tick x1] =
     let (c1,aux1,n1) = bComp n [x1] in
       ([Tick (HD c1)], aux1, n1)) /\
  (bComp n [Op op xs] =
     let (c1,aux1,n1) = bComp n xs in
       ([Op op c1],aux1,n1)) /\
  (bComp n [Handle x1 x2] =
     let (args,x0) = destLet x1 in
     let (c1,aux1,n1) = bComp n args in
     let (c2,aux2,n2) = bComp n1 [x0] in
     let (c3,aux3,n3) = bComp n2 [x2] in
     let aux4 = [(n3,LENGTH args,HD c1)] in
     let n4 = n3 + 1 in
       ([Call (SOME n3) c1 (SOME (HD c3))], aux1++aux2++aux3++aux4, n4)) /\
  (bComp n [Call dest xs] =
     let (c1,aux1,n1) = bComp n xs in
       ([Call dest c1 NONE],aux1,n1))`
 (WF_REL_TAC `measure (bvl_exp1_size o SND)`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
  \\ Cases_on `x1` \\ fs [destLet_def]
  \\ SRW_TAC [] [bvl_exp_size_def] \\ DECIDE_TAC);

(* verification proof *)

val bComp_LENGTH_lemma = prove(
  ``!n xs. (LENGTH (FST (bComp n xs)) = LENGTH xs)``,
  HO_MATCH_MP_TAC (fetch "-" "bComp_ind") \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [bComp_def] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] [] \\ DECIDE_TAC);

val bComp_LENGTH = prove(
  ``(bComp n xs = (ys,aux,n1)) ==> (LENGTH ys = LENGTH xs)``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL bComp_LENGTH_lemma) \\ fs [])

val aux_code_installed_def = Define `
  (aux_code_installed [] t <=> T) /\
  (aux_code_installed ((name,arg_count,body)::rest) t <=>
     (lookup (2 * name + 1) t = SOME (arg_count,body)) /\
     aux_code_installed rest t)`

val adjust_bv_def = tDefine "adjust_bv" `
  (adjust_bv b (Number i) = Number i) /\
  (adjust_bv b (RefPtr r) = RefPtr (b r)) /\
  (adjust_bv b (CodePtr c) = CodePtr (2 * c)) /\
  (adjust_bv b (Block tag vs) = Block tag (MAP (adjust_bv b) vs)) /\
  (adjust_bv b _ = Number 0)`
 (WF_REL_TAC `measure (bc_value_size o SND)`
  \\ Induct_on `vs` \\ fs [] \\ SRW_TAC [] [bc_value_size_def]
  \\ RES_TAC \\ FIRST_X_ASSUM (ASSUME_TAC o SPEC_ALL) \\ DECIDE_TAC)

(*

val bvl_bvi_corr_def = Define `
  bvl_bvi_corr (s:bvl_state) (t:bvi_state) (b:num->num) <=>
    INJ b (FDOM s.refs) (FDOM t.refs) /\
    (s.output = t.output) /\
    (s.globals = t.globals)`; (* TODO FIX THIS LINE *)

     ; refs    : num |-> ref_value
     ; code    : (num # bvl_exp # num) num_map


val inc_clock_def = Define ``

val bComp_correct = prove(
  ``!xs env s1 n res s2 t1 n2 ys aux b1.
      (bEval (xs,env,s1) = (res,s2)) /\ res <> Error /\
      (bComp n xs = (ys,aux,n2)) /\
      bvl_bvi_corr s1 t1 b1 /\
      aux_code_installed aux t1.code ==>
      ?t2 b2. (iEval (ys,MAP (adjust_bv b2) env,t1) = (res,t2)) /\
              bvl_bvi_corr s2 t2 b2``,

  SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ recInduct bEval_ind \\ REPEAT STRIP_TAC
  \\ fs [bEval_def,bComp_def,iEval_def]
  THEN1 (* NIL *)
   (Q.EXISTS_TAC `b1` \\ fs [])

  THEN1 (* CONS *)

    `?c1 aux1 n1. bComp n [x] = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ `?c2 aux2 n2. bComp n1 (y::xs) = (c2,aux2,n2)` by METIS_TAC [PAIR]
    \\ fs [LET_DEF] \\ SRW_TAC [] []

    iEval_CONS

  THEN1 (* Var *)
   (Cases_on `tail` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `n < LENGTH env`
    \\ FULL_SIMP_TAC (srw_ss()) [pEval_def]
    \\ FULL_SIMP_TAC std_ss [var_corr_def,res_list_def]
    \\ FULL_SIMP_TAC std_ss [var_corr_def,LIST_REL_def]
    \\ FULL_SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN]
    \\ FULL_SIMP_TAC (srw_ss()) [get_var_def,set_var_def,lookup_insert,res_list_def]
    \\ Q.MATCH_ASSUM_RENAME_TAC `k < LENGTH env` []
    \\ FULL_SIMP_TAC (srw_ss()) [state_rel_def,call_env_def,isException_def]
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
    \\ REPEAT STRIP_TAC \\ fs [jump_exc_NONE])
  THEN1 (* If *)
   (`?c1 v1 n1. bComp n corr F live [x1] = (c1,v1,n1)` by METIS_TAC [PAIR]
    \\ `?c2 v2 n2. bComp n1 corr tail live [x2] = (c2,v2,n2)` by METIS_TAC [PAIR]
    \\ `?c3 v3 n3. bComp n2 corr tail live [x3] = (c3,v3,n3)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,pEval_def]
    \\ Cases_on `tail` \\ FULL_SIMP_TAC std_ss [] THEN1
     (SIMP_TAC std_ss [pEval_def]
      \\ Cases_on `bEval ([x1],env,s)` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
      \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [isResult_def,isException_def]
      \\ Cases_on `pres`
      \\ FULL_SIMP_TAC (srw_ss()) [isResult_def,isException_def]
      \\ IMP_RES_TAC bEval_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
      \\ IMP_RES_TAC bComp_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
      \\ SRW_TAC [] []
      \\ Q.MATCH_ASSUM_RENAME_TAC `var_corr [w] [n5] t2` []
      \\ `get_var n5 t2 = SOME w` by FULL_SIMP_TAC (srw_ss()) [var_corr_def]
      \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [LET_DEF]
      \\ CONV_TAC (DEPTH_CONV (DEPTH_CONV PairRules.PBETA_CONV))
      \\ IMP_RES_TAC bComp_LESS_EQ
      \\ `EVERY (\n. lookup n t2.locals <> NONE) live` by
        (fs [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
         \\ Cases_on `lookup n' t1.locals` \\ fs [] \\ METIS_TAC [])
      \\ Cases_on `w = bool_to_val T` \\ FULL_SIMP_TAC (srw_ss()) []
      THEN1
       (Q.PAT_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
        \\ FULL_SIMP_TAC std_ss []
        \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n1`,`corr`,`T`,`live`])
        \\ FULL_SIMP_TAC std_ss [])
      \\ Cases_on `w = bool_to_val F` \\ FULL_SIMP_TAC (srw_ss()) []
      THEN1
       (Q.PAT_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
        \\ FULL_SIMP_TAC std_ss []
        \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n2`,`corr`,`T`,`live`])
        \\ FULL_SIMP_TAC std_ss []
        \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
        THEN1 (REPEAT STRIP_TAC \\ FIRST_X_ASSUM MATCH_MP_TAC \\ DECIDE_TAC)
        \\ FULL_SIMP_TAC std_ss []))
    \\ SIMP_TAC std_ss [pEval_def]
    \\ Cases_on `bEval ([x1],env,s)` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [isResult_def,isException_def]
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) [isResult_def,isException_def]
    \\ IMP_RES_TAC bEval_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC bComp_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SRW_TAC [] []
    \\ Q.MATCH_ASSUM_RENAME_TAC `var_corr [w] [n5] t2` []
    \\ `get_var n5 t2 = SOME w` by FULL_SIMP_TAC (srw_ss()) [var_corr_def]
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [LET_DEF]
    \\ CONV_TAC (DEPTH_CONV (DEPTH_CONV PairRules.PBETA_CONV))
    \\ IMP_RES_TAC bComp_LESS_EQ
    \\ `EVERY (\n. lookup n t2.locals <> NONE) live` by
      (fs [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
       \\ Cases_on `lookup n' t1.locals` \\ fs [] \\ METIS_TAC [])
    \\ Cases_on `w = bool_to_val T` \\ FULL_SIMP_TAC (srw_ss()) []
    THEN1
     (Q.PAT_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n1`,`corr`,`F`,`live`])
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
             \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
      \\ FULL_SIMP_TAC std_ss [jump_exc_NONE])
    \\ Cases_on `w = bool_to_val F` \\ FULL_SIMP_TAC (srw_ss()) []
    THEN1
     (Q.PAT_ASSUM `(res,s3) = bb` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n2`,`corr`,`F`,`live`])
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
             \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
      \\ FULL_SIMP_TAC std_ss [jump_exc_NONE]))
  THEN1 (* Let *)
   (`?c1 vs n1. bComp n corr F live xs = (c1,vs,n1)` by METIS_TAC [PAIR]
    \\ `?c2 v2 n2. bComp n1 (vs ++ corr) tail live [x2] =
                   (c2,v2,n2)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,pEval_def]
    \\ Cases_on `bEval (xs,env,s)`
    \\ REVERSE (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [isResult_def,isException_def]
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) [isResult_def,isException_def]
    \\ Q.PAT_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ `var_corr (a ++ env) (vs ++ corr) t2` by
     (FULL_SIMP_TAC (srw_ss()) [var_corr_def]
      \\ MATCH_MP_TAC LIST_REL_APPEND
      \\ FULL_SIMP_TAC std_ss [LIST_REL_REVERSE])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n1`,
         `vs ++ corr`,`tail`,`live`])
    \\ `EVERY (\n. lookup n t2.locals <> NONE) live` by
      (fs [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
       \\ Cases_on `lookup n' t1.locals` \\ fs [] \\ METIS_TAC [])
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
  THEN1 (* Raise *)
   (`?c1 v1 n1. bComp n corr F live [x1] = (c1,v1,n1)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,pEval_def,call_env_def]
    \\ Cases_on `bEval ([x1],env,s)` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ FULL_SIMP_TAC std_ss [isException_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [isResult_def,isException_def]
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) [isResult_def,isException_def]
    \\ IMP_RES_TAC bEval_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC bComp_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SRW_TAC [] []
    \\ `get_var t t2 = SOME w` by fs [var_corr_def]
    \\ fs [] \\ Cases_on `jump_exc t2` \\ fs [res_list_def]
    \\ FULL_SIMP_TAC std_ss [state_rel_def]
    \\ IMP_RES_TAC jump_exc_IMP \\ fs []
    \\ fs [jump_exc_def])
  THEN1 (* Handle *)
   (`?c1 v1 n1. bComp n corr F live [x1] = (c1,v1,n1)` by METIS_TAC [PAIR]
    \\ `?c2 v2 n2. bComp (n1+1) (n1::corr) F live [x2] = (c2,v2,n2)` by
          METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,pEval_def]
    \\ IMP_RES_TAC bComp_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ REVERSE (Cases_on `tail`) \\ fs [] \\ SRW_TAC [] []
    \\ Q.MATCH_ASSUM_RENAME_TAC `bComp n corr F live [x1] = (c1,[v1],n1)` []
    \\ Q.MATCH_ASSUM_RENAME_TAC
          `bComp (n1+1) (n1::corr) F live [x2] = (c2,[v2],n2)` []
    \\ FULL_SIMP_TAC std_ss [pEval_def]
    \\ Cases_on `bEval ([x1],env,s1)` \\ fs []
    \\ Cases_on `q` \\ fs [isException_def,isResult_def]
    \\ `domain (list_to_num_set (live ++ corr)) SUBSET domain t1.locals` by
     (fs [SUBSET_DEF,domain_lookup,lookup_list_to_num_set,EVERY_MEM]
      \\ REPEAT STRIP_TAC \\ RES_TAC THEN1
       (`lookup x t1.locals <> NONE` by METIS_TAC []
        \\ Cases_on `lookup x t1.locals` \\ fs [] \\ METIS_TAC [])
      \\ fs [var_corr_def,get_var_def]
      \\ IMP_RES_TAC MEM_LIST_REL \\ fs [])
    \\ fs [cut_env_def]
    \\ Q.ABBREV_TAC `env1 = mk_wf (inter t1.locals (list_to_num_set (live ++ corr)))`
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`push_exc env1 env1 t1`,
         `n`,`corr`,`F`,`live`])
    \\ `var_corr env corr (push_exc env1 env1 t1) /\
        state_rel s1 (push_exc env1 env1 t1) /\
        !k. n <= k ==> lookup k (push_exc env1 env1 t1).locals = NONE` by
         (UNABBREV_ALL_TAC
          \\ fs [var_corr_def,push_exc_def,get_var_def,state_rel_def,
                 lookup_inter_EQ,lookup_list_to_num_set]
          \\ Q.PAT_ASSUM `LIST_REL rrr xs1 xs2` MP_TAC
          \\ ONCE_REWRITE_TAC [LIST_REL_MEM] \\ fs [] \\ NO_TAC)
    \\ `EVERY (\n. lookup n (push_exc env1 env1 t1).locals <> NONE) live` by
        (UNABBREV_ALL_TAC \\ fs [EVERY_MEM,push_exc_def,
           lookup_inter_EQ,lookup_list_to_num_set] \\ NO_TAC)
    \\ fs [] \\ REPEAT STRIP_TAC \\ fs [LET_DEF,jump_exc_push_exc]
    \\ Cases_on `pres` \\ fs []
    \\ IMP_RES_TAC bEval_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ TRY (Cases_on `x`) \\ fs [res_list_def]
    THEN1 (* not tail, body of handle returns normally *)
     (POP_ASSUM (K ALL_TAC)
      \\ `get_var v1 t2 = SOME w` by fs [get_var_def,var_corr_def]
      \\ fs [get_var_def,set_var_def]
      \\ Q.PAT_ASSUM `x11 = t2.stack` (ASSUME_TAC o GSYM)
      \\ Q.PAT_ASSUM `x11 = t2.handler` (ASSUME_TAC o GSYM)
      \\ fs [pop_exc_def,push_exc_def,state_rel_def,var_corr_def,get_var_def]
      \\ fs [lookup_insert] \\ IMP_RES_TAC bComp_LESS_EQ \\ fs []
      \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC THEN1 DECIDE_TAC
      THEN1 (SRW_TAC [] [] THEN1 DECIDE_TAC
             \\ FIRST_X_ASSUM MATCH_MP_TAC \\ DECIDE_TAC)
      THEN1 (FULL_SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN]
             \\ REPEAT STRIP_TAC
             \\ Q.MATCH_ASSUM_RENAME_TAC `k < LENGTH env` []
             \\ `EL k corr <> n2` by ALL_TAC \\ fs []
             \\ `k < LENGTH corr /\ n1 <= n2` by DECIDE_TAC \\ RES_TAC
             \\ REPEAT STRIP_TAC \\ fs [])
      THEN1 (Cases_on `k = n2` \\ fs [] \\ UNABBREV_ALL_TAC
             \\ fs [lookup_inter_EQ] \\ CCONTR_TAC
             \\ `n <= k` by DECIDE_TAC \\ res_tac \\ fs [])
      THEN1 (`lookup k env1 = SOME x` by (UNABBREV_ALL_TAC
               \\ fs [lookup_inter_EQ,lookup_list_to_num_set]
               \\ CCONTR_TAC \\ fs [])
             \\ res_tac \\ SRW_TAC [] []
             \\ res_tac \\ SRW_TAC [] [] \\ `F` by DECIDE_TAC)
      \\ POP_ASSUM MP_TAC
      \\ Cases_on `jump_exc t1` \\ fs []
      \\ IMP_RES_TAC jump_exc_IMP \\ fs [jump_exc_def])
    THEN1 (* not tail, body of handle raises exception *)
     (`(t2.stack = t1.stack) /\
       (t2.handler = t1.handler) /\ (t2.locals = env1)` by
       (IMP_RES_TAC jump_exc_IMP \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
        \\ POP_ASSUM MP_TAC \\ fs [push_exc_def]
        \\ fs [jump_exc_def,push_exc_def,Q.SPEC `y::x::xs` LAST_N_LENGTH
                 |> SIMP_RULE std_ss [LENGTH,ADD1]] \\ fs [] \\ NO_TAC)
      \\ Q.PAT_ASSUM `(res,s2) = xxx` (ASSUME_TAC o GSYM) \\ fs []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`set_var n1 b t2`,`n1+1`,
           `n1::corr`,`F`,`live`])
      \\ fs [] \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (IMP_RES_TAC bComp_LESS_EQ \\ REPEAT STRIP_TAC THEN1
         (fs [var_corr_def,get_var_def,set_var_def]
          \\ FULL_SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN]
          \\ REPEAT STRIP_TAC
          \\ Q.MATCH_ASSUM_RENAME_TAC `k < LENGTH env` []
          \\ `EL k corr <> n1` by ALL_TAC \\ UNABBREV_ALL_TAC
          \\ fs [lookup_insert,lookup_inter_EQ,lookup_list_to_num_set]
          \\ `k < LENGTH corr /\ n <= n1` by DECIDE_TAC \\ RES_TAC
          \\ REPEAT STRIP_TAC \\ fs [] \\ METIS_TAC [MEM_EL])
        THEN1 (fs [set_var_def,lookup_insert]
          \\ SRW_TAC [] [] THEN1 DECIDE_TAC
          \\ `n <= k` by DECIDE_TAC
          \\ UNABBREV_ALL_TAC \\ fs [lookup_inter_EQ] \\ RES_TAC)
        \\ fs [state_rel_def,set_var_def,jump_exc_NONE,lookup_insert]
        \\ IMP_RES_TAC jump_exc_IMP_jump_exc
        \\ fs [EVERY_MEM,push_exc_def] \\ SRW_TAC [] [])
      \\ STRIP_TAC \\ fs []
      \\ REVERSE (Cases_on `pres`) \\ fs [set_var_def] THEN1 (METIS_TAC [])
      \\ Cases_on `res` \\ fs []
      \\ IMP_RES_TAC bEval_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
      \\ `get_var v2 t2' = SOME w` by fs [var_corr_def,get_var_def]
      \\ fs [lookup_insert] \\ IMP_RES_TAC bComp_LESS_EQ \\ fs []
      \\ Q.MATCH_ASSUM_RENAME_TAC `get_var v2 t3 = SOME w` []
      \\ REPEAT STRIP_TAC THEN1 (fs [state_rel_def])
      THEN1 DECIDE_TAC THEN1 DECIDE_TAC
      THEN1 (SRW_TAC [] [] THEN1 DECIDE_TAC
             \\ FIRST_X_ASSUM MATCH_MP_TAC \\ DECIDE_TAC)
      THEN1 (`var_corr env corr t3` by fs [var_corr_def]
             \\ FULL_SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN,var_corr_def]
             \\ REPEAT STRIP_TAC \\ fs [get_var_def,lookup_insert]
             \\ Q.MATCH_ASSUM_RENAME_TAC `k < LENGTH env` []
             \\ `EL k corr <> n2` by ALL_TAC \\ fs []
             \\ `k < LENGTH corr /\ n2 <= n2` by DECIDE_TAC \\ RES_TAC
             \\ REPEAT STRIP_TAC \\ fs [])
      THEN1 (Cases_on `k = n2` \\ fs [] \\ res_tac \\ DECIDE_TAC)
      THEN1 (Cases_on `n <= k` THEN1 (RES_TAC \\ fs [push_exc_def])
             \\ `k <> n2 /\ k <> n1` by DECIDE_TAC \\ fs []
             \\ FIRST_X_ASSUM MATCH_MP_TAC \\ UNABBREV_ALL_TAC
             \\ fs [lookup_inter_EQ,lookup_list_to_num_set]
             \\ CCONTR_TAC \\ fs [])
      \\ fs [var_corr_def,get_var_def]
      \\ POP_ASSUM MP_TAC
      \\ Cases_on `jump_exc t1` \\ fs []
      \\ IMP_RES_TAC jump_exc_IMP \\ fs [jump_exc_def])
    THEN1 (* tail, body of handle returns normally *)
     (POP_ASSUM (K ALL_TAC)
      \\ `get_var v1 t2 = SOME w` by fs [get_var_def,var_corr_def]
      \\ fs [get_var_def,set_var_def]
      \\ Q.PAT_ASSUM `x11 = t2.stack` (ASSUME_TAC o GSYM)
      \\ Q.PAT_ASSUM `x11 = t2.handler` (ASSUME_TAC o GSYM)
      \\ fs [pop_exc_def,push_exc_def,state_rel_def,var_corr_def,
             get_var_def,call_env_def,lookup_insert,res_list_def])
    THEN1 (* tail, body of handle raises exception *)
     (`(t2.stack = t1.stack) /\
       (t2.handler = t1.handler) /\ (t2.locals = env1)` by
       (IMP_RES_TAC jump_exc_IMP \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
        \\ POP_ASSUM MP_TAC \\ fs [push_exc_def]
        \\ fs [jump_exc_def,push_exc_def,Q.SPEC `y::x::xs` LAST_N_LENGTH
                 |> SIMP_RULE std_ss [LENGTH,ADD1]] \\ fs [] \\ NO_TAC)
      \\ Q.PAT_ASSUM `(res,s2) = xxx` (ASSUME_TAC o GSYM) \\ fs []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`set_var n1 b t2`,
           `n1+1`,`n1::corr`,`F`,`live`])
      \\ fs [] \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (IMP_RES_TAC bComp_LESS_EQ \\ REPEAT STRIP_TAC THEN1
         (fs [var_corr_def,get_var_def,set_var_def]
          \\ FULL_SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN]
          \\ REPEAT STRIP_TAC
          \\ Q.MATCH_ASSUM_RENAME_TAC `k < LENGTH env` []
          \\ `EL k corr <> n1` by ALL_TAC \\ UNABBREV_ALL_TAC
          \\ fs [lookup_insert,lookup_inter_EQ,lookup_list_to_num_set]
          \\ `k < LENGTH corr /\ n <= n1` by DECIDE_TAC \\ RES_TAC
          \\ REPEAT STRIP_TAC \\ fs [] \\ METIS_TAC [MEM_EL])
        THEN1 (fs [set_var_def,lookup_insert]
          \\ SRW_TAC [] [] THEN1 DECIDE_TAC
          \\ `n <= k` by DECIDE_TAC
          \\ UNABBREV_ALL_TAC \\ fs [lookup_inter_EQ] \\ RES_TAC)
        \\ fs [state_rel_def,set_var_def,jump_exc_NONE,lookup_insert]
        \\ IMP_RES_TAC jump_exc_IMP_jump_exc
        \\ fs [EVERY_MEM,push_exc_def] \\ SRW_TAC [] [])
      \\ STRIP_TAC \\ fs []
      \\ REVERSE (Cases_on `pres`) \\ fs [set_var_def] THEN1 (METIS_TAC [])
      \\ Cases_on `res` \\ fs []
      \\ IMP_RES_TAC bEval_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
      \\ `get_var v2 t2' = SOME w` by fs [var_corr_def,get_var_def]
      \\ fs [] \\ fs [get_var_def,isResult_def,res_list_def,call_env_def,
                      isException_def,state_rel_def]))
  THEN1 (* Op *)
   (`?c1 vs n1. bComp n corr F live xs = (c1,vs,n1)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,pEval_def]
    \\ Cases_on `bEval (xs,env,s)`
    \\ REVERSE (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [isResult_def,isException_def]
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) [isResult_def,isException_def]
    THEN1 SRW_TAC [] [pEval_def] THEN1 SRW_TAC [] [pEval_def]
    \\ Cases_on `bEvalOp op a r` \\ fs []
    \\ PairCases_on `x` \\ fs [] \\ REV_FULL_SIMP_TAC std_ss []
    \\ (fn (hs,goal) => (REVERSE (`let tail = F in ^goal` by ALL_TAC))
           (hs,goal)) THEN1
     (fs [LET_DEF] \\ REVERSE (Cases_on `tail`) THEN1 METIS_TAC []
      \\ fs [pEval_def,LET_DEF] \\ REV_FULL_SIMP_TAC std_ss []
      \\ Cases_on `pres` \\ fs [] \\ Cases_on `res` \\ fs []
      \\ fs [var_corr_def,isResult_def,isException_def,call_env_def,
             res_list_def,state_rel_def])
    \\ `domain (list_to_num_set (vs ++ live ++ corr)) SUBSET
        domain t2.locals` by
     (fs [SUBSET_DEF,domain_lookup,lookup_list_to_num_set,EVERY_MEM]
      \\ REPEAT STRIP_TAC \\ RES_TAC
      \\ fs [var_corr_def,get_var_def]
      \\ IMP_RES_TAC MEM_LIST_REL \\ fs []
      \\ `lookup x t1.locals <> NONE` by METIS_TAC []
      \\ Cases_on `lookup x t1.locals` \\ fs [] \\ METIS_TAC []) \\ fs []
    \\ Q.ABBREV_TAC `env1 = mk_wf (inter t2.locals (list_to_num_set (vs++live++corr)))`
    \\ `var_corr a vs (t2 with locals := env1)` by
     (UNABBREV_ALL_TAC
      \\ fs [var_corr_def,push_exc_def,get_var_def,state_rel_def,
             lookup_inter_EQ,lookup_list_to_num_set]
      \\ Q.PAT_ASSUM `LIST_REL rrr xs1 xs2` MP_TAC
      \\ ONCE_REWRITE_TAC [LIST_REL_MEM] \\ fs [] \\ NO_TAC)
    \\ IMP_RES_TAC get_vars_thm
    \\ `state_rel r (t2 with <|locals := env1; space := 0|>)` by
          (fs [state_rel_def] \\ NO_TAC)
    \\ fs [LET_DEF,pEval_def,bAssign_def]
    \\ Cases_on `op_space_reset op`
    \\ fs [pEval_def,cut_state_opt_def,cut_state_def,cut_env_def]
    \\ fs [pEvalOp_def,pEvalOpSpace_def]
    \\ IMP_RES_TAC bEvalOp_bvp_to_bvl \\ fs []
    \\ fs [get_var_def,set_var_def,res_list_def,isResult_def]
    \\ fs [call_env_def,bvl_to_bvp_def,isException_def]
    \\ fs [state_rel_def] \\ IMP_RES_TAC bEvalOp_code \\ fs []
    \\ IMP_RES_TAC bComp_LESS_EQ \\ fs [lookup_insert]
    THEN1
     (REPEAT STRIP_TAC THEN1 DECIDE_TAC
      THEN1 (SRW_TAC [] [] THEN1 DECIDE_TAC
         \\ UNABBREV_ALL_TAC \\ fs [lookup_inter_EQ]
         \\ `n1 <= k` by DECIDE_TAC \\ fs [])
      THEN1 (fs [LIST_REL_EL_EQN,var_corr_def,get_var_def,lookup_insert]
        \\ REPEAT STRIP_TAC
        \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env` []
        \\ `EL l corr <> n1` by ALL_TAC \\ FULL_SIMP_TAC std_ss []
        \\ `n1 <= n1 /\ l < LENGTH corr` by DECIDE_TAC
        \\ `lookup n1 t2.locals = NONE` by METIS_TAC []
        \\ RES_TAC \\ CCONTR_TAC \\ fs [] \\ UNABBREV_ALL_TAC
        \\ fs [lookup_insert,lookup_inter_EQ,lookup_list_to_num_set]
        \\ fs [] \\ METIS_TAC [MEM_EL])
      THEN1 (Cases_on `k = n1` \\ fs [] \\ UNABBREV_ALL_TAC
        \\ fs [lookup_insert,lookup_inter_EQ,lookup_list_to_num_set]
        \\ RES_TAC \\ DECIDE_TAC)
      THEN1
        (`k <> n1` by (REPEAT STRIP_TAC \\ RES_TAC \\ fs [] \\ NO_TAC)
         \\ fs [] \\ UNABBREV_ALL_TAC
         \\ fs [lookup_insert,lookup_inter_EQ,lookup_list_to_num_set]
         \\ CCONTR_TAC \\ fs [])
      THEN1 (POP_ASSUM MP_TAC \\ Cases_on `jump_exc t1` \\ fs []
         \\ IMP_RES_TAC jump_exc_IMP
         \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC \\ fs [jump_exc_def])
      \\ fs [var_corr_def,get_var_def])
    \\ Cases_on `op_space_req op = 0` \\ fs [pEval_def]
    \\ fs [pEval_def,cut_state_opt_def,cut_state_def,cut_env_def]
    \\ fs [pEvalOp_def,pEvalOpSpace_def,LET_DEF]
    \\ IMP_RES_TAC bEvalOp_bvp_to_bvl \\ fs []
    \\ fs [get_var_def,set_var_def,res_list_def,isResult_def]
    \\ fs [call_env_def,bvl_to_bvp_def,isException_def]
    \\ fs [state_rel_def] \\ IMP_RES_TAC bEvalOp_code \\ fs []
    \\ IMP_RES_TAC bComp_LESS_EQ \\ fs [lookup_insert]
    THEN1
     (REPEAT STRIP_TAC THEN1 DECIDE_TAC
      THEN1 (SRW_TAC [] [] THEN1 DECIDE_TAC
         \\ UNABBREV_ALL_TAC \\ fs [lookup_inter_EQ]
         \\ `n1 <= k` by DECIDE_TAC \\ fs [])
      THEN1 (fs [LIST_REL_EL_EQN,var_corr_def,get_var_def,lookup_insert]
        \\ REPEAT STRIP_TAC
        \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env` []
        \\ `EL l corr <> n1` by ALL_TAC \\ FULL_SIMP_TAC std_ss []
        \\ `n1 <= n1 /\ l < LENGTH corr` by DECIDE_TAC
        \\ `lookup n1 t2.locals = NONE` by METIS_TAC []
        \\ RES_TAC \\ CCONTR_TAC \\ fs [] \\ UNABBREV_ALL_TAC
        \\ fs [lookup_insert,lookup_inter_EQ,lookup_list_to_num_set]
        \\ fs [] \\ METIS_TAC [MEM_EL])
      THEN1 (Cases_on `k = n1` \\ fs [] \\ UNABBREV_ALL_TAC
        \\ fs [lookup_insert,lookup_inter_EQ,lookup_list_to_num_set]
        \\ RES_TAC \\ DECIDE_TAC)
      THEN1
        (`k <> n1` by (REPEAT STRIP_TAC \\ RES_TAC \\ fs [] \\ NO_TAC)
         \\ fs [] \\ UNABBREV_ALL_TAC
         \\ fs [lookup_insert,lookup_inter_EQ,lookup_list_to_num_set]
         \\ CCONTR_TAC \\ fs [])
      THEN1 (POP_ASSUM MP_TAC \\ Cases_on `jump_exc t1` \\ fs []
         \\ IMP_RES_TAC jump_exc_IMP
         \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC \\ fs [jump_exc_def])
      \\ fs [var_corr_def,get_var_def])
    \\ fs [get_vars_add_space,consume_space_add_space,lookup_insert]
    THEN1
     (REPEAT STRIP_TAC THEN1 DECIDE_TAC
      THEN1 (SRW_TAC [] [] THEN1 DECIDE_TAC
         \\ UNABBREV_ALL_TAC \\ fs [lookup_inter_EQ]
         \\ `n1 <= k` by DECIDE_TAC \\ fs [])
      THEN1 (fs [LIST_REL_EL_EQN,var_corr_def,get_var_def,lookup_insert]
        \\ REPEAT STRIP_TAC
        \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env` []
        \\ `EL l corr <> n1` by ALL_TAC \\ FULL_SIMP_TAC std_ss []
        \\ `n1 <= n1 /\ l < LENGTH corr` by DECIDE_TAC
        \\ `lookup n1 t2.locals = NONE` by METIS_TAC []
        \\ RES_TAC \\ CCONTR_TAC \\ fs [] \\ UNABBREV_ALL_TAC
        \\ fs [lookup_insert,lookup_inter_EQ,lookup_list_to_num_set]
        \\ fs [] \\ METIS_TAC [MEM_EL])
      THEN1 (Cases_on `k = n1` \\ fs [] \\ UNABBREV_ALL_TAC
        \\ fs [lookup_insert,lookup_inter_EQ,lookup_list_to_num_set]
        \\ RES_TAC \\ DECIDE_TAC)
      THEN1
        (`k <> n1` by (REPEAT STRIP_TAC \\ RES_TAC \\ fs [] \\ NO_TAC)
         \\ fs [] \\ UNABBREV_ALL_TAC
         \\ fs [lookup_insert,lookup_inter_EQ,lookup_list_to_num_set]
         \\ CCONTR_TAC \\ fs [])
      THEN1 (POP_ASSUM MP_TAC \\ Cases_on `jump_exc t1` \\ fs []
         \\ IMP_RES_TAC jump_exc_IMP
         \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC \\ fs [jump_exc_def])
      \\ fs [var_corr_def,get_var_def]))
  THEN1 (* Tick *)
   (`?c1 v1 n1. bComp n corr tail live [x] = (c1,v1,n1)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,pEval_def]
    \\ Cases_on `t1.clock = 0` \\ FULL_SIMP_TAC std_ss []
    THEN1 (fs [state_rel_def,res_list_def,
             isResult_def,isException_def,call_env_def])
    \\ `s.clock <> 0` by ALL_TAC
    THEN1 (FULL_SIMP_TAC std_ss [state_rel_def,res_list_def,isResult_def])
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`dec_clock t1`,`n`,`corr`,`tail`,`live`])
    \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [var_corr_def,dec_clock_def,
         get_var_def,state_rel_def,bvlTheory.dec_clock_def,jump_exc_NONE])
  THEN1 (* Call *)
   (`?c1 vs n1. bComp n corr F live xs = (c1,vs,n1)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,pEval_def,call_env_def]
    \\ Cases_on `bEval (xs,env,s1)`
    \\ REVERSE (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [isResult_def,isException_def]
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) [isResult_def,isException_def]
    \\ Cases_on `find_code dest a r.code` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss []
    \\ Q.MATCH_ASSUM_RENAME_TAC `find_code dest a r.code = SOME (args,exp)` []
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ `t2.clock = r.clock` by FULL_SIMP_TAC std_ss [state_rel_def]
    \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `r.clock = 0`
    \\ FULL_SIMP_TAC std_ss [res_list_def,isResult_def]
    THEN1 (fs [isException_def,state_rel_def])
    \\ `get_vars vs t2 = SOME a` by IMP_RES_TAC get_vars_thm
    \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC find_code_lemma
    \\ FULL_SIMP_TAC (srw_ss()) [] \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [bCompile_def,isException_def]
    \\ Q.PAT_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `tail` THEN1
     (FIRST_X_ASSUM (MP_TAC o Q.SPECL [`call_env args (dec_clock t2)`,
           `LENGTH (args:bc_value list)`,
           `GENLIST I (LENGTH (args:bc_value list))`,`T`,`[]`])
      \\ FULL_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (FULL_SIMP_TAC (srw_ss()) [state_rel_def,dec_clock_def,call_env_def,
          bvlTheory.dec_clock_def,var_corr_def,get_var_def,LIST_REL_REVERSE,
          LIST_REL_lookup_fromList,lookup_fromList_NONE,jump_exc_NONE])
      \\ STRIP_TAC \\ fs [LET_DEF]
      \\ MP_TAC (Q.SPECL [`prog`,
            `call_env args (dec_clock t2)`] pEval_pOptimise) \\ fs []
      \\ SIMP_TAC std_ss [call_env_def]
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (BasicProvers.FULL_CASE_TAC \\ fs []
        \\ REPEAT STRIP_TAC \\ fs [res_list_def])
      \\ REPEAT STRIP_TAC \\ fs []
      \\ Cases_on `pres` \\ fs [] \\ FULL_SIMP_TAC std_ss []
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC (srw_ss()) [call_env_def,dec_clock_def]
      \\ REV_FULL_SIMP_TAC (srw_ss()) [])
    \\ `domain (list_to_num_set (live ++ corr)) SUBSET domain t2.locals` by
     (fs [SUBSET_DEF,domain_lookup,lookup_list_to_num_set,EVERY_MEM]
      \\ REPEAT STRIP_TAC \\ RES_TAC THEN1
       (`lookup x t1.locals <> NONE` by METIS_TAC []
        \\ Cases_on `lookup x t1.locals` \\ fs [] \\ METIS_TAC [])
      \\ fs [var_corr_def,get_var_def]
      \\ IMP_RES_TAC MEM_LIST_REL \\ fs [])
    \\ fs [cut_env_def]
    \\ Q.ABBREV_TAC `env2 = mk_wf (inter t2.locals (list_to_num_set (live ++ corr)))`
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL
          [`call_env args (push_env env2 (dec_clock t2))`,
           `LENGTH (args:bc_value list)`,
           `GENLIST I (LENGTH (args:bc_value list))`,`T`,`[]`])
    \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (FULL_SIMP_TAC (srw_ss()) [state_rel_def,dec_clock_def,call_env_def,
          bvlTheory.dec_clock_def,var_corr_def,get_var_def,LIST_REL_REVERSE,
          LIST_REL_lookup_fromList,lookup_fromList_NONE,push_env_def]
        \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
        \\ `jump_exc t2 <> NONE` by FULL_SIMP_TAC std_ss []
        \\ Cases_on `jump_exc t2` \\ fs []
        \\ IMP_RES_TAC jump_exc_IMP
        \\ SIMP_TAC (srw_ss()) [jump_exc_def]
        \\ IMP_RES_TAC LAST_N_TL \\ fs [] \\ DECIDE_TAC)
    \\ STRIP_TAC \\ fs [LET_DEF]
    \\ MP_TAC (Q.SPECL [`prog`,`call_env args
         (push_env env2 (dec_clock t2))`] pEval_pOptimise) \\ fs []
    \\ SIMP_TAC std_ss [call_env_def]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (BasicProvers.FULL_CASE_TAC \\ fs []
      \\ REPEAT STRIP_TAC \\ fs [res_list_def])
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) [call_env_def]
    \\ FULL_SIMP_TAC std_ss []
    \\ REVERSE (Cases_on `x`) \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [res_list_def] \\ SRW_TAC [] [isResult_def]
    \\ FULL_SIMP_TAC std_ss [isResult_def,isException_def]
    THEN1
     (IMP_RES_TAC jump_exc_IMP
      \\ FULL_SIMP_TAC (srw_ss()) [call_env_def,push_env_def,dec_clock_def]
      \\ SIMP_TAC (srw_ss()) [jump_exc_def]
      \\ Cases_on `t2.handler = LENGTH t2.stack` THEN1
       (FULL_SIMP_TAC std_ss [Q.SPEC `x::xs` LAST_N_LENGTH
           |> SIMP_RULE std_ss [LENGTH,ADD1]] \\ fs [])
      \\ `t2.handler < LENGTH t2.stack` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss []
      \\ IMP_RES_TAC LAST_N_TL
      \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ `pop_env t2' = SOME (t2' with
         <| stack := t2.stack; locals := env2 |>)` by ALL_TAC THEN1
     (Q.PAT_ASSUM `xx = t2'.stack` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC (srw_ss()) [call_env_def,push_env_def,
           pop_env_def,dec_clock_def])
    \\ fs [set_var_def,state_rel_def]
    \\ IMP_RES_TAC bComp_LESS_EQ
    \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC
    THEN1
     (UNABBREV_ALL_TAC
      \\ fs [lookup_insert,lookup_inter]
      \\ SRW_TAC [] [] THEN1 DECIDE_TAC
      \\ `lookup k t2.locals = NONE` by ALL_TAC \\ fs []
      \\ FIRST_X_ASSUM MATCH_MP_TAC
      \\ DECIDE_TAC)
    THEN1
     (FULL_SIMP_TAC (srw_ss()) [var_corr_def,get_var_def,lookup_insert]
      \\ FULL_SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN]
      \\ REPEAT STRIP_TAC
      \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env` []
      \\ `EL l corr <> n1` by ALL_TAC \\ FULL_SIMP_TAC std_ss []
      \\ `n1 <= n1 /\ l < LENGTH corr` by DECIDE_TAC
      \\ `lookup n1 t1.locals = NONE` by METIS_TAC []
      \\ RES_TAC \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
      \\ UNABBREV_ALL_TAC \\ fs [lookup_inter]
      \\ POP_ASSUM MP_TAC \\ fs []
      \\ `MEM (EL l corr) corr` by METIS_TAC [MEM_EL]
      \\ fs [lookup_list_to_num_set])
    THEN1
     (FULL_SIMP_TAC (srw_ss()) [var_corr_def,get_var_def,lookup_insert]
      \\ Cases_on `k = n1` \\ FULL_SIMP_TAC std_ss []
      \\ CCONTR_TAC \\ `n1 <= k` by DECIDE_TAC
      \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
      \\ UNABBREV_ALL_TAC \\ fs [lookup_inter])
    THEN1
     (`lookup k t2.locals = SOME x` by
          (FIRST_X_ASSUM MATCH_MP_TAC \\ fs [])
      \\ UNABBREV_ALL_TAC \\ fs [lookup_inter,lookup_insert]
      \\ `lookup k (list_to_num_set (live ++ corr)) = SOME ()` by
           (fs [lookup_list_to_num_set] \\ CCONTR_TAC \\ fs [])
      \\ `k <> n1` by ALL_TAC \\ fs [] \\ CCONTR_TAC \\ fs []
      \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
    \\ REPEAT (FULL_SIMP_TAC (srw_ss()) [var_corr_def,get_var_def,lookup_insert,
                call_env_def,push_env_def,dec_clock_def]
               \\ FULL_SIMP_TAC (srw_ss()) [jump_exc_def]
               \\ REPEAT BasicProvers.FULL_CASE_TAC)));

val option_case_NONE = prove(
  ``(case pres of NONE => F | SOME x => p x) <=> ?r. (pres = SOME r) /\ p r``,
  Cases_on `pres` \\ SRW_TAC [] []);

val bCompile_lemma = bComp_correct
  |> Q.SPECL [`[exp]`,`env`,`s1`,`res`,`s2`,`t1`,`n`,`GENLIST I n`,`T`,`[]`]
  |> SIMP_RULE std_ss [LENGTH,GSYM bCompile_def,option_case_NONE,
       PULL_EXISTS,EVERY_DEF];

val bCompile_correct = store_thm("bCompile_correct",
  ``^(bCompile_lemma |> concl |> dest_imp |> fst) ==>
    ?t2 prog vs next_var r.
      pEval (bCompile n exp,t1) = (SOME r,t2) /\
      state_rel s2 t2 /\ res_list r = res``,
  REPEAT STRIP_TAC \\ MP_TAC bCompile_lemma \\ fs []
  \\ REPEAT STRIP_TAC \\ fs [bCompile_def,LET_DEF]
  \\ MP_TAC (Q.SPECL [`prog`,`t1`] pEval_pOptimise) \\ fs []
  \\ `r <> Error` by (REPEAT STRIP_TAC \\ fs [res_list_def]) \\ fs []);

*)

val _ = export_theory();
