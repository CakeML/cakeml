open HolKernel Parse boolLib bossLib; val _ = new_theory "bvl_to_bvp";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open bytecodeTheory bvlTheory;
open bvl_inlineTheory bvpTheory;
open bvp_lemmasTheory bvp_simpTheory bvp_liveTheory;
open sptreeTheory lcsymtacs;

infix \\ val op \\ = op THEN;

(* compilation from BVL to BVP *)

val bAssign_def = Define `
  bAssign n1 op vs live env =
    if op_space_reset op then
      Assign n1 op vs (SOME (list_to_num_set (vs++live++env)))
    else
      let k = op_space_req op in
        if k = 0 then Assign n1 op vs NONE
          else Seq (MakeSpace k (list_to_num_set (vs++live++env)))
                   (Assign n1 op vs NONE)`;

val bComp_def = tDefine "bComp" `
  (bComp (n:num) (env:num list) tail live [] =
    (Skip,[]:num list,n)) /\
  (bComp n env tail live (x::y::xs) =
     let (c1,v1,n1) = bComp n env F live [x] in
     let (c2,vs,n2) = bComp n1 env F (HD v1::live) (y::xs) in
       (Seq c1 c2, HD v1 :: vs, n2)) /\
  (bComp n env tail live [Var v] =
     if tail
     then (Return (EL v env), [n], n+1)
     else (Move n (EL v env), [n], n+1)) /\
  (bComp n env tail live [If x1 x2 x3] =
     let (c1,v1,n1) = bComp n env F live [x1] in
     let (c2,v2,n2) = bComp n1 env tail live [x2] in
     let (c3,v3,n3) = bComp n2 env tail live [x3] in
       if tail then
         (If c1 (HD v1) c2 c3,[n3],n3+1)
       else
         (If c1 (HD v1) (Seq c2 (Move n3 (HD v2)))
                        (Seq c3 (Move n3 (HD v3))),[n3],n3+1)) /\
  (bComp n env tail live [Let xs x2] =
     let (c1,vs,n1) = bComp n env F live xs in
     let (c2,v2,n2) = bComp n1 (REVERSE vs ++ env) tail live [x2] in
       (Seq c1 c2, v2, n2)) /\
  (bComp n env tail live [Raise x1] =
     let (c1,v1,n1) = bComp n env F live [x1] in
       (Seq c1 (Raise (HD v1)), v1, n1)) /\
  (bComp n env tail live [Handle x1 x2] =
     let ns = list_to_num_set (live ++ env) in
     let (c1,v1,n1) = bComp n env F live [x1] in
     let (c2,v2,n2) = bComp (n1+1) (n1::env) F live [x2] in
     let c3 = Handle ns (Seq c1 (Move n2 (HD v1))) n2 n1
                     ns (Seq c2 (Move n2 (HD v2))) in
       (if tail then Seq c3 (Return n2) else c3, [n2], n2+1)) /\
  (bComp n env tail live [Op op xs] =
     let (c1,vs,n1) = bComp n env F live xs in
     let c2 = Seq c1 (bAssign n1 op vs live env) in
       (if tail then Seq c2 (Return n1) else c2, [n1], n1+1)) /\
  (bComp n env tail live [Tick x1] =
     let (c1,v1,n1) = bComp n env tail live [x1] in
       (Seq Tick c1, v1, n1)) /\
  (bComp n env tail live [Call dest xs] =
     let (c1,vs,n1) = bComp n env F live xs in
     let ret = (if tail then NONE
                else SOME (n1, list_to_num_set (live ++ env))) in
       (Seq c1 (Call ret dest vs), [n1], n1+1))`
 (WF_REL_TAC `measure (bvl_exp1_size o SND o SND o SND o SND)`);

val bCompile_def = Define `
  bCompile arg_count exp =
    bComp arg_count (REVERSE (GENLIST I arg_count)) T [] [exp]`;

(* verification proof *)

val res_list_def = Define `
  (res_list (Result x) = Result [x]) /\
  (res_list (Exception y) = Exception y) /\
  (res_list TimeOut = TimeOut) /\
  (res_list Error = Error)`;

val var_corr_def = Define `
  var_corr env corr t <=>
    EVERY2 (\v x. get_var v t = SOME x) corr env`;

val bComp_LESS_EQ_lemma = prove(
  ``!n env tail live xs.
      n <= SND (SND (bComp n env tail live xs))``,
  HO_MATCH_MP_TAC (fetch "-" "bComp_ind") \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [bComp_def] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] [] \\ DECIDE_TAC);

val bComp_LESS_EQ = store_thm("bComp_LESS_EQ",
  ``!n env tail live xs c vs new_var.
      (bComp n env tail live xs = (c,vs,new_var)) ==> n <= new_var``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL bComp_LESS_EQ_lemma)
  \\ FULL_SIMP_TAC std_ss []);

val bComp_LENGTH_lemma = prove(
  ``!n env tail live xs.
      (LENGTH (FST (SND (bComp n env tail live xs))) = LENGTH xs)``,
  HO_MATCH_MP_TAC (fetch "-" "bComp_ind") \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [bComp_def] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] []);

val bComp_LENGTH = store_thm("bComp_LENGTH",
  ``!n env tail live xs c vs new_var.
      (bComp n env tail live xs = (c,vs,new_var)) ==> (LENGTH vs = LENGTH xs)``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL bComp_LENGTH_lemma)
  \\ FULL_SIMP_TAC std_ss []);

val bComp_SING_IMP = prove(
  ``(bComp n env tail live [x] = (c,vs,new_var)) ==> ?t. vs = [t]``,
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

val code_rel_def = Define `
  code_rel bvl_code bvp_code <=>
    (domain bvl_code = domain bvp_code) /\
    !n (ignore:num) exp arg_count.
      (lookup n bvl_code = SOME (ignore,exp,arg_count)) ==>
      (lookup n bvp_code = SOME (ignore,FST (bCompile arg_count exp),arg_count))`;

val state_rel_def = Define `
  state_rel (s:bvl_state) (t:bvp_state) <=>
    (s.clock = t.clock) /\
    code_rel s.code t.code /\
    (s.globals = t.globals) /\
    (s.refs = t.refs) /\
    (s.output = t.output)`;

val get_vars_thm = prove(
  ``!vs a t2. var_corr a vs t2 ==> (get_vars vs t2 = SOME a)``,
  Induct \\ Cases_on `a` \\ FULL_SIMP_TAC std_ss [get_vars_def]
  \\ FULL_SIMP_TAC (srw_ss()) [var_corr_def] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss []);

val find_code_lemma = prove(
  ``state_rel r t2 /\
    (find_code dest a r.code = SOME (args,exp)) ==>
    (find_code dest a t2.code = SOME (args,FST (bCompile (LENGTH args) exp)))``,
  REVERSE (Cases_on `dest`) \\ SIMP_TAC std_ss [find_code_def]
  \\ FULL_SIMP_TAC (srw_ss()) [state_rel_def,code_rel_def]
  \\ REPEAT STRIP_TAC THEN1
   (Cases_on `lookup x r.code` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ PairCases_on `x'` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ RES_TAC \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Cases_on `LAST a` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `lookup n r.code` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ PairCases_on `x` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ RES_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ `x2 = LENGTH args` by ALL_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `?t1 t2. a = SNOC t1 t2` by METIS_TAC [SNOC_CASES]
  \\ FULL_SIMP_TAC std_ss [FRONT_SNOC,LENGTH_SNOC,ADD1]);

val LIST_REL_GENLIST_I = prove(
  ``!xs. LIST_REL P (GENLIST I (LENGTH xs)) xs =
         !n. n < LENGTH xs ==> P n (EL n xs)``,
  HO_MATCH_MP_TAC SNOC_INDUCT
  \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,GENLIST,SNOC_APPEND]
  \\ FULL_SIMP_TAC std_ss [LIST_REL_SNOC]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1
   (Cases_on `n < LENGTH xs`
    \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_APPEND1]
    \\ `n = LENGTH xs` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_APPEND2,EL,HD])
  THEN1 (`n < SUC (LENGTH xs)` by DECIDE_TAC \\ RES_TAC
    \\ POP_ASSUM MP_TAC \\ Q.PAT_ASSUM `!x.bb` (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_APPEND1])
  \\ POP_ASSUM (MP_TAC o Q.SPEC `LENGTH xs`)
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_APPEND2,EL,HD]);

val LIST_REL_lookup_fromList = prove(
  ``LIST_REL (\v x. lookup v (fromList args) = SOME x)
     (GENLIST I (LENGTH args)) args``,
  SIMP_TAC std_ss [lookup_fromList,LIST_REL_GENLIST_I]);

val lookup_fromList_NONE = prove(
  ``!k. LENGTH args <= k ==> (lookup k (fromList args) = NONE)``,
  SIMP_TAC std_ss [lookup_fromList] \\ DECIDE_TAC);

val jump_exc_NONE = prove(
  ``(jump_exc (t with locals := x) = NONE <=> jump_exc t = NONE) /\
    (jump_exc (t with clock := c) = NONE <=> jump_exc t = NONE)``,
  FULL_SIMP_TAC (srw_ss()) [jump_exc_def] \\ REPEAT STRIP_TAC
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ FULL_SIMP_TAC std_ss []);

val jump_exc_IMP = prove(
  ``(jump_exc s = SOME t) ==>
    s.handler < LENGTH s.stack /\
    ?n e xs. (LAST_N (s.handler + 1) s.stack = Exc n::Env e::xs) /\
             (t = s with <|handler := n; locals := e; stack := xs|>)``,
  SIMP_TAC std_ss [jump_exc_def]
  \\ Cases_on `LAST_N (s.handler + 1) s.stack` \\ fs [] \\ Cases_on `t'`
  \\ fs [] \\ Cases_on `h'` \\ fs [] \\ Cases_on `h` \\ fs [])

val jump_exc_push_exc = prove(
  ``jump_exc (push_exc env1 env2 t1) <> NONE``,
  fs [jump_exc_def,push_exc_def,Q.SPEC `y::x::xs` LAST_N_LENGTH
           |> SIMP_RULE std_ss [LENGTH,ADD1]] \\ fs [] \\ DECIDE_TAC);

val jump_exc_IMP_jump_exc = prove(
  ``(t2.handler = t1.handler) /\ (t2.stack = t1.stack) ==>
    jump_exc t1 <> NONE ==> jump_exc t2 <> NONE``,
  Cases_on `jump_exc t1` \\ fs [] \\ IMP_RES_TAC jump_exc_IMP
  \\ fs [jump_exc_def]);

val bvl_state_explode = prove(
  ``!s1 (s2:bvl_state).
      s1 = s2 <=>
      (s1.code = s2.code) /\
      (s1.clock = s2.clock) /\
      (s1.globals = s2.globals) /\
      (s1.output = s2.output) /\
      (s1.refs = s2.refs)``,
  Cases \\ Cases \\ fs (TypeBase.updates_of ``:bvl_state`` @
                        TypeBase.accessors_of ``:bvl_state``)
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ fs []);

val s_space_ID = prove(
  ``!s. (s with space := s.space) = s``,
  fs [bvp_state_explode]);

val get_vars_add_space = prove(
  ``!vs s x. (get_vars vs (add_space s x) = get_vars vs s) /\
             (get_vars vs (add_space s x with locals := y) = get_vars vs (s with locals := y))``,
  Induct \\ fs [get_vars_def,get_var_def,add_space_def]);

val bEvalOp_code = prove(
  ``!op s1 s2. (bEvalOp op a s1 = SOME (x0,s2)) ==> (s2.code = s1.code)``,
  Cases \\ REPEAT GEN_TAC \\ EVAL_TAC
  \\ REPEAT (BasicProvers.FULL_CASE_TAC) \\ fs []);

val bEvalOp_bvp_to_bvl = prove(
  ``(bEvalOp op a s1 = SOME (x0,s2)) /\ state_rel s1 t1 ==>
    (bEvalOp op a (bvp_to_bvl t1) = SOME (x0,s2 with code := LN))``,
  fs [bvp_to_bvl_def,state_rel_def]
  \\ Cases_on `op` \\ fs [bEvalOp_def]
  \\ REPEAT BasicProvers.CASE_TAC \\ fs []
  \\ CCONTR_TAC \\ fs [] \\ SRW_TAC [] []
  \\ fs [bvl_state_explode] \\ fs []);

val lookup_list_to_num_set = prove(
  ``!xs. lookup x (list_to_num_set xs) = if MEM x xs then SOME () else NONE``,
  Induct \\ srw_tac [] [list_to_num_set_def,lookup_def,lookup_insert] \\ fs []);

val MEM_LIST_REL = prove(
  ``!xs ys P x. LIST_REL P xs ys /\ MEM x xs ==> ?y. MEM y ys /\ P x y``,
  Induct \\ Cases_on `ys` \\ fs [] \\ REPEAT STRIP_TAC \\ fs []
  \\ RES_TAC \\ METIS_TAC []);

val LIST_REL_MEM = prove(
  ``!xs ys P. LIST_REL P xs ys <=>
              LIST_REL (\x y. MEM x xs /\ MEM y ys ==> P x y) xs ys``,
  fs [LIST_REL_EL_EQN] \\ METIS_TAC [MEM_EL]);

val consume_space_add_space = prove(
  ``consume_space k (add_space t k with locals := env1) =
    SOME (t with locals := env1)``,
  fs [consume_space_def,add_space_def,bvp_state_explode] \\ DECIDE_TAC);

val bComp_correct = prove(
  ``!xs env s1 res s2 t1 n corr tail live.
      (bEval (xs,env,s1) = (res,s2)) /\ res <> Error /\
      var_corr env corr t1 /\ (LENGTH xs <> 1 ==> ~tail) /\
      (!k. n <= k ==> (lookup k t1.locals = NONE)) /\
      state_rel s1 t1 /\ EVERY (\n. lookup n t1.locals <> NONE) live /\
      (isException res ==> jump_exc t1 <> NONE) ==>
      ?t2 prog pres vs next_var.
        (bComp n corr tail live xs = (prog,vs,next_var)) /\
        (pEval (prog,t1) = (pres,t2)) /\ state_rel s2 t2 /\
        (case pres of
         | SOME r =>
            ((res_list r = res) /\
             (isResult res ==>
                tail /\
                (t1.stack = t2.stack) /\
                (t1.handler = t2.handler)) /\
             (isException res ==>
                (jump_exc (t2 with <| stack := t1.stack;
                                      handler := t1.handler |>) = SOME t2)))
         | NONE => ~tail /\ n <= next_var /\
                   EVERY (\v. n <= v /\ v < next_var) vs /\
                   (!k. next_var <= k ==> (lookup k t2.locals = NONE)) /\
                   var_corr env corr t2 /\
                   (!k x. (lookup k t2.locals = SOME x) ==> k < next_var) /\
                   (!k x. (lookup k t1.locals = SOME x) /\
                          (~MEM k live ==> MEM k corr) ==>
                          (lookup k t2.locals = SOME x)) /\
                   (t1.stack = t2.stack) /\ (t1.handler = t2.handler) /\
                   (jump_exc t1 <> NONE ==> jump_exc t2 <> NONE) /\
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
   (`?c1 v1 n1. bComp n corr F live [x] = (c1,v1,n1)` by METIS_TAC [PAIR]
    \\ `?c2 vs n2. bComp n1 corr F (HD v1::live) (y::xs) = (c2,vs,n2)` by
          METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,pEval_def]
    \\ Cases_on `bEval ([x],env,s)`
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [isException_def]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ FULL_SIMP_TAC std_ss [isException_def] \\ REPEAT STRIP_TAC
    \\ Cases_on `pres` \\ FULL_SIMP_TAC std_ss [isResult_def]
    \\ Cases_on `bEval (y::xs,env,r)`
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [isResult_def,isException_def]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n1`,`corr`,`F`,`HD v1::live`])
    \\ Q.PAT_ASSUM `isException res ==> bbb` MP_TAC
    \\ `EVERY (\n. lookup n t2.locals <> NONE) (HD v1::live)` by
     (IMP_RES_TAC bEval_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
      \\ IMP_RES_TAC bComp_SING_IMP \\ fs [var_corr_def,get_var_def]
      \\ fs [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
      \\ Cases_on `lookup n' t1.locals` \\ fs [] \\ METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss [isException_def] \\ REPEAT STRIP_TAC
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
    \\ `?c2 v2 n2. bComp n1 (REVERSE vs ++ corr) tail live [x2] =
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
    \\ `var_corr (REVERSE a ++ env) (REVERSE vs ++ corr) t2` by
     (FULL_SIMP_TAC (srw_ss()) [var_corr_def]
      \\ MATCH_MP_TAC LIST_REL_APPEND
      \\ FULL_SIMP_TAC std_ss [LIST_REL_REVERSE])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n1`,
         `(REVERSE vs ++ corr)`,`tail`,`live`])
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
    \\ Q.ABBREV_TAC `env1 = (inter t1.locals (list_to_num_set (live ++ corr)))`
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
      THEN1 (Cases_on `k = n2` \\ fs [] \\ res_tac \\ DECIDE_TAC)
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
    \\ Q.ABBREV_TAC `env1 = inter t2.locals (list_to_num_set (vs++live++corr))`
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
           `REVERSE (GENLIST I (LENGTH (args:bc_value list)))`,`T`,`[]`])
      \\ FULL_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (FULL_SIMP_TAC (srw_ss()) [state_rel_def,dec_clock_def,call_env_def,
          bvlTheory.dec_clock_def,var_corr_def,get_var_def,LIST_REL_REVERSE,
          LIST_REL_lookup_fromList,lookup_fromList_NONE,jump_exc_NONE])
      \\ STRIP_TAC \\ Cases_on `pres` \\ fs [] \\ FULL_SIMP_TAC std_ss []
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC (srw_ss()) [call_env_def,dec_clock_def]
      \\ REV_FULL_SIMP_TAC std_ss [])
    \\ `domain (list_to_num_set (live ++ corr)) SUBSET domain t2.locals` by
     (fs [SUBSET_DEF,domain_lookup,lookup_list_to_num_set,EVERY_MEM]
      \\ REPEAT STRIP_TAC \\ RES_TAC THEN1
       (`lookup x t1.locals <> NONE` by METIS_TAC []
        \\ Cases_on `lookup x t1.locals` \\ fs [] \\ METIS_TAC [])
      \\ fs [var_corr_def,get_var_def]
      \\ IMP_RES_TAC MEM_LIST_REL \\ fs [])
    \\ fs [cut_env_def]
    \\ Q.ABBREV_TAC `env2 = (inter t2.locals (list_to_num_set (live ++ corr)))`
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL
          [`call_env args (push_env env2 (dec_clock t2))`,
           `LENGTH (args:bc_value list)`,
           `REVERSE (GENLIST I (LENGTH (args:bc_value list)))`,`T`,`[]`])
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
    \\ STRIP_TAC
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
      \\ FULL_SIMP_TAC std_ss [lookup_insert,lookup_inter]
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

val bCompile_correct = save_thm("bCompile_correct",
  bComp_correct
  |> Q.SPECL [`[exp]`,`env`,`s1`,`res`,`s2`,`t1`,`n`,
              `REVERSE (GENLIST I n)`,`T`,`[]`]
  |> SIMP_RULE std_ss [LENGTH,GSYM bCompile_def,option_case_NONE,
       PULL_EXISTS,EVERY_DEF]);

val _ = export_theory();
