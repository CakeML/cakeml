open preamble bvl_handleTheory bvlSemTheory bvlPropsTheory;

val _ = new_theory"bvl_handleProof";

val evaluate_GENLIST =
  evaluate_genlist_vars
  |> Q.SPECL[`0`,`env ++ ys`,`LENGTH (env:bvlSem$v list)`,`s`]
  |> SIMP_RULE(srw_ss()++ETA_ss)[TAKE_APPEND1];

val compile_correct = Q.prove(
  `!xs env s1 res s2 ys.
     (evaluate (xs,env,s1) = (res,s2)) /\ res <> Rerr(Rabort Rtype_error) ==>
     (evaluate (compile (LENGTH env) xs,env ++ ys,s1) = (res,s2))`,
  SIMP_TAC std_ss [Once EQ_SYM_EQ]
  \\ recInduct evaluate_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [compile_def,evaluate_def,compile_HD_SING]
  THEN1 (* Cons *)
   (ONCE_REWRITE_TAC [GSYM compile_HD_SING] \\ fs []
    \\ SIMP_TAC std_ss [Once evaluate_CONS]
    \\ fs [compile_HD_SING]
    \\ Cases_on `evaluate ([x],env,s)` \\ Cases_on `q` \\ fs []
    \\ Cases_on `evaluate (y::xs,env,r)` \\ Cases_on `q` \\ fs []
    \\ rw[] \\ fs[])
  THEN1 (* Var *)
   (Cases_on `n < LENGTH env` \\ fs []
    \\ `n < LENGTH env + LENGTH ys` by DECIDE_TAC
    \\ fs [compile_def,evaluate_def,rich_listTheory.EL_APPEND1])
  THEN1 (* If *)
   (Cases_on `evaluate ([x1],env,s)` \\ Cases_on `q` \\ fs []
    \\ SRW_TAC [] [] \\ fs []
    \\ FIRST_X_ASSUM MATCH_MP_TAC \\ METIS_TAC [])
  THEN1 (* Let *)
   (Cases_on `evaluate (xs,env,s)` \\ Cases_on `q` \\ fs []
    \\ rw[] \\ fs[]
    \\ ONCE_REWRITE_TAC [ADD_COMM]
    \\ `LENGTH xs = LENGTH a` by (IMP_RES_TAC evaluate_IMP_LENGTH \\ fs [])
    \\ fs [] \\ FIRST_X_ASSUM MATCH_MP_TAC \\ METIS_TAC [])
  THEN1 (* Raise *)
   (Cases_on `evaluate ([x1],env,s)` \\ Cases_on `q` \\ fs [] \\ rw[] \\ fs[])
  THEN1 (* Handle *)
   (fs [LET_DEF,evaluate_def,compile_HD_SING,evaluate_GENLIST]
    \\ Cases_on `evaluate ([x1],env,s1)` \\ fs []
    \\ `q <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ fs []) \\ fs []
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] \\ fs []
    \\ Cases_on `q` \\ fs [ADD1]
    \\ Cases_on`e` \\ fs[]
    \\ FIRST_X_ASSUM MATCH_MP_TAC \\ METIS_TAC [])
  THEN1 (* Op *)
   (Cases_on `evaluate (xs,env,s)` \\ Cases_on `q` \\ fs [] \\ rw[] \\ fs[])
  THEN1 (* Tick *)
   (Cases_on `s.clock = 0` \\ fs [compile_HD_SING]
    \\ FIRST_X_ASSUM MATCH_MP_TAC \\ METIS_TAC [])
  THEN1 (* Call *)
   (Cases_on `evaluate (xs,env,s1)` \\ Cases_on `q` \\ fs [] \\ rw[] \\ fs[]))
  |> Q.SPECL [`xs`,`env`,`s1`,`res`,`s2`,`[]`]
  |> SIMP_RULE std_ss [APPEND_NIL];

val _ = save_thm("compile_correct",compile_correct);

val _ = export_theory();
