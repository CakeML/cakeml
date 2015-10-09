open preamble
     bvi_to_bvpTheory
     bviSemTheory bviPropsTheory
     bvpSemTheory bvpPropsTheory
     bvp_simpProofTheory
     bvp_liveProofTheory
     bvp_spaceProofTheory;

val _ = new_theory"bvi_to_bvpProof";

(* value relation *)

val code_rel_def = Define `
  code_rel bvi_code bvp_code <=>
    wf bvi_code /\ wf bvp_code /\
    (domain bvi_code = domain bvp_code) /\
    !n exp arg_count.
      (lookup n bvi_code = SOME (arg_count,exp)) ==>
      (lookup n bvp_code = SOME (arg_count,compile_exp arg_count exp))`;

val state_rel_def = Define `
  state_rel (s:'ffi bviSem$state) (t:'ffi bvpSem$state) <=>
    (s.clock = t.clock) /\
    code_rel s.code t.code /\
    (s.refs = t.refs) /\
    (s.ffi = t.ffi) /\
    (s.global = t.global)`;

(* semantics lemmas *)

val find_code_def = bvlSemTheory.find_code_def;

val find_code_lemma = prove(
  ``state_rel r t2 /\
    (find_code dest a r.code = SOME (args,exp)) ==>
    (find_code dest a t2.code = SOME (args,compile_exp (LENGTH args) exp))``,
  reverse (Cases_on `dest`) \\ SIMP_TAC std_ss [find_code_def]
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
  \\ `x0 = LENGTH args` by ALL_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `?t1 t2. a = SNOC t1 t2` by METIS_TAC [SNOC_CASES]
  \\ FULL_SIMP_TAC std_ss [FRONT_SNOC,LENGTH_SNOC,ADD1]);

val do_app_bvp_to_bvi = prove(
  ``(do_app op a s1 = Rval (x0,s2)) /\ state_rel s1 t1 ==>
    (do_app op a (bvp_to_bvi t1) =
      Rval (x0,s2 with code := map (K ARB) t1.code))``,
  fs [state_rel_def]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ fs []
  \\ fs [bviSemTheory.do_app_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `do_app_aux op a s1` \\ fs []
  \\ reverse (Cases_on `x`) \\ fs [] THEN1
   (Cases_on `op` \\ fs [do_app_aux_def]
    \\ SRW_TAC [] [] \\ fs [] \\ SRW_TAC [] []
    \\ fs [bvp_to_bvi_def,bviSemTheory.state_component_equality]
    \\ Cases_on `a` \\ fs []
    \\ SRW_TAC [] [] \\ fs [] \\ SRW_TAC [] []
    \\ fs [bvp_to_bvi_def,bviSemTheory.state_component_equality]
    \\ every_case_tac
    \\ fs [bvp_to_bvi_def,bviSemTheory.state_component_equality])
  \\ `do_app_aux op a (bvp_to_bvi t1) = SOME NONE` by
   (Cases_on `op` \\ fs [do_app_aux_def]
    \\ every_case_tac \\ fs [])
  \\ `bvi_to_bvl (bvp_to_bvi t1) = bvi_to_bvl s1` by ALL_TAC THEN1
   (fs [bvi_to_bvl_def,bvp_to_bvi_def,code_rel_def,
        spt_eq_thm,lookup_map_K,domain_map,
        bvlSemTheory.state_component_equality]) \\ fs []
  \\ Cases_on `do_app op a (bvi_to_bvl s1)` \\ fs []
  \\ Cases_on `a'` \\ fs []
  \\ fs [bvl_to_bvi_def,bvp_to_bvi_def,bviSemTheory.state_component_equality]);

(* compiler correctness *)

val optimise_correct = Q.store_thm("optimise_correct",
  `!c s. FST (evaluate (c,s)) <> SOME (Rerr(Rabort Rtype_error)) /\
         FST (evaluate (c,s)) <> NONE ==>
         (evaluate (optimise c,s) = evaluate (c,s))`,
  fs [optimise_def] \\ REPEAT STRIP_TAC \\ Cases_on `evaluate (c,s)` \\ fs []
  \\ METIS_TAC [simp_correct,bvp_liveProofTheory.compile_correct,bvp_spaceProofTheory.compile_correct,FST]);

val compile_RANGE_lemma = prove(
  ``!n env tail live xs.
      EVERY (\v. n <= v /\ v < (SND (SND (compile n env tail live xs))))
        (FST (SND (compile n env tail live xs)))``,
  HO_MATCH_MP_TAC compile_ind \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [compile_def] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ IMP_RES_TAC compile_SING_IMP
  \\ fs [EVERY_MEM]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ IMP_RES_TAC compile_LESS_EQ
  \\ TRY (Cases_on `tail`) \\ fs [] \\ DECIDE_TAC);

val compile_RANGE = prove(
  ``(compile n env tail live xs = (ys,vs,k)) ==> EVERY (\v. n <= v /\ v < k) vs``,
  REPEAT STRIP_TAC \\ MP_TAC (compile_RANGE_lemma |> SPEC_ALL) \\ fs []);

val _ = temp_overload_on("res_list",``map_result (λv. [v]) I``);
val _ = temp_overload_on("isException",``λx. ∃v. x = Rerr(Rraise v)``);
val _ = temp_overload_on("isResult",``λx. ∃v. x = Rval v``);

val RW = REWRITE_RULE;

val compile_correct = Q.prove(
  `!xs env s1 res s2 t1 n corr tail live.
     (evaluate (xs,env,s1) = (res,s2)) /\ res <> Rerr(Rabort Rtype_error) /\
     var_corr env corr t1 /\ (LENGTH xs <> 1 ==> ~tail) /\
     (!k. n <= k ==> (lookup k t1.locals = NONE)) /\
     state_rel s1 t1 /\ EVERY (\n. lookup n t1.locals <> NONE) live /\
     (isException res ==> jump_exc t1 <> NONE) ==>
     ?t2 prog pres vs next_var.
       (compile n corr tail live xs = (prog,vs,next_var)) /\
       (evaluate (prog,t1) = (pres,t2)) /\ state_rel s2 t2 /\
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
                  | Rval xs => var_corr xs vs t2
                  | _ => F)`,
  SIMP_TAC std_ss [Once EQ_SYM_EQ]
  \\ recInduct bviSemTheory.evaluate_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [compile_def,bvpSemTheory.evaluate_def,bviSemTheory.evaluate_def]
  THEN1 (* NIL *)
    (SRW_TAC [] [var_corr_def]
     \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss [NOT_LESS]
     \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
  THEN1 (* CONS *)
   (`?c1 v1 n1. compile n corr F live [x] = (c1,v1,n1)` by METIS_TAC [PAIR]
    \\ `?c2 vs n2. compile n1 corr F (HD v1::live) (y::xs) = (c2,vs,n2)` by
          METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,evaluate_def]
    \\ Cases_on `evaluate ([x],env,s)`
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ rpt var_eq_tac >> fs[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ Cases_on `pres` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `evaluate (y::xs,env,r)`
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ rpt var_eq_tac >> fs[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n1`,`corr`,`F`,`HD v1::live`])
    \\ simp[]
    \\ `EVERY (\n. lookup n t2.locals <> NONE) (HD v1::live)` by
     (IMP_RES_TAC evaluate_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
      \\ IMP_RES_TAC compile_SING_IMP \\ fs [var_corr_def,get_var_def]
      \\ fs [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
      \\ Cases_on `lookup n' t1.locals` \\ fs [] \\ METIS_TAC [])
    \\ fs[] \\ strip_tac
    \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) [var_corr_def]
    \\ IMP_RES_TAC evaluate_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC compile_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC THEN1 DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM]
    THEN1 (REPEAT STRIP_TAC \\ RES_TAC \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [get_var_def])
  THEN1 (* Var *)
   (Cases_on `tail` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `n < LENGTH env`
    \\ FULL_SIMP_TAC (srw_ss()) [evaluate_def]
    \\ FULL_SIMP_TAC std_ss [var_corr_def]
    \\ FULL_SIMP_TAC std_ss [var_corr_def,LIST_REL_def]
    \\ FULL_SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN]
    \\ FULL_SIMP_TAC (srw_ss()) [get_var_def,set_var_def,lookup_insert]
    \\ Q.MATCH_ASSUM_RENAME_TAC `k < LENGTH env`
    \\ FULL_SIMP_TAC (srw_ss()) [state_rel_def,call_env_def]
    \\ REPEAT STRIP_TAC
    \\ SRW_TAC [] [] THEN1 DECIDE_TAC
    THEN1 (FIRST_X_ASSUM MATCH_MP_TAC \\ DECIDE_TAC)
    THEN1 (Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env`
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
   (`?c1 v1 n1. compile n corr F live [x1] = (c1,v1,n1)` by METIS_TAC [PAIR]
    \\ `?c2 v2 n2. compile n1 corr tail live [x2] = (c2,v2,n2)` by METIS_TAC [PAIR]
    \\ `?c3 v3 n3. compile n2 corr tail live [x3] = (c3,v3,n3)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,evaluate_def]
    \\ Cases_on `tail` \\ FULL_SIMP_TAC std_ss [] THEN1
     (SIMP_TAC std_ss [evaluate_def]
      \\ Cases_on `evaluate ([x1],env,s)` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
      \\ rpt var_eq_tac >> fs[] >> strip_tac
      \\ Cases_on `pres`
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ IMP_RES_TAC evaluate_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
      \\ IMP_RES_TAC compile_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
      \\ SRW_TAC [] []
      \\ Q.MATCH_ASSUM_RENAME_TAC `var_corr [w] [n5] t2`
      \\ `get_var n5 t2 = SOME w` by FULL_SIMP_TAC (srw_ss()) [var_corr_def]
      \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [LET_DEF]
      \\ CONV_TAC (DEPTH_CONV (DEPTH_CONV PairRules.PBETA_CONV))
      \\ IMP_RES_TAC compile_LESS_EQ
      \\ `EVERY (\n. lookup n t2.locals <> NONE) live` by
        (fs [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
         \\ Cases_on `lookup n' t1.locals` \\ fs [] \\ METIS_TAC [])
      \\ Cases_on `w = Boolv T` \\ FULL_SIMP_TAC (srw_ss()) []
      THEN1
       (Q.PAT_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
        \\ FULL_SIMP_TAC std_ss []
        \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n1`,`corr`,`T`,`live`])
        \\ FULL_SIMP_TAC std_ss [])
      \\ Cases_on `w = Boolv F` \\ FULL_SIMP_TAC (srw_ss()) []
      THEN1
       (Q.PAT_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
        \\ FULL_SIMP_TAC std_ss []
        \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n2`,`corr`,`T`,`live`])
        \\ FULL_SIMP_TAC std_ss []
        \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
        THEN1 (REPEAT STRIP_TAC \\ FIRST_X_ASSUM MATCH_MP_TAC \\ DECIDE_TAC)
        \\ FULL_SIMP_TAC std_ss []))
    \\ SIMP_TAC std_ss [evaluate_def]
    \\ Cases_on `evaluate ([x1],env,s)` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ rpt var_eq_tac >> fs[] >> strip_tac
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC evaluate_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC compile_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SRW_TAC [] []
    \\ Q.MATCH_ASSUM_RENAME_TAC `var_corr [w] [n5] t2`
    \\ `get_var n5 t2 = SOME w` by FULL_SIMP_TAC (srw_ss()) [var_corr_def]
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [LET_DEF]
    \\ CONV_TAC (DEPTH_CONV (DEPTH_CONV PairRules.PBETA_CONV))
    \\ IMP_RES_TAC compile_LESS_EQ
    \\ `EVERY (\n. lookup n t2.locals <> NONE) live` by
      (fs [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
       \\ Cases_on `lookup n' t1.locals` \\ fs [] \\ METIS_TAC [])
    \\ Cases_on `w = Boolv T` \\ FULL_SIMP_TAC (srw_ss()) []
    THEN1
     (Q.PAT_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n1`,`corr`,`F`,`live`])
      \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
      \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ Cases_on `res` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ IMP_RES_TAC evaluate_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
      \\ SRW_TAC [] []
      \\ Q.MATCH_ASSUM_RENAME_TAC `var_corr [w7] [n7] t7`
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
        \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env`
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
    \\ Cases_on `w = Boolv F` \\ FULL_SIMP_TAC (srw_ss()) []
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
      \\ IMP_RES_TAC evaluate_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
      \\ SRW_TAC [] []
      \\ Q.MATCH_ASSUM_RENAME_TAC `var_corr [w7] [n7] t7`
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
        \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env`
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
   (`?c1 vs n1. compile n corr F live xs = (c1,vs,n1)` by METIS_TAC [PAIR]
    \\ `?c2 v2 n2. compile n1 (vs ++ corr) tail live [x2] =
                   (c2,v2,n2)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,evaluate_def]
    \\ Cases_on `evaluate (xs,env,s)`
    \\ reverse (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ rpt var_eq_tac >> fs[] >> strip_tac
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Q.PAT_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ `var_corr (a ++ env) (vs ++ corr) t2` by
     (FULL_SIMP_TAC (srw_ss()) [var_corr_def]
      \\ MATCH_MP_TAC (GEN_ALL EVERY2_APPEND_suff)
      \\ FULL_SIMP_TAC std_ss [LIST_REL_REVERSE_EQ])
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
   (`?c1 v1 n1. compile n corr F live [x1] = (c1,v1,n1)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,evaluate_def,call_env_def]
    \\ Cases_on `evaluate ([x1],env,s)` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ rpt var_eq_tac >> fs[] >> strip_tac
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC evaluate_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC compile_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SRW_TAC [] []
    \\ `get_var t t2 = SOME w` by fs [var_corr_def]
    \\ fs [] \\ Cases_on `jump_exc t2` \\ fs []
    \\ FULL_SIMP_TAC std_ss [state_rel_def]
    \\ IMP_RES_TAC jump_exc_IMP \\ fs []
    \\ fs [jump_exc_def])
  THEN1 (* Op *)
   (`?c1 vs n1. compile n corr F live xs = (c1,vs,n1)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,evaluate_def]
    \\ Cases_on `evaluate (xs,env,s)`
    \\ reverse (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ rpt var_eq_tac >> fs[] >> strip_tac
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) []
    THEN1 SRW_TAC [] [evaluate_def]
    \\ `domain (list_to_num_set (REVERSE vs ++ live ++ corr)) SUBSET
        domain t2.locals` by
     (fs [SUBSET_DEF,domain_lookup,lookup_list_to_num_set,EVERY_MEM]
      \\ REPEAT STRIP_TAC \\ RES_TAC
      \\ fs [var_corr_def,get_var_def]
      \\ IMP_RES_TAC MEM_LIST_REL \\ fs []
      \\ `lookup x t1.locals <> NONE` by METIS_TAC []
      \\ Cases_on `lookup x t1.locals` \\ fs [] \\ METIS_TAC []) \\ fs []
    \\ Q.ABBREV_TAC `env1 = mk_wf (inter t2.locals (list_to_num_set (REVERSE vs++live++corr)))`
    \\ `var_corr (REVERSE a) (REVERSE vs) (t2 with locals := env1)` by
     (UNABBREV_ALL_TAC
      \\ fs [var_corr_def,get_var_def,state_rel_def,
             lookup_inter_EQ,lookup_list_to_num_set]
      \\ Q.PAT_ASSUM `LIST_REL rrr xs1 xs2` MP_TAC
      \\ ONCE_REWRITE_TAC [LIST_REL_MEM] \\ fs [EVERY2_REVERSE] \\ NO_TAC)
    \\ IMP_RES_TAC get_vars_thm
    \\ `state_rel r (t2 with <|locals := env1; space := 0|>)` by
          (fs [state_rel_def] \\ NO_TAC)
    \\ reverse(Cases_on `do_app op (REVERSE a) r`) \\ fs [] >- (
         imp_res_tac bviPropsTheory.do_app_err >> fs[] )
    \\ PairCases_on `a'` \\ fs [] \\ REV_FULL_SIMP_TAC std_ss []
    \\ rpt var_eq_tac >> fs[]
    \\ fs [LET_DEF,evaluate_def,iAssign_def]
    \\ (fn (hs,goal) => (reverse (`let tail = F in ^goal` by ALL_TAC))
           (hs,goal)) THEN1
     (fs [LET_DEF] \\ reverse (Cases_on `tail`) THEN1 METIS_TAC []
      \\ fs [evaluate_def,LET_DEF] \\ REV_FULL_SIMP_TAC std_ss []
      \\ Cases_on `pres` \\ fs []
      \\ fs [var_corr_def,call_env_def,state_rel_def])
    \\ simp[]
    \\ IMP_RES_TAC do_app_bvp_to_bvi \\ fs []
    \\ Cases_on `op_space_reset op`
    \\ fs [evaluate_def,cut_state_opt_def,cut_state_def,cut_env_def]
    \\ fs [bvpSemTheory.do_app_def,do_space_def]
    \\ simp[]
    \\ fs [get_var_def,set_var_def]
    \\ fs [call_env_def,bvi_to_bvp_def]
    \\ fs [state_rel_def] \\ IMP_RES_TAC do_app_code \\ fs []
    \\ IMP_RES_TAC compile_LESS_EQ \\ fs [lookup_insert]
    THEN1
     (REPEAT STRIP_TAC
      THEN1 (SRW_TAC [] [] THEN1 DECIDE_TAC
         \\ UNABBREV_ALL_TAC \\ fs [lookup_inter_EQ]
         \\ `n1 <= k` by DECIDE_TAC \\ fs [])
      THEN1 (fs [LIST_REL_EL_EQN,var_corr_def,get_var_def,lookup_insert]
        \\ REPEAT STRIP_TAC
        \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env`
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
    \\ imp_res_tac get_vars_reverse
    \\ Cases_on `op_space_req op = 0` \\ fs [evaluate_def]
    \\ fs [evaluate_def,cut_state_opt_def,cut_state_def,cut_env_def]
    \\ fs [bvpSemTheory.do_app_def,do_space_def,LET_DEF]
    \\ IMP_RES_TAC do_app_bvp_to_bvi \\ fs []
    \\ fs [get_var_def,set_var_def]
    \\ fs [call_env_def,bvi_to_bvp_def]
    \\ fs [state_rel_def] \\ IMP_RES_TAC do_app_code \\ fs []
    \\ IMP_RES_TAC compile_LESS_EQ \\ fs [lookup_insert]
    THEN1
     (REPEAT STRIP_TAC
      THEN1 (SRW_TAC [] [] THEN1 DECIDE_TAC
         \\ UNABBREV_ALL_TAC \\ fs [lookup_inter_EQ]
         \\ `n1 <= k` by DECIDE_TAC \\ fs [])
      THEN1 (fs [LIST_REL_EL_EQN,var_corr_def,get_var_def,lookup_insert]
        \\ REPEAT STRIP_TAC
        \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env`
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
     (REPEAT STRIP_TAC
      THEN1 (SRW_TAC [] [] THEN1 DECIDE_TAC
         \\ UNABBREV_ALL_TAC \\ fs [lookup_inter_EQ]
         \\ `n1 <= k` by DECIDE_TAC \\ fs [])
      THEN1 (fs [LIST_REL_EL_EQN,var_corr_def,get_var_def,lookup_insert]
        \\ REPEAT STRIP_TAC
        \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env`
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
   (`?c1 v1 n1. compile n corr tail live [x] = (c1,v1,n1)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,evaluate_def]
    \\ Cases_on `t1.clock = 0` \\ FULL_SIMP_TAC std_ss []
    THEN1 (fs [state_rel_def,call_env_def])
    \\ `s.clock <> 0` by ALL_TAC
    THEN1 (FULL_SIMP_TAC std_ss [state_rel_def])
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`dec_clock t1`,`n`,`corr`,`tail`,`live`])
    \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [var_corr_def,bvpSemTheory.dec_clock_def,
         get_var_def,state_rel_def,bviSemTheory.dec_clock_def,jump_exc_NONE])
  THEN1 (* Call *)
   (Cases_on `handler` THEN1 (* Call without handler *)
     (`?c1 vs n1. compile n corr F live xs = (c1,vs,n1)` by METIS_TAC [PAIR]
      \\ FULL_SIMP_TAC std_ss [LET_DEF,evaluate_def,call_env_def,compile_def,
           evaluate_mk_ticks]
      \\ Cases_on `evaluate (xs,env,s1)`
      \\ reverse (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
      \\ rpt var_eq_tac >> fs[]>> strip_tac
      \\ Cases_on `pres`
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ Cases_on `find_code dest a r.code` \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss []
      \\ Q.MATCH_ASSUM_RENAME_TAC `find_code dest a r.code = SOME (args,exp)`
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ `t2.clock = r.clock` by FULL_SIMP_TAC std_ss [state_rel_def]
      \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `r.clock < ticks + 1`
      \\ fs[]
      THEN1 (
        `r.clock < ticks ∨ r.clock = ticks` by decide_tac >>
        fs [state_rel_def, funpow_dec_clock_clock])
      \\ `~(r.clock < ticks)` by decide_tac
      \\ `(FUNPOW dec_clock ticks t2).clock ≠ 0` by simp [funpow_dec_clock_clock]
      \\ fs []
      \\ `get_vars vs t2 = SOME a` by IMP_RES_TAC get_vars_thm
      \\ FULL_SIMP_TAC std_ss []
      \\ IMP_RES_TAC find_code_lemma
      \\ FULL_SIMP_TAC (srw_ss()) [] \\ POP_ASSUM (K ALL_TAC)
      \\ FULL_SIMP_TAC std_ss [compile_exp_def]
      \\ Q.PAT_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `tail` THEN1
       (`evaluate ([exp],args,dec_clock (ticks + 1) r) = (res,s2)` by ALL_TAC THEN1
        (Cases_on `evaluate ([exp],args,dec_clock (ticks+1) r)` \\ fs []
           \\ Cases_on `q` \\ fs [] \\
           Cases_on`e` >> fs[]) \\ fs []
        \\ FIRST_X_ASSUM (qspecl_then
             [`call_env args (FUNPOW dec_clock (ticks+1) t2)`,
               `LENGTH args`,
               `GENLIST I (LENGTH args)`,`T`,`[]`]mp_tac)
        \\ FULL_SIMP_TAC std_ss []
        \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
         (FULL_SIMP_TAC (srw_ss()) [state_rel_def,bvpSemTheory.dec_clock_def,
          bviSemTheory.dec_clock_def,var_corr_def,get_var_def,LIST_REL_REVERSE_EQ,
          LIST_REL_lookup_fromList,lookup_fromList_outside,jump_exc_NONE,call_env_def,
          funpow_dec_clock_clock])
        \\ STRIP_TAC \\ fs [LET_DEF]
        \\ MP_TAC (Q.SPECL [`prog`,
            `call_env args (FUNPOW dec_clock (ticks+1) t2)`] optimise_correct)
        \\ fs [] \\ SIMP_TAC std_ss [call_env_def]
        \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
         (BasicProvers.FULL_CASE_TAC \\ fs [funpow_dec_clock_clock]
          \\ REPEAT STRIP_TAC \\ fs [])
        \\ REPEAT STRIP_TAC \\ fs [get_vars_FUNPOW_dec_clock,COUNT_LIST_GENLIST]
        \\ fs [FUNPOW_dec_clock_code]
        \\ fs [GSYM ADD1,FUNPOW_SUC]
        \\ Cases_on `pres` \\ fs [] \\ FULL_SIMP_TAC std_ss []
        \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
        \\ FULL_SIMP_TAC (srw_ss()) [call_env_def,
           bviSemTheory.dec_clock_def,bvpSemTheory.dec_clock_def]
        \\ REV_FULL_SIMP_TAC (srw_ss()) [FUNPOW_dec_clock_code])
      \\ `domain (list_to_num_set (live ++ corr)) SUBSET domain t2.locals` by
       (fs [SUBSET_DEF,domain_lookup,lookup_list_to_num_set,EVERY_MEM]
        \\ REPEAT STRIP_TAC \\ RES_TAC THEN1
       (`lookup x t1.locals <> NONE` by METIS_TAC []
          \\ Cases_on `lookup x t1.locals` \\ fs [] \\ METIS_TAC [])
        \\ fs [var_corr_def,get_var_def]
        \\ IMP_RES_TAC MEM_LIST_REL \\ fs [])
      \\ fs [cut_env_def]
      \\ `evaluate ([exp],args,dec_clock (ticks + 1) r) = (res,s2)` by ALL_TAC THEN1
       (Cases_on `evaluate ([exp],args,dec_clock (ticks + 1) r)` \\ fs []
        \\ Cases_on `q` \\ fs []
        \\ Cases_on`e` \\ fs[]) \\ fs []
      \\ Q.ABBREV_TAC `env2 = (inter t2.locals (list_to_num_set (live ++ corr)))`
      \\ FIRST_X_ASSUM (qspecl_then
          [`call_env args (push_env env2 F (FUNPOW dec_clock (ticks + 1) t2))`,
           `LENGTH args`,
           `GENLIST I (LENGTH args)`,`T`,`[]`]mp_tac)
      \\ FULL_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (FULL_SIMP_TAC (srw_ss()) [state_rel_def,bvpSemTheory.dec_clock_def,
          bviSemTheory.dec_clock_def,var_corr_def,get_var_def,LIST_REL_REVERSE_EQ,
          LIST_REL_lookup_fromList,lookup_fromList_outside,push_env_def,
          call_env_def,FUNPOW_dec_clock_code]
          \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
          \\ `jump_exc t2 <> NONE` by fs[]
          \\ Cases_on `jump_exc t2` \\ fs []
          \\ IMP_RES_TAC jump_exc_IMP
          \\ SIMP_TAC (srw_ss()) [jump_exc_def,FUNPOW_dec_clock_code]
          \\ IMP_RES_TAC LAST_N_TL \\ fs []
          \\ DECIDE_TAC)
      \\ STRIP_TAC \\ fs [LET_DEF]
      \\ MP_TAC (Q.SPECL [`prog`,`call_env args
         (push_env env2 F (FUNPOW dec_clock (ticks + 1) t2))`]
            optimise_correct) \\ fs []
      \\ SIMP_TAC std_ss [call_env_def]
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (BasicProvers.FULL_CASE_TAC \\ fs []
        \\ REPEAT STRIP_TAC \\ fs [])
      \\ REPEAT STRIP_TAC \\ fs []
      \\ fs [get_vars_FUNPOW_dec_clock,FUNPOW_dec_clock_code,COUNT_LIST_GENLIST]
      \\ fs [GSYM ADD1,FUNPOW_SUC]
      \\ Cases_on `pres` \\ fs [call_env_def]
      \\ `~(r.clock ≤ ticks)` by DECIDE_TAC \\ fs []
      \\ reverse (Cases_on `x`) \\ FULL_SIMP_TAC (srw_ss()) []
      \\ rpt var_eq_tac >> fs[]
      THEN1
       (Cases_on`e`>>fs[]>>
        IMP_RES_TAC jump_exc_IMP
        \\ FULL_SIMP_TAC (srw_ss()) [call_env_def,push_env_def,
           bvpSemTheory.dec_clock_def,bviSemTheory.dec_clock_def]
        \\ SIMP_TAC (srw_ss()) [jump_exc_def]
        \\ fs [FUNPOW_dec_clock_code]
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
             pop_env_def,bvpSemTheory.dec_clock_def,bviSemTheory.dec_clock_def,
             FUNPOW_dec_clock_code])
      \\ fs [set_var_def,state_rel_def]
      \\ IMP_RES_TAC compile_LESS_EQ
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
        \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env`
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
                call_env_def,push_env_def,bvpSemTheory.dec_clock_def,
                bviSemTheory.dec_clock_def]
                 \\ FULL_SIMP_TAC (srw_ss()) [jump_exc_def]
                 \\ BasicProvers.EVERY_CASE_TAC))
    \\ (* Call with handle *)
      `?c1 vs n1. compile n corr F live xs = (c1,vs,n1)` by METIS_TAC [PAIR]
      \\ `?c2 v n2. compile (n1+1) (n1::corr) F live [x] = (c2,v,n2)` by
            METIS_TAC [PAIR]
      \\ fs [LET_DEF,evaluate_def,evaluate_mk_ticks,call_env_def,compile_def]
      \\ Cases_on `evaluate (xs,env,s1)`
      \\ Cases_on `dest = NONE` \\ fs []
      \\ reverse (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
      \\ rpt var_eq_tac >> fs[]>> strip_tac
      \\ Cases_on `pres`
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ Cases_on `find_code dest a r.code` \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `x'` \\ FULL_SIMP_TAC std_ss []
      \\ Q.MATCH_ASSUM_RENAME_TAC `find_code dest a r.code = SOME (args,exp)`
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ `t2.clock = r.clock` by FULL_SIMP_TAC std_ss [state_rel_def]
      \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `r.clock < ticks + 1`
      \\ fs[]
      THEN1 (`r.clock < ticks \/ r.clock <= ticks` by DECIDE_TAC
             \\ fs [state_rel_def]
             \\ SRW_TAC [] []
             \\ fs [state_rel_def])
      \\ `get_vars vs t2 = SOME a` by IMP_RES_TAC get_vars_thm
      \\ FULL_SIMP_TAC std_ss []
      \\ IMP_RES_TAC find_code_lemma
      \\ FULL_SIMP_TAC (srw_ss()) [] \\ POP_ASSUM (K ALL_TAC)
      \\ FULL_SIMP_TAC std_ss [compile_exp_def]
      \\ `~(r.clock < ticks) /\ ~(r.clock ≤ ticks)` by DECIDE_TAC \\ fs []
      \\ Q.PAT_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss []
      \\ `domain (list_to_num_set (live ++ corr)) SUBSET domain t2.locals` by
       (fs [SUBSET_DEF,domain_lookup,lookup_list_to_num_set,EVERY_MEM]
        \\ REPEAT STRIP_TAC \\ RES_TAC THEN1
         (`lookup x' t1.locals <> NONE` by METIS_TAC []
          \\ Cases_on `lookup x' t1.locals` \\ fs [] \\ METIS_TAC [])
        \\ fs [var_corr_def,get_var_def]
        \\ IMP_RES_TAC MEM_LIST_REL \\ fs [] \\ NO_TAC)
      \\ fs [cut_env_def]
      \\ Cases_on `evaluate ([exp],args,dec_clock (ticks + 1) r)`
      \\ Q.MATCH_ASSUM_RENAME_TAC
            `evaluate ([exp],args,dec_clock (ticks + 1) r) = (res4,r4)`
      \\ Cases_on `isException res4` THEN1
       (Cases_on `res4` \\ fs [LET_DEF] \\ fs[]
        \\ Q.ABBREV_TAC `env2 = (inter t2.locals (list_to_num_set (live ++ corr)))`
        \\ FIRST_X_ASSUM (qspecl_then
            [`call_env args (push_env env2 T (FUNPOW dec_clock (ticks+1) t2))`,
             `LENGTH args`,
             `GENLIST I (LENGTH args)`,`T`,`[]`] mp_tac)
        \\ FULL_SIMP_TAC std_ss []
        \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
         (FULL_SIMP_TAC (srw_ss()) [state_rel_def,bvpSemTheory.dec_clock_def,
            bviSemTheory.dec_clock_def,var_corr_def,get_var_def,LIST_REL_REVERSE_EQ,
            LIST_REL_lookup_fromList,lookup_fromList_outside,push_env_def,call_env_def]
          \\ fs [jump_exc_def,LAST_N_LENGTH |> Q.SPEC `x::xs` |> RW [LENGTH,ADD1]])
        \\ REPEAT STRIP_TAC
        \\ Cases_on `pres` \\ fs []
        \\ rpt var_eq_tac \\ fs[]
        \\ MP_TAC (Q.SPECL [`prog`,`call_env args
           (push_env env2 T (FUNPOW dec_clock (ticks+1) t2))`]
              optimise_correct) \\ fs []
        \\ fs[COUNT_LIST_GENLIST]
        \\ SIMP_TAC std_ss [call_env_def] \\ REPEAT STRIP_TAC \\ fs []
        \\ Cases_on `evaluate (c2,set_var n1 v' t2')` \\ fs []
        \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL
              [`set_var n1 v' t2'`,`n1+1`,`n1::corr`,`F`,`live`]) \\ fs []
        \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
         (fs [var_corr_def,state_rel_def,set_var_def,lookup_insert,get_var_def]
          \\ fs [jump_exc_def,call_env_def,push_env_def,bvpSemTheory.dec_clock_def]
          \\ fs [jump_exc_def,LAST_N_LENGTH |> Q.SPEC `x::xs` |> RW [LENGTH,ADD1]]
          \\ fs [bvpSemTheory.state_component_equality]
          \\ Q.PAT_ASSUM `env2 = t2'.locals` (ASSUME_TAC o GSYM) \\ fs []
          \\ Q.UNABBREV_TAC `env2` \\ fs [lookup_inter_alt]
          \\ fs [domain_lookup,lookup_list_to_num_set]
          \\ REPEAT STRIP_TAC THEN1
           (fs [LIST_REL_EL_EQN] \\ REPEAT STRIP_TAC
            \\ Q.MATCH_ASSUM_RENAME_TAC `n3 < LENGTH env`
            \\ `MEM (EL n3 corr) corr` by METIS_TAC [MEM_EL] \\ fs []
            \\ SRW_TAC [] []
            \\ `EL n3 corr <= EL n3 corr` by fs [] \\ RES_TAC \\ fs [])
          THEN1 (`k <> n1 /\ n1 <= k` by DECIDE_TAC \\ fs [])
          THEN1
           (fs [EVERY_MEM] \\ REPEAT STRIP_TAC
            \\ Cases_on `n' = n1` \\ RES_TAC \\ fs []
            \\ Cases_on `lookup n' t1.locals` \\ fs []
            \\ RES_TAC \\ fs [] \\ Cases_on `lookup n' t2.locals` \\ fs [])
          \\ Cases_on `LAST_N (t2'.handler + 1) t2'.stack` \\ fs []
          \\ Cases_on `h` \\ fs [])
        \\ REPEAT STRIP_TAC \\ fs [GSYM ADD1, FUNPOW_SUC]
        \\ reverse (Cases_on `q`) \\ fs [] THEN1
         (REPEAT STRIP_TAC \\ fs [set_var_def,jump_exc_def,call_env_def,
            push_env_def,bvpSemTheory.dec_clock_def]
          \\ fs [jump_exc_def,LAST_N_LENGTH |> Q.SPEC `x::xs` |> RW [LENGTH,ADD1]]
          \\ NTAC 2 (POP_ASSUM MP_TAC)
          \\ Q.PAT_ASSUM `xxx = t2'` (fn th => ONCE_REWRITE_TAC [GSYM th]) \\ fs [])
        \\ Cases_on `res` \\ fs [] \\ fs []
        \\ `(t2'.stack = t2.stack) /\ (t2'.handler = t2.handler)` by ALL_TAC THEN1
         (REPEAT STRIP_TAC \\ fs [set_var_def,jump_exc_def,call_env_def,
            push_env_def,bvpSemTheory.dec_clock_def]
          \\ fs [jump_exc_def,LAST_N_LENGTH |> Q.SPEC `x::xs` |> RW [LENGTH,ADD1]]
          \\ fs [bvpSemTheory.state_component_equality])
        \\ Cases_on `tail` \\ fs [evaluate_def]
        THEN1
         (IMP_RES_TAC compile_LENGTH
          \\ `?v1. v = [v1]` by (Cases_on `v` \\ fs [LENGTH_NIL])
          \\ fs [var_corr_def,set_var_def,call_env_def]
          \\ fs [state_rel_def])
        \\ REPEAT STRIP_TAC
        THEN1 DECIDE_TAC
        THEN1
         (IMP_RES_TAC compile_RANGE \\ fs [EVERY_MEM]
          \\ REPEAT STRIP_TAC \\ RES_TAC \\ DECIDE_TAC)
        THEN1 (fs [var_corr_def])
        THEN1
         (FIRST_X_ASSUM MATCH_MP_TAC \\ reverse STRIP_TAC THEN1 METIS_TAC []
          \\ fs [set_var_def,lookup_insert]
          \\ `k <> n1` by ALL_TAC \\ fs [] THEN1
           (REPEAT STRIP_TAC \\ fs []
            \\ `n <= n1` by DECIDE_TAC \\ RES_TAC \\ fs [])
          \\ UNABBREV_ALL_TAC
          \\ REPEAT STRIP_TAC \\ fs [set_var_def,jump_exc_def,call_env_def,
            push_env_def,bvpSemTheory.dec_clock_def]
          \\ fs [jump_exc_def,LAST_N_LENGTH |> Q.SPEC `x::xs` |> RW [LENGTH,ADD1]]
          \\ fs [bvpSemTheory.state_component_equality]
          \\ Q.PAT_ASSUM `xxx = t2'.locals` (ASSUME_TAC o GSYM)
          \\ fs [lookup_inter_alt]
          \\ fs [domain_lookup,lookup_list_to_num_set] \\ METIS_TAC [])
        \\ fs [set_var_def]
        \\ fs [jump_exc_def]
        \\ Cases_on `LAST_N (t1.handler + 1) t1.stack` \\ fs []
        \\ Cases_on `h` \\ fs []
        \\ fs [call_env_def,push_env_def,bvpSemTheory.dec_clock_def]
        \\ Cases_on `LAST_N (r'.handler + 1) r'.stack` \\ fs []
        \\ Cases_on `h` \\ fs [])
      \\ `(res4,r4) = (res,s2)` by ALL_TAC
      THEN1 (Cases_on `res4` \\ fs [] \\ Cases_on`e` \\ fs[]) \\ fs []
      \\ Q.ABBREV_TAC `env2 = (inter t2.locals (list_to_num_set (live ++ corr)))`
      \\ FIRST_X_ASSUM (qspecl_then
          [`call_env args (push_env env2 T (FUNPOW dec_clock (ticks+1) t2))`,
           `LENGTH args`,
           `GENLIST I (LENGTH args)`,`T`,`[]`]mp_tac)
      \\ FULL_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (FULL_SIMP_TAC (srw_ss()) [state_rel_def,bvpSemTheory.dec_clock_def,
          bviSemTheory.dec_clock_def,var_corr_def,get_var_def,LIST_REL_REVERSE_EQ,
          LIST_REL_lookup_fromList,lookup_fromList_outside,push_env_def,call_env_def]
          \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
          \\ `jump_exc t2 <> NONE` by FULL_SIMP_TAC std_ss []
          \\ Cases_on `jump_exc t2` \\ fs []
          \\ IMP_RES_TAC jump_exc_IMP
          \\ SIMP_TAC (srw_ss()) [jump_exc_def]
          \\ IMP_RES_TAC LAST_N_TL \\ fs [] \\ DECIDE_TAC)
      \\ STRIP_TAC \\ fs [LET_DEF]
      \\ MP_TAC (Q.SPECL [`prog`,`call_env args
         (push_env env2 T (FUNPOW dec_clock (ticks+1) t2))`]
            optimise_correct) \\ fs []
      \\ SIMP_TAC std_ss [call_env_def]
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (BasicProvers.FULL_CASE_TAC \\ fs []
        \\ REPEAT STRIP_TAC \\ fs [])
      \\ REPEAT STRIP_TAC \\ fs [GSYM ADD1,FUNPOW_SUC]
      \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) [call_env_def,COUNT_LIST_GENLIST]
      \\ FULL_SIMP_TAC std_ss []
      \\ reverse (Cases_on `x'`) \\ FULL_SIMP_TAC (srw_ss()) []
      \\ rpt BasicProvers.VAR_EQ_TAC
      \\ fs [set_var_def,state_rel_def]
      THEN1 ( Cases_on`e`>>fs[] )
      \\ `pop_env t2' = SOME (t2' with
         <| stack := t2.stack; locals := env2
          ; handler := t2.handler |>)` by ALL_TAC THEN1
       (Q.PAT_ASSUM `xx = t2'.stack` (ASSUME_TAC o GSYM)
        \\ FULL_SIMP_TAC (srw_ss()) [call_env_def,push_env_def,
           pop_env_def,bvpSemTheory.dec_clock_def,bviSemTheory.dec_clock_def])
      \\ Cases_on `tail` \\ fs [evaluate_def]
      THEN1 (fs [get_var_def,call_env_def])
      \\ IMP_RES_TAC compile_LESS_EQ
      \\ IMP_RES_TAC compile_SING_IMP
      \\ fs [] \\ IMP_RES_TAC compile_RANGE \\ fs [EVERY_DEF]
      \\ IMP_RES_TAC compile_LESS_EQ
      \\ REPEAT STRIP_TAC
      THEN1 DECIDE_TAC
      THEN1 DECIDE_TAC
      THEN1
       (UNABBREV_ALL_TAC
        \\ fs [lookup_insert,lookup_inter_alt]
        \\ `k <> t'` by DECIDE_TAC \\ fs []
        \\ REPEAT STRIP_TAC
        \\ FIRST_X_ASSUM MATCH_MP_TAC
        \\ DECIDE_TAC)
      THEN1
       (FULL_SIMP_TAC (srw_ss()) [var_corr_def,get_var_def,lookup_insert]
        \\ FULL_SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN]
        \\ REPEAT STRIP_TAC
        \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env`
        \\ RES_TAC
        \\ UNABBREV_ALL_TAC \\ fs [lookup_inter_alt]
        \\ fs [domain_lookup,lookup_list_to_num_set]
        \\ `MEM (EL l corr) corr` by METIS_TAC [MEM_EL] \\ fs []
        \\ SRW_TAC [] []
        \\ `n <= EL l corr` by DECIDE_TAC
        \\ RES_TAC \\ fs [])
      THEN1
       (FULL_SIMP_TAC (srw_ss()) [var_corr_def,get_var_def,lookup_insert]
        \\ Cases_on `k = t'` \\ FULL_SIMP_TAC std_ss []
        \\ CCONTR_TAC \\ `n2 <= k` by DECIDE_TAC
        \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
        \\ `n1 <= k` by DECIDE_TAC \\ RES_TAC
        \\ UNABBREV_ALL_TAC \\ fs [lookup_inter_alt])
      THEN1
       (FULL_SIMP_TAC (srw_ss()) [var_corr_def,get_var_def,lookup_insert]
        \\ `k <> t'` by ALL_TAC
        THEN1 (REPEAT STRIP_TAC \\ `n1 <= k` by DECIDE_TAC \\ RES_TAC \\ fs [])
        \\ fs [] \\ Cases_on `n1 <= t'` \\ RES_TAC \\ fs []
        \\ UNABBREV_ALL_TAC \\ fs [lookup_inter_alt]
        \\ fs [domain_lookup,lookup_list_to_num_set]
        \\ METIS_TAC [])
      THEN1
       (fs [] \\ fs [jump_exc_def] \\ rfs[]
        \\ Cases_on `LAST_N (t2.handler + 1) t2.stack` \\ fs []
        \\ Cases_on `h` \\ fs [])
      \\ REPEAT (FULL_SIMP_TAC (srw_ss()) [var_corr_def,get_var_def,lookup_insert,
                call_env_def,push_env_def,bvpSemTheory.dec_clock_def,
                bviSemTheory.dec_clock_def]
                 \\ FULL_SIMP_TAC (srw_ss()) [jump_exc_def]
                 \\ BasicProvers.EVERY_CASE_TAC)));

val compile_exp_lemma = compile_correct
  |> Q.SPECL [`[exp]`,`env`,`s1`,`res`,`s2`,`t1`,`n`,`GENLIST I n`,`T`,`[]`]
  |> SIMP_RULE std_ss [LENGTH,GSYM compile_exp_def,option_case_NONE_F,
       PULL_EXISTS,EVERY_DEF];

val compile_exp_correct = store_thm("compile_exp_correct",
  ``^(compile_exp_lemma |> concl |> dest_imp |> fst) ==>
    ?t2 prog vs next_var r.
      evaluate (compile_exp n exp,t1) = (SOME r,t2) /\
      state_rel s2 t2 /\ res_list r = res``,
  REPEAT STRIP_TAC \\ MP_TAC compile_exp_lemma \\ fs []
  \\ REPEAT STRIP_TAC \\ fs [compile_exp_def,LET_DEF]
  \\ MP_TAC (Q.SPECL [`prog`,`t1`] optimise_correct) \\ fs []
  \\ discharge_hyps >- (rpt strip_tac >> fs[]) >> rw[COUNT_LIST_GENLIST]);

val _ = export_theory();
