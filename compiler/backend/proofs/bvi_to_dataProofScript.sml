open preamble
     bvi_to_dataTheory
     bviSemTheory bviPropsTheory
     dataSemTheory dataPropsTheory
     data_simpProofTheory
     data_liveProofTheory
     data_spaceProofTheory;

val _ = new_theory"bvi_to_dataProof";

(* value relation *)

val code_rel_def = Define `
  code_rel bvi_code data_code <=>
    wf bvi_code /\ wf data_code /\
    (domain bvi_code = domain data_code) /\
    !n exp arg_count.
      (lookup n bvi_code = SOME (arg_count,exp)) ==>
      (lookup n data_code = SOME (arg_count,compile_exp arg_count exp))`;

val state_rel_def = Define `
  state_rel (s:'ffi bviSem$state) (t:'ffi dataSem$state) <=>
    (s.clock = t.clock) /\
    code_rel s.code t.code /\
    (s.refs = t.refs) /\
    (s.ffi = t.ffi) /\
    (s.global = t.global)`;

(* semantics lemmas *)

val find_code_def = bvlSemTheory.find_code_def;
val _ = temp_bring_to_front_overload"find_code"{Name="find_code",Thy="bvlSem"};

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

val do_app_data_to_bvi = prove(
  ``(do_app op a s1 = Rval (x0,s2)) /\ state_rel s1 t1 ==>
    (do_app op a (data_to_bvi t1) =
      Rval (x0,s2 with code := map (K ARB) t1.code))``,
  full_simp_tac(srw_ss())[state_rel_def]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[bviSemTheory.do_app_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `do_app_aux op a s1` \\ full_simp_tac(srw_ss())[]
  \\ reverse (Cases_on `x`) \\ full_simp_tac(srw_ss())[] THEN1
   (Cases_on `op` \\ full_simp_tac(srw_ss())[do_app_aux_def]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[data_to_bvi_def,bviSemTheory.state_component_equality]
    \\ Cases_on `a` \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[data_to_bvi_def,bviSemTheory.state_component_equality]
    \\ every_case_tac
    \\ full_simp_tac(srw_ss())[data_to_bvi_def,bviSemTheory.state_component_equality])
  \\ `do_app_aux op a (data_to_bvi t1) = SOME NONE` by
   (Cases_on `op` \\ full_simp_tac(srw_ss())[do_app_aux_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ `bvi_to_bvl (data_to_bvi t1) = bvi_to_bvl s1` by ALL_TAC THEN1
   (full_simp_tac(srw_ss())[bvi_to_bvl_def,data_to_bvi_def,code_rel_def,
        spt_eq_thm,lookup_map_K,domain_map,
        bvlSemTheory.state_component_equality]) \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `do_app op a (bvi_to_bvl s1)` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `a'` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[bvl_to_bvi_def,data_to_bvi_def,bviSemTheory.state_component_equality]);

(* compiler correctness *)

val optimise_correct = Q.store_thm("optimise_correct",
  `!c s. FST (evaluate (c,s)) <> SOME (Rerr(Rabort Rtype_error)) /\
         FST (evaluate (c,s)) <> NONE ==>
         (evaluate (optimise c,s) = evaluate (c,s))`,
  full_simp_tac(srw_ss())[optimise_def] \\ REPEAT STRIP_TAC \\ Cases_on `evaluate (c,s)` \\ full_simp_tac(srw_ss())[]
  \\ METIS_TAC [simp_correct,data_liveProofTheory.compile_correct,data_spaceProofTheory.compile_correct,FST]);

val compile_RANGE_lemma = prove(
  ``!n env tail live xs.
      EVERY (\v. n <= v /\ v < (SND (SND (compile n env tail live xs))))
        (FST (SND (compile n env tail live xs)))``,
  HO_MATCH_MP_TAC compile_ind \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [compile_def] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ IMP_RES_TAC compile_SING_IMP
  \\ full_simp_tac(srw_ss())[EVERY_MEM]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ IMP_RES_TAC compile_LESS_EQ
  \\ TRY (Cases_on `tail`) \\ full_simp_tac(srw_ss())[] \\ DECIDE_TAC);

val compile_RANGE = prove(
  ``(compile n env tail live xs = (ys,vs,k)) ==> EVERY (\v. n <= v /\ v < k) vs``,
  REPEAT STRIP_TAC \\ MP_TAC (compile_RANGE_lemma |> SPEC_ALL) \\ full_simp_tac(srw_ss())[]);

val _ = temp_overload_on("res_list",``map_result (λv. [v]) I``);
val _ = temp_overload_on("isException",``λx. ∃v. x = Rerr(Rraise v)``);
val _ = temp_overload_on("isResult",``λx. ∃v. x = Rval v``);

val RW = REWRITE_RULE;

val compile_correct = Q.prove(
  `!xs env s1 res s2 t1 n corr tail live.
     (evaluate (xs,env,s1) = (res,s2)) /\ res <> Rerr(Rabort Rtype_error) /\
     var_corr env corr t1.locals /\ (LENGTH xs <> 1 ==> ~tail) /\
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
                  var_corr env corr t2.locals /\
                  (!k x. (lookup k t2.locals = SOME x) ==> k < next_var) /\
                  (!k x. (lookup k t1.locals = SOME x) /\
                         (~MEM k live ==> MEM k corr) ==>
                         (lookup k t2.locals = SOME x)) /\
                  (t1.stack = t2.stack) /\ (t1.handler = t2.handler) /\
                  (jump_exc t1 <> NONE ==> jump_exc t2 <> NONE) /\
                  case res of
                  | Rval xs => var_corr xs vs t2.locals
                  | _ => F)`,
  SIMP_TAC std_ss [Once EQ_SYM_EQ]
  \\ recInduct bviSemTheory.evaluate_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [compile_def,dataSemTheory.evaluate_def,bviSemTheory.evaluate_def]
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
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ Cases_on `pres` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `evaluate (y::xs,env,r)`
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n1`,`corr`,`F`,`HD v1::live`])
    \\ simp[]
    \\ `EVERY (\n. lookup n t2.locals <> NONE) (HD v1::live)` by
     (IMP_RES_TAC evaluate_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
      \\ IMP_RES_TAC compile_SING_IMP \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def]
      \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
      \\ Cases_on `lookup n' t1.locals` \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [])
    \\ full_simp_tac(srw_ss())[] \\ strip_tac
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
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[jump_exc_NONE])
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
      \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[] >> strip_tac
      \\ Cases_on `pres`
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ IMP_RES_TAC evaluate_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
      \\ IMP_RES_TAC compile_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
      \\ SRW_TAC [] []
      \\ Q.MATCH_ASSUM_RENAME_TAC `var_corr [w] [n5] t2.locals`
      \\ `get_var n5 t2.locals = SOME w` by FULL_SIMP_TAC (srw_ss()) [var_corr_def]
      \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [LET_DEF]
      \\ CONV_TAC (DEPTH_CONV (DEPTH_CONV PairRules.PBETA_CONV))
      \\ IMP_RES_TAC compile_LESS_EQ
      \\ `EVERY (\n. lookup n t2.locals <> NONE) live` by
        (full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
         \\ Cases_on `lookup n' t1.locals` \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [])
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
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[] >> strip_tac
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC evaluate_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC compile_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SRW_TAC [] []
    \\ Q.MATCH_ASSUM_RENAME_TAC `var_corr [w] [n5] t2.locals`
    \\ `get_var n5 t2.locals = SOME w` by FULL_SIMP_TAC (srw_ss()) [var_corr_def]
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [LET_DEF]
    \\ CONV_TAC (DEPTH_CONV (DEPTH_CONV PairRules.PBETA_CONV))
    \\ IMP_RES_TAC compile_LESS_EQ
    \\ `EVERY (\n. lookup n t2.locals <> NONE) live` by
      (full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
       \\ Cases_on `lookup n' t1.locals` \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [])
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
      \\ Q.MATCH_ASSUM_RENAME_TAC `var_corr [w7] [n7] (_ t7)`
      \\ `get_var n7 t7.locals = SOME w7` by FULL_SIMP_TAC (srw_ss()) [var_corr_def]
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
      \\ Q.MATCH_ASSUM_RENAME_TAC `var_corr [w7] [n7] (_ t7)`
      \\ `get_var n7 t7.locals = SOME w7` by FULL_SIMP_TAC (srw_ss()) [var_corr_def]
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
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[] >> strip_tac
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Q.PAT_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ `var_corr (a ++ env) (vs ++ corr) t2.locals` by
     (FULL_SIMP_TAC (srw_ss()) [var_corr_def]
      \\ MATCH_MP_TAC (GEN_ALL EVERY2_APPEND_suff)
      \\ FULL_SIMP_TAC std_ss [LIST_REL_REVERSE_EQ])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`n1`,
         `vs ++ corr`,`tail`,`live`])
    \\ `EVERY (\n. lookup n t2.locals <> NONE) live` by
      (full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
       \\ Cases_on `lookup n' t1.locals` \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [])
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
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[] >> strip_tac
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC evaluate_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC compile_SING_IMP \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SRW_TAC [] []
    \\ `get_var t t2.locals = SOME w` by full_simp_tac(srw_ss())[var_corr_def]
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `jump_exc t2` \\ full_simp_tac(srw_ss())[]
    \\ FULL_SIMP_TAC std_ss [state_rel_def]
    \\ IMP_RES_TAC jump_exc_IMP \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[jump_exc_def])
  THEN1 (* Op *)
   (`?c1 vs n1. compile n corr F live xs = (c1,vs,n1)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,evaluate_def]
    \\ Cases_on `evaluate (xs,env,s)`
    \\ reverse (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[] >> strip_tac
    \\ Cases_on `pres`
    \\ FULL_SIMP_TAC (srw_ss()) []
    THEN1 SRW_TAC [] [evaluate_def]
    \\ `domain (list_to_num_set (REVERSE vs ++ live ++ corr)) SUBSET
        domain t2.locals` by
     (full_simp_tac(srw_ss())[SUBSET_DEF,domain_lookup,lookup_list_to_num_set,EVERY_MEM]
      \\ REPEAT STRIP_TAC \\ RES_TAC
      \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def]
      \\ IMP_RES_TAC MEM_LIST_REL \\ full_simp_tac(srw_ss())[]
      \\ `lookup x t1.locals <> NONE` by METIS_TAC []
      \\ Cases_on `lookup x t1.locals` \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [])
    \\ full_simp_tac(srw_ss())[]
    \\ Q.ABBREV_TAC `env1 = mk_wf (inter t2.locals (list_to_num_set (REVERSE vs++live++corr)))`
    \\ `var_corr (REVERSE a) (REVERSE vs) env1` by
     (UNABBREV_ALL_TAC
      \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def,state_rel_def,
             lookup_inter_EQ,lookup_list_to_num_set]
      \\ Q.PAT_ASSUM `LIST_REL rrr xs1 xs2` MP_TAC
      \\ ONCE_REWRITE_TAC [LIST_REL_MEM]
      \\ full_simp_tac(srw_ss())[EVERY2_REVERSE] \\ NO_TAC)
    \\ IMP_RES_TAC get_vars_thm
    \\ `state_rel r (t2 with <|locals := env1; space := 0|>)` by
          (full_simp_tac(srw_ss())[state_rel_def] \\ NO_TAC)
    \\ reverse(Cases_on `do_app op (REVERSE a) r`) \\ full_simp_tac(srw_ss())[] >- (
         imp_res_tac bviPropsTheory.do_app_err >> full_simp_tac(srw_ss())[] )
    \\ PairCases_on `a'` \\ full_simp_tac(srw_ss())[] \\ REV_FULL_SIMP_TAC std_ss []
    \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[LET_DEF,evaluate_def,iAssign_def]
    \\ (fn (hs,goal) => (reverse (`let tail = F in ^goal` by ALL_TAC))
           (hs,goal)) THEN1
     (full_simp_tac(srw_ss())[LET_DEF]
      \\ reverse (Cases_on `tail`) THEN1 METIS_TAC []
      \\ full_simp_tac(srw_ss())[evaluate_def,LET_DEF] \\ REV_FULL_SIMP_TAC std_ss []
      \\ Cases_on `pres` \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[var_corr_def,call_env_def,state_rel_def])
    \\ simp[]
    \\ IMP_RES_TAC do_app_data_to_bvi \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `op_requires_names op`
    \\ full_simp_tac(srw_ss())[evaluate_def,cut_state_opt_def,
           cut_state_def,cut_env_def,op_requires_names_def]
    \\ full_simp_tac(srw_ss())[dataSemTheory.do_app_def,do_space_def]
    \\ simp[]
    \\ full_simp_tac(srw_ss())[get_var_def,set_var_def]
    \\ full_simp_tac(srw_ss())[call_env_def,bvi_to_data_def]
    \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ IMP_RES_TAC do_app_code \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC compile_LESS_EQ \\ full_simp_tac(srw_ss())[lookup_insert]
    \\ TRY(qmatch_assum_rename_tac`op = FFI _`
           \\ fs[op_space_reset_def,data_spaceTheory.op_space_req_def,data_to_bvi_ignore])
    THEN1
     (REPEAT STRIP_TAC
      THEN1 (SRW_TAC [] [] THEN1 DECIDE_TAC
         \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[lookup_inter_EQ]
         \\ `n1 <= k` by DECIDE_TAC \\ full_simp_tac(srw_ss())[])
      THEN1 (full_simp_tac(srw_ss())[LIST_REL_EL_EQN,var_corr_def,
                get_var_def,lookup_insert]
        \\ REPEAT STRIP_TAC
        \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env`
        \\ `EL l corr <> n1` by ALL_TAC \\ FULL_SIMP_TAC std_ss []
        \\ `n1 <= n1 /\ l < LENGTH corr` by DECIDE_TAC
        \\ `lookup n1 t2.locals = NONE` by METIS_TAC []
        \\ RES_TAC \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
        \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,
              lookup_list_to_num_set]
        \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [MEM_EL])
      THEN1 (Cases_on `k = n1` \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
        \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,
               lookup_list_to_num_set]
        \\ RES_TAC \\ DECIDE_TAC)
      THEN1
        (`k <> n1` by (REPEAT STRIP_TAC \\ RES_TAC
                       \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
         \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
         \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,
              lookup_list_to_num_set]
         \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[])
      THEN1 (POP_ASSUM MP_TAC \\ Cases_on `jump_exc t1` \\ full_simp_tac(srw_ss())[]
         \\ IMP_RES_TAC jump_exc_IMP
         \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
         \\ full_simp_tac(srw_ss())[jump_exc_def])
      \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def])
    THEN1 (
      rw[lookup_insert,var_corr_def,get_var_def,Abbr`env1`,lookup_inter_EQ]
      \\ fs[var_corr_def,LIST_REL_EL_EQN,get_var_def] \\ rw[lookup_inter_EQ]
      \\ fs[lookup_list_to_num_set] \\ res_tac \\ fs[jump_exc_NONE]
      \\ fs[jump_exc_def] \\ every_case_tac \\ fs[]
      \\ METIS_TAC[MEM_EL] )
    \\ imp_res_tac get_vars_reverse
    \\ imp_res_tac get_vars_IMP_LENGTH \\ full_simp_tac (srw_ss()) []
    \\ Cases_on `op_space_req op (LENGTH vs) = 0`
    \\ full_simp_tac(srw_ss())[evaluate_def,op_requires_names_def]
    \\ full_simp_tac(srw_ss())[evaluate_def,cut_state_opt_def,
          cut_state_def,cut_env_def]
    \\ full_simp_tac(srw_ss())[dataSemTheory.do_app_def,do_space_def,LET_DEF]
    \\ IMP_RES_TAC do_app_data_to_bvi \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[get_var_def,set_var_def]
    \\ full_simp_tac(srw_ss())[call_env_def,bvi_to_data_def]
    \\ full_simp_tac(srw_ss())[state_rel_def] \\ IMP_RES_TAC do_app_code
    \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC compile_LESS_EQ \\ full_simp_tac(srw_ss())[lookup_insert]
    THEN1
     (REPEAT STRIP_TAC
      THEN1 (SRW_TAC [] [] THEN1 DECIDE_TAC
         \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[lookup_inter_EQ]
         \\ `n1 <= k` by DECIDE_TAC \\ full_simp_tac(srw_ss())[])
      THEN1 (full_simp_tac(srw_ss())[LIST_REL_EL_EQN,
               var_corr_def,get_var_def,lookup_insert]
        \\ REPEAT STRIP_TAC
        \\ rename1 `l1 < LENGTH corr`
        \\ `EL l1 corr <> n1` by ALL_TAC \\ FULL_SIMP_TAC std_ss []
        \\ `n1 <= n1 /\ l1 < LENGTH corr` by DECIDE_TAC
        \\ `lookup n1 t2.locals = NONE` by METIS_TAC []
        \\ RES_TAC \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
        \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,
             lookup_list_to_num_set]
        \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [MEM_EL])
      THEN1 (Cases_on `k = n1` \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
        \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,
              lookup_list_to_num_set]
        \\ RES_TAC \\ DECIDE_TAC)
      THEN1
        (`k <> n1` by (REPEAT STRIP_TAC \\ RES_TAC
                       \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
         \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
         \\ full_simp_tac(srw_ss())[lookup_insert,
               lookup_inter_EQ,lookup_list_to_num_set]
         \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[])
      THEN1 (POP_ASSUM MP_TAC \\ Cases_on `jump_exc t1` \\ full_simp_tac(srw_ss())[]
         \\ IMP_RES_TAC jump_exc_IMP
         \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
         \\ full_simp_tac(srw_ss())[jump_exc_def])
      \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def])
    \\ full_simp_tac(srw_ss())[consume_space_add_space,lookup_insert]
    THEN1
     (REPEAT STRIP_TAC
      THEN1 (SRW_TAC [] [] THEN1 DECIDE_TAC
         \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[lookup_inter_EQ]
         \\ `n1 <= k` by DECIDE_TAC \\ full_simp_tac(srw_ss())[])
      THEN1 (full_simp_tac(srw_ss())[LIST_REL_EL_EQN,var_corr_def,get_var_def,lookup_insert]
        \\ REPEAT STRIP_TAC
        \\ Q.MATCH_ASSUM_RENAME_TAC `l1 < LENGTH corr`
        \\ `EL l1 corr <> n1` by ALL_TAC \\ FULL_SIMP_TAC std_ss []
        \\ `n1 <= n1 /\ l1 < LENGTH corr` by DECIDE_TAC
        \\ `lookup n1 t2.locals = NONE` by METIS_TAC []
        \\ RES_TAC \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
        \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,lookup_list_to_num_set]
        \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [MEM_EL])
      THEN1 (Cases_on `k = n1` \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
        \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,lookup_list_to_num_set]
        \\ RES_TAC \\ DECIDE_TAC)
      THEN1
        (`k <> n1` by (REPEAT STRIP_TAC \\ RES_TAC \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
         \\ full_simp_tac(srw_ss())[] \\ UNABBREV_ALL_TAC
         \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_EQ,lookup_list_to_num_set]
         \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[])
      THEN1 (POP_ASSUM MP_TAC \\ Cases_on `jump_exc t1` \\ full_simp_tac(srw_ss())[]
         \\ IMP_RES_TAC jump_exc_IMP
         \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC \\ full_simp_tac(srw_ss())[jump_exc_def])
      \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def]))
  THEN1 (* Tick *)
   (`?c1 v1 n1. compile n corr tail live [x] = (c1,v1,n1)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,evaluate_def]
    \\ Cases_on `t1.clock = 0` \\ FULL_SIMP_TAC std_ss []
    THEN1 (full_simp_tac(srw_ss())[state_rel_def,call_env_def])
    \\ `s.clock <> 0` by ALL_TAC
    THEN1 (FULL_SIMP_TAC std_ss [state_rel_def])
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`dec_clock t1`,`n`,`corr`,`tail`,`live`])
    \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [var_corr_def,dataSemTheory.dec_clock_def,
         get_var_def,state_rel_def,bviSemTheory.dec_clock_def,jump_exc_NONE])
  THEN1 (* Call *)
   (Cases_on `handler` THEN1 (* Call without handler *)
     (`?c1 vs n1. compile n corr F live xs = (c1,vs,n1)` by METIS_TAC [PAIR]
      \\ FULL_SIMP_TAC std_ss [LET_DEF,evaluate_def,call_env_def,compile_def,
           evaluate_mk_ticks]
      \\ Cases_on `evaluate (xs,env,s1)`
      \\ reverse (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
      \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[]>> strip_tac
      \\ Cases_on `pres`
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ Cases_on `find_code dest a r.code` \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss []
      \\ Q.MATCH_ASSUM_RENAME_TAC `find_code dest a r.code = SOME (args,exp)`
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ `t2.clock = r.clock` by FULL_SIMP_TAC std_ss [state_rel_def]
      \\ `get_vars vs t2.locals = SOME a` by IMP_RES_TAC get_vars_thm
      \\ FULL_SIMP_TAC std_ss []
      \\ IMP_RES_TAC find_code_lemma
      \\ FULL_SIMP_TAC (srw_ss()) [] \\ POP_ASSUM (K ALL_TAC)
      \\ `domain (list_to_num_set (live ++ corr)) SUBSET domain t2.locals` by
       (full_simp_tac(srw_ss())[SUBSET_DEF,domain_lookup,lookup_list_to_num_set,EVERY_MEM]
        \\ REPEAT STRIP_TAC \\ RES_TAC THEN1
         (`lookup x t1.locals <> NONE` by METIS_TAC []
            \\ Cases_on `lookup x t1.locals` \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [])
        \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def]
        \\ IMP_RES_TAC MEM_LIST_REL \\ full_simp_tac(srw_ss())[])
      \\ full_simp_tac(srw_ss())[] \\ Cases_on `r.clock < ticks + 1` \\ full_simp_tac(srw_ss())[] THEN1
       (`r.clock < ticks \/ r.clock = ticks` by decide_tac \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[state_rel_def, funpow_dec_clock_clock]
        \\ Cases_on `tail` \\ full_simp_tac(srw_ss())[state_rel_def, funpow_dec_clock_clock]
        \\ full_simp_tac(srw_ss())[cut_env_def])
      \\ `~(r.clock < ticks)` by decide_tac \\ full_simp_tac(srw_ss())[]
      \\ `(FUNPOW dec_clock ticks t2).clock ≠ 0` by simp [funpow_dec_clock_clock]
      \\ full_simp_tac(srw_ss())[]
      \\ FULL_SIMP_TAC std_ss [compile_exp_def]
      \\ Q.PAT_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `tail` THEN1
       (`evaluate ([exp],args,dec_clock (ticks + 1) r) = (res,s2)` by ALL_TAC THEN1
        (Cases_on `evaluate ([exp],args,dec_clock (ticks+1) r)` \\ full_simp_tac(srw_ss())[]
           \\ Cases_on `q` \\ full_simp_tac(srw_ss())[] \\
           Cases_on`e` >> full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
        \\ FIRST_X_ASSUM (qspecl_then
             [`call_env args (FUNPOW dec_clock (ticks+1) t2)`,
               `LENGTH args`,
               `GENLIST I (LENGTH args)`,`T`,`[]`]mp_tac)
        \\ FULL_SIMP_TAC std_ss []
        \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
         (FULL_SIMP_TAC (srw_ss()) [state_rel_def,dataSemTheory.dec_clock_def,
          bviSemTheory.dec_clock_def,var_corr_def,get_var_def,LIST_REL_REVERSE_EQ,
          LIST_REL_lookup_fromList,lookup_fromList_outside,jump_exc_NONE,call_env_def,
          funpow_dec_clock_clock])
        \\ STRIP_TAC \\ full_simp_tac(srw_ss())[LET_DEF]
        \\ MP_TAC (Q.SPECL [`prog`,
            `call_env args (FUNPOW dec_clock (ticks+1) t2)`] optimise_correct)
        \\ full_simp_tac(srw_ss())[] \\ SIMP_TAC std_ss [call_env_def]
        \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
         (BasicProvers.FULL_CASE_TAC \\ full_simp_tac(srw_ss())[funpow_dec_clock_clock]
          \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[])
        \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[COUNT_LIST_GENLIST]
        \\ full_simp_tac(srw_ss())[FUNPOW_dec_clock_code]
        \\ full_simp_tac(srw_ss())[GSYM ADD1,FUNPOW_SUC]
        \\ Cases_on `pres` \\ full_simp_tac(srw_ss())[] \\ FULL_SIMP_TAC std_ss []
        \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
        \\ FULL_SIMP_TAC (srw_ss()) [call_env_def,
           bviSemTheory.dec_clock_def,dataSemTheory.dec_clock_def]
        \\ REV_FULL_SIMP_TAC (srw_ss()) [FUNPOW_dec_clock_code])
      \\ full_simp_tac(srw_ss())[cut_env_def]
      \\ `evaluate ([exp],args,dec_clock (ticks + 1) r) = (res,s2)` by ALL_TAC THEN1
       (Cases_on `evaluate ([exp],args,dec_clock (ticks + 1) r)` \\ full_simp_tac(srw_ss())[]
        \\ Cases_on `q` \\ full_simp_tac(srw_ss())[]
        \\ Cases_on`e` \\ full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
      \\ Q.ABBREV_TAC `env2 = (inter t2.locals (list_to_num_set (live ++ corr)))`
      \\ FIRST_X_ASSUM (qspecl_then
          [`call_env args (push_env env2 F (FUNPOW dec_clock (ticks + 1) t2))`,
           `LENGTH args`,
           `GENLIST I (LENGTH args)`,`T`,`[]`]mp_tac)
      \\ FULL_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (FULL_SIMP_TAC (srw_ss()) [state_rel_def,dataSemTheory.dec_clock_def,
          bviSemTheory.dec_clock_def,var_corr_def,get_var_def,LIST_REL_REVERSE_EQ,
          LIST_REL_lookup_fromList,lookup_fromList_outside,push_env_def,
          call_env_def,FUNPOW_dec_clock_code]
          \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
          \\ `jump_exc t2 <> NONE` by full_simp_tac(srw_ss())[]
          \\ Cases_on `jump_exc t2` \\ full_simp_tac(srw_ss())[]
          \\ IMP_RES_TAC jump_exc_IMP
          \\ SIMP_TAC (srw_ss()) [jump_exc_def,FUNPOW_dec_clock_code]
          \\ IMP_RES_TAC LASTN_TL \\ full_simp_tac(srw_ss())[]
          \\ DECIDE_TAC)
      \\ STRIP_TAC \\ full_simp_tac(srw_ss())[LET_DEF]
      \\ MP_TAC (Q.SPECL [`prog`,`call_env args
         (push_env env2 F (FUNPOW dec_clock (ticks + 1) t2))`]
            optimise_correct) \\ full_simp_tac(srw_ss())[]
      \\ SIMP_TAC std_ss [call_env_def]
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (BasicProvers.FULL_CASE_TAC \\ full_simp_tac(srw_ss())[]
        \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[])
      \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[FUNPOW_dec_clock_code,COUNT_LIST_GENLIST]
      \\ full_simp_tac(srw_ss())[GSYM ADD1,FUNPOW_SUC]
      \\ Cases_on `pres` \\ full_simp_tac(srw_ss())[call_env_def]
      \\ `~(r.clock ≤ ticks)` by DECIDE_TAC \\ full_simp_tac(srw_ss())[]
      \\ reverse (Cases_on `x`) \\ FULL_SIMP_TAC (srw_ss()) []
      \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[]
      THEN1
       (Cases_on`e`>>full_simp_tac(srw_ss())[]>>
        IMP_RES_TAC jump_exc_IMP
        \\ FULL_SIMP_TAC (srw_ss()) [call_env_def,push_env_def,
           dataSemTheory.dec_clock_def,bviSemTheory.dec_clock_def]
        \\ SIMP_TAC (srw_ss()) [jump_exc_def]
        \\ full_simp_tac(srw_ss())[FUNPOW_dec_clock_code]
        \\ Cases_on `t2.handler = LENGTH t2.stack` THEN1
         (FULL_SIMP_TAC std_ss [Q.SPEC `x::xs` LASTN_LENGTH_ID
             |> SIMP_RULE std_ss [LENGTH,ADD1]] \\ full_simp_tac(srw_ss())[])
        \\ `t2.handler < LENGTH t2.stack` by DECIDE_TAC
        \\ FULL_SIMP_TAC std_ss []
        \\ IMP_RES_TAC LASTN_TL
        \\ FULL_SIMP_TAC (srw_ss()) [])
      \\ `pop_env t2' = SOME (t2' with
         <| stack := t2.stack; locals := env2 |>)` by ALL_TAC THEN1
       (Q.PAT_ASSUM `xx = t2'.stack` (ASSUME_TAC o GSYM)
        \\ FULL_SIMP_TAC (srw_ss()) [call_env_def,push_env_def,
             pop_env_def,dataSemTheory.dec_clock_def,bviSemTheory.dec_clock_def,
             FUNPOW_dec_clock_code])
      \\ full_simp_tac(srw_ss())[set_var_def,state_rel_def]
      \\ IMP_RES_TAC compile_LESS_EQ
      \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC
      THEN1
       (UNABBREV_ALL_TAC
        \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter]
        \\ SRW_TAC [] [] THEN1 DECIDE_TAC
        \\ `lookup k t2.locals = NONE` by ALL_TAC \\ full_simp_tac(srw_ss())[]
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
        \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[lookup_inter]
        \\ POP_ASSUM MP_TAC \\ full_simp_tac(srw_ss())[]
        \\ `MEM (EL l corr) corr` by METIS_TAC [MEM_EL]
        \\ full_simp_tac(srw_ss())[lookup_list_to_num_set])
      THEN1
       (FULL_SIMP_TAC (srw_ss()) [var_corr_def,get_var_def,lookup_insert]
        \\ Cases_on `k = n1` \\ FULL_SIMP_TAC std_ss []
        \\ CCONTR_TAC \\ `n1 <= k` by DECIDE_TAC
        \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
        \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[lookup_inter])
      THEN1
       (`lookup k t2.locals = SOME x` by
          (FIRST_X_ASSUM MATCH_MP_TAC \\ full_simp_tac(srw_ss())[])
        \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[lookup_inter,lookup_insert]
        \\ `lookup k (list_to_num_set (live ++ corr)) = SOME ()` by
           (full_simp_tac(srw_ss())[lookup_list_to_num_set] \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[])
        \\ `k <> n1` by ALL_TAC \\ full_simp_tac(srw_ss())[] \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[]
        \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
      \\ REPEAT (FULL_SIMP_TAC (srw_ss()) [var_corr_def,get_var_def,lookup_insert,
                call_env_def,push_env_def,dataSemTheory.dec_clock_def,
                bviSemTheory.dec_clock_def]
                 \\ FULL_SIMP_TAC (srw_ss()) [jump_exc_def]
                 \\ BasicProvers.EVERY_CASE_TAC))
    \\ (* Call with handle *)
      `?c1 vs n1. compile n corr F live xs = (c1,vs,n1)` by METIS_TAC [PAIR]
      \\ `?c2 v n2. compile (n1+1) (n1::corr) F live [x] = (c2,v,n2)` by
            METIS_TAC [PAIR]
      \\ full_simp_tac(srw_ss())[LET_DEF,evaluate_def,evaluate_mk_ticks,call_env_def,compile_def]
      \\ Cases_on `evaluate (xs,env,s1)`
      \\ Cases_on `dest = NONE` \\ full_simp_tac(srw_ss())[]
      \\ reverse (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`n`,`corr`,`F`,`live`])
      \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[]>> strip_tac
      \\ Cases_on `pres`
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ Cases_on `find_code dest a r.code` \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `x'` \\ FULL_SIMP_TAC std_ss []
      \\ Q.MATCH_ASSUM_RENAME_TAC `find_code dest a r.code = SOME (args,exp)`
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ `t2.clock = r.clock` by FULL_SIMP_TAC std_ss [state_rel_def]
      \\ `domain (list_to_num_set (live ++ corr)) SUBSET domain t2.locals` by
       (full_simp_tac(srw_ss())[SUBSET_DEF,domain_lookup,lookup_list_to_num_set,EVERY_MEM]
        \\ REPEAT STRIP_TAC \\ RES_TAC THEN1
         (`lookup x' t1.locals <> NONE` by METIS_TAC []
          \\ Cases_on `lookup x' t1.locals` \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [])
        \\ full_simp_tac(srw_ss())[var_corr_def,get_var_def]
        \\ IMP_RES_TAC MEM_LIST_REL \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
      \\ IMP_RES_TAC find_code_lemma
      \\ FULL_SIMP_TAC (srw_ss()) [] \\ POP_ASSUM (K ALL_TAC)
      \\ `get_vars vs t2.locals = SOME a` by IMP_RES_TAC get_vars_thm
      \\ full_simp_tac(srw_ss())[] \\ Cases_on `r.clock < ticks + 1` \\ full_simp_tac(srw_ss())[] THEN1
       (`r.clock < ticks \/ r.clock = ticks` by decide_tac \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[state_rel_def, funpow_dec_clock_clock]
        \\ Cases_on `tail` \\ full_simp_tac(srw_ss())[state_rel_def, funpow_dec_clock_clock]
        \\ full_simp_tac(srw_ss())[cut_env_def])
      \\ `~(r.clock < ticks)` by decide_tac \\ full_simp_tac(srw_ss())[]
      \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [compile_exp_def]
      \\ `~(r.clock < ticks) /\ ~(r.clock ≤ ticks)` by DECIDE_TAC \\ full_simp_tac(srw_ss())[]
      \\ Q.PAT_ASSUM `(res,s2) = bb` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss []
      \\ full_simp_tac(srw_ss())[cut_env_def]
      \\ Cases_on `evaluate ([exp],args,dec_clock (ticks + 1) r)`
      \\ Q.MATCH_ASSUM_RENAME_TAC
            `evaluate ([exp],args,dec_clock (ticks + 1) r) = (res4,r4)`
      \\ Cases_on `isException res4` THEN1
       (Cases_on `res4` \\ full_simp_tac(srw_ss())[LET_DEF] \\ full_simp_tac(srw_ss())[]
        \\ Q.ABBREV_TAC `env2 = (inter t2.locals (list_to_num_set (live ++ corr)))`
        \\ FIRST_X_ASSUM (qspecl_then
            [`call_env args (push_env env2 T (FUNPOW dec_clock (ticks+1) t2))`,
             `LENGTH args`,
             `GENLIST I (LENGTH args)`,`T`,`[]`] mp_tac)
        \\ FULL_SIMP_TAC std_ss []
        \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
         (FULL_SIMP_TAC (srw_ss()) [state_rel_def,dataSemTheory.dec_clock_def,
            bviSemTheory.dec_clock_def,var_corr_def,get_var_def,LIST_REL_REVERSE_EQ,
            LIST_REL_lookup_fromList,lookup_fromList_outside,push_env_def,call_env_def]
          \\ full_simp_tac(srw_ss())[jump_exc_def,LASTN_LENGTH_ID |> Q.SPEC `x::xs` |> RW [LENGTH,ADD1]])
        \\ REPEAT STRIP_TAC
        \\ Cases_on `pres` \\ full_simp_tac(srw_ss())[]
        \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
        \\ MP_TAC (Q.SPECL [`prog`,`call_env args
           (push_env env2 T (FUNPOW dec_clock (ticks+1) t2))`]
              optimise_correct) \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[COUNT_LIST_GENLIST]
        \\ SIMP_TAC std_ss [call_env_def] \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
        \\ Cases_on `evaluate (c2,set_var n1 v' t2')` \\ full_simp_tac(srw_ss())[]
        \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL
              [`set_var n1 v' t2'`,`n1+1`,`n1::corr`,`F`,`live`]) \\ full_simp_tac(srw_ss())[]
        \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
         (full_simp_tac(srw_ss())[var_corr_def,state_rel_def,set_var_def,lookup_insert,get_var_def]
          \\ full_simp_tac(srw_ss())[jump_exc_def,call_env_def,push_env_def,dataSemTheory.dec_clock_def]
          \\ full_simp_tac(srw_ss())[jump_exc_def,LASTN_LENGTH_ID |> Q.SPEC `x::xs` |> RW [LENGTH,ADD1]]
          \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality]
          \\ Q.PAT_ASSUM `env2 = t2'.locals` (ASSUME_TAC o GSYM) \\ full_simp_tac(srw_ss())[]
          \\ Q.UNABBREV_TAC `env2` \\ full_simp_tac(srw_ss())[lookup_inter_alt]
          \\ full_simp_tac(srw_ss())[domain_lookup,lookup_list_to_num_set]
          \\ REPEAT STRIP_TAC THEN1
           (full_simp_tac(srw_ss())[LIST_REL_EL_EQN] \\ REPEAT STRIP_TAC
            \\ Q.MATCH_ASSUM_RENAME_TAC `n3 < LENGTH env`
            \\ `MEM (EL n3 corr) corr` by METIS_TAC [MEM_EL] \\ full_simp_tac(srw_ss())[]
            \\ SRW_TAC [] []
            \\ `EL n3 corr <= EL n3 corr` by full_simp_tac(srw_ss())[] \\ RES_TAC \\ full_simp_tac(srw_ss())[])
          THEN1 (`k <> n1 /\ n1 <= k` by DECIDE_TAC \\ full_simp_tac(srw_ss())[])
          THEN1
           (full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC
            \\ Cases_on `n' = n1` \\ RES_TAC \\ full_simp_tac(srw_ss())[]
            \\ Cases_on `lookup n' t1.locals` \\ full_simp_tac(srw_ss())[]
            \\ RES_TAC \\ full_simp_tac(srw_ss())[] \\ Cases_on `lookup n' t2.locals` \\ full_simp_tac(srw_ss())[])
          \\ Cases_on `LASTN (t2'.handler + 1) t2'.stack` \\ full_simp_tac(srw_ss())[]
          \\ Cases_on `h` \\ full_simp_tac(srw_ss())[])
        \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[GSYM ADD1, FUNPOW_SUC]
        \\ reverse (Cases_on `q`) \\ full_simp_tac(srw_ss())[] THEN1
         (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[set_var_def,jump_exc_def,call_env_def,
            push_env_def,dataSemTheory.dec_clock_def]
          \\ full_simp_tac(srw_ss())[jump_exc_def,LASTN_LENGTH_ID |> Q.SPEC `x::xs` |> RW [LENGTH,ADD1]]
          \\ NTAC 2 (POP_ASSUM MP_TAC)
          \\ Q.PAT_ASSUM `xxx = t2'` (fn th => ONCE_REWRITE_TAC [GSYM th]) \\ full_simp_tac(srw_ss())[])
        \\ Cases_on `res` \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]
        \\ `(t2'.stack = t2.stack) /\ (t2'.handler = t2.handler)` by ALL_TAC THEN1
         (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[set_var_def,jump_exc_def,call_env_def,
            push_env_def,dataSemTheory.dec_clock_def]
          \\ full_simp_tac(srw_ss())[jump_exc_def,LASTN_LENGTH_ID |> Q.SPEC `x::xs` |> RW [LENGTH,ADD1]]
          \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality])
        \\ Cases_on `tail` \\ full_simp_tac(srw_ss())[evaluate_def]
        THEN1
         (IMP_RES_TAC compile_LENGTH
          \\ `?v1. v = [v1]` by (Cases_on `v` \\ full_simp_tac(srw_ss())[LENGTH_NIL])
          \\ full_simp_tac(srw_ss())[var_corr_def,set_var_def,call_env_def]
          \\ full_simp_tac(srw_ss())[state_rel_def])
        \\ REPEAT STRIP_TAC
        THEN1 DECIDE_TAC
        THEN1
         (IMP_RES_TAC compile_RANGE \\ full_simp_tac(srw_ss())[EVERY_MEM]
          \\ REPEAT STRIP_TAC \\ RES_TAC \\ DECIDE_TAC)
        THEN1 (full_simp_tac(srw_ss())[var_corr_def])
        THEN1
         (FIRST_X_ASSUM MATCH_MP_TAC \\ reverse STRIP_TAC THEN1 METIS_TAC []
          \\ full_simp_tac(srw_ss())[set_var_def,lookup_insert]
          \\ `k <> n1` by ALL_TAC \\ full_simp_tac(srw_ss())[] THEN1
           (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
            \\ `n <= n1` by DECIDE_TAC \\ RES_TAC \\ full_simp_tac(srw_ss())[])
          \\ UNABBREV_ALL_TAC
          \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[set_var_def,jump_exc_def,call_env_def,
            push_env_def,dataSemTheory.dec_clock_def]
          \\ full_simp_tac(srw_ss())[jump_exc_def,LASTN_LENGTH_ID |> Q.SPEC `x::xs` |> RW [LENGTH,ADD1]]
          \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality]
          \\ Q.PAT_ASSUM `xxx = t2'.locals` (ASSUME_TAC o GSYM)
          \\ full_simp_tac(srw_ss())[lookup_inter_alt]
          \\ full_simp_tac(srw_ss())[domain_lookup,lookup_list_to_num_set] \\ METIS_TAC [])
        \\ full_simp_tac(srw_ss())[set_var_def]
        \\ full_simp_tac(srw_ss())[jump_exc_def]
        \\ Cases_on `LASTN (t1.handler + 1) t1.stack` \\ full_simp_tac(srw_ss())[]
        \\ Cases_on `h` \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[call_env_def,push_env_def,dataSemTheory.dec_clock_def]
        \\ Cases_on `LASTN (r'.handler + 1) r'.stack` \\ full_simp_tac(srw_ss())[]
        \\ Cases_on `h` \\ full_simp_tac(srw_ss())[])
      \\ `(res4,r4) = (res,s2)` by ALL_TAC
      THEN1 (Cases_on `res4` \\ full_simp_tac(srw_ss())[] \\ Cases_on`e` \\ full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
      \\ Q.ABBREV_TAC `env2 = (inter t2.locals (list_to_num_set (live ++ corr)))`
      \\ FIRST_X_ASSUM (qspecl_then
          [`call_env args (push_env env2 T (FUNPOW dec_clock (ticks+1) t2))`,
           `LENGTH args`,
           `GENLIST I (LENGTH args)`,`T`,`[]`]mp_tac)
      \\ FULL_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (FULL_SIMP_TAC (srw_ss()) [state_rel_def,dataSemTheory.dec_clock_def,
          bviSemTheory.dec_clock_def,var_corr_def,get_var_def,LIST_REL_REVERSE_EQ,
          LIST_REL_lookup_fromList,lookup_fromList_outside,push_env_def,call_env_def]
          \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
          \\ `jump_exc t2 <> NONE` by FULL_SIMP_TAC std_ss []
          \\ Cases_on `jump_exc t2` \\ full_simp_tac(srw_ss())[]
          \\ IMP_RES_TAC jump_exc_IMP
          \\ SIMP_TAC (srw_ss()) [jump_exc_def]
          \\ IMP_RES_TAC LASTN_TL \\ full_simp_tac(srw_ss())[] \\ DECIDE_TAC)
      \\ STRIP_TAC \\ full_simp_tac(srw_ss())[LET_DEF]
      \\ MP_TAC (Q.SPECL [`prog`,`call_env args
         (push_env env2 T (FUNPOW dec_clock (ticks+1) t2))`]
            optimise_correct) \\ full_simp_tac(srw_ss())[]
      \\ SIMP_TAC std_ss [call_env_def]
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (BasicProvers.FULL_CASE_TAC \\ full_simp_tac(srw_ss())[]
        \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[])
      \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[GSYM ADD1,FUNPOW_SUC]
      \\ Cases_on `pres` \\ FULL_SIMP_TAC (srw_ss()) [call_env_def,COUNT_LIST_GENLIST]
      \\ FULL_SIMP_TAC std_ss []
      \\ reverse (Cases_on `x'`) \\ FULL_SIMP_TAC (srw_ss()) []
      \\ rpt BasicProvers.VAR_EQ_TAC
      \\ full_simp_tac(srw_ss())[set_var_def,state_rel_def]
      THEN1 ( Cases_on`e`>>full_simp_tac(srw_ss())[] )
      \\ `pop_env t2' = SOME (t2' with
         <| stack := t2.stack; locals := env2
          ; handler := t2.handler |>)` by ALL_TAC THEN1
       (Q.PAT_ASSUM `xx = t2'.stack` (ASSUME_TAC o GSYM)
        \\ FULL_SIMP_TAC (srw_ss()) [call_env_def,push_env_def,
           pop_env_def,dataSemTheory.dec_clock_def,bviSemTheory.dec_clock_def])
      \\ Cases_on `tail` \\ full_simp_tac(srw_ss())[evaluate_def]
      THEN1 (full_simp_tac(srw_ss())[get_var_def,call_env_def])
      \\ IMP_RES_TAC compile_LESS_EQ
      \\ IMP_RES_TAC compile_SING_IMP
      \\ full_simp_tac(srw_ss())[] \\ IMP_RES_TAC compile_RANGE \\ full_simp_tac(srw_ss())[EVERY_DEF]
      \\ IMP_RES_TAC compile_LESS_EQ
      \\ REPEAT STRIP_TAC
      THEN1 DECIDE_TAC
      THEN1 DECIDE_TAC
      THEN1
       (UNABBREV_ALL_TAC
        \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_alt]
        \\ `k <> t'` by DECIDE_TAC \\ full_simp_tac(srw_ss())[]
        \\ REPEAT STRIP_TAC
        \\ FIRST_X_ASSUM MATCH_MP_TAC
        \\ DECIDE_TAC)
      THEN1
       (FULL_SIMP_TAC (srw_ss()) [var_corr_def,get_var_def,lookup_insert]
        \\ FULL_SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN]
        \\ REPEAT STRIP_TAC
        \\ Q.MATCH_ASSUM_RENAME_TAC `l < LENGTH env`
        \\ RES_TAC
        \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[lookup_inter_alt]
        \\ full_simp_tac(srw_ss())[domain_lookup,lookup_list_to_num_set]
        \\ `MEM (EL l corr) corr` by METIS_TAC [MEM_EL] \\ full_simp_tac(srw_ss())[]
        \\ SRW_TAC [] []
        \\ `n <= EL l corr` by DECIDE_TAC
        \\ RES_TAC \\ full_simp_tac(srw_ss())[])
      THEN1
       (FULL_SIMP_TAC (srw_ss()) [var_corr_def,get_var_def,lookup_insert]
        \\ Cases_on `k = t'` \\ FULL_SIMP_TAC std_ss []
        \\ CCONTR_TAC \\ `n2 <= k` by DECIDE_TAC
        \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
        \\ `n1 <= k` by DECIDE_TAC \\ RES_TAC
        \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[lookup_inter_alt])
      THEN1
       (FULL_SIMP_TAC (srw_ss()) [var_corr_def,get_var_def,lookup_insert]
        \\ `k <> t'` by ALL_TAC
        THEN1 (REPEAT STRIP_TAC \\ `n1 <= k` by DECIDE_TAC \\ RES_TAC \\ full_simp_tac(srw_ss())[])
        \\ full_simp_tac(srw_ss())[] \\ Cases_on `n1 <= t'` \\ RES_TAC \\ full_simp_tac(srw_ss())[]
        \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[lookup_inter_alt]
        \\ full_simp_tac(srw_ss())[domain_lookup,lookup_list_to_num_set]
        \\ METIS_TAC [])
      THEN1
       (full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[jump_exc_def] \\ rev_full_simp_tac(srw_ss())[]
        \\ Cases_on `LASTN (t2.handler + 1) t2.stack` \\ full_simp_tac(srw_ss())[]
        \\ Cases_on `h` \\ full_simp_tac(srw_ss())[])
      \\ REPEAT (FULL_SIMP_TAC (srw_ss()) [var_corr_def,get_var_def,lookup_insert,
                call_env_def,push_env_def,dataSemTheory.dec_clock_def,
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
  REPEAT STRIP_TAC \\ MP_TAC compile_exp_lemma \\ full_simp_tac(srw_ss())[]
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[compile_exp_def,LET_DEF]
  \\ MP_TAC (Q.SPECL [`prog`,`t1`] optimise_correct) \\ full_simp_tac(srw_ss())[]
  \\ impl_tac >- (rpt strip_tac >> full_simp_tac(srw_ss())[]) >> srw_tac[][COUNT_LIST_GENLIST]);

val state_rel_dec_clock = Q.prove(
  `state_rel s1 t1 ⇒ state_rel (dec_clock 1 s1) (dec_clock t1)`,
  srw_tac[][state_rel_def,bviSemTheory.dec_clock_def,dataSemTheory.dec_clock_def])

val compile_part_evaluate = Q.store_thm("compile_part_evaluate",
  `evaluate ([Call 0 (SOME start) [] NONE],[],s1) = (res,s2) ∧
   res ≠ Rerr (Rabort Rtype_error) ∧ state_rel s1 t1 ∧
   isEmpty t1.locals ∧ (∀x. res = Rerr (Rraise x) ⇒ jump_exc t1 ≠ NONE)
   ⇒
   ∃r t2.
   evaluate ((Call NONE (SOME start) [] NONE),t1) = (SOME r,t2) ∧
   state_rel s2 t2 ∧ res_list r = res`,
  srw_tac[][bviSemTheory.evaluate_def,dataSemTheory.evaluate_def,get_vars_def,find_code_def] >>
  Cases_on`lookup start s1.code`>>full_simp_tac(srw_ss())[]>>
  qmatch_assum_rename_tac`lookup start s1.code = SOME p` >>
  PairCases_on`p` >>
  `lookup start t1.code = SOME (p0,compile_exp p0 p1)` by (
    full_simp_tac(srw_ss())[state_rel_def,code_rel_def] ) >>
  full_simp_tac(srw_ss())[] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >> var_eq_tac >>
  `s1.clock = t1.clock` by full_simp_tac(srw_ss())[state_rel_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
    full_simp_tac(srw_ss())[call_env_def,state_rel_def] >>
    rpt var_eq_tac >> simp[] ) >>
  simp[] >> full_simp_tac(srw_ss())[] >>
  first_assum(subterm split_pair_case0_tac o concl) >> full_simp_tac(srw_ss())[] >>
  drule (GEN_ALL compile_exp_correct) >>
  simp[var_corr_def,SIMP_RULE std_ss [NULL_EQ]NULL_GENLIST] >>
  imp_res_tac state_rel_dec_clock >>
  disch_then(drule o (CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(equal``state_rel`` o fst o strip_comb)))))) >>
  simp[] >>
  impl_tac >- (
    simp[lookup_def,dataSemTheory.dec_clock_def] >>
    full_simp_tac(srw_ss())[jump_exc_def] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >>
    rpt var_eq_tac >> full_simp_tac(srw_ss())[] ) >>
  strip_tac >>
  simp[call_env_def,fromList_def] >>
  `dec_clock t1 with locals := LN = dec_clock t1` by (
    EVAL_TAC >> simp[dataSemTheory.state_component_equality] ) >>
  pop_assum SUBST1_TAC >> simp[] >>
  every_case_tac >> full_simp_tac(srw_ss())[]);

val MAP_FST_compile_prog = Q.store_thm("MAP_FST_compile_prog[simp]",
  `∀prog. MAP FST (compile_prog prog) = MAP FST prog`,
  simp[compile_prog_def,MAP_MAP_o,MAP_EQ_f,FORALL_PROD,compile_part_def]);

val compile_part_thm = Q.prove(
  `compile_part = λ(x,y). (x, (λ(a,b). (a, compile_exp a b)) y)`,
  simp[FUN_EQ_THM,FORALL_PROD,compile_part_def])

val compile_prog_evaluate = Q.store_thm("compile_prog_evaluate",
  `evaluate ([Call 0 (SOME start) [] NONE],[],initial_state ffi0 (fromAList prog) k) = (r,s) ∧
   r ≠ Rerr (Rabort Rtype_error) ∧ (∀x. r ≠ Rerr (Rraise x))
   ⇒
   ∃r2 s2.
   evaluate (Call NONE (SOME start) [] NONE, initial_state ffi0 (fromAList (compile_prog prog)) k) = (SOME r2,s2) ∧
   state_rel s s2 ∧ res_list r2 = r`,
  srw_tac[][] >>
  match_mp_tac (GEN_ALL compile_part_evaluate) >>
  asm_exists_tac >> simp[] >>
  simp[initial_state_def,state_rel_def] >>
  simp[code_rel_def,wf_fromAList,domain_fromAList,lookup_fromAList] >>
  simp[compile_prog_def,ALOOKUP_MAP,compile_part_thm]);

(* observational semantics *)

val compile_prog_semantics = Q.store_thm("compile_prog_semantics",
  `semantics ffi0 (fromAList prog) start ≠ Fail ⇒
   semantics ffi0 (fromAList (compile_prog prog)) start =
   semantics ffi0 (fromAList prog) start`,
  simp[bviSemTheory.semantics_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    qx_gen_tac`res`>>srw_tac[][]>>
    simp[dataSemTheory.semantics_def] >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
      rator_x_assum`bviSem$evaluate`kall_tac >>
      last_x_assum(qspec_then`k'`mp_tac)>>simp[] >>
      (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
      spose_not_then strip_assume_tac >>
      drule compile_prog_evaluate >>
      impl_tac >- ( srw_tac[][] >> strip_tac >> full_simp_tac(srw_ss())[] ) >>
      strip_tac >> full_simp_tac(srw_ss())[] >> rveq >>
      every_case_tac >> full_simp_tac(srw_ss())[] ) >>
    DEEP_INTRO_TAC some_intro >> simp[] >>
    conj_tac >- (
      gen_tac >> strip_tac >> rveq >> simp[] >>
      qmatch_assum_abbrev_tac`bviSem$evaluate (exps,[],ss) = _` >>
      qmatch_assum_abbrev_tac`dataSem$evaluate (bxps,bs) = _` >>
      qspecl_then[`exps`,`[]`,`ss`]mp_tac bviPropsTheory.evaluate_add_to_clock_io_events_mono >>
      qspecl_then[`bxps`,`bs`]mp_tac dataPropsTheory.evaluate_add_clock_io_events_mono >>
      simp[bviPropsTheory.inc_clock_def,Abbr`ss`,Abbr`bs`] >>
      disch_then(qspec_then`k`strip_assume_tac) >>
      disch_then(qspec_then`k'`strip_assume_tac) >>
      Cases_on`s.ffi.final_event`>>full_simp_tac(srw_ss())[]>-(
        Cases_on`s'.ffi.final_event`>>full_simp_tac(srw_ss())[]>-(
          unabbrev_all_tac >>
          drule compile_prog_evaluate >>
          impl_tac >- ( every_case_tac >> full_simp_tac(srw_ss())[] ) >>
          strip_tac >>
          drule dataPropsTheory.evaluate_add_clock >>
          impl_tac >- (
            full_simp_tac(srw_ss())[] >> strip_tac >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] ) >>
          disch_then(qspec_then`k'`mp_tac)>>simp[]>>
          rator_x_assum`dataSem$evaluate`mp_tac >>
          drule dataPropsTheory.evaluate_add_clock >>
          impl_tac >- (
            full_simp_tac(srw_ss())[] >> strip_tac >> full_simp_tac(srw_ss())[] ) >>
          disch_then(qspec_then`k`mp_tac)>>simp[]>>
          ntac 3 strip_tac >> rveq >> full_simp_tac(srw_ss())[] >>
          full_simp_tac(srw_ss())[state_component_equality] >>
          full_simp_tac(srw_ss())[state_rel_def] >>
          every_case_tac >> full_simp_tac(srw_ss())[] ) >>
        first_assum(subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) o concl) >> full_simp_tac(srw_ss())[] >>
        unabbrev_all_tac >>
        drule compile_prog_evaluate >>
        impl_tac >- (
          last_x_assum(qspec_then`k+k'`mp_tac)>>
          rpt strip_tac >> fsrw_tac[ARITH_ss][] >> rev_full_simp_tac(srw_ss())[] ) >>
        strip_tac >>
        rator_x_assum`bviSem$evaluate`mp_tac >>
        drule bviPropsTheory.evaluate_add_clock >>
        impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
        disch_then(qspec_then`k'`mp_tac)>>simp[inc_clock_def] >>
        ntac 2 strip_tac >> rveq >>
        fsrw_tac[ARITH_ss][state_rel_def] >> rev_full_simp_tac(srw_ss())[] ) >>
      first_assum(subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) o concl) >> full_simp_tac(srw_ss())[] >>
      unabbrev_all_tac >>
      drule compile_prog_evaluate >>
      impl_tac >- (
        last_x_assum(qspec_then`k+k'`mp_tac)>>
        rpt strip_tac >> fsrw_tac[ARITH_ss][] >> rev_full_simp_tac(srw_ss())[] ) >>
      strip_tac >> rveq >>
      fsrw_tac[ARITH_ss][] >>
      reverse(Cases_on`s'.ffi.final_event`)>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>- (
        full_simp_tac(srw_ss())[state_rel_def] >> rev_full_simp_tac(srw_ss())[] ) >>
      rator_x_assum`dataSem$evaluate`mp_tac >>
      drule dataPropsTheory.evaluate_add_clock >>
      impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
      disch_then(qspec_then`k`mp_tac)>>simp[inc_clock_def] >>
      ntac 2 strip_tac >> rveq >>
      fsrw_tac[ARITH_ss][state_rel_def] >> rev_full_simp_tac(srw_ss())[] ) >>
    drule compile_prog_evaluate >>
    impl_tac >- (
      last_x_assum(qspec_then`k`mp_tac)>>
      full_simp_tac(srw_ss())[] >> rpt strip_tac >> full_simp_tac(srw_ss())[] ) >>
    strip_tac >>
    asm_exists_tac >> simp[] >>
    full_simp_tac(srw_ss())[state_rel_def] >>
    every_case_tac >> full_simp_tac(srw_ss())[] ) >>
  strip_tac >>
  simp[dataSemTheory.semantics_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
    last_x_assum(qspec_then`k`mp_tac) >>
    (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (#2 g)) >>
    strip_tac >>
    drule compile_prog_evaluate >>
    impl_tac >- (
      conj_tac >> spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[] ) >>
    strip_tac >>
    full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    every_case_tac >> full_simp_tac(srw_ss())[] ) >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    spose_not_then strip_assume_tac >>
    last_x_assum(qspec_then`k`mp_tac) >>
    (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (#2 g)) >>
    strip_tac >>
    drule compile_prog_evaluate >>
    impl_tac >- (
      conj_tac >> spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[] ) >>
    strip_tac >>
    full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >>
    last_x_assum(qspec_then`k`mp_tac) >>
    simp[] >>
    every_case_tac >> simp[] >>
    rev_full_simp_tac(srw_ss())[state_rel_def]) >>
  strip_tac >>
  rpt(AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[FUN_EQ_THM] >> gen_tac >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (rhs(#2 g))) >>
  drule compile_prog_evaluate >>
  impl_tac >- (
    conj_tac >> spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[] >>
    last_x_assum(qspec_then`k`mp_tac)>>simp[]) >>
  strip_tac >> simp[] >>
  full_simp_tac(srw_ss())[state_rel_def]);

val _ = export_theory();
