(*
  Correctness proof for data_live
*)
open preamble data_liveTheory dataSemTheory dataPropsTheory;

val _ = new_theory"data_liveProof";

val _ = temp_bring_to_front_overload"get_vars"{Name="get_vars",Thy="dataSem"};
val _ = temp_bring_to_front_overload"cut_env"{Name="cut_env",Thy="dataSem"};

val SPLIT_PAIR = Q.prove(
  `!x y z. (x = (y,z)) <=> (y = FST x) /\ (z = SND x)`,
  Cases \\ SRW_TAC [] [] \\ METIS_TAC []);

val state_rel_def = Define `
  state_rel (s1:('a,'ffi) dataSem$state) (t1:('a,'ffi) dataSem$state) (live:num_set) <=>
    s1.code = t1.code /\ s1.clock = t1.clock /\ s1.space = t1.space /\
    s1.ffi = t1.ffi /\ s1.refs = t1.refs /\ s1.global = t1.global /\
    s1.handler = t1.handler /\ (LENGTH s1.stack = LENGTH t1.stack) /\
    s1.compile = t1.compile /\ s1.compile_oracle = t1.compile_oracle /\
    s1.tstamps = t1.tstamps /\
    (!x. x IN domain live ==> (lookup x s1.locals = lookup x t1.locals))`;

val state_rel_ID = Q.prove(
  `!s live. state_rel s s live`,
  fs [state_rel_def]);

val jump_exc_IMP_state_rel = Q.prove(
  `!s1 t1 s2 t2.
      (jump_exc s1 = SOME s2) /\ (jump_exc t1 = SOME t2) /\
      state_rel s1 t1 LN /\ (LENGTH s2.stack = LENGTH t2.stack) ==>
      state_rel (s2 with handler := s1.handler)
                (t2 with handler := t1.handler) LN`,
  REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [jump_exc_def]
  \\ every_case_tac >> fs[]
  \\ SRW_TAC [] [] \\ fs [state_rel_def]);

val state_rel_IMP_do_app_aux = Q.prove(
  `(do_app_aux op args s1 = Rval (v,s2)) /\
    state_rel s1 t1 anything ==>
    (s1.handler = s2.handler) /\ (s1.stack = s2.stack) /\
    (do_app_aux op args t1 = Rval (v,s2 with <| locals := t1.locals ;
                                             stack := t1.stack ;
                                             handler := t1.handler |>))`,
  STRIP_TAC
  \\ Cases_on `op`
  \\ fs [do_app_aux_def,do_space_def,with_fresh_ts_def,state_rel_def]
  \\ fs [state_rel_def,consume_space_def,case_eq_thms,do_install_def,UNCURRY]
  \\ ASM_SIMP_TAC (srw_ss()) [dataSemTheory.state_component_equality]
  \\ SRW_TAC [] [] \\ fs[]);

val state_rel_IMP_do_app = Q.prove(
  `(do_app op args s1 = Rval (v,s2)) /\
    state_rel s1 t1 anything ==>
    (s1.handler = s2.handler) /\ (s1.stack = s2.stack) /\
    (do_app op args t1 = Rval (v,s2 with <| locals := t1.locals ;
                                             stack := t1.stack ;
                                             handler := t1.handler |>))`,
  STRIP_TAC
  \\ IMP_RES_TAC do_app_const
  \\ fs [do_app_def, do_space_def, do_install_def
        , state_rel_def, consume_space_def
        , UNCURRY, case_eq_thms]
 \\ ASM_SIMP_TAC (srw_ss()) [dataSemTheory.state_component_equality]
 \\ qmatch_goalsub_abbrev_tac `do_app_aux op args t1'`
 \\ TRY (qpat_x_assum `_ = s1'` (ASSUME_TAC o GSYM))
 \\ `state_rel s1' t1' anything` by (UNABBREV_ALL_TAC \\ fs [state_rel_def])
 \\ IMP_RES_TAC state_rel_IMP_do_app_aux
 \\ rw [Abbr `t1'`]);

val state_rel_IMP_do_app_aux_err = Q.prove(
  `(do_app_aux op args s1 = Rerr e) /\ state_rel s1 t1 anything ==>
    (do_app_aux op args t1 = Rerr e)`,
  STRIP_TAC
  \\ Cases_on `op`
  \\ fs [do_app_aux_def,do_space_def,with_fresh_ts_def]
  \\ fs [state_rel_def,consume_space_def,case_eq_thms,do_install_def,UNCURRY]
  \\ ASM_SIMP_TAC (srw_ss()) [dataSemTheory.state_component_equality]
  \\ SRW_TAC [] [] \\ fs[]);

val state_rel_IMP_do_app_err = Q.prove(
  `(do_app op args s1 = Rerr e) /\ state_rel s1 t1 anything ==>
    (do_app op args t1 = Rerr e)`,
  STRIP_TAC
  \\ fs [do_app_def,do_space_def]
  \\ fs [state_rel_def,consume_space_def,case_eq_thms,do_install_def,UNCURRY]
  \\ qmatch_goalsub_abbrev_tac `do_app_aux op args t1'`
  \\ TRY (qpat_x_assum `_ = s1'` (ASSUME_TAC o GSYM))
  \\ `state_rel s1' t1' anything` by (UNABBREV_ALL_TAC \\ fs [state_rel_def])
  \\ IMP_RES_TAC state_rel_IMP_do_app_aux_err
  \\ rw [Abbr `t1'`]
);

val state_rel_IMP_get_vars = Q.prove(
  `!args s1 t1 t xs.
      state_rel s1 t1 (list_insert args t) /\
      (get_vars args s1.locals = SOME xs) ==>
      (get_vars args t1.locals = SOME xs)`,
  Induct \\ fs [get_vars_def] \\ REPEAT STRIP_TAC
  \\ `state_rel s1 t1 (list_insert args t) /\
      (get_var h s1.locals = get_var h t1.locals)` by
   (fs [state_rel_def,list_insert_def,domain_list_insert,get_var_def]
    \\ METIS_TAC []) \\ fs []
  \\ every_case_tac >> fs[]
  \\ RES_TAC \\ fs [] \\ SRW_TAC [] []);

val is_pure_do_app_Rerr_IMP = Q.prove(
  `is_pure op /\ do_app op xs s = Rerr e ==>
    Rabort Rtype_error = e`,
  Cases_on `op` \\ fs [is_pure_def,do_app_def,do_app_aux_def]
  \\ simp[do_space_def,data_spaceTheory.op_space_req_def,
          case_eq_thms,do_install_def,UNCURRY] \\ rw[]);

val is_pure_do_app_Rval_IMP = Q.prove(
  `is_pure op /\ do_app op x s = Rval (q,r) ==> r = s`,
  Cases_on `op` \\ fs [is_pure_def,do_app_def,do_app_aux_def]
  \\ simp[do_space_def,dataLangTheory.op_space_reset_def,data_spaceTheory.op_space_req_def,
          consume_space_def,do_install_def,UNCURRY,case_eq_thms]
  \\ rw[] \\ fs [state_component_equality,is_pure_def,data_spaceTheory.op_space_req_def]);

val evaluate_compile = Q.prove(
  `!c s1 res s2 l2 t1 l1 d.
      (evaluate (c,s1) = (res,s2)) /\ state_rel s1 t1 l1 /\
      (compile c l2 = (d,l1)) /\ (res <> SOME (Rerr (Rabort Rtype_error))) /\
      (!s3. (jump_exc s1 = SOME s3) ==>
            ?t3. (jump_exc t1 = SOME t3) /\ state_rel s3 t3 LN /\
                 (t3.handler = s3.handler) /\
                 (LENGTH t3.stack = LENGTH s3.stack)) ==>
      ?t2. (evaluate (d,t1) = (res,t2)) /\
           state_rel s2 t2 (case res of NONE => l2 | _ => LN)`,
  ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ recInduct evaluate_ind \\ REPEAT STRIP_TAC
  THEN1 (* Skip *)
    (fs [evaluate_def,compile_def])
  THEN1 (* Move *)
    (fs [evaluate_def,compile_def,get_var_def,state_rel_def]
     \\ Cases_on `lookup src t1.locals`
     \\ fs [set_var_def,lookup_insert])
  THEN1 (* Assign *)
    (Cases_on `names_opt` THEN1
      (fs [compile_def]
       \\ Cases_on `lookup dest l2 = NONE ∧ is_pure op` \\ fs []
       THEN1
        (rpt var_eq_tac \\ fs [evaluate_def,cut_state_opt_def]
         \\ every_case_tac \\ fs [] \\ rpt var_eq_tac
         \\ imp_res_tac is_pure_do_app_Rerr_IMP \\ fs []
         \\ imp_res_tac is_pure_do_app_Rval_IMP \\ fs [] \\ rpt var_eq_tac
         \\ fs [state_rel_def,set_var_def,lookup_insert,domain_lookup] \\ rw [])
       \\ fs [] \\ pop_assum kall_tac \\ rpt var_eq_tac
       \\ fs [evaluate_def,get_var_def,LET_DEF]
       \\ every_case_tac >> fs[] \\ SRW_TAC [] []
       \\ fs [compile_def,LET_DEF,evaluate_def,cut_state_opt_def] \\ rw[]
       \\ qmatch_assum_rename_tac`get_vars args _ = SOME xx`
       \\ `get_vars args t1.locals = SOME xx` by IMP_RES_TAC state_rel_IMP_get_vars
       \\ fs [] \\ IMP_RES_TAC state_rel_IMP_do_app
       \\ fs [] \\ IMP_RES_TAC state_rel_IMP_do_app_err
       \\ fs [state_rel_def,set_var_def,lookup_insert]
       \\ SRW_TAC [] [call_env_def] \\ IMP_RES_TAC do_app_const
       \\ fs [domain_list_insert,state_component_equality] \\ rfs [])
     \\ fs [evaluate_def,get_var_def,LET_DEF]
     \\ every_case_tac >> fs[] \\ SRW_TAC [] []
     \\ fs [compile_def,LET_DEF,evaluate_def,cut_state_opt_def]
     \\ Q.MATCH_ASSUM_RENAME_TAC `do_app op vs t = _`
     \\ Cases_on `domain x SUBSET domain s.locals` \\ fs []
     \\ fs [cut_state_def,cut_env_def]
     \\ (`domain (inter x (list_insert args (delete dest l2))) SUBSET
         domain t1.locals` by
      (fs [domain_inter,domain_list_insert,SUBSET_DEF,state_rel_def]
       \\ RES_TAC \\ fs [domain_lookup]
       \\ fs [PULL_EXISTS,oneTheory.one] \\ RES_TAC \\ METIS_TAC []))
     \\ fs [] \\ SRW_TAC [] []
     \\ Q.ABBREV_TAC `t4 = mk_wf (inter t1.locals
                (inter x (list_insert args (delete dest l2))))`
     \\ `state_rel (s with locals := mk_wf (inter s.locals x))
        (t1 with locals := t4) LN` by (fs [state_rel_def] \\ NO_TAC)
     \\ `get_vars args t4 = SOME vs` by
      (UNABBREV_ALL_TAC
       \\ Q.PAT_X_ASSUM `xx = SOME vs` (fn th => ONCE_REWRITE_TAC [GSYM th])
       \\ MATCH_MP_TAC EVERY_get_vars
       \\ fs [EVERY_MEM,lookup_inter_alt,domain_inter,domain_list_insert]
       \\ SRW_TAC [] [] \\ fs [state_rel_def]
       \\ FIRST_X_ASSUM (MATCH_MP_TAC o GSYM)
       \\ fs [domain_inter,domain_list_insert] \\ NO_TAC)
     \\ fs [] \\ IMP_RES_TAC state_rel_IMP_do_app
     \\ fs [] \\ IMP_RES_TAC state_rel_IMP_do_app_err
     \\ fs [state_rel_def,set_var_def,lookup_insert]
     \\ REPEAT STRIP_TAC \\ SRW_TAC [] [call_env_def]
     \\ fs [domain_inter,domain_list_insert,domain_delete]
     \\ UNABBREV_ALL_TAC
     \\ IMP_RES_TAC do_app_const
     \\ fs []
     \\ fs [lookup_inter_alt,domain_inter,domain_list_insert,domain_delete])
  THEN1 (* Tick *)
    (fs [evaluate_def,compile_def,state_rel_def] \\ SRW_TAC [] []
     \\ fs [call_env_def,dec_clock_def]
     \\ BasicProvers.FULL_CASE_TAC \\ fs [])
  THEN1 (* MakeSpace *)
   (fs [evaluate_def,compile_def,get_var_def,state_rel_def,LET_DEF,cut_env_def]
    \\ Cases_on `domain names SUBSET domain s.locals` \\ fs []
    \\ SRW_TAC [] [add_space_def]
    \\ fs [domain_inter,lookup_inter_assoc,lookup_inter_alt]
    \\ fs [domain_lookup,PULL_EXISTS,lookup_inter_EQ,SUBSET_DEF]
    \\ Cases_on `lookup x names` \\ fs [lookup_inter,oneTheory.one]
    \\ REPEAT BasicProvers.CASE_TAC \\ METIS_TAC [])
  THEN1 (* Raise *)
   (fs [evaluate_def,compile_def] \\ Cases_on `get_var n s.locals` \\ fs []
    \\ fs [state_rel_def]
    \\ Q.PAT_X_ASSUM `lookup n s.locals = lookup n t1.locals`
         (ASSUME_TAC o GSYM) \\ fs [get_var_def]
    \\ SRW_TAC [] [call_env_def]
    \\ Cases_on `jump_exc s` \\ fs [] \\ SRW_TAC [] []
    \\ Cases_on `jump_exc t1` \\ fs [] \\ SRW_TAC [] [])
  THEN1 (* Return *)
   (fs [evaluate_def,compile_def] \\ Cases_on `get_var n s.locals` \\ fs []
    \\ fs [state_rel_def]
    \\ Q.PAT_X_ASSUM `lookup n s.locals = lookup n t1.locals`
         (ASSUME_TAC o GSYM) \\ fs [get_var_def]
    \\ SRW_TAC [] [call_env_def])
  THEN1 (* Seq *)
   (fs [evaluate_def]
    \\ `?res1 u1. evaluate (c1,s) = (res1,u1)` by METIS_TAC [PAIR]
    \\ `?res2 u2. evaluate (c2,u1) = (res2,u2)` by METIS_TAC [PAIR]
    \\ `?x2 l5. compile c2 l2 = (x2,l5)` by METIS_TAC [PAIR]
    \\ `?x1 l6. compile c1 l5 = (x1,l6)` by METIS_TAC [PAIR]
    \\ fs [LET_DEF,compile_def,evaluate_def]
    \\ FIRST_X_ASSUM (MP_TAC o GSYM o Q.SPECL [`l5`,`t1`]) \\ fs []
    \\ Cases_on `res1 = SOME (Rerr (Rabort Rtype_error))` \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (METIS_TAC [])
    \\ REPEAT STRIP_TAC
    \\ reverse (Cases_on `res1 = NONE`) \\ fs []
    THEN1 (SRW_TAC [] [] \\ Cases_on `res` \\ fs [])
    \\ Q.PAT_X_ASSUM `!x y. bb` (MP_TAC o GSYM o Q.SPECL [`l2`,`t2`]) \\ fs []
    \\ REV_FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.PAT_X_ASSUM `!x.bbb` (ASSUME_TAC o GSYM)
    \\ IMP_RES_TAC evaluate_NONE_jump_exc \\ Q.PAT_X_ASSUM `!x.bbb` (K ALL_TAC)
    \\ RES_TAC
    \\ IMP_RES_TAC evaluate_NONE_jump_exc_ALT \\ POP_ASSUM (K ALL_TAC)
    \\ POP_ASSUM (K ALL_TAC) \\ fs []
    \\ `state_rel u1 t2 LN` by fs [state_rel_def]
    \\ MP_TAC (Q.SPECL [`u1`,`t2`] jump_exc_IMP_state_rel) \\ fs []
    \\ ASM_SIMP_TAC (srw_ss()) [state_rel_def])
  THEN1 (* If *)
   (Q.ABBREV_TAC `l9 = l2` \\ POP_ASSUM (K ALL_TAC)
    \\ `?d3 l3. compile c2 l9 = (d3,l3)` by METIS_TAC [PAIR]
    \\ `?d2 l2. compile c1 l9 = (d2,l2)` by METIS_TAC [PAIR]
    \\ fs [compile_def,LET_DEF] \\ rw []
    \\ fs [evaluate_def] \\ REPEAT STRIP_TAC
    \\ Cases_on `get_var n s.locals` \\ fs []
    \\ `(get_var n s.locals = get_var n t1.locals)` by
         (fs [state_rel_def,domain_union,domain_insert,get_var_def]
          \\ METIS_TAC [])
    \\ Cases_on `isBool T x` \\ fs [] THEN1
     (Q.PAT_X_ASSUM `xxx = evaluate (c1,s)` (ASSUME_TAC o GSYM) \\ fs []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l9`,`t1`]) \\ fs []
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
      \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ REPEAT STRIP_TAC \\ fs []
      \\ fs [state_rel_def,domain_union])
    \\ Cases_on `isBool F x` \\ fs [] THEN1
     (Q.PAT_X_ASSUM `xxx = evaluate (c2,s)` (ASSUME_TAC o GSYM) \\ fs []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l9`,`t1`]) \\ fs []
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
      \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ REPEAT STRIP_TAC \\ fs []
      \\ fs [state_rel_def,domain_union]))
  (* Call from here onwards *)
  \\ Cases_on `ret` \\ fs [evaluate_def,compile_def]
  THEN1 (* Call with ret = NONE *)
   (`s.clock = t1.clock /\ s.code = t1.code` by fs [state_rel_def]
    \\ REV_FULL_SIMP_TAC std_ss []
    \\ fs [] \\ Cases_on `get_vars args s.locals` \\ fs []
    \\ `get_vars args t1.locals = get_vars args s.locals` by
     (MATCH_MP_TAC EVERY_get_vars
      \\ fs [EVERY_MEM,state_rel_def,domain_list_to_num_set])
    \\ fs [] \\ REV_FULL_SIMP_TAC std_ss []
    \\ Cases_on `find_code dest x t1.code` \\ fs []
    \\ Cases_on `x'` \\ fs []
    \\ Cases_on `handler` \\ fs []
    \\ Q.PAT_X_ASSUM `(res,s2) = xxx` (ASSUME_TAC o GSYM) \\ fs []
    \\ Cases_on `t1.clock = 0`
    THEN1 (fs [call_env_def,state_rel_def] \\ rw [] \\ rfs[])
    \\ Cases_on `evaluate (r,call_env q (dec_clock s))` \\ fs []
    \\ Cases_on `q'` \\ fs [] \\ SRW_TAC [] []
    \\ `call_env q (dec_clock t1) =
        call_env q (dec_clock s) with stack := t1.stack` by
      fs [call_env_def,dec_clock_def,state_rel_def,state_component_equality]
    \\ fs [] \\ Q.MATCH_ASSUM_RENAME_TAC
         `evaluate (r,call_env q (dec_clock s)) = (SOME res2,s2)`
    \\ (Q.ISPECL_THEN [`r`,`call_env q (dec_clock s)`] mp_tac evaluate_stack_swap)
    \\ fs [] \\ Cases_on `res2` \\ fs [] THEN1
     (fs [call_env_def,dec_clock_def] \\ REPEAT STRIP_TAC
      \\ `LENGTH s.stack = LENGTH t1.stack` by fs [state_rel_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `t1.stack`) \\ fs []
      \\ SRW_TAC [] [state_rel_def])
    THEN Cases_on`e` >> fs[] THEN1
     (REPEAT STRIP_TAC
      \\ POP_ASSUM (MP_TAC o Q.SPECL [`t1.stack`])
      \\ Q.PAT_X_ASSUM `!x.bbb` (MP_TAC o GSYM)
      \\ Q.MATCH_ASSUM_RENAME_TAC
           `jump_exc (call_env q (dec_clock s)) = SOME s3`
      \\ Q.PAT_X_ASSUM `jump_exc (call_env q (dec_clock s)) = SOME s3`
            (MP_TAC o GSYM)
      \\ SIMP_TAC (srw_ss()) [call_env_def,dec_clock_def,Once jump_exc_def]
      \\ NTAC 2 BasicProvers.CASE_TAC \\ STRIP_TAC
      \\ POP_ASSUM (fn th => FULL_SIMP_TAC std_ss [GSYM th])
      \\ ASM_SIMP_TAC (srw_ss()) [Once jump_exc_def]
      \\ SIMP_TAC std_ss [Once jump_exc_def]
      \\ NTAC 2 BasicProvers.CASE_TAC \\ fs [] \\ STRIP_TAC
      \\ `s.handler = t1.handler /\
          LENGTH s.stack = LENGTH t1.stack` by fs [state_rel_def]
      \\ ASM_SIMP_TAC (srw_ss()) [Once jump_exc_def]
      \\ REPEAT STRIP_TAC \\ fs [] \\ fs [state_rel_def])
    THEN Cases_on`a`>>fs[] THEN
     (fs [call_env_def,dec_clock_def] \\ REPEAT STRIP_TAC
      \\ `LENGTH s.stack = LENGTH t1.stack` by fs [state_rel_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `t1.stack`) \\ fs []
      \\ SRW_TAC [] [state_rel_def]))
  (* Call with SOME ret *)
  \\ Cases_on `x` \\ Q.MATCH_ASSUM_RENAME_TAC
       `(d,l1) = compile (Call (SOME (v,names)) dest args handler) l2`
  \\ Cases_on `handler`
  THEN1 (* Call with handler NONE *)
   (fs [compile_def,LET_DEF,evaluate_def]
    \\ `t1.clock = s.clock /\ t1.code = s.code` by fs [state_rel_def]
    \\ Cases_on `get_vars args s.locals` \\ fs []
    \\ IMP_RES_TAC state_rel_IMP_get_vars \\ fs []
    \\ Cases_on `find_code dest x s.code` \\ fs []
    \\ Cases_on `x'` \\ fs []
    \\ Cases_on `cut_env names s.locals` \\ fs []
    \\ fs [cut_env_def] \\ reverse (SRW_TAC [] []) THEN1
     (POP_ASSUM MP_TAC \\ fs []
      \\ fs [SUBSET_DEF,domain_list_insert,domain_inter,
             domain_delete,state_rel_def]
      \\ REPEAT STRIP_TAC \\ IMP_RES_TAC get_vars_IMP_domain
      \\ fs [domain_lookup] \\ METIS_TAC [])
    \\ Q.ABBREV_TAC `t5 = call_env q (push_env
             ((inter t1.locals (inter names (delete v l2)))) F (dec_clock t1))`
    \\ `(call_env q (push_env ((inter s.locals names)) F (dec_clock s))
          with stack := t5.stack) = t5` by
     (UNABBREV_ALL_TAC
      \\ fs [call_env_def,push_env_def,dec_clock_def,state_rel_def,
             state_component_equality] \\ NO_TAC) \\ fs []
    \\ Q.ABBREV_TAC `t4 =
         call_env q (push_env ((inter s.locals names)) F (dec_clock s))`
    \\ `LENGTH t4.stack = LENGTH t5.stack` by
     (UNABBREV_ALL_TAC \\ fs [call_env_def,push_env_def,dec_clock_def]
      \\ fs [state_rel_def] \\ NO_TAC)
    \\ (Q.ISPECL_THEN [`r`,`t4`] mp_tac evaluate_stack_swap)
    \\ Cases_on `s.clock = 0` \\ fs []
    THEN1 (fs [state_rel_def,call_env_def])
    \\ Cases_on `evaluate (r,t4)` \\ fs []
    \\ Cases_on `q'` \\ fs [] \\ Cases_on `x'` \\ fs [] THEN1
     (REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `t5.stack`) \\ fs []
      \\ REPEAT STRIP_TAC \\ fs [] \\ SIMP_TAC (srw_ss()) [pop_env_def]
      \\ UNABBREV_ALL_TAC \\ fs [call_env_def,push_env_def]
      \\ fs [pop_env_def] \\ fs [state_rel_def,set_var_def]
      \\ fs [lookup_insert,lookup_inter_alt,domain_list_insert,
             domain_inter,domain_delete] \\ REPEAT STRIP_TAC
      \\ Cases_on `x' = v` \\ fs []
      \\ Cases_on `x' IN domain names` \\ fs []
      \\ REPEAT STRIP_TAC \\ SRW_TAC [] [])
    THEN Cases_on`e` >> fs[] THEN1
     (REPEAT STRIP_TAC
      \\ POP_ASSUM (MP_TAC o Q.SPECL [`t5.stack`])
      \\ Q.PAT_X_ASSUM `!x.bbb` (MP_TAC o GSYM)
      \\ Q.MATCH_ASSUM_RENAME_TAC `jump_exc t4 = SOME s3`
      \\ Q.PAT_X_ASSUM `jump_exc t4 = SOME s3` (MP_TAC o GSYM)
      \\ UNABBREV_ALL_TAC
      \\ SIMP_TAC (srw_ss()) [call_env_def,push_env_def,
           dec_clock_def,Once jump_exc_def]
      \\ NTAC 2 BasicProvers.CASE_TAC \\ STRIP_TAC
      \\ `s.handler < LENGTH s.stack` by
       (Cases_on `s.handler = LENGTH s.stack`
        \\ fs [LASTN_LEMMA] \\ DECIDE_TAC)
      \\ IMP_RES_TAC LASTN_TL \\ fs []
      \\ ASM_SIMP_TAC (srw_ss()) [Once jump_exc_def]
      \\ SIMP_TAC std_ss [Once jump_exc_def]
      \\ NTAC 2 BasicProvers.CASE_TAC \\ fs [] \\ STRIP_TAC
      \\ `s.handler = t1.handler /\
          LENGTH s.stack = LENGTH t1.stack` by fs [state_rel_def]
      \\ ASM_SIMP_TAC (srw_ss()) [Once jump_exc_def]
      \\ `t1.handler < LENGTH t1.stack` by (fs [] \\ NO_TAC)
      \\ IMP_RES_TAC LASTN_TL \\ fs [] \\ REPEAT STRIP_TAC
      \\ Q.ABBREV_TAC `env = Env ((inter t1.locals
                                 (inter names (delete v l2))))`
      \\ `t1 with <| locals := fromList q; stack := env::t1.stack;
                     clock := s.clock - 1|> =
          s with <| locals := fromList q; stack := env::t1.stack;
                    clock := s.clock - 1|>` by
                fs [state_component_equality,state_rel_def]
      \\ REV_FULL_SIMP_TAC std_ss []
      \\ fs [state_rel_def] \\ SRW_TAC [] [] \\ fs [])
    THEN Cases_on`a`>>fs[] THEN
     (REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `t5.stack`) \\ fs []
      \\ REPEAT STRIP_TAC \\ fs [state_rel_ID]))
  (* Call with SOME handler *)
  \\ `?var handle. x = (var,handle)` by METIS_TAC [PAIR]
  \\ POP_ASSUM (fn th => fs [th])
  \\ `?d6 l6. compile handle l2 = (d6,l6)` by METIS_TAC [PAIR]
  \\ fs [compile_def,LET_DEF,evaluate_def]
  \\ `t1.clock = s.clock /\ t1.code = s.code` by fs [state_rel_def]
  \\ Cases_on `get_vars args s.locals` \\ fs []
  \\ IMP_RES_TAC state_rel_IMP_get_vars \\ fs []
  \\ Cases_on `find_code dest x s.code` \\ fs []
  \\ Cases_on `x'` \\ fs []
  \\ Cases_on `cut_env names s.locals` \\ fs []
  \\ fs [cut_env_def] \\ reverse (SRW_TAC [] []) THEN1
   (POP_ASSUM MP_TAC \\ fs []
    \\ fs [SUBSET_DEF,domain_list_insert,domain_inter,
           domain_delete,state_rel_def]
    \\ REPEAT STRIP_TAC \\ IMP_RES_TAC get_vars_IMP_domain
    \\ fs [domain_lookup] \\ METIS_TAC [])
  \\ Q.ABBREV_TAC `t5 = call_env q (push_env
           ((inter t1.locals (inter names
              (union (delete v l2) (delete var l6))))) T (dec_clock t1))`
  \\ `(call_env q (push_env ((inter s.locals names)) T (dec_clock s))
        with stack := t5.stack) = t5` by
   (UNABBREV_ALL_TAC
    \\ fs [call_env_def,push_env_def,dec_clock_def,state_rel_def,
           state_component_equality] \\ NO_TAC) \\ fs []
  \\ Q.ABBREV_TAC `t4 =
       call_env q (push_env ((inter s.locals names)) T (dec_clock s))`
  \\ `LENGTH t4.stack = LENGTH t5.stack` by
   (UNABBREV_ALL_TAC \\ fs [call_env_def,push_env_def,dec_clock_def]
    \\ fs [state_rel_def] \\ NO_TAC)
  \\ (Q.ISPECL_THEN [`r`,`t4`]mp_tac evaluate_stack_swap)
  \\ Cases_on `s.clock = 0` \\ fs []
  THEN1 (fs [state_rel_def,call_env_def])
  \\ Cases_on `evaluate (r,t4)` \\ fs []
  \\ Cases_on `q'` \\ fs [] \\ Cases_on `x'` \\ fs [] THEN1
   (REPEAT STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `t5.stack`) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs [] \\ SIMP_TAC (srw_ss()) [pop_env_def]
    \\ UNABBREV_ALL_TAC \\ fs [call_env_def,push_env_def]
    \\ fs [pop_env_def] \\ fs [state_rel_def,set_var_def]
    \\ fs [lookup_insert,lookup_inter_alt,lookup_union,
           domain_list_insert,domain_union,
           domain_inter,domain_delete] \\ REPEAT STRIP_TAC
    \\ fs [dec_clock_def])
  \\ Cases_on`e`>>fs[]
  \\ TRY (
    Cases_on`a` >> fs[] >> (
    REPEAT STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `t5.stack`) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs [state_rel_ID] \\ NO_TAC))
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`t5.stack`])
  \\ UNABBREV_ALL_TAC
  \\ NTAC 3 (SIMP_TAC std_ss [Once dec_clock_def])
  \\ NTAC 3 (SIMP_TAC std_ss [Once push_env_def])
  \\ NTAC 3 (SIMP_TAC std_ss [Once call_env_def])
  \\ fs [] \\ SIMP_TAC (srw_ss()) [Once jump_exc_def]
  \\ `LENGTH s.stack = LENGTH t1.stack` by fs [state_rel_def]
  \\ fs [LASTN_LEMMA]
  \\ `(call_env q (push_env (inter s.locals names) T (dec_clock s)) with
       stack := Exc (inter t1.locals
          (inter names (union (delete v l2) (delete var l6))))
       t1.handler::t1.stack) =
      call_env q (push_env (inter t1.locals
                (inter names (union (delete v l2) (delete var l6)))) T
             (dec_clock t1))` by (fs [call_env_def,push_env_def,dec_clock_def])
  \\ fs [] \\ REPEAT STRIP_TAC \\ POP_ASSUM (K ALL_TAC)
  \\ POP_ASSUM (K ALL_TAC)
  \\ FIRST_X_ASSUM MATCH_MP_TAC \\ fs []
  \\ STRIP_TAC THEN1
   (fs [state_rel_def,set_var_def,lookup_insert,call_env_def,
      push_env_def,dec_clock_def,jump_exc_def]
    \\ POP_ASSUM (ASSUME_TAC o GSYM) \\ fs [LASTN_LEMMA]
    \\ SRW_TAC [] [] \\ fs []
    \\ Q.PAT_X_ASSUM `inter s.locals names = r'.locals` (ASSUME_TAC o GSYM)
    \\ fs [] \\ fs [lookup_inter_alt,domain_inter,domain_union,
         domain_delete,domain_list_insert] \\ SRW_TAC [] [])
  \\ fs [state_rel_def,set_var_def,lookup_insert,call_env_def,
      push_env_def,dec_clock_def,jump_exc_def]
  \\ POP_ASSUM (ASSUME_TAC o GSYM) \\ fs [LASTN_LEMMA]
  \\ SRW_TAC [] [] \\ fs []
  \\ Cases_on `LASTN (r'.handler + 1) r'.stack` \\ fs []
  \\ Cases_on `h` \\ fs []
  \\ SRW_TAC [] [] \\ fs []
  \\ Cases_on `LASTN (t1.handler + 1) t1.stack` \\ fs []
  \\ Cases_on `h` \\ fs []
  \\ SRW_TAC [] [] \\ fs []);

Theorem compile_correct:
   !c s. FST (evaluate (c,s)) <> SOME (Rerr(Rabort Rtype_error)) /\
         FST (evaluate (c,s)) <> NONE ==>
         (evaluate (FST (compile c LN),s) = evaluate (c,s))
Proof
  REPEAT STRIP_TAC
  \\ (evaluate_compile |> ONCE_REWRITE_RULE [SPLIT_PAIR]
       |> SIMP_RULE std_ss [] |> Q.SPECL [`c`,`s`,`LN`,`s`]
       |> SIMP_RULE std_ss [state_rel_ID] |> MP_TAC)
  \\ fs [] \\ REPEAT STRIP_TAC
  \\ Cases_on `evaluate (c,s)` \\ fs []
  \\ Cases_on `evaluate (FST (compile c LN),s)` \\ fs []
  \\ SRW_TAC [] [] \\ Cases_on `q` \\ fs []
  \\ IMP_RES_TAC evaluate_locals_LN
  \\ fs [state_rel_def,state_component_equality]
  \\ (Q.ISPECL_THEN [`c`,`s`] mp_tac evaluate_stack)
  \\ (Q.ISPECL_THEN [`FST (compile c LN)`,`s`]mp_tac evaluate_stack)
  \\ fs [] \\ Cases_on `x` \\ fs []
  \\ Cases_on`e`>>fs[] \\ Cases_on`a`>>fs[]
  \\ REPEAT STRIP_TAC \\ fs [] \\ SRW_TAC [] [] \\ fs []
QED

Theorem get_code_labels_compile:
   ∀x y. get_code_labels (FST (compile x y)) ⊆ get_code_labels x
Proof
  recInduct data_liveTheory.compile_ind
  \\ rw[data_liveTheory.compile_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ fs[SUBSET_DEF]
QED

val _ = export_theory();
