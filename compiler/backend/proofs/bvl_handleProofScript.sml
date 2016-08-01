open preamble bvl_handleTheory bvlSemTheory bvlPropsTheory;
open indexedListsTheory;

val _ = new_theory"bvl_handleProof";

(* TODO: move, and open indexedListsTheory in preamble *)

val MAPi_ID = store_thm("MAPi_ID[simp]",
  ``MAPi (\x y. y) = I``,
  fs [FUN_EQ_THM] \\ Induct \\ fs [o_DEF]);

(* -- *)

val evaluate_SmartLet = store_thm("evaluate_SmartLet[simp]",
  ``bvlSem$evaluate ([SmartLet xs x],env,s) = evaluate ([Let xs x],env,s)``,
  rw [SmartLet_def] \\ fs [LENGTH_NIL,evaluate_def]);

val let_ok_def = Define `
  (let_ok (Let xs b) <=> EVERY isVar xs /\ bVarBound (LENGTH xs) [b]) /\
  (let_ok _ = F)`;

val handle_ok_def = tDefine "handle_ok" `
  (handle_ok [] <=> T) /\
  (handle_ok ((x:bvl$exp)::y::xs) <=>
     handle_ok [x] /\ handle_ok (y::xs)) /\
  (handle_ok [Var v] <=> T) /\
  (handle_ok [If x1 x2 x3] <=>
     handle_ok [x1] /\ handle_ok [x2] /\ handle_ok [x3]) /\
  (handle_ok [Let xs x2] <=>
     if LENGTH xs = 0 then
       let_ok x2 /\ (!ys y. x2 = Let ys y ==> handle_ok [y])
     else
       handle_ok xs /\ handle_ok [x2]) /\
  (handle_ok [Raise x1] <=> handle_ok [x1]) /\
  (handle_ok [Tick x1] <=> handle_ok [x1]) /\
  (handle_ok [Op op xs] <=> handle_ok xs) /\
  (handle_ok [Handle x1 x2] <=>
     case x1 of
     | Let xs b =>
         EVERY isVar xs /\ bVarBound (LENGTH xs) [b] /\
         handle_ok [b] /\ handle_ok [x2]
     | _ => F) /\
  (handle_ok [Call ticks dest xs] <=> handle_ok xs)`
  (WF_REL_TAC `measure (exp1_size)`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
   \\ SRW_TAC [] [bvlTheory.exp_size_def] \\ DECIDE_TAC);

val no_raise_evaluate = store_thm("no_raise_evaluate",
  ``!xs env s1 res r.
      no_raise xs /\ (evaluate (xs,env,s1) = (res,r)) ==>
      !a. res <> Rerr (Rraise a)``,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC \\ rw []
  \\ pop_assum mp_tac \\ fs []
  \\ once_rewrite_tac [evaluate_def] \\ fs [no_raise_def]
  \\ every_case_tac \\ fs [] \\ res_tac \\ fs []
  \\ CCONTR_TAC \\ rw [] \\ fs [] \\ rveq
  \\ imp_res_tac do_app_err \\ fs []);

val evaluate_GENLIST = save_thm("evaluate_GENLIST",
  evaluate_genlist_vars
  |> Q.SPECL[`0`,`env ++ ys`,`LENGTH (env:bvlSem$v list)`,`s`]
  |> SIMP_RULE(srw_ss()++ETA_ss)[TAKE_APPEND1]);

val env_rel_def = Define `
  env_rel l env env1 =
    LIST_RELi (\i v1 v2. has_var i l ==> v1 = v2) env env1`

val env_rel_mk_Union = store_thm("env_rel_mk_Union",
  ``!env env1. env_rel (mk_Union lx ly) env env1 <=>
               env_rel lx env env1 /\ env_rel ly env env1``,
  fs [LIST_RELi_EL_EQN,env_rel_def] \\ metis_tac []);

val env_rel_length = store_thm("env_rel_length",
  ``env_rel l env env1 ==> LENGTH env1 = LENGTH env``,
  fs [LIST_RELi_EL_EQN,env_rel_def]);

val env_rel_MAPi = store_thm("env_rel_MAPi",
  ``env_rel l1 env (MAPi (\i v. if has_var i l1 then v else Number 0) env)``,
  fs [LIST_RELi_EL_EQN,env_rel_def]);

val IMP_EL_SING = store_thm("IMP_EL_SING",
  ``k = LENGTH xs ==> EL k (xs ++ [x] ++ ys) = x``,
  rw [] \\ fs [] \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [EL_APPEND2]);

val ALOOKUP_MAPi_SWAP = store_thm("ALOOKUP_MAPi_SWAP",
  ``!z n k xs.
      n <> k ==>
      ALOOKUP (MAPi (λi x. (x,i+z)) (xs ++ [k])) n =
      ALOOKUP (MAPi (λi x. (x,i+z)) xs) n``,
  Induct_on `xs` \\ fs [o_DEF,ADD1]) |> Q.SPEC `0` |> SIMP_RULE std_ss [];

val ALOOKUP_MAPi_APPEND2 = store_thm("ALOOKUP_MAPi_APPEND2",
  ``!z xs k.
      ~MEM k xs ==>
      ALOOKUP (MAPi (λi x. (x,i+z)) (xs ++ [k])) k = SOME (LENGTH xs + z)``,
  Induct_on `xs` \\ fs [o_DEF,ADD1]) |> Q.SPEC `0` |> SIMP_RULE std_ss [];

val evaluate_LetLet = store_thm("evaluate_LetLet",
  ``(∀env2 extra.
       env_rel l1 env env2 ==> evaluate ([y],env2 ++ extra,s1) = res) /\
    env_rel l1 env env1 ==>
    evaluate ([LetLet (LENGTH env) l1 y],env1 ++ extra,s1) = res``,
  fs [LetLet_def] \\ rw [o_DEF] \\ fs [Once evaluate_def]
  \\ qabbrev_tac `qs = (FILTER (λn. has_var n l1) (GENLIST I (LENGTH env)))`
  \\ `evaluate
        (MAP Var qs,env1 ++ extra,s1) =
        (Rval (MAP (\i. EL i env) qs), s1)` by
   (`EVERY (\n. has_var n l1 /\ n < LENGTH env) qs` by
      (fs [EVERY_MEM] \\ unabbrev_all_tac \\ fs [MEM_FILTER,MEM_GENLIST])
    \\ ntac 2 (pop_assum mp_tac \\ pop_assum kall_tac)
    \\ Induct_on `qs` \\ fs [evaluate_def]
    \\ once_rewrite_tac [evaluate_CONS]
    \\ rw [] \\ fs [evaluate_def]
    \\ imp_res_tac env_rel_length \\ fs [EL_APPEND1]
    \\ fs [env_rel_def,LIST_RELi_EL_EQN])
  \\ fs [evaluate_def]
  \\ qpat_abbrev_tac `ev = bvlSem$evaluate _`
  \\ qsuff_tac `ev =
       (Rval (MAPi (\i v. if has_var i l1 then v else Number 0) env),s1)`
  THEN1
   (fs [] \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC] \\ strip_tac
    \\ first_x_assum match_mp_tac \\ fs [env_rel_MAPi])
  \\ unabbrev_all_tac \\ rpt (pop_assum kall_tac)
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
  \\ qspec_tac (`env1 ++ extra`,`ex`)
  \\ qspec_tac (`env`,`env`)
  \\ HO_MATCH_MP_TAC SNOC_INDUCT \\ rw [] \\ fs [evaluate_def]
  \\ fs [GENLIST,SNOC_APPEND,FILTER,FILTER_APPEND]
  \\ fs [REWRITE_RULE [SNOC_APPEND] evaluate_SNOC,MAP_APPEND]
  \\ qpat_abbrev_tac `ev = bvlSem$evaluate _`
  \\ `ev = (Rval (MAPi (λi v. if has_var i l1 then v else Number 0) env),s1)` by
   (unabbrev_all_tac
    \\ pop_assum (qspec_then `MAP (λi. EL i (env ++ [x]))
         (if has_var (LENGTH env) l1 then [LENGTH env] else []) ++ ex` mp_tac)
    \\ disch_then (fn th => fs [GSYM th])
    \\ AP_TERM_TAC \\ fs [GENLIST_FUN_EQ] \\ rw []
    THEN1
     (ntac 3 (AP_TERM_TAC ORELSE AP_THM_TAC)
      \\ match_mp_tac ALOOKUP_MAPi_SWAP \\ fs [])
    \\ fs [MAP_EQ_f,MEM_FILTER,MEM_GENLIST,EL_APPEND1] \\ NO_TAC) \\ fs []
  \\ `ALOOKUP
        (MAPi (λi x. (x,i))
          (FILTER (λn. has_var n l1) (GENLIST I (LENGTH env)) ++
           if has_var (LENGTH env) l1 then [LENGTH env] else []))
        (LENGTH env) =
      if has_var (LENGTH env) l1 then
        SOME (LENGTH (FILTER (λn. has_var n l1) (GENLIST I (LENGTH env))))
      else NONE` by
   (IF_CASES_TAC \\ fs []
    \\ TRY (match_mp_tac ALOOKUP_MAPi_APPEND2)
    \\ fs [MEM_FILTER,MEM_GENLIST,ALOOKUP_NONE,o_DEF,MAPi_ID] \\ NO_TAC)
  \\ fs [] \\ reverse (Cases_on `has_var (LENGTH env) l1`) \\ fs []
  \\ fs [evaluate_def,do_app_def,MAPi_def,MAPi_APPEND]
  \\ fs [EL_APPEND2] \\ match_mp_tac IMP_EL_SING \\ fs []);

val env_rel_refl = store_thm("env_rel_refl",
  ``env_rel l env env``,
  fs [LIST_RELi_EL_EQN,env_rel_def]);

val OptionalLetLet_IMP = prove(
  ``(ys,l,s') = OptionalLetLet y (LENGTH env) lx s1 limit /\
    (∀env2 extra.
      env_rel l env env2 ⇒ evaluate ([y],env2 ++ extra,s) = res) /\
    env_rel l env env1 ==>
    evaluate (ys,env1 ++ extra,s) = res``,
  rw [OptionalLetLet_def,evaluate_def]
  \\ drule evaluate_LetLet \\ fs []);

val OptionalLetLet_limit = store_thm("OptionalLetLet_limit",
  ``(ys,l,s') = OptionalLetLet e (LENGTH env) lx s1 limit ==> l = lx``,
  rw [OptionalLetLet_def]);

val compile_correct = store_thm("compile_correct",
  ``!xs env s1 ys env1 res s2 extra l s.
      compile limit (LENGTH env) xs = (ys,l,s) /\ env_rel l env env1 /\
      (evaluate (xs,env,s1) = (res,s2)) /\ res <> Rerr(Rabort Rtype_error) ==>
      (evaluate (ys,env1 ++ extra,s1) = (res,s2))``,
  SIMP_TAC std_ss [Once EQ_SYM_EQ]
  \\ recInduct evaluate_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [compile_def,evaluate_def]
  \\ fs [LET_THM] \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs [env_rel_mk_Union]
  \\ imp_res_tac compile_sing \\ rveq
  \\ imp_res_tac env_rel_length
  \\ TRY
   (imp_res_tac OptionalLetLet_limit \\ rveq \\ fs []
    \\ drule (GEN_ALL OptionalLetLet_IMP)
    \\ disch_then match_mp_tac
    \\ fs [] \\ rpt strip_tac
    \\ fs [evaluate_def])
  THEN1 (* Cons *)
   (Cases_on `evaluate ([x],env,s)` \\ Cases_on `q` \\ fs []
    \\ Cases_on `evaluate (y::xs,env,r)` \\ Cases_on `q` \\ fs []
    \\ rw[] \\ fs[] \\ res_tac \\ fs []
    \\ SIMP_TAC std_ss [Once evaluate_CONS] \\ fs [])
  THEN1 (* Var *)
   (Cases_on `n < LENGTH env` \\ fs [] \\ rveq
    \\ `n < LENGTH env1 + LENGTH extra` by DECIDE_TAC
    \\ fs [evaluate_def,rich_listTheory.EL_APPEND1]
    \\ fs [env_rel_def,LIST_RELi_EL_EQN])
  THEN1 (* If *)
   (fs [env_rel_mk_Union]
    \\ first_x_assum drule
    \\ Cases_on `evaluate ([x1],env,s)` \\ Cases_on `q` \\ fs []
    \\ disch_then (qspec_then `[]` mp_tac) \\ fs [] \\ rw []
    \\ Cases_on `Boolv T = HD a` \\ fs [] \\ res_tac \\ fs [evaluate_def]
    \\ Cases_on `Boolv F = HD a` \\ fs [] \\ res_tac \\ fs [evaluate_def])
  THEN1 (* Let *)
   (Cases_on `LENGTH xs = 0` \\ fs [LENGTH_NIL] \\ rveq
    \\ fs [evaluate_def,env_rel_mk_Union]
    \\ imp_res_tac OptionalLetLet_limit \\ rveq \\ fs []
    \\ drule (GEN_ALL OptionalLetLet_IMP)
    \\ disch_then match_mp_tac
    \\ fs [env_rel_mk_Union]
    \\ rpt strip_tac
    \\ fs [evaluate_def]
    \\ Cases_on `evaluate (xs,env,s)` \\ Cases_on `q` \\ fs [] \\ rw []
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
    \\ res_tac \\ fs []
    \\ `env_rel l2 (a ++ env) (a ++ env2)` by
     (fs [env_rel_def,LIST_RELi_EL_EQN] \\ rw []
      \\ Cases_on `i < LENGTH a` \\ fs [EL_APPEND1,NOT_LESS,EL_APPEND2] \\ NO_TAC)
    \\ res_tac \\ fs [])
  THEN1 (* Raise *)
   (Cases_on `evaluate ([x1],env,s)` \\ Cases_on `q` \\ fs [] \\ rw []
    \\ res_tac \\ fs [evaluate_def])
  THEN1 (* Handle *)
   (Cases_on `evaluate ([x1],env,s1)` \\ fs []
    \\ `q <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ fs []) \\ fs []
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] \\ fs []
    \\ rename1 `compile limit (LENGTH env) [x1] = ([yy],l1,s3)`
    \\ Cases_on `no_raise [yy]` \\ fs [] \\ rveq \\ res_tac THEN1
     (pop_assum (assume_tac o SPEC_ALL)
      \\ imp_res_tac no_raise_evaluate
      \\ every_case_tac \\ fs [])
    \\ fs [evaluate_def,env_rel_mk_Union]
    \\ drule evaluate_LetLet \\ fs []
    \\ every_case_tac \\ fs [ADD1] \\ rw [] \\ rfs[]
    \\ `env_rel l2 (a::env) (a::env1)` by
     (fs [env_rel_def,LIST_RELi_EL_EQN]
      \\ Cases \\ fs [ADD1]) \\ res_tac \\ fs [])
  THEN1 (* Op *)
   (Cases_on `evaluate (xs,env,s)` \\ Cases_on `q` \\ fs [] \\ rw []
    \\ res_tac \\ fs [evaluate_def])
  THEN1 (* Tick *)
   (Cases_on `s.clock = 0` \\ fs [] \\ rw [evaluate_def])
  THEN1 (* Call *)
   (Cases_on `evaluate (xs,env,s1)` \\ Cases_on `q` \\ fs [] \\ rw[]
    \\ res_tac \\ fs []))
  |> Q.SPECL [`xs`,`env`,`s1`,`ys`,`env`,`res`,`s2`,`[]`]
  |> SIMP_RULE std_ss [APPEND_NIL,env_rel_refl];

val _ = save_thm("compile_correct",compile_correct);

val compile_correct = store_thm("compile_correct",
  ``(evaluate ([x],env,s1) = (res,s2)) /\ res <> Rerr(Rabort Rtype_error) /\
    k = LENGTH env ==>
    (evaluate ([compile_exp l k x],env,s1) = (res,s2))``,
  fs [compile_exp_def]
  \\ Cases_on `compile l (LENGTH env) [x]` \\ PairCases_on `r`
  \\ rw [] \\ imp_res_tac compile_sing \\ rw []
  \\ imp_res_tac compile_correct);

val compile_IMP_LENGTH = store_thm("compile_IMP_LENGTH",
  ``compile l n xs = (ys,l1,s1) ==> LENGTH ys = LENGTH xs``,
  rw [] \\ mp_tac (SPEC_ALL compile_length) \\ asm_simp_tac std_ss []);

val bVarBound_CONS = store_thm("bVarBound_CONS",
  ``bVarBound m [x] /\ bVarBound m xs ==> bVarBound m (x::xs)``,
  Cases_on `xs` \\ fs []);

val bVarBound_MEM = store_thm("bVarBound_MEM",
  ``bVarBound n xs <=> !x. MEM x xs ==> bVarBound n [x]``,
  fs [Once bVarBound_EVERY,EVERY_MEM]);

val bEvery_MEM = store_thm("bEvery_MEM",
  ``bEvery p xs = !x. MEM x xs ==> bEvery p [x]``,
  fs [Once bEvery_EVERY,EVERY_MEM]);

val bVarBound_LESS_EQ = store_thm("bVarBound_LESS_EQ",
  ``!m xs n. bVarBound m xs /\ m <= n ==> bVarBound n xs``,
  HO_MATCH_MP_TAC bVarBound_ind \\ rw [] \\ fs []);

val ALOOKUP_MAPi = store_thm("ALOOKUP_MAPi",
  ``!xs i x.
      ALOOKUP (MAPi (λi x. (x,i)) xs) n = SOME x ==> x < LENGTH xs``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ rw []
  \\ fs [SNOC_APPEND,MAPi_APPEND,ALOOKUP_APPEND]
  \\ every_case_tac \\ fs []);

val bVarBound_SmartLet = store_thm("bVarBound_SmartLet[simp]",
  ``bVarBound m [SmartLet x xs] = bVarBound m [Let x xs]``,
  rw [SmartLet_def] \\ fs [LENGTH_NIL]);

val bVarBound_LetLet = store_thm("bVarBound_LetLet",
  ``bVarBound m [y] /\ n <= m ==> bVarBound m [LetLet n l1 y]``,
  fs [LetLet_def] \\ strip_tac
  \\ once_rewrite_tac [bVarBound_MEM]
  \\ fs [MEM_MAP,MEM_GENLIST,PULL_EXISTS,MEM_FILTER]
  \\ reverse conj_tac
  THEN1 (match_mp_tac bVarBound_LESS_EQ \\ asm_exists_tac \\ fs [])
  \\ rw [] \\ every_case_tac \\ fs []
  \\ qabbrev_tac `xs = FILTER (λn. has_var n l1) (GENLIST I n)`
  \\ imp_res_tac ALOOKUP_MAPi \\ fs []);

val bVarBound_OptionalLetLet = store_thm("bVarBound_OptionalLetLet",
  ``bVarBound m [e] /\ n <= m ==> bVarBound m (FST (OptionalLetLet e n l s limit))``,
  rw [OptionalLetLet_def,bVarBound_LetLet]);

val bVarBound_compile = Q.store_thm("bVarBound_compile",
  `∀l n xs m. n ≤ m ⇒ bVarBound m (FST (compile l n xs))`,
  ho_match_mp_tac compile_ind \\ rw [] \\ fs [compile_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ imp_res_tac compile_sing \\ rw [] \\ res_tac
  \\ imp_res_tac bVarBound_CONS \\ fs []
  \\ TRY (first_x_assum match_mp_tac) \\ fs []
  \\ imp_res_tac compile_IMP_LENGTH \\ fs []
  \\ imp_res_tac bVarBound_LetLet \\ fs []
  \\ match_mp_tac bVarBound_OptionalLetLet \\ fs []);

val compile_IMP_bVarBound = store_thm("compile_IMP_bVarBound",
  ``compile l n xs = (ys,l2,s2) ==> bVarBound n ys``,
  rw [] \\ mp_tac (Q.INST [`m`|->`n`] (SPEC_ALL bVarBound_compile)) \\ fs []);

val bEvery_CONS = store_thm("bEvery_CONS",
  ``bEvery p [x] /\ bEvery p xs ==> bEvery p (x::xs)``,
  Cases_on `xs` \\ fs []);

val handle_ok_Var_Const_list = store_thm("handle_ok_Var_Const_list",
  ``EVERY (\x. ?v i. x = Var v \/ x = Op (Const i) []) xs ==> handle_ok xs``,
  Induct_on `xs` \\ fs [handle_ok_def,PULL_EXISTS] \\ rw []
  \\ Cases_on `xs` \\ fs [handle_ok_def]);

val handle_ok_SmartLet = store_thm("handle_ok_SmartLet",
  ``handle_ok [SmartLet xs x] <=> handle_ok xs /\ handle_ok [x]``,
  rw [SmartLet_def,handle_ok_def] \\ fs [LENGTH_NIL,handle_ok_def]);

val handle_ok_OptionalLetLet = store_thm("handle_ok_OptionalLetLet",
  ``handle_ok [e] /\ bVarBound n [e] ==>
    handle_ok (FST (OptionalLetLet e n lx s l))``,
  rw [OptionalLetLet_def] \\ fs [handle_ok_def]
  \\ reverse conj_tac THEN1
   (fs [LetLet_def,handle_ok_SmartLet]
    \\ match_mp_tac handle_ok_Var_Const_list
    \\ rw [EVERY_MEM,MEM_GENLIST] \\ every_case_tac \\ fs [])
  \\ fs [let_ok_def,LetLet_def]
  \\ fs [LetLet_def,EVERY_MEM,MEM_MAP,PULL_EXISTS,isVar_def]
  \\ conj_tac THEN1
     (once_rewrite_tac [bVarBound_MEM]
      \\ fs [MEM_GENLIST,PULL_EXISTS] \\ rw []
      \\ every_case_tac \\ fs []
      \\ imp_res_tac ALOOKUP_MAPi \\ fs [])
  \\ match_mp_tac bVarBound_LESS_EQ \\ asm_exists_tac \\ fs []);

val compile_handle_ok = store_thm("compile_handle_ok",
  ``∀l n xs. handle_ok (FST (compile l n xs))``,
  ho_match_mp_tac compile_ind \\ rw []
  \\ fs [compile_def,handle_ok_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ imp_res_tac compile_sing \\ rw [] \\ res_tac
  THEN1 (Cases_on `dy` \\ fs [handle_ok_def])
  \\ fs [handle_ok_def]
  \\ fs [LetLet_def,EVERY_MEM,MEM_MAP,PULL_EXISTS,isVar_def]
  \\ imp_res_tac compile_IMP_LENGTH \\ fs []
  \\ TRY (match_mp_tac handle_ok_OptionalLetLet)
  \\ fs [handle_ok_def]
  \\ TRY (imp_res_tac compile_IMP_bVarBound \\ fs [] \\ NO_TAC)
  \\ conj_tac THEN1
   (conj_tac THEN1
     (once_rewrite_tac [bVarBound_MEM]
      \\ fs [MEM_GENLIST,PULL_EXISTS] \\ rw []
      \\ every_case_tac \\ fs []
      \\ imp_res_tac ALOOKUP_MAPi \\ fs [])
    \\ fs [handle_ok_def]
    \\ `[y'] = FST (compile l n [x1])` by fs []
    \\ pop_assum (fn th => rewrite_tac [th])
    \\ match_mp_tac bVarBound_compile \\ fs [])
  \\ rw [SmartLet_def] \\ fs [handle_ok_def]
  \\ rpt (pop_assum kall_tac)
  \\ match_mp_tac handle_ok_Var_Const_list
  \\ fs [EVERY_GENLIST]
  \\ rw [] \\ every_case_tac \\ fs []);

val compile_exp_handle_ok = store_thm("compile_exp_handle_ok",
  ``handle_ok [compile_exp l n x]``,
  fs [bvl_handleTheory.compile_exp_def]
  \\ Cases_on `compile l n [x]` \\ fs [] \\ PairCases_on `r`
  \\ imp_res_tac bvl_handleTheory.compile_sing \\ fs []
  \\ qspecl_then [`l`,`n`,`[x]`] mp_tac compile_handle_ok \\ fs []);

val _ = export_theory();
