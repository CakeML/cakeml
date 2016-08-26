open preamble bvl_constTheory bvlSemTheory bvlPropsTheory;

val _ = new_theory"bvl_constProof";

val v_rel_def = Define `
  v_rel (:'a) a x y xs ys =
    case a of
    | Var n => LLOOKUP ys n = SOME x
    | Op _ _ => !(s:'a bvlSem$state) env. evaluate ([a],env,s) = (Rval [x],s)
    | _ => F`;

val env_rel_def = Define `
  (env_rel (:'a) [] e1 e2 = (e1 = e2)) /\
  (env_rel (:'a) (NONE::rest) (x::e1) (y::e2) <=>
     (x = y) /\ env_rel (:'a) rest e1 e2) /\
  (env_rel (:'a) (SOME a::rest) (x::e1) (y::e2) <=>
     v_rel (:'a) a x y (x::e1) (y::e2) /\ env_rel (:'a) rest e1 e2) /\
  (env_rel _ _ _ _ = F)`

val env_rel_length = store_thm("env_rel_length",
  ``!ax env env2. env_rel (:α) ax env env2 ==> LENGTH env2 = LENGTH env``,
  Induct \\ Cases_on `env` \\ Cases_on `env2` \\ fs [env_rel_def]
  \\ Cases \\ fs [env_rel_def]);

val env_rel_LLOOKUP_NONE = prove(
  ``!ax env env2 n.
      env_rel (:α) ax env env2 /\
      (LLOOKUP ax n = NONE \/ LLOOKUP ax n = SOME NONE) ==>
      EL n env2 = EL n env``,
  Induct \\ Cases_on `env` \\ Cases_on `env2` \\ fs [env_rel_def]
  \\ Cases \\ fs [env_rel_def,LLOOKUP_def]
  \\ rw [] \\ fs [] \\ Cases_on `n` \\ fs [EL]);

val env_rel_LOOKUP_SOME = prove(
  ``!env env2 ax x n.
      env_rel (:α) ax env env2 /\
      LLOOKUP ax n = SOME (SOME x) ==>
      v_rel (:'a) x (EL n env) (EL n env2) (DROP n env) (DROP n env2)``,
  Induct \\ Cases_on `env2` \\ Cases_on `ax` \\ fs [env_rel_def,LLOOKUP_def]
  \\ rw [] \\ fs [env_rel_def] \\ res_tac \\ fs []
  \\ Cases_on `n` \\ fs [env_rel_def]
  \\ first_x_assum match_mp_tac
  \\ Cases_on `h'` \\ fs [env_rel_def]);

val evaluate_delete_var_Rerr_SING = store_thm("evaluate_delete_var_Rerr_SING",
  ``!x s r e env2.
      evaluate ([x],env2,s) = (Rerr e,r) /\
      e <> Rabort Rtype_error ==>
      evaluate ([bvl_const$delete_var x],env2,s) = (Rerr e,r)``,
  Cases \\ fs [delete_var_def]
  \\ fs [evaluate_def,do_app_def] \\ rw []
  \\ CCONTR_TAC \\ fs [] \\ rw []);

val evaluate_delete_var_Rerr = prove(
  ``!xs s r e env2.
      evaluate (xs,env2,s) = (Rerr e,r) /\
      e <> Rabort Rtype_error ==>
      evaluate (MAP bvl_const$delete_var xs,env2,s) = (Rerr e,r)``,
  Induct \\ fs [] \\ once_rewrite_tac [evaluate_CONS]
  \\ rw [] \\ every_case_tac \\ fs [] \\ rw []
  \\ TRY (drule evaluate_delete_var_Rerr_SING \\ fs [])
  \\ res_tac \\ fs []
  \\ Cases_on `h` \\ fs [delete_var_def]
  \\ rw [] \\ fs []
  \\ fs [evaluate_def,do_app_def] \\ rw []
  \\ every_case_tac \\ fs [] \\ rw []);

val evaluate_delete_var_Rval = prove(
  ``!xs env2 s a r ax env.
      evaluate (xs,env2,s:'a bvlSem$state) = (Rval a,r) /\
      env_rel (:'a) ax env env2 ==>
      ?b. evaluate (MAP delete_var xs,env2,s) = (Rval b,r) /\
          env_rel (:'a) (extract_list xs ++ ax) (a ++ env) (b ++ env2)``,
  Induct \\ fs [env_rel_def,extract_list_def]
  \\ once_rewrite_tac [evaluate_CONS]
  \\ rw [] \\ Cases_on `evaluate ([h],env2,s)` \\ fs []
  THEN1 (imp_res_tac evaluate_IMP_LENGTH \\ Cases_on `a` \\ fs [])
  \\ Cases_on `q` \\ fs []
  \\ Cases_on `?i. h = Var i` \\ fs []
  THEN1
   (rw [] \\ fs [delete_var_def,evaluate_def,do_app_def]
    \\ every_case_tac \\ fs [] \\ rw []
    \\ res_tac \\ fs [extract_def,env_rel_def] \\ rw []
    \\ fs [v_rel_def,LLOOKUP_EQ_EL]
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
    \\ fs [GSYM ADD1,ADD_CLAUSES,EL_APPEND2])
  \\ `delete_var h = h` by (Cases_on `h` \\ fs [delete_var_def]) \\ fs []
  \\ Cases_on `evaluate (xs,env2,r')` \\ fs [] \\ Cases_on `q` \\ fs []
  \\ res_tac \\ fs [] \\ rw []
  \\ Cases_on `extract h xs` \\ fs [env_rel_def]
  \\ imp_res_tac evaluate_SING \\ rw [] \\ fs []
  \\ Cases_on `h` \\ fs [extract_def]
  \\ rename1 `bvl_const$extract (Op opp ll) _ = SOME xx`
  \\ Cases_on `opp` \\ fs [extract_def] \\ rw []
  \\ every_case_tac \\ fs []
  \\ fs [v_rel_def,NULL_EQ,evaluate_def,do_app_def]
  \\ every_case_tac \\ fs []);

val IS_SOME_dest_Op_Const = store_thm("IS_SOME_dest_Op_Const[simp]",
  ``IS_SOME (dest_Op_Const h) = ?i. h = Op (Const i) []``,
  Cases_on `h` \\ fs [dest_Op_Const_def]
  \\ Cases_on `o'` \\ fs [dest_Op_Const_def]
  \\ rw [] \\ fs [NULL_EQ]);

val evaluate_EQ_NIL = store_thm("evaluate_EQ_NIL",
  ``bvlSem$evaluate (xs,env,s) = (Rval [],t) <=> xs = [] /\ s = t``,
  mp_tac (Q.SPECL [`xs`,`env`,`s`] evaluate_LENGTH)
  \\ every_case_tac \\ fs []
  \\ rw [] \\ TRY eq_tac \\ fs [] \\ rw [] \\ fs [LENGTH_NIL]
  \\ CCONTR_TAC \\ fs [] \\ fs [evaluate_def]);

val is_simple_thm = store_thm("is_simple_thm",
  ``is_simple v <=> (?t. v = Op (Cons t) []) \/ (?i. v = Op (Const i) [])``,
  Cases_on `v` \\ fs [is_simple_def]
  \\ Cases_on `o'` \\ fs [is_simple_def,NULL_EQ]);

val SmartOp_thm = store_thm("SmartOp_thm",
  ``evaluate ([Op op xs],env,s) = (res,s2) /\
    res ≠ Rerr (Rabort Rtype_error) ==>
    evaluate ([SmartOp op xs],env,s) = (res,s2)``,
  full_simp_tac std_ss [SmartOp_def]
  \\ reverse (Cases_on `op`) \\ fs [] \\ every_case_tac \\ fs []
  \\ fs [quantHeuristicsTheory.LIST_LENGTH_7] \\ rw []
  \\ fs [dest_Op_Const_def,evaluate_def,do_app_def] \\ rw []
  \\ fs [dest_Op_Const_def,evaluate_def,do_app_def] \\ rw []
  \\ rfs [] \\ fs [is_simple_thm] \\ rfs [] \\ rw []
  \\ fs [dest_Op_Const_def,evaluate_def,do_app_def] \\ rw []
  \\ eq_tac \\ rw []);

val evaluate_env_rel = store_thm("evaluate_env_rel",
  ``!xs env1 (s1:'a bvlSem$state) ax env2 res s2 ys.
      (evaluate (xs,env1,s1) = (res,s2)) /\
      env_rel (:'a) ax env1 env2 /\
      res <> Rerr (Rabort Rtype_error) ==>
      (evaluate (compile ax xs,env2,s1) = (res,s2))``,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [compile_def,evaluate_def,compile_HD_SING]
  THEN1
   (`?y0. compile ax [x] = [y0]` by
     (`LENGTH (compile ax [x]) = LENGTH [x]` by fs [compile_length]
      \\ Cases_on `compile ax [x]` \\ fs [LENGTH_NIL])
    \\ `?y1 ys. compile ax (y::xs) = y1::ys` by
     (`LENGTH (compile ax (y::xs)) = LENGTH (y::xs)` by fs [compile_length]
      \\ Cases_on `compile ax (y::xs)` \\ fs [LENGTH_NIL])
    \\ fs [] \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
    \\ rpt (first_x_assum drule) \\ fs []
    \\ rw [] \\ rpt (first_x_assum drule) \\ fs [] \\ rw []
    \\ fs [evaluate_def])
  THEN1
   (Cases_on `n < LENGTH env` \\ fs [] \\ rw []
    \\ Cases_on `LLOOKUP ax n` \\ fs []
    \\ imp_res_tac env_rel_length
    THEN1 (fs [evaluate_def] \\ metis_tac [env_rel_LLOOKUP_NONE])
    \\ CASE_TAC
    THEN1 (fs [evaluate_def] \\ metis_tac [env_rel_LLOOKUP_NONE])
    \\ CASE_TAC
    \\ drule env_rel_LOOKUP_SOME \\ fs [] \\ fs [v_rel_def]
    \\ disch_then drule \\ fs [] \\ rw []
    \\ fs [evaluate_def]
    \\ fs [LLOOKUP_EQ_EL]
    \\ fs [EL_DROP] \\ rfs [EL_DROP])
  THEN1
   (Cases_on `evaluate ([x1],env,s)` \\ fs []
    \\ Cases_on `q` \\ fs [] \\ rw [] \\ res_tac \\ fs []
    \\ every_case_tac \\ fs []
    \\ imp_res_tac evaluate_SING \\ fs [] \\ rveq \\ fs []
    \\ res_tac \\ fs []
    \\ fs [evaluate_def,compile_HD_SING]
    \\ imp_res_tac (prove(``x = y ==> [x] = [y]``,fs []))
    \\ full_simp_tac std_ss [compile_HD_SING]
    \\ fs [evaluate_def,EVAL ``Bool T``,EVAL ``Bool F``])
  THEN1
   (fs [LET_THM,evaluate_def]
    \\ Cases_on `evaluate (xs,env,s)` \\ fs []
    \\ Cases_on `q` \\ fs [] \\ rw []
    \\ res_tac \\ fs []
    \\ imp_res_tac evaluate_delete_var_Rerr \\ fs []
    \\ drule evaluate_delete_var_Rval \\ fs [compile_HD_SING]
    \\ disch_then drule \\ strip_tac \\ fs [])
  THEN1
   (Cases_on `evaluate ([x1],env,s)` \\ fs []
    \\ Cases_on `q` \\ fs [] \\ rw [] \\ res_tac \\ fs []
    \\ every_case_tac \\ fs [])
  THEN1
   (Cases_on `evaluate ([x1],env,s1)` \\ fs [] \\ Cases_on `q` \\ fs []
    \\ res_tac \\ rw [] \\ Cases_on `e` \\ fs [] \\ rw [] \\ fs []
    \\ first_x_assum match_mp_tac
    \\ fs [env_rel_def])
  \\ TRY (match_mp_tac SmartOp_thm)
  \\ fs [evaluate_def] \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ res_tac \\ fs [] \\ rw [] \\ fs [] \\ rw [] \\ fs []);

val compile_thm = save_thm("compile_thm",
  evaluate_env_rel
  |> Q.SPECL [`xs`,`env`,`s1`,`[]`,`env`] |> GEN_ALL
  |> SIMP_RULE std_ss [env_rel_def])

val evaluate_compile_exp = store_thm("evaluate_compile_exp",
  ``evaluate ([d],env,s) = (r,t) /\
    r <> Rerr (Rabort Rtype_error) ==>
    evaluate ([bvl_const$compile_exp d],env,s) = (r,t)``,
  fs [compile_exp_def]
  \\ `LENGTH (compile [] [d]) = LENGTH [d]` by fs [compile_length]
  \\ Cases_on `compile [] [d]` \\ fs [LENGTH_NIL] \\ rw []
  \\ imp_res_tac compile_thm \\ rfs []);

val _ = export_theory();
