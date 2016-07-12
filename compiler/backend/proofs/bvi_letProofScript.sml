open preamble bvi_letTheory bviSemTheory bviPropsTheory;

val _ = new_theory"bvi_letProof";

val v_rel_def = Define `
  v_rel a x y xs ys <=> LLOOKUP ys a = SOME x`;

val env_rel_def = Define `
  (env_rel [] d e1 e2 = (e1 = DROP d e2)) /\
  (env_rel (a::rest) d (x::e1) (y::e2) <=>
     v_rel a x y (x::e1) (y::e2) /\ env_rel rest d e1 e2) /\
  (env_rel _ _ _ _ = F)`

val env_rel_length = store_thm("env_rel_length",
  ``!ax env env2. env_rel ax d env env2 ==> LENGTH env <= LENGTH env2``,
  Induct \\ Cases_on `env` \\ Cases_on `env2` \\ fs [env_rel_def]
  \\ rw [] \\ Cases_on `d` \\ fs []
  \\ imp_res_tac (METIS_PROVE [] ``x=y ==> LENGTH x = LENGTH y``) \\ fs []);

val env_rel_LLOOKUP_NONE = prove(
  ``!ax env env2 n d.
      env_rel ax d env env2 /\
      LLOOKUP ax n = NONE /\
      n < LENGTH env ==>
      n+d < LENGTH env2 /\
      EL (n+d) env2 = EL n env``,
  Induct THEN1 (fs [env_rel_def,LLOOKUP_def,EL_DROP])
  \\ Cases_on `env` \\ Cases_on `env2` \\ fs [env_rel_def]
  \\ rw [] \\ Cases_on `n` \\ fs []
  \\ res_tac \\ fs [LLOOKUP_def] \\ rfs [] \\ fs[ADD_CLAUSES]);

val env_rel_LOOKUP_SOME = prove(
  ``!env env2 ax x n d.
      env_rel ax d env env2 /\
      LLOOKUP ax n = SOME x ==>
      v_rel x (EL n env) (EL n env2) (DROP n env) (DROP n env2)``,
  Induct \\ Cases_on `env2` \\ Cases_on `ax` \\ fs [env_rel_def,LLOOKUP_def]
  \\ rw [] \\ fs [env_rel_def] \\ res_tac \\ fs []
  \\ Cases_on `n` \\ fs [env_rel_def]
  \\ first_x_assum match_mp_tac
  \\ Cases_on `h'` \\ fs [env_rel_def]);

val evaluate_delete_var_Rerr_SING = store_thm("evaluate_delete_var_Rerr_SING",
  ``!x s r e env2.
      evaluate ([x],env2,s) = (Rerr e,r) /\
      e <> Rabort Rtype_error ==>
      evaluate ([delete_var x],env2,s) = (Rerr e,r)``,
  Cases \\ fs [delete_var_def]
  \\ fs [evaluate_def,do_app_def] \\ rw []
  \\ CCONTR_TAC \\ fs [] \\ rw []);

val evaluate_delete_var_Rerr = prove(
  ``!xs s r e env2.
      evaluate (xs,env2,s) = (Rerr e,r) /\
      e <> Rabort Rtype_error ==>
      evaluate (MAP delete_var xs,env2,s) = (Rerr e,r)``,
  Induct \\ fs [] \\ once_rewrite_tac [evaluate_CONS]
  \\ rw [] \\ every_case_tac \\ fs [] \\ rw []
  \\ TRY (drule evaluate_delete_var_Rerr_SING \\ fs [])
  \\ res_tac \\ fs []
  \\ Cases_on `h` \\ fs [delete_var_def]
  \\ rw [] \\ fs [] \\ fs [evaluate_def,do_app_def,do_app_aux_def] \\ rw []
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs [] \\ rw []
  \\ pop_assum mp_tac \\ EVAL_TAC);

val evaluate_delete_var_Rval = prove(
  ``!xs env2 s a r ax env d.
      evaluate (xs,env2,s:'a bviSem$state) = (Rval a,r) /\
      env_rel ax d env env2 ==>
      ?b. evaluate (MAP delete_var xs,env2,s) = (Rval b,r) /\
          env_rel (extract_list xs ++ ax) d (a ++ env) (b ++ env2)``,
  Induct \\ fs [env_rel_def,extract_list_def]
  \\ once_rewrite_tac [evaluate_CONS]
  \\ rw [] \\ Cases_on `evaluate ([h],env2,s)` \\ fs []
  THEN1 (imp_res_tac evaluate_IMP_LENGTH \\ Cases_on `a` \\ fs [])
  \\ Cases_on `q` \\ fs []
  \\ Cases_on `?i. h = Var i` \\ fs []
  THEN1
   (rw [] \\ fs [delete_var_def,evaluate_def,do_app_def,
                 do_app_aux_def,EVAL ``small_enough_int 0``]
    \\ every_case_tac \\ fs [] \\ rw []
    \\ res_tac \\ fs [extract_def,env_rel_def] \\ rw []
    \\ fs [v_rel_def,LLOOKUP_EQ_EL]
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
    \\ fs [GSYM ADD1,ADD_CLAUSES,EL_APPEND2])
  \\ `delete_var h = h` by (Cases_on `h` \\ fs [delete_var_def]) \\ fs []
  \\ Cases_on `evaluate (xs,env2,r')` \\ fs [] \\ Cases_on `q` \\ fs []
  \\ res_tac \\ fs [] \\ rw []
  \\ `extract h xs = 0` by (Cases_on `h` \\ fs [extract_def]) \\ fs []
  \\ imp_res_tac evaluate_SING_IMP \\ rw [] \\ fs []
  \\ fs [v_rel_def,env_rel_def,LLOOKUP_def]);

val evaluate_SNOC_Rval = store_thm("evaluate_SNOC_Rval",
  ``evaluate (SNOC x y,env,s) = (Rval a,r) ==>
    ?a1 a2 r1.
      a = SNOC a1 a2 /\ LENGTH y = LENGTH a2 /\
      evaluate (y,env,s) = (Rval a2,r1) /\
      evaluate ([x],env,r1) = (Rval [a1],r)``,
  fs [evaluate_SNOC]
  \\ every_case_tac \\ fs []
  \\ imp_res_tac evaluate_SING_IMP \\ rw []
  \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []);

val compile_CONS = store_thm("compile_CONS",
  ``compile ax d (x::xs) = compile ax d [x] ++ compile ax d xs``,
  Cases_on `xs` \\ fs [compile_def]);

val compile_APPEND = store_thm("compile_APPEND",
  ``!xs ys ax d. compile ax d (xs ++ ys) = compile ax d xs ++ compile ax d ys``,
  Induct \\ fs [compile_def]
  \\ once_rewrite_tac [compile_CONS] \\ fs []);

val evaluate_env_rel = store_thm("evaluate_env_rel",
  ``!xs env1 (s1:'a bviSem$state) ax env2 res s2 ys d.
      (evaluate (xs,env1,s1) = (res,s2)) /\
      env_rel ax d env1 env2 /\
      res <> Rerr (Rabort Rtype_error) ==>
      (evaluate (compile ax d xs,env2,s1) = (res,s2))``,

  recInduct evaluate_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [compile_def,evaluate_def,compile_HD_SING]
  THEN1
   (`?y0. compile ax d [x] = [y0]` by
     (`LENGTH (compile ax d [x]) = LENGTH [x]` by fs [compile_length]
      \\ Cases_on `compile ax d [x]` \\ fs [LENGTH_NIL])
    \\ `?y1 ys. compile ax d (y::xs) = y1::ys` by
     (`LENGTH (compile ax d (y::xs)) = LENGTH (y::xs)` by fs [compile_length]
      \\ Cases_on `compile ax d (y::xs)` \\ fs [LENGTH_NIL])
    \\ fs [] \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
    \\ rpt (first_x_assum drule) \\ fs []
    \\ rw [] \\ rpt (first_x_assum drule) \\ fs [] \\ rw []
    \\ fs [evaluate_def])
  THEN1
   (Cases_on `n < LENGTH env` \\ fs [] \\ rw []
    \\ Cases_on `LLOOKUP ax n` \\ fs []
    \\ imp_res_tac env_rel_length
    THEN1 (fs [evaluate_def] \\ metis_tac [env_rel_LLOOKUP_NONE,ADD_COMM])
    \\ drule env_rel_LOOKUP_SOME \\ fs [] \\ fs [v_rel_def]
    \\ disch_then drule \\ fs [] \\ rw []
    \\ fs [evaluate_def]
    \\ fs [LLOOKUP_EQ_EL]
    \\ fs [EL_DROP] \\ rfs [EL_DROP])
  THEN1
   (Cases_on `evaluate ([x1],env,s)` \\ fs []
    \\ Cases_on `q` \\ fs [] \\ rw [] \\ res_tac \\ fs []
    \\ every_case_tac \\ fs [])
  THEN1
   (fs [LET_THM,evaluate_def,LENGTH_NIL]
    \\ Cases_on `evaluate (xs,env,s)` \\ fs []
    \\ IF_CASES_TAC \\ fs []
    THEN1 (fs [evaluate_def] \\ rveq \\ fs [])
    \\ reverse IF_CASES_TAC \\ fs []
    THEN1
     (Cases_on `q` \\ fs [] \\ rw []
      \\ res_tac \\ fs []
      \\ imp_res_tac evaluate_delete_var_Rerr
      \\ fs [evaluate_def,compile_HD_SING]
      \\ drule evaluate_delete_var_Rval \\ fs [compile_HD_SING]
      \\ disch_then drule \\ strip_tac
      \\ fs [evaluate_def,compile_HD_SING])
    \\ rveq \\ fs []
    \\ imp_res_tac (METIS_PROVE [SNOC_CASES] ``m <> [] ==> ?x y. m = SNOC x y``)
    \\ rveq \\ fs []
    \\ reverse (Cases_on `q`) \\ fs[evaluate_def] \\ rveq
    THEN1
     (fs [evaluate_SNOC]
      \\ Cases_on `evaluate (y,env,s)` \\ fs []
      \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
      \\ cheat)
    \\ Cases_on `LENGTH y < LENGTH a + LENGTH env` \\ fs []
    \\ rveq \\ fs [] \\ res_tac
    \\ drule evaluate_SNOC_Rval \\ strip_tac \\ fs[compile_HD_SING]
    \\ fs [compile_APPEND,SNOC_APPEND]
    \\ qpat_assum `_ = (Rval (a2 ++ [a1]),r)` mp_tac
    \\ once_rewrite_tac [GSYM compile_HD_SING]
    \\ rewrite_tac [GSYM SNOC_APPEND] \\ strip_tac
    \\ drule evaluate_SNOC_Rval \\ rewrite_tac [SNOC_11]
    \\ fs [] \\ strip_tac \\ fs[compile_HD_SING]
    \\ full_simp_tac std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND]
    \\ fs [EL_APPEND2]
    \\ cheat (* induction needs to be done differently *))
  THEN1
   (Cases_on `evaluate ([x1],env,s)` \\ fs []
    \\ Cases_on `q` \\ fs [] \\ rw [] \\ res_tac \\ fs []
    \\ every_case_tac \\ fs [])
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ res_tac \\ fs [] \\ rw [] \\ fs [] \\ rw [] \\ fs [compile_HD_SING]
  \\ rw [] \\ first_x_assum match_mp_tac
  \\ fs [env_rel_def] \\ fs [v_rel_def,LLOOKUP_def]);

val compile_thm = save_thm("compile_thm",
  evaluate_env_rel
  |> Q.SPECL [`xs`,`env`,`s1`,`[]`,`env`] |> GEN_ALL
  |> SIMP_RULE std_ss [env_rel_def])

val evaluate_compile_exp = store_thm("evaluate_compile_exp",
  ``evaluate ([d],env,s) = (r,t) /\
    r <> Rerr (Rabort Rtype_error) ==>
    evaluate ([bvi_let$compile_exp d],env,s) = (r,t)``,
  fs [compile_exp_def]
  \\ `LENGTH (compile [] [d]) = LENGTH [d]` by fs [compile_length]
  \\ Cases_on `compile [] [d]` \\ fs [LENGTH_NIL] \\ rw []
  \\ imp_res_tac compile_thm \\ rfs []);

val _ = export_theory();
