(*
  Definitions and theorems supporting ml_progLib, which constructs a
  CakeML program and its semantic environment.
*)
Theory ml_prog
Ancestors
  ast semanticPrimitives evaluate semanticPrimitivesProps
  evaluateProps mlstring integer evaluate_dec namespace
  alist_tree primSemEnv[qualified]
Libs
  preamble


val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

(* --- env operators --- *)

(* Functions write, write_cons, write_mod, empty_env, merge_env should
   never be expanded by EVAL and are therefore defined using
   nocompute. These should never be exanded by EVAL because that would
   cause very slow appends. *)

Definition write_def[nocompute]:
  write name v (env:v sem_env) = env with v := nsBind name v env.v
End

Definition write_cons_def[nocompute]:
  write_cons n d (env:v sem_env) =
    (env with c := nsAppend (nsSing n d) env.c)
End

Definition empty_env_def[nocompute]:
  (empty_env:v sem_env) = <| v := nsEmpty ; c:= nsEmpty|>
End

Definition write_mod_def[nocompute]:
  write_mod mn (env:v sem_env) env2 =
    env2 with <|
      c := nsAppend (nsLift mn env.c) env2.c
      ; v := nsAppend (nsLift mn env.v) env2.v |>
End

Definition merge_env_def[nocompute]:
  merge_env (env2:v sem_env) env1 =
    <| v := nsAppend env2.v env1.v
     ; c := nsAppend env2.c env1.c|>
End

(* the components of nsLookup are 'nicer' partial functions *)

Definition nsLookup_Short_def[nocompute]:
  nsLookup_Short ns nm = nsLookup ns (Short nm)
End

Definition nsLookup_Mod1_def[nocompute]:
  nsLookup_Mod1 ns = (case ns of Bind _ ms => ALOOKUP ms)
End

Theorem nsLookup_eq:
   nsLookup ns (Short nm) = nsLookup_Short ns nm /\
    nsLookup ns (Long mnm id) = (case nsLookup_Mod1 ns mnm of
      NONE => NONE | SOME ns2 => nsLookup ns2 id)
Proof
  fs [nsLookup_Short_def]
  \\ Cases_on `ns`
  \\ fs[nsLookup_Mod1_def, nsLookup_def]
QED

(* base facts about the partial functions *)

Theorem option_choice_f_apply:
   option_choice_f f g x = OPTION_CHOICE (f x) (g x)
Proof
  fs [option_choice_f_def]
QED

Theorem nsLookup_Short_Bind:
   nsLookup_Short (Bind ss ms) = ALOOKUP ss
Proof
  fs [nsLookup_Short_def, nsLookup_def, FUN_EQ_THM]
QED

Theorem nsLookup_Short_nsAppend:
   nsLookup_Short (nsAppend ns1 ns2)
    = option_choice_f (nsLookup_Short ns1) (nsLookup_Short ns2)
Proof
  Cases_on `ns1` \\ Cases_on `ns2`
  \\ fs [nsLookup_Short_Bind, nsAppend_def,
    alookup_append_option_choice_f]
QED

Theorem nsLookup_Mod1_Bind:
   nsLookup_Mod1 (Bind ss ms) nm = ALOOKUP ms nm
Proof
  fs [nsLookup_Mod1_def]
QED

Theorem nsLookup_Mod1_nsAppend:
   nsLookup_Mod1 (nsAppend ns1 ns2)
    = option_choice_f (nsLookup_Mod1 ns1) (nsLookup_Mod1 ns2)
Proof
  Cases_on `ns1` \\ Cases_on `ns2`
  \\ fs [nsLookup_Mod1_def, nsAppend_def,
    alookup_append_option_choice_f]
QED

Theorem nsLookup_Short_nsLift:
   nsLookup_Short (nsLift mnm ns) = ALOOKUP []
Proof
  Cases_on `ns` \\ fs [nsLift_def, nsLookup_Short_Bind]
QED

Theorem nsLookup_Mod1_nsLift:
   nsLookup_Mod1 (nsLift mnm ns) = ALOOKUP [(mnm, ns)]
Proof
  Cases_on `ns` \\ fs [nsLift_def, nsLookup_Mod1_def]
QED

Theorem nsLookup_pf_nsBind:
   nsLookup_Short (nsBind n v ns)
        = option_choice_f (ALOOKUP [(n, v)]) (nsLookup_Short ns) /\
  nsLookup_Mod1 (nsBind n v ns) = nsLookup_Mod1 ns
Proof
  Cases_on `ns`
  \\ fs [nsLookup_Short_def,nsLookup_Mod1_def, FUN_EQ_THM,
    write_def,nsLookup_def,nsBind_def,option_choice_f_def]
  \\ rpt strip_tac
  \\ fs [] \\ CASE_TAC \\ fs []
QED

(* equalities on these partial functions for the various env operators *)

Theorem nsLookup_write_eqs:
   nsLookup_Short ((write n v env).c) = nsLookup_Short env.c /\
    nsLookup_Mod1 ((write n v env).c) = nsLookup_Mod1 env.c /\
    nsLookup_Mod1 ((write n v env).v) = nsLookup_Mod1 env.v /\
    nsLookup_Short ((write n v env).v) = option_choice_f (ALOOKUP [(n, v)])
        (nsLookup_Short env.v)
Proof
  fs[write_def, nsLookup_pf_nsBind]
QED

Theorem nsLookup_write_cons_eqs:
   nsLookup_Short ((write_cons n v env).v) = nsLookup_Short env.v /\
    nsLookup_Mod1 ((write_cons n v env).v) = nsLookup_Mod1 env.v /\
    nsLookup_Mod1 ((write_cons n v env).c) = nsLookup_Mod1 env.c /\
    nsLookup_Short ((write_cons n v env).c) = option_choice_f (ALOOKUP [(n, v)])
        (nsLookup_Short env.c)
Proof
  fs[write_cons_def, nsLookup_pf_nsBind]
QED

Theorem nsLookup_merge_env_eqs:
   nsLookup_Short ((merge_env env env2).v)
        = option_choice_f (nsLookup_Short env.v) (nsLookup_Short env2.v) /\
    nsLookup_Mod1 ((merge_env env env2).v)
        = option_choice_f (nsLookup_Mod1 env.v) (nsLookup_Mod1 env2.v) /\
    nsLookup_Short ((merge_env env env2).c)
        = option_choice_f (nsLookup_Short env.c) (nsLookup_Short env2.c) /\
    nsLookup_Mod1 ((merge_env env env2).c)
        = option_choice_f (nsLookup_Mod1 env.c) (nsLookup_Mod1 env2.c)
Proof
  fs[merge_env_def, nsLookup_Short_nsAppend, nsLookup_Mod1_nsAppend]
QED

Theorem nsLookup_write_mod_eqs:
   nsLookup_Short ((write_mod mnm env env2).v) = nsLookup_Short env2.v /\
    nsLookup_Mod1 ((write_mod mnm env env2).v)
        = option_choice_f (ALOOKUP [(mnm, env.v)]) (nsLookup_Mod1 env2.v) /\
    nsLookup_Short ((write_mod mnm env env2).c) = nsLookup_Short env2.c /\
    nsLookup_Mod1 ((write_mod mnm env env2).c)
        = option_choice_f (ALOOKUP [(mnm, env.c)]) (nsLookup_Mod1 env2.c)
Proof
  fs[write_mod_def, nsLookup_Short_nsAppend, nsLookup_Mod1_nsAppend,
    nsLookup_Short_nsLift, nsLookup_Mod1_nsLift,
    alookup_empty_option_choice_f]
QED

Theorem nsLookup_empty_eqs:
   nsLookup_Short empty_env.v = ALOOKUP [] /\
    nsLookup_Mod1 empty_env.v = ALOOKUP [] /\
    nsLookup_Short empty_env.c = ALOOKUP [] /\
    nsLookup_Mod1 empty_env.c = ALOOKUP []
Proof
  fs[empty_env_def, nsEmpty_def, nsLookup_Short_Bind, nsLookup_Mod1_def]
QED

(* nonsense theorem instantiated when env's are defined *)

Theorem nsLookup_eq_format:
   !env:v sem_env.
     (nsLookup_Short env.v = nsLookup_Short env.v) /\
     (nsLookup_Short env.c = nsLookup_Short env.c) /\
     (nsLookup_Mod1 env.v = nsLookup_Mod1 env.v) /\
     (nsLookup_Mod1 env.c = nsLookup_Mod1 env.c)
Proof
  rewrite_tac []
QED

(* some shorthands that are allowed to EVAL are below *)

Definition write_rec_def:
  write_rec funs env1 env =
    FOLDR (\f env. write (FST f) (Recclosure env1 funs (FST f)) env) env funs
End

Theorem write_rec_thm:
   write_rec funs env1 env =
    env with v := build_rec_env funs env1 env.v
Proof
  fs [write_rec_def,build_rec_env_def]
  \\ qspec_tac (`Recclosure env1 funs`,`hh`)
  \\ qspec_tac (`env`,`env`)
  \\ Induct_on `funs` \\ fs [FORALL_PROD]
  \\ fs [write_def]
QED

Definition write_conses_def:
  write_conses [] env = env /\
  write_conses ((n,y)::xs) env =
    write_cons n y (write_conses xs env)
End

Definition write_tdefs_def:
  write_tdefs n [] env = env /\
  write_tdefs n ((x,_,condefs)::tds) env =
    write_tdefs (n+1) tds (write_conses (REVERSE (build_constrs n condefs)) env)
End

Theorem write_conses_v[local]:
    !xs env. (write_conses xs env).v = env.v
Proof
  Induct \\ fs [write_conses_def,FORALL_PROD,write_cons_def]
QED

Theorem write_tdefs_lemma[local]:
    !tds env n.
      write_tdefs n tds env =
      merge_env <|v := nsEmpty; c := build_tdefs n tds|> env
Proof
  Induct \\ fs [write_tdefs_def,merge_env_def,build_tdefs_def,FORALL_PROD]
  \\ rw [write_conses_v]
  \\ rewrite_tac [GSYM namespacePropsTheory.nsAppend_assoc]
  \\ AP_TERM_TAC
  \\ Q.SPEC_TAC (`REVERSE (build_constrs n p_2)`,`xs`)
  \\ Induct \\ fs [write_conses_def,FORALL_PROD,write_cons_def]
QED

Theorem write_tdefs_thm:
   write_tdefs n tds empty_env =
    <|v := nsEmpty; c := build_tdefs n tds|>
Proof
  fs [write_tdefs_lemma,empty_env_def,merge_env_def]
QED

Theorem merge_env_write_conses[local]:
    !xs env. merge_env (write_conses xs env1) env2 =
             write_conses xs (merge_env env1 env2)
Proof
  Induct \\ fs [write_conses_def,FORALL_PROD]
  \\ fs [write_cons_def,merge_env_def,sem_env_component_equality]
QED

Theorem merge_env_write_tdefs[local]:
    !tds n env1 env2.
      merge_env (write_tdefs n tds env1) env2 =
      write_tdefs n tds (merge_env env1 env2)
Proof
  Induct \\ fs [write_tdefs_def,FORALL_PROD,merge_env_write_conses]
QED

(* it's not clear if these are still needed, but ml_progComputeLib and
   cfTacticsLib want them to be present. *)

Theorem nsLookup_nsAppend_Short[compute]:
    (nsLookup (nsAppend e1 e2) (Short id) =
    case nsLookup e1 (Short id) of
      NONE =>
        nsLookup e2 (Short id)
    | SOME v => SOME v)
Proof
  every_case_tac>>
  Cases_on`nsLookup e2(Short id)`>>
  fs[namespacePropsTheory.nsLookup_nsAppend_some,
     namespacePropsTheory.nsLookup_nsAppend_none,id_to_mods_def]
QED

Theorem write_simp[compute]:
   (write n v env).c = env.c /\
    nsLookup (write n v env).v (Short q) =
      if n = q then SOME v else nsLookup env.v (Short q)
Proof
  IF_CASES_TAC>>fs[write_def,namespacePropsTheory.nsLookup_nsBind]
QED

Theorem write_cons_simp[compute]:
   (write_cons n v env).v = env.v /\
    nsLookup (write_cons n v env).c (Short q) =
      if n = q then SOME v else nsLookup env.c (Short q)
Proof
  IF_CASES_TAC>>fs[write_cons_def,namespacePropsTheory.nsLookup_nsBind]
QED

Theorem write_mod_simp[compute]:
   (nsLookup (write_mod mn env env2).v (Short q) =
    nsLookup env2.v (Short q)) ∧
   (nsLookup (write_mod mn env env2).c (Short c) =
    nsLookup env2.c (Short c)) ∧
   (nsLookup (write_mod mn env env2).v (Long mn' r) =
    if mn = mn' then nsLookup env.v r
    else nsLookup env2.v (Long mn' r)) ∧
   (nsLookup (write_mod mn env env2).c (Long mn' s) =
    if mn = mn' then nsLookup env.c s
    else nsLookup env2.c (Long mn' s))
Proof
  rw[write_mod_def]
QED

Theorem empty_simp[compute]:
   nsLookup empty_env.v q = NONE /\
   nsLookup empty_env.c q = NONE
Proof
  fs [empty_env_def]
QED
(* the components of nsLookup are 'nicer' partial functions *)

(* --- declarations --- *)

Definition Decls_def:
  Decls env s1 ds env2 s2 <=>
    s1.clock = s2.clock /\
    ?ck1 ck2. evaluate_dec_list (s1 with clock := ck1) env ds =
                                (s2 with clock := ck2, Rval env2)
End

Definition Prog_def:
  Prog env s1 ds env2 s2 <=>
    s1.clock = s2.clock /\
    ?ck1 ck2. evaluate_decs (s1 with clock := ck1) env ds =
                            (s2 with clock := ck2, Rval env2)
End

Theorem Decls_Dtype:
   !env s tds env2 s2 locs.
      Decls env s [Dtype locs tds] env2 s2 <=>
      EVERY check_dup_ctors tds /\
      s2 = s with <| next_type_stamp := (s.next_type_stamp + LENGTH tds) |> /\
      env2 = write_tdefs s.next_type_stamp tds empty_env
Proof
  SIMP_TAC std_ss [Decls_def,evaluate_dec_list_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs [bool_case_eq]
  \\ rveq \\ fs [state_component_equality,write_tdefs_thm]
QED

Theorem Decls_Dexn:
   !env s n l env2 s2 locs.
      Decls env s [Dexn locs n l] env2 s2 <=>
      s2 = s with <| next_exn_stamp := (s.next_exn_stamp + 1) |> /\
      env2 = write_cons n (LENGTH l, ExnStamp s.next_exn_stamp) empty_env
Proof
  SIMP_TAC std_ss [Decls_def,evaluate_dec_list_def,write_cons_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs [bool_case_eq]
  \\ rveq \\ fs [state_component_equality,write_tdefs_thm]
  \\ fs [nsBind_def,nsEmpty_def,nsSing_def,empty_env_def]
QED

Theorem Decls_Dtabbrev:
   !env s x y z env2 s2 locs.
      Decls env s [Dtabbrev locs x y z] env2 s2 <=>
      s2 = s ∧ env2 = empty_env
Proof
  fs [Decls_def,evaluate_dec_list_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs [bool_case_eq]
  \\ rveq \\ fs [state_component_equality,empty_env_def]
QED

Definition eval_rel_def:
  eval_rel s1 env e s2 x <=>
    s1.clock = s2.clock /\
    ?ck1 ck2.
       evaluate (s1 with clock := ck1) env [e] =
                (s2 with clock := ck2,Rval [x])
End

Theorem eval_rel_alt:
   eval_rel s1 env e s2 x <=>
    s2.clock = s1.clock ∧
    ∃ck. evaluate (s1 with clock := ck) env [e] = (s2,Rval [x])
Proof
  reverse eq_tac \\ rw [] \\ fs [eval_rel_def]
  THEN1 (qexists_tac `ck` \\ fs [state_component_equality])
  \\ drule evaluatePropsTheory.evaluate_set_clock \\ fs []
  \\ disch_then (qspec_then `s2.clock` strip_assume_tac)
  \\ rename [`evaluate (s1 with clock := ck) env [e]`]
  \\ qexists_tac `ck` \\ fs [state_component_equality]
QED

Definition eval_list_rel_def:
  eval_list_rel s1 env e s2 x <=>
    s1.clock = s2.clock /\
    ?ck1 ck2.
       evaluate (s1 with clock := ck1) env e =
                (s2 with clock := ck2,Rval x)
End

Definition eval_match_rel_def:
  eval_match_rel s1 env v pats err_v s2 x <=>
    s1.clock = s2.clock /\
    ?ck1 ck2.
       evaluate_match
                (s1 with clock := ck1) env v pats err_v =
                (s2 with clock := ck2,Rval [x])
End

(* Delays the write *)
Theorem Decls_Dlet:
   !env s1 v e s2 env2 locs.
      Decls env s1 [Dlet locs (Pvar v) e] env2 s2 <=>
      ?x. eval_rel s1 env e s2 x /\ (env2 = write v x empty_env)
Proof
  simp [Decls_def,evaluate_dec_list_def,eval_rel_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs [bool_case_eq]
  THEN1
   (FULL_CASE_TAC
    \\ Cases_on `r` \\ fs [pat_bindings_def,ALL_DISTINCT,MEM,
         pmatch_def,combine_dec_result_def] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_sing \\ fs [] \\ rveq
    \\ fs [write_def,empty_env_def] \\ asm_exists_tac \\ fs [])
  \\ fs [pat_bindings_def,ALL_DISTINCT,MEM,
         pmatch_def,combine_dec_result_def]
  \\ qexists_tac `ck1` \\ qexists_tac `ck2`
  \\ fs [write_def,empty_env_def]
QED

Theorem FOLDR_LEMMA[local]:
  ∀xs ys. FOLDR (\(x1,x2,x3) x4. (x1, f x1 x2 x3) :: x4) [] xs ++ ys =
          FOLDR (\(x1,x2,x3) x4. (x1, f x1 x2 x3) :: x4) ys xs
Proof
  Induct \\ FULL_SIMP_TAC (srw_ss()) [FORALL_PROD]
QED

(* Delays the write in build_rec_env *)
Theorem Decls_Dletrec:
   ∀env s1 funs s2 env2 locs.
      Decls env s1 [Dletrec locs funs] env2 s2 <=>
      (s2 = s1) /\
      ALL_DISTINCT (MAP (\(x,y,z). x) funs) /\
      (env2 = write_rec funs env empty_env)
Proof
  simp [Decls_def,evaluate_dec_list_def,bool_case_eq,PULL_EXISTS]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs []
  \\ fs [state_component_equality,write_rec_def]
  \\ fs[write_def,write_rec_thm,empty_env_def,build_rec_env_def]
  \\ rpt (pop_assum kall_tac)
  \\ qspec_tac (`Recclosure env funs`,`xx`)
  \\ qspec_tac (`nsEmpty:env_val`,`nn`)
  \\ Induct_on `funs` \\ fs [FORALL_PROD]
  \\ pop_assum (assume_tac o GSYM) \\ fs []
QED

Theorem Decls_Dmod:
   Decls env1 s1 [Dmod mn ds] env2 s2 <=>
   ?s env.
      Decls env1 s1 ds env s /\ s2 = s /\
      env2 = write_mod mn env empty_env
Proof
  fs [Decls_def,Decls_def,evaluate_dec_list_def,PULL_EXISTS,
      combine_dec_result_def,write_mod_def,empty_env_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs [pair_case_eq,result_case_eq]
  \\ rveq \\ fs [] \\ asm_exists_tac \\ fs []
QED

Theorem Decls_Dlocal:
   Decls env st lds env2 st2
    ==> Decls (merge_env env2 env) st2 ds env3 st3
    ==> Decls env st [Dlocal lds ds] env3 st3
Proof
  fs [Decls_def,evaluate_dec_list_def,extend_dec_env_def,merge_env_def]
  \\ rw [pair_case_eq, result_case_eq]
  \\ imp_res_tac evaluate_dec_list_set_clock
  \\ fs [] \\ metis_tac []
QED

Theorem Decls_Denv:
  ∀env s1 v s2 env2.
    Decls env s1 [Denv v] env2 s2 ⇔
    ∃env1 es.
      declare_env s1.eval_state env = SOME (env1, es) ∧
      s2 = s1 with eval_state := es ∧
      env2 = write v env1 empty_env
Proof
  rw[Decls_def, evaluate_dec_list_def]
  \\ TOP_CASE_TAC
  \\ PairCases_on`x`
  \\ simp[write_def,empty_env_def,state_component_equality]
  \\ rw[nsEmpty_def, nsSing_def, nsBind_def]
  \\ rw[EQ_IMP_THM]
QED

Theorem Decls_NIL:
   !env s n l env2 s2.
      Decls env s [] env2 s2 <=>
      s2 = s ∧ env2 = empty_env
Proof
  fs [Decls_def,evaluate_dec_list_def,state_component_equality,empty_env_def]
  \\ rw [] \\ eq_tac \\ rw []
QED

Theorem Decls_CONS:
   !s1 s3 env1 d ds1 ds2 env3.
      Decls env1 s1 (d::ds2) env3 s3 =
      ?envA envB s2.
         Decls env1 s1 [d] envA s2 /\
         Decls (merge_env envA env1) s2 ds2 envB s3 /\
         env3 = merge_env envB envA
Proof
  rw[Decls_def,PULL_EXISTS,evaluate_dec_list_def]
  \\ reverse (rw[EQ_IMP_THM]) \\ fs []
  THEN1
   (once_rewrite_tac [evaluate_dec_list_cons]
    \\ imp_res_tac evaluate_dec_list_add_to_clock \\ fs []
    \\ first_x_assum (qspec_then `ck1'` assume_tac)
    \\ qexists_tac `ck1+ck1'` \\ fs []
    \\ fs [merge_env_def,extend_dec_env_def,combine_dec_result_def]
    \\ fs [state_component_equality])
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [evaluate_dec_list_cons]
  \\ fs [pair_case_eq,result_case_eq] \\ rw [] \\ fs [PULL_EXISTS]
  \\ gvs [evaluate_dec_list_def]
  \\ Cases_on `r` \\ fs [combine_dec_result_def]
  \\ rveq \\ fs []
  \\ qexists_tac `env1'` \\ fs []
  \\ qexists_tac `a` \\ fs []
  \\ qexists_tac `s1' with clock := s3.clock` \\ fs [merge_env_def]
  \\ qexists_tac `ck1` \\ fs [state_component_equality]
  \\ qexists_tac `s1'.clock` \\ fs [state_component_equality]
  \\ `(s1' with clock := s1'.clock) = s1'` by fs [state_component_equality]
  \\ fs [extend_dec_env_def]
  \\ fs [state_component_equality]
QED

Theorem merge_env_empty_env:
   merge_env env empty_env = env /\
   merge_env empty_env env = env
Proof
  rw [merge_env_def,empty_env_def]
QED

Theorem merge_env_assoc:
   merge_env env1 (merge_env env2 env3) = merge_env (merge_env env1 env2) env3
Proof
  fs [merge_env_def]
QED

Theorem Decls_APPEND:
   !s1 s3 env1 ds1 ds2 env3.
      Decls env1 s1 (ds1 ++ ds2) env3 s3 =
      ?envA envB s2.
         Decls env1 s1 ds1 envA s2 /\
         Decls (merge_env envA env1) s2 ds2 envB s3 /\
         env3 = merge_env envB envA
Proof
  Induct_on `ds1` \\ fs [APPEND,Decls_NIL,merge_env_empty_env]
  \\ once_rewrite_tac [Decls_CONS]
  \\ fs [PULL_EXISTS,merge_env_assoc] \\ metis_tac []
QED

Theorem Decls_SNOC:
   !s1 s3 env1 ds1 d env3.
      Decls env1 s1 (SNOC d ds1) env3 s3 =
      ?envA envB s2.
         Decls env1 s1 ds1 envA s2 /\
         Decls (merge_env envA env1) s2 [d] envB s3 /\
         env3 = merge_env envB envA
Proof
  METIS_TAC [SNOC_APPEND, Decls_APPEND]
QED

Theorem Decls_set_eval_state:
  Decls env1 s1 ds env2 s2 ∧ s1.eval_state = NONE ⇒
  ∀es.
    Decls env1 (s1 with eval_state := es) ds env2
               (s2 with eval_state := es)
Proof
  rw [Decls_def]
  \\ drule_then (qspec_then ‘es’ assume_tac) eval_dec_list_no_eval_simulation
  \\ gvs []
  \\ pop_assum $ irule_at Any
QED

(* The translator and CF tools use the following definition of ML_code
   to build (and verify) an ML program within the logic. The goal is to
   prove 'Decls' of the completed list of declarations. The program is
   constructed one statement at a time, with facts about the resulting
   environment built over time. There is a list of currently open blocks
   (e.g. struct and local constructs) so that the contents of modules and
   local objects can also be built up one statement at a time.
*)

Definition ML_code_env_def:
  (ML_code_env env [] = env) ∧
  (ML_code_env env ((comm, st, decls, res_env) :: bls)
        = merge_env res_env (ML_code_env env bls))
End

Definition ML_code_def:
  (ML_code env [] res_st <=> T) ∧
  (ML_code env (((comment : mlstring # mlstring), st, decls, res_env) :: bls) res_st <=>
     ML_code env bls st ∧
     Decls (ML_code_env env bls) st decls res_env res_st)
End

(* retreive the Decls from a toplevel ML_code *)
Theorem ML_code_Decls:
  ML_code env1 [(comm, st1, prog, env2)] st2 ==>
    Decls env1 st1 prog env2 st2
Proof
  fs [ML_code_def, ML_code_env_def]
QED

(* an empty program *)
local open primSemEnvTheory in

local
  val init_env_tm =
    ``SND (THE (prim_sem_env (ARB:unit ffi_state)))``
    |> (SIMP_CONV std_ss [primSemEnvTheory.prim_sem_env_eq] THENC EVAL)
    |> concl |> rand
  val init_state_tm =
    ``FST(THE (prim_sem_env (ffi:'ffi ffi_state)))``
    |> (SIMP_CONV std_ss [primSemEnvTheory.prim_sem_env_eq] THENC EVAL)
    |> concl |> rand
in
  (* init_env_def should not be unpacked by EVAL. Queries will be handled
     by the nsLookup_conv apparatus, which will use the pfun_eqs thm below. *)
Definition init_env_def[nocompute]:
  init_env = ^init_env_tm
End

Definition init_state_def:
  init_state ffi = ^init_state_tm
End
end

Theorem init_state_env_thm:
   THE (prim_sem_env ffi) = (init_state ffi,init_env)
Proof
  rewrite_tac[prim_sem_env_eq,THE_DEF,init_state_def,init_env_def]
QED

Theorem nsLookup_init_env_pfun_eqs =
  [``nsLookup_Short init_env.c``, ``nsLookup_Short init_env.v``,
    ``nsLookup_Mod1 init_env.c``, ``nsLookup_Mod1 init_env.v``]
  |> map (SIMP_CONV bool_ss
        [init_env_def, nsLookup_Short_Bind, nsLookup_Mod1_def,
            namespace_case_def, sem_env_accfupds, K_DEF])
  |> LIST_CONJ;

end

Theorem ML_code_NIL:
   ML_code init_env [((«Toplevel», «»), init_state ffi, [], empty_env)]
    (init_state ffi)
Proof
  fs [ML_code_def,Decls_NIL]
QED

(* opening and closing of modules *)

Theorem ML_code_new_block:
   !comm2. ML_code inp_env ((comm, st, decls, env) :: bls) st2 ==>
    let env2 = ML_code_env inp_env ((comm, st, decls, env) :: bls) in
    ML_code inp_env ((comm2, st2, [], empty_env)
        :: (comm, st, decls, env) :: bls) st2
Proof
  fs [ML_code_def] \\ rw [Decls_NIL] \\ EVAL_TAC
QED

Theorem ML_code_close_module:
   ML_code inp_env (((«Module», mn), m_i_st, m_decls, m_env)
        :: (comm, st, decls, env) :: bls) st2
    ==> let env2 = write_mod mn m_env env
        in ML_code inp_env ((comm, st, SNOC (Dmod mn m_decls) decls,
            env2) :: bls) st2
Proof
  rw [ML_code_def, ML_code_env_def]
  \\ fs [SNOC_APPEND,Decls_APPEND]
  \\ asm_exists_tac \\ fs [Decls_Dmod,PULL_EXISTS]
  \\ asm_exists_tac
  \\ fs [write_mod_def,merge_env_def,empty_env_def]
QED

Theorem ML_code_close_local:
   ML_code inp_env (((«Local», ln2), l2_i_st, l2_decls, l2_env)
        :: ((«Local», ln1), l1_i_st, l1_decls, l1_env)
        :: (comm, st, decls, env) :: bls) st2
    ==> let env2 = merge_env l2_env env
        in ML_code inp_env ((comm, st, SNOC (Dlocal l1_decls l2_decls) decls,
            env2) :: bls) st2
Proof
  rw [ML_code_def, ML_code_env_def]
  \\ fs [SNOC_APPEND,Decls_APPEND] \\ metis_tac [Decls_Dlocal]
QED

(* appending a Dtype *)

Theorem ML_code_Dtype:
   !tds locs. ML_code inp_env ((comm, s1, prog, env2) :: bls) s2 ==>
     EVERY check_dup_ctors tds ==>
     let nts = s2.next_type_stamp in
     let s3 = (s2 with next_type_stamp := nts + LENGTH tds) in
     let env3 = write_tdefs nts tds env2 in
     ML_code inp_env ((comm, s1, SNOC (Dtype locs tds) prog, env3) :: bls) s3
Proof
  fs [ML_code_def,SNOC_APPEND,Decls_APPEND,Decls_Dtype,merge_env_empty_env]
  \\ rw [] \\ rpt (asm_exists_tac \\ fs [])
  \\ fs [merge_env_write_tdefs] \\ AP_TERM_TAC
  \\ fs [merge_env_def,empty_env_def,sem_env_component_equality]
QED

(* appending a Dexn *)

Theorem ML_code_Dexn:
   !n l locs. ML_code inp_env ((comm, s1, prog, env2) :: bls) s2 ==>
     let nes = s2.next_exn_stamp in
     let s3 = s2 with next_exn_stamp := nes + 1 in
     let env3 = write_cons n (LENGTH l,ExnStamp nes) env2 in
     ML_code inp_env ((comm, s1, SNOC (Dexn locs n l) prog, env3) :: bls) s3
Proof
  fs [ML_code_def,SNOC_APPEND,Decls_APPEND,Decls_Dexn,merge_env_empty_env]
  \\ rw [] \\ rpt (asm_exists_tac \\ fs [])
  \\ fs [write_cons_def,merge_env_def,empty_env_def,sem_env_component_equality]
QED

(* appending a Dtabbrev *)

Theorem ML_code_Dtabbrev:
   !x y z locs. ML_code inp_env ((comm, s1, prog, env2) :: bls) s2 ==>
     ML_code inp_env ((comm, s1, SNOC (Dtabbrev locs x y z) prog, env2) :: bls)
       s2
Proof
  fs [ML_code_def,SNOC_APPEND,Decls_APPEND,Decls_Dtabbrev,merge_env_empty_env]
QED

(* appending a Letrec *)

Theorem build_rec_env_APPEND[local]:
  nsAppend (build_rec_env funs cl_env nsEmpty) add_to_env =
   build_rec_env funs cl_env add_to_env
Proof
  fs [build_rec_env_def] \\ qspec_tac (`Recclosure cl_env funs`,`xxx`)
  \\ qspec_tac (`add_to_env`,`xs`)
  \\ Induct_on `funs` \\ fs [FORALL_PROD]
QED

Theorem ML_code_Dletrec:
   !fns locs. ML_code env0 ((comm, s1, prog, env2) :: bls) s2 ==>
      ALL_DISTINCT (MAP (λ(x,y,z). x) fns) ==>
      let code_env = ML_code_env env0 ((comm, s1, prog, env2) :: bls) in
      let env3 = write_rec fns code_env env2 in
      ML_code env0 ((comm, s1, SNOC (Dletrec locs fns) prog, env3) :: bls) s2
Proof
  fs [ML_code_def,SNOC_APPEND,Decls_APPEND,Decls_Dletrec,ML_code_env_def]
  \\ rw [] \\ asm_exists_tac
  \\ fs [merge_env_def,write_rec_thm,empty_env_def,sem_env_component_equality]
  \\ fs [build_rec_env_APPEND]
QED

(* appending a Let *)

Theorem ML_code_Dlet_var:
  ∀cenv e s3 x n locs. ML_code env0 ((comm, s1, prog, env1) :: bls) s2 ==>
    eval_rel s2 cenv e s3 x ==>
    cenv = ML_code_env env0 ((comm, s1, prog, env1) :: bls) ==>
    let env2 = write n x env1 in let s3_abbrev = s3 in
    ML_code env0 ((comm, s1, SNOC (Dlet locs (Pvar n) e) prog, env2)
        :: bls) s3_abbrev
Proof
  fs [ML_code_def,ML_code_env_def,SNOC_APPEND,Decls_APPEND,Decls_Dlet]
  \\ rw [] \\ asm_exists_tac \\ fs [PULL_EXISTS]
  \\ fs [write_def,merge_env_def,empty_env_def,sem_env_component_equality]
QED

Theorem ML_code_Dlet_var_lit:
  ∀loc name l. ML_code env0 ((comm, s1, prog, env1)::bls) s2 ⇒
    let env2 = write name (Litv l) env1 in let s3_abbrev = s2 in
      ML_code env0 ((comm,s1,SNOC (Dlet loc (Pvar name) (Lit l)) prog,env2)::bls) s3_abbrev
Proof
  rpt strip_tac
  \\ irule ML_code_Dlet_var \\ fs []
  \\ pop_assum $ irule_at Any
  \\ fs [eval_rel_def,evaluateTheory.evaluate_def]
  \\ fs [semanticPrimitivesTheory.state_component_equality]
QED

Theorem ML_code_Dlet_Fun:
  ∀n v e locs. ML_code env0 ((comm, s1, prog, env1) :: bls) s2 ==>
    let code_env = ML_code_env env0 ((comm, s1, prog, env1) :: bls) in
    let v_abbrev = Closure code_env v e in
    let env2 = write n v_abbrev env1 in
    ML_code env0 ((comm, s1, SNOC (Dlet locs (Pvar n) (Fun v e)) prog,
        env2) :: bls) s2
Proof
  rw [] \\ imp_res_tac ML_code_Dlet_var
  \\ fs [evaluate_def,state_component_equality,eval_rel_def]
QED

Theorem ML_code_Dlet_Var_Var:
  ∀n vname locs. ML_code env0 ((comm, s1, prog, env1) :: bls) s2 ==>
    let cenv = ML_code_env env0 ((comm, s1, prog, env1) :: bls) in
    ∀x. nsLookup cenv.v vname = SOME x ==>
    let env2 = write n x env1 in
    ML_code env0 ((comm, s1, SNOC (Dlet locs (Pvar n) (Var vname)) prog, env2)
        :: bls) s2
Proof
  rw []
  \\ irule (SIMP_RULE std_ss [LET_THM] ML_code_Dlet_var) \\ fs []
  \\ first_x_assum $ irule_at $ Pos hd
  \\ fs [eval_rel_def,evaluate_def,state_component_equality]
QED

Theorem ML_code_Dlet_Var_Ref_Var:
  ∀n vname locs. ML_code env0 ((comm, s1, prog, env1) :: bls) s2 ==>
    let cenv = ML_code_env env0 ((comm, s1, prog, env1) :: bls) in
    ∀x. nsLookup cenv.v vname = SOME x ==>
    let len = LENGTH s2.refs in
    let loc = Loc T len in
    let env2 = write n loc env1 in
    let s2_abbrev = s2 with refs := s2.refs ++ [Refv x] in
    ML_code env0 ((comm, s1, SNOC (Dlet locs (Pvar n) (App Opref [Var vname])) prog, env2)
        :: bls) s2_abbrev
Proof
  rw []
  \\ irule (SIMP_RULE std_ss [LET_THM] ML_code_Dlet_var) \\ fs []
  \\ first_x_assum $ irule_at $ Pos hd
  \\ fs [eval_rel_def,evaluate_def,state_component_equality,AllCaseEqs(),
         do_app_def,store_alloc_def, getOpClass_def]
QED

(* appending an environment *)

Definition declare_env_rel_def:
  declare_env_rel s2 env1 s3 envv ⇔
  ∃es.
    declare_env s2.eval_state env1 = SOME (envv, es) ∧
    s3 = s2 with eval_state := es
End

Theorem ML_code_Denv:
  ∀n cenv s3 envv.
    ML_code env0 ((comm,s1,prog,env1)::bls) s2 ⇒
    declare_env_rel s2 cenv s3 envv ⇒
    cenv = ML_code_env env0 ((comm,s1,prog,env1)::bls) ⇒
    let
      env2 = write n envv env1;
      s3_abbrev = s3
    in
    ML_code env0 ((comm,s1,SNOC (Denv n) prog,env2)::bls) s3_abbrev
Proof
  rw[ML_code_def, SNOC_APPEND, Decls_APPEND, Decls_Denv,
     declare_env_rel_def, ML_code_env_def]
  \\ first_assum $ irule_at Any
  \\ first_assum $ irule_at Any
  \\ rw[write_def, merge_env_def, empty_env_def,
        sem_env_component_equality]
QED

(* setting the eval_state *)

Theorem ML_code_set_eval_state: (* only supported at the top-level for simplicity *)
  ML_code env0 [(comm,s1,prog,env1)] s2 ⇒
  s1.eval_state = NONE ⇒
  ∀es. ML_code env0 [(comm,s1 with eval_state := SOME es,prog,env1)]
                          (s2 with eval_state := SOME es)
Proof
  rw [ML_code_def]
  \\ drule_all Decls_set_eval_state
  \\ fs []
QED

(* lookup function definitions *)

Definition lookup_var_def:
  lookup_var name (env:v sem_env) = nsLookup env.v (Short name)
End

Definition lookup_cons_def:
  lookup_cons name (env:v sem_env) = nsLookup env.c name
End

(* the old lookup formulation worked via nsLookup/mod_defined,
   and mod_defined is still used in various characteristic scripts
   so we supply an eval theorem that maps to the new approach. *)

Definition mod_defined_def[nocompute]:
  mod_defined env n =
    ∃p1 p2 e3.
      p1 ≠ [] ∧ id_to_mods n = p1 ++ p2 ∧
      nsLookupMod env p1 = SOME e3
End

Theorem mod_defined_nsLookup_Mod1[compute]:
   mod_defined env id = (case id of Short _ => F
        | Long mn _ => (case nsLookup_Mod1 env mn of NONE => F | _ => T))
Proof
  PURE_CASE_TAC \\ fs [id_to_mods_def, mod_defined_def]
    \\ Cases_on `env`
    \\ fs [Once EXISTS_LIST, nsLookupMod_def, nsLookup_Mod1_def]
    \\ PURE_CASE_TAC \\ fs [Once EXISTS_LIST, nsLookupMod_def]
QED

(* theorems about old lookup functions *)
(* FIXME: everything below this line is unlikely to be needed. *)

Theorem nsLookupMod_nsBind[local]:
  p ≠ [] ⇒
  nsLookupMod (nsBind k v env) p = nsLookupMod env p
Proof
  Cases_on`env`>>fs[nsBind_def]>> Induct_on`p`>>
  fs[nsLookupMod_def]
QED

Theorem nsLookup_write:
   (nsLookup (write n v env).v (Short name) =
       if n = name then SOME v else nsLookup env.v (Short name)) /\
   (nsLookup (write n v env).v (Long mn lname)  =
       nsLookup env.v (Long mn lname)) /\
   (nsLookup (write n v env).c a = nsLookup env.c a) /\
   (mod_defined (write n v env).v x = mod_defined env.v x) /\
   (mod_defined (write n v env).c x = mod_defined env.c x)
Proof
  fs [write_def] \\ rw []
  \\ metis_tac[nsLookupMod_nsBind,mod_defined_def]
QED

Theorem nsLookup_write_cons:
   (nsLookup (write_cons n v env).v a = nsLookup env.v a) /\
   (nsLookup (write_cons n d env).c (Short name) =
     if name = n then SOME d else nsLookup env.c (Short name)) /\
   (mod_defined (write_cons n d env).v x = mod_defined env.v x) /\
   (mod_defined (write_cons n d env).c x = mod_defined env.c x) /\
   (nsLookup (write_cons n d env).c (Long mn lname) =
    nsLookup env.c (Long mn lname))
Proof
  fs [write_cons_def] \\ rw [] \\
  metis_tac[nsLookupMod_nsBind,mod_defined_def]
QED

Theorem nsLookup_empty:
   (nsLookup empty_env.v a = NONE) /\
   (nsLookup empty_env.c b = NONE) /\
   (mod_defined empty_env.v x = F) /\
   (mod_defined empty_env.c x = F)
Proof
  rw[empty_env_def, nsLookup_def, mod_defined_def,
    nsLookupMod_def] \\ Cases_on`p1` \\ fs[]
QED

val nsLookupMod_nsAppend = Q.prove(`
  nsLookupMod (nsAppend env1 env2) p =
  if p = [] then SOME (nsAppend env1 env2)
  else
    case nsLookupMod env1 p of
      SOME v => SOME v
    | NONE =>
      if (∃p1 p2 e3. p1 ≠ [] ∧ p = p1 ++ p2 ∧ nsLookupMod env1 p1 = SOME e3) then NONE
      else nsLookupMod env2 p`,
  IF_CASES_TAC>-
    fs[nsLookupMod_def]>>
  BasicProvers.TOP_CASE_TAC>>
  rw[]>>
  TRY(Cases_on`nsLookupMod env2 p`)>>
  fs[namespacePropsTheory.nsLookupMod_nsAppend_none,namespacePropsTheory.nsLookupMod_nsAppend_some]>>
  metis_tac[option_CLAUSES]) |> GEN_ALL;

Theorem nsLookup_write_mod:
   (nsLookup (write_mod mn env1 env2).v (Short n) =
    nsLookup env2.v (Short n)) /\
   (nsLookup (write_mod mn env1 env2).c (Short n) =
    nsLookup env2.c (Short n)) /\
   (mod_defined (write_mod mn env1 env2).v (Long mn' r) =
     ((mn = mn') \/ mod_defined env2.v (Long mn' r))) /\
   (mod_defined (write_mod mn env1 env2).c (Long mn' r) =
     if mn = mn' then T
     else mod_defined env2.c (Long mn' r)) /\
   (nsLookup (write_mod mn env1 env2).v (Long mn1 ln) =
    if mn = mn1 then nsLookup env1.v ln else
      nsLookup env2.v (Long mn1 ln)) /\
   (nsLookup (write_mod mn env1 env2).c (Long mn1 ln) =
    if mn = mn1 then nsLookup env1.c ln else
      nsLookup env2.c (Long mn1 ln))
Proof
  fs [write_mod_def,mod_defined_def] \\
  EVAL_TAC \\
  fs[GSYM nsLift_def,id_to_mods_def,nsLookupMod_nsAppend] \\
  simp[] >> CONJ_TAC>>
  (eq_tac
  >-
    (strip_tac>>
    Cases_on`p1`>>fs[]>>
    fs[namespacePropsTheory.nsLookupMod_nsLift]>>
    Cases_on`mn=h`>>fs[]>>
    qexists_tac`h::t`>>fs[])
  >>
  Cases_on`mn=mn'`>>fs[]
  >-
    (qexists_tac`[mn']`>>fs[namespacePropsTheory.nsLookupMod_nsLift,nsLookupMod_def])
  >>
    strip_tac>>
    asm_exists_tac>>fs[namespacePropsTheory.nsLookupMod_nsLift,nsLookupMod_def]>>
    Cases_on`p1`>>fs[]>> rw[]>>
    Cases_on`p1'`>>fs[]>>
    metis_tac[])
QED

Theorem nsLookup_merge_env:
   (nsLookup (merge_env e1 e2).v (Short n) =
      case nsLookup e1.v (Short n) of
      | NONE => nsLookup e2.v (Short n)
      | SOME x => SOME x) /\
   (nsLookup (merge_env e1 e2).c (Short n) =
      case nsLookup e1.c (Short n) of
      | NONE => nsLookup e2.c (Short n)
      | SOME x => SOME x) /\
   (nsLookup (merge_env e1 e2).v (Long mn ln) =
      case nsLookup e1.v (Long mn ln) of
      | NONE => if mod_defined e1.v (Long mn ln) then NONE
                else nsLookup e2.v (Long mn ln)
      | SOME x => SOME x) /\
   (nsLookup (merge_env e1 e2).c (Long mn ln) =
      case nsLookup e1.c (Long mn ln) of
      | NONE => if mod_defined e1.c (Long mn ln) then NONE
                else nsLookup e2.c (Long mn ln)
      | SOME x => SOME x) ∧
   (mod_defined (merge_env e1 e2).v x =
   (mod_defined e1.v x ∨ mod_defined e2.v x)) /\
   (mod_defined (merge_env e1 e2).c x =
   (mod_defined e1.c x ∨ mod_defined e2.c x))
Proof
  fs [merge_env_def,mod_defined_def] \\ rw[] \\ every_case_tac
  \\ fs[namespacePropsTheory.nsLookup_nsAppend_some]
  THEN1 (Cases_on `nsLookup e2.v (Short n)`
         \\ fs [namespacePropsTheory.nsLookup_nsAppend_none,
                namespacePropsTheory.nsLookup_nsAppend_some]
         \\ rw [] \\ fs [namespaceTheory.id_to_mods_def])
  THEN1 (Cases_on `nsLookup e2.c (Short n)`
         \\ fs [namespacePropsTheory.nsLookup_nsAppend_none,
                namespacePropsTheory.nsLookup_nsAppend_some]
         \\ rw [] \\ fs [namespaceTheory.id_to_mods_def])
  THEN1 (Cases_on `nsLookup e2.v (Long mn ln)`
         \\ fs [namespacePropsTheory.nsLookup_nsAppend_none,
                namespacePropsTheory.nsLookup_nsAppend_some]
         \\ metis_tac [mod_defined_def])
  THEN1 (Cases_on `nsLookup e2.v (Long mn ln)`
         \\ fs [namespacePropsTheory.nsLookup_nsAppend_none,
                namespacePropsTheory.nsLookup_nsAppend_some]
         \\ fs [mod_defined_def] \\ rw []
         \\ CCONTR_TAC \\ Cases_on `nsLookupMod e1.v p1` \\ fs []
         \\ metis_tac [])
  THEN1 (Cases_on `nsLookup e2.c (Long mn ln)`
         \\ fs [namespacePropsTheory.nsLookup_nsAppend_none,
                namespacePropsTheory.nsLookup_nsAppend_some]
         \\ metis_tac [mod_defined_def])
  THEN1 (Cases_on `nsLookup e2.c (Long mn ln)`
         \\ fs [namespacePropsTheory.nsLookup_nsAppend_none,
                namespacePropsTheory.nsLookup_nsAppend_some]
         \\ fs [mod_defined_def] \\ rw []
         \\ CCONTR_TAC \\ Cases_on `nsLookupMod e1.c p1` \\ fs []
         \\ metis_tac [])
  THEN1
    (EVAL_TAC>>fs[nsLookupMod_nsAppend]>>eq_tac>>rw[]>>rfs[]
    >-
      (every_case_tac>>
      metis_tac[])
    >-
      (asm_exists_tac>>fs[])
    >>
      Cases_on`mod_defined e1.v x`>>fs[mod_defined_def]
      >-
        (rveq>>asm_exists_tac>>qexists_tac`p2'`>>fs[])
      >>
      asm_exists_tac>>fs[]>>
      first_assum(qspecl_then[`p1`,`p2`] assume_tac)>>rfs[]>>
      Cases_on`nsLookupMod e1.v p1`>>fs[]>>
      rw[]>>
      rename[`nsLookupMod _ xx`,`p1 ++ p2`,`xx ++ p3`] >>
      first_x_assum(qspecl_then[`xx`,`p3++p2`]mp_tac) >>
      fs[])
  THEN1
    (EVAL_TAC>>fs[nsLookupMod_nsAppend]>>eq_tac>>rw[]>>rfs[]
    >-
      (every_case_tac>>
      metis_tac[])
    >-
      (asm_exists_tac>>fs[])
    >>
      Cases_on`mod_defined e1.c x`>>fs[mod_defined_def]
      >-
        (rveq>>asm_exists_tac>>qexists_tac`p2'`>>fs[])
      >>
      asm_exists_tac>>fs[]>>
      first_assum(qspecl_then[`p1`,`p2`] assume_tac)>>rfs[]>>
      Cases_on`nsLookupMod e1.c p1`>>fs[]>>
      rw[]>>
      rename[`nsLookupMod _ xx`,`p1 ++ p2`,`xx ++ p3`] >>
      first_x_assum(qspecl_then[`xx`,`p3++p2`]mp_tac) >>
      fs[])
QED

Theorem nsLookup_nsBind_compute[compute]:
   (nsLookup (nsBind n v e) (Short n1) =
    if n = n1 then SOME v else nsLookup e (Short n1)) /\
   (nsLookup (nsBind n v e) (Long l1 l2) = nsLookup e (Long l1 l2))
Proof
  rw [namespacePropsTheory.nsLookup_nsBind]
QED

Theorem nsLookup_nsAppend[compute] =
  nsLookup_merge_env
  |> SIMP_RULE (srw_ss()) [merge_env_def]
  |> Q.INST [`e1`|->`<|c:=e1c;v:=e1v|>`,`e2`|->`<|c:=e2c;v:=e2v|>`]
  |> SIMP_RULE (srw_ss()) []

(* Base case for mod_defined (?) *)
Theorem mod_defined_base[compute]:
   mod_defined (Bind _ []) _ = F
Proof
  rw[mod_defined_def]>>Cases_on`p1`>>EVAL_TAC
QED


(* --- the rest of this file might be unused junk --- *)

(* misc theorems about lookup functions *)

(* No idea why this is sparated out *)
Theorem lookup_var_write:
   (lookup_var v (write w x env) = if v = w then SOME x else lookup_var v env) /\
    (nsLookup (write w x env).v (Short v)  =
       if v = w then SOME x else nsLookup env.v (Short v) ) /\
   (nsLookup (write w x env).v (Long mn lname)  =
       nsLookup env.v (Long mn lname)) ∧
    (lookup_cons name (write w x env) = lookup_cons name env)
Proof
  fs [lookup_var_def,write_def,lookup_cons_def] \\ rw []
QED

Theorem lookup_var_write_mod:
   (lookup_var v (write_mod mn e1 env) = lookup_var v env) /\
   (lookup_cons (Long mn1 (Short name)) (write_mod mn2 e1 env) =
    if mn1 = mn2 then
      lookup_cons (Short name) e1
    else
      lookup_cons (Long mn1 (Short name)) env) /\
   (lookup_cons (Short name) (write_mod mn2 e1 env) =
    lookup_cons (Short name) env)
Proof
  fs [lookup_var_def,write_mod_def, lookup_cons_def] \\ rw []
QED

Theorem lookup_var_write_cons:
   (lookup_var v (write_cons n d env) = lookup_var v env) /\
   (lookup_cons (Short name) (write_cons n d env) =
     if name = n then SOME d else lookup_cons (Short name) env) /\
   (lookup_cons (Long l full_name) (write_cons n d env) =
    lookup_cons (Long l full_name) env) /\
   (nsLookup (write_cons n d env).v x = nsLookup env.v x)
Proof
  fs [lookup_var_def,write_cons_def,lookup_cons_def] \\ rw []
QED

Theorem lookup_var_empty_env:
   (lookup_var v empty_env = NONE) /\
    (nsLookup empty_env.v (Short k) = NONE) /\
    (nsLookup empty_env.v (Long mn m) = NONE) /\
    (lookup_cons name empty_env = NONE)
Proof
  fs[lookup_var_def,empty_env_def,lookup_cons_def]
QED

(*
Theorem lookup_var_merge_env:
   (lookup_var v1 (merge_env e1 e2) =
       case lookup_var v1 e1 of
       | NONE => lookup_var v1 e2
       | res => res) /\
    (lookup_cons name (merge_env e1 e2) =
       case lookup_cons name e1 of
       | NONE => lookup_cons name e2
       | res => res)
Proof
  fs [lookup_var_def,lookup_cons_def,merge_env_def] \\ rw[] \\ every_case_tac \\
  fs[namespacePropsTheory.nsLookup_nsAppend_some]
  >-
    (Cases_on`nsLookup e2.v (Short v1)`>>
    fs[namespacePropsTheory.nsLookup_nsAppend_none,
       namespacePropsTheory.nsLookup_nsAppend_some,namespaceTheory.id_to_mods_def])
  \\ ... (* TODO *)
QED);
*)

Definition prog_syntax_ok_def:
  prog_syntax_ok prog = IS_SOME (check_cons_dec_list init_env.c prog)
End

Theorem prog_syntax_ok_isPREFIX:
  ∀p1 p2. prog_syntax_ok p1 ∧ isPREFIX p2 p1 ⇒ prog_syntax_ok p2
Proof
  rw [prog_syntax_ok_def,IS_SOME_EXISTS]
  \\ drule_then irule check_cons_dec_list_isPREFIX \\ fs []
QED

Theorem Decls_IMP_Prog:
  Decls init_env s1 ds env2 s2 ⇒
  prog_syntax_ok ds ⇒
  Prog init_env s1 ds env2 s2
Proof
  rw []
  \\ gvs [Decls_def,Prog_def,evaluate_dec_list_eq_evaluate_decs,prog_syntax_ok_def]
  \\ last_x_assum $ irule_at Any
QED

Theorem prog_syntax_ok_semantics:
  prog_syntax_ok prog ⇒
  semantics_dec_list st init_env prog = semantics_prog st init_env prog
Proof
  simp [FUN_EQ_THM] \\ strip_tac \\ Cases
  \\ gvs [semanticsTheory.semantics_prog_def, semantics_dec_list_def]
  \\ gvs [prog_syntax_ok_def, evaluate_dec_list_eq_evaluate_decs,
          semanticsTheory.evaluate_prog_with_clock_def,
          evaluate_decTheory.evaluate_dec_list_with_clock_def]
QED
