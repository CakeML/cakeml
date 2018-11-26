(*
  Definitions and theorems supporting ml_progLib, which constructs a
  CakeML program and its semantic environment.
*)

open preamble
open astTheory libTheory semanticPrimitivesTheory
     semanticPrimitivesPropsTheory evaluatePropsTheory;
open mlstringTheory integerTheory;
open terminationTheory;
open namespaceTheory;
open alist_treeTheory;

val _ = new_theory "ml_prog";

(* --- env operators --- *)

(* Functions write, write_cons, write_mod, empty_env, merge_env should
   never be expanded by EVAL and are therefore defined using
   zDefine. These should never be exanded by EVAL because that would
   cause very slow appends. *)

val write_def = zDefine `
  write name v (env:v sem_env) = env with v := nsBind name v env.v`;

val write_cons_def = zDefine `
  write_cons n d (env:v sem_env) =
    (env with c := nsAppend (nsSing n d) env.c)`

val empty_env_def = zDefine `
  (empty_env:v sem_env) = <| v := nsEmpty ; c:= nsEmpty|>`;

val write_mod_def = zDefine `
  write_mod mn (env:v sem_env) env2 =
    env2 with <|
      c := nsAppend (nsLift mn env.c) env2.c
      ; v := nsAppend (nsLift mn env.v) env2.v |>`

val merge_env_def = zDefine `
  merge_env (env2:v sem_env) env1 =
    <| v := nsAppend env2.v env1.v
     ; c := nsAppend env2.c env1.c|>`

(* the components of nsLookup are 'nicer' partial functions *)

val nsLookup_Short_def = zDefine `
  nsLookup_Short ns nm = nsLookup ns (Short nm)`;

val nsLookup_Mod1_def = zDefine `
  nsLookup_Mod1 ns = (case ns of Bind _ ms => ALOOKUP ms)`;

val nsLookup_eq = Q.store_thm("nsLookup_eq",
  `nsLookup ns (Short nm) = nsLookup_Short ns nm /\
    nsLookup ns (Long mnm id) = (case nsLookup_Mod1 ns mnm of
      NONE => NONE | SOME ns2 => nsLookup ns2 id)`,
  fs [nsLookup_Short_def]
  \\ Cases_on `ns`
  \\ fs[nsLookup_Mod1_def, nsLookup_def]);

(* base facts about the partial functions *)

val option_choice_f_apply = Q.store_thm("option_choice_f_apply",
  `option_choice_f f g x = OPTION_CHOICE (f x) (g x)`,
  fs [option_choice_f_def]);

val nsLookup_Short_Bind = Q.store_thm("nsLookup_Short_Bind",
  `nsLookup_Short (Bind ss ms) = ALOOKUP ss`,
  fs [nsLookup_Short_def, nsLookup_def, FUN_EQ_THM]);

val nsLookup_Short_nsAppend = Q.store_thm("nsLookup_Short_nsAppend",
  `nsLookup_Short (nsAppend ns1 ns2)
    = option_choice_f (nsLookup_Short ns1) (nsLookup_Short ns2)`,
  Cases_on `ns1` \\ Cases_on `ns2`
  \\ fs [nsLookup_Short_Bind, nsAppend_def,
    alookup_append_option_choice_f]);

val nsLookup_Mod1_Bind = Q.store_thm("nsLookup_Mod1_Bind",
  `nsLookup_Mod1 (Bind ss ms) nm = ALOOKUP ms nm`,
  fs [nsLookup_Mod1_def]);

val nsLookup_Mod1_nsAppend = Q.store_thm("nsLookup_Mod1_nsAppend",
  `nsLookup_Mod1 (nsAppend ns1 ns2)
    = option_choice_f (nsLookup_Mod1 ns1) (nsLookup_Mod1 ns2)`,
  Cases_on `ns1` \\ Cases_on `ns2`
  \\ fs [nsLookup_Mod1_def, nsAppend_def,
    alookup_append_option_choice_f]);

val nsLookup_Short_nsLift = Q.store_thm("nsLookup_Short_nsLift",
  `nsLookup_Short (nsLift mnm ns) = ALOOKUP []`,
  Cases_on `ns` \\ fs [nsLift_def, nsLookup_Short_Bind]);

val nsLookup_Mod1_nsLift = Q.store_thm("nsLookup_Mod1_nsLift",
  `nsLookup_Mod1 (nsLift mnm ns) = ALOOKUP [(mnm, ns)]`,
  Cases_on `ns` \\ fs [nsLift_def, nsLookup_Mod1_def]);

val nsLookup_pf_nsBind = Q.store_thm("nsLookup_pf_nsBind",
  `nsLookup_Short (nsBind n v ns)
        = option_choice_f (ALOOKUP [(n, v)]) (nsLookup_Short ns) /\
  nsLookup_Mod1 (nsBind n v ns) = nsLookup_Mod1 ns`,
  Cases_on `ns`
  \\ fs [nsLookup_Short_def,nsLookup_Mod1_def, FUN_EQ_THM,
    write_def,nsLookup_def,nsBind_def,option_choice_f_def]
  \\ rpt strip_tac
  \\ fs [] \\ CASE_TAC \\ fs []);

(* equalities on these partial functions for the various env operators *)

val nsLookup_write_eqs = Q.store_thm("nsLookup_write_eqs",
  `nsLookup_Short ((write n v env).c) = nsLookup_Short env.c /\
    nsLookup_Mod1 ((write n v env).c) = nsLookup_Mod1 env.c /\
    nsLookup_Mod1 ((write n v env).v) = nsLookup_Mod1 env.v /\
    nsLookup_Short ((write n v env).v) = option_choice_f (ALOOKUP [(n, v)])
        (nsLookup_Short env.v)`,
  fs[write_def, nsLookup_pf_nsBind]
);

val nsLookup_write_cons_eqs = Q.store_thm("nsLookup_write_cons_eqs",
  `nsLookup_Short ((write_cons n v env).v) = nsLookup_Short env.v /\
    nsLookup_Mod1 ((write_cons n v env).v) = nsLookup_Mod1 env.v /\
    nsLookup_Mod1 ((write_cons n v env).c) = nsLookup_Mod1 env.c /\
    nsLookup_Short ((write_cons n v env).c) = option_choice_f (ALOOKUP [(n, v)])
        (nsLookup_Short env.c)`,
  fs[write_cons_def, nsLookup_pf_nsBind]
);

val nsLookup_merge_env_eqs = Q.store_thm("nsLookup_merge_env_eqs",
  `nsLookup_Short ((merge_env env env2).v)
        = option_choice_f (nsLookup_Short env.v) (nsLookup_Short env2.v) /\
    nsLookup_Mod1 ((merge_env env env2).v)
        = option_choice_f (nsLookup_Mod1 env.v) (nsLookup_Mod1 env2.v) /\
    nsLookup_Short ((merge_env env env2).c)
        = option_choice_f (nsLookup_Short env.c) (nsLookup_Short env2.c) /\
    nsLookup_Mod1 ((merge_env env env2).c)
        = option_choice_f (nsLookup_Mod1 env.c) (nsLookup_Mod1 env2.c)`,
  fs[merge_env_def, nsLookup_Short_nsAppend, nsLookup_Mod1_nsAppend]);

val nsLookup_write_mod_eqs = Q.store_thm("nsLookup_write_mod_eqs",
  `nsLookup_Short ((write_mod mnm env env2).v) = nsLookup_Short env2.v /\
    nsLookup_Mod1 ((write_mod mnm env env2).v)
        = option_choice_f (ALOOKUP [(mnm, env.v)]) (nsLookup_Mod1 env2.v) /\
    nsLookup_Short ((write_mod mnm env env2).c) = nsLookup_Short env2.c /\
    nsLookup_Mod1 ((write_mod mnm env env2).c)
        = option_choice_f (ALOOKUP [(mnm, env.c)]) (nsLookup_Mod1 env2.c)`,
  fs[write_mod_def, nsLookup_Short_nsAppend, nsLookup_Mod1_nsAppend,
    nsLookup_Short_nsLift, nsLookup_Mod1_nsLift,
    alookup_empty_option_choice_f]);

val nsLookup_empty_eqs = Q.store_thm("nsLookup_empty_eqs",
  `nsLookup_Short empty_env.v = ALOOKUP [] /\
    nsLookup_Mod1 empty_env.v = ALOOKUP [] /\
    nsLookup_Short empty_env.c = ALOOKUP [] /\
    nsLookup_Mod1 empty_env.c = ALOOKUP []`,
  fs[empty_env_def, nsEmpty_def, nsLookup_Short_Bind, nsLookup_Mod1_def]);

(* nonsense theorem instantiated when env's are defined *)

val nsLookup_eq_format = Q.store_thm("nsLookup_eq_format",
  `!env:v sem_env.
     (nsLookup_Short env.v = nsLookup_Short env.v) /\
     (nsLookup_Short env.c = nsLookup_Short env.c) /\
     (nsLookup_Mod1 env.v = nsLookup_Mod1 env.v) /\
     (nsLookup_Mod1 env.c = nsLookup_Mod1 env.c)`,
  rewrite_tac []);

(* some shorthands that are allowed to EVAL are below *)

val write_rec_def = Define `
  write_rec funs env1 env =
    FOLDR (\f env. write (FST f) (Recclosure env1 funs (FST f)) env) env funs`;

val write_rec_thm = Q.store_thm("write_rec_thm",
  `write_rec funs env1 env =
    env with v := build_rec_env funs env1 env.v`,
  fs [write_rec_def,build_rec_env_def]
  \\ qspec_tac (`Recclosure env1 funs`,`hh`)
  \\ qspec_tac (`env`,`env`)
  \\ Induct_on `funs` \\ fs [FORALL_PROD]
  \\ fs [write_def]);

val write_conses_def = Define `
  write_conses ([] :(tvarN, type_ident # stamp) alist) env = env /\
  write_conses ((n,y)::xs) env =
    write_cons n y (write_conses xs env)`;

val write_tdefs_def = Define `
  write_tdefs n [] env = env /\
  write_tdefs n ((x,_,condefs)::tds) env =
    write_tdefs (n+1) tds (write_conses (REVERSE (build_constrs n condefs)) env)`

val write_conses_v = prove(
  ``!xs env. (write_conses xs env).v = env.v``,
  Induct \\ fs [write_conses_def,FORALL_PROD,write_cons_def]);

val write_tdefs_lemma = prove(
  ``!tds env n.
      write_tdefs n tds env =
      merge_env <|v := nsEmpty; c := build_tdefs n tds|> env``,
  Induct \\ fs [write_tdefs_def,merge_env_def,build_tdefs_def,FORALL_PROD]
  \\ rw [write_conses_v]
  \\ rewrite_tac [GSYM namespacePropsTheory.nsAppend_assoc]
  \\ AP_TERM_TAC
  \\ Q.SPEC_TAC (`REVERSE (build_constrs n p_2)`,`xs`)
  \\ Induct \\ fs [write_conses_def,FORALL_PROD,write_cons_def]);

val write_tdefs_thm = store_thm("write_tdefs_thm",
  ``write_tdefs n tds empty_env =
    <|v := nsEmpty; c := build_tdefs n tds|>``,
  fs [write_tdefs_lemma,empty_env_def,merge_env_def]);

val merge_env_write_conses = prove(
  ``!xs env. merge_env (write_conses xs env1) env2 =
             write_conses xs (merge_env env1 env2)``,
  Induct \\ fs [write_conses_def,FORALL_PROD]
  \\ fs [write_cons_def,merge_env_def,sem_env_component_equality]);

val merge_env_write_tdefs = prove(
  ``!tds n env1 env2.
      merge_env (write_tdefs n tds env1) env2 =
      write_tdefs n tds (merge_env env1 env2)``,
  Induct \\ fs [write_tdefs_def,FORALL_PROD,merge_env_write_conses]);

(* it's not clear if these are still needed, but ml_progComputeLib and
   cfTacticsLib want them to be present. *)

val nsLookup_nsAppend_Short = Q.store_thm("nsLookup_nsAppend_Short[compute]",`
  (nsLookup (nsAppend e1 e2) (Short id) =
    case nsLookup e1 (Short id) of
      NONE =>
        nsLookup e2 (Short id)
    | SOME v => SOME v)`,
  every_case_tac>>
  Cases_on`nsLookup e2(Short id)`>>
  fs[namespacePropsTheory.nsLookup_nsAppend_some,
     namespacePropsTheory.nsLookup_nsAppend_none,id_to_mods_def]);

val write_simp = Q.store_thm("write_simp[compute]",
  `(write n v env).c = env.c /\
    nsLookup (write n v env).v (Short q) =
      if n = q then SOME v else nsLookup env.v (Short q)`,
  IF_CASES_TAC>>fs[write_def,namespacePropsTheory.nsLookup_nsBind]);

val write_cons_simp = Q.store_thm("write_cons_simp[compute]",
  `(write_cons n v env).v = env.v /\
    nsLookup (write_cons n v env).c (Short q) =
      if n = q then SOME v else nsLookup env.c (Short q)`,
  IF_CASES_TAC>>fs[write_cons_def,namespacePropsTheory.nsLookup_nsBind]);

val write_mod_simp = Q.store_thm("write_mod_simp[compute]",
  `(nsLookup (write_mod mn env env2).v (Short q) =
    nsLookup env2.v (Short q)) ∧
   (nsLookup (write_mod mn env env2).c (Short c) =
    nsLookup env2.c (Short c)) ∧
   (nsLookup (write_mod mn env env2).v (Long mn' r) =
    if mn = mn' then nsLookup env.v r
    else nsLookup env2.v (Long mn' r)) ∧
   (nsLookup (write_mod mn env env2).c (Long mn' s) =
    if mn = mn' then nsLookup env.c s
    else nsLookup env2.c (Long mn' s))`,
  rw[write_mod_def]);

val empty_simp = Q.store_thm("empty_simp[compute]",
  `nsLookup empty_env.v q = NONE /\
   nsLookup empty_env.c q = NONE`,
  fs [empty_env_def] );
(* the components of nsLookup are 'nicer' partial functions *)




(* --- declarations --- *)

val Decls_def = Define `
  Decls env s1 ds env2 s2 <=>
    s1.clock = s2.clock /\
    ?ck1 ck2. evaluate_decs (s1 with clock := ck1) env ds =
                            (s2 with clock := ck2, Rval env2)`;

val Decls_Dtype = Q.store_thm("Decls_Dtype",
  `!env s tds env2 s2 locs.
      Decls env s [Dtype locs tds] env2 s2 <=>
      EVERY check_dup_ctors tds /\
      s2 = s with <| next_type_stamp := (s.next_type_stamp + LENGTH tds) |> /\
      env2 = write_tdefs s.next_type_stamp tds empty_env`,
  SIMP_TAC std_ss [Decls_def,evaluate_decs_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs [bool_case_eq]
  \\ rveq \\ fs [state_component_equality,write_tdefs_thm]);

val Decls_Dexn = Q.store_thm("Decls_Dexn",
  `!env s n l env2 s2 locs.
      Decls env s [Dexn locs n l] env2 s2 <=>
      s2 = s with <| next_exn_stamp := (s.next_exn_stamp + 1) |> /\
      env2 = write_cons n (LENGTH l, ExnStamp s.next_exn_stamp) empty_env`,
  SIMP_TAC std_ss [Decls_def,evaluate_decs_def,write_cons_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs [bool_case_eq]
  \\ rveq \\ fs [state_component_equality,write_tdefs_thm]
  \\ fs [nsBind_def,nsEmpty_def,nsSing_def,empty_env_def]);

val Decls_Dtabbrev = Q.store_thm("Decls_Dtabbrev",
  `!env s x y z env2 s2 locs.
      Decls env s [Dtabbrev locs x y z] env2 s2 <=>
      s2 = s ∧ env2 = empty_env`,
  fs [Decls_def,evaluate_decs_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs [bool_case_eq]
  \\ rveq \\ fs [state_component_equality,empty_env_def]);

val eval_rel_def = Define `
  eval_rel s1 env e s2 x <=>
    s1.clock = s2.clock /\
    ?ck1 ck2.
       evaluate (s1 with clock := ck1) env [e] =
                (s2 with clock := ck2,Rval [x])`

val eval_rel_alt = store_thm("eval_rel_alt",
  ``eval_rel s1 env e s2 x <=>
    s2.clock = s1.clock ∧
    ∃ck. evaluate (s1 with clock := ck) env [e] = (s2,Rval [x])``,
  reverse eq_tac \\ rw [] \\ fs [eval_rel_def]
  THEN1 (qexists_tac `ck` \\ fs [state_component_equality])
  \\ drule evaluatePropsTheory.evaluate_set_clock \\ fs []
  \\ disch_then (qspec_then `s2.clock` strip_assume_tac)
  \\ rename [`evaluate (s1 with clock := ck) env [e]`]
  \\ qexists_tac `ck` \\ fs [state_component_equality]);

val eval_list_rel_def = Define `
  eval_list_rel s1 env e s2 x <=>
    s1.clock = s2.clock /\
    ?ck1 ck2.
       evaluate (s1 with clock := ck1) env e =
                (s2 with clock := ck2,Rval x)`

val eval_match_rel_def = Define `
  eval_match_rel s1 env v pats err_v s2 x <=>
    s1.clock = s2.clock /\
    ?ck1 ck2.
       evaluate_match
                (s1 with clock := ck1) env v pats err_v =
                (s2 with clock := ck2,Rval [x])`

(* Delays the write *)
val Decls_Dlet = Q.store_thm("Decls_Dlet",
  `!env s1 v e s2 env2 locs.
      Decls env s1 [Dlet locs (Pvar v) e] env2 s2 <=>
      ?x. eval_rel s1 env e s2 x /\ (env2 = write v x empty_env)`,
  simp [Decls_def,evaluate_decs_def,eval_rel_def]
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
  \\ fs [write_def,empty_env_def]);

val FOLDR_LEMMA = Q.prove(
  `!xs ys. FOLDR (\(x1,x2,x3) x4. (x1, f x1 x2 x3) :: x4) [] xs ++ ys =
           FOLDR (\(x1,x2,x3) x4. (x1, f x1 x2 x3) :: x4) ys xs`,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [FORALL_PROD]);

(* Delays the write in build_rec_env *)
val Decls_Dletrec = Q.store_thm("Decls_Dletrec",
  `!env s1 funs s2 env2 locs.
      Decls env s1 [Dletrec locs funs] env2 s2 <=>
      (s2 = s1) /\
      ALL_DISTINCT (MAP (\(x,y,z). x) funs) /\
      (env2 = write_rec funs env empty_env)`,
  simp [Decls_def,evaluate_decs_def,bool_case_eq,PULL_EXISTS]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs []
  \\ fs [state_component_equality,write_rec_def]
  \\ fs[write_def,write_rec_thm,empty_env_def,build_rec_env_def]
  \\ rpt (pop_assum kall_tac)
  \\ qspec_tac (`Recclosure env funs`,`xx`)
  \\ qspec_tac (`nsEmpty:env_val`,`nn`)
  \\ Induct_on `funs` \\ fs [FORALL_PROD]
  \\ pop_assum (assume_tac o GSYM) \\ fs []);

val Decls_Dmod = Q.store_thm("Decls_Dmod",
  `Decls env1 s1 [Dmod mn sn ds] env2 s2 <=>
   ?s env.
      Decls env1 s1 ds env s /\ s2 = s /\
      env2 = write_mod mn env empty_env`,
  fs [Decls_def,Decls_def,evaluate_decs_def,PULL_EXISTS,
      combine_dec_result_def,write_mod_def,empty_env_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs [pair_case_eq,result_case_eq]
  \\ rveq \\ fs [] \\ asm_exists_tac \\ fs []);

val Decls_NIL = Q.store_thm("Decls_NIL",
  `!env s n l env2 s2.
      Decls env s [] env2 s2 <=>
      s2 = s ∧ env2 = empty_env`,
  fs [Decls_def,evaluate_decs_def,state_component_equality,empty_env_def]
  \\ rw [] \\ eq_tac \\ rw []);

val Decls_CONS = Q.store_thm("Decls_CONS",
  `!s1 s3 env1 d ds1 ds2 env3.
      Decls env1 s1 (d::ds2) env3 s3 =
      ?envA envB s2.
         Decls env1 s1 [d] envA s2 /\
         Decls (merge_env envA env1) s2 ds2 envB s3 /\
         env3 = merge_env envB envA`,
  rw[Decls_def,PULL_EXISTS,evaluate_decs_def]
  \\ reverse (rw[EQ_IMP_THM]) \\ fs []
  THEN1
   (once_rewrite_tac [evaluate_decs_cons]
    \\ imp_res_tac evaluate_decs_add_to_clock \\ fs []
    \\ first_x_assum (qspec_then `ck1'` assume_tac)
    \\ qexists_tac `ck1+ck1'` \\ fs []
    \\ fs [merge_env_def,extend_dec_env_def,combine_dec_result_def]
    \\ fs [state_component_equality])
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [evaluate_decs_cons]
  \\ fs [pair_case_eq,result_case_eq] \\ rw [] \\ fs [PULL_EXISTS]
  \\ Cases_on `r` \\ fs [combine_dec_result_def]
  \\ rveq \\ fs []
  \\ qexists_tac `env1'` \\ fs []
  \\ qexists_tac `a` \\ fs []
  \\ qexists_tac `s1' with clock := s3.clock` \\ fs [merge_env_def]
  \\ qexists_tac `ck1` \\ fs [state_component_equality]
  \\ qexists_tac `s1'.clock` \\ fs [state_component_equality]
  \\ `(s1' with clock := s1'.clock) = s1'` by fs [state_component_equality]
  \\ fs [extend_dec_env_def]
  \\ fs [state_component_equality]);

val merge_env_empty_env = Q.store_thm("merge_env_empty_env",
  `merge_env env empty_env = env /\
   merge_env empty_env env = env`,
  rw [merge_env_def,empty_env_def]);

val merge_env_assoc = Q.store_thm("merge_env_assoc",
  `merge_env env1 (merge_env env2 env3) = merge_env (merge_env env1 env2) env3`,
  fs [merge_env_def]);

val Decls_APPEND = Q.store_thm("Decls_APPEND",
  `!s1 s3 env1 ds1 ds2 env3.
      Decls env1 s1 (ds1 ++ ds2) env3 s3 =
      ?envA envB s2.
         Decls env1 s1 ds1 envA s2 /\
         Decls (merge_env envA env1) s2 ds2 envB s3 /\
         env3 = merge_env envB envA`,
  Induct_on `ds1` \\ fs [APPEND,Decls_NIL,merge_env_empty_env]
  \\ once_rewrite_tac [Decls_CONS]
  \\ fs [PULL_EXISTS,merge_env_assoc] \\ metis_tac []);

val Decls_SNOC = Q.store_thm("Decls_SNOC",
  `!s1 s3 env1 ds1 d env3.
      Decls env1 s1 (SNOC d ds1) env3 s3 =
      ?envA envB s2.
         Decls env1 s1 ds1 envA s2 /\
         Decls (merge_env envA env1) s2 [d] envB s3 /\
         env3 = merge_env envB envA`,
  METIS_TAC [SNOC_APPEND, Decls_APPEND]);


(* The translator and CF tools use the following definition of ML_code
   to build verified ML programs. *)

val ML_code_def = Define `
  (ML_code env1 s1 prog NONE env2 s2 <=>
     Decls env1 s1 prog env2 s2) /\
  (ML_code env1 s1 prog (SOME (mn:string,outside,env)) env2 s2 <=>
     ?s.
       Decls env1 s1 outside env s /\
       Decls (merge_env env env1) s prog env2 s2)`

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
  val init_env_def = Define `
    init_env = ^init_env_tm`;
  val init_state_def = Define `
    init_state ffi = ^init_state_tm`;
end

val init_state_env_thm = Q.store_thm("init_state_env_thm",
  `THE (prim_sem_env ffi) = (init_state ffi,init_env)`,
  CONV_TAC(RAND_CONV EVAL) \\ rewrite_tac[prim_sem_env_eq,THE_DEF]);

val nsLookup_init_state_pfun_eqs = save_thm("nsLookup_init_state_pfun_eqs",
  [``nsLookup_Short init_env.c``, ``nsLookup_Short init_env.v``,
    ``nsLookup_Mod1 init_env.c``, ``nsLookup_Mod1 init_env.v``]
  |> map (SIMP_CONV bool_ss
        [init_env_def, nsLookup_Short_Bind, nsLookup_Mod1_def,
            namespace_case_def, sem_env_accfupds, K_DEF])
  |> LIST_CONJ);

end

val ML_code_NIL = Q.store_thm("ML_code_NIL",
  `ML_code init_env (init_state ffi) [] NONE empty_env (init_state ffi)`,
  fs [ML_code_def,Decls_NIL]);

(* opening and closing of modules *)

val ML_code_new_module = Q.store_thm("ML_code_new_module",
  `ML_code env1 s1 prog NONE env2 s2 ==>
    !mn. ML_code env1 s1 [] (SOME (mn,prog,env2)) empty_env s2`,
  fs [ML_code_def] \\ rw [Decls_NIL] \\ EVAL_TAC);

val ML_code_close_module = Q.store_thm("ML_code_close_module",
  `ML_code env1 s1 prog (SOME (mn,ds,env)) env2 s2 ==>
(* ∀sigs. *)
      ML_code env1 s1 (SNOC (Dmod mn NONE prog) ds) NONE
        (write_mod mn env2 env) s2`,
  fs [ML_code_def] \\ rw [] \\ fs [SNOC_APPEND,Decls_APPEND]
  \\ asm_exists_tac \\ fs [Decls_Dmod,PULL_EXISTS]
  \\ asm_exists_tac \\ fs []
  \\ fs [write_mod_def,merge_env_def,empty_env_def]);

(* appending a Dtype *)

val ML_code_Dtype = Q.store_thm("ML_code_Dtype",
  `ML_code env1 s1 prog mn env2 s2 ==>
   !tds locs.
     EVERY check_dup_ctors tds ==>
     ML_code env1 s1 (SNOC (Dtype locs tds) prog) mn
       (write_tdefs s2.next_type_stamp tds env2)
       (s2 with next_type_stamp := s2.next_type_stamp + LENGTH tds)`,
  Cases_on `mn` \\ TRY (PairCases_on `x`)
  \\ fs [ML_code_def,SNOC_APPEND,Decls_APPEND,Decls_Dtype,merge_env_empty_env]
  \\ rw [] \\ rpt (asm_exists_tac \\ fs [])
  \\ fs [merge_env_write_tdefs] \\ AP_TERM_TAC
  \\ fs [merge_env_def,empty_env_def,sem_env_component_equality]);

(* appending a Dexn *)

val ML_code_Dexn = Q.store_thm("ML_code_Dexn",
  `ML_code env1 s1 prog mn env2 s2 ==>
   !n l locs.
     ML_code env1 s1 (SNOC (Dexn locs n l) prog) mn
       (write_cons n (LENGTH l,ExnStamp s2.next_exn_stamp) env2)
       (s2 with next_exn_stamp := s2.next_exn_stamp + 1)`,
  Cases_on `mn` \\ TRY (PairCases_on `x`)
  \\ fs [ML_code_def,SNOC_APPEND,Decls_APPEND,Decls_Dexn,merge_env_empty_env]
  \\ rw [] \\ rpt (asm_exists_tac \\ fs [])
  \\ fs [write_cons_def,merge_env_def,empty_env_def,sem_env_component_equality]);

(* appending a Dtabbrev *)

val ML_code_Dtabbrev = Q.store_thm("ML_code_Dtabbrev",
  `ML_code env1 s1 prog mn env2 s2 ==>
   !x y z locs.
     ML_code env1 s1 (SNOC (Dtabbrev locs x y z) prog) mn env2 s2`,
  Cases_on `mn` \\ TRY (PairCases_on `x`)
  \\ fs [ML_code_def,SNOC_APPEND,Decls_APPEND,Decls_Dtabbrev,merge_env_empty_env]);

(* appending a Letrec *)

val build_rec_env_APPEND = Q.prove(
  `nsAppend (build_rec_env funs cl_env nsEmpty) add_to_env =
   build_rec_env funs cl_env add_to_env`,
  fs [build_rec_env_def] \\ qspec_tac (`Recclosure cl_env funs`,`xxx`)
  \\ qspec_tac (`add_to_env`,`xs`)
  \\ Induct_on `funs` \\ fs [FORALL_PROD]);

val ML_code_env_def = Define `
  (ML_code_env env1 NONE env2 = merge_env env2 env1) /\
  (ML_code_env env1 (SOME (_,_,env)) env2 = merge_env env2 (merge_env env env1))`;

val ML_code_Dletrec = Q.store_thm("ML_code_Dletrec",
  `ML_code env1 s1 prog mn env2 s2 ==>
    !fns locs.
      ALL_DISTINCT (MAP (λ(x,y,z). x) fns) ==>
      ML_code env1 s1 (SNOC (Dletrec locs fns) prog) mn
        (write_rec fns (ML_code_env env1 mn env2) env2) s2`,
  Cases_on `mn` \\ TRY (PairCases_on `x`)
  \\ fs [ML_code_def,SNOC_APPEND,Decls_APPEND,Decls_Dletrec]
  \\ rw [] \\ rpt (asm_exists_tac \\ fs [ML_code_env_def])
  \\ fs [merge_env_def,write_rec_thm,empty_env_def,sem_env_component_equality]
  \\ fs [build_rec_env_APPEND]);

(* appending a Let *)

val ML_code_Dlet_var = Q.store_thm("ML_code_Dlet_var",
  `ML_code env1 s1 prog mn env2 s2 ==>
    !e x s3.
      eval_rel s2 (ML_code_env env1 mn env2) e s3 x ==>
      !n locs.
        ML_code env1 s1 (SNOC (Dlet locs (Pvar n) e) prog)
          mn (write n x env2) s3`,
  Cases_on `mn` \\ TRY (PairCases_on `x`)
  \\ fs [ML_code_env_def]
  \\ fs [ML_code_def,SNOC_APPEND,Decls_APPEND,Decls_Dlet]
  \\ rw [] \\ asm_exists_tac \\ fs [PULL_EXISTS]
  \\ rw [] \\ rpt (asm_exists_tac \\ fs [])
  \\ fs [write_def,merge_env_def,empty_env_def,sem_env_component_equality]);

val ML_code_Dlet_Fun = Q.store_thm("ML_code_Dlet_Fun",
  `ML_code env1 s1 prog mn env2 s2 ==>
    !n v e locs.
      ML_code env1 s1 (SNOC (Dlet locs (Pvar n) (Fun v e)) prog)
        mn (write n (Closure (ML_code_env env1 mn env2) v e) env2) s2`,
  rw [] \\ match_mp_tac (ML_code_Dlet_var |> MP_CANON) \\ fs []
  \\ fs [evaluate_def,state_component_equality,eval_rel_def]);

(* lookup function definitions *)

val lookup_var_def = Define `
  lookup_var name (env:v sem_env) = nsLookup env.v (Short name)`;

val lookup_cons_def = Define `
  lookup_cons name (env:v sem_env) = nsLookup env.c name`;

(* the old lookup formulation worked via nsLookup/mod_defined,
   and mod_defined is still used in various characteristic scripts
   so we supply an eval theorem that maps to the new approach. *)

val mod_defined_def = zDefine `
  mod_defined env n =
    ∃p1 p2 e3.
      p1 ≠ [] ∧ id_to_mods n = p1 ++ p2 ∧
      nsLookupMod env p1 = SOME e3`;

val mod_defined_nsLookup_Mod1 = Q.store_thm(
  "mod_defined_nsLookup_Mod1",
  `mod_defined env id = (case id of Short _ => F
        | Long mn _ => (case nsLookup_Mod1 env mn of NONE => F | _ => T))`,
  PURE_CASE_TAC \\ fs [id_to_mods_def, mod_defined_def]
    \\ Cases_on `env`
    \\ fs [Once EXISTS_LIST, nsLookupMod_def, nsLookup_Mod1_def]
    \\ PURE_CASE_TAC \\ fs [Once EXISTS_LIST, nsLookupMod_def]);

(* theorems about old lookup functions *)
(* FIXME: everything below this line is unlikely to be needed. *)

val nsLookupMod_nsBind = Q.prove(`
  p ≠ [] ⇒
  nsLookupMod (nsBind k v env) p = nsLookupMod env p`,
  Cases_on`env`>>fs[nsBind_def]>> Induct_on`p`>>
  fs[nsLookupMod_def]);

val nsLookup_write = Q.store_thm("nsLookup_write",
  `(nsLookup (write n v env).v (Short name) =
       if n = name then SOME v else nsLookup env.v (Short name)) /\
   (nsLookup (write n v env).v (Long mn lname)  =
       nsLookup env.v (Long mn lname)) /\
   (nsLookup (write n v env).c a = nsLookup env.c a) /\
   (mod_defined (write n v env).v x = mod_defined env.v x) /\
   (mod_defined (write n v env).c x = mod_defined env.c x)`,
  fs [write_def] \\ EVAL_TAC \\ rw []
  \\ metis_tac[nsLookupMod_nsBind,mod_defined_def]);

val nsLookup_write_cons = Q.store_thm("nsLookup_write_cons",
  `(nsLookup (write_cons n v env).v a = nsLookup env.v a) /\
   (nsLookup (write_cons n d env).c (Short name) =
     if name = n then SOME d else nsLookup env.c (Short name)) /\
   (mod_defined (write_cons n d env).v x = mod_defined env.v x) /\
   (mod_defined (write_cons n d env).c x = mod_defined env.c x) /\
   (nsLookup (write_cons n d env).c (Long mn lname) =
    nsLookup env.c (Long mn lname))`,
  fs [write_cons_def] \\ EVAL_TAC \\ rw [] \\
  metis_tac[nsLookupMod_nsBind,mod_defined_def]);

val nsLookup_empty = Q.store_thm("nsLookup_empty",
  `(nsLookup empty_env.v a = NONE) /\
   (nsLookup empty_env.c b = NONE) /\
   (mod_defined empty_env.v x = F) /\
   (mod_defined empty_env.c x = F)`,
  rw[empty_env_def, nsLookup_def, mod_defined_def,
    nsLookupMod_def] \\ Cases_on`p1` \\ fs[]);

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

val nsLookup_write_mod = Q.store_thm("nsLookup_write_mod",
  `(nsLookup (write_mod mn env1 env2).v (Short n) =
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
      nsLookup env2.c (Long mn1 ln))`,
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
    metis_tac[]));

val nsLookup_merge_env = Q.store_thm("nsLookup_merge_env[compute]",
  `(nsLookup (merge_env e1 e2).v (Short n) =
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
   (mod_defined e1.c x ∨ mod_defined e2.c x))`,
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
  );

val nsLookup_nsBind_compute = Q.store_thm("nsLookup_nsBind_compute[compute]",
  `(nsLookup (nsBind n v e) (Short n1) =
    if n = n1 then SOME v else nsLookup e (Short n1)) /\
   (nsLookup (nsBind n v e) (Long l1 l2) = nsLookup e (Long l1 l2))`,
  rw [namespacePropsTheory.nsLookup_nsBind]);

val nsLookup_nsAppend = save_thm("nsLookup_nsAppend[compute]",
  nsLookup_merge_env
  |> SIMP_RULE (srw_ss()) [merge_env_def]
  |> Q.INST [`e1`|->`<|c:=e1c;v:=e1v|>`,`e2`|->`<|c:=e2c;v:=e2v|>`]
  |> SIMP_RULE (srw_ss()) []);

(* Base case for mod_defined (?) *)
val mod_defined_base = store_thm("mod_defined_base[compute]",
  ``mod_defined (Bind _ []) _ = F``,
  rw[mod_defined_def]>>Cases_on`p1`>>EVAL_TAC);


(* --- the rest of this file might be unused junk --- *)

(* misc theorems about lookup functions *)

(* No idea why this is sparated out *)
val lookup_var_write = Q.store_thm("lookup_var_write",
  `(lookup_var v (write w x env) = if v = w then SOME x else lookup_var v env) /\
    (nsLookup (write w x env).v (Short v)  =
       if v = w then SOME x else nsLookup env.v (Short v) ) /\
   (nsLookup (write w x env).v (Long mn lname)  =
       nsLookup env.v (Long mn lname)) ∧
    (lookup_cons name (write w x env) = lookup_cons name env)`,
  fs [lookup_var_def,write_def,lookup_cons_def] \\ rw []);

val lookup_var_write_mod = Q.store_thm("lookup_var_write_mod",
  `(lookup_var v (write_mod mn e1 env) = lookup_var v env) /\
   (lookup_cons (Long mn1 (Short name)) (write_mod mn2 e1 env) =
    if mn1 = mn2 then
      lookup_cons (Short name) e1
    else
      lookup_cons (Long mn1 (Short name)) env) /\
   (lookup_cons (Short name) (write_mod mn2 e1 env) =
    lookup_cons (Short name) env)`,
  fs [lookup_var_def,write_mod_def, lookup_cons_def] \\ rw []);

val lookup_var_write_cons = Q.store_thm("lookup_var_write_cons",
  `(lookup_var v (write_cons n d env) = lookup_var v env) /\
   (lookup_cons (Short name) (write_cons n d env) =
     if name = n then SOME d else lookup_cons (Short name) env) /\
   (lookup_cons (Long l full_name) (write_cons n d env) =
    lookup_cons (Long l full_name) env) /\
   (nsLookup (write_cons n d env).v x = nsLookup env.v x)`,
  fs [lookup_var_def,write_cons_def,lookup_cons_def] \\ rw []);

val lookup_var_empty_env = Q.store_thm("lookup_var_empty_env",
  `(lookup_var v empty_env = NONE) /\
    (nsLookup empty_env.v (Short k) = NONE) /\
    (nsLookup empty_env.v (Long mn m) = NONE) /\
    (lookup_cons name empty_env = NONE)`,
  fs[lookup_var_def,empty_env_def,lookup_cons_def]);

(*
val lookup_var_merge_env = Q.store_thm("lookup_var_merge_env",
  `(lookup_var v1 (merge_env e1 e2) =
       case lookup_var v1 e1 of
       | NONE => lookup_var v1 e2
       | res => res) /\
    (lookup_cons name (merge_env e1 e2) =
       case lookup_cons name e1 of
       | NONE => lookup_cons name e2
       | res => res)`,
  fs [lookup_var_def,lookup_cons_def,merge_env_def] \\ rw[] \\ every_case_tac \\
  fs[namespacePropsTheory.nsLookup_nsAppend_some]
  >-
    (Cases_on`nsLookup e2.v (Short v1)`>>
    fs[namespacePropsTheory.nsLookup_nsAppend_none,
       namespacePropsTheory.nsLookup_nsAppend_some,namespaceTheory.id_to_mods_def])
  \\ cheat (* TODO *)));
*)

val _ = export_theory();
