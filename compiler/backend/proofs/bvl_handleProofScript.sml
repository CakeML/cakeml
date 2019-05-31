(*
  Correctness proof for bvl_handle
*)
open preamble bvl_handleTheory bvlSemTheory bvlPropsTheory;

val _ = new_theory"bvl_handleProof";

val _ = set_grammar_ancestry["bvlSem","bvl_handle","bvlProps"];

Theorem evaluate_SmartLet[simp]:
   bvlSem$evaluate ([SmartLet xs x],env,s) = evaluate ([Let xs x],env,s)
Proof
  rw [SmartLet_def] \\ fs [NULL_EQ,evaluate_def]
QED

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

val evaluate_GENLIST = save_thm("evaluate_GENLIST",
  evaluate_genlist_vars
  |> Q.SPECL[`0`,`env ++ ys`,`LENGTH (env:bvlSem$v list)`,`s`]
  |> SIMP_RULE(srw_ss()++ETA_ss)[TAKE_APPEND1]);

val env_rel_def = Define `
  env_rel l env env1 =
    LIST_RELi (\i v1 v2. has_var i l ==> v1 = v2) env env1`

Theorem env_rel_mk_Union:
   !env env1. env_rel (mk_Union lx ly) env env1 <=>
               env_rel lx env env1 /\ env_rel ly env env1
Proof
  fs [LIST_RELi_EL_EQN,env_rel_def] \\ metis_tac []
QED

Theorem env_rel_length:
   env_rel l env env1 ==> LENGTH env1 = LENGTH env
Proof
  fs [LIST_RELi_EL_EQN,env_rel_def]
QED

Theorem env_rel_MAPi:
   env_rel l1 env (MAPi (\i v. if has_var i l1 then v else Number 0) env)
Proof
  fs [LIST_RELi_EL_EQN,env_rel_def]
QED

Theorem IMP_EL_SING:
   k = LENGTH xs ==> EL k (xs ++ [x] ++ ys) = x
Proof
  rw [] \\ fs [] \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [EL_APPEND2]
QED

Theorem ALOOKUP_MAPi_SWAP = Q.prove(`
  !z n k xs.
      n <> k ==>
      ALOOKUP (MAPi (λi x. (x,i+z)) (xs ++ [k])) n =
      ALOOKUP (MAPi (λi x. (x,i+z)) xs) n`,
  Induct_on `xs` \\ fs [o_DEF,ADD1]) |> Q.SPEC `0` |> SIMP_RULE std_ss [];

Theorem ALOOKUP_MAPi_APPEND2 = Q.prove(`
  !z xs k.
      ~MEM k xs ==>
      ALOOKUP (MAPi (λi x. (x,i+z)) (xs ++ [k])) k = SOME (LENGTH xs + z)`,
  Induct_on `xs` \\ fs [o_DEF,ADD1]) |> Q.SPEC `0` |> SIMP_RULE std_ss [];

Theorem IS_SOME_lookup_db_to_set:
   !n. IS_SOME (lookup n (db_to_set l)) = has_var n l
Proof
  fs [db_varsTheory.lookup_db_to_set,IS_SOME_EXISTS]
QED

Theorem evaluate_LetLet:
   (∀env2 extra.
       env_rel l1 env env2 ==> evaluate ([y],env2 ++ extra,s1) = res) /\
    env_rel l1 env env1 ==>
    evaluate ([LetLet (LENGTH env) (db_to_set l1) y],env1 ++ extra,s1) = res
Proof
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
  \\ fs [evaluate_def,IS_SOME_lookup_db_to_set]
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
  \\ fs [EL_APPEND2] \\ match_mp_tac IMP_EL_SING \\ fs []
QED

Theorem env_rel_refl:
   env_rel l env env
Proof
  fs [LIST_RELi_EL_EQN,env_rel_def]
QED

val opt_lemma = Q.prove(
  `x = y <=> (x = SOME () <=> y = SOME ())`,
  Cases_on `x` \\ Cases_on `y` \\ fs []);

val OptionalLetLet_IMP = Q.prove(
  `(ys,l,s',nr') = OptionalLetLet y (LENGTH env) lx s1 limit nr /\
    (∀env2 extra.
      env_rel l env env2 ⇒ evaluate ([y],env2 ++ extra,s) = res) /\
    env_rel l env env1 /\ b ==>
    evaluate (ys,env1 ++ extra,s) = res /\ b`,
  rw [OptionalLetLet_def,evaluate_def]
  \\ drule evaluate_LetLet \\ fs []
  \\ fs [GSYM db_varsTheory.vars_flatten_def,GSYM db_varsTheory.vars_to_list_def]
  \\ sg `db_to_set (vars_flatten lx) = db_to_set lx` \\ fs []
  \\ fs [spt_eq_thm,db_varsTheory.wf_db_to_set]
  \\ rw [] \\ once_rewrite_tac [opt_lemma]
  \\ rewrite_tac [GSYM db_varsTheory.lookup_db_to_set]
  \\ fs []);

Theorem OptionalLetLet_limit:
   (ys,l,s',nr') = OptionalLetLet e (LENGTH env) lx s1 limit nr /\
    env_rel l env env1 ==> env_rel lx env env1
Proof
  rw [OptionalLetLet_def,GSYM db_varsTheory.vars_to_list_def,
      GSYM db_varsTheory.vars_flatten_def,env_rel_def] \\ fs []
QED

Theorem OptionalLetLet_nr:
   (ys,l,s',nr') = OptionalLetLet e (LENGTH env) lx s1 limit nr ==>
    nr' = nr
Proof
  rw [OptionalLetLet_def,GSYM db_varsTheory.vars_to_list_def,
      GSYM db_varsTheory.vars_flatten_def,env_rel_def] \\ fs []
QED

Theorem compile_correct = Q.prove(`
  !xs env s1 ys env1 res s2 extra l s nr.
      compile limit (LENGTH env) xs = (ys,l,s,nr) /\ env_rel l env env1 /\
      (evaluate (xs,env,s1) = (res,s2)) /\ res <> Rerr(Rabort Rtype_error) ==>
      (evaluate (ys,env1 ++ extra,s1) = (res,s2)) /\
      (nr ==> !e. res <> Rerr (Rraise e))`,
  SIMP_TAC std_ss [Once EQ_SYM_EQ]
  \\ recInduct evaluate_ind \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac
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
   (fs [env_rel_mk_Union] \\ rpt gen_tac \\ strip_tac
    \\ drule (GEN_ALL OptionalLetLet_IMP) \\ strip_tac
    \\ pop_assum match_mp_tac
    \\ drule (GEN_ALL OptionalLetLet_limit)
    \\ fs [env_rel_mk_Union] \\ strip_tac
    \\ Cases_on `evaluate ([x1],env,s)` \\ Cases_on `q` \\ fs []
    \\ rveq \\ fs []
    \\ imp_res_tac OptionalLetLet_nr
    \\ rw [] \\ res_tac
    \\ Cases_on `Boolv T = HD a` \\ fs [] \\ res_tac \\ fs [evaluate_def]
    \\ Cases_on `Boolv F = HD a` \\ fs [] \\ res_tac \\ fs [evaluate_def])
  THEN1 (* Let *)
   (Cases_on `LENGTH xs = 0` \\ fs [LENGTH_NIL,NULL_EQ] \\ rveq
    \\ fs [evaluate_def,env_rel_mk_Union] THEN1 metis_tac []
    \\ fs [env_rel_mk_Union] \\ rpt gen_tac \\ strip_tac
    \\ drule (GEN_ALL OptionalLetLet_IMP) \\ strip_tac
    \\ pop_assum match_mp_tac
    \\ drule (GEN_ALL OptionalLetLet_limit)
    \\ fs [env_rel_mk_Union] \\ strip_tac
    \\ Cases_on `evaluate (xs,env,s)` \\ Cases_on `q` \\ fs [] \\ rw []
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
    \\ imp_res_tac OptionalLetLet_nr
    \\ TRY
     (res_tac \\ fs [evaluate_def]
      \\ `env_rel l2 (a ++ env) (a ++ env2)` by
       (fs [env_rel_def,LIST_RELi_EL_EQN] \\ rw []
        \\ Cases_on `i < LENGTH a` \\ fs [EL_APPEND1,NOT_LESS,EL_APPEND2] \\ NO_TAC)
      \\ res_tac \\ fs [] \\ NO_TAC)
    \\ fs [] \\ res_tac \\ fs [] \\ res_tac \\ fs []
    \\ `env_rel l2 (a ++ env) (a ++ env1)` by
     (fs [env_rel_def,LIST_RELi_EL_EQN] \\ rw []
      \\ Cases_on `i < LENGTH a` \\ fs [EL_APPEND1,NOT_LESS,EL_APPEND2] \\ NO_TAC)
    \\ res_tac \\ fs [])
  THEN1 (* Raise *)
   (fs [env_rel_mk_Union] \\ rpt gen_tac \\ strip_tac
    \\ drule (GEN_ALL OptionalLetLet_IMP) \\ strip_tac
    \\ pop_assum match_mp_tac
    \\ drule (GEN_ALL OptionalLetLet_limit)
    \\ fs [env_rel_mk_Union] \\ strip_tac
    \\ Cases_on `evaluate ([x1],env,s)` \\ Cases_on `q` \\ fs [] \\ rw []
    \\ imp_res_tac OptionalLetLet_nr
    \\ res_tac \\ fs [evaluate_def])
  THEN1 (* Handle *)
   (rpt gen_tac \\ strip_tac
    \\ Cases_on `evaluate ([x1],env,s1)` \\ fs []
    \\ `q <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ fs []) \\ fs []
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] \\ fs []
    \\ rename1 `compile limit (LENGTH env) [x1] = ([yy],l1,s3)`
    \\ Cases_on `nr1` \\ fs [] \\ rveq
    THEN1
     (Cases_on `q` \\ fs [] \\ rveq \\ fs []
      \\ Cases_on `e` \\ fs [] \\ rfs [] \\ rveq \\ fs [])
    \\ fs [evaluate_def,env_rel_mk_Union]
    \\ drule evaluate_LetLet \\ fs []
    \\ every_case_tac \\ fs [ADD1] \\ rw [] \\ rfs[]
    \\ `env_rel l2 (a::env) (a::env1)` by
     (fs [env_rel_def,LIST_RELi_EL_EQN]
      \\ Cases \\ fs [ADD1]) \\ res_tac \\ fs [])
  THEN1 (* Op *)
   (fs [env_rel_mk_Union] \\ rpt gen_tac \\ strip_tac
    \\ drule (GEN_ALL OptionalLetLet_IMP) \\ strip_tac
    \\ pop_assum match_mp_tac
    \\ drule (GEN_ALL OptionalLetLet_limit)
    \\ imp_res_tac OptionalLetLet_nr
    \\ fs [env_rel_mk_Union] \\ strip_tac
    \\ Cases_on `evaluate (xs,env,s)` \\ Cases_on `q` \\ fs [] \\ rw []
    \\ res_tac \\ fs [evaluate_def]
    \\ every_case_tac \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac do_app_err \\ fs [] \\ res_tac \\ fs [])
  THEN1 (* Tick *)
   (Cases_on `s.clock = 0` \\ fs [] \\ rw [evaluate_def] \\ res_tac \\ fs [])
  THEN1 (* Call *)
   (fs [env_rel_mk_Union] \\ rpt gen_tac \\ strip_tac
    \\ drule (GEN_ALL OptionalLetLet_IMP) \\ strip_tac
    \\ pop_assum match_mp_tac
    \\ drule (GEN_ALL OptionalLetLet_limit)
    \\ imp_res_tac OptionalLetLet_nr
    \\ fs [env_rel_mk_Union] \\ strip_tac
    \\ Cases_on `evaluate (xs,env,s1)` \\ Cases_on `q` \\ fs [] \\ rw[]
    \\ res_tac \\ fs [evaluate_def]))
  |> Q.SPECL [`xs`,`env`,`s1`,`ys`,`env`,`res`,`s2`,`[]`]
  |> SIMP_RULE std_ss [APPEND_NIL,env_rel_refl];

val _ = save_thm("compile_correct",compile_correct);

Theorem compile_correct:
   (evaluate ([x],env,s1) = (res,s2)) /\ res <> Rerr(Rabort Rtype_error) /\
    k = LENGTH env ==>
    (evaluate ([compile_exp l k x],env,s1) = (res,s2))
Proof
  fs [compile_exp_def]
  \\ Cases_on `compile l (LENGTH env) [bvl_const$compile_exp x]`
  \\ PairCases_on `r` \\ rw []
  \\ drule bvl_constProofTheory.evaluate_compile_exp \\ fs [] \\ rw []
  \\ drule compile_sing \\ rw []
  \\ drule compile_correct \\ fs []
QED

Theorem dest_Seq_thm:
   !x. dest_Seq x = SOME (y0,y1) <=>
        x = Let [y0;y1] (Var 1)
Proof
  ho_match_mp_tac dest_Seq_ind \\ fs [] \\ rw [] \\ EVAL_TAC
  \\ rw [] \\ eq_tac \\ rw []
QED

Theorem compile_seqs_correct:
   !l x acc s1 s2 s3 res res3.
      evaluate ([x],[],s1) = (res,s2) /\
      (!y r. acc = SOME y /\ res = Rval r ==>
             res3 <> Rerr (Rabort Rtype_error) /\
             evaluate ([y],[],s2) = (res3,s3)) /\
      res <> Rerr (Rabort Rtype_error) ==>
      evaluate ([compile_seqs l x acc],[],s1) =
        if acc = NONE then (res,s2) else
          case res of Rval _ => (res3,s3) | _ => (res,s2)
Proof
  HO_MATCH_MP_TAC compile_seqs_ind \\ rpt strip_tac
  \\ once_rewrite_tac [compile_seqs_def]
  \\ Cases_on `dest_Seq x` \\ fs []
  THEN1
   (CASE_TAC \\ fs []
    THEN1 (match_mp_tac compile_correct \\ fs [])
    \\ fs [bvlSemTheory.evaluate_def]
    \\ drule (GEN_ALL compile_correct) \\ fs [] \\ rw []
    \\ CASE_TAC \\ fs []
    \\ pop_assum kall_tac
    \\ rename1 `evaluate ([y],[],s2) = (res3,s3)`
    \\ `FST (evaluate ([y],[],s2)) <> Rerr (Rabort Rtype_error)` by fs []
    \\ drule evaluate_expand_env \\ fs [])
  \\ rename1 `dest_Seq x = SOME y` \\ PairCases_on `y`
  \\ fs [dest_Seq_thm] \\ rveq
  \\ fs [evaluate_def]
  \\ Cases_on `evaluate ([y0],[],s1)` \\ fs []
  \\ rename1 `evaluate ([y0],[],s1) = (res5,s5)`
  \\ first_assum drule \\ strip_tac
  \\ reverse (Cases_on `res5`) \\ fs []
  THEN1 (rveq \\ fs [] \\ rfs [])
  \\ Cases_on `evaluate ([y1],[],s5)` \\ fs []
  \\ rename1 `evaluate ([y1],[],s5) = (res6,s6)`
  \\ Cases_on `res6` \\ fs []
  \\ fs [ADD1]
  \\ drule evaluate_SING
  \\ strip_tac \\ rveq \\ fs [] \\ rveq \\ fs []
  \\ qpat_x_assum `!x1 x2 x3 x4. _` kall_tac
  \\ first_x_assum drule \\ fs []
  \\ Cases_on `acc` \\ fs []
QED

Theorem compile_any_correct:
   (evaluate ([x],env,s1) = (res,s2)) /\ res <> Rerr(Rabort Rtype_error) /\
    k = LENGTH env ==>
    (evaluate ([compile_any split_seq l k x],env,s1) = (res,s2))
Proof
  rw [compile_any_def,compile_correct] \\ fs [LENGTH_NIL] \\ rw []
  \\ drule compile_seqs_correct
  \\ disch_then (qspecl_then [`l`,`NONE`] mp_tac) \\ fs []
QED

Theorem compile_IMP_LENGTH:
   compile l n xs = (ys,l1,s1) ==> LENGTH ys = LENGTH xs
Proof
  rw [] \\ mp_tac (SPEC_ALL compile_length) \\ asm_simp_tac std_ss []
QED

Theorem bVarBound_CONS:
   bVarBound m [x] /\ bVarBound m xs ==> bVarBound m (x::xs)
Proof
  Cases_on `xs` \\ fs []
QED

Theorem bVarBound_MEM:
   bVarBound n xs <=> !x. MEM x xs ==> bVarBound n [x]
Proof
  fs [Once bVarBound_EVERY,EVERY_MEM]
QED

Theorem bEvery_MEM:
   bEvery p xs = !x. MEM x xs ==> bEvery p [x]
Proof
  fs [Once bEvery_EVERY,EVERY_MEM]
QED

Theorem bVarBound_LESS_EQ:
   !m xs n. bVarBound m xs /\ m <= n ==> bVarBound n xs
Proof
  HO_MATCH_MP_TAC bVarBound_ind \\ rw [] \\ fs []
QED

Theorem ALOOKUP_MAPi:
   !xs i x.
      ALOOKUP (MAPi (λi x. (x,i)) xs) n = SOME x ==> x < LENGTH xs
Proof
  HO_MATCH_MP_TAC SNOC_INDUCT \\ rw []
  \\ fs [SNOC_APPEND,MAPi_APPEND,ALOOKUP_APPEND]
  \\ every_case_tac \\ fs []
QED

Theorem bVarBound_SmartLet[simp]:
   bVarBound m [SmartLet x xs] = bVarBound m [Let x xs]
Proof
  rw [SmartLet_def] \\ fs [NULL_EQ]
QED

Theorem bVarBound_LetLet:
   bVarBound m [y] /\ n <= m ==> bVarBound m [LetLet n (l1:num_set) y]
Proof
  fs [LetLet_def] \\ strip_tac
  \\ once_rewrite_tac [bVarBound_MEM]
  \\ fs [MEM_MAP,MEM_GENLIST,PULL_EXISTS,MEM_FILTER]
  \\ reverse conj_tac
  THEN1 (match_mp_tac bVarBound_LESS_EQ \\ asm_exists_tac \\ fs [])
  \\ rw [] \\ every_case_tac \\ fs []
  \\ qabbrev_tac `xs = FILTER (λn. IS_SOME (lookup n l1)) (GENLIST I n)`
  \\ imp_res_tac ALOOKUP_MAPi \\ fs []
QED

Theorem bVarBound_OptionalLetLet:
   bVarBound m [e] /\ n <= m ==>
    bVarBound m (FST (OptionalLetLet e n l s limit nr))
Proof
  rw [OptionalLetLet_def,bVarBound_LetLet]
QED

Theorem bVarBound_compile:
   ∀l n xs m. n ≤ m ⇒ bVarBound m (FST (compile l n xs))
Proof
  ho_match_mp_tac compile_ind \\ rw [] \\ fs [compile_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ imp_res_tac compile_sing \\ rw [] \\ res_tac
  \\ imp_res_tac bVarBound_CONS \\ fs []
  \\ TRY (first_x_assum match_mp_tac) \\ fs []
  \\ imp_res_tac compile_IMP_LENGTH \\ fs []
  \\ imp_res_tac bVarBound_LetLet \\ fs []
  \\ match_mp_tac bVarBound_OptionalLetLet \\ fs []
QED

Theorem compile_IMP_bVarBound:
   compile l n xs = (ys,l2,s2) ==> bVarBound n ys
Proof
  rw [] \\ mp_tac (Q.INST [`m`|->`n`] (SPEC_ALL bVarBound_compile)) \\ fs []
QED

Theorem compile_exp_bVarBound:
   bVarBound n [compile_exp l n x]
Proof
  fs [compile_exp_def]
  \\ Cases_on `compile l n [bvl_const$compile_exp x]`
  \\ Cases_on `r` \\ fs []
  \\ drule compile_IMP_bVarBound
  \\ drule compile_IMP_LENGTH
  \\ Cases_on `q` \\ fs []
  \\ Cases_on `t` \\ fs []
QED

Theorem compile_seqs_bVarBound:
   !l x acc.
      (!y. acc = SOME y ==> bVarBound 0 [y]) ==>
      bVarBound 0 [compile_seqs l x acc]
Proof
  HO_MATCH_MP_TAC compile_seqs_ind \\ rw []
  \\ once_rewrite_tac [compile_seqs_def]
  \\ Cases_on `dest_Seq x` \\ fs []
  THEN1
   (CASE_TAC \\ fs [compile_exp_bVarBound]
    \\ match_mp_tac bVarBound_LESS_EQ
    \\ asm_exists_tac \\ fs [])
  \\ rename1 `dest_Seq x = SOME y` \\ PairCases_on `y`
  \\ fs [] \\ first_x_assum match_mp_tac \\ fs []
QED

Theorem bEvery_CONS:
   bEvery p [x] /\ bEvery p xs ==> bEvery p (x::xs)
Proof
  Cases_on `xs` \\ fs []
QED

Theorem handle_ok_Var_Const_list:
   EVERY (\x. ?v i. x = Var v \/ x = Op (Const i) []) xs ==> handle_ok xs
Proof
  Induct_on `xs` \\ fs [handle_ok_def,PULL_EXISTS] \\ rw []
  \\ Cases_on `xs` \\ fs [handle_ok_def]
QED

Theorem handle_ok_SmartLet:
   handle_ok [SmartLet xs x] <=> handle_ok xs /\ handle_ok [x]
Proof
  rw [SmartLet_def,handle_ok_def] \\ fs [NULL_EQ,LENGTH_NIL,handle_ok_def]
QED

Theorem handle_ok_OptionalLetLet:
   handle_ok [e] /\ bVarBound n [e] ==>
    handle_ok (FST (OptionalLetLet e n lx s l nr))
Proof
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
  \\ match_mp_tac bVarBound_LESS_EQ \\ asm_exists_tac \\ fs []
QED

Theorem compile_handle_ok:
   ∀l n xs. handle_ok (FST (compile l n xs))
Proof
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
  \\ TRY ( conj_tac >- ( strip_tac \\ fs[LENGTH_NIL] ) )
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
  \\ IF_CASES_TAC \\ fs[]
  \\ rpt (pop_assum kall_tac)
  \\ match_mp_tac handle_ok_Var_Const_list
  \\ fs [EVERY_GENLIST]
  \\ rw [] \\ every_case_tac \\ fs []
QED

Theorem compile_exp_handle_ok:
   handle_ok [compile_exp l n x]
Proof
  fs [bvl_handleTheory.compile_exp_def]
  \\ Cases_on `compile l n [bvl_const$compile_exp x]`
  \\ fs [] \\ PairCases_on `r`
  \\ imp_res_tac bvl_handleTheory.compile_sing \\ fs []
  \\ qspecl_then [`l`,`n`,`[bvl_const$compile_exp x]`] mp_tac compile_handle_ok
  \\ fs []
QED

Theorem compile_seqs_handle_ok:
   !l x acc.
      (!y. acc = SOME y ==> handle_ok [y] /\ bVarBound 0 [y]) ==>
      handle_ok [compile_seqs l x acc]
Proof
  HO_MATCH_MP_TAC compile_seqs_ind \\ rw []
  \\ once_rewrite_tac [compile_seqs_def]
  \\ Cases_on `dest_Seq x` \\ fs []
  THEN1
   (CASE_TAC \\ fs [compile_exp_handle_ok]
    \\ fs [handle_ok_def,compile_exp_handle_ok]
    \\ fs [let_ok_def])
  \\ rename1 `dest_Seq x = SOME y` \\ PairCases_on `y`
  \\ fs [] \\ first_x_assum match_mp_tac \\ fs []
  \\ match_mp_tac compile_seqs_bVarBound \\ fs []
QED

Theorem compile_any_handle_ok:
   handle_ok [compile_any split_seq l n x]
Proof
  rw [compile_any_def,compile_exp_handle_ok]
  \\ match_mp_tac compile_seqs_handle_ok \\ fs []
QED

Theorem handle_ok_CONS:
   !x xs. handle_ok (x::xs) <=> handle_ok [x] /\ handle_ok xs
Proof
  Cases_on `xs` \\ fs [handle_ok_def]
QED

Theorem handle_ok_EVERY:
   !xs. handle_ok xs <=> EVERY (\x. handle_ok [x]) xs
Proof
  Induct \\ fs [handle_ok_def] \\ simp [Once handle_ok_CONS] \\ fs []
QED

Theorem LetLet_code_labels[simp]:
   get_code_labels (LetLet x y z) = get_code_labels z
Proof
  rw[bvl_handleTheory.LetLet_def]
  \\ rw[bvl_handleTheory.SmartLet_def, MAP_MAP_o, o_DEF, MAP_GENLIST]
  \\ rw[Once EXTENSION, MEM_FILTER, MEM_MAP, MEM_GENLIST, PULL_EXISTS, PULL_FORALL]
  \\ rw[EQ_IMP_THM]
  \\ rpt(pop_assum mp_tac)
  \\ TOP_CASE_TAC \\ fs[]
  \\ EVAL_TAC
QED

Theorem compile_code_labels:
   ∀a b c. BIGUNION (set (MAP get_code_labels (FST (bvl_handle$compile a b c)))) ⊆
           BIGUNION (set (MAP get_code_labels c))
Proof
  recInduct bvl_handleTheory.compile_ind
  \\ rw[bvl_handleTheory.compile_def]
  \\ rpt (pairarg_tac \\ fs[])
  \\ imp_res_tac bvl_handleTheory.compile_sing
  \\ rveq \\ fs[NULL_EQ] \\ rw[bvl_handleTheory.OptionalLetLet_def]
  \\ fs[]
  \\ fsrw_tac[DNF_ss][SUBSET_DEF]
  \\ EVAL_TAC
QED

Theorem compile_exp_code_labels:
   ∀a b c. get_code_labels (compile_exp a b c) ⊆ get_code_labels c
Proof
  rw[bvl_handleTheory.compile_exp_def]
  \\ Cases_on`bvl_handle$compile a b [compile_exp c]`
  \\ PairCases_on`r`
  \\ imp_res_tac bvl_handleTheory.compile_sing \\ rveq \\ fs[]
  \\ pop_assum mp_tac
  \\ specl_args_of_then``bvl_handle$compile``compile_code_labels mp_tac
  \\ rw[] \\ fs[]
  \\ metis_tac[bvl_constProofTheory.compile_exp_code_labels, SUBSET_TRANS]
QED

Theorem compile_seqs_code_labels:
   !cut e acc.
     get_code_labels (compile_seqs cut e acc) SUBSET
     get_code_labels e UNION
     (case acc of NONE => {} | SOME r => get_code_labels r)
Proof
  ho_match_mp_tac bvl_handleTheory.compile_seqs_ind \\ rw []
  \\ rw [Once bvl_handleTheory.compile_seqs_def]
  \\ rpt (PURE_TOP_CASE_TAC \\ fs []) \\ rw []
  \\ fs [dest_Seq_thm] \\ rw []
  \\ metis_tac [compile_exp_code_labels, SUBSET_UNION, SUBSET_TRANS, UNION_SUBSET]
QED

val _ = export_theory();
