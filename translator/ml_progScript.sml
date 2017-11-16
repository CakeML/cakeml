open preamble
open astTheory libTheory semanticPrimitivesTheory bigStepTheory
     determTheory semanticPrimitivesPropsTheory bigStepPropsTheory bigClockTheory;
open mlstringTheory integerTheory;
open terminationTheory;
open namespaceTheory;

val _ = new_theory "ml_prog";

(* TODO: The translator might need a corresponding simplification for Longs too
  Also, the translator should probably use a custom compset rather than [compute]
  i.e. these automatic rewrites should be moved elsewhere
*)
val nsLookup_nsAppend_Short = Q.store_thm("nsLookup_nsAppend_Short[compute]",`
  (nsLookup (nsAppend e1 e2) (Short id) =
    case nsLookup e1 (Short id) of
      NONE =>
        nsLookup e2 (Short id)
    | SOME v => SOME v)`,
  every_case_tac>>
  Cases_on`nsLookup e2(Short id)`>>
  fs[namespacePropsTheory.nsLookup_nsAppend_some,namespacePropsTheory.nsLookup_nsAppend_none,id_to_mods_def]);

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

(* some theorems that can be used by EVAL to compute lookups *)
(*
val SND_ALOOKUP_def = Define `
  (SND_ALOOKUP (x,[]) q = NONE) /\
  (SND_ALOOKUP (x,(y,z)::xs) q = if q = y then SOME z else SND_ALOOKUP (x,xs) q)`;
*)

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

(*
val SND_ALOOKUP_EQ_ALOOKUP = Q.store_thm("SND_ALOOKUP_EQ_ALOOKUP",
  `!xs ys q. SND_ALOOKUP (xs,ys) q = ALOOKUP ys q`,
  Induct_on `ys` \\ fs [ALOOKUP_def,SND_ALOOKUP_def,FORALL_PROD] \\ rw []);

*)

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
    (*ALOOKUP empty_env.m q = NONE /\*)
    nsLookup empty_env.c q = NONE`,
  fs [empty_env_def] );

(*
val merge_env_simp = Q.store_thm("merge_env_simp[compute]",
  `(nsLookup (merge_env e1 e2).v (Short k) =
      case nsLookup e1.v (Short k) of SOME x => SOME x | NONE => nsLookup e2.v (Short k)) /\
    (*(ALOOKUP (merge_env e1 e2).m k =
      case ALOOKUP e1.m k of SOME x => SOME x | NONE => ALOOKUP e2.m k) /\*)
    (nsLookup (merge_env e1 e2).c (Short k) =
      case nsLookup e1.c (Short k) of SOME x => SOME x | NONE => nsLookup e2.c (Short k))`,
  fs [merge_env_def] >> every_case_tac >> fs[namespacePropsTheory.nsLookup_nsAppend_some] >>
  try(Cases_on`nsLookup e2.v (Short k)`)>>
  try(Cases_on`nsLookup e2.c (Short k)`)>>
  fs[namespacePropsTheory.nsLookup_nsAppend_none,namespacePropsTheory.nsLookup_nsAppend_some,namespaceTheory.id_to_mods_def])
*)

(*
val SND_ALOOKUP_INTRO = Q.store_thm("SND_ALOOKUP_INTRO[compute]",
  `lookup_alist_mod_env (Short v) x = SND_ALOOKUP x v`,
  Cases_on `x` \\ fs [lookup_alist_mod_env_def,SND_ALOOKUP_EQ_ALOOKUP]);

*)

(* some shorthands that are allowed to EVAL are below *)

val write_rec_def = Define `
  write_rec funs env1 env =
    FOLDR (\f env. write (FST f) (Recclosure env1 funs (FST f)) env) env funs`;

val write_tds_def = Define `
  write_tds mn tds env =
    FOLDR (\(n,d) env. write_cons n d env) env
       (REVERSE
          (FLAT
             (MAP
                (λ(tvs,tn,condefs).
                   MAP
                     (λ(conN,ts). (conN,LENGTH ts,TypeId (mk_id mn tn)))
                     condefs) tds)))`;

val write_exn_def = Define `
  write_exn mn n l env =
    write_cons n (LENGTH l,TypeExn (mk_id mn n)) env`;

val write_rec_thm = Q.store_thm("write_rec_thm",
  `write_rec funs env1 env =
    env with v := build_rec_env funs env1 env.v`,
  fs [write_rec_def,build_rec_env_def]
  \\ qspec_tac (`Recclosure env1 funs`,`hh`)
  \\ qspec_tac (`env`,`env`)
  \\ Induct_on `funs` \\ fs [FORALL_PROD]
  \\ fs [write_def]);

val write_tds_thm = Q.store_thm("write_tds_thm",
  `write_tds mn tds env =
    env with c := nsAppend (build_tdefs mn tds) env.c`,
  fs [write_tds_def,build_tdefs_def,REVERSE_FLAT] \\
  qid_spec_tac`env` \\ Induct_on`tds` \\ rw[]
  >-
    fs[sem_env_component_equality]
  >>
  fs[FOLDR_APPEND]>>
  FULL_SIMP_TAC std_ss [GSYM namespacePropsTheory.nsAppend_alist_to_ns]>>
  PairCases_on`h`>>fs[]>>
  pop_assum kall_tac>>
  qid_spec_tac`env`>>
  Induct_on`h2`>>fs[FOLDR_REVERSE]>>rw[] >>
  pairarg_tac>>fs[REVERSE_FLAT]>>
  FULL_SIMP_TAC std_ss [GSYM namespacePropsTheory.nsAppend_alist_to_ns]>>
  fs[write_cons_def]>>
  FULL_SIMP_TAC std_ss [GSYM namespacePropsTheory.nsAppend_assoc]>>
  FULL_SIMP_TAC std_ss [namespacePropsTheory.nsAppend_nsBind,namespacePropsTheory.nsAppend_nsEmpty]);

val write_exn_thm = Q.store_thm("write_exn_thm",
  `write_exn mn n l env =
    env with c :=
    nsAppend (nsSing n (LENGTH l, TypeExn (mk_id mn n))) env.c`,
  fs [write_exn_def,write_cons_def]);

(* --- declarations --- *)

(* TODO: Not clear if the empty bind check is actually needed *)
val Decls_def = Define `
  Decls mn env s1 ds env2 s2 =
    (evaluate_decs F mn env s1 ds (s2,Rval env2))`;
    (*To faithfully reflect the original, this also needs to say that the modules are empty:
    ?bnd. env2.v = Bind bnd [])`;*)
(*
?new_tds res_env.
      evaluate_decs F mn env s1 ds (s2,new_tds, Rval res_env) /\
      env2.m = [] ∧
      env2.c = ([],new_tds) ∧
      env2.v = res_env`;*)

val Decls_Dtype = Q.store_thm("Decls_Dtype",
  `!mn env s tds env2 s2 locs.
      Decls mn env s [Dtype locs tds] env2 s2 <=>
      check_dup_ctors tds /\
      DISJOINT (type_defs_to_new_tdecs mn tds) s.defined_types /\
      ALL_DISTINCT (MAP (\(tvs,tn,ctors). tn) tds) /\
      s2 = s with defined_types := type_defs_to_new_tdecs mn tds UNION s.defined_types /\
      env2 = <| v := nsEmpty; c := (build_tdefs mn tds) |>`,
  SIMP_TAC std_ss [Decls_def]
  \\ ONCE_REWRITE_TAC [evaluate_decs_cases] \\ SIMP_TAC (srw_ss()) []
  \\ ONCE_REWRITE_TAC [evaluate_decs_cases] \\ SIMP_TAC (srw_ss()) []
  \\ fs [PULL_EXISTS]
  \\ SIMP_TAC (srw_ss()) [evaluate_dec_cases, combine_dec_result_def]
  \\ srw_tac[QUANT_INST_ss[record_default_qp]][]
  \\ rw[sem_env_component_equality,empty_env_def,nsEmpty_def] \\ eq_tac \\ rw[] \\ fs[]);

(* delays the cons *)
val Decls_Dexn = Q.store_thm("Decls_Dexn",
  `!mn env s n l env2 s2 locs.
      Decls mn env s [Dexn locs n l] env2 s2 <=>
      TypeExn (mk_id mn n) NOTIN s.defined_types /\
      s2 = s with defined_types := {TypeExn (mk_id mn n)} UNION s.defined_types /\
      env2 = write_exn mn n l empty_env`,
  SIMP_TAC std_ss [Decls_def]
  \\ ONCE_REWRITE_TAC [evaluate_decs_cases] \\ SIMP_TAC (srw_ss()) []
  \\ ONCE_REWRITE_TAC [evaluate_decs_cases] \\ SIMP_TAC (srw_ss()) []
  \\ SIMP_TAC (srw_ss()) [evaluate_dec_cases, combine_dec_result_def]
  \\ srw_tac[QUANT_INST_ss[record_default_qp]][]
  \\ fs[PULL_EXISTS,write_exn_thm]
  \\ rw[] \\ eq_tac \\ rw[] \\ fs[empty_env_def,nsSing_def,nsBind_def,nsEmpty_def]);

val Decls_Dtabbrev = Q.store_thm("Decls_Dtabbrev",
  `!mn env s n l env2 s2 locs.
      Decls mn env s [Dtabbrev locs x y z] env2 s2 <=>
      s2 = s ∧ env2 = empty_env`,
  fs [Decls_def]
  \\ ONCE_REWRITE_TAC [evaluate_decs_cases] \\ SIMP_TAC (srw_ss()) []
  \\ ONCE_REWRITE_TAC [evaluate_decs_cases] \\ SIMP_TAC (srw_ss()) []
  \\ SIMP_TAC (srw_ss()) [evaluate_dec_cases, combine_dec_result_def]
  \\ rw [] \\ eq_tac \\ fs [empty_env_def,nsEmpty_def,nsAppend_def]);

(* Delays the write *)
val Decls_Dlet = Q.store_thm("Decls_Dlet",
  `!mn env s1 v e s2 env2 locs.
      Decls mn env s1 [Dlet locs (Pvar v) e] env2 s2 <=>
      ?x. evaluate F env s1 e (s2,Rval x) /\
          (env2 = write v x empty_env)`,
  SIMP_TAC std_ss [Decls_def]
  \\ ONCE_REWRITE_TAC [evaluate_decs_cases] \\ SIMP_TAC (srw_ss()) []
  \\ ONCE_REWRITE_TAC [evaluate_decs_cases] \\ SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC (srw_ss()) [pat_bindings_def,ALL_DISTINCT,MEM,
       pmatch_def, evaluate_dec_cases,combine_dec_result_def]
  \\ FULL_SIMP_TAC std_ss [PULL_EXISTS] \\ REPEAT STRIP_TAC
  \\ srw_tac[QUANT_INST_ss[record_default_qp]][]
  \\ simp[empty_env_def]
  \\ fs[write_def,nsEmpty_def,nsBind_def] \\ eq_tac \\ rw[] \\ fs[]);

val FOLDR_LEMMA = Q.prove(
  `!xs ys. FOLDR (\(x1,x2,x3) x4. (x1, f x1 x2 x3) :: x4) [] xs ++ ys =
            FOLDR (\(x1,x2,x3) x4. (x1, f x1 x2 x3) :: x4) ys xs`,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [FORALL_PROD]);

(* Delays the write in build_rec_env *)
val Decls_Dletrec = Q.store_thm("Decls_Dletrec",
  `!mn env s1 funs s2 env2 locs.
      Decls mn env s1 [Dletrec locs funs] env2 s2 <=>
      (s2 = s1) /\
      ALL_DISTINCT (MAP (\(x,y,z). x) funs) /\
      (env2 = write_rec funs env empty_env)`,
  SIMP_TAC std_ss [Decls_def]
  \\ ONCE_REWRITE_TAC [evaluate_decs_cases] \\ SIMP_TAC (srw_ss()) []
  \\ ONCE_REWRITE_TAC [evaluate_decs_cases] \\ SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC (srw_ss()) [pat_bindings_def,ALL_DISTINCT,MEM,
       pmatch_def,evaluate_dec_cases,
       combine_dec_result_def,PULL_EXISTS] \\ REPEAT STRIP_TAC
  \\ fs[write_def,write_rec_thm,empty_env_def,build_rec_env_def]
  \\ rw[] \\ eq_tac \\ rw[] \\ fs[]
  \\ pop_assum kall_tac
  \\ qho_match_abbrev_tac`∃bnd. FOLDR (λ(f,x,e) env'. nsBind f (foo f) env')  _ _ = Bind bnd _`
  \\ pop_assum kall_tac
  \\ Induct_on`funs`\\ rw[nsEmpty_def,nsBind_def]
  \\ pairarg_tac \\ fs[nsBind_def]);

val Decls_NIL = Q.store_thm("Decls_NIL",
  `!mn env s n l env2 s2.
      Decls mn env s [] env2 s2 <=>
      s2 = s ∧ env2 = empty_env`,
  fs [Decls_def]
  \\ ONCE_REWRITE_TAC [evaluate_decs_cases] \\ SIMP_TAC (srw_ss()) []
  \\ ONCE_REWRITE_TAC [evaluate_decs_cases] \\ SIMP_TAC (srw_ss()) []
  \\ SIMP_TAC (srw_ss()) [evaluate_dec_cases, combine_dec_result_def]
  \\ rw [] \\ eq_tac
  \\ fs [empty_env_def,nsEmpty_def]);

val Decls_CONS = Q.store_thm("Decls_CONS",
  `!s1 s3 mn env1 d ds1 ds2 env3.
      Decls mn env1 s1 (d::ds2) env3 s3 =
      ?envA envB s2.
         Decls mn env1 s1 [d] envA s2 /\
         Decls mn (merge_env envA env1) s2 ds2 envB s3 /\
         env3 = merge_env envB envA`,
  rw[Decls_def,PULL_EXISTS]
  \\ rw[Once evaluate_decs_cases,PULL_EXISTS]
  \\ rw[Once evaluate_decs_cases,SimpRHS,PULL_EXISTS]
  \\ reverse (rw[EQ_IMP_THM])
  THEN1
   (ntac 2 (qhdtm_x_assum`evaluate_decs`mp_tac)
    \\ rw[Once evaluate_decs_cases] >> fs[]
    \\ fs [merge_env_def] \\ rfs []
    \\ fs [empty_env_def,merge_env_def,extend_dec_env_def]
    \\ fs [combine_dec_result_def]
    \\ ONCE_REWRITE_TAC[CONJ_COMM]
    \\ fs[nsAppend_def]
    \\ qexists_tac`s2` \\ qexists_tac`new_env` \\ qexists_tac`Rval envB` \\ fs[]
    \\ rw[] \\ EVAL_TAC)
  \\ rw[Once evaluate_decs_cases,PULL_EXISTS,combine_dec_result_def]
  \\ asm_exists_tac \\ fs[]
  \\ CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``evaluate_decs`` o fst o strip_comb)))
  \\ Cases_on`r`>>fs[combine_dec_result_def]
  \\ qexists_tac`a`
  \\ fs [empty_env_def,merge_env_def,extend_dec_env_def]
  \\ rw [sem_env_component_equality]
  \\ Cases_on`new_env.v`
  \\ Cases_on`a.v` \\ fs[nsAppend_def]);

val merge_env_empty_env = Q.store_thm("merge_env_empty_env",
  `merge_env env empty_env = env /\
    merge_env empty_env env = env`,
  rw [merge_env_def,empty_env_def]);

val merge_env_assoc = Q.store_thm("merge_env_assoc",
  `merge_env env1 (merge_env env2 env3) = merge_env (merge_env env1 env2) env3`,
  fs [merge_env_def]);

val Decls_APPEND = Q.store_thm("Decls_APPEND",
  `!s1 s3 mn env1 ds1 ds2 env3.
      Decls mn env1 s1 (ds1 ++ ds2) env3 s3 =
      ?envA envB s2.
         Decls mn env1 s1 ds1 envA s2 /\
         Decls mn (merge_env envA env1) s2 ds2 envB s3 /\
         env3 = merge_env envB envA`,
  Induct_on `ds1` \\ fs [APPEND,Decls_NIL,merge_env_empty_env]
  \\ once_rewrite_tac [Decls_CONS]
  \\ fs [PULL_EXISTS,merge_env_assoc] \\ metis_tac []);

val Decls_SNOC = Q.store_thm("Decls_SNOC",
  `!s1 s3 mn env1 ds1 d env3.
      Decls mn env1 s1 (SNOC d ds1) env3 s3 =
      ?envA envB s2.
         Decls mn env1 s1 ds1 envA s2 /\
         Decls mn (merge_env envA env1) s2 [d] envB s3 /\
         env3 = merge_env envB envA`,
  METIS_TAC [SNOC_APPEND, Decls_APPEND]);

(* --- programs --- *)

val Prog_def = Define `
  Prog env1 s1 prog env2 s2 <=>
    evaluate_prog F env1 s1 prog
      (s2,Rval env2)`

val Prog_NIL = Q.store_thm("Prog_NIL",
  `!s1 s3 env1 ds1 ds2 env3.
      Prog env1 s1 [] env3 s3 <=> (env3 = empty_env) /\ (s3 = s1)`,
  fs [Prog_def,Once evaluate_prog_cases] \\ EVAL_TAC \\ rw [empty_env_def,nsEmpty_def] \\
  metis_tac[]);

val Prog_CONS = Q.store_thm("Prog_CONS",
  `!s1 s3 env1 d ds2 env3.
      Prog env1 s1 (d::ds2) env3 s3 =
      ?envA envB s2.
         Prog env1 s1 [d] envA s2 /\
         Prog (merge_env envA env1) s2 ds2 envB s3 /\
         env3 = merge_env envB envA`,
  fs [Prog_def]
  \\ simp [Once evaluate_prog_cases]
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ simp [Once evaluate_prog_cases]
  \\ simp [Once evaluate_prog_cases]
  \\ fs [PULL_EXISTS,combine_dec_result_def]
  \\ rw [] \\ eq_tac \\ rw []
  \\ fs [merge_env_def,EXISTS_PROD]
  THEN1
   (once_rewrite_tac [CONJ_ASSOC]
   \\ once_rewrite_tac [CONJ_SYM]
   \\ fs [extend_dec_env_def] \\ asm_exists_tac
   \\ fs[])
  \\ asm_exists_tac \\ fs[]
  \\ Cases_on `r` \\ fs [extend_dec_env_def]
  \\ asm_exists_tac \\ fs[]);

val Prog_APPEND = Q.store_thm("Prog_APPEND",
  `!s1 s3 env1 ds1 ds2 env3.
      Prog env1 s1 (ds1 ++ ds2) env3 s3 =
      ?envA envB s2.
         Prog env1 s1 ds1 envA s2 /\
         Prog (merge_env envA env1) s2 ds2 envB s3 /\
         env3 = merge_env envB envA`,
  Induct_on `ds1` \\ fs [Prog_NIL] \\ once_rewrite_tac [Prog_CONS]
  \\ fs [] \\ metis_tac [merge_env_assoc,merge_env_empty_env]);

val Prog_Tdec = Q.store_thm("Prog_Tdec",
  `Prog env1 s1 [Tdec d] env2 s2 <=>
    Decls [] env1 s1 [d] env2 s2`,
  fs [Prog_def,Decls_def,Once evaluate_prog_cases]
  \\ fs [Prog_def,Decls_def,Once evaluate_prog_cases]
  \\ fs [combine_dec_result_def,Once evaluate_top_cases,PULL_EXISTS]
  \\ fs [Once evaluate_decs_cases,PULL_EXISTS,combine_dec_result_def]
  \\ fs [Once evaluate_decs_cases,PULL_EXISTS,combine_dec_result_def,extend_dec_env_def]);

val Prog_Tmod = Q.store_thm("Prog_Tmod",
  `Prog env1 s1 [Tmod mn specs ds] env2 s2 <=>
    [mn] ∉ s1.defined_mods /\ no_dup_types ds /\
    ?s env.
      Decls [mn] env1 s1 ds env s /\
      s2 = s with defined_mods := {[mn]} ∪ s.defined_mods /\
      env2 = write_mod mn env empty_env`,
  fs [Prog_def,Decls_def,Once evaluate_prog_cases,PULL_EXISTS,combine_dec_result_def,Once evaluate_top_cases]
  \\ fs [Prog_def,Decls_def,Once evaluate_prog_cases,PULL_EXISTS,Once evaluate_top_cases]
  \\ fs [write_mod_def,empty_env_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs []
  \\ TRY (asm_exists_tac \\ fs [])
  \\ qexists_tac `s` \\ fs[]
  \\ qexists_tac`env` \\ fs[]);

(* The translator and CF tools use the following definition of ML_code
   to build verified ML programs. *)

val ML_code_def = Define `
  (ML_code env1 s1 prog NONE env2 s2 <=>
     Prog env1 s1 prog env2 s2) /\
  (ML_code env1 s1 prog (SOME (mn,ds,env)) env2 s2 <=>
     ?s.
       [mn] ∉ s.defined_mods /\ no_dup_types ds /\
       Prog env1 s1 prog env s /\
       Decls [mn] (merge_env env env1) s ds env2 s2)`

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

end

val ML_code_NIL = Q.store_thm("ML_code_NIL",
  `ML_code init_env (init_state ffi) [] NONE empty_env (init_state ffi)`,
  fs [ML_code_def,Prog_NIL]);

val nsLookup_init_env = save_thm("nsLookup_init_env[compute]",
  init_env_def
  |> concl
  |> find_terms (can (match_term ``(s:string,_)``))
  |> map (fn tm => EVAL ``nsLookup init_env.c (Short ^(rand(rator tm)))``)
  |> LIST_CONJ);

(* opening and closing of modules *)

val ML_code_new_module = Q.store_thm("ML_code_new_module",
  `ML_code env1 s1 prog NONE env2 s2 ==>
    !mn. [mn] ∉ s2.defined_mods ==>
         ML_code env1 s1 prog (SOME (mn,[],env2)) empty_env s2`,
  fs [ML_code_def] \\ rw [Decls_NIL] \\ EVAL_TAC);

val ML_code_close_module = Q.store_thm("ML_code_close_module",
  `ML_code env1 s1 prog (SOME (mn,ds,env)) env2 s2 ==>
    !sigs.
      ML_code env1 s1 (SNOC (Tmod mn sigs ds) prog) NONE
        (write_mod mn env2 env)
        (s2 with defined_mods := [mn] INSERT s2.defined_mods)`,
  fs [ML_code_def] \\ rw [] \\ fs [SNOC_APPEND,Prog_APPEND]
  \\ asm_exists_tac \\ fs [Prog_Tmod,PULL_EXISTS]
  \\ asm_exists_tac \\ fs []
  \\ conj_tac
  THEN1 (AP_THM_TAC \\ rpt AP_TERM_TAC \\ fs [EXTENSION])
  \\ fs [write_mod_def,merge_env_def,empty_env_def]);

(* appending a Dtype *)

val ML_code_NONE_Dtype = Q.store_thm("ML_code_NONE_Dtype",
  `ML_code env1 s1 prog NONE env2 s2 ==>
    !tds locs.
      check_dup_ctors tds ∧
      DISJOINT (type_defs_to_new_tdecs [] tds) s2.defined_types ∧
      ALL_DISTINCT (MAP (λ(tvs,tn,ctors). tn) tds) ==>
      ML_code env1 s1 (SNOC (Tdec (Dtype locs tds)) prog) NONE
        (write_tds [] tds env2)
        (s2 with defined_types :=
                   type_defs_to_new_tdecs [] tds ∪ s2.defined_types)`,
  fs [ML_code_def,SNOC_APPEND,Prog_APPEND,Prog_Tdec,Decls_Dtype]
  \\ rw [] \\ asm_exists_tac \\ fs [] \\ Cases_on `env2.c`
  \\ fs [write_tds_thm,merge_env_def,empty_env_def,sem_env_component_equality]);

val ML_code_SOME_Dtype = Q.store_thm("ML_code_SOME_Dtype",
  `ML_code env1 s1 prog (SOME (mn,ds,env)) env2 s2 ==>
    !tds locs.
      check_dup_ctors tds ∧ no_dup_types (SNOC (Dtype locs tds) ds) /\
      DISJOINT (type_defs_to_new_tdecs [mn] tds) s2.defined_types ∧
      ALL_DISTINCT (MAP (λ(tvs,tn,ctors). tn) tds) ==>
      ML_code env1 s1 prog (SOME (mn,SNOC (Dtype locs tds) ds,env))
        (write_tds [mn] tds env2)
        (s2 with defined_types :=
                   type_defs_to_new_tdecs [mn] tds ∪ s2.defined_types)`,
  fs [ML_code_def,SNOC_APPEND,Prog_APPEND,Prog_Tdec,Decls_Dtype,Decls_SNOC]
  \\ rw [] \\ asm_exists_tac \\ fs [] \\ rw [] \\ asm_exists_tac
  \\ fs [write_tds_thm,merge_env_def,empty_env_def,sem_env_component_equality]);

(* appending a Dexn *)

val ML_code_NONE_Dexn = Q.store_thm("ML_code_NONE_Dexn",
  `ML_code env1 s1 prog NONE env2 s2 ==>
    !n l locs.
      TypeExn (mk_id [] n) ∉ s2.defined_types ==>
      ML_code env1 s1 (SNOC (Tdec (Dexn locs n l)) prog) NONE
        (write_exn [] n l env2)
        (s2 with defined_types := {TypeExn (mk_id [] n)} ∪ s2.defined_types)`,
  fs [ML_code_def,SNOC_APPEND,Prog_APPEND,Prog_Tdec,Decls_Dexn]
  \\ rw [] \\ asm_exists_tac \\ fs [] \\ Cases_on `env2.c`
  \\ fs [write_exn_thm,merge_env_def,empty_env_def,sem_env_component_equality]);

val ML_code_SOME_Dexn = Q.store_thm("ML_code_SOME_Dexn",
  `ML_code env1 s1 prog (SOME (mn,ds,env)) env2 s2 ==>
    !n l locs.
      TypeExn (mk_id [mn] n) ∉ s2.defined_types ==>
      ML_code env1 s1 prog (SOME (mn,SNOC (Dexn locs n l) ds,env))
        (write_exn [mn] n l env2)
        (s2 with defined_types :=
                   {TypeExn (mk_id [mn] n)} ∪ s2.defined_types)`,
  fs [ML_code_def,SNOC_APPEND,Decls_APPEND,Prog_Tdec,Decls_Dexn]
  \\ rw [] \\ asm_exists_tac \\ fs []
  \\ fs [no_dup_types_def,  decs_to_types_def]
  \\ asm_exists_tac \\ fs [] \\ Cases_on `env2.c`
  \\ fs [write_exn_thm,merge_env_def,empty_env_def,sem_env_component_equality]);

(* appending a Dtabbrev *)

val ML_code_NONE_Dtabbrev = Q.store_thm("ML_code_NONE_Dtabbrev",
  `ML_code env1 s1 prog NONE env2 s2 ==>
    !x y z locs.
      ML_code env1 s1 (SNOC (Tdec (Dtabbrev locs x y z)) prog) NONE env2 s2`,
  fs [ML_code_def,SNOC_APPEND,Prog_APPEND,Prog_Tdec,Decls_Dtabbrev,
      merge_env_empty_env]);

val ML_code_SOME_Dtabbrev = Q.store_thm("ML_code_SOME_Dtabbrev",
  `ML_code env1 s1 prog (SOME (mn,ds,env)) env2 s2 ==>
    !x y z locs.
      ML_code env1 s1 prog (SOME (mn,SNOC (Dtabbrev locs x y z) ds,env)) env2 s2`,
  fs [ML_code_def,SNOC_APPEND,Decls_APPEND,Prog_Tdec,Decls_Dtabbrev]
  \\ rw [] \\ asm_exists_tac \\ fs [no_dup_types_def,  decs_to_types_def]
  \\ asm_exists_tac \\ fs [merge_env_empty_env]);

(* appending a Letrec *)

val build_rec_env_APPEND = Q.prove(
  `nsAppend (build_rec_env funs cl_env nsEmpty) add_to_env =
    build_rec_env funs cl_env add_to_env`,
  fs [build_rec_env_def] \\ qspec_tac (`Recclosure cl_env funs`,`xxx`)
  \\ qspec_tac (`add_to_env`,`xs`)
  \\ Induct_on `funs` \\ fs [FORALL_PROD]);

val ML_code_NONE_Dletrec = Q.store_thm("ML_code_NONE_Dletrec",
  `ML_code env1 s1 prog NONE env2 s2 ==>
    !fns locs.
      ALL_DISTINCT (MAP (λ(x,y,z). x) fns) ==>
      ML_code env1 s1 (SNOC (Tdec (Dletrec locs fns)) prog) NONE
        (write_rec fns (merge_env env2 env1) env2) s2`,
  fs [ML_code_def,SNOC_APPEND,Prog_APPEND,Prog_Tdec,Decls_Dletrec]
  \\ rw [] \\ asm_exists_tac \\ fs []
  \\ fs [merge_env_def,write_rec_thm,empty_env_def,sem_env_component_equality]
  \\ fs [build_rec_env_APPEND]);

val ML_code_SOME_Dletrec = Q.store_thm("ML_code_SOME_Dletrec",
  `ML_code env1 s1 prog (SOME (mn,ds,env)) env2 s2 ==>
    !fns locs.
      ALL_DISTINCT (MAP (λ(x,y,z). x) fns) ==>
      ML_code env1 s1 prog (SOME (mn,SNOC (Dletrec locs fns) ds,env))
        (write_rec fns (merge_env env2 (merge_env env env1)) env2) s2`,
  fs [ML_code_def,SNOC_APPEND,Prog_APPEND,Prog_Tdec,Decls_Dletrec,Decls_SNOC]
  \\ rw [] \\ asm_exists_tac \\ fs []
  \\ fs [no_dup_types_def,  decs_to_types_def]
  \\ asm_exists_tac \\ fs []
  \\ fs [merge_env_def,write_rec_thm,empty_env_def,sem_env_component_equality]
  \\ fs [build_rec_env_APPEND]);

(* appending a Let *)

val ML_code_NONE_Dlet_var = Q.store_thm("ML_code_NONE_Dlet_var",
  `ML_code env1 s1 prog NONE env2 s2 ==>
    !e x s3.
      evaluate F (merge_env env2 env1) s2 e (s3,Rval x) ==>
      !n locs.
        ML_code env1 s1 (SNOC (Tdec (Dlet locs (Pvar n) e)) prog)
          NONE (write n x env2) s3`,
  fs [ML_code_def,SNOC_APPEND,Prog_APPEND,Prog_Tdec,Decls_Dlet]
  \\ rw [] \\ asm_exists_tac \\ fs [PULL_EXISTS]
  \\ rw [] \\ asm_exists_tac \\ fs []
  \\ fs [write_def,merge_env_def,empty_env_def,sem_env_component_equality]);

val ML_code_SOME_Dlet_var = Q.store_thm("ML_code_SOME_Dlet_var",
  `ML_code env1 s1 prog (SOME (mn,ds,env)) env2 s2 ==>
    !e x s3.
      evaluate F (merge_env env2 (merge_env env env1)) s2 e (s3,Rval x) ==>
      !n locs.
        ML_code env1 s1 prog (SOME (mn,SNOC (Dlet locs (Pvar n) e) ds,env))
          (write n x env2) s3`,
  fs [ML_code_def,SNOC_APPEND,Prog_APPEND,Prog_Tdec,Decls_Dlet,Decls_SNOC]
  \\ rw [] \\ asm_exists_tac \\ fs [PULL_EXISTS]
  \\ fs [no_dup_types_def,  decs_to_types_def]
  \\ rw [] \\ asm_exists_tac \\ fs []
  \\ rw [] \\ asm_exists_tac \\ fs []
  \\ fs [write_def,merge_env_def,empty_env_def,sem_env_component_equality]);

val ML_code_NONE_Dlet_Fun = Q.store_thm("ML_code_NONE_Dlet_Fun",
  `ML_code env1 s1 prog NONE env2 s2 ==>
    !n v e locs.
      ML_code env1 s1 (SNOC (Tdec (Dlet locs (Pvar n) (Fun v e))) prog)
        NONE (write n (Closure (merge_env env2 env1) v e) env2) s2`,
  rw [] \\ match_mp_tac (ML_code_NONE_Dlet_var |> MP_CANON) \\ fs []
  \\ fs [Once evaluate_cases]);

val ML_code_SOME_Dlet_Fun = Q.store_thm("ML_code_SOME_Dlet_Fun",
  `ML_code env1 s1 prog (SOME (mn,ds,env)) env2 s2 ==>
    !n v e locs.
      ML_code env1 s1 prog (SOME (mn,SNOC (Dlet locs (Pvar n) (Fun v e)) ds,env))
        (write n (Closure (merge_env env2 (merge_env env env1)) v e) env2) s2`,
  rw [] \\ match_mp_tac (ML_code_SOME_Dlet_var |> MP_CANON) \\ fs []
  \\ fs [Once evaluate_cases]);

(* lookup function definitions *)

val lookup_var_def = Define `
  lookup_var name (env:v sem_env) = nsLookup env.v (Short name)`;

val lookup_cons_def = Define `
  lookup_cons name (env:v sem_env) = nsLookup env.c (Short name)`;

(* theorems about lookup functions *)

val mod_defined_def = zDefine `
  mod_defined env n =
    ∃p1 p2 e3.
      p1 ≠ [] ∧ id_to_mods n = p1 ++ p2 ∧
      nsLookupMod env p1 = SOME e3`;

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
  EVAL_TAC \\ rw [mod_defined_def]
  \\ Cases_on`p1`>>fs[nsLookupMod_def,empty_env_def]);

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

val nsLookup_eq_format = Q.store_thm("nsLookup_eq_format",
  `!env:v sem_env.
     (nsLookup env.v (Short n) = nsLookup env.v (Short n)) /\
     (nsLookup env.c (Short n) = nsLookup env.c (Short n)) /\
     (nsLookup env.v (Long n1 n2) = nsLookup env.v (Long n1 n2)) /\
     (nsLookup env.c (Long n1 n2) = nsLookup env.c (Long n1 n2)) /\
     (mod_defined env.v (Long n1 n2) = mod_defined env.v (Long n1 n2)) /\
     (mod_defined env.c (Long n1 n2) = mod_defined env.c (Long n1 n2))`,
  rewrite_tac []);

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
    (*(lookup_mod m (write_mod mn e1 env) =
     if m = mn then SOME e1.v else lookup_mod m env) /\*)
    (lookup_cons name (write_mod mn e1 env) = lookup_cons name env)`,
  fs [lookup_var_def,write_mod_def,
      lookup_cons_def] \\ rw [] \\ Cases_on`name` \\ fs[namespacePropsTheory.nsLookup_nsLift_append]);
 (*fs [lookup_var_id_def,lookup_var_def,write_mod_def,
      lookup_cons_thm,lookup_mod_def] \\ rw []
  \\ Cases_on `env.c` \\ fs [] \\ fs [lookup_alist_mod_env_def]);*)

val lookup_var_write_cons = Q.store_thm("lookup_var_write_cons",
  `(lookup_var v (write_cons n d env) = lookup_var v env) /\
   (lookup_cons name (write_cons n d env) =
     if name = n then SOME d else lookup_cons name env) /\
   (nsLookup (write_cons n d env).v x = nsLookup env.v x)`,
  fs [lookup_var_def,write_cons_def,lookup_cons_def] \\ rw []);

val lookup_var_empty_env = Q.store_thm("lookup_var_empty_env",
  `(lookup_var v empty_env = NONE) /\
    (nsLookup empty_env.v (Short k) = NONE) /\
    (nsLookup empty_env.v (Long mn m) = NONE) /\
    (lookup_cons name empty_env = NONE)`,
  fs[lookup_var_def,empty_env_def,lookup_cons_def]);
  (*fs [lookup_var_id_def,lookup_var_def,empty_env_def,lookup_cons_thm] \\ rw []
  \\ fs [lookup_alist_mod_env_def]);*)

val lookup_var_merge_env = Q.store_thm("lookup_var_merge_env",
  `(lookup_var v1 (merge_env e1 e2) =
       case lookup_var v1 e1 of
       | NONE => lookup_var v1 e2
       | res => res) /\
    (lookup_cons v1 (merge_env e1 e2) =
       case lookup_cons v1 e1 of
       | NONE => lookup_cons v1 e2
       | res => res)
    (*(lookup_mod v1 (merge_env e1 e2) =
       case lookup_mod v1 e1 of
       | NONE => lookup_mod v1 e2
       | res => res)*)`,
  fs [lookup_var_def,lookup_cons_def,merge_env_def] \\ rw[] \\ every_case_tac \\
  fs[namespacePropsTheory.nsLookup_nsAppend_some]
  >-
    (Cases_on`nsLookup e2.v (Short v1)`>>
    fs[namespacePropsTheory.nsLookup_nsAppend_none,namespacePropsTheory.nsLookup_nsAppend_some,namespaceTheory.id_to_mods_def])
  >>
    (Cases_on`nsLookup e2.c (Short v1)`>>
    fs[namespacePropsTheory.nsLookup_nsAppend_none,namespacePropsTheory.nsLookup_nsAppend_some,namespaceTheory.id_to_mods_def]));

val _ = export_theory();
