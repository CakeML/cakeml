open preamble
open astTheory libTheory semanticPrimitivesTheory bigStepTheory
     determTheory evalPropsTheory bigClockTheory;
open mlstringTheory integerTheory;
open terminationTheory;

val _ = new_theory "ml_decls";


(* --- declarations --- *)

val Decls_def = Define `
  Decls mn env s1 ds env2 s2 =
    ?new_tds res_env.
      evaluate_decs F mn env s1 ds (s2,new_tds, Rval res_env) /\
      env2.m = env.m ∧
      env2.c = merge_alist_mod_env ([],new_tds) env.c ∧
      env2.v = res_env ++ env.v`;

val write_def = Define `
  write name v env = env with v := (name,v)::env.v`;

val write_rec_def = Define `
  write_rec funs env2 =
    env2 with v := build_rec_env funs env2 env2.v`;

val write_tds_def = Define `
  write_tds mn tds env =
    env with c := merge_alist_mod_env ([],build_tdefs mn tds) env.c`;

val write_exn_def = Define `
  write_exn mn n l env =
    env with c := merge_alist_mod_env
                    ([],[(n,LENGTH l,TypeExn (mk_id mn n))]) env.c`;

val Decls_Dtype = store_thm("Decls_Dtype",
  ``!mn env s tds env2 s2.
      Decls mn env s [Dtype tds] env2 s2 <=>
      check_dup_ctors tds /\
      DISJOINT (type_defs_to_new_tdecs mn tds) s.defined_types /\
      ALL_DISTINCT (MAP (\(tvs,tn,ctors). tn) tds) /\
      s2 = s with defined_types := type_defs_to_new_tdecs mn tds UNION s.defined_types /\
      (env2 = write_tds mn tds env)``,
  SIMP_TAC std_ss [Decls_def]
  \\ ONCE_REWRITE_TAC [evaluate_decs_cases] \\ SIMP_TAC (srw_ss()) []
  \\ ONCE_REWRITE_TAC [evaluate_decs_cases] \\ SIMP_TAC (srw_ss()) []
  \\ SIMP_TAC (srw_ss()) [evaluate_dec_cases, combine_dec_result_def]
  \\ srw_tac[QUANT_INST_ss[record_default_qp]][]
  \\ rw[write_tds_def,environment_component_equality]
  \\ METIS_TAC[]);

val Decls_Dexn = store_thm("Decls_Dexn",
  ``!mn env s n l env2 s2.
      Decls mn env s [Dexn n l] env2 s2 <=>
      TypeExn (mk_id mn n) NOTIN s.defined_types /\
      s2 = s with defined_types := {TypeExn (mk_id mn n)} UNION s.defined_types /\
      env2 = write_exn mn n l env``,
  SIMP_TAC std_ss [Decls_def]
  \\ ONCE_REWRITE_TAC [evaluate_decs_cases] \\ SIMP_TAC (srw_ss()) []
  \\ ONCE_REWRITE_TAC [evaluate_decs_cases] \\ SIMP_TAC (srw_ss()) []
  \\ SIMP_TAC (srw_ss()) [evaluate_dec_cases, combine_dec_result_def]
  \\ srw_tac[QUANT_INST_ss[record_default_qp]][]
  \\ fs[PULL_EXISTS,write_exn_def,write_tds_def,environment_component_equality]
  \\ fs [AC CONJ_COMM CONJ_ASSOC,APPEND]);

val Decls_Dlet = store_thm("Decls_Dlet",
  ``!mn env s1 v e s2 env2.
      Decls mn env s1 [Dlet (Pvar v) e] env2 s2 <=>
      ?x. s2.defined_types = s1.defined_types /\
          evaluate F env s1 e (s2,Rval x) /\
          (env2 = write v x env)``,
  SIMP_TAC std_ss [Decls_def]
  \\ ONCE_REWRITE_TAC [evaluate_decs_cases] \\ SIMP_TAC (srw_ss()) []
  \\ ONCE_REWRITE_TAC [evaluate_decs_cases] \\ SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC (srw_ss()) [pat_bindings_def,ALL_DISTINCT,MEM,
       pmatch_def, evaluate_dec_cases,
       combine_dec_result_def]
  \\ FULL_SIMP_TAC std_ss [PULL_EXISTS] \\ REPEAT STRIP_TAC
  \\ srw_tac[QUANT_INST_ss[record_default_qp]][]
  \\ simp[environment_component_equality]
  \\ FULL_SIMP_TAC std_ss [write_def,merge_alist_mod_env_def,APPEND, finite_mapTheory.FUNION_FEMPTY_1,
                           finite_mapTheory.FUNION_FEMPTY_2]
  \\ simp[]
  \\ METIS_TAC [big_unclocked, pair_CASES, evaluate_no_new_types_mods,FST]);

val FOLDR_LEMMA = prove(
  ``!xs ys. FOLDR (\(x1,x2,x3) x4. (x1, f x1 x2 x3) :: x4) [] xs ++ ys =
            FOLDR (\(x1,x2,x3) x4. (x1, f x1 x2 x3) :: x4) ys xs``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [FORALL_PROD]);

val Decls_Dletrec = store_thm("Decls_Dletrec",
  ``!mn env s1 funs s2 env2.
      Decls mn env s1 [Dletrec funs] env2 s2 <=>
      (s2 = s1) /\
      ALL_DISTINCT (MAP (\(x,y,z). x) funs) /\
      (env2 = write_rec funs env)``,
  SIMP_TAC std_ss [Decls_def]
  \\ ONCE_REWRITE_TAC [evaluate_decs_cases] \\ SIMP_TAC (srw_ss()) []
  \\ ONCE_REWRITE_TAC [evaluate_decs_cases] \\ SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC (srw_ss()) [pat_bindings_def,ALL_DISTINCT,MEM,
       pmatch_def,evaluate_dec_cases,
       combine_dec_result_def,PULL_EXISTS] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [write_def,merge_alist_mod_env_def,
       APPEND,write_rec_def,APPEND,merge_alist_mod_env_empty,
       build_rec_env_def,FOLDR_LEMMA]
  \\ fs [environment_component_equality]
  \\ METIS_TAC []);

val Decls_NIL = store_thm("Decls_NIL",
  ``!s1 s3 mn env1 ds1 ds2 env3.
      Decls mn env1 s1 [] env3 s3 <=> (env3 = env1) /\ (s3 = s1)``,
  REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [APPEND,Decls_def,PULL_EXISTS]
  \\ SIMP_TAC std_ss [Once evaluate_decs_cases]
  \\ SIMP_TAC (srw_ss()) [merge_alist_mod_env_def]
  \\ METIS_TAC [environment_component_equality]);

val Decls_CONS = store_thm("Decls_CONS",
  ``!s1 s3 mn env1 ds1 ds2 env3.
      Decls mn env1 s1 (d::ds2) env3 s3 =
      ?env2 s2.
         Decls mn env1 s1 [d] env2 s2 /\
         Decls mn env2 s2 ds2 env3 s3``,
  rw[Decls_def,PULL_EXISTS] >>
  rw[Once evaluate_decs_cases,PULL_EXISTS] >>
  rw[Once evaluate_decs_cases,SimpRHS,PULL_EXISTS] >>
  rw[EQ_IMP_THM] >>
  ONCE_REWRITE_TAC[CONJ_COMM] >>
  first_assum(match_exists_tac o concl) >> simp[] >- (
    rw[Once evaluate_decs_cases,PULL_EXISTS,combine_dec_result_def] >>
    CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``evaluate_decs`` o fst o strip_comb))) >>
    Cases_on`r`>>fs[combine_dec_result_def] >>
    first_assum(match_exists_tac o concl) >>
    simp[extend_dec_env_def,merge_alist_mod_env_assoc] >>
    Cases_on`env1.c`>>simp[merge_alist_mod_env_def] ) >>
  ntac 2 (rator_x_assum`evaluate_decs`mp_tac) >>
  rw[Once evaluate_decs_cases] >> fs[] >>
  qpat_abbrev_tac`env2' = extend_dec_env X Y Z` >>
  `env2 = env2'` by (
    simp[environment_component_equality,Abbr`env2'`,extend_dec_env_def] >>
    fs[combine_dec_result_def] ) >>
  rw[Abbr`env2'`] >>
  first_assum(match_exists_tac o concl) >>
  fs[combine_dec_result_def,merge_alist_mod_env_assoc] >>
  Cases_on`env1.c`>>simp[merge_alist_mod_env_def]);

val Decls_APPEND = store_thm("Decls_APPEND",
  ``!s1 s3 mn env1 ds1 ds2 env3.
      Decls mn env1 s1 (ds1 ++ ds2) env3 s3 =
      ?env2 s2.
         Decls mn env1 s1 ds1 env2 s2 /\
         Decls mn env2 s2 ds2 env3 s3``,
  Induct_on `ds1` \\ FULL_SIMP_TAC std_ss [APPEND,Decls_NIL]
  \\ ONCE_REWRITE_TAC [Decls_CONS]
  \\ FULL_SIMP_TAC std_ss [PULL_EXISTS,AC CONJ_COMM CONJ_ASSOC]
  \\ METIS_TAC []);

val Decls_SNOC = store_thm("Decls_SNOC",
  ``!s1 s3 mn env1 ds1 d env3.
     Decls mn env1 s1 (SNOC d ds1) env3 s3 =
     ?env2 s2.
       Decls mn env1 s1 ds1 env2 s2 /\
       Decls mn env2 s2 [d] env3 s3``,
  METIS_TAC [SNOC_APPEND, Decls_APPEND]);


(* --- programs --- *)

val Prog_def = Define `
  Prog env1 s1 prog env2 s2 <=>
    ?new_tds new_mods new_env.
      (evaluate_prog F env1 s1 prog
         (s2,new_tds,Rval (new_mods,new_env))) /\
      (env2 = extend_top_env new_mods new_env new_tds env1)`

val Prog_NIL = store_thm("Prog_NIL",
  ``!s1 s3 env1 ds1 ds2 env3.
      Prog env1 s1 [] env3 s3 <=> (env3 = env1) /\ (s3 = s1)``,
  fs [Prog_def,Once evaluate_prog_cases] \\ EVAL_TAC \\ rw []
  \\ fs [environment_component_equality] \\ eq_tac \\ rw []);

val merge_alist_mod_env_ASSOC = prove(
  ``merge_alist_mod_env x (merge_alist_mod_env y z) =
    merge_alist_mod_env (merge_alist_mod_env x y) z``,
  Cases_on `x` \\ Cases_on `y` \\ Cases_on `z`
  \\ fs [merge_alist_mod_env_def,APPEND_ASSOC]);

val Prog_CONS = store_thm("Prog_CONS",
  ``!s1 s3 env1 d ds2 env3.
      Prog env1 s1 (d::ds2) env3 s3 =
      ?env2 s2.
        Prog env1 s1 [d] env2 s2 /\
        Prog env2 s2 ds2 env3 s3``,
  fs [Prog_def]
  \\ simp [Once evaluate_prog_cases]
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ simp [Once evaluate_prog_cases]
  \\ simp [Once evaluate_prog_cases]
  \\ fs [PULL_EXISTS]
  \\ rw [] \\ eq_tac \\ rw []
  THEN1
   (once_rewrite_tac [CONJ_ASSOC]
    \\ once_rewrite_tac [CONJ_SYM]
    \\ rewrite_tac [GSYM CONJ_ASSOC]
    \\ asm_exists_tac \\ fs []
    \\ fs [extend_top_env_def,combine_mod_result_def,merge_alist_mod_env_ASSOC])
  \\ Cases_on `r` \\ fs [combine_mod_result_def]
  \\ BasicProvers.FULL_CASE_TAC \\ fs []
  \\ asm_exists_tac \\ fs []
  \\ asm_exists_tac \\ fs []
  \\ fs [extend_top_env_def,combine_mod_result_def,merge_alist_mod_env_ASSOC])

val Prog_APPEND = store_thm("Prog_APPEND",
  ``!s1 s3 env1 ds1 ds2 env3.
      Prog env1 s1 (ds1 ++ ds2) env3 s3 =
      ?env2 s2.
         Prog env1 s1 ds1 env2 s2 /\
         Prog env2 s2 ds2 env3 s3``,
  Induct_on `ds1` \\ fs [Prog_NIL]
  \\ once_rewrite_tac [Prog_CONS] \\ fs [] \\ metis_tac []);

val Prog_Tdec = store_thm("Prog_Tdec",
  ``Prog env1 s1 [Tdec d] env2 s2 <=>
    Decls NONE env1 s1 [d] env2 s2``,
  fs [Prog_def,Decls_def,Once evaluate_prog_cases]
  \\ fs [Prog_def,Decls_def,Once evaluate_prog_cases]
  \\ fs [combine_mod_result_def,Once evaluate_top_cases,PULL_EXISTS]
  \\ fs [Once evaluate_decs_cases,PULL_EXISTS,combine_dec_result_def]
  \\ fs [Once evaluate_decs_cases,PULL_EXISTS,combine_dec_result_def,
         extend_top_env_def,environment_component_equality]
  \\ rw [] \\ eq_tac \\ rw [] \\ asm_exists_tac \\ fs []);

val mod_env_update_def = Define `
  mod_env_update mn (e1,e2) (b1,b2) =
    ((mn,BUTLASTN (LENGTH e2) b2)::e1,e2)`;

val Prog_Tmod = store_thm("Prog_Tmod",
  ``Prog env1 s1 [Tmod mn specs ds] env2 s2 <=>
    mn ∉ s1.defined_mods /\ no_dup_types ds /\
    ?s env.
      Decls (SOME mn) env1 s1 ds env s /\
      s2 = s with defined_mods := {mn} ∪ s.defined_mods /\
      env2 = env1 with <| m := (mn,BUTLASTN (LENGTH env1.v) env.v)::env1.m ;
                          c := mod_env_update mn env1.c env.c |>``,
  fs [Prog_def,Decls_def,Once evaluate_prog_cases,PULL_EXISTS,
      combine_mod_result_def,Once evaluate_top_cases]
  \\ fs [Prog_def,Decls_def,Once evaluate_prog_cases,PULL_EXISTS,
         combine_mod_result_def,Once evaluate_top_cases]
  \\ fs [extend_top_env_def,environment_component_equality]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs [BUTLASTN_LENGTH_APPEND]
  \\ ASM_REWRITE_TAC [] \\ TRY asm_exists_tac \\ ASM_REWRITE_TAC []
  \\ TRY (qexists_tac `<| m := env1.m ;
       c := merge_alist_mod_env ([],new_tds''') env1.c;
       v := new_env'' ++ env1.v |>`)
  \\ fs [BUTLASTN_LENGTH_APPEND] \\ Cases_on `env1.c`
  \\ fs [merge_alist_mod_env_def,mod_env_update_def,BUTLASTN_LENGTH_APPEND])

val _ = export_theory();
