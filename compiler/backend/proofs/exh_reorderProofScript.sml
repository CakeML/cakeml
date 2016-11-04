open preamble exh_reorderTheory exhSemTheory exhPropsTheory

val _ = new_theory "exh_reorderProof";

val s = ``s:'ffi exhSem$state``;

val MEM_size_mono = Q.store_thm("MEM_size_mono",
`! a b. (MEM a b) ==> ((v_size a) < 1 + v3_size b)`,
    Induct_on `b`
    \\ rw [v_size_def]
    \\ res_tac
    \\ rw []
)

val MEM_size_mono_v1_size = Q.store_thm("MEM_size_mono_v1_size",
`! a v env. MEM (a,v) env ==> v_size v  < 1 + v1_size env`,
   Induct_on `env`
   \\ rw [v_size_def]
   >- rw [v_size_def] 
   \\ res_tac 
   \\ rw []
)

val compile_v_def = tDefine "compile_v" `
    (compile_v (Litv l) = Litv l) /\
    (compile_v (Conv n vs) = Conv n (MAP compile_v vs)) /\
    (compile_v (Closure env name e) = Closure (MAP (\(a, v). (a, compile_v v) ) env) name (HD (compile [e]))) /\
    (compile_v (Recclosure env funs name) = Recclosure (MAP (\(a, v). (a, compile_v v) ) env) (MAP (\(a, b, e). (a, b, HD(compile [e]))) funs) name) /\
    (compile_v (Loc n) = Loc n) /\
    (compile_v (Vectorv vs) = Vectorv (MAP compile_v vs)) ` 

   (
    WF_REL_TAC `measure v_size`
    \\ rw []
    \\ imp_res_tac MEM_size_mono_v1_size    
    \\ imp_res_tac MEM_size_mono
    \\ rw []
    )

val _ = export_rewrites ["compile_v_def"];

val _ = overload_on ("compile_env", ``MAP \(tn, v). (tn, compile_v v)``);

val ALOOKUP_compile_env = Q.store_thm ("ALOOKUP_compile_env",
    `! env q x. 
        (ALOOKUP (compile_env env) q) = OPTION_MAP compile_v (ALOOKUP env q)`,
    Induct \\ rw []
    \\ pairarg_tac
    \\ fs []
    \\ rw []
)

val compile_store_v_def = Define `
    (compile_store_v (Refv v) = Refv (compile_v v)) /\
    (compile_store_v (W8array l) = W8array l) /\
    (compile_store_v (Varray vs) = Varray (MAP compile_v vs))`

val compile_state_def = Define `
    compile_state (^s) = 
    <| clock := s.clock;
       refs := MAP compile_store_v s.refs;
       ffi := s.ffi;
       globals := MAP (OPTION_MAP compile_v) s.globals
    |>`;

val compile_state_simps = save_thm ("compile_state_simps", LIST_CONJ
    [EVAL ``(compile_state s).globals``,
     EVAL ``(compile_state s).clock``,
     EVAL ``(compile_state s).ffi``,
     EVAL ``(compile_state s).refs``]);

val _ = export_rewrites ["compile_state_simps"];

val compile_length = Q.store_thm ("compile_length",
    `! es. LENGTH (compile es) = LENGTH es`,
    ho_match_mp_tac compile_ind
    \\ rw [compile_def]
    )

val compile_singleton = Q.store_thm ("compile_singleton",
   `! e. ?e2. compile [e] = [e2]`,
    rw []
    \\ qspec_then `[e]` mp_tac compile_length
    \\ rw [LENGTH_EQ_NUM_compute]
)

infixr $;
fun (f $ x) = f x

(*
val (asl, w) = top_goal ();
val goal = top_goal ();
*)

fun hd_compile_sing_tac (goal as (asl,w)) = 
    let 
       val t = find_term (can (match_term ``HD (exh_reorder$compile [e])``)) w;
       val e_term =  rand $ rator $ rand $ rand t;
       in 
        strip_assume_tac $ SPEC e_term compile_singleton
    end
    goal

val compile_cons = Q.store_thm ("compile_cons",
   `! e es. compile (e::es) = HD (compile [e]) :: (compile es)`,
   rw []
   \\ Cases_on `es`
   \\ rw [compile_def]
   \\ METIS_TAC [compile_singleton, HD]
)

fun app_compile_sing_tac (goal as (asl,w)) =
    let 
        val t = find_term (can (match_term 
            ``(evaluate env s (exh_reorder$compile [e1] ++ exh_reorder$compile (e2::es)))``)) w;
        val app_term = rand $ t;
        val e1_term = rand $ rator $ rand $ rand $ rator app_term;
        val e2_term = rand $ rator $ rand $ rand app_term;
        in 
                (
                 rw [Once compile_cons, SimpR ``$++``]
                 THEN rw [Once compile_cons, SimpR ``CONS``]
                 THEN (strip_assume_tac $ SPEC e1_term compile_singleton)
                 THEN (strip_assume_tac $ SPEC e2_term compile_singleton)
                )
                goal

    end

val compile_nil = save_thm ("compile_nil[simp]", EVAL ``exh_reorder$compile []``);

val compile_app_tran = Q.store_thm ("compile_app_tran", 
    `! x h. compile (x ++ h) = (compile x) ++ (compile h)`,
    Induct_on `x`
    \\ fs []
    \\ rw [Once compile_cons] 
    \\ hd_compile_sing_tac
    \\ rw [Once compile_cons]
)

val rev_compile_compile_rev = Q.store_thm ("rev_compile_compile_rev", 
    `! x. REVERSE (compile x) = compile (REVERSE x)`,
    Induct
    \\ fs []
    \\ rw [Once compile_cons]
    \\ hd_compile_sing_tac
    \\ rw [EQ_SYM_EQ, REVERSE_DEF]
    \\ rw [compile_app_tran]
   )

val map_reverse_reverse_map = Q.store_thm ("map_reverse_reverse_map", 
    `! f l. REVERSE (MAP f l) = MAP f (REVERSE l)`,
    Induct_on `l`
    \\ fs [])


val ALOOKUP_none_not_some = Q.store_thm ("ALOOKUP_none_not_some",
    `! env n. (ALOOKUP env n = NONE) ==> (ALOOKUP env n = SOME x) ==> F`,
    Induct_on `env`
    \\ fs []
)

val MAP_FST_MAP_triple = Q.store_thm ("MAP_FST_MAP_triple",
    `! a b c y l. (MAP FST (MAP (\(a,b,c). a, b, (y c)) l)) = (MAP FST l)`,
    Induct_on `l`
    \\ fs []
    \\ rw []
    \\ pairarg_tac
    \\ fs []
)

val _ = temp_overload_on ("None",``NONE``)
val _ = temp_overload_on ("Some",``SOME``)
val _ = temp_overload_on ("Length",``LENGTH``)


val find_match_def = Define`
    find_match refs v [] = No_match /\
    find_match refs v (pe::pes) = 
        if ALL_DISTINCT (pat_bindings (FST pe) []) then
            case pmatch refs (FST pe) v [] of
            | Match env' => Match (env', SND pe)
            | Match_type_error => Match_type_error
            | _ => find_match refs v pes
        else Match_type_error `


val is_const_con_pat_bindings_empty = Q.store_thm("is_const_con_pat_bindings_empty",
    `is_const_con x ==> pat_bindings x a = a`,
    Cases_on `x`
    \\ fs [is_const_con_def]
    \\ EVAL_TAC)

val find_match_drop_no_match = Q.store_thm ("find_match_drop_no_match",
    `! a b. pmatch refs (FST b) v [] = No_match /\ (is_const_con (FST b)) ==>
     ((find_match refs v ( a++ [b] ++c)) = find_match refs v (a++c))`,
     Induct
     \\ rw [find_match_def, is_const_con_pat_bindings_empty]
)

val find_match_may_drop_dup = Q.store_thm ("find_match_may_drop_dup",
    `! a b. ((is_const_con (FST b)) /\ (MEM (FST b) (MAP FST a))) ==>
     ((find_match refs v ( a++ [b] ++c)) = find_match refs v (a++c))`,
     Induct
     \\ rw [find_match_def]
     \\ CASE_TAC
     \\ rw [find_match_drop_no_match]
)

val pmatch_same_match = Q.store_thm("pmatch_same_match",
    `is_const_con x /\ pmatch refs x v [] = Match a /\ ¬(isPvar y) /\
        pmatch refs y v [] = Match b
        ==> (x = y)`,
    Cases_on `x` \\ rw [is_const_con_def]
    \\ Cases_on `v` \\ fs [pmatch_def]
    \\ every_case_tac \\ fs []
    \\ fs [LENGTH_NIL_SYM]
    \\ Cases_on `y` \\ fs [pmatch_def]
    \\ rw []
    \\ every_case_tac \\ fs [LENGTH_NIL]
)

val pmatch_match_match = Q.store_thm("pmatch_match_match",
    `! x y v. is_const_con x /\ isPcon y /\ pmatch refs x v [] = Match_type_error ==>
        pmatch refs y v [] = Match_type_error`,
     Cases \\ fs [isPcon_def, is_const_con_def] 
     \\ Cases \\ fs [isPcon_def,is_const_con_def] 
     \\ Cases \\ fs [pmatch_def]
     \\ rw [LENGTH_NIL_SYM, LENGTH_NIL]
     \\ fs [LENGTH_NIL_SYM, LENGTH_NIL]
     \\ spose_not_then strip_assume_tac \\ fs[LENGTH_NIL_SYM]
     \\ rfs[pmatch_def]);

val pmatch_match_con = Q.store_thm("pmatch_match_con",
    `∀x y v.
     is_const_con x /\ pmatch refs x v [] = Match a /\ (isPcon y) ==>
        pmatch refs y v [] <> Match_type_error`,
    Cases \\ Cases \\ fs[is_const_con_def,isPcon_def,pmatch_def]
    \\ Cases \\ fs[pmatch_def]
    \\ rw[]
    \\ fs[LENGTH_NIL_SYM,pmatch_def,LENGTH_NIL]);

val isPcon_isPvar = Q.store_thm("isPcon_isPvar",
  `∀x. isPcon x ==> ¬isPvar x`,
  Cases \\ rw[isPcon_def,isPvar_def]);

val find_match_may_reord = Q.store_thm("find_match_may_reord",
    `! a b. is_const_con (FST b) /\ ¬((MEM (FST b) (MAP FST a)))
            /\ EVERY isPcon (MAP FST a) /\
            find_match refs v (a ++ [b] ++ c) ≠ Match_type_error
            ==> 
        find_match refs v (a ++ [b] ++ c) = find_match refs v (b::a++c) `,
    Induct \\ fs []
    \\ rw [find_match_def]
    \\ every_case_tac \\ fs [find_match_def]
    >- ( imp_res_tac pmatch_match_match \\ fs [])
    >- ( imp_res_tac pmatch_match_match \\ fs [])
    >- (
        imp_res_tac isPcon_isPvar \\
        imp_res_tac pmatch_same_match  )
    >- (
      CCONTR_TAC \\ fs[EVERY_MAP] \\
      first_x_assum(qspec_then`b`mp_tac) \\ rw[] )
    >- (
      CCONTR_TAC \\ fs[]
      \\ fs[is_const_con_pat_bindings_empty] ))

val find_match_drop_after_pvar = Q.store_thm("find_match_drop_after_pvar",
    `! a. isPvar (FST b) ==>
        find_match refs v (a ++ [b] ++ c) = find_match refs v (a ++ [b])
    `,
    Induct \\ fs [find_match_def]
    \\ rw [] 
    \\ CASE_TAC
    \\ Cases_on `FST b` \\ fs [pmatch_def, isPvar_def]
    )

val (reord_rules,reord_ind,reord_cases) = Hol_reln`
  (isPvar (FST b) ==> reord (a ++ [b] ++ c) (a ++ [b])) /\
  (is_const_con (FST b) /\
   MEM (FST b) (MAP FST a) ==>
   reord (a ++ [b] ++ c) (a ++ c)) /\
  (is_const_con (FST b) /\
   ¬MEM (FST b) (MAP FST a) /\
   EVERY isPcon (MAP FST a) ==>
   reord (a ++ [b] ++ c) ([b] ++ a ++ c))`;

val const_cons_sep_reord = Q.store_thm("const_cons_sep_reord", 
    `! a const_cons. 
        const_cons_sep pes a const_cons = (const_cons', a') /\
        EVERY isPcon (MAP FST a) /\
        EVERY ($~ o is_const_con) (MAP FST a) /\
        EVERY is_const_con (MAP FST const_cons) 
         ==> 
        reord^* (const_cons ++ (REVERSE a) ++ pes) (const_cons' ++ (REVERSE a')) `,
    Induct_on `pes` \\ fs [] \\ rw [const_cons_sep_def]
    >- (
        rw []
        \\ match_mp_tac RTC_SUBSET
        \\ rw [reord_cases]
    )
    >- (
       rw [Once RTC_CASES1]
       \\ disj2_tac
       \\ fs []
       \\ first_x_assum drule \\ strip_tac
       \\ rfs []
       \\ HINT_EXISTS_TAC
       \\ rw [reord_cases]
       \\ METIS_TAC [APPEND_ASSOC, MEM_APPEND, MAP_APPEND]
    )
    >-(
      fs [] 
      \\ first_x_assum drule \\ strip_tac
      \\ rfs []
      \\ rw [Once RTC_CASES1]
      \\ disj2_tac
      \\ HINT_EXISTS_TAC
      \\ rw [reord_cases]
      \\ disj2_tac \\ disj2_tac
      \\ qexists_tac`const_cons++REVERSE a`
      \\ simp[MAP_REVERSE,EVERY_REVERSE]
      \\ fs[EVERY_MEM,MEM_MAP]
      \\ metis_tac[is_const_con_is_Pcon] )
    >- (
      first_x_assum drule \\ strip_tac
      \\ rfs[]
      \\ metis_tac[CONS_APPEND,APPEND_ASSOC] )
    >- (
      rw[REVERSE_APPEND] ))


val const_cons_fst_reord = Q.store_thm("const_cons_fst_reord", 
    `reord^* pes (const_cons_fst pes)`,
    fs [const_cons_fst_def]
    \\ pairarg_tac
    \\ fs []
    \\ METIS_TAC [const_cons_sep_reord, REVERSE_DEF, APPEND_NIL,EVERY_DEF, MAP]
)

val evaluate_match_find_match_none = Q.store_thm ("evaluate_match_find_match_none",
    `(!env. find_match s.refs v pes ≠ Match env) ==>
            evaluate_match env s v pes = (s, Rerr(Rabort Rtype_error))
            `,
    Induct_on `pes`
    \\ fs [find_match_def, evaluate_def]
    \\ Cases
    \\ fs [evaluate_def]
    \\ rw []
    \\ simp [Once pmatch_nil]
    \\ every_case_tac
    \\ fs [evaluate_def,find_match_def]
)

(*connection between evaluate_match and find_match*)
val evaluate_match_find_match_some = Q.store_thm ("evaluate_match_find_match_some",
    ` find_match s.refs v pes = Match (env',e) ==>
        evaluate_match env s v pes = evaluate (env' ++ env) s [e] `,
    Induct_on `pes`
    \\ fs [find_match_def,evaluate_def]
    \\ Cases
    \\ fs [evaluate_def]
    \\ TOP_CASE_TAC
    \\ strip_tac
    \\ rw [Once pmatch_nil]
    \\ pop_assum mp_tac
    \\ TOP_CASE_TAC \\ fs[]
)

val find_match_preserved_reord = Q.store_thm("find_match_preserved_reord", 
    `! pes pes'. reord pes pes' ==> 
        find_match refs v pes <> Match_type_error ==> 
            find_match refs v pes = find_match refs v pes'`,
    ho_match_mp_tac reord_ind
    \\ strip_tac 
    >-( 
        METIS_TAC [find_match_drop_after_pvar]
    )
    \\ strip_tac
    >- (
        METIS_TAC [find_match_may_drop_dup]
    )
    \\ METIS_TAC [find_match_may_reord, APPEND_ASSOC, CONS_APPEND] 
)

val find_match_preserved_reord_RTC = Q.store_thm("find_match_preserved_reord_RTC", 
    `! pes pes'. reord^* pes pes' ==> 
        find_match refs v pes <> Match_type_error ==> 
            find_match refs v pes = find_match refs v pes'`,
    ho_match_mp_tac RTC_INDUCT
    \\ METIS_TAC [find_match_preserved_reord]
    )

val const_cons_fst_find_match = Q.store_thm("const_cons_fst_find_match",
    `find_match refs v pes <> Match_type_error ==> 
        find_match refs v pes = find_match refs v (const_cons_fst pes)`,
    METIS_TAC [find_match_preserved_reord_RTC, const_cons_fst_reord])

(*
 example:
 n.b. the constant constructors come in reverse order
 to fix this, const_cons_fst could REVERSE the const_cons accumulator
EVAL ``
const_cons_fst [
  (Pcon 1 [Pvar "x"], e1);
  (Pcon 3 [], e3);
  (Pvar "z", ez);
  (Pcon 2 [Pvar "y"], e2);
  (Pcon 4 [], e4)]``;
*)

val pmatch_nil_rwt =
    pmatch_nil |> CONJUNCT1
    |> ADD_ASSUM``(env:(tvarN,exhSem$v) alist) <> []`` |> DISCH_ALL


val pmatch_nil_imp = Q.store_thm( "pmatch_nil_imp",
    ` pmatch refs p err_v [] = res 
            ==> pmatch refs p err_v env = map_match (combin$C $++ env) res`,
    METIS_TAC [pmatch_nil])


val pmatch_compile = Q.store_thm("pmatch_compile", 
` (! refs p err_v env. 
    pmatch (MAP compile_store_v refs) p (compile_v err_v) (compile_env env) = 
    map_match (compile_env) (pmatch refs p err_v env)) /\
  (! refs ps vs env.
   pmatch_list (MAP compile_store_v refs) ps (MAP compile_v vs) (compile_env env) =  
   map_match (compile_env) (pmatch_list refs ps vs env)
  ) `,
  ho_match_mp_tac pmatch_ind \\ rw [pmatch_def]
  >- (fs [ETA_AX])
  >- (
    fs [semanticPrimitivesTheory.store_lookup_def] 
    \\ rw [EL_MAP]
    \\ match_mp_tac EQ_SYM
    \\ CASE_TAC \\ fs[compile_store_v_def]
  )

  >- (
    every_case_tac \\ fs []
    \\ rw []
  )
 )

val pmatch_compile_nil = pmatch_compile |> CONJUNCT1 
    |> SPEC_ALL
    |> Q.GEN`env`
    |> Q.SPEC`[]`
    |> SIMP_RULE (srw_ss())[]

val find_match_compile = Q.store_thm("find_match_compile",
    `find_match (MAP compile_store_v refs) (compile_v v) (MAP (I ## f) pes) = 
     map_match (compile_env ## f) (find_match refs v pes)`,
     Induct_on `pes`
     \\ fs [find_match_def]
     \\ rw [] 
     \\ fs [pmatch_compile_nil]
     \\ every_case_tac \\ fs []
     \\ rw []
)

val find_match_imp_compile = Q.store_thm("find_match_imp_compile",
  `find_match s.refs v pes = Match (env',e) ==>
   find_match (compile_state s).refs (compile_v v)
       (MAP (\(p,e). (p,HD(compile[e]))) pes) =
           Match (compile_env env', HD(compile[e]))`,
  strip_tac \\
  (Q.GENL[`pes`,`v`,`refs`,`f`]find_match_compile
   |> Q.ISPECL_THEN[`\e. HD(compile[e])`,`s.refs`,`v`,`pes`]mp_tac) \\
  simp[] \\
  disch_then(SUBST1_TAC o SYM) \\
  rpt(AP_TERM_TAC ORELSE AP_THM_TAC) \\
  simp[FUN_EQ_THM,FORALL_PROD]);


do_opapp_compile = Q.store_thm("do_opapp_compile", 

val compile_correct = Q.store_thm( "compile_correct",
    `(!env ^s es s1 r1. 
        (evaluate env s es = (s1, r1)) /\
        r1 <> Rerr (Rabort Rtype_error) ==>
        (evaluate (compile_env env) (compile_state s) (compile es) =
            (compile_state s1, map_result (MAP compile_v) compile_v r1)
            ))
       /\ 
        (!(env:(tvarN, exhSem$v) alist) ^s (err_v:exhSem$v) (pes:(pat,exhLang$exp)alist) s1 r1. 
            evaluate_match env ^s err_v pes = (s1,r1) /\ 
            r1 <> Rerr (Rabort Rtype_error) ==> 
                evaluate_match (compile_env env) (compile_state s) (compile_v err_v)
                    (MAP (\(p,e). (p,HD(compile[e]))) pes) =
                     (compile_state s1, map_result (MAP compile_v) compile_v r1))`,
            (*find_match s.refs err_v pes = res /\ 
            res <> Match_type_error
                ==> find_match (compile_state s).refs (compile_v err_v) pes = 
                map_match (\(env,e). (compile_env env, HD (compile [e]))) res)`,*)
    
    ho_match_mp_tac evaluate_ind
    \\ rw [compile_def]
    \\ fs [evaluate_def]
    \\ rw []
    \\ fs [MAP_FST_MAP_triple]
    >- (
        every_case_tac
        \\ fs []
        \\ rfs []
        \\ app_compile_sing_tac
        \\ fs []
        \\ rfs []
        \\ rfs [Once compile_cons]
        \\ imp_res_tac evaluate_sing
        \\ rw []
        \\ fs []
        \\ rfs [Once evaluate_def]
       )
   >- (
       hd_compile_sing_tac
       \\ every_case_tac \\ fs [] \\ rw [] \\ rfs []
       \\ imp_res_tac evaluate_sing \\ fs []
   )
   >- (
      hd_compile_sing_tac
      \\ every_case_tac \\ fs [] \\ rw [] \\ rfs []
      \\ qmatch_assum_rename_tac `evaluate_match env s' v pes = _` 
      \\ Cases_on `!env. find_match s'.refs v pes <> Match env `
      \\ imp_res_tac evaluate_match_find_match_none \\ fs[]
      \\ Cases_on `env'` 
      \\ first_x_assum (CHANGED_TAC o (SUBST1_TAC o SYM))
      \\ qmatch_assum_rename_tac`_ = Match (env',e')`
      \\ `find_match s'.refs v (const_cons_fst pes) = Match (env',e')`
      by metis_tac[const_cons_fst_find_match,
                   semanticPrimitivesTheory.match_result_distinct]
    
      \\ imp_res_tac find_match_imp_compile
      \\ imp_res_tac evaluate_match_find_match_some
      \\ fs []
   )
   (*10 left*)
   >- (
      every_case_tac \\ fs [] \\ rw [] \\ rfs []
      \\ rfs [rev_compile_compile_rev]
      \\ rw [map_reverse_reverse_map]
      \\ fs [ETA_AX]
   )
   >- (
      every_case_tac \\ fs [ALOOKUP_compile_env]  
   )
   (* 8 subgoals *)
   >- (
      rfs [EL_MAP]
      \\ fs [IS_SOME_EXISTS]
   )
   >- (
      fs [EL_MAP]
      \\ rfs []
   )
   (*6 left*)
   >- (
      (*the app case*)
      every_case_tac  \\ fs [rev_compile_compile_rev] \\ rfs [] 
      (*14*)

       \\ rw [compile_state_def]
      (*32 subgoals...*)
      >- (
         \\ fs [] \\ rfs []
         \\ rw []
         \\ Induct_on `a'`
         \\ fs []
         \\ rw []
         \\ rw [do_opapp_def]
         \\ fs []
         \\ rw []
         \\ every_case_tac
         >- (
            fs [REVERSE_APPEND] \\ rfs [] \\ rw []
            \\ fs [do_opapp_def]
         )
         >- (
            fs []
            \\ fs [do_opapp_def] 
            \\ rw []
            \\ res_tac 
         )
       *) 
   )

   >- (
      hd_compile_sing_tac
      \\ every_case_tac \\ fs [] \\ rw [] \\ rfs []
      \\ imp_res_tac evaluate_sing \\ fs []
      \\ qmatch_assum_rename_tac `evaluate_match env s' v pes = _` 
      \\ Cases_on `!env. find_match s'.refs v pes <> Match env `
      \\ imp_res_tac evaluate_match_find_match_none \\ fs[]
      \\ Cases_on `env'` 
      \\ rw []
      \\ first_x_assum (CHANGED_TAC o (SUBST1_TAC o SYM))
      \\ qmatch_assum_rename_tac`_ = Match (env',e')`
      \\ `find_match s'.refs v (const_cons_fst pes) = Match (env',e')`
      by metis_tac[const_cons_fst_find_match,
                   semanticPrimitivesTheory.match_result_distinct]
    
      \\ imp_res_tac find_match_imp_compile
      \\ imp_res_tac evaluate_match_find_match_some
      \\ fs []
   )

  >- (
       hd_compile_sing_tac
       \\ every_case_tac \\ fs [] \\ rw []
       \\ rfs []
       \\ imp_res_tac evaluate_sing \\ fs []
       \\ rfs []
       \\ fs [libTheory.opt_bind_def]
       \\ CASE_TAC \\ fs[]
       \\ hd_compile_sing_tac
       \\ imp_res_tac evaluate_sing \\ fs []
   )
   >- ( cheat )
   >- (
     fs[compile_state_def,MAP_GENLIST]
     )

   >-(
     fs [pmatch_compile]
     \\ every_case_tac \\ fs []
     \\ hd_compile_sing_tac \\ fs []
     \\ rfs []
    )
)
