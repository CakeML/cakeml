open preamble flat_reorder_matchTheory flatSemTheory flatPropsTheory

val _ = new_theory "flat_reorder_matchProof";

(* TODO: move *)

infixr $;
fun (f $ x) = f x

val list_result_map_result = Q.store_thm("list_result_map_result",
  `list_result (map_result f g r) = map_result (MAP f) g (list_result r)`,
  Cases_on`r` \\ EVAL_TAC);

val MAP_FST_MAP_triple = Q.store_thm ("MAP_FST_MAP_triple",
  `! a b c y l. (MAP FST (MAP (\(a,b,c). a, b, (y c)) l)) = (MAP FST l)`,
  Induct_on `l` \\ fs [] \\ rw []
  \\ pairarg_tac \\ fs [])

val ALOOKUP_MAP3 = Q.store_thm("ALOOKUP_MAP3",
  `ALOOKUP (MAP (λ(a,b,c). (a,b, f c)) ls) =
   OPTION_MAP (λ(b,c). (b, f c)) o (ALOOKUP ls)`,
  qmatch_goalsub_abbrev_tac`OPTION_MAP g o _`
  \\ Q.ISPECL_THEN[`g`,`ls`](mp_tac o GSYM) ALOOKUP_MAP
  \\ simp[Abbr`g`,LAMBDA_PROD]);

val _ = temp_overload_on ("None",``NONE``)
val _ = temp_overload_on ("Some",``SOME``)
val _ = temp_overload_on ("Length",``LENGTH``)

val BAG_DISJOINT_SYM = Q.store_thm("BAG_DISJOINT_SYM",
  `BAG_DISJOINT b1 b2 ⇔ BAG_DISJOINT b2 b1`,
  rw[BAG_DISJOINT,DISJOINT_SYM]);

val BAG_ALL_DISTINCT_SUB = Q.store_thm("BAG_ALL_DISTINCT_SUB",
  `BAG_ALL_DISTINCT b2 ∧ b1 ≤ b2 ⇒ BAG_ALL_DISTINCT b1`,
  rw[BAG_ALL_DISTINCT,SUB_BAG,BAG_INN]
  \\ spose_not_then strip_assume_tac
  \\ fs[NOT_LESS_EQUAL,GREATER_EQ]
  \\ first_x_assum(qspecl_then[`e`,`2`]mp_tac)
  \\ simp[NOT_LESS_EQUAL]
  \\ first_x_assum(qspec_then`e`mp_tac)
  \\ simp[]);

val BAG_OF_LIST_def = Define`
  (BAG_OF_LIST [] = {||}) ∧
  (BAG_OF_LIST (x::xs) = BAG_INSERT x (BAG_OF_LIST xs))`;
val _ = export_rewrites["BAG_OF_LIST_def"];

val BAG_OF_LIST_empty = Q.store_thm("BAG_OF_LIST_empty[simp]",
  `(BAG_OF_LIST l = {||} ⇔ (l = []))`,
  Cases_on`l` \\ rw[]);

val BAG_INSERT_BAG_UNION = Q.store_thm("BAG_INSERT_BAG_UNION",
  `BAG_INSERT x (BAG_UNION b1 b2) = BAG_UNION (BAG_INSERT x b1) b2`,
  rw[BAG_INSERT_UNION,ASSOC_BAG_UNION]);

val BAG_OF_LIST_APPEND = Q.store_thm("BAG_OF_LIST_APPEND",
  `∀l1 l2. BAG_OF_LIST (l1 ++ l2) = BAG_UNION (BAG_OF_LIST l1) (BAG_OF_LIST l2)`,
  Induct \\ simp[BAG_INSERT_BAG_UNION]);

(* -- *)

val s = ``s:'ffi modSem$state``;

(* value transformation *)

val MEM_size_mono = Q.store_thm("MEM_size_mono",
  `!a b. (MEM a b) ==> ((v_size a) < 1 + v3_size b)`,
  Induct_on `b` \\ rw [v_size_def] \\ res_tac \\ rw [])

val MEM_size_mono_v1_size = Q.store_thm("MEM_size_mono_v1_size",
  `! a v env. MEM (a,v) env ==> v_size v  < 1 + v1_size env`,
  Induct_on `env` \\ rw[] \\ rw [v_size_def] \\ res_tac \\ rw [])

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
  \\ rw [])

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

val dec_clock_compile_state = Q.store_thm("dec_clock_compile_state",
  `dec_clock (compile_state s) = compile_state (dec_clock s)`,
  EVAL_TAC);

val compile_state_with_clock = Q.store_thm("compile_state_with_clock",
  `compile_state st with clock := k = compile_state (st with clock := k)`,
  EVAL_TAC);

val compile_state_simps = save_thm ("compile_state_simps", LIST_CONJ
    [EVAL ``(compile_state s).globals``,
     EVAL ``(compile_state s).clock``,
     EVAL ``(compile_state s).ffi``,
     EVAL ``(compile_state s).refs``]);

val _ = export_rewrites ["compile_state_simps"];

(* syntactic properties of the compiler *)

val isPcon_isPvar = Q.store_thm("isPcon_isPvar",
  `∀x. isPcon x ==> ¬isPvar x`,
  Cases \\ rw[isPcon_def,isPvar_def]);

val is_const_con_thm = Q.store_thm("is_const_con_thm",
  `is_const_con x ⇔ ∃t. x = Pcon (SOME t) []`,
  Cases_on`x` \\ EVAL_TAC \\ rw[]
  \\ rename1`Pcon t l` \\ Cases_on`t` \\ EVAL_TAC \\ rw[]);

val isPcon_thm = Q.store_thm("is_Pcon_thm",
  `isPcon x ⇔ ∃t l. x = Pcon (SOME t) l`,
  Cases_on`x` \\ EVAL_TAC \\ rw[]
  \\ rename1`Pcon t l` \\ Cases_on`t` \\ EVAL_TAC \\ rw[EXISTS_THM]);

val is_const_con_is_Pcon = Q.store_thm("is_const_con_is_Pcon",
  `is_const_con x ==> isPcon x`,
  rw[is_const_con_thm,isPcon_thm]);

val is_const_con_pat_bindings_empty = Q.store_thm("is_const_con_pat_bindings_empty",
    `is_const_con x ==> pat_bindings x a = a`,
    rw [is_const_con_thm] \\ EVAL_TAC)

fun hd_compile_sing_tac (goal as (asl,w)) =
    let
       val t = find_term (can (match_term ``HD (mod_reorder_match$compile [e])``)) w;
       val e_term =  rand $ rator $ rand $ rand t;
       in
        strip_assume_tac $ SPEC e_term compile_sing
    end
    goal

fun app_compile_sing_tac (goal as (asl,w)) =
    let
        val t = find_term (can (match_term
            ``(evaluate env s (flat_reorder_match$compile [e1] ++ flat_reorder_match$compile (e2::es)))``)) w;
        val app_term = rand $ t;
        val e1_term = rand $ rator $ rand $ rand $ rator app_term;
        val e2_term = rand $ rator $ rand $ rand app_term;
        in
                (
                 rw [Once compile_cons, SimpR ``$++``]
                 THEN rw [Once compile_cons, SimpR ``CONS``]
                 THEN (strip_assume_tac $ SPEC e1_term compile_sing)
                 THEN (strip_assume_tac $ SPEC e2_term compile_sing)
                )
                goal
    end

val compile_append = Q.store_thm ("compile_append",
  `! x h. compile (x ++ h) = (compile x) ++ (compile h)`,
  Induct_on `x`
  \\ fs []
  \\ rw [Once compile_cons]
  \\ hd_compile_sing_tac
  \\ rw [Once compile_cons])

val compile_reverse = Q.store_thm ("compile_reverse",
  `! x. REVERSE (compile x) = compile (REVERSE x)`,
  Induct
  \\ fs []
  \\ rw [Once compile_cons]
  \\ hd_compile_sing_tac
  \\ rw [EQ_SYM_EQ, REVERSE_DEF]
  \\ rw [compile_append])

(* alternative characterisation of pattern matching *)

val find_match_def = Define`
    find_match env s v [] = No_match /\
    find_match env s v (pe::pes) =
        if ALL_DISTINCT (pat_bindings (FST pe) []) then
            case pmatch env s (FST pe) v [] of
            | Match env' => Match (env', SND pe)
            | Match_type_error => Match_type_error
            | _ => find_match env s v pes
        else Match_type_error `

val evaluate_match_find_match_none = Q.store_thm ("evaluate_match_find_match_none",
  `env.exh_pat ∧ (!r. find_match env ^s.refs v pes ≠ Match r) ==>
          evaluate_match env s v pes errv = (s, Rerr (Rabort Rtype_error))`,
  Induct_on `pes`
  \\ fs [find_match_def, evaluate_def]
  \\ Cases
  \\ fs [evaluate_def]
  \\ IF_CASES_TAC \\ fs[]
  \\ TOP_CASE_TAC
  \\ rw [])

val evaluate_match_find_match_some = Q.store_thm ("evaluate_match_find_match_some",
  ` find_match env s.refs v pes = Match (env',e) ==>
      evaluate_match env s v pes errv = evaluate (env with v := env' ++ env.v) s [e] `,
  Induct_on `pes`
  \\ fs [find_match_def,evaluate_def]
  \\ Cases
  \\ fs [evaluate_def]
  \\ TOP_CASE_TAC
  \\ CASE_TAC
  \\ rw[])

(* reordering operations are allowed *)

val pmatch_same_match = Q.store_thm("pmatch_same_match",
  `is_const_con x /\ pmatch env refs x v [] = Match a /\ ¬(isPvar y) /\
      pmatch env refs y v [] = Match b
      ==> (x = y)`,
  rw [is_const_con_thm]
  \\ Cases_on `v` \\ fs [pmatch_def]
  \\ rename[`Pcon o1 _`,`Conv o2 _`,`isPvar v`]
  \\ Cases_on`o1` \\ Cases_on`o2` \\ Cases_on`v`
  \\ fs[pmatch_def,bool_case_eq] \\ rveq
  \\ rename[`Pcon o1`] \\ Cases_on`o1`
  \\ fs[pmatch_def,bool_case_eq]
  \\ every_case_tac \\ fs [] \\ rveq
  \\ fs[semanticPrimitivesTheory.same_ctor_def]
  \\ rename[`pmatch_list _ _ _ l _`]
  \\ Cases_on`l` \\ fs[pmatch_def]
  \\ rename[`pmatch_list _ _ l _ _`]
  \\ Cases_on`l` \\ fs[pmatch_def]);

val pmatch_match_match = Q.store_thm("pmatch_match_match",
  `! x y v. is_const_con x /\ isPcon y /\ pmatch env refs x v [] = Match_type_error ==>
      pmatch env refs y v [] = Match_type_error`,
  rw[is_const_con_thm,isPcon_thm]
  \\ Cases_on`v` \\ fs[pmatch_def]
  \\ rename1`Conv tt _` \\ Cases_on`tt`
  \\ fs[pmatch_def,semanticPrimitivesTheory.same_ctor_def]
  \\ pop_assum mp_tac \\ simp[bool_case_eq]
  \\ Cases_on`env.check_ctor` \\ fs[]
  \\ Cases_on`t` \\ Cases_on`x` \\ Cases_on`t'` \\ fs[ctor_same_type_def]
  \\ rename1`((g,t),LENGTH l)`
  \\ Cases_on`((g,t),LENGTH l) ∈ env.c` \\ fs[]
  \\ rename1`r1 ≠ r2`
  \\ Cases_on`t = r2` \\ fs[] \\ rveq
  \\ srw_tac[DNF_ss][]

  Cases \\ fs [isPcon_def, is_const_con_def]
  \\ Cases \\ fs [isPcon_def,is_const_con_def]
  \\ Cases \\ fs [pmatch_def]
  \\ rename[`Pcon o1 l1`,`Conv o2 l2`]
  \\ Cases_on`o1` \\ Cases_on`o2` \\ fs[pmatch_def]
  \\ rename[`Pcon o1 l1`]
  \\ Cases_on`o1` \\ fs[pmatch_def,semanticPrimitivesTheory.same_ctor_def]
  \\ rw[] \\ fs[pmatch_def] \\ rw[] \\ fs[pmatch_def]
  \\ rw [LENGTH_NIL_SYM, LENGTH_NIL]
  \\ fs [LENGTH_NIL_SYM, LENGTH_NIL]
  \\ spose_not_then strip_assume_tac \\ fs[LENGTH_NIL_SYM]
  \\ rfs[pmatch_def]);

val pmatch_match_con = Q.store_thm("pmatch_match_con",
    `∀x y v.
     is_const_con x /\ pmatch env s x v [] = Match a /\ (isPcon y) ==>
        pmatch env s y v [] <> Match_type_error`,
    Cases \\ Cases \\ fs[is_const_con_def,isPcon_def,pmatch_def]
    \\ Cases \\ fs[pmatch_def]
    \\ rename[`Pcon o1 l1`,`Conv o2 l2`]
    \\ Cases_on`o1` \\ Cases_on`o2` \\ fs[pmatch_def] \\ rw[]
    \\ fs[]

    \\ rw[]
    \\ fs[LENGTH_NIL_SYM,pmatch_def,LENGTH_NIL]);

val find_match_drop_no_match = Q.store_thm ("find_match_drop_no_match",
    `! a b. pmatch env s (FST b) v [] = No_match /\ (is_const_con (FST b)) ==>
     ((find_match env s v ( a++ [b] ++c)) = find_match env s v (a++c))`,
     Induct
     \\ rw [find_match_def, is_const_con_pat_bindings_empty]
)

val find_match_may_drop_dup = Q.store_thm ("find_match_may_drop_dup",
    `! a b. ((is_const_con (FST b)) /\ (MEM (FST b) (MAP FST a))) ==>
     ((find_match env s v ( a++ [b] ++c)) = find_match env s v (a++c))`,
     Induct
     \\ rw [find_match_def]
     \\ CASE_TAC
     \\ rw [find_match_drop_no_match]
)

val find_match_may_reord = Q.store_thm("find_match_may_reord",
    `! a b. is_const_con (FST b) /\ ¬((MEM (FST b) (MAP FST a)))
            /\ EVERY isPcon (MAP FST a) /\
            find_match env s v (a ++ [b] ++ c) ≠ Match_type_error
            ==>
        find_match env s v (a ++ [b] ++ c) = find_match env s v (b::a++c) `,
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

(* characterisation of reordering operations as rules *)

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
    \\ imp_res_tac const_cons_sep_reord \\ fs[])

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

(* main lemma: find_match semantics preserved by compilation *)

val const_cons_fst_find_match = Q.store_thm("const_cons_fst_find_match",
    `find_match refs v pes <> Match_type_error ==>
        find_match refs v pes = find_match refs v (const_cons_fst pes)`,
    METIS_TAC [find_match_preserved_reord_RTC, const_cons_fst_reord])

(* semantic auxiliaries respect transformation of values *)

val pmatch_nil_rwt =
    pmatch_nil |> CONJUNCT1
    |> ADD_ASSUM``(env:(tvarN,flatSem$v) alist) <> []`` |> DISCH_ALL

val pmatch_nil_imp = Q.store_thm( "pmatch_nil_imp",
    ` pmatch refs p err_v [] = res
            ==> pmatch refs p err_v env = map_match (combin$C $++ env) res`,
    METIS_TAC [pmatch_nil])

val pmatch_compile = Q.store_thm("pmatch_compile",
  `(! refs p err_v env.
      pmatch (MAP compile_store_v refs) p (compile_v err_v) (compile_env env) =
      map_match (compile_env) (pmatch refs p err_v env)) /\
   (! refs ps vs env.
      pmatch_list (MAP compile_store_v refs) ps (MAP compile_v vs) (compile_env env) =
      map_match (compile_env) (pmatch_list refs ps vs env)) `,
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
  ))

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
   \\ rw [])

val find_match_imp_compile = Q.store_thm("find_match_imp_compile",
  `find_match s.refs v pes = Match (env',e) ==>
   find_match (compile_state s).refs (compile_v v)
       (MAP (\(p,e). (p,HD(compile[e]))) pes) =
           Match (compile_env env', HD(compile[e]))`,
  strip_tac \\
  (Q.GENL[`f`,`refs`,`v`,`pes`]find_match_compile
   |> Q.ISPECL_THEN[`\e. HD(compile[e])`,`s.refs`,`v`,`pes`]mp_tac) \\
  simp[] \\
  disch_then(SUBST1_TAC o SYM) \\
  rpt(AP_TERM_TAC ORELSE AP_THM_TAC) \\
  simp[FUN_EQ_THM,FORALL_PROD]);

val do_opapp_compile = Q.store_thm("do_opapp_compile[simp]",
  `do_opapp (MAP compile_v as) =
    OPTION_MAP (λ(env,e). (compile_env env, HD (compile [e]))) (do_opapp as)`,
  rw[do_opapp_def]
  \\ every_case_tac
  \\ fs[semanticPrimitivesPropsTheory.find_recfun_ALOOKUP,build_rec_env_merge]
  \\ rw[] \\ fsrw_tac[ETA_ss][ALOOKUP_MAP3,MAP_MAP_o,o_DEF,UNCURRY]);

val do_eq_compile = Q.store_thm("do_eq_compile[simp]",
  `(∀v1 v2. do_eq (compile_v v1) (compile_v v2) = do_eq v1 v2) ∧
   (∀v1 v2. do_eq_list (MAP compile_v v1) (MAP compile_v v2) = do_eq_list v1 v2)`,
  ho_match_mp_tac do_eq_ind
  \\ srw_tac[ETA_ss][do_eq_def]
  \\ every_case_tac \\ fs[]);

val store_v_same_type_compile = Q.store_thm("store_v_same_type_compile[simp]",
  `(store_v_same_type (compile_store_v v1) v2 ⇔ store_v_same_type v1 v2) ∧
   (store_v_same_type v1 (compile_store_v v2) ⇔ store_v_same_type v1 v2) ∧
   (store_v_same_type (Refv (compile_v x1)) v2 ⇔ store_v_same_type (Refv x1) v2) ∧
   (store_v_same_type v1 (Refv (compile_v x2)) ⇔ store_v_same_type v1 (Refv x2))`,
  Cases_on`v1` \\ Cases_on`v2` \\ EVAL_TAC);

val v_to_char_list_compile = Q.store_thm("v_to_char_list_compile[simp]",
  `∀ls. v_to_char_list (compile_v ls) = v_to_char_list ls`,
  ho_match_mp_tac v_to_char_list_ind \\ rw[v_to_char_list_def]);

val v_to_list_compile = Q.store_thm("v_to_list_compile[simp]",
  `∀v. v_to_list (compile_v v) = OPTION_MAP (MAP compile_v) (v_to_list v)`,
  ho_match_mp_tac v_to_list_ind \\ rw[v_to_list_def]
  \\ every_case_tac \\ fs[]);

val vs_to_strings_compile = Q.store_thm("vs_to_strings_compile[simp]",
  `∀vs. vs_to_string (MAP compile_v vs) = vs_to_string vs`,
  ho_match_mp_tac vs_to_string_ind \\ rw[vs_to_string_def]);

val do_app_compile = Q.store_thm("do_app_compile[simp]",
  `do_app (compile_state s) op (MAP compile_v as) =
   OPTION_MAP (λ(s,r). (compile_state s, map_result compile_v compile_v r)) (do_app s op as)`,
  Cases_on`do_app s op as`
  \\ pop_assum(strip_assume_tac o SIMP_RULE(srw_ss())[do_app_cases,do_app_cases_none])
  \\ rw[]
  \\ fs[do_app_def,
        semanticPrimitivesTheory.store_assign_def,
        semanticPrimitivesTheory.store_alloc_def,
        semanticPrimitivesTheory.store_lookup_def,
        EL_MAP,compile_store_v_def]
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ EVAL_TAC
  \\ rfs[EL_MAP,semanticPrimitivesTheory.store_v_same_type_def,
         LUPDATE_MAP,compile_store_v_def,map_replicate]
  \\ every_case_tac \\ fs[compile_store_v_def]);

(* main results *)

val compile_evaluate = Q.store_thm( "compile_evaluate",
  `(!env ^s es s1 r1.
      (evaluate env s es = (s1, r1)) /\
      r1 <> Rerr (Rabort Rtype_error) ==>
      (evaluate (compile_env env) (compile_state s) (compile es) =
          (compile_state s1, map_result (MAP compile_v) compile_v r1)
          ))
     /\
      (!(env:(tvarN, flatSem$v) alist) ^s (err_v:flatSem$v) (pes:(pat,flatLang$exp)alist) s1 r1.
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
      \\ rfs [compile_reverse]
      \\ rw [MAP_REVERSE]
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
      every_case_tac  \\ fs [compile_reverse] \\ rfs [] \\ rw[] \\
      fs[GSYM MAP_REVERSE,dec_clock_compile_state] \\ rw[] \\
      TRY(hd_compile_sing_tac \\ fs[]) \\
      fs[list_result_map_result] )
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
   >- (
     fs[build_rec_env_merge,MAP_MAP_o,o_DEF,UNCURRY] \\
     `∃e'. compile [e] = [e']` by METIS_TAC[compile_sing] \\
     fs[]
   )
   >- (
     fs[compile_state_def,MAP_GENLIST]
     )
   >-(
     fs [pmatch_compile]
     \\ every_case_tac \\ fs []
     \\ hd_compile_sing_tac \\ fs []
     \\ rfs []
    )
);

val compile_evaluate_rwt = Q.store_thm("compile_evaluate_rwt",
  `SND (evaluate env st es) ≠ Rerr (Rabort Rtype_error) ⇒
   evaluate (compile_env env) (compile_state st) (compile es) =
     (compile_state ## map_result (MAP compile_v) compile_v) (evaluate env st es)`,
  Cases_on`evaluate env st es` \\ rw[] \\ imp_res_tac compile_evaluate);

val compile_semantics = Q.store_thm("compile_semantics",
  `semantics env (st:'ffi flatSem$state) es ≠ Fail ⇒
   semantics (compile_env env) (compile_state st) (compile es) = semantics env st es`,
  simp[semantics_def,compile_state_with_clock] \\
  IF_CASES_TAC \\ fs[compile_evaluate_rwt] \\
  DEEP_INTRO_TAC some_intro \\ fs[] \\ rw[] \\
  DEEP_INTRO_TAC some_intro \\ fs[] \\ rw[] \\
  fs[PAIR_MAP] \\ rveq \\ fs[]
  \\ TRY ( qexists_tac`k` \\ simp[] \\ CASE_TAC \\ fs[] )
  \\ TRY (
    first_x_assum(qspec_then`k`mp_tac) \\ simp[]
    \\ spose_not_then strip_assume_tac \\ fs[]
    \\ NO_TAC)
  \\ qmatch_goalsub_abbrev_tac`FST p`
  \\ Cases_on`p` \\ fs[markerTheory.Abbrev_def]
  \\ pop_assum (assume_tac o SYM)
  \\ qmatch_assum_rename_tac`evaluate _ (st with clock := k1) _ = (s,r)`
  \\ qmatch_assum_rename_tac`evaluate _ (st with clock := k2) _ = (s',r')`
  \\ qspecl_then[`k1`,`k2`]strip_assume_tac LESS_EQ_CASES
  \\ rpt(pop_assum mp_tac)
  \\ map_every qid_spec_tac [`k1`,`k2`,`s`,`r`,`s'`,`r'`,`outcome`,`outcome'`]
     THEN_LT USE_SG_THEN (fn th => metis_tac[th]) 1 2
  \\ rpt gen_tac \\ rpt(disch_then strip_assume_tac)
  \\ fs[LESS_EQ_EXISTS] \\ rveq
  \\ qmatch_asmsub_rename_tac`st with clock := kk + p`
  \\ qspecl_then[`env`,`st with clock := kk`,`es`,`p`]strip_assume_tac
       (CONJUNCT1 evaluate_add_to_clock_io_events_mono)
  \\ rfs[]
  \\ every_case_tac \\ fs[]
  \\ qspecl_then[`p`,`env`,`st with clock := kk`,`es`]mp_tac
       (Q.GEN`extra`(CONJUNCT1 evaluate_add_to_clock))
  \\ fs[]
  \\ CCONTR_TAC \\ fs[]);

(* syntactic results *)

val _ = bring_to_front_overload"elist_globals"{Thy="flatProps",Name="elist_globals"};

val elist_globals_eq_empty = Q.store_thm("elist_globals_eq_empty",
  `elist_globals l = {||} ⇔ ∀e. MEM e l ⇒ set_globals e = {||}`,
  Induct_on`l` \\ rw[set_globals_def] \\ rw[EQ_IMP_THM] \\ rw[]);

val compile_elist_globals_eq_empty = Q.store_thm("compile_elist_globals_eq_empty",
  `∀es. elist_globals es = {||} ⇒ elist_globals (compile es) = {||}`,
  ho_match_mp_tac compile_ind
  \\ rw[compile_def]
  \\ TRY hd_compile_sing_tac \\ fs[]
  \\ fs[elist_globals_append]
  \\ TRY hd_compile_sing_tac \\ fs[]
  \\ fs[elist_globals_eq_empty]
  \\ fs[MEM_MAP,MAP_MAP_o,UNCURRY,o_DEF,PULL_EXISTS,FORALL_PROD]
  \\ rw[] \\ imp_res_tac const_cons_fst_MEM
  \\ res_tac
  \\ hd_compile_sing_tac \\ fs[]);

val compile_set_globals_eq_empty = Q.store_thm("compile_set_globals_eq_empty",
  `set_globals e = {||} ⇒ set_globals (HD (compile [e])) = {||}`,
  qspec_then`[e]`mp_tac compile_elist_globals_eq_empty
  \\ rw[] \\ fs[] \\ hd_compile_sing_tac \\ fs[]);

val compile_esgc_free = Q.store_thm("compile_esgc_free",
  `∀es. EVERY esgc_free es ⇒ EVERY esgc_free (compile es)`,
  ho_match_mp_tac compile_ind
  \\ rw[compile_def] \\ fs[]
  \\ hd_compile_sing_tac \\ fs[]
  \\ fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,elist_globals_eq_empty]
  \\ fs[MEM_MAP,MAP_MAP_o,PULL_EXISTS,FORALL_PROD]
  \\ rw[]
  \\ TRY(
    match_mp_tac compile_set_globals_eq_empty
    \\ res_tac )
  \\ METIS_TAC[compile_sing,HD,MEM,const_cons_fst_MEM,compile_set_globals_eq_empty]);

val const_cons_sep_sub_bag = Q.store_thm("const_cons_sep_sub_bag",
  `∀pes a const_cons c a'.
    const_cons_sep pes a const_cons = (c,a') ⇒
    elist_globals (MAP SND (c ++ REVERSE a')) ≤
    elist_globals (MAP SND (const_cons ++ REVERSE a ++ pes))`,
  Induct_on`pes` \\ rw[const_cons_sep_def]
  \\ fs[elist_globals_append,REVERSE_APPEND]
  \\ fs[SUB_BAG_UNION]
  \\ first_x_assum drule \\ rw[elist_globals_append]
  \\ metis_tac[SUB_BAG_UNION,ASSOC_BAG_UNION,COMM_BAG_UNION]);

val const_cons_fst_sub_bag = Q.store_thm("const_cons_fst_sub_bag",
  `elist_globals (MAP SND (const_cons_fst pes)) ≤
   elist_globals (MAP SND pes)`,
  rw[const_cons_fst_def]
  \\ pairarg_tac \\ fs[]
  \\ imp_res_tac const_cons_sep_sub_bag \\ fs[])

val const_cons_fst_distinct_globals = Q.store_thm("const_cons_fst_distinct_globals",
  `BAG_ALL_DISTINCT (elist_globals (MAP SND pes)) ⇒
   BAG_ALL_DISTINCT (elist_globals (MAP SND (const_cons_fst pes)))`,
  METIS_TAC[const_cons_fst_sub_bag,BAG_ALL_DISTINCT_SUB]);

val compile_sub_bag = Q.store_thm("compile_sub_bag",
  `∀es. (elist_globals (compile es)) ≤ (elist_globals es)`,
  ho_match_mp_tac compile_ind
  \\ rw[compile_def]
  \\ TRY hd_compile_sing_tac \\ fs[SUB_BAG_UNION,elist_globals_append]
  \\ TRY hd_compile_sing_tac \\ fs[SUB_BAG_UNION]
  \\ fs[MAP_MAP_o,UNCURRY,o_DEF] \\ fs[LAMBDA_PROD]
  \\ FIRST (map (fn th => match_mp_tac (MP_CANON th) \\ conj_tac >- simp[]) (CONJUNCTS SUB_BAG_UNION))
  \\ TRY (
    ntac 3 (pop_assum kall_tac)
    \\ Induct_on`funs` \\ fs[FORALL_PROD] \\ rw[]
    \\ hd_compile_sing_tac \\ fs[]
    \\ first_x_assum(fn th => mp_tac th \\ impl_tac >- METIS_TAC[])
    \\ fsrw_tac[DNF_ss][SUB_BAG_UNION] )
  THEN_LT USE_SG_THEN ACCEPT_TAC 1 2
  \\ match_mp_tac SUB_BAG_TRANS
  \\ qexists_tac`elist_globals (MAP SND (const_cons_fst pes))`
  \\ (reverse conj_tac >- METIS_TAC[const_cons_fst_sub_bag])
  \\ ntac 3 (pop_assum kall_tac)
  \\ pop_assum mp_tac
  \\ Q.SPEC_TAC(`const_cons_fst pes`,`ls`)
  \\ Induct \\ rw[]
  \\ pairarg_tac \\ fs[]
  \\ hd_compile_sing_tac \\ fs[]
  \\ first_x_assum (fn th => mp_tac th \\ impl_tac >- METIS_TAC[])
  \\ fsrw_tac[DNF_ss][UNCURRY,SUB_BAG_UNION]);

val compile_distinct_globals = Q.store_thm("compile_distinct_globals",
  `BAG_ALL_DISTINCT (elist_globals es) ⇒ BAG_ALL_DISTINCT (elist_globals (compile es))`,
  METIS_TAC[compile_sub_bag,BAG_ALL_DISTINCT_SUB]);

val () = export_theory();
