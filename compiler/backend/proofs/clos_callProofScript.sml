open preamble match_goal dep_rewrite
     closSemTheory closPropsTheory
     clos_callTheory
     db_varsTheory clos_freeProofTheory;

val _ = new_theory"clos_callProof";

(* TODO: move *)

val TAKE_MAP = Q.store_thm("TAKE_MAP",
  `∀ls n f. TAKE n (MAP f ls) = MAP f (TAKE n ls)`,
  Induct \\ rw[]);

val IS_SUFFIX_TRANS = Q.store_thm("IS_SUFFIX_TRANS",
  `∀l1 l2 l3. IS_SUFFIX l1 l2 ∧ IS_SUFFIX l2 l3 ⇒ IS_SUFFIX l1 l3`,
  rw[IS_SUFFIX_APPEND] \\ metis_tac[APPEND_ASSOC]);

val ALL_DISTINCT_FLAT_EVERY = Q.store_thm("ALL_DISTINCT_FLAT_EVERY",
  `∀ls. ALL_DISTINCT (FLAT ls) ⇒ EVERY ALL_DISTINCT ls`,
  Induct \\ simp[ALL_DISTINCT_APPEND]);

val IN_EVEN = SIMP_CONV std_ss [IN_DEF] ``x ∈ EVEN``;

val v_size_lemma = prove(
  ``MEM (v:closSem$v) vl ⇒ v_size v < v1_size vl``,
  Induct_on `vl` >> dsimp[v_size_def] >> rpt strip_tac >>
  res_tac >> simp[]);

val list_to_num_set_append = Q.store_thm("list_to_num_set_append",
  `∀l1 l2. list_to_num_set (l1 ++ l2) = union (list_to_num_set l1) (list_to_num_set l2)`,
  Induct \\ rw[list_to_num_set_def]
  \\ rw[Once insert_union]
  \\ rw[Once insert_union,SimpRHS]
  \\ rw[union_assoc])

val subspt_domain_SUBSET = Q.store_thm("subspt_domain_SUBSET",
  `subspt s1 s2 ⇒ domain s1 ⊆ domain s2`,
  rw[subspt_def,SUBSET_DEF]);

val evaluate_add_clock =
  evaluate_add_to_clock
  |> SIMP_RULE (srw_ss()) []
  |> CONJUNCT1 |> GEN_ALL
  |> REWRITE_RULE[GSYM AND_IMP_INTRO]

val DISJOINT_IMAGE_SUC = store_thm("DISJOINT_IMAGE_SUC",
  ``DISJOINT (IMAGE SUC x) (IMAGE SUC y) <=> DISJOINT x y``,
  fs [IN_DISJOINT] \\ metis_tac [DECIDE ``(SUC n = SUC m) <=> (m = n)``]);

val IMAGE_SUC_SUBSET_UNION = store_thm("IMAGE_SUC_SUBSET_UNION",
  ``IMAGE SUC x SUBSET IMAGE SUC y UNION IMAGE SUC z <=>
    x SUBSET y UNION z``,
  fs [SUBSET_DEF] \\ metis_tac [DECIDE ``(SUC n = SUC m) <=> (m = n)``]);

val ALL_DISTINCT_APPEND_APPEND_IMP = store_thm("ALL_DISTINCT_APPEND_APPEND_IMP",
  ``ALL_DISTINCT (xs ++ ys ++ zs) ==>
    ALL_DISTINCT (xs ++ ys) /\ ALL_DISTINCT (xs ++ zs) /\ ALL_DISTINCT (ys ++ zs)``,
  fs [ALL_DISTINCT_APPEND]);

(* -- *)

(* value relation *)

val subg_def = Define`
  subg g0 g1 ⇔
    subspt (FST g0) (FST g1) ∧
    (* IS_SUFFIX (SND g1) (SND g0) ∧ *)
    (∀k v. ALOOKUP (SND g0) k = SOME v ⇒ ALOOKUP (SND g1) k = SOME v) ∧
    ALL_DISTINCT (MAP FST (SND g1))`;

val subg_refl = Q.store_thm("subg_refl",
  `∀g. ALL_DISTINCT (MAP FST (SND g)) ⇒ subg g g`,
  rw[subg_def]);

val subg_trans = Q.store_thm("subg_trans",
  `∀g1 g2 g3. subg g1 g2 ∧ subg g2 g3 ⇒ subg g1 g3`,
  rw[subg_def] \\ metis_tac[subspt_trans,IS_SUFFIX_TRANS]);

val wfg'_def = Define`
  wfg' g ⇔
    domain (FST g) ⊆ EVEN ∧
    EVERY (λ(n,p). ∀v. has_var v (SND (free [p])) ⇒ v < n) (MAP SND (SND g)) ∧
    set (MAP FST (SND g)) ⊆ IMAGE SUC (domain (FST g))`;

val wfg_def = Define`
  wfg g ⇔
    domain (FST g) ⊆ EVEN ∧
    EVERY (λ(n,p). ∀v. has_var v (SND (free [p])) ⇒ v < n) (MAP SND (SND g)) ∧
    set (MAP FST (SND g)) = IMAGE SUC (domain (FST g)) ∧
    ALL_DISTINCT (MAP FST (SND g))`;

val recclosure_rel_def = Define`
  recclosure_rel g l g0 loc fns1 fns2 ⇔
     EVEN loc ∧
     every_Fn_SOME (MAP SND fns1) ∧ every_Fn_vs_NONE (MAP SND fns1) ∧
     set (code_locs (MAP SND fns1)) ⊆ EVEN ∧
     DISJOINT (set (GENLIST (λi. 2*i+loc) (LENGTH fns1))) (set (code_locs (MAP SND fns1))) ∧
     ALL_DISTINCT (code_locs (MAP SND fns1)) ∧ wfg g0 ∧
     DISJOINT (IMAGE SUC (set (code_locs (MAP SND fns1)))) (set (MAP FST (SND g0))) ∧
     DISJOINT (set (GENLIST (λi. 2*i+loc+1) (LENGTH fns1))) (set (MAP FST (SND g0))) ∧
     let (es,new_g) = calls (MAP SND fns1) (insert_each loc (LENGTH fns1) g0) in
     if EVERY2 (λ(n,_) p. ∀v. has_var v (SND (free [p])) ⇒ v < n) fns1 es
     then
       fns2 = calls_list loc fns1 ∧
       subg (code_list loc (ZIP (MAP FST fns1,es)) new_g) g ∧
       set (code_locs (MAP SND fns1)) DIFF domain (FST new_g) ⊆ l
     else
       let (es,new_g) = calls (MAP SND fns1) g0 in
       fns2 = ZIP (MAP FST fns1, es) ∧
       subg new_g g ∧
       set (code_locs (MAP SND fns1)) DIFF domain (FST new_g) ⊆ l ∧
       set (GENLIST (λi. 2*i+loc) (LENGTH fns1)) ⊆ l`;

val v_rel_def = tDefine"v_rel"`
  (v_rel g l (Number i) v ⇔ v = Number i) ∧
  (v_rel g l (Word64 w) v ⇔ v = Word64 w) ∧
  (v_rel g l (Block n vs) v ⇔
    ∃vs'. v = Block n vs' ∧ LIST_REL (v_rel g l) vs vs') ∧
  (v_rel g l (RefPtr n) v ⇔ v = RefPtr n) ∧
  (v_rel g l (Closure loco vs1 env1 n bod1) v ⇔
     ∃g0 loc vs2 env2 bod2.
       recclosure_rel g l g0 loc [(n,bod1)] [(n,bod2)] ∧
       v = Closure (SOME loc) vs2 env2 n bod2 ∧ loco = SOME loc ∧
       LIST_REL (v_rel g l) vs1 vs2 ∧ LIST_REL (v_rel g l) env1 env2) ∧
  (v_rel g l (Recclosure loco vs1 env1 fns1 i) v ⇔
     ∃g0 loc vs2 env2 fns2.
       recclosure_rel g l g0 loc fns1 fns2 ∧
       v = Recclosure (SOME loc) vs2 env2 fns2 i ∧ loco = SOME loc ∧
       LIST_REL (v_rel g l) vs1 vs2 ∧ LIST_REL (v_rel g l) env1 env2)`
  (WF_REL_TAC `measure (v_size o FST o SND o SND)` >> simp[v_size_def] >>
   rpt strip_tac >> imp_res_tac v_size_lemma >> simp[]);

val v_rel_ind = theorem"v_rel_ind";

val code_includes_def = Define`
  code_includes al code ⇔
    ∀k v. ALOOKUP al k = SOME v ⇒ FLOOKUP code k = SOME v`;

val state_rel_def = Define`
  state_rel g l (s:'ffi closSem$state) (t:'ffi closSem$state) ⇔
    (s.ffi = t.ffi) ∧
    (s.clock = t.clock) ∧
    LIST_REL (OPTREL (v_rel g l)) s.globals t.globals ∧
    fmap_rel (ref_rel (v_rel g l)) s.refs t.refs ∧
    s.code = FEMPTY ∧ code_includes (SND g) t.code`;

val state_rel_clock = Q.store_thm("state_rel_clock",
  `state_rel g l s t ⇒ s.clock = t.clock`,
  rw[state_rel_def]);

val state_rel_with_clock = Q.store_thm("state_rel_with_clock",
  `state_rel g l s t ⇒ state_rel g l (s with clock := k) (t with clock := k)`,
  rw[state_rel_def]);

(* syntactic properties of compiler *)

val calls_length = Q.store_thm("calls_length",
  `∀xs g0 ys g. calls xs g0 = (ys,g) ⇒ LENGTH ys = LENGTH xs`,
  ho_match_mp_tac calls_ind
  \\ rw[calls_def] \\ rw[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
  \\ every_case_tac \\ fs[] \\ rw[]);

val calls_sing = Q.store_thm("calls_sing",
  `∀x g0 ys g. calls [x] g0 = (ys,g) ⇒ ?y. ys = [y]`,
  rw [] \\ imp_res_tac calls_length \\ fs []
  \\ Cases_on `ys` \\ fs [LENGTH_NIL] );

val FST_code_list = Q.store_thm("FST_code_list[simp]",
  `∀loc fns g. FST (code_list loc fns g) = FST g`,
  ho_match_mp_tac code_list_ind
  \\ rw[code_list_def]);

val SND_insert_each = Q.store_thm("SND_insert_each[simp]",
  `∀p n g. SND (insert_each p n g) = SND g`,
  ho_match_mp_tac insert_each_ind
  \\ rw[insert_each_def]);

val calls_list_MAPi = Q.store_thm("calls_list_MAPi",
  `∀loc. calls_list loc = MAPi (λi p. (FST p, Call 0 (loc+2*i+1) (GENLIST Var (FST p))))`,
  simp[FUN_EQ_THM]
  \\ CONV_TAC(SWAP_FORALL_CONV)
  \\ Induct \\ simp[calls_list_def]
  \\ Cases \\ simp[calls_list_def]
  \\ simp[o_DEF,ADD1,LEFT_ADD_DISTRIB]
  \\ rw[] \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ simp[FUN_EQ_THM]);

val domain_FST_insert_each = Q.store_thm("domain_FST_insert_each",
  `∀p n g. domain (FST (insert_each p n g)) = set (GENLIST (λi. 2 * i + p) n) ∪ domain (FST g)`,
  ho_match_mp_tac insert_each_ind
  \\ rw[insert_each_def,GENLIST_CONS,o_DEF,ADD1,LEFT_ADD_DISTRIB]
  \\ simp[EXTENSION,MEM_GENLIST]
  \\ metis_tac[ADD_ASSOC,ADD_COMM]);

val SND_code_list_change = Q.store_thm("SND_code_list_change",
  `∀loc fns g g'. SND g = SND g' ⇒
    SND (code_list loc fns g) = SND (code_list loc fns g')`,
  ho_match_mp_tac code_list_ind
  \\ rw[code_list_def]
  \\ Cases_on`g'` \\ rw[code_list_def]
  \\ fs[FORALL_PROD]);

val MAP_FST_code_list = Q.store_thm("MAP_FST_code_list",
  `∀loc fns g.
    MAP FST (SND (code_list loc fns g)) =
    REVERSE (GENLIST (λi. loc + i*2 + 1) (LENGTH fns)) ++ MAP FST (SND g)`,
  ho_match_mp_tac code_list_ind
  \\ rw[code_list_def]
  \\ rw[GENLIST_CONS,MAP_REVERSE]
  \\ rw[o_DEF,ADD1]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ rw[FUN_EQ_THM]);

val SND_code_list_ZIP = Q.store_thm("SND_code_list_ZIP",
  `∀loc fns g. SND (code_list loc fns g) =
   REVERSE(ZIP (GENLIST ($+ (loc+1) o $* 2) (LENGTH fns), fns)) ++ (SND g)`,
  ho_match_mp_tac code_list_ind
  \\ rw[code_list_def,GENLIST_CONS]
  \\ simp[REVERSE_ZIP,o_DEF,ADD1,LEFT_ADD_DISTRIB]);

val ALOOKUP_code_list = Q.store_thm("ALOOKUP_code_list",
  `∀loc fns g k.
    ALOOKUP (SND (code_list loc fns g)) k =
    case some i. i < LENGTH fns ∧ k = loc + 2*i+1 of
    | SOME i => SOME (EL i fns)
    | NONE => ALOOKUP (SND g) k`,
  rw[SND_code_list_ZIP,ALOOKUP_APPEND]
  \\ DEP_REWRITE_TAC[alookup_distinct_reverse]
  \\ conj_asm1_tac
  >- simp[MAP_ZIP,ALL_DISTINCT_GENLIST]
  \\ BasicProvers.TOP_CASE_TAC
  >- (
    fs[ALOOKUP_ZIP_FAIL,MEM_GENLIST]
    \\ DEEP_INTRO_TAC some_intro
    \\ simp[] \\ metis_tac[] )
  \\ drule (GEN_ALL ALOOKUP_ALL_DISTINCT_MEM)
  \\ simp[MEM_ZIP,PULL_EXISTS]
  \\ imp_res_tac ALOOKUP_MEM \\ fs[MEM_ZIP]
  \\ DEEP_INTRO_TAC some_intro \\ rw[]);

val insert_each_subspt = Q.store_thm("insert_each_subspt",
  `∀p n g. subspt (FST g) (FST (insert_each p n g))`,
  ho_match_mp_tac insert_each_ind
  \\ rw[insert_each_def]
  \\ fs[subspt_def,lookup_insert]
  \\ rw[] \\ fs[domain_lookup]);

val code_list_IS_SUFFIX = Q.store_thm("code_list_IS_SUFFIX",
  `∀loc fns g. IS_SUFFIX (SND (code_list loc fns g)) (SND g)`,
  ho_match_mp_tac code_list_ind
  \\ rw[code_list_def] \\ fs[IS_SUFFIX_APPEND]);

val calls_subspt = Q.store_thm("calls_subspt",
  `∀xs g0 ys g. calls xs g0 = (ys,g) ⇒ subspt (FST g0) (FST g)`,
  ho_match_mp_tac calls_ind
  \\ rw[calls_def] \\ rw[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ metis_tac[subspt_trans,insert_each_subspt]);

val calls_IS_SUFFIX = Q.store_thm("calls_IS_SUFFIX",
  `∀xs g0 ys g. calls xs g0 = (ys,g) ⇒ IS_SUFFIX (SND g) (SND g0)`,
  ho_match_mp_tac calls_ind
  \\ rw[calls_def] \\ rw[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ metis_tac[IS_SUFFIX_TRANS,IS_SUFFIX_CONS,code_list_IS_SUFFIX]);

val calls_add_SUC_code_locs = Q.store_thm("calls_add_SUC_code_locs",
  `∀xs g0 ys g. calls xs g0 = (ys,g) ⇒
    set (MAP FST (SND g)) ⊆
    set (MAP FST (SND g0)) ∪ IMAGE SUC (set (code_locs xs))`,
  ho_match_mp_tac calls_ind
  \\ rw[calls_def,code_locs_def]
  \\ rpt (pairarg_tac \\ fs[]) \\ rw[]
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ imp_res_tac calls_length
  \\ fs[MAP_FST_code_list,LIST_TO_SET_GENLIST]
  \\ fs[SUBSET_DEF,PULL_EXISTS,ADD1]
  \\ metis_tac[]);

val calls_ALL_DISTINCT = Q.store_thm("calls_ALL_DISTINCT",
  `∀xs g0 ys g.
    calls xs g0 = (ys,g) ∧ ALL_DISTINCT (MAP FST (SND g0)) ∧
    ALL_DISTINCT (code_locs xs) ∧
    DISJOINT (IMAGE SUC (set (code_locs xs))) (set (MAP FST (SND g0)))
    ⇒ ALL_DISTINCT (MAP FST (SND g))`,
  ho_match_mp_tac calls_ind
  \\ rw[calls_def] \\ rw[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
  \\ fs[code_locs_def]
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ TRY (
    first_x_assum match_mp_tac
    \\ imp_res_tac calls_add_SUC_code_locs
    \\ fs[IN_DISJOINT,SUBSET_DEF]
    \\ fs[ALL_DISTINCT_APPEND]
    \\ TRY (
      conj_tac >- (
        first_x_assum match_mp_tac
        \\ spose_not_then strip_assume_tac \\ rw[]
        \\ imp_res_tac calls_IS_SUFFIX
        \\ fs[IS_SUFFIX_APPEND]
        \\ metis_tac[MEM_APPEND,numTheory.INV_SUC] ))
    \\ spose_not_then strip_assume_tac \\ rw[]
    \\ imp_res_tac calls_IS_SUFFIX
    \\ fs[IS_SUFFIX_APPEND]
    \\ metis_tac[MEM_APPEND,numTheory.INV_SUC] )
  \\ TRY (
    rename1`MEM 1n _`
    \\ imp_res_tac calls_add_SUC_code_locs
    \\ fs[ALL_DISTINCT_APPEND,SUBSET_DEF]
    \\ metis_tac[ONE,numTheory.INV_SUC] )
  \\ TRY (
    rename1`MEM (_ + 1n) _`
    \\ imp_res_tac calls_add_SUC_code_locs
    \\ fs[ALL_DISTINCT_APPEND,SUBSET_DEF,ADD1]
    \\ metis_tac[ADD1,numTheory.INV_SUC] )
  THEN1 (
    fs[MAP_FST_code_list,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND,
       ALL_DISTINCT_GENLIST,MEM_GENLIST,PULL_EXISTS]
    \\ imp_res_tac LIST_REL_LENGTH \\ rw[]
    \\ imp_res_tac calls_IS_SUFFIX
    \\ imp_res_tac calls_add_SUC_code_locs
    \\ fs[IS_SUFFIX_APPEND,SUBSET_DEF]
    \\ fs[IN_DISJOINT,MEM_GENLIST]
    \\ rfs[GSYM ADD1]
    \\ metis_tac[numTheory.INV_SUC] )
  \\ fs[MAP_FST_code_list,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND,
        ALL_DISTINCT_GENLIST,MEM_GENLIST,PULL_EXISTS]
  \\ imp_res_tac LIST_REL_LENGTH \\ rw[]
  \\ imp_res_tac calls_IS_SUFFIX
  \\ imp_res_tac calls_add_SUC_code_locs
  \\ fs[IS_SUFFIX_APPEND,SUBSET_DEF]
  \\ fs[IN_DISJOINT,MEM_GENLIST]
  \\ reverse conj_asm2_tac >- metis_tac[numTheory.INV_SUC,ADD1,ADD_ASSOC]
  \\ rfs[]
  \\ spose_not_then strip_assume_tac
  \\ res_tac \\ fs[ADD1]
  \\ res_tac
  \\ first_x_assum(qspec_then`i`mp_tac)
  \\ simp[]);

val calls_subg = Q.store_thm("calls_subg",
  `∀xs g0 ys g.
    calls xs g0 = (ys,g) ∧
    ALL_DISTINCT (MAP FST (SND g0)) ∧
    ALL_DISTINCT (code_locs xs) ∧
    DISJOINT (IMAGE SUC (set (code_locs xs))) (set (MAP FST (SND g0)))
    ⇒ subg g0 g`,
  simp[subg_def]
  \\ rpt gen_tac \\ strip_tac
  \\ REWRITE_TAC[CONJ_ASSOC]
  \\ reverse conj_asm2_tac
  >- metis_tac[calls_ALL_DISTINCT]
  \\ conj_tac >- metis_tac[calls_subspt]
  \\ imp_res_tac calls_IS_SUFFIX
  \\ fs[IS_SUFFIX_APPEND]
  \\ simp[ALOOKUP_APPEND]
  \\ rw[]
  \\ BasicProvers.CASE_TAC
  \\ fs[ALL_DISTINCT_APPEND]
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs[MEM_MAP,PULL_EXISTS]
  \\ res_tac \\ fs[]
  \\ metis_tac[FST]);

val calls_domain = Q.store_thm("calls_domain",
  `∀xs g0 ys g. calls xs g0 = (ys,g) ⇒
    domain (FST g) ⊆ domain (FST g0) ∪ IMAGE PRE (set (MAP FST (SND g)))`,
  ho_match_mp_tac calls_ind
  \\ rw[calls_def]
  \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
  \\ fs[SUBSET_DEF] \\ rw[]
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ TRY (
    imp_res_tac calls_subspt
    \\ imp_res_tac calls_IS_SUFFIX
    \\ fs[IS_SUFFIX_APPEND] \\ fs[]
    \\ metis_tac[])
  \\ imp_res_tac calls_length
  \\ fs[domain_FST_insert_each,MAP_FST_code_list,MEM_GENLIST]
  \\ metis_tac[EVAL``PRE 1``,prim_recTheory.PRE,ADD1,ADD_ASSOC]);

val wfg'_insert_each = Q.store_thm("wfg'_insert_each",
  `∀n g loc. wfg' g ∧ (0 < n ⇒ EVEN loc) ⇒ wfg' (insert_each loc n g)`,
  Induct \\ Cases \\ rw[insert_each_def]
  \\ first_x_assum match_mp_tac
  \\ fs[wfg'_def,SUBSET_DEF,IN_EVEN]
  \\ metis_tac[EVEN_ADD,EVAL``EVEN 2``]);

val wfg'_code_list = Q.store_thm("wfg'_code_list",
  `∀ls g loc.
      wfg' g ∧ set (GENLIST (λi. loc + 2 * i) (LENGTH ls)) ⊆ domain (FST g) ∧
        EVERY (λ(n,p). ∀v. has_var v (SND (free[p])) ⇒ v < n) ls
      ⇒ wfg' (code_list loc ls g)`,
  rw[wfg'_def,SUBSET_DEF,MEM_GENLIST,MAP_FST_code_list]
  >- (
    simp[SND_code_list_ZIP]
    \\ simp[MAP_REVERSE,EVERY_REVERSE,MAP_ZIP] )
  >- (
    fs[ADD1,PULL_EXISTS]
    \\ metis_tac[ADD_ASSOC] )
  \\ metis_tac[]);

val closed_Fn = Q.store_thm("closed_Fn",
  `closed (Fn loco vs args e) ⇔
   ∀v. has_var v (SND (free [e])) ⇒ v < args`,
  rw[closed_def]
  \\ qspec_then`[e]`mp_tac free_thm
  \\ simp[] \\ pairarg_tac \\ fs[]
  \\ rw[]
  \\ fs[clos_freeTheory.free_def]
  \\ rw[EQ_IMP_THM]
  >- (
    spose_not_then strip_assume_tac
    \\ fs[NOT_LESS]
    \\ fs[LESS_EQ_EXISTS] \\ rveq
    \\ fs[lookup_db_to_set]
    \\ metis_tac[lookup_db_to_set_Shift,ADD_COMM,lookup_def,NOT_SOME_NONE] )
  \\ `wf (db_to_set (Shift args l))` by simp[wf_db_to_set]
  \\ simp[spt_eq_thm,wf_def]
  \\ simp[lookup_db_to_set_Shift]
  \\ simp[lookup_def]
  \\ rw[]
  \\ Cases_on`lookup (args+n) (db_to_set l)` \\ rw[]
  \\ Cases_on `x` \\ fs[GSYM lookup_db_to_set]
  \\ res_tac \\ fs[]);

val calls_wfg' = Q.store_thm("calls_wfg'",
  `∀xs g0 ys g.
    calls xs g0 = (ys,g) ∧
    set (code_locs xs) ⊆ EVEN ∧
    every_Fn_SOME xs ∧ wfg' g0 ⇒
    wfg' g`,
  ho_match_mp_tac calls_ind
  \\ rw[calls_def] \\ rw[] \\ fs[code_locs_def]
  \\ rpt (pairarg_tac \\ fs[])
  \\ every_case_tac \\ fs[] \\ rw[]
  >- (
    drule wfg'_insert_each \\ fs[IN_EVEN]
    \\ disch_then(qspec_then`1`mp_tac) \\ simp[]
    \\ disch_then drule \\ rw[]
    \\ fs[wfg'_def,ADD1,closed_Fn]
    \\ imp_res_tac calls_subspt
    \\ fs[subspt_def,domain_lookup]
    \\ first_x_assum match_mp_tac
    \\ REWRITE_TAC[ONE]
    \\ Cases_on`g0`
    \\ REWRITE_TAC[insert_each_def]
    \\ simp[lookup_insert] )
  \\ `0 < LENGTH fns ⇒ EVEN x`
  by (
    Cases_on`fns` \\ fs[SUBSET_DEF,IN_EVEN,MEM_GENLIST]
    \\ first_x_assum match_mp_tac
    \\ qexists_tac`0` \\ simp[] )
  \\ drule wfg'_insert_each
  \\ disch_then drule \\ rw[]
  \\ fs[]
  \\ match_mp_tac wfg'_code_list
  \\ imp_res_tac calls_length
  \\ fs[SUBSET_DEF]
  \\ imp_res_tac calls_subspt
  \\ fs[subspt_def,domain_lookup]
  \\ conj_tac
  >- (
    rw[] \\ first_x_assum match_mp_tac
    \\ qmatch_abbrev_tac`lookup k d = SOME _`
    \\ `k ∈ domain d` suffices_by simp[domain_lookup]
    \\ simp[Abbr`d`,domain_FST_insert_each])
  \\ simp[ZIP_MAP,EVERY_MAP]
  \\ fs[EVERY2_EVERY,LAMBDA_PROD,closed_Fn]);

val calls_wfg = Q.store_thm("calls_wfg",
  `∀xs g0 ys g.
    calls xs g0 = (ys,g) ∧
    set (code_locs xs) ⊆ EVEN ∧
    ALL_DISTINCT (code_locs xs) ∧
    DISJOINT (IMAGE SUC (set (code_locs xs))) (set (MAP FST (SND g0))) ∧
    every_Fn_SOME xs ∧ wfg g0
    ⇒
    wfg g`,
  rw[]
  \\ `wfg' g0` by fs[wfg_def,SET_EQ_SUBSET,wfg'_def]
  \\ imp_res_tac calls_wfg'
  \\ imp_res_tac calls_domain
  \\ imp_res_tac calls_IS_SUFFIX
  \\ imp_res_tac calls_add_SUC_code_locs
  \\ fs[wfg_def,wfg'_def,SET_EQ_SUBSET]
  \\ imp_res_tac calls_ALL_DISTINCT
  \\ fs[SUBSET_DEF,IS_SUFFIX_APPEND] \\ rw[]
  \\ res_tac \\ rw[]
  \\ res_tac \\ rw[] \\ fs[]
  \\ rw[] \\ rfs[]);

(*
val calls_wfg = Q.store_thm("calls_wfg",'_wfg
  `∀xs g0 ys g. calls xs g0 = (ys,g) ∧
    wfg' g0 ∧
    set (code_locs xs) ⊆ EVEN ∧
    every_Fn_SOME xs ∧
    ALL_DISTINCT (MAP FST (SND g0)) ∧
    ALL_DISTINCT (code_locs xs) ∧
    DISJOINT (IMAGE SUC (set (code_locs xs))) (set (MAP FST (SND g0))) ∧

    ⇒
    wfg g`,
  rw[]
  \\ imp_res_tac calls_wfg'
  \\ fs[wfg_def,wfg'_def,SET_EQ_SUBSET]
  \\ imp_res_tac calls_ALL_DISTINCT \\ rfs[]
  \\ imp_res_tac calls_add_SUC_code_locs
  \\ imp_res_tac calls_domain
  \\ fs[SUBSET_DEF,PULL_EXISTS]
  \\ rw[]
  \\ first_x_assum drule
  \\ rw[]
  >- (
    wfg'_def
*)

val FST_insert_each_same = Q.store_thm("FST_insert_each_same",
  `∀p n g0 g0'.
    FST g0 = FST g0' ⇒ FST (insert_each p n g0) = FST (insert_each p n g0')`,
  ho_match_mp_tac insert_each_ind
  \\ rw[insert_each_def] \\ fs[FORALL_PROD]
  \\ Cases_on`g0'` \\ fs[insert_each_def]);

val code_list_replace_SND = Q.store_thm("code_list_replace_SND",
  `∀loc fns g0 g g0' ls.
   code_list loc fns g0 = g ∧
   FST g0 = FST g0' ∧
   SND g = ls ++ SND g0
   ⇒
   code_list loc fns g0' = (FST g, ls ++ SND g0')`,
  ho_match_mp_tac code_list_ind
  \\ rw[code_list_def] \\ fs[] \\ rw[]
  \\ Cases_on`g0'` \\ fs[code_list_def]
  \\ fs[FORALL_PROD]
  \\ qmatch_asmsub_abbrev_tac`SND (code_list l2 fns g)`
  \\ qispl_then[`l2`,`fns`,`g`]strip_assume_tac code_list_IS_SUFFIX
  \\ fs[IS_SUFFIX_APPEND,Abbr`g`] \\ fs[] \\ rw[] \\ fs[]);

val calls_replace_SND = Q.store_thm("calls_replace_SND",
  `∀xs g0 ys g g0' ls.
    calls xs g0 = (ys,g) ∧
    FST g0 = FST g0' ∧
    SND g = ls ++ SND g0
    ⇒
    calls xs g0' = (ys,(FST g,ls ++ SND g0'))`,
  ho_match_mp_tac calls_ind
  \\ rw[calls_def] \\ fs[]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rveq \\ fs[]
  \\ imp_res_tac calls_length
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
  \\ rveq \\ fs[]
  \\ TRY (
    qmatch_goalsub_rename_tac`Letrec`
    \\ every_case_tac \\ fs[] \\ rveq \\ fs[]
    \\ qmatch_asmsub_abbrev_tac`insert_each p n g0`
    \\ TRY (
      first_x_assum(qspec_then`insert_each p n g0'`mp_tac)
      \\ simp[FST_insert_each_same]
      \\ imp_res_tac calls_IS_SUFFIX \\ fs[IS_SUFFIX_APPEND]
      \\ strip_tac \\ fs[] \\ rveq \\ fs[]
      \\ first_x_assum(qspec_then`g0'`mp_tac) \\ simp[]
      \\ strip_tac \\ fs[] \\ rveq \\ fs[]
      \\ qmatch_asmsub_abbrev_tac`calls [x1] (a,b)`
      \\ first_x_assum(qspec_then`a,b`mp_tac)
      \\ simp[]
      \\ NO_TAC)
    \\ last_x_assum(qspec_then`insert_each p n g0'`mp_tac)
    \\ simp[FST_insert_each_same]
    \\ imp_res_tac calls_IS_SUFFIX \\ fs[IS_SUFFIX_APPEND]
    \\ strip_tac \\ fs[] \\ rw[]
    \\ qmatch_asmsub_abbrev_tac`SND (code_list p ll gg)`
    \\ qispl_then[`p`,`ll`,`gg`]mp_tac code_list_replace_SND
    \\ simp[]
    \\ disch_then(qspec_then`FST gg,l++SND g0'`mp_tac)
    \\ simp[]
    \\ qispl_then[`p`,`ll`,`gg`]strip_assume_tac code_list_IS_SUFFIX
    \\ fs[IS_SUFFIX_APPEND] \\ fs[] \\ rveq \\ fs[] )
  \\ TRY (
    qmatch_goalsub_rename_tac`closed (Fn _ _ _ _)`
    \\ every_case_tac \\ fs[] \\ rveq \\ fs[]
    \\ TRY (
      qmatch_asmsub_abbrev_tac`insert_each p n g0`
      \\ first_x_assum(qspec_then`insert_each p n g0'`mp_tac)
      \\ simp[FST_insert_each_same]
      \\ imp_res_tac calls_IS_SUFFIX \\ fs[IS_SUFFIX_APPEND]
      \\ strip_tac \\ fs[]
      \\ NO_TAC)
    \\ first_x_assum(qspec_then`g0'`mp_tac) \\ simp[]
    \\ strip_tac \\ rveq \\ fs[]
    \\ qmatch_asmsub_abbrev_tac`insert_each p n g0`
    \\ first_x_assum(qspec_then`insert_each p n g0'`mp_tac)
    \\ simp[FST_insert_each_same]
    \\ imp_res_tac calls_IS_SUFFIX \\ fs[IS_SUFFIX_APPEND]
    \\ strip_tac \\ fs[] )
  \\ every_case_tac \\ fs[] \\ rveq \\ fs[]
  \\ first_x_assum(qspec_then`g0'`mp_tac) \\ simp[]
  \\ imp_res_tac calls_IS_SUFFIX \\ fs[IS_SUFFIX_APPEND]
  \\ (strip_tac ORELSE spose_not_then strip_assume_tac) \\ rveq \\ fs[] \\ rveq \\ fs[]
  \\ metis_tac[SND,FST,PAIR,APPEND_ASSOC,CONS_11,IS_SOME_DEF]);

val insert_each'_def = Define`
  (insert_each' p 0 g = g) ∧
  (insert_each' p (SUC n) (g1,g2) =
   insert_each' (p+2) n (insert p () g1, ((p+1,0n,closLang$Op El [])::g2)))`;

val insert_each'_ind = theorem"insert_each'_ind";

val wfg_insert_each' = Q.store_thm("wfg_insert_each'",
  `∀p n g.
    wfg g ∧
    EVEN p ∧
    DISJOINT (set (GENLIST (λi. p+2*i) n)) (domain (FST g))
    ⇒ wfg (insert_each' p n g)`,
  ho_match_mp_tac insert_each'_ind
  \\ rw[insert_each'_def]
  \\ first_x_assum match_mp_tac
  \\ fs[wfg_def,GSYM ADD1]
  \\ fs[IN_DISJOINT,MEM_GENLIST,IN_EVEN,EVEN_ADD]
  \\ fs[METIS_PROVE[]``x ∨ y ⇔ ¬x ⇒ y``,PULL_EXISTS]
  \\ rw[]
  >- ( simp[clos_freeTheory.free_def] )
  \\ first_assum (qspec_then`0`mp_tac)
  \\ first_x_assum (qspec_then`SUC i`mp_tac)
  \\ simp[ADD1,LEFT_ADD_DISTRIB]);

val FST_insert_each' = Q.store_thm("FST_insert_each'",
  `∀p n g. FST (insert_each' p n g) = FST (insert_each p n g)`,
  ho_match_mp_tac insert_each'_ind
  \\ rw[insert_each'_def,insert_each_def]
  \\ match_mp_tac FST_insert_each_same
  \\ rw[]);

val MAP_FST_insert_each' = Q.store_thm("MAP_FST_insert_each'",
  `∀p n g.
   MAP FST (SND (insert_each' p n g)) =
   REVERSE (GENLIST (λi. p + i * 2 + 1) n) ++
   MAP FST (SND g)`,
  ho_match_mp_tac insert_each'_ind
  \\ rw[insert_each'_def,GENLIST_CONS,o_DEF,ADD1,LEFT_ADD_DISTRIB]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ simp[FUN_EQ_THM]);


(* TODO: this is because TAKE_def is in srw_ss; I think it should not be *)
val TAKE_shadow_def = zDefine`TAKE_shadow = TAKE`

val calls_el_sing = Q.store_thm("calls_el_sing",
  `∀xs g0 ys g i.
    calls xs g0 = (ys,g) ∧
    i < LENGTH xs ∧
    ALL_DISTINCT (MAP FST (SND g0)) ∧
    ALL_DISTINCT (code_locs xs) ∧
    DISJOINT (IMAGE SUC (set (code_locs xs))) (set (MAP FST (SND g0))) ∧
    wfg g0 ∧ every_Fn_SOME xs ∧ set (code_locs xs) ⊆ EVEN
    ⇒
     ∃ga gb.
       calls [EL i xs] ga = ([EL i ys],gb) ∧
       subg g0 ga ∧ subg ga gb ∧ subg gb g ∧ wfg ga ∧ wfg gb ∧
       DISJOINT (IMAGE SUC (set (code_locs [EL i xs]))) (set (MAP FST (SND ga))) ∧
       set (MAP FST (SND ga)) ⊆ set (MAP FST (SND g0)) ∪ IMAGE SUC (set (code_locs (TAKE i xs))) ∧
       (set (code_locs [EL i xs]) DIFF (domain (FST gb))) ⊆ (set (code_locs xs) DIFF (domain (FST g)))`,
  PURE_REWRITE_TAC[GSYM TAKE_shadow_def]
  \\ ho_match_mp_tac calls_ind \\ rw[]
  \\ imp_res_tac calls_length
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
  \\ TRY (
    rveq \\ asm_exists_tac \\ fs[]
    \\ rpt conj_tac
    \\ TRY(
      match_mp_tac calls_wfg
      \\ asm_exists_tac \\ fs[]
      \\ NO_TAC)
    \\ metis_tac[calls_ALL_DISTINCT,subg_refl,calls_subg])
  \\ fs[calls_def]
  \\ rpt(pairarg_tac \\ fs[]) \\ rveq
  \\ imp_res_tac calls_length
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2] \\ rveq
  \\ Cases_on`i` \\ fs[]
  >- (
    asm_exists_tac \\ fs[]
    \\ rpt conj_asm1_tac
    \\ TRY (match_mp_tac subg_refl \\ fs[] )
    \\ TRY (fs[SUBSET_DEF,code_locs_def] \\ NO_TAC)
    \\ TRY (
      fs[SUBSET_DEF,code_locs_def]
      \\ qmatch_goalsub_rename_tac`code_locs [x]`
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ drule calls_wfg
      \\ impl_tac
      >- (
        fs[ALL_DISTINCT_APPEND,IN_DISJOINT,SUBSET_DEF]
        \\ metis_tac[numTheory.INV_SUC] )
      \\ strip_tac
      \\ rfs[wfg_def]
      \\ fs[SUBSET_DEF,ALL_DISTINCT_APPEND,PULL_EXISTS]
      \\ gen_tac
      \\ metis_tac[numTheory.INV_SUC])
    \\ (match_mp_tac calls_subg ORELSE match_mp_tac calls_wfg)
    \\ asm_exists_tac \\ fs[]
    \\ fs[code_locs_def,ALL_DISTINCT_APPEND]
    \\ imp_res_tac calls_ALL_DISTINCT \\ fs[]
    \\ imp_res_tac calls_add_SUC_code_locs
    \\ fs[IN_DISJOINT,SUBSET_DEF]
    \\ metis_tac[numTheory.INV_SUC] )
  \\ first_x_assum drule
  \\ impl_tac
  >- (
    fs[code_locs_def,ALL_DISTINCT_APPEND]
    \\ imp_res_tac calls_ALL_DISTINCT \\ fs[]
    \\ reverse conj_tac
    >- ( match_mp_tac calls_wfg \\ asm_exists_tac \\ fs[] )
    \\ imp_res_tac calls_add_SUC_code_locs
    \\ fs[IN_DISJOINT,SUBSET_DEF]
    \\ metis_tac[numTheory.INV_SUC] )
  \\ strip_tac \\ asm_exists_tac \\ fs[]
  \\ reverse conj_tac
  >- (
    reverse conj_tac
    >- ( fs[code_locs_def,SUBSET_DEF] )
    \\ imp_res_tac calls_add_SUC_code_locs
    \\ fs[SUBSET_DEF]
    \\ fs[REWRITE_RULE[GSYM TAKE_shadow_def]TAKE]
    \\ simp[Once code_locs_cons]
    \\ metis_tac[numTheory.INV_SUC] )
  \\ match_mp_tac subg_trans
  \\ first_assum(part_match_exists_tac(last o strip_conj) o concl) \\ rw[]
  \\ match_mp_tac calls_subg
  \\ asm_exists_tac \\ fs[]
  \\ fs[code_locs_def,ALL_DISTINCT_APPEND]);

(*
val calls_el_sing' = Q.store_thm("calls_el_sing'",
  `∀xs g0 ys g i.
    calls xs g0 = (ys,g) ∧
    i < LENGTH xs ∧
    ALL_DISTINCT (MAP FST (SND g0)) ∧
    ALL_DISTINCT (code_locs xs) ∧
    DISJOINT (IMAGE SUC (set (code_locs xs))) (set (MAP FST (SND g0))) ∧
    wfg' g0 ∧ wfg g ∧ every_Fn_SOME xs ∧ set (code_locs xs) ⊆ EVEN
    ⇒
     ∃ga gb.
       calls [EL i xs] ga = ([EL i ys],gb) ∧
       subg g0 ga ∧ subg ga gb ∧ subg gb g ∧ wfg' ga ∧ wfg gb ∧
       DISJOINT (IMAGE SUC (set (code_locs [EL i xs]))) (set (MAP FST (SND ga))) ∧
       set (MAP FST (SND ga)) ⊆ set (MAP FST (SND g0)) ∪ IMAGE SUC (set (code_locs (TAKE i xs))) (*∧
       (set (code_locs [EL i xs]) DIFF (domain (FST gb))) ⊆ (set (code_locs xs) DIFF (domain (FST g)))*)`,
  PURE_REWRITE_TAC[GSYM TAKE_shadow_def]
  \\ ho_match_mp_tac calls_ind \\ rw[]
  \\ imp_res_tac calls_length
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
  \\ TRY (
    rveq \\ asm_exists_tac \\ fs[]
    \\ rpt conj_tac
    \\ TRY(
      match_mp_tac calls_wfg'
      \\ asm_exists_tac \\ fs[]
      \\ NO_TAC)
    \\ metis_tac[calls_ALL_DISTINCT,subg_refl,calls_subg])
  \\ fs[calls_def]
  \\ rpt(pairarg_tac \\ fs[]) \\ rveq
  \\ imp_res_tac calls_length
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2] \\ rveq
  \\ Cases_on`i` \\ fs[]
  >- (
    asm_exists_tac \\ fs[]
    \\ rpt conj_asm1_tac
    \\ TRY (match_mp_tac subg_refl \\ fs[] )
    \\ TRY (fs[SUBSET_DEF,code_locs_def] \\ NO_TAC)
    \\ TRY (
      fs[SUBSET_DEF,code_locs_def]
      \\ qmatch_goalsub_rename_tac`code_locs [x]`
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ drule calls_wfg'
      \\ impl_tac
      >- (
        fs[ALL_DISTINCT_APPEND,IN_DISJOINT,SUBSET_DEF]
        \\ metis_tac[numTheory.INV_SUC] )
      \\ strip_tac
      \\ rfs[wfg'_def]
      \\ fs[SUBSET_DEF,ALL_DISTINCT_APPEND,PULL_EXISTS]
      \\ gen_tac
      \\ metis_tac[numTheory.INV_SUC])
    \\ (match_mp_tac calls_subg ORELSE match_mp_tac calls_wfg')
    \\ asm_exists_tac \\ fs[]
    \\ fs[code_locs_def,ALL_DISTINCT_APPEND]
    \\ imp_res_tac calls_ALL_DISTINCT \\ fs[]
    \\ imp_res_tac calls_add_SUC_code_locs
    \\ fs[IN_DISJOINT,SUBSET_DEF]
    \\ metis_tac[numTheory.INV_SUC] )
  \\ first_x_assum drule
  \\ impl_tac
  >- (
    fs[code_locs_def,ALL_DISTINCT_APPEND]
    \\ imp_res_tac calls_ALL_DISTINCT \\ fs[]
    \\ reverse conj_tac
    >- ( match_mp_tac calls_wfg' \\ asm_exists_tac \\ fs[] )
    \\ imp_res_tac calls_add_SUC_code_locs
    \\ fs[IN_DISJOINT,SUBSET_DEF]
    \\ metis_tac[numTheory.INV_SUC] )
  \\ strip_tac \\ asm_exists_tac \\ fs[]
  \\ reverse conj_tac
  >- (
    fs[code_locs_def,SUBSET_DEF]
    \\ imp_res_tac calls_add_SUC_code_locs
    \\ fs[SUBSET_DEF]
    \\ fs[REWRITE_RULE[GSYM TAKE_shadow_def]TAKE]
    \\ simp[Once code_locs_cons]
    \\ metis_tac[numTheory.INV_SUC] )
  \\ match_mp_tac subg_trans
  \\ first_assum(part_match_exists_tac(last o strip_conj) o concl) \\ rw[]
  \\ match_mp_tac calls_subg
  \\ asm_exists_tac \\ fs[]
  \\ fs[code_locs_def,ALL_DISTINCT_APPEND]);
*)

(*
val calls_subg_mono = Q.store_thm("calls_subg_mono",
  `∀xs g0 ys g g0' ys' g'.
    calls xs g0 = (ys,g) ∧ subg g0 g0' ∧
    calls xs g0' = (ys',g')
    ⇒
    subg g g'`,
  ho_match_mp_tac calls_ind
  \\ rw[calls_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rveq \\ fs[]
  \\ rpt (
    first_x_assum match_mp_tac
    \\ first_assum(part_match_exists_tac (last o strip_conj) o concl)
    \\ fs[] )
  \\ qhdtm_x_assum`COND`mp_tac
  \\ qmatch_goalsub_abbrev_tac`COND b1`
  \\ qhdtm_x_assum`COND`mp_tac
  \\ qmatch_goalsub_abbrev_tac`COND b2`
  \\ rw[] \\ fs[]
  \\ rpt (
    first_x_assum match_mp_tac
    \\ first_assum(part_match_exists_tac (last o strip_conj) o concl)
    \\ fs[] )
  \\ cheat (* need to show calls only removes free variables *) );
*)

val _ = delete_const"TAKE_shadow"

(* properties of value relation *)

val v_rel_subg = Q.store_thm("v_rel_subg",
  `∀g l v1 v2 g' l'.
    v_rel g l v1 v2 ∧ subg g g' ∧ l ⊆ l' ⇒
    v_rel g' l' v1 v2`,
  ho_match_mp_tac v_rel_ind
  \\ rw[v_rel_def,recclosure_rel_def]
  \\ fsrw_tac[ETA_ss][PULL_FORALL]
  \\ rpt(
    qmatch_assum_abbrev_tac`LIST_REL (v_rel g l) l1 l2`
    \\ `LIST_REL (v_rel g' l') l1 l2`
    by (
      match_mp_tac EVERY2_MEM_MONO
      \\ first_assum(part_match_exists_tac (last o strip_conj) o concl)
      \\ simp[FORALL_PROD]
      \\ imp_res_tac LIST_REL_LENGTH
      \\ simp[MEM_ZIP,PULL_EXISTS]
      \\ metis_tac[MEM_EL] )
    \\ qpat_assum`LIST_REL (v_rel g l) l1 l2` kall_tac
    \\ map_every qunabbrev_tac[`l2`,`l1`])
  \\ fs[]
  \\ qexists_tac`g0`
  \\ rpt(pairarg_tac \\ fs[])
  \\ imp_res_tac calls_length
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
  \\ rveq \\ fs[]
  \\ IF_CASES_TAC \\ fs[]
  \\ metis_tac[subg_trans,SUBSET_DEF]);

val state_rel_subg = Q.store_thm("state_rel_subg",
  `subg g0 g ∧ state_rel g0 l0 s t ∧ l0 ⊆ l ∧ code_includes (SND g) t.code ⇒ state_rel g l s t`,
  rw[state_rel_def]
  \\ TRY (
    match_mp_tac (GEN_ALL (MP_CANON LIST_REL_mono))
    \\ first_assum(part_match_exists_tac (last o strip_conj) o concl) \\ rw[]
    \\ match_mp_tac (GEN_ALL (MP_CANON OPTREL_MONO))
    \\ first_assum(part_match_exists_tac (last o strip_conj) o concl)
    \\ metis_tac[v_rel_subg] )
  \\ TRY (
    match_mp_tac (GEN_ALL (MP_CANON fmap_rel_mono))
    \\ first_assum(part_match_exists_tac (last o strip_conj) o concl)
    \\ simp[]
    \\ Cases \\ Cases \\ fs[]
    \\ match_mp_tac (GEN_ALL LIST_REL_mono)
    \\ metis_tac[v_rel_subg] ));

val code_includes_subg = Q.store_thm("code_includes_subg",
  `subg g1 g2 ⇒ code_includes (SND g2) code ⇒ code_includes (SND g1) code`,
  rw[subg_def,code_includes_def,IS_SUFFIX_APPEND]
  \\ first_x_assum match_mp_tac
  \\ rw[ALOOKUP_APPEND]
  \\ BasicProvers.CASE_TAC
  \\ imp_res_tac ALOOKUP_MEM
  \\ rfs[ALL_DISTINCT_APPEND,MEM_MAP,PULL_EXISTS]
  \\ res_tac \\ fs[]
  \\ metis_tac[FST]);

val code_includes_ALOOKUP = Q.store_thm("code_includes_ALOOKUP",
  `code_includes al code ∧ ALOOKUP al loc = SOME r ⇒ FLOOKUP code loc = SOME r`,
  rw[code_includes_def]);

val dest_closure_v_rel_lookup = Q.store_thm("dest_closure_v_rel_lookup",
  `dest_closure (SOME loc) v1 env1 = SOME x ∧
   v_rel g l v1 v2 ∧
   LIST_REL (v_rel g l) env1 env2 ∧
   wfg g ∧ loc ∈ domain (FST g) ∧ loc ∉ l  ⇒
   ∃e l1 xs n ls g01 g1 l1'.
     x = Full_app e (env1++l1) [] ∧ EL n xs = (LENGTH env1,e) ∧
     calls (MAP SND xs) g01 = (ls,g1) ∧ n < LENGTH ls ∧
     subg (code_list (loc - 2*n) (ZIP (MAP FST xs,ls)) g1) g ∧
     ALOOKUP (SND g) (loc+1) = SOME (LENGTH env1,EL n ls) ∧
     dest_closure (SOME loc) v2 env2 = SOME (Full_app (Call 0 (loc+1) (GENLIST Var (LENGTH env1))) (env2++l1') []) ∧
     LIST_REL (v_rel g l) l1 l1'`,
  rw[dest_closure_def]
  \\ every_case_tac \\ fs[v_rel_def,recclosure_rel_def]
  \\ rw[] \\ fs[check_loc_def] \\ rw[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ rfs[]
  \\ fs[LENGTH_NIL] \\ rveq
  \\ imp_res_tac LIST_REL_LENGTH \\ fs[]
  \\ fs[DROP_LENGTH_NIL_rwt,revtakerev]
  >- (
    qpat_abbrev_tac`el = (_,_)`
    \\ qexists_tac`[el]` \\ simp[Abbr`el`]
    \\ last_assum(part_match_exists_tac(el 2 o strip_conj) o concl)
    \\ qexists_tac`0` \\ simp[]
    \\ imp_res_tac calls_length \\ fs[]
    \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
    \\ fs[calls_list_def] \\ rveq
    \\ Cases_on`new_g` \\ fs[code_list_def,subg_def,IS_SUFFIX_APPEND]
    (*
    \\ conj_tac
    >- (
      simp[ALOOKUP_APPEND]
      \\ BasicProvers.CASE_TAC
      \\ imp_res_tac ALOOKUP_MEM
      \\ rfs[ALL_DISTINCT_APPEND,MEM_MAP,PULL_EXISTS]
      \\ res_tac \\ fs[] )
    *)
    \\ fsrw_tac[ETA_ss][]
    (*
    \\ `subg g0 g`
    by (
      qpat_assum`calls _ (insert_each _ _ _) = _`assume_tac
      \\ drule calls_subg
      \\ impl_tac >- rfs[wfg_def]
      \\ strip_tac
      \\ `subg g0 (insert_each loc 1 g0)`
      by ( simp[subg_def,insert_each_subspt] \\ fs[wfg_def] )
      \\ match_mp_tac subg_trans
      \\ asm_exists_tac \\ rw[]
      \\ match_mp_tac subg_trans
      \\ asm_exists_tac \\ rw[]
      \\ match_mp_tac subg_trans
      \\ last_assum (part_match_exists_tac (last o strip_conj) o concl)
      \\ simp[]
      \\ fs[subg_def]
      \\ fs[IS_SUFFIX_APPEND,GSYM ADD1]
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ rfs[SUBSET_DEF]
      \\ fs[ALL_DISTINCT_APPEND] )
    \\ match_mp_tac (GEN_ALL (MP_CANON LIST_REL_mono))
    \\ metis_tac[v_rel_subg]
    *))
  \\ last_assum(part_match_exists_tac(el 2 o strip_conj) o concl)
  \\ asm_exists_tac \\ simp[]
  \\ qhdtm_x_assum`COND`mp_tac
  \\ reverse IF_CASES_TAC
  >- (
    simp[SUBSET_DEF,MEM_GENLIST,PULL_EXISTS]
    \\ fs[NOT_LESS_EQUAL]
    \\ metis_tac[ADD_COMM] )
  \\ strip_tac \\ rveq
  \\ imp_res_tac calls_length
  \\ fs[]
  \\ fs[calls_list_MAPi]
  \\ rfs[NOT_LESS_EQUAL]
  \\ fs[indexedListsTheory.EL_MAPi]
  \\ conj_tac
  >- (
    fs[subg_def]
    \\ first_x_assum match_mp_tac
    \\ simp[ALOOKUP_code_list]
    \\ DEEP_INTRO_TAC some_intro
    \\ simp[EL_ZIP,EL_MAP] )
    (*
    \\ simp[ALOOKUP_APPEND]
    \\ reverse BasicProvers.CASE_TAC
    >- (
      imp_res_tac ALOOKUP_MEM
      \\ rfs[ALL_DISTINCT_APPEND,MEM_MAP,PULL_EXISTS]
      \\ fs[MAP_FST_code_list,ALL_DISTINCT_APPEND,MEM_GENLIST]
      \\ res_tac \\ fs[]
      \\ fs[SND_code_list_ZIP,MEM_ZIP]
      \\ rfs[EL_GENLIST,FORALL_PROD]
      \\ fs[MEM_MAP,PULL_EXISTS,FORALL_PROD]
      \\ fs[MEM_EL,PULL_FORALL]
      \\ fs[METIS_PROVE[]``¬A ∨ B ⇔ A ⇒ B``]
      \\ fs[AND_IMP_INTRO]
      \\ metis_tac[PAIR])
    \\ simp[ALOOKUP_code_list]
    \\ DEEP_INTRO_TAC some_intro
    \\ simp[EL_ZIP,EL_MAP] )
    *)
  \\ simp[revtakerev,revdroprev]
  \\ match_mp_tac EVERY2_APPEND_suff
  \\ fsrw_tac[ETA_ss][]
  \\ simp[LIST_REL_GENLIST]
  \\ simp[v_rel_def,recclosure_rel_def]
  \\ fsrw_tac[ETA_ss][]
  \\ simp[calls_list_MAPi]
  (*
  \\ reverse conj_tac
  >- (
    `subg g0 g`
    by (
      qpat_assum`calls _ (insert_each _ _ _) = _`assume_tac
      \\ drule calls_subg
      \\ impl_tac >- rfs[wfg_def]
      \\ qpat_abbrev_tac`g1 = insert_each _ _ _`
      \\ `subg g0 g1`
      by ( simp[Abbr`g1`,subg_def,insert_each_subspt] \\ fs[wfg_def] )
      \\ strip_tac
      \\ match_mp_tac subg_trans
      \\ asm_exists_tac \\ rw[]
      \\ match_mp_tac subg_trans
      \\ asm_exists_tac \\ rw[]
      \\ match_mp_tac subg_trans
      \\ last_assum (part_match_exists_tac (last o strip_conj) o concl)
      \\ simp[]
      \\ fs[subg_def]
      \\ conj_tac
      >- ( fs[IS_SUFFIX_APPEND,GSYM ADD1,SND_code_list_ZIP] )
      \\ simp[MAP_FST_code_list]
      \\ simp[ALL_DISTINCT_APPEND,ALL_DISTINCT_GENLIST]
      \\ simp[MEM_GENLIST,PULL_EXISTS]
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ rfs[SUBSET_DEF] \\ rw[]
      \\ strip_tac \\ first_x_assum drule
      \\ simp[Abbr`g1`] \\ fs[]
      \\ fs[IN_DISJOINT,MEM_GENLIST,PULL_EXISTS]
      \\ metis_tac[ADD_ASSOC,ADD1,numTheory.INV_SUC])
    \\ match_mp_tac (GEN_ALL (MP_CANON LIST_REL_mono))
    \\ metis_tac[v_rel_subg])
  *)
  \\ rw[]
  \\ qexists_tac`g0`
  \\ simp[]);

val dest_closure_v_rel = Q.store_thm("dest_closure_v_rel",
  `dest_closure loco v1 env1 = SOME x1 ∧
   v_rel g l v1 v2 ∧
   LIST_REL (v_rel g l) env1 env2
   ⇒
   ∃x2.
   dest_closure loco v2 env2 = SOME x2 ∧
   (case x1 of Partial_app c1 =>
     ∃c2. x2 = Partial_app c2 ∧ v_rel g l c1 c2
    | Full_app e1 args1 rest1 =>
      ∃g0 fns1 loc i fns2 args2 rest2.
        x2 = Full_app (SND (EL i fns2)) args2 rest2 ∧
        LIST_REL (v_rel g l) args1 args2 ∧
        LIST_REL (v_rel g l) rest1 rest2 ∧
        recclosure_rel g l g0 loc fns1 fns2 ∧
        i < LENGTH fns1 ∧
        EL i fns1 = (FST (EL i fns2), e1) ∧
        FST (EL i fns2) ≤ LENGTH args2
        (*
        every_Fn_SOME [e1] ∧
        every_Fn_vs_NONE [e1] ∧
        set (code_locs [e1]) ⊆ EVEN ∧
        ALL_DISTINCT (code_locs [e1]) *)(*∧
        (∃e2 g0 g1.
          calls [e1] g0 = ([e2],g1)*))`,
  rw[dest_closure_def]
  \\ Cases_on`v1` \\ fs[v_rel_def]
  \\ rveq \\ fs[]
  \\ imp_res_tac LIST_REL_LENGTH \\ fs[]
  \\ rw[] \\ fs[] \\ rveq \\ fs[]
  \\ rpt(pairarg_tac \\ fs[])
  >- (
    fs[revtakerev,revdroprev,recclosure_rel_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ imp_res_tac calls_length
    \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
    \\ rveq \\ fs[]
    \\ map_every qexists_tac [`g0`,`([n,e])`,`loc`]
    \\ simp[calls_list_def]
    \\ qmatch_goalsub_abbrev_tac`COND b`
    \\ Cases_on`b` \\ fs[calls_list_def]
    \\ rpt conj_tac
    \\ TRY (match_mp_tac EVERY2_TAKE \\ fs[])
    \\ match_mp_tac EVERY2_APPEND_suff
    \\ fsrw_tac[ETA_ss][]
    \\ match_mp_tac EVERY2_APPEND_suff \\ fs[]
    \\ match_mp_tac EVERY2_DROP \\ fs[] )
  >- (
    simp[v_rel_def]
    \\ asm_exists_tac
    \\ fsrw_tac[ETA_ss][]
    \\ match_mp_tac EVERY2_APPEND_suff
    \\ fs[] )
  \\ fsrw_tac[ETA_ss][]
  \\ `LENGTH fns2 = LENGTH l1 ∧ num_args = num_args'`
  by (
    fs[recclosure_rel_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ every_case_tac \\ fs[calls_list_MAPi]
    \\ imp_res_tac calls_length \\ fs[]
    \\ rw[] \\ rfs[indexedListsTheory.EL_MAPi] \\ fs[]
    \\ qpat_assum`¬(LENGTH _ ≤ _)`assume_tac
    \\ fs[EL_ZIP,EL_MAP])
  \\ fs[]
  \\ reverse IF_CASES_TAC \\ fs[] \\ rveq \\ fs[]
  >- (
    fs[v_rel_def]
    \\ asm_exists_tac
    \\ fsrw_tac[ETA_ss][]
    \\ match_mp_tac EVERY2_APPEND_suff \\ fs[] )
  \\ fs[revdroprev,revtakerev]
  \\ first_assum(part_match_exists_tac (el 4 o rev o strip_conj) o concl)
  \\ qexists_tac`n` \\ fs[]
  \\ conj_tac
  >- (
    fs[v_rel_def,recclosure_rel_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ fsrw_tac[ETA_ss][]
    \\ match_mp_tac EVERY2_APPEND_suff \\ fs[]
    \\ match_mp_tac EVERY2_APPEND_suff
    \\ fs[LIST_REL_GENLIST]
    \\ conj_tac
    >- (
      match_mp_tac EVERY2_APPEND_suff \\ fs[]
      \\ match_mp_tac EVERY2_DROP \\ fs[] )
    \\ simp[v_rel_def,recclosure_rel_def]
    \\ ntac 2 strip_tac
    \\ qexists_tac`g0`
    \\ fsrw_tac[ETA_ss][] )
  \\ match_mp_tac EVERY2_TAKE \\ fs[]);

(*
  \\ fs[recclosure_rel_def]
  \\ fs[Q.SPEC`MAP _ _`every_Fn_SOME_EVERY,
        Q.SPEC`MAP _ _`every_Fn_vs_NONE_EVERY,
        code_locs_map,
        EVERY_MAP,EVERY_MEM,FORALL_PROD,NOT_LESS_EQUAL]
  \\ rpt conj_tac
  \\ TRY (
    first_x_assum match_mp_tac
    \\ metis_tac[MEM_EL] )
  \\ TRY (
    imp_res_tac ALL_DISTINCT_FLAT_EVERY
    \\ fs[EVERY_MAP,EVERY_MEM,FORALL_PROD]
    \\ first_x_assum match_mp_tac
    \\ metis_tac[MEM_EL] )
  \\ TRY (
    qmatch_goalsub_rename_tac`$SUBSET`
    \\ fs[SUBSET_DEF,MEM_FLAT,PULL_EXISTS,MEM_MAP,FORALL_PROD]
    \\ metis_tac[MEM_EL] ));
*)

(* semantic functions respect relation *)

val v_rel_Unit = store_thm("v_rel_Unit[simp]",
  ``v_rel g1 l1 Unit Unit``,
  EVAL_TAC \\ fs []);

val do_eq_thm = store_thm("do_eq_thm",
  ``(!h1 h1a b h2 h2a.
       do_eq h1 h1a = Eq_val b /\ v_rel g1 l1 h1 h2 /\ v_rel g1 l1 h1a h2a ==>
       do_eq h2 h2a = Eq_val b) /\
    (!h1 h1a b h2 h2a.
       do_eq_list h1 h1a = Eq_val b /\
       LIST_REL (v_rel g1 l1) h1 h2 /\
       LIST_REL (v_rel g1 l1) h1a h2a ==>
       do_eq_list h2 h2a = Eq_val b)``,
  HO_MATCH_MP_TAC do_eq_ind \\ fs [] \\ rw []
  THEN1
   (Cases_on `h1` \\ Cases_on `h1a` \\ fs [v_rel_def,do_eq_def]
    \\ rw [] \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ rfs [] \\ rpt (pop_assum mp_tac)
    \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ rw [])
  \\ fs [v_rel_def,do_eq_def |> CONJUNCT2] \\ every_case_tac \\ fs []
  \\ res_tac \\ fs [])

val v_to_list_thm = store_thm("v_to_list_thm",
  ``!h h' x.
      v_to_list h = SOME x /\ v_rel g1 l1 h h' ==>
      ?x'. v_to_list h' = SOME x' /\ LIST_REL (v_rel g1 l1) x x'``,
  recInduct v_to_list_ind \\ rw [] \\ fs [v_to_list_def] \\ rw []
  \\ fs [v_rel_def,v_to_list_def] \\ rw []
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ res_tac \\ fs [] \\ rw []);

val v_rel_list_to_v = store_thm("v_rel_list_to_v",
  ``!l1 l2.
      LIST_REL (v_rel g1 l) l1 l2 ==>
      v_rel g1 l (list_to_v l1) (list_to_v l2)``,
  Induct \\ fs [v_rel_def,list_to_v_def,PULL_EXISTS]);

val do_app_thm = prove(
  ``state_rel g1 l1 r t /\
    LIST_REL (v_rel g1 l1) a v ==>
    case do_app op (REVERSE a) r of
      Rerr (Rraise _) => F
    | Rerr (Rabort e) => (e = Rtype_error)
    | Rval (w,s) =>
       ?w' s'. (do_app op (REVERSE v) t = Rval (w',s')) /\
               v_rel g1 l1 w w' /\ state_rel g1 l1 s s'``,
  once_rewrite_tac [GSYM REVERSE_REVERSE]
  \\ qspec_tac (`REVERSE a`,`xs`)
  \\ qspec_tac (`REVERSE v`,`ys`)
  \\ fs [REVERSE_REVERSE,LIST_REL_REVERSE_EQ]
  \\ Cases_on `op = Equal` THEN1
   (fs [do_app_def,state_rel_def] \\ every_case_tac \\ fs []
    \\ rw [] \\ fs [] \\ fs [v_rel_def] \\ rw []
    \\ every_case_tac \\ fs []
    \\ imp_res_tac do_eq_thm \\ fs [] \\ fs [Boolv_def,v_rel_def])
  \\ Cases_on `?n. op = FromList n` THEN1
   (fs [do_app_def,state_rel_def] \\ every_case_tac \\ fs []
    \\ rw [] \\ fs [] \\ fs [v_rel_def] \\ rw []
    \\ every_case_tac \\ fs [v_rel_def]
    \\ imp_res_tac v_to_list_thm \\ fs [] \\ rw []
    \\ fs [Boolv_def,v_rel_def,LIST_REL_EL_EQN])
  \\ Cases_on `op = ToList` THEN1
   (fs [do_app_def,state_rel_def] \\ every_case_tac \\ fs []
    \\ rw [] \\ fs [] \\ fs [v_rel_def] \\ rw []
    \\ every_case_tac \\ fs [v_rel_def] \\ rw []
    \\ match_mp_tac v_rel_list_to_v \\ fs [LIST_REL_EL_EQN])
  \\ Cases_on `op = Add \/ op = Sub \/ op = Mult \/ op = Div \/ op = Mod \/
               op = Less \/ op = LessEq \/ op = Greater \/ op = GreaterEq` THEN1
   (fs [] \\ rw []
    \\ fs [do_app_def,state_rel_def] \\ every_case_tac \\ fs []
    \\ rw [] \\ fs [] \\ fs [v_rel_def] \\ rw []
    \\ fs [Boolv_def] \\ rw [v_rel_def])
  \\ Cases_on `?n. op = Global n` \\ fs [] \\ rw [] THEN1
   (fs [Once do_app_def] \\ every_case_tac
    \\ fs [get_global_def,do_app_def,state_rel_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [LIST_REL_EL_EQN]
    \\ res_tac \\ rw []
    \\ qpat_assum `!x.bbb` mp_tac
    \\ rfs [] \\ full_case_tac \\ fs [OPTREL_def])
  \\ Cases_on `?n. op = SetGlobal n` \\ fs [] \\ rw [] THEN1
   (fs [Once do_app_def] \\ every_case_tac
    \\ fs [get_global_def,do_app_def,state_rel_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [LIST_REL_EL_EQN]
    \\ res_tac \\ rw []
    \\ qpat_assum `!x.bbb` mp_tac
    \\ rfs [] \\ full_case_tac
    \\ fs [OPTREL_def,EL_LUPDATE] \\ rw [] \\ rw [])
  \\ Cases_on `op = AllocGlobal` \\ fs [] \\ rw [] THEN1
   (fs [Once do_app_def] \\ every_case_tac
    \\ fs [get_global_def,do_app_def,state_rel_def]
    \\ fs [OPTREL_def,EL_LUPDATE] \\ rw [] \\ rw [])
  \\ Cases_on `?tag. op = Cons tag` \\ fs [] \\ rw [] THEN1
   (fs [Once do_app_def] \\ every_case_tac
    \\ fs [do_app_def,state_rel_def]
    \\ fs [v_rel_def] \\ rw []
    \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  \\ Cases_on `op = El` \\ fs [] \\ rw [] THEN1
   (fs [do_app_def,state_rel_def] \\ every_case_tac \\ fs []
    \\ rw [] \\ fs [] \\ fs [v_rel_def] \\ rw []
    \\ fs [LIST_REL_EL_EQN] \\ res_tac \\ rw [])
  \\ Cases_on `op = LengthBlock` \\ fs [] \\ rw [] THEN1
   (fs [do_app_def,state_rel_def] \\ every_case_tac \\ fs []
    \\ rw [] \\ fs [] \\ fs [v_rel_def] \\ rw []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
  \\ Cases_on `op = Length` \\ fs [] \\ rw [] THEN1
   (fs [do_app_def,state_rel_def] \\ every_case_tac \\ fs []
    \\ rw [] \\ fs [] \\ fs [v_rel_def] \\ rw []
    \\ fs [fmap_rel_OPTREL_FLOOKUP]
    \\ first_x_assum (qspec_then `n` mp_tac)
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ fs [OPTREL_def] \\ rw []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
  \\ Cases_on `op = LengthByte` \\ fs [] \\ rw [] THEN1
   (fs [do_app_def,state_rel_def] \\ every_case_tac \\ fs []
    \\ rw [] \\ fs [] \\ fs [v_rel_def] \\ rw []
    \\ fs [fmap_rel_OPTREL_FLOOKUP]
    \\ first_x_assum (qspec_then `n` mp_tac)
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ fs [OPTREL_def] \\ rw []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
  \\ Cases_on `op = RefByte` \\ fs [] \\ rw [] THEN1
   (fs [do_app_def,state_rel_def] \\ every_case_tac \\ fs []
    \\ rw [] \\ fs [] \\ fs [v_rel_def] \\ rw []
    \\ `FDOM r.refs = FDOM t.refs` by fs [fmap_rel_def] \\ fs []
    \\ match_mp_tac fmap_rel_FUPDATE_same \\ fs [])
  \\ Cases_on `op = GlobalsPtr \/ op = SetGlobalsPtr` THEN1
   (fs [Once do_app_def] \\ every_case_tac)
  \\ Cases_on `op = RefArray` THEN1
   (fs [do_app_def,state_rel_def] \\ every_case_tac \\ fs []
    \\ rw [] \\ fs [] \\ fs [v_rel_def] \\ rw []
    \\ `FDOM r.refs = FDOM t.refs` by fs [fmap_rel_def] \\ fs []
    \\ match_mp_tac fmap_rel_FUPDATE_same \\ fs [LIST_REL_REPLICATE_same])
  \\ Cases_on `?n1 n2. op = TagLenEq n1 n2 \/ op = TagEq n1 \/
                       op = BlockCmp \/ op = IsBlock \/ op = Label n1` THEN1
   (fs [do_app_def,state_rel_def] \\ every_case_tac \\ fs []
    \\ rw [] \\ fs [] \\ fs [v_rel_def,Boolv_def] \\ rw []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
  \\ Cases_on `?n1. op = FFI n1` THEN1
   (fs [do_app_def,state_rel_def] \\ every_case_tac \\ fs []
    \\ rw [] \\ fs [] \\ fs [v_rel_def,Boolv_def] \\ rw []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ fs [fmap_rel_OPTREL_FLOOKUP]
    \\ first_assum (qspec_then `n` assume_tac)
    \\ qpat_assum `!x.bbb` mp_tac
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ fs [OPTREL_def] \\ rw [] \\ fs [ref_rel_def]
    \\ fs [FLOOKUP_UPDATE] \\ rw [] \\ fs [ref_rel_def])
  \\ Cases_on `op = Ref` THEN1
   (fs [do_app_def,state_rel_def] \\ every_case_tac \\ fs []
    \\ rw [] \\ fs [] \\ fs [v_rel_def,Boolv_def] \\ rw []
    \\ `FDOM r.refs = FDOM t.refs` by fs [fmap_rel_def] \\ fs []
    \\ match_mp_tac fmap_rel_FUPDATE_same \\ fs [])
  \\ Cases_on `?i. op = Const i` THEN1
   (fs [do_app_def,state_rel_def] \\ every_case_tac \\ fs []
    \\ rw [] \\ fs [] \\ fs [v_rel_def,Boolv_def] \\ rw []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
  \\ Cases_on `(?w oo. op = WordOp w oo) \/
               op = WordFromInt \/ op = WordToInt \/
               (?w s n. op = WordShift w s n)` THEN1
   (fs [do_app_def,state_rel_def] \\ every_case_tac \\ fs []
    \\ rw [] \\ fs [] \\ fs [v_rel_def,Boolv_def] \\ rw [])
  \\ Cases_on `(?w oo. op = WordOp w oo) \/
               op = WordFromInt \/ op = WordToInt \/
               (?w s n. op = WordShift w s n)` THEN1
   (fs [do_app_def,state_rel_def] \\ every_case_tac \\ fs []
    \\ rw [] \\ fs [] \\ fs [v_rel_def,Boolv_def] \\ rw [])
  \\ Cases_on `op = Deref` THEN1
   (fs [do_app_def,state_rel_def] \\ every_case_tac \\ fs [v_rel_def]
    \\ rw [] \\ fs [fmap_rel_OPTREL_FLOOKUP]
    \\ first_assum (qspec_then `n` assume_tac)
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ fs [OPTREL_def] \\ rw [] \\ fs [ref_rel_def]
    \\ rw [] \\ fs [ref_rel_def,LIST_REL_EL_EQN] \\ rfs []
    \\ Cases_on `i` \\ fs [])
  \\ Cases_on `op = DerefByte` THEN1
   (fs [do_app_def,state_rel_def] \\ every_case_tac \\ fs [v_rel_def]
    \\ rw [] \\ fs [fmap_rel_OPTREL_FLOOKUP]
    \\ first_assum (qspec_then `n` assume_tac)
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ fs [OPTREL_def] \\ rw [] \\ fs [ref_rel_def]
    \\ rw [] \\ fs [ref_rel_def,LIST_REL_EL_EQN] \\ rfs [])
  \\ Cases_on `op = Update \/ op = UpdateByte` THEN1
   (fs [do_app_def,state_rel_def] \\ every_case_tac \\ fs []
    \\ rw [] \\ fs [] \\ fs [v_rel_def] \\ rw []
    \\ rw [] \\ fs [fmap_rel_OPTREL_FLOOKUP]
    \\ first_assum (qspec_then `n` assume_tac)
    \\ fs [OPTREL_def] \\ rw [] \\ fs [ref_rel_def]
    \\ rw [] \\ fs [ref_rel_def,LIST_REL_EL_EQN] \\ rfs []
    \\ fs [FLOOKUP_UPDATE] \\ rw [] \\ fs [ref_rel_def]
    \\ match_mp_tac EVERY2_LUPDATE_same \\ fs []
    \\ fs [ref_rel_def,LIST_REL_EL_EQN])
  \\ Cases_on `op` \\ fs []);

val NOT_IN_domain_FST_g = store_thm("NOT_IN_domain_FST_g",
  ``ALL_DISTINCT (code_locs xs ++ code_locs ys) ⇒
    calls ys g' = (e2,g) ⇒
    wfg g' ⇒
    MEM x (code_locs xs) ⇒
    x ∉ domain (FST g') ⇒
    x ∉ domain (FST g)``,
  rw [] \\ imp_res_tac calls_domain
  \\ fs [SUBSET_DEF,DISJOINT_DEF,EXTENSION] \\ rw []
  \\ CCONTR_TAC \\ fs [] \\ res_tac \\ rveq \\ fs []
  \\ drule calls_add_SUC_code_locs \\ fs [SUBSET_DEF]
  \\ asm_exists_tac \\ fs [] \\ CCONTR_TAC \\ fs []
  \\ rfs [wfg_def,SUBSET_DEF,EXTENSION] \\ rveq \\ fs []
  \\ fs [ALL_DISTINCT_APPEND] \\ res_tac);

val v_rel_Boolv = store_thm("v_rel_Boolv[simp]",
  ``v_rel g1 l1 (Boolv b) v <=> (v = Boolv b)``,
  Cases_on `b` \\ Cases_on `v` \\ fs [v_rel_def,Boolv_def]);

(* compiler correctness *)

val calls_correct = Q.store_thm("calls_correct",
  `(∀tmp xs env1 (s0:'ffi closSem$state) g0 g env2 t0 ys res s l l1 g1.
    tmp = (xs,env1,s0) ∧
    evaluate (xs,env1,s0) = (res,s) ∧
    res ≠ Rerr (Rabort Rtype_error) ∧
    calls xs g0 = (ys,g) ∧
    every_Fn_SOME xs ∧ every_Fn_vs_NONE xs ∧
    set (code_locs xs) ⊆ EVEN ∧
    wfg g0 ∧
    ALL_DISTINCT (code_locs xs) ∧
    DISJOINT (IMAGE SUC (set (code_locs xs))) (set (MAP FST (SND g0))) ∧
    l = set (code_locs xs) DIFF domain (FST g) ∧
    LIST_REL (v_rel g1 l1) env1 env2 ∧
    state_rel g1 l1 s0 t0 ∧
    subg g g1 ∧ l ⊆ l1 ∧ DISJOINT l1 (domain (FST g1)) ∧ wfg g1 ∧
    code_includes (SND g) t0.code
    ⇒
    ∃ck res' t.
    evaluate (ys,env2,t0 with clock := t0.clock + ck) = (res',t) ∧
    state_rel g1 l1 s t ∧
    result_rel (LIST_REL (v_rel g1 l1)) (v_rel g1 l1) res res') ∧
  (∀loco f args (s0:'ffi closSem$state) loc g l t0 res s f' args'.
    evaluate_app loco f args s0 = (res,s) ∧
    res ≠ Rerr (Rabort Rtype_error) ∧
    v_rel g l f f' ∧
    LIST_REL (v_rel g l) args args' ∧
    state_rel g l s0 t0 ∧
    wfg g ∧ DISJOINT l (domain (FST g))
    ⇒
    ∃ck res' t.
    evaluate_app loco f' args' (t0 with clock := t0.clock + ck) = (res',t) ∧
    state_rel g l s t ∧
    result_rel (LIST_REL (v_rel g l)) (v_rel g l) res res')`,
  ho_match_mp_tac evaluate_ind
  \\ conj_tac
  >- (
    rw[]
    \\ qexists_tac`0`
    \\ fs[calls_def,evaluate_def]
    \\ rveq \\ fs[evaluate_def]
    \\ fs[code_locs_def]
    \\ metis_tac[state_rel_subg,SUBSET_REFL])
  \\ conj_tac >-
   (fs [evaluate_def,calls_def] \\ rw []
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ Cases_on `evaluate ([x],env,s)` \\ fs []
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ `subg g' g` by
     (match_mp_tac calls_subg \\ fs []
      \\ asm_exists_tac \\ fs []
      \\ fs[code_locs_def,ALL_DISTINCT_APPEND]
      \\ strip_tac THEN1
       (match_mp_tac calls_ALL_DISTINCT
        \\ asm_exists_tac \\ fs [wfg_def])
      \\ imp_res_tac calls_ALL_DISTINCT \\ fs[]
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ fs[IN_DISJOINT,SUBSET_DEF]
      \\ metis_tac[numTheory.INV_SUC])
    \\ `wfg g'` by
     (match_mp_tac calls_wfg \\ asm_exists_tac \\ fs []
      \\ fs [code_locs_def,ALL_DISTINCT_APPEND])
    \\ imp_res_tac calls_sing \\ rw []
    \\ Cases_on `e2` THEN1 (imp_res_tac calls_length \\ fs [])
    \\ rename1 `calls (y::xs) g' = (z::zs,g)`
    \\ reverse (Cases_on `q`) \\ fs [] \\ rw [] \\ fs []
    \\ first_x_assum drule \\ fs []
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
    \\ fs [AND_IMP_INTRO] \\ impl_tac
    \\ TRY (fs [code_locs_def,ALL_DISTINCT_APPEND] \\ NO_TAC)
    \\ rpt (disch_then drule) \\ fs [GSYM CONJ_ASSOC]
    \\ rpt (disch_then drule) \\ fs [AND_IMP_INTRO]
    \\ impl_tac \\ TRY
     (imp_res_tac subg_trans \\ fs []
      \\ imp_res_tac code_includes_subg \\ fs []
      \\ fs [code_locs_def]
      \\ match_mp_tac SUBSET_TRANS
      \\ simp [Once CONJ_COMM] \\ asm_exists_tac \\ fs []
      \\ fs [SUBSET_DEF,DISJOINT_DEF,EXTENSION] \\ rw []
      \\ drule (GEN_ALL NOT_IN_domain_FST_g)
      \\ rpt (disch_then drule \\ fs []) \\ NO_TAC)
    \\ strip_tac \\ fs []
    \\ rw [] \\ fs [PULL_EXISTS,evaluate_def]
    THEN1 (qexists_tac `ck` \\ fs [])
    \\ Cases_on `evaluate (y::xs,env,r)` \\ fs []
    \\ `q ≠ Rerr (Rabort Rtype_error)` by (CCONTR_TAC \\ fs []) \\ fs []
    \\ first_x_assum drule \\ fs []
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
    \\ fs [AND_IMP_INTRO] \\ impl_tac
    THEN1
     (fs [code_locs_def,ALL_DISTINCT_APPEND,wfg_def] \\ rfs []
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ fs [DISJOINT_IMAGE_SUC] \\ fs [IN_DISJOINT]
      \\ CCONTR_TAC \\ fs [] \\ rfs [IMAGE_SUC_SUBSET_UNION]
      \\ fs [SUBSET_DEF]
      \\ first_x_assum drule \\ CCONTR_TAC \\ fs [] \\ metis_tac [])
    \\ fs [GSYM CONJ_ASSOC]
    \\ rpt (disch_then drule \\ fs [])
    \\ impl_tac THEN1
     (imp_res_tac subg_trans \\ fs []
      \\ imp_res_tac code_includes_subg \\ fs []
      \\ fs [code_locs_def]
      \\ imp_res_tac evaluate_const \\ fs []
      \\ match_mp_tac SUBSET_TRANS
      \\ simp [Once CONJ_COMM] \\ asm_exists_tac \\ fs []
      \\ fs [SUBSET_DEF,DISJOINT_DEF,EXTENSION] \\ rw [])
    \\ strip_tac
    \\ qpat_assum `_ = (Rval _,t)` assume_tac
    \\ drule evaluate_add_clock \\ fs []
    \\ disch_then (qspec_then `ck'` assume_tac)
    \\ qexists_tac `ck+ck'` \\ fs [AC ADD_COMM ADD_ASSOC]
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_IMP_LENGTH
    \\ fs [] \\ Cases_on `a` \\ fs [])
  (* Var *)
  \\ conj_tac >- (
    fs [evaluate_def,calls_def] \\ rw []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ qexists_tac `0` \\ fs []
    \\ fs [LIST_REL_EL_EQN])
  (* If *)
  \\ conj_tac >-
   (fs [evaluate_def,calls_def] \\ rw []
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ Cases_on `evaluate ([x1],env,s)` \\ fs []
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ `subg g' g''` by
     (match_mp_tac calls_subg \\ fs []
      \\ asm_exists_tac \\ fs []
      \\ fs[code_locs_def,ALL_DISTINCT_APPEND]
      \\ strip_tac THEN1
       (match_mp_tac calls_ALL_DISTINCT
        \\ asm_exists_tac \\ fs [wfg_def])
      \\ imp_res_tac calls_ALL_DISTINCT \\ fs[]
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ fs[IN_DISJOINT,SUBSET_DEF]
      \\ metis_tac[numTheory.INV_SUC])
    \\ `wfg g'` by
     (match_mp_tac calls_wfg \\ asm_exists_tac \\ fs []
      \\ fs [code_locs_def,ALL_DISTINCT_APPEND] \\ NO_TAC)
    \\ `wfg g''` by
     (match_mp_tac calls_wfg \\ asm_exists_tac \\ fs []
      \\ fs [code_locs_def,ALL_DISTINCT_APPEND]
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ fs[IN_DISJOINT,SUBSET_DEF]
      \\ metis_tac[numTheory.INV_SUC])
    \\ `wfg g` by
     (match_mp_tac calls_wfg \\ asm_exists_tac \\ fs []
      \\ fs [code_locs_def,ALL_DISTINCT_APPEND]
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ fs[IN_DISJOINT,SUBSET_DEF]
      \\ metis_tac[numTheory.INV_SUC])
    \\ `subg g'' g` by
     (match_mp_tac calls_subg \\ fs []
      \\ asm_exists_tac \\ fs []
      \\ fs[code_locs_def,ALL_DISTINCT_APPEND]
      \\ strip_tac THEN1 (fs [wfg_def])
      \\ imp_res_tac calls_ALL_DISTINCT \\ fs[]
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ fs[IN_DISJOINT,SUBSET_DEF]
      \\ metis_tac[numTheory.INV_SUC])
    \\ imp_res_tac calls_sing \\ rw []
    \\ reverse (Cases_on `q`) \\ fs [] \\ rw [] \\ fs []
    \\ TRY (`e ≠ Rabort Rtype_error` by (CCONTR_TAC \\ fs [] \\ NO_TAC) \\ fs [])
    \\ first_x_assum drule \\ fs []
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
    \\ fs [AND_IMP_INTRO] \\ impl_tac
    \\ TRY (fs [code_locs_def,ALL_DISTINCT_APPEND] \\ NO_TAC)
    \\ fs [GSYM CONJ_ASSOC]
    \\ rpt (disch_then drule) \\ fs []
    \\ impl_tac
    \\ TRY
     (imp_res_tac subg_trans \\ fs []
      \\ imp_res_tac code_includes_subg \\ fs []
      \\ fs [code_locs_def]
      \\ match_mp_tac SUBSET_TRANS
      \\ simp [Once CONJ_COMM] \\ asm_exists_tac \\ fs []
      \\ fs [SUBSET_DEF,DISJOINT_DEF,EXTENSION] \\ rw []
      \\ `ALL_DISTINCT (code_locs [x1] ++ code_locs [x3])` by
            (imp_res_tac ALL_DISTINCT_APPEND_APPEND_IMP \\ NO_TAC)
      \\ drule (GEN_ALL NOT_IN_domain_FST_g)
      \\ rpt (disch_then drule \\ fs [])
      \\ `ALL_DISTINCT (code_locs [x1] ++ code_locs [x2])` by
            (imp_res_tac ALL_DISTINCT_APPEND_APPEND_IMP \\ NO_TAC)
      \\ drule (GEN_ALL NOT_IN_domain_FST_g)
      \\ rpt (disch_then drule \\ fs []) \\ NO_TAC)
    \\ strip_tac \\ fs []
    \\ rw [] \\ fs [PULL_EXISTS,evaluate_def]
    THEN1 (qexists_tac `ck` \\ fs [])
    \\ `?a1. a = [a1]` by
     (imp_res_tac evaluate_IMP_LENGTH
      \\ Cases_on `a` \\ fs [LENGTH_NIL]) \\ rveq \\ fs []
    \\ rveq \\ fs []
    \\ Cases_on `a1 = Boolv T` \\ fs [] \\ rveq \\ fs []
    THEN1
     (first_x_assum drule \\ fs []
      \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
      \\ fs [AND_IMP_INTRO] \\ impl_tac
      THEN1
       (fs [code_locs_def,ALL_DISTINCT_APPEND,wfg_def] \\ rfs []
        \\ imp_res_tac calls_add_SUC_code_locs
        \\ fs [DISJOINT_IMAGE_SUC] \\ fs [IN_DISJOINT]
        \\ CCONTR_TAC \\ fs [] \\ rfs [IMAGE_SUC_SUBSET_UNION]
        \\ fs [SUBSET_DEF]
        \\ first_x_assum drule \\ CCONTR_TAC \\ fs [] \\ metis_tac [])
      \\ fs [GSYM CONJ_ASSOC,AND_IMP_INTRO]
      \\ rpt (disch_then drule \\ fs [])
      \\ impl_tac THEN1
       (imp_res_tac subg_trans \\ fs []
        \\ imp_res_tac code_includes_subg \\ fs []
        \\ fs [code_locs_def]
        \\ imp_res_tac evaluate_const \\ fs []
        \\ match_mp_tac SUBSET_TRANS
        \\ simp [Once CONJ_COMM] \\ asm_exists_tac \\ fs []
        \\ fs [SUBSET_DEF,DISJOINT_DEF,EXTENSION] \\ rw []
        \\ `ALL_DISTINCT (code_locs [x2] ++ code_locs [x3])` by
              (imp_res_tac ALL_DISTINCT_APPEND_APPEND_IMP \\ NO_TAC)
        \\ drule (GEN_ALL NOT_IN_domain_FST_g)
        \\ rpt (disch_then drule \\ fs []))
      \\ strip_tac
      \\ imp_res_tac evaluate_const \\ fs [] \\ rfs []
      \\ qpat_assum `_ = (Rval _,t)` assume_tac
      \\ drule evaluate_add_clock \\ fs []
      \\ disch_then (qspec_then `ck'` assume_tac)
      \\ qexists_tac `ck+ck'` \\ fs [AC ADD_COMM ADD_ASSOC])
    \\ Cases_on `a1 = Boolv F` \\ fs [] \\ rveq \\ fs []
    THEN1
     (first_x_assum drule \\ fs []
      \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
      \\ fs [AND_IMP_INTRO] \\ impl_tac
      THEN1
       (fs [code_locs_def,ALL_DISTINCT_APPEND,wfg_def] \\ rfs []
        \\ imp_res_tac calls_add_SUC_code_locs
        \\ fs [DISJOINT_IMAGE_SUC] \\ fs [IN_DISJOINT]
        \\ CCONTR_TAC \\ fs [] \\ rfs [IMAGE_SUC_SUBSET_UNION]
        \\ fs [SUBSET_DEF]
        \\ first_x_assum drule \\ CCONTR_TAC \\ fs [] \\ metis_tac [])
      \\ fs [GSYM CONJ_ASSOC,AND_IMP_INTRO]
      \\ rpt (disch_then drule \\ fs [])
      \\ impl_tac THEN1
       (imp_res_tac subg_trans \\ fs []
        \\ imp_res_tac code_includes_subg \\ fs []
        \\ fs [code_locs_def]
        \\ imp_res_tac evaluate_const \\ fs []
        \\ match_mp_tac SUBSET_TRANS
        \\ simp [Once CONJ_COMM] \\ asm_exists_tac \\ fs []
        \\ fs [SUBSET_DEF,DISJOINT_DEF,EXTENSION] \\ rw []
        \\ drule (GEN_ALL NOT_IN_domain_FST_g)
        \\ rpt (disch_then drule \\ fs []))
      \\ strip_tac
      \\ imp_res_tac evaluate_const \\ fs [] \\ rfs []
      \\ qpat_assum `_ = (Rval _,t)` assume_tac
      \\ drule evaluate_add_clock \\ fs []
      \\ disch_then (qspec_then `ck'` assume_tac)
      \\ qexists_tac `ck+ck'` \\ fs [AC ADD_COMM ADD_ASSOC]))
  (* Let *)
  \\ conj_tac >- (
    fs [evaluate_def,calls_def] \\ rw []
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ Cases_on `evaluate (xs,env,s)` \\ fs []
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ `subg g' g` by
     (match_mp_tac calls_subg \\ fs []
      \\ asm_exists_tac \\ fs []
      \\ fs[code_locs_def,ALL_DISTINCT_APPEND]
      \\ strip_tac THEN1
       (match_mp_tac calls_ALL_DISTINCT
        \\ asm_exists_tac \\ fs [wfg_def])
      \\ imp_res_tac calls_ALL_DISTINCT \\ fs[]
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ fs[IN_DISJOINT,SUBSET_DEF]
      \\ metis_tac[numTheory.INV_SUC])
    \\ `wfg g'` by
     (match_mp_tac calls_wfg \\ asm_exists_tac \\ fs []
      \\ fs [code_locs_def,ALL_DISTINCT_APPEND])
    \\ reverse (Cases_on `q`) \\ fs [] \\ rw [] \\ fs []
    \\ first_x_assum drule \\ fs []
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
    \\ fs [AND_IMP_INTRO] \\ impl_tac
    \\ TRY (fs [code_locs_def,ALL_DISTINCT_APPEND] \\ NO_TAC)
    \\ rpt (disch_then drule) \\ fs [GSYM CONJ_ASSOC]
    \\ rpt (disch_then drule) \\ fs [AND_IMP_INTRO]
    \\ impl_tac \\ TRY
     (imp_res_tac subg_trans \\ fs []
      \\ imp_res_tac code_includes_subg \\ fs []
      \\ fs [code_locs_def]
      \\ match_mp_tac SUBSET_TRANS
      \\ simp [Once CONJ_COMM] \\ asm_exists_tac \\ fs []
      \\ fs [SUBSET_DEF,DISJOINT_DEF,EXTENSION] \\ rw []
      \\ drule (GEN_ALL NOT_IN_domain_FST_g)
      \\ rpt (disch_then drule \\ fs []) \\ NO_TAC)
    \\ strip_tac \\ fs []
    \\ rw [] \\ fs [PULL_EXISTS,evaluate_def]
    THEN1 (qexists_tac `ck` \\ fs [])
    \\ first_x_assum drule \\ fs []
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
    \\ fs [AND_IMP_INTRO] \\ impl_tac
    THEN1
     (fs [code_locs_def,ALL_DISTINCT_APPEND,wfg_def] \\ rfs []
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ fs [DISJOINT_IMAGE_SUC] \\ fs [IN_DISJOINT]
      \\ CCONTR_TAC \\ fs [] \\ rfs [IMAGE_SUC_SUBSET_UNION]
      \\ fs [SUBSET_DEF]
      \\ first_x_assum drule \\ CCONTR_TAC \\ fs [] \\ metis_tac [])
    \\ fs [GSYM CONJ_ASSOC]
    \\ `LIST_REL (v_rel g1 l1) (a ++ env) (v' ++ env2)` by
         (match_mp_tac EVERY2_APPEND_suff \\ fs [])
    \\ rpt (disch_then drule \\ fs [])
    \\ impl_tac THEN1
     (imp_res_tac subg_trans \\ fs []
      \\ imp_res_tac code_includes_subg \\ fs []
      \\ fs [code_locs_def]
      \\ imp_res_tac evaluate_const \\ fs []
      \\ match_mp_tac SUBSET_TRANS
      \\ simp [Once CONJ_COMM] \\ asm_exists_tac \\ fs []
      \\ fs [SUBSET_DEF,DISJOINT_DEF,EXTENSION] \\ rw [])
    \\ strip_tac
    \\ qpat_assum `_ = (Rval _,t)` assume_tac
    \\ drule evaluate_add_clock \\ fs []
    \\ disch_then (qspec_then `ck'` assume_tac)
    \\ qexists_tac `ck+ck'` \\ fs [AC ADD_COMM ADD_ASSOC]
    \\ `[HD e2] = e2` by (imp_res_tac calls_sing \\ fs [])
    \\ fs [])
  (* Raise *)
  \\ conj_tac >-
   (fs [evaluate_def,calls_def] \\ rw []
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ fs [evaluate_def]
    \\ `[HD e1] = e1` by (imp_res_tac calls_sing \\ fs [])
    \\ fs [dec_clock_def] \\ pop_assum kall_tac
    \\ Cases_on `evaluate ([x1],env,s)` \\ fs []
    \\ `q ≠ Rerr (Rabort Rtype_error)` by (CCONTR_TAC \\ fs []) \\ fs []
    \\ first_x_assum drule \\ fs [code_locs_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ strip_tac \\ fs []
    \\ qexists_tac `ck` \\ fs []
    \\ every_case_tac \\ fs [evalPropsTheory.result_rel_def,PULL_EXISTS]
    \\ rw [] \\ imp_res_tac evaluate_IMP_LENGTH
    \\ Cases_on `a` \\ Cases_on `a'` \\ fs [])
  (* Handle *)
  \\ conj_tac >- (
    fs [evaluate_def,calls_def] \\ rw []
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ Cases_on `evaluate ([x1],env,s1)` \\ fs []
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ `subg g' g` by
     (match_mp_tac calls_subg \\ fs []
      \\ asm_exists_tac \\ fs []
      \\ fs[code_locs_def,ALL_DISTINCT_APPEND]
      \\ strip_tac THEN1
       (match_mp_tac calls_ALL_DISTINCT
        \\ asm_exists_tac \\ fs [wfg_def])
      \\ imp_res_tac calls_ALL_DISTINCT \\ fs[]
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ fs[IN_DISJOINT,SUBSET_DEF]
      \\ metis_tac[numTheory.INV_SUC])
    \\ `wfg g'` by
     (match_mp_tac calls_wfg \\ asm_exists_tac \\ fs []
      \\ fs [code_locs_def,ALL_DISTINCT_APPEND])
    \\ imp_res_tac calls_sing \\ rw []
    \\ Cases_on `q` \\ fs [] \\ rw [] \\ fs []
    \\ TRY (`e ≠ Rabort Rtype_error` by (CCONTR_TAC \\ fs [] \\ NO_TAC) \\ fs [])
    \\ first_x_assum drule \\ fs []
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
    \\ fs [AND_IMP_INTRO] \\ impl_tac
    \\ TRY (fs [code_locs_def,ALL_DISTINCT_APPEND] \\ NO_TAC)
    \\ fs [GSYM CONJ_ASSOC]
    \\ rpt (disch_then drule) \\ fs []
    \\ impl_tac \\ TRY
     (imp_res_tac subg_trans \\ fs []
      \\ imp_res_tac code_includes_subg \\ fs []
      \\ fs [code_locs_def]
      \\ match_mp_tac SUBSET_TRANS
      \\ simp [Once CONJ_COMM] \\ asm_exists_tac \\ fs []
      \\ fs [SUBSET_DEF,DISJOINT_DEF,EXTENSION] \\ rw []
      \\ drule (GEN_ALL NOT_IN_domain_FST_g)
      \\ rpt (disch_then drule \\ fs []) \\ NO_TAC)
    \\ strip_tac \\ fs []
    \\ rw [] \\ fs [PULL_EXISTS,evaluate_def]
    THEN1 (qexists_tac `ck` \\ fs [])
    \\ reverse (Cases_on `e`) \\ fs [] \\ rveq \\ fs []
    THEN1 (qexists_tac `ck` \\ fs [])
    \\ first_x_assum drule \\ fs []
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
    \\ fs [AND_IMP_INTRO] \\ impl_tac
    THEN1
     (fs [code_locs_def,ALL_DISTINCT_APPEND,wfg_def] \\ rfs []
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ fs [DISJOINT_IMAGE_SUC] \\ fs [IN_DISJOINT]
      \\ CCONTR_TAC \\ fs [] \\ rfs [IMAGE_SUC_SUBSET_UNION]
      \\ fs [SUBSET_DEF]
      \\ first_x_assum drule \\ CCONTR_TAC \\ fs [] \\ metis_tac [])
    \\ fs [GSYM CONJ_ASSOC,AND_IMP_INTRO]
    \\ rpt (disch_then drule \\ fs [])
    \\ impl_tac THEN1
     (imp_res_tac subg_trans \\ fs []
      \\ imp_res_tac code_includes_subg \\ fs []
      \\ fs [code_locs_def]
      \\ imp_res_tac evaluate_const \\ fs []
      \\ match_mp_tac SUBSET_TRANS
      \\ simp [Once CONJ_COMM] \\ asm_exists_tac \\ fs []
      \\ fs [SUBSET_DEF,DISJOINT_DEF,EXTENSION] \\ rw [])
    \\ strip_tac
    \\ imp_res_tac evaluate_const \\ fs [] \\ rfs []
    \\ qpat_assum `_ = (Rerr _,t)` assume_tac
    \\ drule evaluate_add_clock \\ fs []
    \\ disch_then (qspec_then `ck'` assume_tac)
    \\ qexists_tac `ck+ck'` \\ fs [AC ADD_COMM ADD_ASSOC])
  (* Op *)
  \\ conj_tac >-
   (fs [evaluate_def,calls_def] \\ rw []
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ fs [evaluate_def]
    \\ Cases_on `evaluate (xs,env,s)` \\ fs []
    \\ `q ≠ Rerr (Rabort Rtype_error)` by (CCONTR_TAC \\ fs []) \\ fs []
    \\ first_x_assum drule \\ fs [code_locs_def]
    \\ rpt (disch_then drule \\ fs[])
    \\ strip_tac \\ qexists_tac `ck` \\ fs []
    \\ reverse (Cases_on `q`) \\ fs [] \\ rw [] \\ fs []
    \\ reverse (Cases_on `do_app op (REVERSE a) r`) \\ fs []
    \\ rw []
    \\ drule (GEN_ALL do_app_thm)
    \\ rpt (disch_then drule \\ fs[])
    \\ disch_then (qspec_then `op` mp_tac) \\ fs []
    THEN1 (every_case_tac \\ fs [])
    \\ rename1 `_ = Rval rr` \\ PairCases_on `rr`
    \\ fs [] \\ rw [] \\ fs [])
  (* Fn *)
  \\ conj_tac >- (
    rw[evaluate_def]
    \\ fs[calls_def]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ fs[IS_SOME_EXISTS] \\ rveq \\ fs[]
    \\ fs[evaluate_def]
    \\ last_x_assum mp_tac
    \\ IF_CASES_TAC \\ fs[]
    \\ strip_tac \\ rveq
    \\ fs[PULL_EXISTS]
    \\ qexists_tac`0`
    \\ simp[v_rel_def,recclosure_rel_def]
    \\ fs[code_locs_def,IN_EVEN]
    \\ imp_res_tac calls_length
    \\ fs[quantHeuristicsTheory.LIST_LENGTH_2] \\ rveq
    \\ fsrw_tac[ETA_ss][PULL_EXISTS,calls_list_def]
    \\ fs[closed_Fn]
    \\ `subg g0 (insert_each x 1 g0)`
    by ( simp[subg_def,insert_each_subspt] \\ fs[wfg_def])
    (*
    \\ `subg g0 g`
    by (
      every_case_tac \\ fs[] \\ rw[]
      \\ drule calls_subg
      \\ qhdtm_x_assum`calls`kall_tac
      \\ drule calls_subg
      \\ (impl_tac >- (fs[ALL_DISTINCT_APPEND] \\ fs[wfg_def]))
      \\ strip_tac
      \\ (impl_tac >- (fs[ALL_DISTINCT_APPEND] \\ fs[wfg_def]))
      \\ strip_tac \\ fs[]
      \\ match_mp_tac subg_trans
      \\ qpat_assum`subg g0 (insert_each _ _ _)`assume_tac
      \\ asm_exists_tac \\ rw[]
      \\ match_mp_tac subg_trans
      \\ asm_exists_tac \\ simp[]
      \\ fs[subg_def]
      \\ fs[IS_SUFFIX_APPEND,GSYM ADD1]
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ rfs[SUBSET_DEF]
      \\ fs[ALL_DISTINCT_APPEND]
      \\ metis_tac[numTheory.INV_SUC] )
    *)
    (*
    \\ qpat_abbrev_tac`l = l0 ∪ _`
    \\ `l0 ⊆ l` by simp[Abbr`l`]
    \\ `state_rel g l s t0` by metis_tac[state_rel_subg]
    *)
    (*
    \\ `subspt (FST g0) (FST g)` by fs[subg_def]
    *)
    \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["g0'"]))
    \\ qexists_tac`g0` \\ fs[]
    \\ fs[ALL_DISTINCT_APPEND]
    \\ `wfg g`
    by (
      reverse every_case_tac \\ fs[] \\ rw[]
      >- ( match_mp_tac calls_wfg \\ asm_exists_tac \\ fs[] )
      \\ qpat_assum`calls _ (insert_each _ _ _) = _`assume_tac
      \\ drule calls_wfg'
      \\ impl_tac
      >- ( fs[wfg'_def,domain_FST_insert_each,wfg_def,IN_EVEN] )
      \\ fs[wfg'_def,wfg_def]
      \\ drule calls_ALL_DISTINCT \\ rfs[]
      \\ ntac 2 strip_tac
      \\ reverse conj_tac
      >- (
        imp_res_tac calls_add_SUC_code_locs
        \\ rfs[SUBSET_DEF,GSYM ADD1,IN_DISJOINT]
        \\ metis_tac[numTheory.INV_SUC] )
      \\ imp_res_tac calls_domain
      \\ rfs[SUBSET_DEF]
      \\ simp[SET_EQ_SUBSET,SUBSET_DEF,GSYM ADD1]
      \\ simp[PULL_EXISTS]
      \\ imp_res_tac calls_IS_SUFFIX
      \\ fs[IS_SUFFIX_APPEND]
      \\ reverse conj_tac
      >- (
        rw[]
        \\ first_x_assum drule
        \\ simp[domain_FST_insert_each]
        \\ strip_tac \\ fs[]
        \\ rveq \\ res_tac \\ rveq
        \\ simp[] )
      \\ imp_res_tac calls_subspt
      \\ imp_res_tac subspt_domain_SUBSET
      \\ fs[domain_FST_insert_each] )
    \\ CASE_TAC \\ fs[] \\ rveq
    \\ simp[evaluate_def]
    \\ fs[DISJOINT_SYM]
    \\ imp_res_tac calls_add_SUC_code_locs
    \\ fs[SUBSET_DEF,GSYM ADD1]
    \\ TRY (Cases_on`new_g'` \\ fs[code_list_def,GSYM ADD1] \\ NO_TAC)
    (*
    \\ `subg g new_g'`
    by (
      match_mp_tac calls_subg_mono
      \\ asm_exists_tac \\ fs[]
      \\ metis_tac[] )
    \\ fs[subg_def]
    \\ imp_res_tac subspt_domain_SUBSET
    \\ fs[SUBSET_DEF,domain_FST_insert_each]
    *)
    \\ rw[] \\ first_x_assum match_mp_tac
    \\ rfs[wfg_def,PULL_EXISTS]
    \\ metis_tac[]
    (*
    \\ rpt conj_tac
    \\ TRY (
      match_mp_tac (GEN_ALL state_rel_subg) \\ fs[]
      \\ first_assum(part_match_exists_tac (el 2 o strip_conj) o concl)
      \\ simp[] )
    \\ TRY ( match_mp_tac subg_refl \\ fs[wfg_def] )
    \\ TRY (
      match_mp_tac (GEN_ALL (MP_CANON LIST_REL_mono))
      \\ first_assum(part_match_exists_tac (last o strip_conj) o concl)
      \\ metis_tac[v_rel_subg,SUBSET_DEF] )
    \\ strip_tac
    \\ `MEM (SUC x) (MAP FST (SND g))` by fs[wfg_def]
    \\ metis_tac[numTheory.INV_SUC]
    *)
    (*
    \\ TRY ( reverse conj_tac >- (
      TRY (
        reverse conj_tac >- (
          spose_not_then strip_assume_tac
          \\ imp_res_tac calls_domain
          \\ imp_res_tac calls_add_SUC_code_locs
          \\ `x ∉ set (code_locs [exp])` by fs[ALL_DISTINCT_APPEND]
          \\ `x ∉ domain (FST g0)`
          by (
            fs[wfg_def]
            \\ fs[SET_EQ_SUBSET,SUBSET_DEF,PULL_EXISTS]
            \\ metis_tac[] )
          \\ `MEM (SUC x) (MAP FST (SND g))`
          by ( drule calls_wfg \\ fs[ALL_DISTINCT_APPEND,wfg_def] )
          \\ fs[SUBSET_DEF]
          \\ metis_tac[numTheory.INV_SUC] ))
      \\ match_mp_tac subg_refl \\ fs[subg_def] ))
    \\ match_mp_tac (GEN_ALL (MP_CANON LIST_REL_mono))
    \\ first_assum(part_match_exists_tac (last o strip_conj) o concl)
    \\ metis_tac[v_rel_subg,SUBSET_REFL]
    *)
    )
  (* Letrec *)
  \\ conj_tac >- cheat
  (* App *)
  \\ conj_tac >- (
    rw[evaluate_def,calls_def]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ fs[code_locs_def]
    \\ qpat_assum`_ = (res,_)`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ last_assum(fn th => mp_tac (MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO]calls_subg) th))
    \\ simp[]
    \\ impl_keep_tac >- fs[ALL_DISTINCT_APPEND,wfg_def] \\ strip_tac
    \\ drule calls_subg
    \\ impl_keep_tac >- (
      imp_res_tac calls_add_SUC_code_locs
      \\ fs[subg_def,ALL_DISTINCT_APPEND,IN_DISJOINT,SUBSET_DEF]
      \\ metis_tac[numTheory.INV_SUC] )
    \\ strip_tac
    \\ `g'' = g` by (every_case_tac \\ fs[])
    \\ rveq \\ fs[]
    (*
    \\ qpat_abbrev_tac`l = l0 ∪ _`
    \\ `l0 ⊆ l` by simp[Abbr`l`]
    *)
    \\ `wfg g'`
    by (
      match_mp_tac calls_wfg
      \\ asm_exists_tac
      \\ fs[ALL_DISTINCT_APPEND] )
    \\ `wfg g`
    by (
      match_mp_tac calls_wfg
      \\ asm_exists_tac \\ fs[] )
    \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      strip_tac \\ rveq \\ rfs[]
      \\ first_x_assum drule \\ fs[DISJOINT_SYM,ALL_DISTINCT_APPEND]
      \\ rpt(disch_then drule)
      \\ impl_tac
      >- (
        conj_tac >- metis_tac[subg_trans]
        \\ simp[]
        \\ reverse conj_tac >- metis_tac[code_includes_subg]
        \\ fs[SUBSET_DEF]
        \\ fs[subg_def]
        \\ imp_res_tac subspt_domain_SUBSET
        \\ fs[SUBSET_DEF] \\ rw[]
        \\ Cases_on`x ∉ domain (FST g)` >- metis_tac[]
        \\ fs[]
        \\ imp_res_tac calls_add_SUC_code_locs
        \\ rfs[wfg_def,SUBSET_DEF,PULL_EXISTS]
        \\ metis_tac[])
      (*
      \\ qpat_abbrev_tac`l' = l0 ∪ _`
      \\ `l' ⊆ l`
      by (
        rw[Abbr`l'`,Abbr`l`,SUBSET_DEF]
        \\ spose_not_then strip_assume_tac
        \\ imp_res_tac calls_add_SUC_code_locs
        \\ `x ∉ set (code_locs [x1])` by (fs[ALL_DISTINCT_APPEND]\\ metis_tac[])
        \\ `MEM (SUC x) (MAP FST (SND g))` by ( fs[wfg_def] )
        \\ `¬MEM (SUC x) (MAP FST (SND g'))` by ( fs[wfg_def] )
        \\ fs[SUBSET_DEF]
        \\ metis_tac[numTheory.INV_SUC] )
      \\ rfs[]
      \\ disch_then(qspecl_then[`env2`,`t0`,`g'`]mp_tac)
      \\ impl_tac
      >- (
        conj_tac
        >- (
          match_mp_tac (GEN_ALL (MP_CANON LIST_REL_mono))
          \\ metis_tac[v_rel_subg]
      *)
      \\ strip_tac
      \\ qexists_tac`ck`
      \\ imp_res_tac calls_length
      \\ `state_rel g1 l1 r t`
      by (
        imp_res_tac evaluate_const \\ fs[]
        \\ metis_tac[state_rel_subg] )
      \\ `exc_rel (v_rel g1 l1) e e'`
      by ( Cases_on`e`\\fs[] \\ metis_tac[v_rel_subg])
      \\ every_case_tac \\ fs[] \\ rw[evaluate_def]
      \\ simp[evaluate_append])
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ qmatch_asmsub_rename_tac`err ≠ Rerr _`
    \\ Cases_on`err = Rerr (Rabort Rtype_error)` \\ fs[]
    \\ first_x_assum drule \\ fs[]
    \\ first_x_assum drule \\ fs[DISJOINT_SYM]
    \\ fs[ALL_DISTINCT_APPEND]
    \\ rpt(disch_then drule)
    \\ impl_tac
    >- (
      conj_tac >- metis_tac[subg_trans]
      \\ simp[]
      \\ reverse conj_tac >- metis_tac[code_includes_subg]
      \\ fs[SUBSET_DEF]
      \\ fs[subg_def]
      \\ imp_res_tac subspt_domain_SUBSET
      \\ fs[SUBSET_DEF] \\ rw[]
      \\ Cases_on`x ∉ domain (FST g)` >- metis_tac[]
      \\ fs[]
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ rfs[wfg_def,SUBSET_DEF,PULL_EXISTS]
      \\ metis_tac[])
    \\ strip_tac \\ fs[]
    (*
    \\ qmatch_asmsub_abbrev_tac`v_rel g' l'`
    \\ `l' ⊆ l`
    by (
      rw[Abbr`l'`,Abbr`l`,SUBSET_DEF]
      \\ spose_not_then strip_assume_tac
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ `x ∉ set (code_locs [x1])` by (fs[ALL_DISTINCT_APPEND]\\ metis_tac[])
      \\ `MEM (SUC x) (MAP FST (SND g))` by ( fs[wfg_def] )
      \\ `¬MEM (SUC x) (MAP FST (SND g'))` by ( fs[wfg_def])
      \\ fs[SUBSET_DEF]
      \\ metis_tac[numTheory.INV_SUC] )
    *)
    \\ disch_then(qspecl_then[`env2`,`t`]mp_tac)
    (* \\ `l0 ⊆ l'` by simp[Abbr`l'`] *)
    \\ disch_then(qspecl_then[`l1`,`g1`]mp_tac)
    \\ impl_tac
    >- (
      imp_res_tac evaluate_const \\ fs[]
      (*
      \\ match_mp_tac (GEN_ALL (MP_CANON LIST_REL_mono))
      \\ metis_tac[v_rel_subg,subg_trans]
      *)
      \\ fs[SUBSET_DEF])
    \\ strip_tac \\ rveq
    (*
    \\ qmatch_assum_abbrev_tac`state_rel g ll _ _`
    \\ `ll ⊆ l`
    by ( simp[Abbr`ll`,Abbr`l`,SUBSET_DEF] )
    \\ `l' ⊆ ll ` by simp[Abbr`ll`]
    \\ `subg g g`
    by (
      match_mp_tac subg_refl
      \\ imp_res_tac calls_ALL_DISTINCT
      \\ rfs[DISJOINT_SYM] )
    *)
    \\ qpat_assum`_ = (ys,_)`mp_tac
    \\ qmatch_goalsub_abbrev_tac`COND b`
    \\ reverse IF_CASES_TAC \\ fs[]
    >- (
      strip_tac \\ rveq
      \\ simp[evaluate_def]
      \\ imp_res_tac calls_length
      \\ simp[]
      \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
      \\ rveq \\ fs[]
      \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
      >- (
        strip_tac \\ rveq \\ fs[]
        \\ qpat_assum`evaluate(es,env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
        \\ disch_then(qspec_then`ck'`mp_tac) \\ simp[] \\ strip_tac
        \\ qexists_tac`ck+ck'` \\ fs[]
        (*
        \\ imp_res_tac evaluate_const \\ fs[]
        \\ conj_tac >- metis_tac[state_rel_subg]
        \\ Cases_on`e` \\ fs[]
        \\ metis_tac[v_rel_subg]*))
      \\ strip_tac \\ fs[] \\ rfs[]
      \\ imp_res_tac evaluate_length_imp
      \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
      \\ rveq \\ fs[]
      (*
      \\ drule (GEN_ALL evaluate_app_imp_clos_rel)
      \\ disch_then drule
      \\ impl_tac >- (CCONTR_TAC \\ fs[] \\ fs[])
      \\ strip_tac
      *)
      \\ first_x_assum drule
      (*
      \\ qmatch_assum_rename_tac `LIST_REL (v_rel g' l') ev1 ev2`
      \\ `LIST_REL (v_rel g ll) ev1 ev2` by metis_tac[LIST_REL_mono,v_rel_subg]
      *)
      \\ disch_then drule
      \\ disch_then drule
      \\ impl_tac >- rw[]
      \\ strip_tac \\ simp[]
      \\ qpat_assum`evaluate(es,env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
      \\ disch_then(qspec_then`ck'+ck''`mp_tac) \\ simp[] \\ strip_tac
      \\ qpat_assum`evaluate([_],env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
      \\ disch_then(qspec_then`ck''`mp_tac) \\ simp[] \\ strip_tac
      \\ qexists_tac`ck+ck'+ck''` \\ fs[]
      (*
      \\ conj_tac >- metis_tac[state_rel_subg,state_rel_def]
      \\ Cases_on`res` \\ fs[] \\ TRY (Cases_on`e` \\ fs[])
      \\ TRY (match_mp_tac (GEN_ALL (MP_CANON LIST_REL_mono)))
      \\ metis_tac[v_rel_subg]*))
    \\ qpat_assum`Abbrev(IS_SOME _ ∧ _)`mp_tac
    \\ simp[markerTheory.Abbrev_def,IS_SOME_EXISTS]
    \\ strip_tac \\ rveq \\ fs[]
    \\ `x ∈ domain (FST g)` by simp[domain_lookup]
    \\ `x ∈ domain (FST g1)` by (
      fs[subg_def]
      \\ imp_res_tac subspt_domain_SUBSET
      \\ fs[SUBSET_DEF] )
    \\ `x ∉ l1` by ( fs[IN_DISJOINT] \\ metis_tac[] )
    (*
    \\ `x ∉ ll`
    by (
      simp[Abbr`ll`]
      \\ Cases_on`x ∈ domain (FST g')`
      >- (fs[IN_DISJOINT] \\ metis_tac[])
      \\ `wfg g'` by imp_res_tac calls_wfg
      \\ `¬MEM (SUC x) (MAP FST (SND g'))` by fs[wfg_def]
      \\ `MEM (SUC x) (MAP FST (SND g))` by fs[wfg_def]
      \\ `MEM x (code_locs [x1])`
      by (
        imp_res_tac calls_add_SUC_code_locs
        \\ fs[SUBSET_DEF]
        \\ metis_tac[numTheory.INV_SUC] )
      \\ `x ∉ l0` by (fs[IN_DISJOINT] \\ metis_tac[])
      \\ simp[Abbr`l'`]
      \\ fs[ALL_DISTINCT_APPEND] )
    *)
    \\ IF_CASES_TAC \\ fs[] \\ strip_tac \\ rveq \\ fs[]
    \\ simp[evaluate_def]
    >- (
      drule (Q.GEN`s`pure_correct)
      \\ disch_then(qspec_then`r`mp_tac)
      \\ simp[]
      \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
      >- (CASE_TAC \\ fs[])
      \\ ntac 2 strip_tac \\ rveq
      \\ fs[quantHeuristicsTheory.LIST_LENGTH_2] \\ rveq
      \\ rfs[] \\ rveq
      (*
      \\ qmatch_assum_rename_tac `LIST_REL (v_rel g' l') ev1 ev2`
      \\ `LIST_REL (v_rel g ll) ev1 ev2` by metis_tac[LIST_REL_mono,v_rel_subg]
      *)
      \\ qmatch_assum_rename_tac`LIST_REL (v_rel g1 l1) ev1 ev2`
      \\ Cases_on`ev1 = []`
      \\ imp_res_tac evaluate_length_imp \\ rfs[]
      \\ fs[evaluate_app_rw]
      \\ qpat_assum`_ = (res,_)`mp_tac
      \\ BasicProvers.TOP_CASE_TAC \\ fs[]
      \\ strip_tac
      \\ drule (GEN_ALL dest_closure_v_rel_lookup)
      \\ disch_then drule
      \\ disch_then drule
      \\ impl_tac >- rw[]
      \\ strip_tac
      \\ `ALOOKUP (SND g) (x+1) = ALOOKUP (SND g1) (x+1)`
      by (
        fs[subg_def]
        \\ Cases_on`ALOOKUP (SND g) (x+1)` \\ fs[]
        >- (
          imp_res_tac ALOOKUP_FAILS
          \\ `¬MEM (SUC x) (MAP FST (SND g))`
          by (
            simp[MEM_MAP,ADD1,Once FORALL_PROD]
            \\ metis_tac[] )
          \\ rfs[wfg_def,GSYM ADD1] )
        \\ rpt(first_x_assum drule)
        \\ simp[] )
      (*
      by (
        `ALL_DISTINCT (MAP FST (SND g1))` by fs[subg_def]
        \\ `∃ls. SND g1 =  ls ++ SND g` by (metis_tac[subg_def,IS_SUFFIX_APPEND])
        \\ pop_assum SUBST_ALL_TAC
        \\ simp_tac(srw_ss())[ALOOKUP_APPEND]
        \\ BasicProvers.CASE_TAC
        \\ fs[ALL_DISTINCT_APPEND]
        \\ imp_res_tac ALOOKUP_MEM
        \\ `¬MEM (x+1) (MAP FST (SND g))`
        by (
          first_x_assum match_mp_tac
          \\ simp[MEM_MAP,PULL_EXISTS]
          \\ metis_tac[FST] )
        \\ rfs[wfg_def,GSYM ADD1] )
      *)
      \\ rfs[]
      \\ drule (GEN_ALL code_includes_ALOOKUP)
      \\ disch_then drule \\ strip_tac
      \\ `t.code = t0.code` by (imp_res_tac evaluate_const \\ fs[])
      \\ first_x_assum drule
      \\ disch_then drule
      \\ qpat_assum`state_rel g1 l1 r t`assume_tac
      (*
      \\ `state_rel g ll r t` by ( metis_tac[state_rel_subg] )
      *)
      \\ disch_then drule
      \\ impl_tac >- rw[]
      \\ strip_tac
      \\ imp_res_tac LIST_REL_LENGTH \\ fs[]
      \\ Cases_on`ev2 = []` \\ fs[]
      \\ fs[evaluate_app_rw]
      \\ qpat_assum`_ = (res',_)`mp_tac
      \\ imp_res_tac state_rel_clock \\ fs[]
      \\ IF_CASES_TAC \\ fs[]
      >- (
        strip_tac \\ rveq
        \\ qexists_tac`ck` \\ simp[find_code_def]
        \\ match_mp_tac state_rel_with_clock
        \\ metis_tac[state_rel_subg] )
      \\ simp[evaluate_def,evaluate_GENLIST_Var]
      \\ simp[find_code_def]
      \\ simp[Once dec_clock_def]
      \\ `t'.code = t.code` by (imp_res_tac evaluate_const \\ fs[])
      \\ fs[]
      \\ simp[Once dec_clock_def]
      \\ imp_res_tac evaluate_length_imp \\ fs[NOT_LESS]
      \\ IF_CASES_TAC
      >- (
        fs[] \\ strip_tac \\ rveq \\ fs[]
        \\ `t'.clock = LENGTH ev2 - ck''` by decide_tac
        \\ fs[]
        \\ qexists_tac`ck` \\ simp[]
        \\ fs[dec_clock_def])
      \\ fs[NOT_LESS_EQUAL]
      \\ strip_tac
      \\ fs[dec_clock_def,TAKE_APPEND1]
      \\ qpat_assum`evaluate(es,env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
      \\ disch_then(qspec_then`ck''`mp_tac) \\ simp[] \\ strip_tac
      \\ qexists_tac`ck+ck''` \\ simp[]
      \\ qpat_assum`_ = (res',_)`mp_tac
      \\ BasicProvers.TOP_CASE_TAC \\ fs[]
      \\ BasicProvers.TOP_CASE_TAC \\ fs[]
      \\ TRY BasicProvers.TOP_CASE_TAC \\ fs[]
      \\ strip_tac \\ rveq \\ fs[]
      \\ TRY (Cases_on`res`\\fs[])
      \\ rveq \\ fs[]
      \\ TRY (
        pop_assum mp_tac \\ CASE_TAC \\ fs[]
        \\ strip_tac \\ rveq \\ fs[] \\ rveq \\ fs[])
      \\ imp_res_tac evaluate_const \\ fs[]
      \\ rpt conj_tac
      \\ TRY(match_mp_tac (GEN_ALL state_rel_subg))
      \\ TRY(match_mp_tac (GEN_ALL (MP_CANON LIST_REL_mono)))
      \\ TRY (Cases_on`e''` \\ fs[])
      \\ metis_tac[v_rel_subg])
    \\ simp[evaluate_append]
    \\ imp_res_tac calls_length
    \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
    \\ rveq \\ fs[]
    \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      rw[]
      \\ qpat_assum`evaluate(es,env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
      \\ disch_then(qspec_then`ck'`mp_tac) \\ simp[] \\ strip_tac
      \\ qexists_tac`ck+ck'` \\ simp[]
      \\ rw[] \\ TRY(Cases_on`e`\\fs[])
      \\ metis_tac[state_rel_subg,state_rel_def,v_rel_subg])
    \\ strip_tac \\ fs[]
    \\ simp[evaluate_GENLIST_Var]
    \\ imp_res_tac evaluate_length_imp \\ fs[]
    \\ fs[quantHeuristicsTheory.LIST_LENGTH_2] \\ rveq
    \\ qpat_assum`LENGTH [_] = _`(assume_tac o SYM) \\ fs[]
    \\ fs[quantHeuristicsTheory.LIST_LENGTH_2] \\ rveq \\ fs[] \\ rveq
    \\ first_x_assum drule
    (*
    \\ qmatch_assum_rename_tac `LIST_REL (v_rel g' l') ev1 ev2`
    \\ `LIST_REL (v_rel g ll) ev1 ev2` by metis_tac[LIST_REL_mono,v_rel_subg]
    *)
    \\ qmatch_assum_rename_tac`LIST_REL (v_rel _ _) ev1 ev2`
    \\ rpt(disch_then drule)
    \\ strip_tac
    \\ simp[find_code_def]
    \\ `t'.code = t0.code` by (imp_res_tac evaluate_const \\ fs[])
    \\ imp_res_tac evaluate_length_imp \\ fs[] \\ rw[]
    \\ Cases_on`ev1 = []` \\ fs[]
    \\ fs[evaluate_app_rw]
    \\ qpat_assum`_ = (res,_)`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ drule (GEN_ALL dest_closure_v_rel_lookup)
    \\ disch_then drule
    \\ disch_then drule
    \\ impl_tac >- rw[]
    \\ strip_tac \\ fs[]
    \\ Cases_on`ev2 = []` \\ fs[]
    \\ fs[evaluate_app_rw]
    \\ qpat_assum`_ = (res',_)`mp_tac
    \\ imp_res_tac state_rel_clock \\ fs[]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs[]
    \\ `ALOOKUP (SND g) (x+1) = ALOOKUP (SND g1) (x+1)`
    by (
      fs[subg_def]
      \\ Cases_on`ALOOKUP (SND g) (x+1)` \\ fs[]
      >- (
        imp_res_tac ALOOKUP_FAILS
        \\ `¬MEM (SUC x) (MAP FST (SND g))`
        by (
          simp[MEM_MAP,ADD1,Once FORALL_PROD]
          \\ metis_tac[] )
        \\ rfs[wfg_def,GSYM ADD1] )
      \\ rpt(first_x_assum drule)
      \\ simp[] )
    (*
    by (
      `ALL_DISTINCT (MAP FST (SND g1))` by fs[subg_def]
      \\ `∃ls. SND g1 =  ls ++ SND g` by (metis_tac[subg_def,IS_SUFFIX_APPEND])
      \\ pop_assum SUBST_ALL_TAC
      \\ simp_tac(srw_ss())[ALOOKUP_APPEND]
      \\ BasicProvers.CASE_TAC
      \\ fs[ALL_DISTINCT_APPEND]
      \\ imp_res_tac ALOOKUP_MEM
      \\ `¬MEM (x+1) (MAP FST (SND g))`
      by (
        first_x_assum match_mp_tac
        \\ simp[MEM_MAP,PULL_EXISTS]
        \\ metis_tac[FST] )
      \\ rfs[wfg_def,GSYM ADD1] )
    *)
    \\ rfs[]
    \\ imp_res_tac code_includes_ALOOKUP \\ fs[]
    \\ IF_CASES_TAC \\ fs[]
    >- (
      strip_tac \\ rveq
      \\ strip_tac \\ rveq
      \\ qpat_assum`evaluate(es,env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
      \\ disch_then(qspec_then`ck'`mp_tac) \\ simp[] \\ strip_tac
      \\ qexists_tac`ck+ck'` \\ simp[]
      \\ match_mp_tac state_rel_with_clock
      \\ metis_tac[state_rel_subg])
    \\ simp[Once dec_clock_def]
    \\ simp[evaluate_def,evaluate_GENLIST_Var]
    \\ simp[find_code_def]
    \\ simp[Once dec_clock_def]
    \\ simp[Once dec_clock_def]
    \\ IF_CASES_TAC
    >- (
      fs[] \\ strip_tac \\ rveq \\ fs[]
      \\ `t'.clock = LENGTH ev2 - ck''` by decide_tac
      \\ fs[] \\ strip_tac
      \\ qpat_assum`evaluate(es,env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
      \\ disch_then(qspec_then`ck'`mp_tac) \\ simp[] \\ strip_tac
      \\ qexists_tac`ck+ck'` \\ simp[]
      \\ fs[dec_clock_def]
      \\ match_mp_tac (GEN_ALL state_rel_subg)
      \\ fs[] \\ metis_tac[] )
    \\ fs[NOT_LESS,NOT_LESS_EQUAL]
    \\ strip_tac
    \\ fs[dec_clock_def,TAKE_APPEND1]
    \\ IF_CASES_TAC \\ fs[]
    >- (
      strip_tac \\ rveq \\ fs[]
      \\ qpat_assum`evaluate(es,env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
      \\ disch_then(qspec_then`ck'`mp_tac) \\ simp[] \\ strip_tac
      \\ qexists_tac`ck+ck'` \\ simp[]
      \\ match_mp_tac state_rel_with_clock
      \\ metis_tac[state_rel_subg] )
    \\ fs[NOT_LESS]
    \\ strip_tac
    \\ qpat_assum`evaluate(es,env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
    \\ disch_then(qspec_then`ck''+ck'`mp_tac) \\ simp[] \\ strip_tac
    \\ qexists_tac`ck+ck'+ck''` \\ simp[]
    \\ qpat_assum`evaluate([_],env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
    \\ disch_then(qspec_then`ck''`mp_tac) \\ simp[] \\ strip_tac
    \\ simp[TAKE_APPEND1]
    \\ qpat_assum`_ = (res',_)`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ TRY BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ strip_tac \\ rveq \\ fs[]
    \\ TRY (Cases_on`res`\\fs[])
    \\ rveq \\ fs[]
    \\ TRY (
      pop_assum mp_tac \\ CASE_TAC \\ fs[]
      \\ strip_tac \\ rveq \\ fs[] \\ rveq \\ fs[])
    \\ imp_res_tac evaluate_const \\ fs[]
    \\ rpt conj_tac
    \\ TRY(match_mp_tac (GEN_ALL state_rel_subg))
    \\ TRY(match_mp_tac (GEN_ALL (MP_CANON LIST_REL_mono)))
    \\ TRY (Cases_on`e''` \\ fs[])
    \\ metis_tac[v_rel_subg])
  (* Tick *)
  \\ conj_tac >-
   (fs [evaluate_def,calls_def] \\ rw []
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ `t0.clock = s.clock` by fs [state_rel_def]
    \\ fs [evaluate_def]
    \\ `[HD e1] = e1` by (imp_res_tac calls_sing \\ fs [])
    THEN1 (qexists_tac `0` \\ fs [state_rel_def])
    \\ fs [dec_clock_def] \\ pop_assum kall_tac
    \\ first_x_assum drule \\ fs [code_locs_def]
    \\ rpt (disch_then drule)
    \\ disch_then (qspec_then `t0 with clock := t0.clock-1` mp_tac)
    \\ fs [] \\ impl_tac THEN1 fs [state_rel_def]
    \\ strip_tac \\ asm_exists_tac \\ fs [])
  (* Call *)
  \\ conj_tac >- (
    rw[evaluate_def,calls_def]
    \\ pairarg_tac \\ fs[]
    \\ qpat_assum`_ = (res,s)`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ `r.code = FEMPTY`
    by (
      imp_res_tac evaluate_const
      \\ fs[state_rel_def])
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    >- ( simp[find_code_def] )
    \\ strip_tac \\ rveq \\ rfs[]
    \\ rw[evaluate_def]
    \\ first_x_assum drule
    \\ fs[code_locs_def]
    \\ disch_then drule \\ fs[]
    \\ rpt(disch_then drule) \\ rw[]
    \\ qexists_tac`ck`
    \\ rw[] )
  \\ conj_tac >- ( rw[evaluate_def] \\ qexists_tac`0` \\ rw[] )

  (* app cons *)
  \\ simp[evaluate_def]
  \\ rpt gen_tac \\ strip_tac
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  >- (
    simp[PULL_EXISTS]
    \\ rpt gen_tac \\ strip_tac
    \\ simp[evaluate_app_rw]
    \\ drule (GEN_ALL dest_closure_v_rel)
    \\ disch_then drule \\ fs[PULL_EXISTS]
    \\ disch_then drule \\ disch_then drule
    \\ strip_tac \\ fs[]
    \\ imp_res_tac state_rel_clock \\ fs[]
    \\ qexists_tac`0` \\ fs[]
    \\ imp_res_tac LIST_REL_LENGTH
    \\ rw[] \\ fs[] \\ rw[dec_clock_def]
    \\ match_mp_tac state_rel_with_clock \\ fs[] )
  \\ fs[PULL_EXISTS]
  \\ rpt gen_tac \\ strip_tac
  \\ simp[evaluate_app_rw]
  \\ drule (GEN_ALL dest_closure_v_rel)
  \\ disch_then drule \\ fs[PULL_EXISTS]
  \\ disch_then drule \\ disch_then drule
  \\ strip_tac \\ fs[]
  \\ imp_res_tac state_rel_clock \\ fs[]
  \\ qpat_assum`_ = (res,_)`mp_tac
  \\ IF_CASES_TAC
  >- (
    rw[]
    \\ qexists_tac`0` \\ fs[]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs[]
    \\ match_mp_tac state_rel_with_clock \\ fs[] )
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ qmatch_assum_rename_tac`_ = (res',_)`

  \\ Cases_on`res' = Rerr (Rabort Rtype_error)` \\ fs[]
  \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
  >- (
    strip_tac \\ rveq \\ fs[] \\ rw[]
    \\ fs[PULL_EXISTS] \\ rfs[]
    \\ fs[recclosure_rel_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ qmatch_assum_rename_tac`v_rel g1 l1 f f'`
    \\ qmatch_assum_rename_tac`LIST_REL _ rest1 rest2`
    \\ first_x_assum(qspecl_then[`g1`,`l1`]mp_tac o CONV_RULE(RESORT_FORALL_CONV List.rev))
    \\ (fn g as (asl,w) =>
        let
          val (fa,_) = dest_imp w
          val (_,b) = strip_forall fa
          val (tm,_) = dest_imp b
          val tms = find_terms (fn x => type_of x = bool andalso free_in x fa) tm
        in
          SUBGOAL_THEN (list_mk_conj tms) strip_assume_tac
        end g)
    >- (
      fs[code_locs_map]
      \\ imp_res_tac ALL_DISTINCT_FLAT_EVERY >>
      fs[Q.SPEC`MAP _ _`every_Fn_SOME_EVERY,
         Q.SPEC`MAP _ _`every_Fn_vs_NONE_EVERY,
         EVERY_MAP,EVERY_MEM,NOT_LESS_EQUAL]
      \\ `MEM (FST (EL i fns2),e) fns1` by metis_tac[MEM_EL]
      \\ fs[EVERY_MAP,EVERY_MEM]
      \\ fs[IN_DISJOINT,SUBSET_DEF,MEM_FLAT,PULL_EXISTS,MEM_MAP]
      \\ rpt(first_x_assum drule) \\ simp[]
      \\ metis_tac[SND] )
    \\ simp[]
    \\ qmatch_asmsub_abbrev_tac`COND b`
    \\ reverse(Cases_on`b`) \\ fs[] \\ rveq
    >- (
      drule (GEN_ALL calls_el_sing)
      \\ disch_then (qspec_then`i`mp_tac)
      \\ impl_tac >- fs[wfg_def]
      \\ simp[EL_MAP] \\ strip_tac
      \\ disch_then drule
      \\ qmatch_goalsub_abbrev_tac`dec_clock dk s0`
      \\ disch_then(qspecl_then[`dec_clock dk t0`,`args2`]mp_tac)
      \\ impl_tac
      >- (
        fs[dec_clock_def]
        \\ rfs[wfg_def]
        (*
        \\ conj_tac
        >- (
          fs[IN_DISJOINT,SUBSET_DEF,PULL_EXISTS,TAKE_MAP,code_locs_map,MEM_FLAT,MEM_MAP]
          \\ spose_not_then strip_assume_tac
          \\ first_x_assum drule \\ simp[]
          \\ conj_tac >- ( metis_tac[] )
          \\ simp[Once MEM_EL]
          \\ spose_not_then strip_assume_tac \\ rveq
          \\ rfs[EL_TAKE]
          \\ metis_tac[numTheory.INV_SUC,LESS_TRANS,MEM_EL] )
        *)
        \\ conj_tac
        >- ( match_mp_tac state_rel_with_clock \\ fs[] )
        \\ conj_tac >- metis_tac[subg_trans]
        \\ conj_tac >- ( fs[SUBSET_DEF] )
        \\ metis_tac[code_includes_subg,state_rel_def] )
      \\ strip_tac
      \\ imp_res_tac calls_length \\ fs[]
      \\ simp[EL_ZIP]
      \\ fs[dec_clock_def]
      \\ imp_res_tac LIST_REL_LENGTH \\ fs[]
      \\ qexists_tac`ck` \\ simp[] \\ rfs[] )
    \\ REWRITE_TAC[calls_list_MAPi]
    \\ simp[]
    \\ simp[evaluate_def,evaluate_GENLIST_Var]
    \\ simp[find_code_def]
    \\ simp[EVAL``(closSem$dec_clock _ _).code``]
    \\ qmatch_assum_abbrev_tac`subg gd g1`
    \\ `code_includes (SND gd) t0.code`
    by ( metis_tac[code_includes_subg,state_rel_def] )
    \\ pop_assum mp_tac
    \\ imp_res_tac calls_length \\ fs[]
    \\ `ALOOKUP (SND gd) (2 * i + loc + 1) = SOME (EL i (ZIP (MAP FST fns1,es)))`
    by (
      simp[Abbr`gd`]
      \\ simp[ALOOKUP_code_list]
      \\ DEEP_INTRO_TAC some_intro \\ simp[] )
    \\ strip_tac
    \\ drule (GEN_ALL code_includes_ALOOKUP)
    \\ disch_then drule
    \\ simp[] \\ strip_tac
    \\ simp[EL_ZIP,EL_MAP]
    \\ strip_tac
    \\ simp[dec_clock_def]
    \\ qpat_assum`calls _ _ = (es,_)`assume_tac
    \\ drule calls_replace_SND
    \\ disch_then(qspec_then`insert_each' loc (LENGTH fns1) g0`mp_tac)
    \\ simp[FST_insert_each']
    \\ drule calls_IS_SUFFIX
    \\ simp[IS_SUFFIX_APPEND]
    \\ strip_tac \\ simp[]
    \\ strip_tac
    \\ drule (GEN_ALL calls_el_sing)
    \\ disch_then(qspec_then`i`mp_tac)
    \\ impl_tac
    >- (
      fs[MAP_FST_insert_each']
      \\ fs[ALL_DISTINCT_APPEND,ALL_DISTINCT_GENLIST]
      \\ conj_tac
      >- (
        rfs[wfg_def,MEM_GENLIST,IN_DISJOINT]
        \\ metis_tac[] )
      \\ conj_asm1_tac
      >- (
        rfs[wfg_def,IN_DISJOINT,MEM_GENLIST,GSYM ADD1]
        \\ metis_tac[numTheory.INV_SUC,DECIDE``2 * i + SUC loc = SUC (2*i+loc)``] )
      \\ match_mp_tac wfg_insert_each'
      \\ fs[IN_DISJOINT,MEM_GENLIST]
      \\ rfs[wfg_def]
      \\ spose_not_then strip_assume_tac
      \\ metis_tac[numTheory.INV_SUC,DECIDE``2 * i + SUC loc = SUC (2*i+loc)``,ADD1] )
    \\ simp[EL_MAP]
    \\ strip_tac
    \\ first_x_assum drule
    \\ qmatch_goalsub_abbrev_tac`dec_clock dk s0`
    \\ qmatch_asmsub_abbrev_tac`(n,e)`
    \\ disch_then(qspecl_then[`dec_clock dk t0`,`args2`]mp_tac)
    \\ impl_tac
    >- (
      fs[dec_clock_def]
      \\ rfs[wfg_def]
      \\ conj_tac
      >- ( match_mp_tac state_rel_with_clock \\ fs[] )
      \\ conj_tac >- cheat (* subg over insert_each' *)
      \\ conj_tac >- ( fs[SUBSET_DEF] )
      \\ cheat (* code_includes over insert_each' *))
    \\ REWRITE_TAC[calls_list_MAPi]
    \\ simp[dec_clock_def]
    \\ `∀v. has_var v (SND (free [EL i es])) ⇒ v < n`
    by (
      fs[markerTheory.Abbrev_def,LIST_REL_EL_EQN]
      \\ first_x_assum(qspec_then`i`mp_tac)
      \\ simp[] )
    \\ cheat (* need to know that evaluate only depends on free vars *))
  \\ imp_res_tac evaluate_length_imp
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
  \\ strip_tac \\ rveq \\ fs[] \\ rfs[]
  \\ fs[PULL_EXISTS]
  \\ cheat);

val _ = export_theory();
