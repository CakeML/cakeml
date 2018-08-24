open preamble backendPropsTheory match_goal dep_rewrite
     closSemTheory closPropsTheory
     clos_callTheory
     db_varsTheory;

val _ = new_theory"clos_callProof";

(* TODO These are the same. Put in closLang? *)
val _ = temp_bring_to_front_overload "free" {Name="free", Thy="clos_call"};
val _ = temp_bring_to_front_overload "closed" {Name="closed", Thy="clos_call"};

val _ = temp_bring_to_front_overload"lookup"{Name="lookup",Thy="sptree"};
val _ = temp_bring_to_front_overload"insert"{Name="insert",Thy="sptree"};
val _ = temp_bring_to_front_overload"delete"{Name="delete",Thy="sptree"};
val _ = temp_bring_to_front_overload"map"{Name="map",Thy="sptree"};
val _ = temp_bring_to_front_overload"wf"{Name="wf",Thy="sptree"};

(* TODO: move *)

val _ = temp_bring_to_front_overload "compile" {Name="compile", Thy="clos_call"};

val MEM_REPLICATE_EQ = Q.store_thm("MEM_REPLICATE_EQ",
  `!n x y. MEM x (REPLICATE n y) <=> x = y /\ n <> 0`,
  Induct \\ fs [REPLICATE] \\ rw [] \\ eq_tac \\ rw []);

val PUSH_EXISTS_IMP = SPEC_ALL RIGHT_EXISTS_IMP_THM;

val TAKE_MAP = Q.store_thm("TAKE_MAP",
  `∀ls n f. TAKE n (MAP f ls) = MAP f (TAKE n ls)`,
  Induct \\ rw[] \\ Cases_on`n` \\ rw[]);

val IS_SUFFIX_TRANS = Q.store_thm("IS_SUFFIX_TRANS",
  `∀l1 l2 l3. IS_SUFFIX l1 l2 ∧ IS_SUFFIX l2 l3 ⇒ IS_SUFFIX l1 l3`,
  rw[IS_SUFFIX_APPEND] \\ metis_tac[APPEND_ASSOC]);

val ALL_DISTINCT_FLAT_EVERY = Q.store_thm("ALL_DISTINCT_FLAT_EVERY",
  `∀ls. ALL_DISTINCT (FLAT ls) ⇒ EVERY ALL_DISTINCT ls`,
  Induct \\ simp[ALL_DISTINCT_APPEND]);

val IN_EVEN = SIMP_CONV std_ss [IN_DEF] ``x ∈ EVEN``;

val v_size_lemma = Q.prove(
  `MEM (v:closSem$v) vl ⇒ v_size v < v1_size vl`,
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

val code_locs_GENLIST_Var = Q.store_thm("code_locs_GENLIST_Var[simp]",
  `∀n t i. code_locs (GENLIST_Var t i n) = []`,
  Induct \\ simp[code_locs_def,Once GENLIST_Var_def,code_locs_append]);

val fv_GENLIST_Var_tra = Q.store_thm("fv_GENLIST_Var_tra",
  `∀n tra i. fv v (GENLIST_Var tra i n) ⇔ v < n`,
  Induct \\ simp[fv_def,Once GENLIST_Var_def,SNOC_APPEND]);

val evaluate_GENLIST_Var_tra = Q.store_thm("evaluate_GENLIST_Var_tra",
  `∀n tr i.
   evaluate (GENLIST_Var tr i n,env,s) =
   if n ≤ LENGTH env then (Rval (TAKE n env),s)
   else (Rerr (Rabort Rtype_error),s)`,
  Induct \\ rw[Once GENLIST_Var_def,evaluate_def,evaluate_append] \\
  simp[TAKE_EL_SNOC,ADD1]);

val evaluate_add_clock =
  evaluate_add_to_clock
  |> SIMP_RULE (srw_ss()) []
  |> CONJUNCT1 |> GEN_ALL
  |> REWRITE_RULE[GSYM AND_IMP_INTRO]

val DISJOINT_IMAGE_SUC = Q.store_thm("DISJOINT_IMAGE_SUC",
  `DISJOINT (IMAGE SUC x) (IMAGE SUC y) <=> DISJOINT x y`,
  fs [IN_DISJOINT] \\ metis_tac [DECIDE ``(SUC n = SUC m) <=> (m = n)``]);

val IMAGE_SUC_SUBSET_UNION = Q.store_thm("IMAGE_SUC_SUBSET_UNION",
  `IMAGE SUC x SUBSET IMAGE SUC y UNION IMAGE SUC z <=>
    x SUBSET y UNION z`,
  fs [SUBSET_DEF] \\ metis_tac [DECIDE ``(SUC n = SUC m) <=> (m = n)``]);

val ALL_DISTINCT_APPEND_APPEND_IMP = Q.store_thm("ALL_DISTINCT_APPEND_APPEND_IMP",
  `ALL_DISTINCT (xs ++ ys ++ zs) ==>
    ALL_DISTINCT (xs ++ ys) /\ ALL_DISTINCT (xs ++ zs) /\ ALL_DISTINCT (ys ++ zs)`,
  fs [ALL_DISTINCT_APPEND]);

val is_Recclosure_def = Define`
  is_Recclosure (Recclosure _ _ _ _ _) = T ∧
  is_Recclosure _ = F`;
val _ = export_rewrites["is_Recclosure_def"];

val every_refv = Define
  `(every_refv P (ValueArray vs) ⇔ EVERY P vs) ∧
   (every_refv P _ ⇔ T)`
val _ = export_rewrites["every_refv_def"];

(* -- *)

(* correctness of free *)

val IMP_EXISTS_IFF = Q.prove(
  `!xs. (!x. MEM x xs ==> (P x <=> Q x)) ==>
         (EXISTS P xs <=> EXISTS Q xs)`,
  Induct \\ fs []);

val free_thm = Q.prove(
  `!xs.
     let (ys,l) = free xs in
       !n. (fv n ys = has_var n l) /\
           (fv n xs = has_var n l)`,
  recInduct free_ind \\ REPEAT STRIP_TAC \\ fs [free_def,LET_DEF]
  \\ TRY (fs [has_var_def,fv_def,fv1_thm] \\ NO_TAC)
  THEN1 (* cons *)
   (`?y1 l1. free [x] = ([y1],l1)` by METIS_TAC [PAIR,free_SING] \\ fs []
    \\ `?y2 l2. free (y::xs) = (y2,l2)` by METIS_TAC [PAIR] \\ fs []
    \\ IMP_RES_TAC evaluate_const \\ rfs [] \\ RES_TAC
    \\ IMP_RES_TAC free_LENGTH
    \\ Cases_on `y2` \\ fs [has_var_def,fv_def,fv1_thm])
  \\ `?y1 l1. free (MAP SND fns) = (y1,l1)` by METIS_TAC [PAIR,free_SING] \\ fs []
  \\ `?y1 l1. free [x1] = ([y1],l1)` by METIS_TAC [PAIR,free_SING] \\ fs []
  \\ `?y1 l1. free xs = (y1,l1)` by METIS_TAC [PAIR,free_SING] \\ fs []
  \\ `?y1 l1. free xs2 = (y1,l1)` by METIS_TAC [PAIR,free_SING] \\ fs []
  \\ `?y2 l2. free [x2] = ([y2],l2)` by METIS_TAC [PAIR,free_SING] \\ fs []
  \\ `?y3 l3. free [x3] = ([y3],l3)` by METIS_TAC [PAIR,free_SING] \\ fs []
  \\ rfs [] \\ RES_TAC \\ IMP_RES_TAC free_LENGTH \\ fs []
  \\ fs [has_var_def,fv_def,fv1_thm,MEM_vars_to_list]
  \\ fs [AC ADD_ASSOC ADD_COMM, MAP_ZIP]
  \\ fs [MAP_MAP_o,o_DEF]
  \\ CONV_TAC (DEPTH_CONV (PairRules.PBETA_CONV)) \\ fs []
  \\ STRIP_TAC \\ Cases_on `has_var (n + LENGTH fns) l1'` \\ fs []
  \\ fs [EXISTS_MAP]
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC IMP_EXISTS_IFF \\ fs [FORALL_PROD]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ Cases_on `free [p_2]` \\ fs []
  \\ IMP_RES_TAC free_SING \\ fs [])
|> curry save_thm "free_thm";

(* value relation *)

val subg_def = Define`
  subg g0 g1 ⇔
    subspt (FST g0) (FST g1) ∧
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
    set (MAP FST (SND g)) ⊆ IMAGE SUC (domain (FST g))`;

val wfg_def = Define`
  wfg g ⇔
    set (MAP FST (SND g)) = IMAGE SUC (domain (FST g)) ∧
    ALL_DISTINCT (MAP FST (SND g))`;

val recclosure_wf_def = Define`
  recclosure_wf loc fns ⇔
    every_Fn_SOME (MAP SND fns) ∧
    every_Fn_vs_NONE (MAP SND fns) ∧
    DISJOINT (set (GENLIST (λi. 2 * i + loc) (LENGTH fns))) (set (code_locs (MAP SND fns))) ∧
    ALL_DISTINCT (code_locs (MAP SND fns))`;

val recclosure_rel_def = Define`
  recclosure_rel g l loc fns1 fns2 ⇔ ∃g0.
     recclosure_wf loc fns1 ∧
     wfg g0 ∧
     DISJOINT (IMAGE SUC (set (code_locs (MAP SND fns1)))) (set (MAP FST (SND g0))) ∧
     DISJOINT (set (GENLIST (λi. 2*i+loc+1) (LENGTH fns1))) (set (MAP FST (SND g0))) ∧
     let (es,new_g) = calls (MAP SND fns1) (insert_each loc (LENGTH fns1) g0) in
     if EVERY2 (λ(n,_) p. ∀v. has_var v (SND (free [p])) ⇒ v < n) fns1 es
     then
       (∃tra n. fns2 = calls_list tra n loc fns1) ∧
       subg (code_list loc (ZIP (MAP FST fns1,es)) new_g) g ∧
       set (code_locs (MAP SND fns1)) DIFF domain (FST new_g) ⊆ l
     else
       let (es,new_g) = calls (MAP SND fns1) g0 in
       fns2 = ZIP (MAP FST fns1, es) ∧
       subg new_g g ∧
       set (code_locs (MAP SND fns1)) DIFF domain (FST new_g) ⊆ l ∧
       set (GENLIST (λi. 2*i+loc) (LENGTH fns1)) ⊆ l`;

val env_rel_def = Define`
  env_rel R env1 env2 a es ⇔
    if LENGTH env1 = LENGTH env2 then LIST_REL R env1 env2 else
    ∀x. EXISTS (λ(n,p). fv1 (n+a+x) p) es ⇒
        x < LENGTH env1 ∧ x < LENGTH env2 ∧
        R (EL x env1) (EL x env2)`;

val env_rel_mono = Q.store_thm("env_rel_mono[mono]",
  `(∀x y. MEM x env1 ∧ MEM y env2 ∧ R x y ⇒ R' x y) ⇒
   env_rel R env1 env2 a es ⇒
   env_rel R' env1 env2 a es`,
  rw[env_rel_def,MEM_EL,PULL_EXISTS,LIST_REL_EL_EQN]);

val env_rel_cong = Q.store_thm("env_rel_cong[defncong]",
  `(∀x y. MEM x env1 ∧ MEM y env2 ⇒ (R x y ⇔ R' x y))
   ⇒ env_rel R env1 env2 a es = env_rel R' env1 env2 a es`,
  rw[env_rel_def,MEM_EL,PULL_EXISTS,EQ_IMP_THM,LIST_REL_EL_EQN]);

val v_rel_def = tDefine"v_rel"`
  (v_rel g l (Number i) v ⇔ v = Number i) ∧
  (v_rel g l (Word64 w) v ⇔ v = Word64 w) ∧
  (v_rel g l (Block n vs) v ⇔
    ∃vs'. v = Block n vs' ∧ LIST_REL (v_rel g l) vs vs') ∧
  (v_rel g l (ByteVector ws) v ⇔ v = ByteVector ws) ∧
  (v_rel g l (RefPtr n) v ⇔ v = RefPtr n) ∧
  (v_rel g l (Closure loco vs1 env1 n bod1) v ⇔
     ∃loc vs2 env2 bod2.
       recclosure_rel g l loc [(n,bod1)] [(n,bod2)] ∧
       v = Closure (SOME loc) vs2 env2 n bod2 ∧ loco = SOME loc ∧
       LIST_REL (v_rel g l) vs1 vs2 ∧
       env_rel (v_rel g l) env1 env2 0 [(n,bod2)]) ∧
  (v_rel g l (Recclosure loco vs1 env1 fns1 i) v ⇔
     ∃loc vs2 env2 fns2.
       recclosure_rel g l loc fns1 fns2 ∧
       v = Recclosure (SOME loc) vs2 env2 fns2 i ∧ loco = SOME loc ∧
       LIST_REL (v_rel g l) vs1 vs2 ∧
       env_rel (v_rel g l) env1 env2 (LENGTH fns2) fns2)`
  (WF_REL_TAC `measure (v_size o FST o SND o SND)` >> simp[v_size_def] >>
   rpt strip_tac >> imp_res_tac v_size_lemma >> simp[]);

val v_rel_ind = theorem"v_rel_ind";

val code_includes_def = Define`
  code_includes al code ⇔
    ∀k v. ALOOKUP al k = SOME v ⇒ FLOOKUP code k = SOME v`;

val wfv_def = tDefine"wfv"`
  (wfv g l (Closure NONE _ _ _ _) ⇔ F) ∧
  (wfv g l (Recclosure NONE _ _ _ _) ⇔ F) ∧
  (wfv g l (Closure (SOME loc) vs env n bod) ⇔
    EVERY (wfv g l) vs ∧ EVERY (wfv g l) env ∧
    ∃fns2.
    recclosure_rel g l loc [(n,bod)] fns2) ∧
  (wfv g l (Recclosure (SOME loc) vs env fns i) ⇔
    EVERY (wfv g l) vs ∧ EVERY (wfv g l) env ∧
    ∃fns2.
    recclosure_rel g l loc fns fns2) ∧
  (wfv g l (Block _ vs) ⇔ EVERY (wfv g l) vs) ∧
  (wfv _ _ _ ⇔ T)`
  (WF_REL_TAC `measure (v_size o SND o SND)` >> simp[v_size_def] >>
   rpt strip_tac >> imp_res_tac v_size_lemma >> simp[]);
val _ = export_rewrites["wfv_def"];

val wfv_ind = theorem"wfv_ind";

val wfv_state_def = Define`
  wfv_state g l s ⇔
    EVERY (OPTION_EVERY (wfv g l)) s.globals ∧
    FEVERY (every_refv (wfv g l) o SND) s.refs ∧
    s.code = FEMPTY ∧ !k. SND (SND (s.compile_oracle k)) = []`;

val _ = temp_type_abbrev("calls_state",
          ``:num_set # (num, num # closLang$exp) alist``);

val state_rel_def = Define`
  state_rel g l (s:(calls_state # 'c,'ffi) closSem$state) (t:('c,'ffi) closSem$state) ⇔
    (s.ffi = t.ffi) ∧
    (s.clock = t.clock) ∧
    (s.max_app = t.max_app) ∧
    LIST_REL (OPTREL (v_rel g l)) s.globals t.globals ∧
    fmap_rel (ref_rel (v_rel g l)) s.refs t.refs ∧
    s.code = FEMPTY ∧ code_includes (SND g) t.code`;

val state_rel_max_app = Q.store_thm("state_rel_max_app",
  `state_rel g l s t ⇒ s.max_app = t.max_app`,
  rw[state_rel_def]);

val state_rel_clock = Q.store_thm("state_rel_clock",
  `state_rel g l s t ⇒ s.clock = t.clock`,
  rw[state_rel_def]);

val state_rel_with_clock = Q.store_thm("state_rel_with_clock",
  `state_rel g l s t ⇒ state_rel g l (s with clock := k) (t with clock := k)`,
  rw[state_rel_def]);

val state_rel_flookup_refs = Q.store_thm("state_rel_flookup_refs",
  `state_rel g l s t ∧ FLOOKUP s.refs k = SOME v ⇒
   ∃v'. FLOOKUP t.refs k = SOME v' ∧ ref_rel (v_rel g l) v v'`,
  rw[state_rel_def,fmap_rel_OPTREL_FLOOKUP]
  \\ first_x_assum(qspec_then`k`mp_tac) \\ rw[OPTREL_def]);

(* syntactic properties of compiler *)

val FST_code_list = Q.store_thm("FST_code_list[simp]",
  `∀loc fns g. FST (code_list loc fns g) = FST g`,
  ho_match_mp_tac code_list_ind
  \\ rw[code_list_def]);

val SND_insert_each = Q.store_thm("SND_insert_each[simp]",
  `∀p n g. SND (insert_each p n g) = SND g`,
  ho_match_mp_tac insert_each_ind
  \\ rw[insert_each_def]);

val calls_list_MAPi = Q.store_thm("calls_list_MAPi",
  `∀loc tra n. calls_list tra n loc = MAPi (λi p. (FST p, Call (tra§n+i§0) 0 (loc+2*i+1) (GENLIST_Var (tra§n+i) 1 (FST p))))`,
  simp[FUN_EQ_THM]
  \\ CONV_TAC(RESORT_FORALL_CONV(List.rev))
  \\ Induct \\ simp[calls_list_def]
  \\ Cases \\ simp[calls_list_def]
  \\ simp[o_DEF,ADD1,LEFT_ADD_DISTRIB]
  \\ rw[] \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ simp[FUN_EQ_THM]);

val calls_list_length = Q.store_thm("calls_list_length[simp]",
  `LENGTH (calls_list t n p fns) = LENGTH fns`,
  rw[calls_list_MAPi]);

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
    first_x_assum match_mp_tac
    \\ fs[MAP_FST_code_list,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND,
          ALL_DISTINCT_GENLIST,MEM_GENLIST,PULL_EXISTS]
    \\ imp_res_tac LIST_REL_LENGTH
    \\ imp_res_tac calls_IS_SUFFIX
    \\ imp_res_tac calls_add_SUC_code_locs
    \\ fs[IS_SUFFIX_APPEND,SUBSET_DEF]
    \\ fs[IN_DISJOINT,MEM_GENLIST]
    \\ rfs[GSYM ADD1]
    \\ metis_tac[numTheory.INV_SUC] )
  \\ first_x_assum match_mp_tac
  \\ fs[MAP_FST_code_list,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND,
        ALL_DISTINCT_GENLIST,MEM_GENLIST,PULL_EXISTS]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ imp_res_tac calls_IS_SUFFIX
  \\ imp_res_tac calls_add_SUC_code_locs
  \\ fs[IS_SUFFIX_APPEND,SUBSET_DEF]
  \\ fs[IN_DISJOINT,MEM_GENLIST]
  \\ fs[MAP_FST_code_list,MEM_GENLIST,PULL_EXISTS]
  \\ rfs[GSYM ADD1]
  \\ metis_tac[numTheory.INV_SUC,DECIDE``2 * i + SUC loc = SUC (2*i+loc)``]);

val compile_ALL_DISTINCT = Q.store_thm("compile_ALL_DISTINCT",
  `compile do_call x = (y,aux) ∧
   ALL_DISTINCT (code_locs x)
  ⇒
   ALL_DISTINCT (MAP FST aux)`,
  Cases_on`do_call` \\ rw[compile_def] \\ rw[]
  \\ pairarg_tac \\ fs[]
  \\ drule calls_ALL_DISTINCT
  \\ rw[]);

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
  \\ imp_res_tac calls_subspt
  \\ imp_res_tac calls_IS_SUFFIX
  \\ imp_res_tac calls_length
  \\ fs[IS_SUFFIX_APPEND] \\ fs[]
  \\ fs[MAP_FST_code_list,MEM_GENLIST,PULL_EXISTS,GSYM ADD1,domain_FST_insert_each]
  \\ metis_tac[numTheory.INV_SUC,prim_recTheory.PRE,EVAL``PRE 1``]);

val wfg'_insert_each = Q.store_thm("wfg'_insert_each",
  `∀n g loc. wfg' g ⇒ wfg' (insert_each loc n g)`,
  Induct \\ Cases \\ rw[insert_each_def]
  \\ first_x_assum match_mp_tac
  \\ fs[wfg'_def,SUBSET_DEF,IN_EVEN]
  \\ metis_tac[EVEN_ADD,EVAL``EVEN 2``]);

val wfg'_code_list = Q.store_thm("wfg'_code_list",
  `∀ls g loc.
      wfg' g ∧ set (GENLIST (λi. loc + 2 * i) (LENGTH ls)) ⊆ domain (FST g)
      ⇒ wfg' (code_list loc ls g)`,
  rw[wfg'_def,SUBSET_DEF,MEM_GENLIST,MAP_FST_code_list]
  >- (
    fs[ADD1,PULL_EXISTS]
    \\ metis_tac[ADD_ASSOC] )
  \\ metis_tac[]);

val closed_Fn = Q.store_thm("closed_Fn",
  `closed (Fn t loco vs args e) ⇔
   ∀v. has_var v (SND (free [e])) ⇒ v < args`,
  rw[closed_def]
  \\ qspec_then`[e]`mp_tac free_thm
  \\ simp[] \\ pairarg_tac \\ fs[]
  \\ rw[]
  \\ fs[free_def]
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

val closed_Fn_fv = Q.store_thm("closed_Fn_fv",
  `closed (Fn t loco vs args e) ⇔
   ∀v. fv v [e] ⇒ v < args`,
  rw[closed_Fn]
  \\ qspec_then`[e]`mp_tac free_thm
  \\ simp[] \\ pairarg_tac \\ fs[]);

val calls_wfg' = Q.store_thm("calls_wfg'",
  `∀xs g0 ys g.
    calls xs g0 = (ys,g) ∧
    every_Fn_SOME xs ∧ wfg' g0 ⇒
    wfg' g`,
  ho_match_mp_tac calls_ind
  \\ rw[calls_def] \\ rw[] \\ fs[code_locs_def]
  \\ rpt (pairarg_tac \\ fs[])
  \\ every_case_tac \\ fs[] \\ rw[]
  >- (
    drule wfg'_insert_each \\ fs[IN_EVEN]
    \\ disch_then(qspec_then`1`mp_tac) \\ simp[] \\ rw[]
    \\ fs[wfg'_def,ADD1,closed_Fn]
    \\ imp_res_tac calls_subspt
    \\ fs[subspt_def,domain_lookup]
    \\ first_x_assum match_mp_tac
    \\ REWRITE_TAC[ONE]
    \\ Cases_on`g0`
    \\ REWRITE_TAC[insert_each_def]
    \\ simp[lookup_insert] )
  \\ drule wfg'_insert_each \\ rw[]
  \\ first_x_assum match_mp_tac \\ fs[]
  \\ match_mp_tac wfg'_code_list
  \\ imp_res_tac calls_length
  \\ fs[SUBSET_DEF]
  \\ imp_res_tac calls_subspt
  \\ fs[subspt_def,domain_lookup]
  \\ rw[] \\ first_x_assum match_mp_tac
  \\ qmatch_abbrev_tac`lookup k d = SOME _`
  \\ `k ∈ domain d` suffices_by simp[domain_lookup]
  \\ simp[Abbr`d`,domain_FST_insert_each]);

val calls_wfg = Q.store_thm("calls_wfg",
  `∀xs g0 ys g.
    calls xs g0 = (ys,g) ∧
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

val calls_fv1_subset = Q.store_thm("calls_fv1_subset",
  `∀xs g0 ys g. calls xs g0 = (ys,g) ⇒
    LIST_REL (λx y. (combin$C fv1) y ⊆ (combin$C fv1) x) xs ys`,
  ho_match_mp_tac calls_ind
  \\ rw[calls_def]
  \\ rpt (pairarg_tac \\ fs[])
  \\ imp_res_tac calls_length
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2] \\ rw[]
  \\ every_case_tac \\ rw[]
  \\ fs[SUBSET_DEF,fv1_thm,IN_DEF,fv_GENLIST_Var_tra,fv_append]
  \\ rw[] \\ rw[]
  \\ TRY (
    fs[LIST_REL_EL_EQN,PULL_EXISTS]
    \\ fs[fv_exists,EXISTS_MEM,MEM_EL,PULL_EXISTS]
    \\ metis_tac[] )
  \\ fs[EXISTS_MEM]
  \\ rpt(pairarg_tac \\ fs[])
  \\ fs[calls_list_MAPi,indexedListsTheory.MEM_MAPi]
  \\ rveq \\ fs[fv1_thm,fv_GENLIST_Var_tra]
  \\ rfs[ZIP_MAP,MEM_MAP] \\ rveq
  \\ fs[LIST_REL_EL_EQN,PULL_EXISTS]
  \\ fs[fv_exists,EXISTS_MEM,MEM_EL,PULL_EXISTS]
  \\ rfs[EL_ZIP] \\ fs[EL_MAP]
  \\ simp[UNCURRY]
  \\ metis_tac[]);

val calls_fv_imp = Q.store_thm("calls_fv_imp",
  `calls xs g0 = (ys,g) ∧ fv v ys ⇒ fv v xs`,
  rw[] \\ imp_res_tac calls_fv1_subset
  \\ fs[LIST_REL_EL_EQN,fv_exists,EXISTS_MEM,MEM_EL,SUBSET_DEF,IN_DEF]
  \\ metis_tac[]);

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
    qmatch_goalsub_rename_tac`closLang$Letrec`
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
    qmatch_goalsub_rename_tac`closed (Fn _ _ _ _ _)`
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
  (insert_each' gt p 0 g = g) ∧
  (insert_each' gt p (SUC n) (g1,g2) =
   insert_each' gt (p+2) n (insert p () g1, ((p+1,THE(ALOOKUP gt (p+1)))::g2)))`;

val insert_each'_ind = theorem"insert_each'_ind";

val wfg_insert_each' = Q.store_thm("wfg_insert_each'",
  `∀gt p n g.
    wfg g ∧
    DISJOINT (set (GENLIST (λi. p+2*i) n)) (domain (FST g))
    ⇒ wfg (insert_each' gt p n g)`,
  ho_match_mp_tac insert_each'_ind
  \\ rw[insert_each'_def]
  \\ first_x_assum match_mp_tac
  \\ fs[wfg_def,GSYM ADD1]
  \\ fs[IN_DISJOINT,MEM_GENLIST,IN_EVEN,EVEN_ADD]
  \\ fs[METIS_PROVE[]``x ∨ y ⇔ ¬x ⇒ y``,PULL_EXISTS]
  \\ rw[]
  \\ first_assum (qspec_then`0`mp_tac)
  \\ first_x_assum (qspec_then`SUC i`mp_tac)
  \\ simp[ADD1,LEFT_ADD_DISTRIB]);

val FST_insert_each' = Q.store_thm("FST_insert_each'",
  `∀gt p n g. FST (insert_each' gt p n g) = FST (insert_each p n g)`,
  ho_match_mp_tac insert_each'_ind
  \\ rw[insert_each'_def,insert_each_def]
  \\ match_mp_tac FST_insert_each_same
  \\ rw[]);

val MAP_FST_insert_each' = Q.store_thm("MAP_FST_insert_each'",
  `∀gt p n g.
   MAP FST (SND (insert_each' gt p n g)) =
   REVERSE (GENLIST (λi. p + i * 2 + 1) n) ++
   MAP FST (SND g)`,
  ho_match_mp_tac insert_each'_ind
  \\ rw[insert_each'_def,GENLIST_CONS,o_DEF,ADD1,LEFT_ADD_DISTRIB]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ simp[FUN_EQ_THM]);

val SND_insert_each' = Q.store_thm("SND_insert_each'",
  `∀gt p n g. SND (insert_each' gt p n g) =
    REVERSE (GENLIST (λi. (2*i+p+1,THE(ALOOKUP gt (2*i+p+1)))) n) ++ SND g`,
  ho_match_mp_tac insert_each'_ind
  \\ rw[insert_each'_def]
  \\ rw[GENLIST_CONS,o_DEF,ADD1]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ simp[FUN_EQ_THM,LEFT_ADD_DISTRIB]);

val calls_el_sing = Q.store_thm("calls_el_sing",
  `∀xs g0 ys g i.
    calls xs g0 = (ys,g) ∧
    i < LENGTH xs ∧
    ALL_DISTINCT (MAP FST (SND g0)) ∧
    ALL_DISTINCT (code_locs xs) ∧
    DISJOINT (IMAGE SUC (set (code_locs xs))) (set (MAP FST (SND g0))) ∧
    wfg g0 ∧ every_Fn_SOME xs
    ⇒
     ∃ga gb.
       calls [EL i xs] ga = ([EL i ys],gb) ∧
       subg g0 ga ∧ subg ga gb ∧ subg gb g ∧ wfg ga ∧ wfg gb ∧
       DISJOINT (IMAGE SUC (set (code_locs [EL i xs]))) (set (MAP FST (SND ga))) ∧
       set (MAP FST (SND ga)) ⊆ set (MAP FST (SND g0)) ∪ IMAGE SUC (set (code_locs (TAKE i xs))) ∧
       (set (code_locs [EL i xs]) DIFF (domain (FST gb))) ⊆ (set (code_locs xs) DIFF (domain (FST g)))`,
  ho_match_mp_tac calls_ind \\ rw[]
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
    \\ fs[TAKE]
    \\ simp[Once code_locs_cons]
    \\ metis_tac[numTheory.INV_SUC] )
  \\ match_mp_tac subg_trans
  \\ first_assum(part_match_exists_tac(last o strip_conj) o concl) \\ rw[]
  \\ match_mp_tac calls_subg
  \\ asm_exists_tac \\ fs[]
  \\ fs[code_locs_def,ALL_DISTINCT_APPEND]);

(* properties of value relation *)

val v_rel_exists = Q.store_thm("v_rel_exists",
  `∀v1. wfv g l v1 ⇒ ∃v2. v_rel g l v1 v2`,
  ho_match_mp_tac v_ind
  \\ rw[v_rel_def]
  >- (
    simp[exists_list_GENLIST]
    \\ qmatch_assum_rename_tac`EVERY _ ls`
    \\ qexists_tac`LENGTH ls`
    \\ fs[EVERY_MEM,MEM_EL,LIST_REL_EL_EQN,PULL_EXISTS]
    \\ simp[GSYM SKOLEM_THM]
    \\ metis_tac[] )
  >- (
    qmatch_asmsub_rename_tac`Closure loco`
    \\ Cases_on`loco` \\ fs[]
    \\ `∃x. fns2 = [n,x]`
    by (
      fs[recclosure_rel_def]
      \\ rpt(pairarg_tac \\ fs[])
      \\ every_case_tac \\ fs[calls_list_MAPi]
      \\ imp_res_tac calls_length \\ fs[quantHeuristicsTheory.LIST_LENGTH_2] )
    \\ fs[] \\ asm_exists_tac
    \\ fs[EVERY_MEM,MEM_EL,LIST_REL_EL_EQN,PULL_EXISTS,env_rel_def]
    \\ simp[exists_list_GENLIST]
    \\ metis_tac[SKOLEM_THM] )
  >- (
    qmatch_asmsub_rename_tac`Recclosure loco`
    \\ Cases_on`loco` \\ fs[]
    \\ asm_exists_tac
    \\ fs[EVERY_MEM,MEM_EL,LIST_REL_EL_EQN,PULL_EXISTS,env_rel_def]
    \\ simp[exists_list_GENLIST]
    \\ metis_tac[SKOLEM_THM] ));

val v_rel_subg = Q.store_thm("v_rel_subg",
  `∀g l v1 v2 g' l'.
    v_rel g l v1 v2 ∧ subg g g' ∧ l ⊆ l' ⇒
    v_rel g' l' v1 v2`,
  ho_match_mp_tac v_rel_ind
  \\ rw[v_rel_def,env_rel_def,recclosure_rel_def]
  \\ Cases_on`LENGTH env1 = LENGTH env2`
  \\ fsrw_tac[ETA_ss][PULL_FORALL,PULL_EXISTS]
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
    \\ qpat_x_assum`LIST_REL (v_rel g l) l1 l2` kall_tac
    \\ map_every qunabbrev_tac[`l2`,`l1`])
  \\ fs[]
  \\ qexists_tac`g0`
  \\ rpt(pairarg_tac \\ fs[])
  \\ imp_res_tac calls_length
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
  \\ rveq \\ fs[]
  \\ CASE_TAC \\ fs[] \\ rfs[]
  \\ fs[EXISTS_MEM,EXISTS_PROD]
  \\ metis_tac[subg_trans,SUBSET_DEF,MEM_EL]);

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
  `dest_closure max_app (SOME loc) v1 env1 = SOME x ∧
   v_rel g l v1 v2 ∧
   LIST_REL (v_rel g l) env1 env2 ∧
   wfg g ∧ loc ∈ domain (FST g) ∧ loc ∉ l  ⇒
   ∃e l1 xs n ls g01 g1 l1' tra i.
     x = Full_app e (env1++l1) [] ∧ EL n xs = (LENGTH env1,e) ∧
     calls (MAP SND xs) g01 = (ls,g1) ∧ n < LENGTH ls ∧
     subg (code_list (loc - 2*n) (ZIP (MAP FST xs,ls)) g1) g ∧
     ALOOKUP (SND g) (loc+1) = SOME (LENGTH env1,EL n ls) ∧
     dest_closure max_app (SOME loc) v2 env2 =
       SOME (Full_app (Call (tra§i§0) 0 (loc+1) (GENLIST_Var (tra§i) 1 (LENGTH env1))) (env2++l1') [])`,
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
    \\ fsrw_tac[ETA_ss][]
    \\ metis_tac[])
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
  \\ rveq \\ fs[]
  \\ rename1`tra § n + n1`
  \\ qexists_tac`tra` \\ qexists_tac`n+n1`
    \\ fs[subg_def]
    \\ first_x_assum match_mp_tac
    \\ simp[ALOOKUP_code_list]
    \\ DEEP_INTRO_TAC some_intro
    \\ simp[EL_ZIP,EL_MAP]
    (*
    )
    *)
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
  \\ simp[revtakerev,revdroprev,TAKE_APPEND]
  \\ TRY (match_mp_tac EVERY2_APPEND_suff)
  \\ fsrw_tac[ETA_ss][]
  \\ simp[LIST_REL_GENLIST]
  \\ simp[v_rel_def,recclosure_rel_def]
  \\ fsrw_tac[ETA_ss][]
  \\ simp[calls_list_MAPi]
  \\ rw[]
  \\ qexists_tac`g0`
  \\ simp[]);

val dest_closure_v_rel = Q.store_thm("dest_closure_v_rel",
  `dest_closure max_app loco v1 env1 = SOME x1 ∧
   v_rel g l v1 v2 ∧
   LIST_REL (v_rel g l) env1 env2
   ⇒
   ∃x2.
   dest_closure max_app loco v2 env2 = SOME x2 ∧
   (case x1 of Partial_app c1 =>
     ∃c2. x2 = Partial_app c2 ∧ v_rel g l c1 c2
    | Full_app e1 args1 rest1 =>
      ∃fns1 loc i fns2 args2 rest2 n.
        x2 = Full_app (SND (EL i fns2)) args2 rest2 ∧
        (let m = if is_Recclosure v2 then LENGTH fns2 else 0 in
         n+m ≤ LENGTH args1 ∧ n+m ≤ LENGTH args2 ∧
         LIST_REL (v_rel g l) (TAKE (n+m) args1) (TAKE (n+m) args2) ∧
         env_rel (v_rel g l) (DROP (n+m) args1) (DROP (n+m) args2) m [EL i fns2]) ∧
        LIST_REL (v_rel g l) rest1 rest2 ∧
        recclosure_rel g l loc fns1 fns2 ∧
        i < LENGTH fns1 ∧
        EL i fns1 = (n,e1))`,
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
    \\ rveq \\ fs[PULL_EXISTS]
    \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["g0'"]))
    \\ map_every qexists_tac [`g0`,`([n,e])`,`loc`]
    \\ simp[calls_list_def]
    \\ qmatch_goalsub_abbrev_tac`COND b`
    \\ imp_res_tac LIST_REL_LENGTH
    \\ simp[TAKE_APPEND,TAKE_LENGTH_ID_rwt]
    \\ simp[DROP_DROP_T,DROP_APPEND,DROP_LENGTH_TOO_LONG]
    \\ Cases_on`b` \\ fs[calls_list_def]
    \\ fsrw_tac[ETA_ss][env_rel_def,fv1_thm,fv_GENLIST_Var_tra,PULL_EXISTS]
    \\ TRY (
        rename1`tra § i § 0`
        \\ qexists_tac`tra` \\ qexists_tac`i` \\ simp[] )
    \\ rpt conj_tac
    \\ rpt (
         (match_mp_tac EVERY2_APPEND_suff ORELSE
          match_mp_tac EVERY2_TAKE ORELSE
          match_mp_tac EVERY2_DROP) \\ fs[])
    \\ rw[] \\ fs[LIST_REL_EL_EQN])
  >- (
    simp[v_rel_def]
    \\ match_mp_tac EVERY2_APPEND_suff
    \\ fsrw_tac[ETA_ss][])
  \\ fsrw_tac[ETA_ss][]
  \\ `LENGTH fns2 = LENGTH l1 ∧ num_args = num_args'`
  by (
    fs[recclosure_rel_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ every_case_tac \\ fs[calls_list_MAPi]
    \\ imp_res_tac calls_length \\ fs[]
    \\ rw[] \\ rfs[indexedListsTheory.EL_MAPi] \\ fs[]
    \\ qpat_x_assum`¬(LENGTH _ ≤ _)`assume_tac
    \\ fs[EL_ZIP,EL_MAP])
  \\ fs[]
  \\ reverse IF_CASES_TAC \\ fs[] \\ rveq \\ fs[]
  >- (
    fs[v_rel_def]
    \\ fsrw_tac[ETA_ss][]
    \\ match_mp_tac EVERY2_APPEND_suff \\ fs[] )
  \\ fs[revdroprev,revtakerev]
  \\ first_assum(part_match_exists_tac (el 3 o rev o strip_conj) o concl)
  \\ qexists_tac`n` \\ fs[]
  \\ simp[TAKE_APPEND,TAKE_LENGTH_ID_rwt,DROP_DROP_T,DROP_APPEND,DROP_LENGTH_TOO_LONG,SUB_PLUS]
  \\ rpt conj_tac
  \\ rpt (
       (match_mp_tac EVERY2_APPEND_suff ORELSE
        match_mp_tac EVERY2_TAKE ORELSE
        match_mp_tac EVERY2_DROP)
       \\ fs[] \\ rpt conj_tac)
  \\ TRY (
    fsrw_tac[ETA_ss][LIST_REL_GENLIST,v_rel_def]
    \\ rw[] \\ asm_exists_tac \\ rw[])
  \\ fs[env_rel_def]
  \\ IF_CASES_TAC \\ fs[]
  \\ fs[EXISTS_MEM,PULL_EXISTS,MEM_EL]
  \\ qx_gen_tac`x`
  \\ first_x_assum(qspecl_then[`x`,`n`]mp_tac)
  \\ simp[]);

val dest_closure_partial_wfv = Q.store_thm("dest_closure_partial_wfv",
  `dest_closure max_app loco v env = SOME (Partial_app x) ∧
   EVERY (wfv g l) env ∧ wfv g l v ⇒ wfv g l x`,
  rw[dest_closure_def]
  \\ every_case_tac \\ fs[]
  \\ rw[]
  \\ rpt(pairarg_tac \\ fs[])
  \\ every_case_tac \\ fs[]
  \\ (qmatch_asmsub_rename_tac`Closure lopt` ORELSE
      qmatch_asmsub_rename_tac`Recclosure lopt`)
  \\ Cases_on`lopt` \\ fs[] \\ rveq
  \\ fsrw_tac[ETA_ss][]
  \\ metis_tac[]);

val dest_closure_full_wfv = Q.store_thm("dest_closure_full_wfv",
  `dest_closure max_app loco v env = SOME (Full_app e args rest) ∧
   wfv g l v ∧ EVERY (wfv g l) env
   ⇒
   ∃ys g01 loc fns1 fns2 i.
     EVERY (wfv g l) args ∧ EVERY (wfv g l) rest ∧
     recclosure_rel g l loc fns1 fns2 ∧
     SND (EL i fns1) = e ∧ i < LENGTH fns1`,
  rw[dest_closure_def]
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ rpt(pairarg_tac \\ fs[])
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ (qmatch_asmsub_rename_tac`Closure lopt` ORELSE
      qmatch_asmsub_rename_tac`Recclosure lopt`)
  \\ Cases_on`lopt` \\ fs[] \\ rveq
  \\ fsrw_tac[ETA_ss][EVERY_REVERSE,EVERY_GENLIST]
  \\ simp[RIGHT_EXISTS_AND_THM]
  \\ rpt conj_tac
  \\ TRY ( match_mp_tac (MP_CANON EVERY_TAKE) \\ fs[EVERY_REVERSE] )
  \\ TRY ( match_mp_tac (MP_CANON EVERY_DROP) \\ fs[EVERY_REVERSE] )
  \\ simp[PULL_EXISTS]
  \\ TRY ( rw[] \\ asm_exists_tac \\ fs[])
  \\ fs[NOT_LESS_EQUAL]
  \\ metis_tac[PAIR,SND,EL,HD]);

val env_rel_DROP = Q.store_thm("env_rel_DROP",
  `env_rel R (DROP x l1) (DROP x l2) x es ∧
   LIST_REL R (TAKE x l1) (TAKE x l2) ∧
   x ≤ LENGTH l1 ∧ x ≤ LENGTH l2
   ⇒
   env_rel R l1 l2 0 es`,
  strip_tac \\ fs[env_rel_def]
  \\ IF_CASES_TAC \\ fs[]
  >- ( metis_tac[EVERY2_APPEND_suff,TAKE_DROP] )
  \\ fs[LIST_REL_EL_EQN,EL_TAKE,EXISTS_MEM,PULL_EXISTS]
  \\ qx_gen_tac`i`
  \\ Cases_on`i<x`\\fs[NOT_LESS]
  \\ pop_assum mp_tac \\ simp[LESS_EQ_EXISTS]
  \\ strip_tac \\ gen_tac \\ strip_tac
  \\ first_x_assum drule \\ rveq
  \\ pairarg_tac \\ fs[]
  \\ disch_then(qspec_then`p`mp_tac)
  \\ simp[] \\ strip_tac
  \\ rfs[EL_DROP]);

val env_rel_DROP_args = Q.store_thm("env_rel_DROP_args",
  `env_rel R (DROP n l1) (DROP n l2) a [(n,e)] ∧
   LIST_REL R (TAKE n l1) (TAKE n l2) ∧
   n ≤ LENGTH l1 ∧ n ≤ LENGTH l2 ⇒
   env_rel R l1 l2 a [(0,e)]`,
  simp[env_rel_def]
  \\ IF_CASES_TAC \\ fs[]
  >- metis_tac[TAKE_DROP,EVERY2_APPEND_suff]
  \\ strip_tac
  \\ qx_gen_tac`x`
  \\ Cases_on`x < n`
  >- ( fs[LIST_REL_EL_EQN,EL_TAKE] )
  \\ fs[NOT_LESS,LESS_EQ_EXISTS]
  \\ strip_tac
  \\ first_x_assum drule
  \\ simp[] \\ strip_tac
  \\ rfs[EL_DROP]);

val subg_insert_each' = Q.store_thm("subg_insert_each'",
  `!gb fns1 es g1.
      subg gb (FST new_g,l ++ SND (insert_each' g1 loc (LENGTH fns1) g)) /\
      SND new_g = l ++ SND g /\ LENGTH fns1 = LENGTH es
      ∧ wfg g ∧
      DISJOINT (set (GENLIST (λi. 2*i+loc+1) (LENGTH fns1))) (IMAGE SUC (domain (FST g))) ∧
      DISJOINT (set (MAP FST l)) (IMAGE SUC (domain (FST g))) ∧
      (∀i. i < LENGTH fns1 ⇒ ALOOKUP g1 (2*i+loc+1) = SOME (FST (EL i fns1), EL i es))
      ==>
      subg (FST new_g,l ++ SND (insert_each' g1 loc (LENGTH fns1) g))
        (code_list loc (ZIP (MAP FST fns1,es)) new_g)`,
  Cases_on `new_g` \\ fs [] \\ PairCases_on `g` \\ fs []
  \\ rw [] \\ rveq \\ fs [subg_def]
  \\ fs[ALL_DISTINCT_APPEND,MAP_FST_code_list,MEM_GENLIST,PULL_EXISTS,
        wfg_def,ALL_DISTINCT_GENLIST,IN_DISJOINT]
  \\ reverse conj_tac
  >- (
    fs[MAP_FST_insert_each',MEM_GENLIST]
    \\ metis_tac[numTheory.INV_SUC,ADD1,ADD_ASSOC] )
  \\ simp[SND_code_list_ZIP]
  \\ rw[ALOOKUP_APPEND]
  \\ pop_assum mp_tac
  \\ BasicProvers.CASE_TAC
  >- (
    rw[]
    \\ BasicProvers.CASE_TAC
    >- (
      imp_res_tac ALOOKUP_MEM
      \\ rfs[REVERSE_ZIP]
      \\ rfs[ALOOKUP_ZIP_FAIL]
      \\ fs[SND_insert_each']
      >- (
        fs[MEM_GENLIST]
        \\ metis_tac[ADD_ASSOC,ADD_COMM] )
      \\ fs[ALOOKUP_APPEND]
      \\ every_case_tac \\ fs[]
      \\ imp_res_tac ALOOKUP_MEM
      \\ fs[MEM_GENLIST]
      \\ metis_tac[ADD_ASSOC,ADD_COMM] )
    \\ fs[SND_insert_each',o_DEF,ALOOKUP_APPEND]
    \\ every_case_tac \\ fs[]
    >- (
      imp_res_tac ALOOKUP_MEM
      \\ imp_res_tac ALOOKUP_FAILS
      \\ rfs[MEM_ZIP,MEM_GENLIST] \\ fs[]
      \\ rveq
      \\ metis_tac[ADD_ASSOC,ADD_COMM] )
    \\ rveq
    \\ rfs[REVERSE_ZIP]
    \\ `SOME x = SOME v` suffices_by rw[]
    \\ pop_assum (SUBST_ALL_TAC o SYM)
    \\ match_mp_tac EQ_SYM
    \\ match_mp_tac ALOOKUP_ALL_DISTINCT_MEM
    \\ imp_res_tac ALOOKUP_MEM
    \\ simp[MAP_REVERSE,MAP_GENLIST,ALL_DISTINCT_GENLIST,MEM_GENLIST]
    \\ rfs[MEM_ZIP]
    \\ simp[EL_ZIP,EL_REVERSE]
    \\ qexists_tac`PRE (LENGTH es - n)`
    \\ simp[EL_MAP])
  \\ rw[]
  \\ BasicProvers.CASE_TAC
  \\ fs[MAP_FST_insert_each']
  \\ imp_res_tac ALOOKUP_MEM
  \\ rfs[MEM_ZIP,MEM_GENLIST,PULL_EXISTS,EL_ZIP]
  \\ rveq
  \\ rfs[EL_GENLIST,MEM_MAP,PULL_EXISTS]
  \\ res_tac \\ fs[ADD1]
  \\ metis_tac[ADD_ASSOC,ADD_COMM]);

val wfv_subg = Q.store_thm("wfv_subg",
  `∀g l v g' l'. wfv g l v ∧ subg g g' ∧ l ⊆ l' ⇒ wfv g' l' v`,
  ho_match_mp_tac wfv_ind \\ rw[]
  \\ fsrw_tac[ETA_ss][]
  \\ fs[EVERY_MEM]
  \\ fs[recclosure_rel_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["g0'"]))
  \\ qexists_tac`g0`\\fs[]
  \\ CASE_TAC \\ fs[SUBSET_DEF]
  \\ rveq \\ fs[]
  \\ metis_tac[subg_trans]);

(* semantic functions respect relation *)

val v_rel_Unit = Q.store_thm("v_rel_Unit[simp]",
  `v_rel g1 l1 Unit Unit`,
  EVAL_TAC \\ fs []);

val v_to_list_thm = Q.store_thm("v_to_list_thm",
  `!h h' x.
      v_to_list h = SOME x /\ v_rel g1 l1 h h' ==>
      ?x'. v_to_list h' = SOME x' /\ LIST_REL (v_rel g1 l1) x x'`,
  recInduct v_to_list_ind \\ rw [] \\ fs [v_to_list_def] \\ rw []
  \\ fs [v_rel_def,v_to_list_def] \\ rw []
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ res_tac \\ fs [] \\ rw []);

val v_rel_IMP_v_to_bytes_lemma = prove(
  ``!x y c g.
      v_rel c g x y ==>
      !ns. (v_to_list x = SOME (MAP (Number o $& o (w2n:word8->num)) ns)) <=>
           (v_to_list y = SOME (MAP (Number o $& o (w2n:word8->num)) ns))``,
  ho_match_mp_tac v_to_list_ind \\ rw []
  \\ fs [v_to_list_def,v_rel_def]
  \\ Cases_on `tag = cons_tag` \\ fs []
  \\ res_tac \\ fs [case_eq_thms]
  \\ Cases_on `ns` \\ fs []
  \\ eq_tac \\ rw [] \\ fs []
  \\ Cases_on `h'` \\ fs [v_rel_def]
  \\ Cases_on `h` \\ fs [v_rel_def]);

val v_rel_IMP_v_to_words_lemma = prove(
  ``!x y c g.
      v_rel c g x y ==>
      !ns. (v_to_list x = SOME (MAP Word64 ns)) <=>
           (v_to_list y = SOME (MAP Word64 ns))``,
  ho_match_mp_tac v_to_list_ind \\ rw []
  \\ fs [v_to_list_def,v_rel_def]
  \\ Cases_on `tag = cons_tag` \\ fs []
  \\ res_tac \\ fs [case_eq_thms]
  \\ Cases_on `ns` \\ fs []
  \\ eq_tac \\ rw [] \\ fs []
  \\ Cases_on `h'` \\ fs [v_rel_def]
  \\ Cases_on `h` \\ fs [v_rel_def]);

val v_to_bytes_thm = Q.store_thm("v_to_bytes_thm",
  `!h h' x.
      v_to_bytes h = SOME x /\ v_rel g1 l1 h h' ==>
      v_to_bytes h' = SOME x`,
  rw [v_to_bytes_def] \\ drule v_rel_IMP_v_to_bytes_lemma \\ fs []
  \\ rw [] \\ fs []);

val v_to_words_thm = Q.store_thm("v_to_words_thm",
  `!h h' x.
      v_to_words h = SOME x /\ v_rel g1 l1 h h' ==>
      v_to_words h' = SOME x`,
  rw [v_to_words_def] \\ drule v_rel_IMP_v_to_words_lemma \\ fs []
  \\ rw [] \\ fs []);

val v_to_list_wfv = Q.store_thm("v_to_list_wfv",
  `!h x. v_to_list h = SOME x /\ wfv g1 l1 h ==> EVERY (wfv g1 l1) x`,
  recInduct v_to_list_ind \\ rw [] \\ fs [v_to_list_def] \\ rw []
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ res_tac \\ fs [] \\ rw []);

val wfv_Boolv = Q.store_thm("wfv_Boolv",
  `wfv g1 l1 (Boolv b) /\ wfv g1 l1 Unit`,
  Cases_on `b` \\ EVAL_TAC);

val vrel_list_to_v = Q.store_thm("vrel_list_to_v",
  `!xs1 xs2 ys1 ys2.
     LIST_REL (v_rel g l) xs1 xs2 /\
     LIST_REL (v_rel g l) ys1 ys2 /\
     v_rel g l (list_to_v xs1) (list_to_v xs2) /\
     v_rel g l (list_to_v ys1) (list_to_v ys2) ==>
       v_rel g l (list_to_v (xs1 ++ ys1)) (list_to_v (xs2 ++ ys2))`,
  Induct >- rw [list_to_v_def] \\ gen_tac
  \\ Induct \\ rw [list_to_v_def] \\ fs [v_rel_def]);

val vrel_v2l_l2v = Q.store_thm("vrel_v2l_l2v",
  `!x y xs ys.
     v_rel g l x y /\
     v_to_list x = SOME xs /\
     v_to_list y = SOME ys ==>
       v_rel g l (list_to_v xs) (list_to_v ys)`,
  ho_match_mp_tac v_to_list_ind \\ rw [v_to_list_def, v_rel_def]
  \\ fs [list_to_v_def] \\ rveq
  \\ fs [v_to_list_def] \\ rveq
  \\ fs [list_to_v_def, case_eq_thms, v_rel_def] \\ rveq
  \\ fs [list_to_v_def, v_rel_def]
  \\ res_tac);

val wfv_v2l_l2v = Q.store_thm("wfv_v2l_l2v",
  `!x y xs ys.  wfv g l x /\ v_to_list x = SOME xs ==> wfv g l (list_to_v xs)`,
  ho_match_mp_tac v_to_list_ind \\ rw [v_to_list_def, wfv_def]
  \\ fs [list_to_v_def, case_eq_thms]
  \\ rw [list_to_v_def]);

val wfv_v2l = Q.store_thm("wfv_v2l",
  `!x y xs ys.
   wfv g l x /\ wfv g l y /\
   v_to_list x = SOME xs /\ v_to_list y = SOME ys ==>
     ?z. wfv g l z /\ v_to_list z = SOME (xs ++ ys)`,
  ho_match_mp_tac v_to_list_ind \\ rw [v_to_list_def] \\ fs []
  >- metis_tac []
  \\ fs [case_eq_thms] \\ rw []
  \\ first_x_assum drule
  \\ disch_then drule \\ fs [] \\ rw []
  \\ Cases_on `z` \\ fs [v_to_list_def]
  \\ qexists_tac `Block cons_tag [h; Block n l']`
  \\ fs [wfv_def, v_to_list_def]);

val do_app_thm = Q.store_thm("do_app_thm",
  `case do_app op (REVERSE a) (r:(calls_state # 'c,'ffi) closSem$state) of
      Rerr (Rraise _) => F
    | Rerr (Rabort e) =>
      (e = Rtype_error \/
       (?f. e = Rffi_error f
            /\ (LIST_REL (v_rel g1 l1) a v /\ state_rel g1 l1 r t
            ==> do_app op (REVERSE v) t = Rerr(Rabort (Rffi_error f)))))
    | Rval (w,s) =>
       (wfv_state g1 l1 r /\ EVERY (wfv g1 l1) a ==>
        wfv_state g1 l1 s /\ wfv g1 l1 w) /\
       (LIST_REL (v_rel g1 l1) a v /\ state_rel g1 l1 r t ==>
        ?w' s'. (do_app op (REVERSE v) t = Rval (w',s')) /\
                v_rel g1 l1 w w' /\ state_rel g1 l1 s s')`,
  reverse CASE_TAC THEN1
   (pop_assum mp_tac
    \\ Cases_on `op` \\ Cases_on `REVERSE a`
    \\ simp[do_app_def, case_eq_thms, bool_case_eq, pair_case_eq, CaseEq"ffi$ffi_result"]
    \\ strip_tac \\ rveq \\ fs []
    \\ Cases_on`a` \\ fs[] \\ rveq \\ fs[]
    \\ strip_tac \\ fs[v_rel_def, PULL_EXISTS] \\ rveq
    \\ imp_res_tac state_rel_flookup_refs \\ fs[]
    \\ fs[state_rel_def])
  \\ rename1 `_ = _ b`
  \\ PairCases_on `b` \\ fs []
  \\ reverse strip_tac
  THEN1
   (assume_tac (GEN_ALL simple_val_rel_do_app
                |> INST_TYPE [alpha|->``:calls_state # 'c``])
    \\ pop_assum (qspecl_then [`REVERSE v`,`REVERSE a`,
                `v_rel g1 l1`,
                `t`,`state_rel g1 l1`,
                `r`,`op`] mp_tac)
    \\ fs [GSYM AND_IMP_INTRO]
    \\ impl_tac THEN1
     (fs [simple_val_rel_def] \\ rpt strip_tac
      \\ Cases_on `x` \\ fs [v_rel_def]
      \\ eq_tac \\ fs []
      \\ rpt (pop_assum kall_tac)
      \\ qspec_tac (`l`,`l`)
      \\ Induct_on `p` \\ fs [PULL_EXISTS])
    \\ reverse impl_tac THEN1 (rw [] \\ fs [])
    \\ fs [simple_state_rel_def] \\ rpt strip_tac
    \\ fs [state_rel_def]
    \\ fs [fmap_rel_def,FLOOKUP_DEF]
    THEN1
     (res_tac \\ fs []
      \\ qpat_x_assum `!x. _` kall_tac
      \\ rfs [] \\ Cases_on `s.refs ' ptr` \\ fs [ref_rel_def])
    THEN1
     (res_tac \\ fs []
      \\ qpat_x_assum `!x. _` kall_tac
      \\ rfs [] \\ Cases_on `s.refs ' ptr` \\ fs [ref_rel_def])
    THEN1 (strip_tac \\ Cases_on `x = p` \\ fs [FAPPLY_FUPDATE_THM])
    THEN1 (strip_tac \\ Cases_on `x = p` \\ fs [FAPPLY_FUPDATE_THM]))
  \\ assume_tac (GEN_ALL simple_val_rel_do_app
                 |> INST_TYPE [alpha|->``:calls_state # 'c``,
                               ``:'c``|->``:calls_state # 'c``])
  \\ pop_assum (qspecl_then [`REVERSE a`,`REVERSE a`,
                `\v1 v2. wfv g1 l1 v1 /\ v1 = v2`,
                `r`,`\s1 s2. wfv_state g1 l1 s1 /\ s1 = s2`,
                `r`,`op`] mp_tac)
  \\ fs [GSYM AND_IMP_INTRO]
  \\ impl_tac THEN1
   (fs [simple_val_rel_def] \\ rpt strip_tac
    \\ eq_tac \\ fs []
    \\ rw [] \\ fs []
    THEN1 (Induct_on `p` \\ fs [] \\ Cases_on `xs` \\ fs [])
    \\ pop_assum mp_tac \\ qspec_tac (`p`,`p`)
    \\ Induct_on `xs` \\ fs [PULL_EXISTS]
    \\ metis_tac [])
  \\ impl_tac THEN1
   (fs [simple_state_rel_def] \\ rpt strip_tac
    \\ fs [wfv_state_def]
    \\ imp_res_tac FEVERY_FLOOKUP \\ fs []
    THEN1
     (pop_assum mp_tac
      \\ qspec_tac (`w`,`w`) \\ Induct \\ fs [])
    THEN1
     (qpat_x_assum `EVERY _ s2.globals` mp_tac
      \\ qspec_tac (`s2.globals`,`w`) \\ Induct \\ fs []
      \\ Cases \\ fs [OPTREL_def])
    THEN1
      (match_mp_tac (FEVERY_STRENGTHEN_THM |> CONJUNCT2) \\ fs [])
    THEN1
      (match_mp_tac (FEVERY_STRENGTHEN_THM |> CONJUNCT2) \\ fs []
       \\ qpat_x_assum `_ xs ys` mp_tac
       \\ qspec_tac (`xs`,`xs`) \\ qspec_tac (`ys`,`ys`)
       \\ Induct \\ fs [] \\ Cases_on `ys` \\ fs [PULL_EXISTS])
    THEN1
      (qsuff_tac `xs = ys` \\ fs []
       \\ qpat_x_assum `_ xs ys` mp_tac
       \\ qspec_tac (`xs`,`xs`) \\ qspec_tac (`ys`,`ys`)
       \\ Induct \\ fs [] \\ Cases_on `xs` \\ simp_tac std_ss [PULL_EXISTS]
       \\ fs [])
    THEN1
      (qpat_x_assum `_ xs ys` mp_tac
       \\ qspec_tac (`ys`,`ys`) \\ qspec_tac (`xs`,`xs`)
       \\ Induct \\ fs [PULL_EXISTS] \\ Cases \\ fs [OPTREL_def]
       \\ metis_tac [])
    THEN1
      (qsuff_tac `xs = ys` \\ fs []
       \\ qpat_x_assum `_ xs ys` mp_tac
       \\ qspec_tac (`xs`,`xs`) \\ qspec_tac (`ys`,`ys`)
       \\ Induct \\ fs [PULL_EXISTS] \\ Cases  \\ Cases \\ fs [OPTREL_def]))
  \\ rw [] \\ fs []
  \\ `LIST_REL (λv1 v2. wfv g1 l1 v1 ∧ v1 = v2) a a` by
       (pop_assum mp_tac \\ rpt (pop_assum kall_tac)
        \\ Induct_on `a` \\ fs [])
  \\ fs []);

val NOT_IN_domain_FST_g = Q.store_thm("NOT_IN_domain_FST_g",
  `ALL_DISTINCT (code_locs xs ++ code_locs ys) ⇒
    calls ys g' = (e2,g) ⇒
    wfg g' ⇒
    MEM x (code_locs xs) ⇒
    x ∉ domain (FST g') ⇒
    x ∉ domain (FST g)`,
  rw [] \\ imp_res_tac calls_domain
  \\ fs [SUBSET_DEF,DISJOINT_DEF,EXTENSION] \\ rw []
  \\ CCONTR_TAC \\ fs [] \\ res_tac \\ rveq \\ fs []
  \\ drule calls_add_SUC_code_locs \\ fs [SUBSET_DEF]
  \\ asm_exists_tac \\ fs [] \\ CCONTR_TAC \\ fs []
  \\ rfs [wfg_def,SUBSET_DEF,EXTENSION] \\ rveq \\ fs []
  \\ fs [ALL_DISTINCT_APPEND] \\ res_tac);

val v_rel_Boolv = Q.store_thm("v_rel_Boolv[simp]",
  `v_rel g1 l1 (Boolv b) v <=> (v = Boolv b)`,
  Cases_on `b` \\ Cases_on `v` \\ fs [v_rel_def,Boolv_def]);

val code_includes_SUBMAP = prove(
  ``code_includes x y1 /\ y1 SUBMAP y2 ==> code_includes x y2``,
  fs [code_includes_def,SUBMAP_DEF,FLOOKUP_DEF] \\ metis_tac []);

val env_rel_Op_Install = prove(
  ``env_rel r env env2 0 [(0,Op v6 Install e1)] <=>
    env_rel r env env2 0 (MAP (λx. (0,x)) e1)``,
  fs [env_rel_def] \\ rw [] \\ fs [fv1_thm,EXISTS_MAP]
  \\ qsuff_tac `!x. EXISTS (λx'. fv1 x x') e1 = fv x e1` \\ fs []
  \\ Induct_on `e1` \\ fs []);

val compile_inc_def = Define `
  compile_inc g (e,xs) =
    let (ea, g') = calls [e] g in (g', HD ea, [])`;

val syntax_ok_def = Define`
  syntax_ok x ⇔ every_Fn_SOME x ∧ every_Fn_vs_NONE x ∧ ALL_DISTINCT (code_locs x)`;

val code_inv_def = Define `
  code_inv (s_code:num |-> num # closLang$exp) s_cc s_co t_code t_cc t_co <=>
    s_code = FEMPTY /\
    s_cc = state_cc compile_inc t_cc /\
    t_co = state_co compile_inc s_co /\
    (∀k. SND (SND (s_co k)) = [])
    (* needs more .. *)`

val code_rel_state_rel_install = store_thm("code_rel_state_rel_install",
  ``code_inv r.code r.compile r.compile_oracle t.code t.compile
           t.compile_oracle /\
    state_rel g1 l1 r t /\
    r.compile cfg (exp',aux) =
      SOME (bytes,data,FST (shift_seq 1 r.compile_oracle 0)) /\
    t.compile_oracle 0 = (cfg',progs) ==>
    DISJOINT (FDOM t.code) (set (MAP FST (SND progs))) ∧
    ALL_DISTINCT (MAP FST (SND progs)) /\
    t.compile cfg' progs = SOME (bytes,data,FST (shift_seq 1 t.compile_oracle 0)) /\
    ?exp1 aux1 g5. progs = (exp1,aux1) /\
    calls [exp'] g1 = ([exp1],g5) /\
    state_rel g1 l1
     (r with
      <|compile_oracle := shift_seq 1 r.compile_oracle;
        code := r.code |++ aux|>)
     (t with
      <|compile_oracle := shift_seq 1 t.compile_oracle;
        code := t.code |++ aux1|>) ∧
    code_inv (r.code |++ aux) r.compile (shift_seq 1 r.compile_oracle)
      (t.code |++ aux1) t.compile (shift_seq 1 t.compile_oracle)``,
  cheat) |> GEN_ALL;

(* compiler correctness *)

val t0 = ``t0:('c,'ffi) closSem$state``;

val calls_correct = Q.store_thm("calls_correct",
  `(∀tmp xs env1 s0 g0 g env2 ^t0 ys res s l l1 g1.
    tmp = (xs,env1,s0) ∧
    evaluate (xs,env1,s0) = (res,s) ∧
    res ≠ Rerr (Rabort Rtype_error) ∧
    calls xs g0 = (ys,g) ∧
    every_Fn_SOME xs ∧ every_Fn_vs_NONE xs ∧
    EVERY (wfv g1 l1) env1 ∧ wfv_state g1 l1 s0 ∧ wfg g0 ∧
    ALL_DISTINCT (code_locs xs) ∧
    DISJOINT (IMAGE SUC (set (code_locs xs))) (set (MAP FST (SND g0))) ∧
    l = set (code_locs xs) DIFF domain (FST g) ∧
    subg g g1 ∧ l ⊆ l1 ∧ DISJOINT l1 (domain (FST g1)) ∧ wfg g1
    ⇒
    ∃ck res' t.
    every_result (EVERY (wfv g1 l1)) (wfv g1 l1) res ∧ wfv_state g1 l1 s ∧
    (env_rel (v_rel g1 l1) env1 env2 0 (MAP (λx. (0,x)) ys) ∧
     state_rel g1 l1 s0 t0 ∧ code_includes (SND g) t0.code ∧
     code_inv s0.code s0.compile s0.compile_oracle
              t0.code t0.compile t0.compile_oracle ⇒
     evaluate (ys,env2,t0 with clock := t0.clock + ck) = (res',t) ∧
     state_rel g1 l1 s t ∧
     code_inv s.code s.compile s.compile_oracle
              t.code t.compile t.compile_oracle ∧
     result_rel (LIST_REL (v_rel g1 l1)) (v_rel g1 l1) res res')) ∧
  (∀loco f args s0 loc g l ^t0 res s f' args'.
    evaluate_app loco f args s0 = (res,s) ∧
    res ≠ Rerr (Rabort Rtype_error) ∧
    wfv g l f ∧ EVERY (wfv g l) args ∧ wfv_state g l s0 ∧
    wfg g ∧ DISJOINT l (domain (FST g))
    ⇒
    ∃ck res' t.
    every_result (EVERY (wfv g l)) (wfv g l) res ∧ wfv_state g l s ∧
    (v_rel g l f f' ∧ LIST_REL (v_rel g l) args args' ∧
     state_rel g l s0 t0 ∧
     code_inv s0.code s0.compile s0.compile_oracle
              t0.code t0.compile t0.compile_oracle ⇒
     evaluate_app loco f' args' (t0 with clock := t0.clock + ck) = (res',t) ∧
     state_rel g l s t ∧
     code_inv s.code s.compile s.compile_oracle
              t.code t.compile t.compile_oracle ∧
     result_rel (LIST_REL (v_rel g l)) (v_rel g l) res res'))`,
  ho_match_mp_tac evaluate_ind
  \\ conj_tac >- (
    rw[]
    \\ qexists_tac`0`
    \\ fs[calls_def,evaluate_def]
    \\ rveq \\ fs[evaluate_def]
    \\ fs[code_locs_def]
    \\ simp[RIGHT_EXISTS_IMP_THM]
    \\ metis_tac[state_rel_subg,SUBSET_REFL])
  \\ conj_tac >- (
    fs [evaluate_def,calls_def] \\ rw []
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
    \\ `q ≠ Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs []) \\ fs []
    \\ first_x_assum drule
    \\ fs[code_locs_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
    \\ fs [AND_IMP_INTRO,PUSH_EXISTS_IMP,GSYM PULL_EXISTS]
    \\ impl_tac THEN1
     (imp_res_tac subg_trans \\ fs []
      \\ imp_res_tac code_includes_subg \\ fs []
      \\ conj_tac THEN1 (fs [code_locs_def,ALL_DISTINCT_APPEND])
      \\ match_mp_tac SUBSET_TRANS
      \\ simp [Once CONJ_COMM] \\ asm_exists_tac \\ fs []
      \\ fs [SUBSET_DEF,DISJOINT_DEF,EXTENSION] \\ rw []
      \\ drule (GEN_ALL NOT_IN_domain_FST_g)
      \\ rpt (disch_then drule \\ fs []) \\ NO_TAC)
    \\ disch_then (qspecl_then [`env2`,`t0`] mp_tac)
    \\ strip_tac
    \\ fs [GSYM PUSH_EXISTS_IMP]
    \\ fs [PUSH_EXISTS_IMP]
    \\ reverse (Cases_on `q`) \\ fs [] \\ rveq \\ fs []
    THEN1
     (strip_tac \\ fs [] \\ qpat_x_assum `_ ==> _` mp_tac
      \\ reverse impl_tac THEN1
       (strip_tac \\ fs [evaluate_def] \\ rw [] \\ qexists_tac `ck` \\ fs [])
      \\ imp_res_tac code_includes_subg
      \\ fs [env_rel_def] \\ IF_CASES_TAC \\ fs [])
    \\ Cases_on `evaluate (y::xs,env,r)` \\ fs []
    \\ `q ≠ Rerr (Rabort Rtype_error)` by (CCONTR_TAC \\ fs []) \\ fs []
    \\ first_x_assum drule \\ fs []
    \\ `ALL_DISTINCT (code_locs (y::xs))` by
          (fs [code_locs_def,ALL_DISTINCT_APPEND] \\ NO_TAC)
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
    \\ disch_then drule \\ fs []
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
    \\ fs [AND_IMP_INTRO] \\ impl_tac THEN1
     (fs [code_locs_def,ALL_DISTINCT_APPEND,wfg_def] \\ rfs []
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ fs [DISJOINT_IMAGE_SUC] \\ fs [IN_DISJOINT]
      \\ CCONTR_TAC \\ fs [] \\ rfs [IMAGE_SUC_SUBSET_UNION]
      \\ fs [SUBSET_DEF]
      \\ TRY(first_x_assum drule) \\ CCONTR_TAC \\ fs [] \\ metis_tac [])
    \\ fs [PULL_FORALL] \\ strip_tac \\ fs [GSYM PULL_FORALL]
    \\ fs [CONJ_ASSOC] \\ conj_tac THEN1
     (every_case_tac \\ fs [] \\ rveq \\ fs []
      \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
      \\ Cases_on `a` \\ fs [])
    \\ strip_tac \\ fs [PULL_FORALL]
    \\ qpat_x_assum `_ ==> _` mp_tac
    \\ impl_tac THEN1
     (imp_res_tac code_includes_subg
      \\ fs [env_rel_def] \\ IF_CASES_TAC \\ fs [])
    \\ strip_tac \\ rw []
    \\ first_x_assum (qspecl_then [`env2`,`t`] mp_tac)
    \\ fs [AND_IMP_INTRO]
    \\ impl_tac THEN1
     (imp_res_tac code_includes_subg
      \\ conj_tac THEN1
       (fs [env_rel_def] \\ IF_CASES_TAC \\ fs []
        \\ ntac 2 strip_tac
        \\ first_x_assum match_mp_tac \\ fs [])
      \\ drule evaluate_mono \\ fs [] \\ strip_tac
      \\ imp_res_tac code_includes_SUBMAP)
    \\ strip_tac
    \\ qpat_x_assum `_ = (Rval _,t)` assume_tac
    \\ drule evaluate_add_clock \\ fs []
    \\ disch_then (qspec_then `ck'` assume_tac)
    \\ qexists_tac `ck+ck'` \\ fs [AC ADD_COMM ADD_ASSOC]
    \\ fs [evaluate_def]
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_IMP_LENGTH
    \\ fs [] \\ Cases_on `a` \\ fs [])
  (* Var *)
  \\ conj_tac >- (
    fs [evaluate_def,calls_def] \\ rw []
    \\ fs[env_rel_def,fv1_thm]
    \\ every_case_tac
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ qexists_tac `0` \\ fs []
    \\ fs [LIST_REL_EL_EQN,EVERY_MEM,MEM_EL,PULL_EXISTS,RIGHT_EXISTS_IMP_THM])
  (* If *)
  \\ conj_tac >- (
    fs [evaluate_def,calls_def] \\ rw []
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
    \\ `q ≠ Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs []) \\ fs []
    \\ first_x_assum drule
    \\ fs[code_locs_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
    \\ fs [AND_IMP_INTRO,PUSH_EXISTS_IMP,GSYM PULL_EXISTS]
    \\ impl_tac THEN1
     (imp_res_tac subg_trans \\ fs []
      \\ imp_res_tac code_includes_subg \\ fs []
      \\ conj_tac THEN1 (fs [code_locs_def,ALL_DISTINCT_APPEND])
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
      \\ rpt (disch_then drule \\ fs []))
    \\ disch_then (qspecl_then [`env2`,`t0`] mp_tac)
    \\ strip_tac
    \\ fs [GSYM PUSH_EXISTS_IMP]
    \\ fs [PUSH_EXISTS_IMP]
    \\ reverse (Cases_on `q`) \\ fs [] \\ rveq \\ fs []
    THEN1
     (strip_tac \\ fs [] \\ qpat_x_assum `_ ==> _` mp_tac
      \\ reverse impl_tac THEN1
       (strip_tac \\ fs [evaluate_def] \\ rw [] \\ qexists_tac `ck` \\ fs [])
      \\ imp_res_tac code_includes_subg
      \\ fs [env_rel_def] \\ IF_CASES_TAC \\ fs []
      \\ ntac 2 strip_tac
      \\ first_x_assum match_mp_tac \\ pop_assum mp_tac
      \\ EVAL_TAC \\ fs [])
    \\ `?a1. a = [a1]` by
     (imp_res_tac evaluate_IMP_LENGTH
      \\ Cases_on `a` \\ fs [LENGTH_NIL]) \\ rveq \\ fs []
    \\ rveq \\ fs []
    \\ Cases_on `a1 = Boolv T` \\ fs [] \\ rveq THEN1
     (first_x_assum drule \\ fs []
      \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
      \\ disch_then drule \\ fs []
      \\ `ALL_DISTINCT (code_locs [x2])` by fs [ALL_DISTINCT_APPEND]
      \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
      \\ fs [AND_IMP_INTRO] \\ impl_tac THEN1
       (imp_res_tac subg_trans \\ fs []
        \\ fs [code_locs_def,ALL_DISTINCT_APPEND,wfg_def] \\ rfs []
        \\ imp_res_tac calls_add_SUC_code_locs
        \\ fs [DISJOINT_IMAGE_SUC] \\ fs [IN_DISJOINT]
        \\ CCONTR_TAC \\ fs [] \\ rfs [IMAGE_SUC_SUBSET_UNION]
        \\ fs [SUBSET_DEF]
        \\ TRY(first_x_assum drule) \\ CCONTR_TAC \\ fs [] \\ metis_tac [])
      \\ strip_tac \\ fs [PULL_FORALL]
      \\ strip_tac
      \\ qpat_x_assum `_ ==> _` mp_tac
      \\ impl_tac THEN1
       (imp_res_tac subg_trans \\ imp_res_tac code_includes_subg
        \\ fs [env_rel_def] \\ IF_CASES_TAC \\ fs []
        \\ ntac 2 strip_tac \\ first_x_assum match_mp_tac
        \\ pop_assum mp_tac \\ EVAL_TAC \\ fs [])
      \\ strip_tac \\ rw []
      \\ first_x_assum (qspecl_then [`env2`,`t`] mp_tac)
      \\ fs [AND_IMP_INTRO]
      \\ impl_tac THEN1
       (imp_res_tac code_includes_subg
        \\ imp_res_tac evaluate_mono \\ fs []
        \\ imp_res_tac code_includes_SUBMAP \\ fs []
        \\ fs [env_rel_def] \\ IF_CASES_TAC \\ fs []
        \\ ntac 2 strip_tac
        \\ first_x_assum match_mp_tac \\ fs []
        \\ pop_assum mp_tac \\ EVAL_TAC \\ fs [])
      \\ strip_tac
      \\ qpat_x_assum `_ = (Rval _,t)` assume_tac
      \\ drule evaluate_add_clock \\ fs []
      \\ disch_then (qspec_then `ck'` assume_tac)
      \\ qexists_tac `ck+ck'` \\ fs [AC ADD_COMM ADD_ASSOC]
      \\ fs [evaluate_def]
      \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
      \\ imp_res_tac evaluate_IMP_LENGTH
      \\ fs [] \\ Cases_on `a` \\ fs [])
    \\ Cases_on `a1 = Boolv F` \\ fs [] \\ rveq THEN1
     (first_x_assum drule \\ fs []
      \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
      \\ disch_then drule \\ fs []
      \\ `ALL_DISTINCT (code_locs [x2])` by fs [ALL_DISTINCT_APPEND]
      \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
      \\ fs [AND_IMP_INTRO] \\ impl_tac THEN1
       (imp_res_tac subg_trans \\ fs []
        \\ fs [code_locs_def,ALL_DISTINCT_APPEND,wfg_def] \\ rfs []
        \\ imp_res_tac calls_add_SUC_code_locs
        \\ fs [DISJOINT_IMAGE_SUC] \\ fs [IN_DISJOINT]
        \\ CCONTR_TAC \\ fs [] \\ rfs [IMAGE_SUC_SUBSET_UNION]
        \\ fs [SUBSET_DEF]
        \\ TRY(first_x_assum drule) \\ CCONTR_TAC \\ fs [] \\ metis_tac [])
      \\ strip_tac \\ fs [PULL_FORALL]
      \\ strip_tac
      \\ qpat_x_assum `_ ==> _` mp_tac
      \\ impl_tac THEN1
       (imp_res_tac subg_trans \\ imp_res_tac code_includes_subg
        \\ fs [env_rel_def] \\ IF_CASES_TAC \\ fs []
        \\ ntac 2 strip_tac \\ first_x_assum match_mp_tac
        \\ pop_assum mp_tac \\ EVAL_TAC \\ fs [])
      \\ strip_tac \\ rw []
      \\ first_x_assum (qspecl_then [`env2`,`t`] mp_tac)
      \\ fs [AND_IMP_INTRO]
      \\ impl_tac THEN1
       (imp_res_tac code_includes_subg
        \\ imp_res_tac evaluate_mono \\ fs []
        \\ imp_res_tac code_includes_SUBMAP \\ fs []
        \\ fs [env_rel_def] \\ IF_CASES_TAC \\ fs []
        \\ ntac 2 strip_tac
        \\ first_x_assum match_mp_tac \\ fs []
        \\ pop_assum mp_tac \\ EVAL_TAC \\ fs [])
      \\ strip_tac
      \\ qpat_x_assum `_ = (Rval _,t)` assume_tac
      \\ drule evaluate_add_clock \\ fs []
      \\ disch_then (qspec_then `ck'` assume_tac)
      \\ qexists_tac `ck+ck'` \\ fs [AC ADD_COMM ADD_ASSOC]
      \\ fs [evaluate_def]
      \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
      \\ imp_res_tac evaluate_IMP_LENGTH
      \\ fs [] \\ Cases_on `a` \\ fs []))
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
    \\ imp_res_tac calls_sing \\ fs [] \\ rveq
    \\ `q ≠ Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs []) \\ fs []
    \\ first_x_assum drule
    \\ fs[code_locs_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
    \\ fs [AND_IMP_INTRO,PUSH_EXISTS_IMP,GSYM PULL_EXISTS]
    \\ impl_tac THEN1
     (imp_res_tac subg_trans \\ fs []
      \\ imp_res_tac code_includes_subg \\ fs []
      \\ conj_tac THEN1 (fs [code_locs_def,ALL_DISTINCT_APPEND])
      \\ match_mp_tac SUBSET_TRANS
      \\ simp [Once CONJ_COMM] \\ asm_exists_tac \\ fs []
      \\ fs [SUBSET_DEF,DISJOINT_DEF,EXTENSION] \\ rw []
      \\ drule (GEN_ALL NOT_IN_domain_FST_g)
      \\ rpt (disch_then drule \\ fs []) \\ NO_TAC)
    \\ disch_then (qspecl_then [`env2`,`t0`] mp_tac)
    \\ strip_tac
    \\ fs [GSYM PUSH_EXISTS_IMP]
    \\ fs [PUSH_EXISTS_IMP]
    \\ reverse (Cases_on `q`) \\ fs [] \\ rveq \\ fs []
    THEN1
     (strip_tac \\ fs [] \\ qpat_x_assum `_ ==> _` mp_tac
      \\ reverse impl_tac THEN1
       (strip_tac \\ fs [evaluate_def] \\ rw [] \\ qexists_tac `ck` \\ fs [])
      \\ imp_res_tac code_includes_subg
      \\ fs [env_rel_def] \\ IF_CASES_TAC \\ fs []
      \\ ntac 2 strip_tac \\ first_x_assum match_mp_tac \\ fs []
      \\ pop_assum mp_tac \\ fs [EXISTS_MAP]
      \\ EVAL_TAC \\ fs [fv_exists]
      \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
    \\ first_x_assum drule \\ fs []
    \\ `ALL_DISTINCT (code_locs [x2])` by
          (fs [code_locs_def,ALL_DISTINCT_APPEND] \\ NO_TAC)
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
    \\ disch_then drule \\ fs []
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
    \\ fs [AND_IMP_INTRO] \\ impl_tac THEN1
     (fs [code_locs_def,ALL_DISTINCT_APPEND,wfg_def] \\ rfs []
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ fs [DISJOINT_IMAGE_SUC] \\ fs [IN_DISJOINT]
      \\ CCONTR_TAC \\ fs [] \\ rfs [IMAGE_SUC_SUBSET_UNION]
      \\ fs [SUBSET_DEF]
      \\ TRY(first_x_assum drule) \\ CCONTR_TAC \\ fs [] \\ metis_tac [])
    \\ fs [PULL_FORALL] \\ strip_tac \\ fs [GSYM PULL_FORALL]
    \\ strip_tac \\ fs [PULL_FORALL]
    \\ qpat_x_assum `_ ==> _` mp_tac
    \\ impl_tac THEN1
     (imp_res_tac code_includes_subg
      \\ fs [env_rel_def] \\ IF_CASES_TAC \\ fs []
      \\ ntac 2 strip_tac \\ first_x_assum match_mp_tac \\ fs []
      \\ pop_assum mp_tac \\ fs []
      \\ fs [EXISTS_MAP] \\ EVAL_TAC \\ fs [fv_exists]
      \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
    \\ strip_tac \\ rw []
    \\ first_x_assum (qspecl_then [`v' ++ env2`,`t`] mp_tac)
    \\ fs [AND_IMP_INTRO]
    \\ impl_tac THEN1
     (imp_res_tac code_includes_subg
      \\ reverse conj_tac
      THEN1 (imp_res_tac evaluate_mono \\ imp_res_tac code_includes_SUBMAP \\ fs [])
      \\ fs [env_rel_def] \\ IF_CASES_TAC \\ fs []
      THEN1 (match_mp_tac EVERY2_APPEND_suff \\ fs []
             \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
      \\ ntac 2 strip_tac
      \\ imp_res_tac LIST_REL_LENGTH \\ fs []
      \\ fs [EL_APPEND_EQN,LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ fs []
      \\ drule (DECIDE ``!m1. ~(n < m2) ==> (n < m1+m2 <=> n-m2 < m1:num)``)
      \\ simp_tac bool_ss [] \\ strip_tac
      \\ first_x_assum match_mp_tac \\ fs [] \\ EVAL_TAC
      \\ imp_res_tac evaluate_IMP_LENGTH \\ fs [])
    \\ strip_tac
    \\ qpat_x_assum `_ = (Rval _,t)` assume_tac
    \\ drule evaluate_add_clock \\ fs []
    \\ disch_then (qspec_then `ck'` assume_tac)
    \\ qexists_tac `ck+ck'` \\ fs [AC ADD_COMM ADD_ASSOC]
    \\ fs [evaluate_def]
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_IMP_LENGTH
    \\ fs [] \\ Cases_on `a` \\ fs [])
  (* Raise *)
  \\ conj_tac >- (
    fs [evaluate_def,calls_def] \\ rw []
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ fs [evaluate_def]
    \\ `[HD e1] = e1` by (imp_res_tac calls_sing \\ fs [])
    \\ fs [dec_clock_def] \\ pop_assum kall_tac
    \\ Cases_on `evaluate ([x1],env,s)` \\ fs []
    \\ `q ≠ Rerr (Rabort Rtype_error)` by (CCONTR_TAC \\ fs []) \\ fs []
    \\ fs [GSYM PULL_EXISTS,PUSH_EXISTS_IMP,GSYM PULL_FORALL]
    \\ first_x_assum drule \\ fs [code_locs_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ fs [GSYM PULL_FORALL] \\ strip_tac
    \\ rw [] THEN1
     (every_case_tac \\ fs [] \\ rw []
      \\ imp_res_tac evaluate_IMP_LENGTH
      \\ Cases_on `a` \\ fs [])
    THEN1 (every_case_tac \\ fs [] \\ rw [])
    \\ fs [PULL_FORALL]
    \\ first_x_assum (qspecl_then [`env2`,`t0`] mp_tac) \\ fs [AND_IMP_INTRO]
    \\ impl_tac THEN1
     (imp_res_tac calls_sing \\ fs [env_rel_def]
      \\ IF_CASES_TAC \\ fs [] \\ ntac 2 strip_tac
      \\ first_x_assum match_mp_tac
      \\ pop_assum mp_tac \\ EVAL_TAC)
    \\ strip_tac \\ fs []
    \\ qexists_tac `ck` \\ fs []
    \\ every_case_tac \\ fs [semanticPrimitivesPropsTheory.result_rel_def,PULL_EXISTS]
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
    \\ imp_res_tac calls_sing \\ fs [] \\ rveq
    \\ `q ≠ Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs []) \\ fs []
    \\ first_x_assum drule
    \\ fs[code_locs_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
    \\ fs [AND_IMP_INTRO,PUSH_EXISTS_IMP,GSYM PULL_EXISTS]
    \\ impl_tac THEN1
     (imp_res_tac subg_trans \\ fs []
      \\ imp_res_tac code_includes_subg \\ fs []
      \\ conj_tac THEN1 (fs [code_locs_def,ALL_DISTINCT_APPEND])
      \\ match_mp_tac SUBSET_TRANS
      \\ simp [Once CONJ_COMM] \\ asm_exists_tac \\ fs []
      \\ fs [SUBSET_DEF,DISJOINT_DEF,EXTENSION] \\ rw []
      \\ drule (GEN_ALL NOT_IN_domain_FST_g)
      \\ rpt (disch_then drule \\ fs []) \\ NO_TAC)
    \\ disch_then (qspecl_then [`env2`,`t0`] mp_tac)
    \\ strip_tac
    \\ fs [GSYM PUSH_EXISTS_IMP]
    \\ fs [PUSH_EXISTS_IMP]
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    THEN1
     (strip_tac \\ fs [] \\ qpat_x_assum `_ ==> _` mp_tac
      \\ reverse impl_tac THEN1
       (strip_tac \\ fs [evaluate_def] \\ rw [] \\ qexists_tac `ck` \\ fs [])
      \\ imp_res_tac code_includes_subg
      \\ fs [env_rel_def] \\ IF_CASES_TAC \\ fs []
      \\ ntac 2 strip_tac \\ first_x_assum match_mp_tac \\ fs []
      \\ pop_assum mp_tac \\ fs [EXISTS_MAP]
      \\ EVAL_TAC \\ fs [fv_exists]
      \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
    \\ reverse (Cases_on `e`) \\ rveq \\ fs [] \\ rveq \\ fs []
    THEN1
     (strip_tac \\ fs [] \\ qpat_x_assum `_ ==> _` mp_tac
      \\ reverse impl_tac THEN1
       (strip_tac \\ fs [evaluate_def] \\ rw [] \\ qexists_tac `ck` \\ fs [])
      \\ imp_res_tac code_includes_subg
      \\ fs [env_rel_def] \\ IF_CASES_TAC \\ fs []
      \\ ntac 2 strip_tac \\ first_x_assum match_mp_tac \\ fs []
      \\ pop_assum mp_tac \\ fs [EXISTS_MAP]
      \\ EVAL_TAC \\ fs [fv_exists]
      \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
    \\ first_x_assum drule \\ fs []
    \\ `ALL_DISTINCT (code_locs [x2])` by
          (fs [code_locs_def,ALL_DISTINCT_APPEND] \\ NO_TAC)
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
    \\ disch_then drule \\ fs []
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
    \\ fs [AND_IMP_INTRO] \\ impl_tac THEN1
     (fs [code_locs_def,ALL_DISTINCT_APPEND,wfg_def] \\ rfs []
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ fs [DISJOINT_IMAGE_SUC] \\ fs [IN_DISJOINT]
      \\ CCONTR_TAC \\ fs [] \\ rfs [IMAGE_SUC_SUBSET_UNION]
      \\ fs [SUBSET_DEF]
      \\ TRY(first_x_assum drule) \\ CCONTR_TAC \\ fs [] \\ metis_tac [])
    \\ fs [PULL_FORALL] \\ strip_tac \\ fs [GSYM PULL_FORALL]
    \\ strip_tac \\ fs [PULL_FORALL]
    \\ qpat_x_assum `_ ==> _` mp_tac
    \\ impl_tac THEN1
     (imp_res_tac code_includes_subg
      \\ fs [env_rel_def] \\ IF_CASES_TAC \\ fs []
      \\ ntac 2 strip_tac \\ first_x_assum match_mp_tac \\ fs []
      \\ pop_assum mp_tac \\ fs []
      \\ fs [EXISTS_MAP] \\ EVAL_TAC \\ fs [fv_exists]
      \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
    \\ strip_tac \\ rw []
    \\ first_x_assum (qspecl_then [`v'::env2`,`t`] mp_tac)
    \\ fs [AND_IMP_INTRO]
    \\ impl_tac THEN1
     (imp_res_tac code_includes_subg
      \\ reverse conj_tac
      THEN1 (imp_res_tac evaluate_mono \\ imp_res_tac code_includes_SUBMAP \\ fs [])
      \\ fs [env_rel_def] \\ IF_CASES_TAC \\ fs []
      \\ Cases \\ fs [] \\ strip_tac
      \\ first_x_assum match_mp_tac
      \\ pop_assum mp_tac \\ EVAL_TAC \\ fs [] \\ fs [ADD1])
    \\ strip_tac
    \\ qpat_x_assum `_ = (Rerr _,t)` assume_tac
    \\ drule evaluate_add_clock \\ fs []
    \\ disch_then (qspec_then `ck'` assume_tac)
    \\ qexists_tac `ck+ck'` \\ fs [AC ADD_COMM ADD_ASSOC]
    \\ fs [evaluate_def])
  (* Op *)
  \\ conj_tac
 >- (
    fs [evaluate_def,calls_def] \\ rw []
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ fs [evaluate_def]
    \\ Cases_on `evaluate (xs,env,s)` \\ fs []
    \\ `q ≠ Rerr (Rabort Rtype_error)` by (CCONTR_TAC \\ fs []) \\ fs []
    \\ first_x_assum drule \\ fs [code_locs_def]
    \\ rpt (disch_then drule \\ fs[])
    \\ fs [GSYM PULL_EXISTS,PUSH_EXISTS_IMP,GSYM PULL_FORALL]
    \\ strip_tac
    \\ reverse (Cases_on `q`) \\ fs [] THEN1
     (rw [] \\ first_assum (qspecl_then [`env2`,`t0`] mp_tac)
      \\ impl_tac THEN1
       (fs [env_rel_def] \\ IF_CASES_TAC \\ fs []
        \\ ntac 2 strip_tac
        \\ first_x_assum match_mp_tac
        \\ pop_assum mp_tac
        \\ fs [EXISTS_MAP,fv_exists]
        \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs []
        \\ EVAL_TAC \\ fs [fv_exists])
      \\ strip_tac \\ rw [] \\ qexists_tac `ck` \\ fs [])
    \\ reverse (Cases_on `op = Install`) THEN1
     (fs [] \\ reverse (Cases_on `do_app op (REVERSE a) r`) \\ fs []
      THEN1
       (rveq \\ mp_tac do_app_thm \\ fs []
        \\ every_case_tac \\ fs []
        \\ strip_tac \\ fs[] \\ rw[]
        \\ first_x_assum(first_assum o mp_then(Pat`code_inv`)mp_tac)
        \\ simp[]
        \\ disch_then(qspec_then`env2`mp_tac)
        \\ impl_tac
        >- fsrw_tac[ETA_ss][env_rel_def, fv1_thm, EXISTS_MAP, fv_exists]
        \\ strip_tac \\ fs[]
        \\ qexists_tac`ck` \\ simp[] \\ rw[]
        \\ cheat (* note: above may not be correct *)
        )
      \\ rename1 `do_app op (REVERSE a) r = Rval z`
      \\ PairCases_on `z` \\ fs [] \\ rveq
      \\ mp_tac (Q.GENL [`t`,`v`] do_app_thm) \\ fs [] \\ rpt strip_tac
      \\ first_assum (qspecl_then [`env2`,`t0`] mp_tac)
      \\ impl_tac THEN1
       (fs [env_rel_def] \\ IF_CASES_TAC \\ fs []
        \\ ntac 2 strip_tac
        \\ first_x_assum match_mp_tac
        \\ pop_assum mp_tac
        \\ fs [EXISTS_MAP,fv_exists]
        \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs []
        \\ EVAL_TAC \\ fs [fv_exists])
      \\ strip_tac \\ qexists_tac `ck` \\ fs []
      \\ first_x_assum (qspecl_then [`t`,`v'`] mp_tac) \\ fs []
      \\ strip_tac \\ pop_assum mp_tac \\ fs []
      \\ imp_res_tac do_app_const \\ fs [])
    \\ rveq \\ fs []
    \\ fs [pair_case_eq]
    \\ rveq \\ fs []
    \\ qpat_x_assum `do_install _ r = _` mp_tac
    \\ simp [Once do_install_def]
    \\ simp [option_case_eq,list_case_eq,PULL_EXISTS,pair_case_eq,bool_case_eq]
    \\ Cases_on `v = Rerr (Rabort Rtype_error)` \\ fs []
    \\ simp [PULL_EXISTS]
    \\ pairarg_tac
    \\ fs [SWAP_REVERSE_SYM,bool_case_eq,option_case_eq,pair_case_eq,PULL_EXISTS]
    \\ rpt gen_tac \\ strip_tac \\ rveq \\ fs []
    THEN1
     (rpt strip_tac \\ fs [] \\ rveq \\ fs []
      THEN1 (fs [wfv_state_def]
             \\ `aux = []` by metis_tac [SND]
             \\ rveq \\ fs [FUPDATE_LIST,shift_seq_def])
      \\ first_x_assum (qspecl_then [`env2`,`t0`] mp_tac)
      \\ impl_tac THEN1 fs [env_rel_Op_Install]
      \\ strip_tac \\ fs [] \\ rveq \\ fs []
      \\ asm_exists_tac \\ fs []
      \\ imp_res_tac v_to_bytes_thm
      \\ imp_res_tac v_to_words_thm
      \\ fs [] \\ rveq \\ fs []
      \\ fs [do_install_def]
      \\ pairarg_tac \\ fs []
      \\ drule code_rel_state_rel_install
      \\ rpt (disch_then drule) \\ strip_tac \\ fs []
      \\ `t.clock = 0` by fs [state_rel_def] \\ fs []
      \\ fs [state_rel_def])
    \\ cheat)
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
    \\ fsrw_tac[ETA_ss][]
    \\ qmatch_asmsub_abbrev_tac`COND b`
    \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["fns2"]))
    \\ rename1`Fn (tra § 0) (SOME x) NONE num_args`
    \\ qexists_tac`if b then calls_list tra 0 x [(num_args,exp)] else [(num_args,HD e1')]` \\ fs[]
    \\ simp[PULL_EXISTS,GSYM RIGHT_EXISTS_IMP_THM]
    \\ simp[RIGHT_EXISTS_AND_THM]
    \\ imp_res_tac calls_length \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
    \\ fs[closed_Fn,code_locs_def,IN_EVEN,GSYM ADD1,ALL_DISTINCT_APPEND]
    \\ `subg g0 (insert_each x 1 g0)`
    by ( simp[subg_def,insert_each_subspt] \\ fs[wfg_def])
    \\ `wfg g`
    by (
      qunabbrev_tac`b` \\ reverse every_case_tac \\ fs[] \\ rw[]
      >- ( match_mp_tac calls_wfg \\ asm_exists_tac \\ fs[] )
      \\ qpat_x_assum`calls _ (insert_each _ _ _) = _`assume_tac
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
    \\ conj_asm1_tac
    >- (
      fs[recclosure_rel_def,recclosure_wf_def,GSYM ADD1]
      \\ qexists_tac`g0` \\ fs[PULL_EXISTS]
      \\ CASE_TAC \\ fs[calls_list_MAPi] \\ rveq
      \\ TRY(qexists_tac`tra` \\ qexists_tac`0` \\ simp[])
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ fs[SUBSET_DEF]
      \\ fs[RIGHT_EXISTS_IMP_THM,GSYM AND_IMP_INTRO]
      \\ rpt conj_tac
      \\ TRY (Cases_on`new_g'` \\ fs[code_list_def,GSYM ADD1] \\ NO_TAC)
      \\ first_x_assum (match_mp_tac o MP_CANON)
      \\ rfs[wfg_def,PULL_EXISTS]
      \\ metis_tac[] )
    \\ simp[v_rel_def,PULL_EXISTS,GSYM RIGHT_EXISTS_IMP_THM]
    \\ fsrw_tac[ETA_ss][]
    \\ simp[RIGHT_EXISTS_IMP_THM]
    \\ Cases_on`b` \\ fs[] \\ rveq \\ simp[evaluate_def]
    \\ fs[calls_list_def,GSYM ADD1] \\ strip_tac
    \\ imp_res_tac state_rel_max_app \\ fs[]
    \\ fs[env_rel_def,fv1_thm])
  (* Letrec *)
  \\ conj_tac >- (
    rw[evaluate_def] \\ fs[IS_SOME_EXISTS]
    \\ fs[calls_def,code_locs_def,ALL_DISTINCT_APPEND,
          ALL_DISTINCT_GENLIST,EVERY_GENLIST,PULL_EXISTS]
    \\ rpt(pairarg_tac \\ fs[])
    \\ fsrw_tac[ETA_ss][]
    \\ imp_res_tac calls_length \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
    \\ rveq \\ fs[]
    \\ qpat_x_assum`_ = (_,g)`mp_tac
    \\ qpat_abbrev_tac`fns2 = calls_list _ _ _ _`
    \\ qmatch_goalsub_rename_tac`Letrec (tr § 0) _ _ fns2 b2`
    \\ qpat_abbrev_tac`fns0 = ZIP _`
    \\ qmatch_goalsub_rename_tac`Letrec _ _ _ fns0 b0`
    \\ qmatch_goalsub_abbrev_tac`COND b`
    \\ strip_tac
    \\ `ys = [Letrec (if b then tr § 0 else tr ) (SOME x) NONE (if b then fns2 else fns0) (if b then b2 else b0)]`
    by ( Cases_on`b` \\ fs[] \\ rveq )
    \\ rveq
    \\ simp[evaluate_def]
    \\ qpat_abbrev_tac`bo = EVERY _ (COND _ _ _)`
    \\ `t0.max_app = s.max_app ⇒ bo = T`
    by (
      unabbrev_all_tac
      \\ CASE_TAC
      \\ fs[EVERY_MEM,calls_list_MAPi,indexedListsTheory.MEM_MAPi,
            FORALL_PROD,PULL_EXISTS,MEM_ZIP,ZIP_MAP,EL_MAP]
      \\ metis_tac[MEM_EL,FST,PAIR] )
    \\ qunabbrev_tac`bo`\\fs[](** MARKER **)
    \\ qmatch_assum_abbrev_tac`calls [exp] g2 = ([b2],_)`
    \\ qmatch_assum_rename_tac`calls [exp] g2 = ([b2],g4)`
    \\ qmatch_assum_rename_tac`calls [exp] g3 = ([b0],g5)`
    \\ `LENGTH fns2 = LENGTH fns0`
    by ( simp[Abbr`fns2`,Abbr`fns0`] )
    \\ Cases_on`fns2=[]`
    >- (
      fs[LENGTH_NIL_SYM]
      \\ `fns=[]`
      by ( Cases_on`fns` \\ fs[calls_list_MAPi] \\ fs[markerTheory.Abbrev_def])
      \\ fs[calls_def,LENGTH_NIL]
      \\ rveq \\ fs[] \\ rveq \\ fs[Abbr`fns1`]
      \\ fs[Abbr`g2`,insert_each_def,code_list_def]
      \\ rveq
      \\ first_x_assum drule
      \\ rpt(disch_then drule) \\ fs[]
      \\ fs[code_locs_def]
      \\ simp[env_rel_def,fv1_thm])
    \\ first_x_assum(qspec_then`if b then g2 else g3`mp_tac)
    \\ disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars["ys'","g'"])))
    \\ disch_then(qspecl_then[`if b then [b2] else [b0]`,`if b then g4 else g5`]mp_tac)
    \\ simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM]
    \\ impl_tac >- rw[]
    \\ disch_then(qspecl_then[`g1`,`l1`]mp_tac o CONV_RULE(RESORT_FORALL_CONV(List.rev)))
    \\ simp[RIGHT_FORALL_IMP_THM]
    \\ qpat_abbrev_tac`fns4 = if b then fns2 else _`
    \\ qpat_abbrev_tac`P ⇔ _ ⊆ l1`
    \\ `P` by ( qunabbrev_tac`P` \\ CASE_TAC \\ fs[SUBSET_DEF] )
    \\ qunabbrev_tac`P` \\ fs[]
    \\ qpat_abbrev_tac`P ⇔ subg _ g1`
    \\ `P` by ( qunabbrev_tac`P` \\ CASE_TAC \\ fs[] )
    \\ qunabbrev_tac`P` \\ fs[]
    \\ qpat_abbrev_tac`P ⇔ DISJOINT _ _`
    \\ `P`
    by (
      qunabbrev_tac`P`
      \\ CASE_TAC \\ fs[Abbr`g2`,MAP_FST_code_list]
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ imp_res_tac calls_domain
      \\ imp_res_tac calls_IS_SUFFIX
      \\ fs[domain_FST_insert_each,IS_SUFFIX_APPEND]
      \\ fs[SUBSET_DEF,MEM_GENLIST,PULL_EXISTS,ADD1,IN_DISJOINT]
      \\ metis_tac[ADD1,numTheory.INV_SUC,ADD_ASSOC,prim_recTheory.PRE] )
    \\ qunabbrev_tac`P` \\ fs[]
    \\ qpat_abbrev_tac`P ⇔ wfg _`
    \\ `P`
    by (
      qunabbrev_tac`P`
      \\ reverse CASE_TAC \\ fs[] \\ rveq
      >- (
         match_mp_tac calls_wfg
      \\ asm_exists_tac \\ fs[] )
      \\ `wfg' g2`
      by (
        simp[Abbr`g2`]
        \\ match_mp_tac wfg'_code_list
        \\ imp_res_tac calls_length
        \\ fs[SUBSET_DEF]
        \\ imp_res_tac calls_subspt
        \\ fs[subspt_def,domain_lookup]
        \\ conj_tac
        >- (
          match_mp_tac calls_wfg'
          \\ asm_exists_tac \\ fs[SUBSET_DEF]
          \\ match_mp_tac wfg'_insert_each
          \\ fs[IN_EVEN]
          \\ fs[wfg'_def,wfg_def] )
        \\ simp[ZIP_MAP,EVERY_MAP,MEM_GENLIST,PULL_EXISTS]
        \\ fs[EVERY2_EVERY,LAMBDA_PROD,closed_Fn,markerTheory.Abbrev_def]
        \\ rw[] \\ first_x_assum match_mp_tac
        \\ qmatch_abbrev_tac`lookup k d = SOME _`
        \\ `k ∈ domain d` suffices_by simp[domain_lookup]
        \\ simp[Abbr`d`,domain_FST_insert_each]
        \\ simp[MEM_GENLIST,PULL_EXISTS,Abbr`k`])
      \\ fs[wfg'_def]
      \\ simp[wfg_def,SET_EQ_SUBSET]
      \\ reverse conj_tac
      >- (
        simp[Abbr`g2`,MAP_FST_code_list,ALL_DISTINCT_APPEND,
             ALL_DISTINCT_GENLIST,MEM_GENLIST,PULL_EXISTS]
        \\ conj_tac
        >- (
          match_mp_tac calls_ALL_DISTINCT
          \\ asm_exists_tac \\ fs[]
          \\ fs[wfg_def] )
        \\ imp_res_tac calls_add_SUC_code_locs
        \\ fs[SUBSET_DEF]
        \\ rpt strip_tac
        \\ first_x_assum drule
        \\ fs[IN_DISJOINT,MEM_GENLIST,PULL_EXISTS,ADD1]
        \\ metis_tac[ADD1,numTheory.INV_SUC,ADD_ASSOC] )
      \\ rfs[Abbr`g2`,MAP_FST_code_list]
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ imp_res_tac calls_domain
      \\ imp_res_tac calls_IS_SUFFIX
      \\ fs[domain_FST_insert_each,IS_SUFFIX_APPEND]
      \\ fs[SUBSET_DEF,MEM_GENLIST,PULL_EXISTS,ADD1,IN_DISJOINT]
      \\ ntac 2 strip_tac
      \\ first_x_assum drule
      \\ rfs[wfg_def,GSYM ADD1]
      \\ metis_tac[ADD1,numTheory.INV_SUC,ADD_ASSOC,prim_recTheory.PRE] )
    \\ qunabbrev_tac`P` \\ fs[]
    \\ `∀i. i < LENGTH fns ⇒ recclosure_rel g1 l1 x fns fns4`
    by (
      simp[recclosure_rel_def]
      \\ simp[recclosure_wf_def]
      \\ fs[closed_Fn]
      \\ gen_tac \\ strip_tac
      \\ qexists_tac`g0` \\ fs[]
      \\ conj_tac
      >- (
        fs[IN_DISJOINT,SUBSET_DEF,MEM_GENLIST,PULL_EXISTS]
        \\ metis_tac[])
      \\ conj_tac
      >- (
        fs[IN_DISJOINT,MEM_GENLIST,PULL_EXISTS]
        \\ metis_tac[ADD1,numTheory.INV_SUC,ADD_ASSOC] )
      \\ `b ⇒ subg g2 g4`
      by (
        strip_tac
        \\ match_mp_tac calls_subg
        \\ asm_exists_tac \\ fs[]
        \\ fs[wfg_def]  )
      \\ `¬b ⇒ subg g3 g5`
      by (
        strip_tac
        \\ match_mp_tac calls_subg
        \\ asm_exists_tac \\ fs[]
        \\ fs[wfg_def] )
      \\ `wfg g`
      by (
        match_mp_tac calls_wfg
        \\ Cases_on`b`\\fs[]
        \\ asm_exists_tac \\ fs[] )
      \\ CASE_TAC \\ fs[PULL_EXISTS] \\ rveq
      \\ TRY(qexists_tac`tr` >> qexists_tac`1` >> conj_tac >- metis_tac[])
      \\ (conj_tac >- metis_tac[subg_trans])
      \\ qpat_x_assum`_ ∪ _ DIFF _ ⊆ _`assume_tac
      \\ fs[SUBSET_DEF] \\ rw[]
      \\ first_x_assum match_mp_tac \\ fs[]
      \\ strip_tac
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ rfs[wfg_def]
      \\ rfs[Abbr`g2`]
      \\ rfs[SUBSET_DEF,PULL_EXISTS]
      \\ first_x_assum drule \\ simp[]
      \\ strip_tac
      \\ first_x_assum drule \\ simp[]
      \\ fs[MEM_GENLIST,IN_DISJOINT]
      \\ metis_tac[numTheory.INV_SUC] )
    \\ impl_tac >- metis_tac[]
    \\ qpat_abbrev_tac`env3 = _ ++ env2`
    \\ disch_then(qspecl_then[`t0`,`env3`]mp_tac)
    \\ strip_tac
    \\ qexists_tac`ck` \\ simp[]
    \\ simp[RIGHT_EXISTS_AND_THM,RIGHT_EXISTS_IMP_THM]
    \\ rpt strip_tac
    \\ imp_res_tac state_rel_max_app
    \\ qpat_x_assum`_ ⇒ _`mp_tac
    \\ impl_tac
    >- (
      fs[]
      \\ `LENGTH fns4 = LENGTH fns`
      by (
        fs[Abbr`fns4`,Abbr`fns0`]
        \\ CASE_TAC \\ fs[] )
      \\ fs[env_rel_def,Abbr`env3`]
      \\ IF_CASES_TAC \\ fs[]
      >- (
        match_mp_tac EVERY2_APPEND_suff \\ fs[]
        \\ simp[LIST_REL_GENLIST]
        \\ simp[v_rel_def]
        \\ fsrw_tac[ETA_ss][PULL_EXISTS]
        \\ ntac 2 strip_tac
        \\ conj_tac >- metis_tac[]
        \\ simp[env_rel_def] )
      \\ simp[EXISTS_MAP]
      \\ qx_gen_tac`a`
      \\ Cases_on`a < LENGTH fns`
      \\ simp[EL_APPEND1,EL_APPEND2]
      >- (
        simp[v_rel_def]
        \\ fsrw_tac[ETA_ss][PULL_EXISTS]
        \\ simp[env_rel_def]
        \\ fs[fv1_thm]
        \\ metis_tac[] )
      \\ fs[fv1_thm]
      \\ strip_tac
      \\ first_x_assum(qspec_then`a - LENGTH fns`mp_tac)
      \\ simp[]
      \\ impl_tac
      >- ( CASE_TAC \\ fs[] )
      \\ simp[] )
    \\ simp[]
    \\ impl_tac >- (CASE_TAC \\ fs[])
    \\ strip_tac
    \\ CASE_TAC \\ fs[])
  (* App *)
  \\ conj_tac >- (
    rw[evaluate_def,calls_def]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ fs[code_locs_def]
    \\ qpat_x_assum`_ = (res,_)`mp_tac
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
    \\ `wfg g'`
    by (
      match_mp_tac calls_wfg
      \\ asm_exists_tac
      \\ fs[ALL_DISTINCT_APPEND] )
    \\ `wfg g`
    by (
      match_mp_tac calls_wfg
      \\ asm_exists_tac \\ fs[] )
    \\ `env_rel (v_rel g1 l1) env env2 0 (MAP (λx. (0,x)) ys) ⇒
        env_rel (v_rel g1 l1) env env2 0 (MAP (λx. (0,x)) es)`
    by (
      qpat_x_assum`_ = (ys,_)`mp_tac
      \\ qmatch_goalsub_abbrev_tac`COND b1`
      \\ reverse(Cases_on`b1`) \\ fs[]
      >- (
        strip_tac \\ rveq
        \\ fsrw_tac[ETA_ss][env_rel_def,fv1_thm,EXISTS_MAP,fv_exists]
        \\ metis_tac[] )
      \\ IF_CASES_TAC \\ fs[]
      >- (
        strip_tac \\ rveq
        \\ fsrw_tac[ETA_ss][env_rel_def,fv1_thm,EXISTS_MAP,fv_exists] )
      \\ strip_tac \\ rveq
      \\ fsrw_tac[ETA_ss][env_rel_def,fv1_thm,EXISTS_MAP,fv_exists]
      \\ metis_tac[])
    \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      strip_tac \\ rveq \\ rfs[]
      \\ first_x_assum drule \\ fs[DISJOINT_SYM,ALL_DISTINCT_APPEND]
      \\ rpt(disch_then drule)
      \\ disch_then(qspecl_then[`env2`,`t0`]mp_tac)
      \\ impl_tac
      >- (
        conj_tac >- metis_tac[subg_trans]
        \\ simp[]
        \\ fs[SUBSET_DEF]
        \\ fs[subg_def]
        \\ imp_res_tac subspt_domain_SUBSET
        \\ fs[SUBSET_DEF] \\ rw[]
        \\ Cases_on`x ∉ domain (FST g)` >- metis_tac[]
        \\ fs[]
        \\ imp_res_tac calls_add_SUC_code_locs
        \\ rfs[wfg_def,SUBSET_DEF,PULL_EXISTS]
        \\ metis_tac[])
      \\ strip_tac
      \\ qexists_tac`ck`
      \\ imp_res_tac calls_length
      \\ simp[RIGHT_EXISTS_AND_THM,RIGHT_EXISTS_IMP_THM]
      \\ strip_tac
      \\ `state_rel g1 l1 r t ∧ code_includes (SND g') t0.code`
      by metis_tac[state_rel_subg,code_includes_subg]
      \\ fs[] \\ rfs[] \\ rveq
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
    \\ disch_then(qspecl_then[`env2`,`t0`]mp_tac)
    \\ impl_tac
    >- (
      conj_tac >- metis_tac[subg_trans]
      \\ simp[]
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
    \\ disch_then(qspecl_then[`env2`,`t`]mp_tac)
    \\ disch_then(qspecl_then[`l1`,`g1`]mp_tac)
    \\ strip_tac
    \\ rveq
    \\ qpat_x_assum`_ = (ys,_)`mp_tac
    \\ qmatch_goalsub_abbrev_tac`COND b`
    \\ reverse IF_CASES_TAC \\ fs[]
    >- (
      strip_tac \\ rveq
      \\ simp[evaluate_def]
      \\ imp_res_tac calls_length
      \\ simp[]
      \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
      \\ rveq \\ fs[]
      \\ qpat_x_assum`_ ⇒ _`mp_tac
      \\ impl_tac
      >- (
        imp_res_tac evaluate_const \\ fs[]
        \\ fs[SUBSET_DEF])
      \\ strip_tac
      \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
      >- (
        strip_tac \\ rveq \\ fs[]
        \\ simp[RIGHT_EXISTS_IMP_THM,RIGHT_EXISTS_AND_THM]
        \\ strip_tac \\ fs[] \\ rfs[]
        \\ `code_includes (SND g') t0.code` by metis_tac[code_includes_subg] \\ fs[]
        \\ qpat_x_assum`evaluate(es,env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
        \\ disch_then(qspec_then`ck'`mp_tac) \\ simp[] \\ strip_tac
        \\ qexists_tac`ck+ck'` \\ fs[]
        \\ qpat_x_assum`_ ⇒ _`mp_tac
        \\ impl_tac
        >- (
          imp_res_tac evaluate_mono \\ fs[]
          \\ fs[env_rel_def,fv1_thm]
          \\ metis_tac[code_includes_SUBMAP] )
        \\ strip_tac \\ fs[])
      \\ strip_tac \\ fs[] \\ rfs[]
      \\ imp_res_tac evaluate_length_imp
      \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
      \\ rveq \\ fs[]
      \\ first_x_assum drule
      \\ rpt(disch_then drule)
      \\ simp[RIGHT_EXISTS_IMP_THM,RIGHT_EXISTS_AND_THM,FORALL_AND_THM]
      \\ strip_tac \\ fs[] \\ strip_tac \\ fs[] \\ rfs[]
      \\ `code_includes (SND g') t0.code` by metis_tac[code_includes_subg] \\ fs[]
      \\ qpat_x_assum`_ ⇒ _`mp_tac
      \\ impl_tac
      >- (
        imp_res_tac evaluate_mono \\ fs[]
        \\ fs[env_rel_def,fv1_thm]
        \\ metis_tac[code_includes_SUBMAP] )
      \\ strip_tac \\ fs[] \\ rveq
      \\ first_x_assum drule
      \\ rpt(disch_then drule)
      \\ strip_tac
      \\ qmatch_assum_rename_tac`LIST_REL (v_rel _ _) ev1 ev2`
      \\ qpat_x_assum`evaluate(es,env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
      \\ disch_then(qspec_then`ck'+ck''`mp_tac) \\ simp[] \\ strip_tac
      \\ qpat_x_assum`evaluate([_],env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
      \\ disch_then(qspec_then`ck''`mp_tac) \\ simp[] \\ strip_tac
      \\ qexists_tac`ck+ck'+ck''` \\ fs[])
    \\ qpat_x_assum`Abbrev(IS_SOME _ ∧ _)`mp_tac
    \\ simp[markerTheory.Abbrev_def,IS_SOME_EXISTS]
    \\ strip_tac \\ rveq \\ fs[]
    \\ `x ∈ domain (FST g)` by simp[domain_lookup]
    \\ `x ∈ domain (FST g1)` by (
      fs[subg_def]
      \\ imp_res_tac subspt_domain_SUBSET
      \\ fs[SUBSET_DEF] )
    \\ `x ∉ l1` by ( fs[IN_DISJOINT] \\ metis_tac[] )
    \\ IF_CASES_TAC \\ fs[] \\ strip_tac \\ rveq \\ fs[]
    \\ simp[evaluate_def]
    >- (
      drule (Q.GEN`s`pure_correct |> INST_TYPE [``:'c``|->``:calls_state # 'c``])
      \\ disch_then(qspec_then`r`mp_tac)
      \\ simp[]
      \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
      >- (CASE_TAC \\ fs[])
      \\ ntac 2 strip_tac \\ rveq
      \\ fs[quantHeuristicsTheory.LIST_LENGTH_2] \\ rveq
      \\ rfs[] \\ rveq
      \\ qpat_x_assum`_ ⇒ _`mp_tac
      \\ impl_tac >- fs[SUBSET_DEF]
      \\ strip_tac \\ fs[]
      \\ first_x_assum drule
      \\ simp[RIGHT_EXISTS_IMP_THM,RIGHT_EXISTS_AND_THM,FORALL_AND_THM]
      \\ strip_tac \\ fs[]
      \\ strip_tac \\ fs[]
      \\ qpat_x_assum`_ ⇒ _`kall_tac
      \\ qpat_x_assum`_ ⇒ _`mp_tac
      \\ impl_keep_tac
      >- ( fs[] \\ metis_tac[code_includes_subg] )
      \\ strip_tac \\ fs[]
      \\ qmatch_assum_rename_tac`LIST_REL (v_rel g1 l1) ev1 ev2`
      \\ Cases_on`ev1 = []`
      \\ imp_res_tac evaluate_length_imp \\ rfs[]
      \\ fs[evaluate_app_rw]
      \\ qpat_x_assum`_ = (res,_)`mp_tac
      \\ BasicProvers.TOP_CASE_TAC \\ fs[]
      \\ strip_tac
      \\ drule (GEN_ALL dest_closure_v_rel_lookup)
      \\ qmatch_assum_rename_tac`dest_closure _ _ f1 ev1 = _`
      \\ `∃f2. v_rel g1 l1 f1 f2`
      by ( match_mp_tac v_rel_exists \\ fs[] )
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
      \\ rfs[]
      \\ qpat_x_assum`code_includes (SND g) _`assume_tac
      \\ drule (GEN_ALL code_includes_ALOOKUP)
      \\ disch_then drule \\ strip_tac
      \\ first_x_assum drule
      \\ disch_then drule
      \\ qpat_x_assum`state_rel g1 l1 r t`assume_tac
      \\ disch_then drule
      \\ disch_then drule
      \\ strip_tac
      \\ imp_res_tac LIST_REL_LENGTH \\ fs[]
      \\ Cases_on`ev2 = []` \\ fs[]
      \\ fs[evaluate_app_rw]
      \\ qpat_x_assum`_ = (_,_)`mp_tac
      \\ imp_res_tac state_rel_clock \\ fs[]
      \\ imp_res_tac state_rel_max_app \\ fs[]
      \\ `FLOOKUP t.code (x + 1) = FLOOKUP t0.code (x + 1)` by
       (imp_res_tac evaluate_mono
        \\ fs [FLOOKUP_DEF,SUBMAP_DEF] \\ rfs []
        \\ metis_tac [])
      \\ IF_CASES_TAC \\ fs[]
      >- (
        strip_tac \\ rveq
        \\ qexists_tac`ck` \\ simp[find_code_def]
        \\ match_mp_tac state_rel_with_clock
        \\ metis_tac[state_rel_subg] )
      \\ simp[evaluate_def,evaluate_GENLIST_Var_tra]
      \\ simp[find_code_def]
      \\ simp[Once dec_clock_def]
      \\ fs[]
      \\ simp[Once dec_clock_def]
      \\ imp_res_tac evaluate_length_imp \\ fs[NOT_LESS]
      \\ IF_CASES_TAC
      >- (
        fs[] \\ strip_tac \\ rveq \\ fs[]
        \\ `t.clock = LENGTH ev2 - ck''` by decide_tac
        \\ fs[]
        \\ qexists_tac`ck` \\ simp[]
        \\ fs[dec_clock_def])
      \\ fs[NOT_LESS_EQUAL]
      \\ strip_tac
      \\ fs[dec_clock_def,TAKE_APPEND1]
      \\ qpat_x_assum`evaluate(es,env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
      \\ disch_then(qspec_then`ck''`mp_tac) \\ simp[] \\ strip_tac
      \\ qexists_tac`ck+ck''` \\ simp[]
      \\ qpat_x_assum`_ _  _ = (_,_)`mp_tac
      \\ BasicProvers.TOP_CASE_TAC \\ fs[]
      \\ BasicProvers.TOP_CASE_TAC \\ fs[]
      \\ TRY BasicProvers.TOP_CASE_TAC \\ fs[]
      \\ TRY BasicProvers.TOP_CASE_TAC \\ fs[])
    \\ qpat_x_assum`_ ⇒ _`mp_tac
    \\ impl_tac
    >- (
      imp_res_tac evaluate_mono \\ fs[]
      \\ fs[SUBSET_DEF] )
    \\ strip_tac
    \\ simp[evaluate_append]
    \\ imp_res_tac calls_length
    \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
    \\ rveq \\ fs[]
    \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      rw[] \\ fs[]
      \\ simp[RIGHT_EXISTS_IMP_THM,RIGHT_EXISTS_AND_THM]
      \\ strip_tac \\ fs[] \\ rfs[]
      \\ `code_includes (SND g') t0.code` by metis_tac[code_includes_subg]
      \\ fs[] \\ rfs[]
      \\ imp_res_tac evaluate_mono \\ fs[]
      \\ imp_res_tac code_includes_SUBMAP \\ fs[]
      \\ qpat_x_assum`_ ⇒ _`mp_tac
      \\ impl_tac
      >- (
        fsrw_tac[ETA_ss][env_rel_def,fv1_thm,EXISTS_MAP]
        \\ metis_tac[] )
      \\ strip_tac \\ fs[]
      \\ qpat_x_assum`evaluate(es,env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
      \\ disch_then(qspec_then`ck'`mp_tac) \\ simp[] \\ strip_tac
      \\ qexists_tac`ck+ck'` \\ simp[])
    \\ strip_tac \\ fs[]
    \\ simp[evaluate_GENLIST_Var_tra]
    \\ imp_res_tac evaluate_length_imp \\ fs[]
    \\ fs[quantHeuristicsTheory.LIST_LENGTH_2] \\ rveq
    \\ rfs[] \\ rveq
    \\ first_x_assum drule
    \\ rpt(disch_then drule)
    \\ simp[RIGHT_EXISTS_IMP_THM,RIGHT_EXISTS_AND_THM,FORALL_AND_THM]
    \\ strip_tac
    \\ strip_tac \\ fs[] \\ rfs[]
    \\ `code_includes (SND g') t0.code` by metis_tac[code_includes_subg]
    \\ fs[]
    \\ imp_res_tac evaluate_mono \\ fs[]
    \\ imp_res_tac code_includes_SUBMAP \\ fs[]
    \\ qpat_x_assum`_ ⇒ _`mp_tac
    \\ impl_keep_tac
    >- (
      fsrw_tac[ETA_ss][env_rel_def,fv1_thm]
      \\ metis_tac[] )
    \\ strip_tac \\ rveq \\ fs[]
    \\ first_x_assum drule
    \\ rpt (disch_then drule)
    \\ strip_tac \\ fs[]
    \\ imp_res_tac evaluate_length_imp \\ fs[] \\ rw[]
    \\ qmatch_assum_rename_tac`LIST_REL (v_rel g1 l1) ev1 ev2`
    \\ Cases_on`ev1 = []` \\ fs[]
    \\ fs[evaluate_app_rw]
    \\ qpat_x_assum`_ = (res,_)`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ drule (GEN_ALL dest_closure_v_rel_lookup)
    \\ disch_then drule
    \\ disch_then drule
    \\ impl_tac >- rw[]
    \\ strip_tac \\ fs[]
    \\ Cases_on`ev2 = []` \\ fs[]
    \\ fs[evaluate_app_rw]
    \\ qpat_x_assum`_ _ _ _ = (_,_)`mp_tac
    \\ imp_res_tac state_rel_clock \\ fs[]
    \\ imp_res_tac state_rel_max_app \\ fs[]
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
    \\ rfs[]
    \\ imp_res_tac code_includes_ALOOKUP \\ fs[]
    \\ IF_CASES_TAC \\ fs[]
    >- (
      strip_tac \\ rveq
      \\ strip_tac \\ rveq
      \\ qpat_x_assum`evaluate(es,env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
      \\ disch_then(qspec_then`ck'`mp_tac) \\ simp[] \\ strip_tac
      \\ qexists_tac`ck+ck'` \\ simp[find_code_def]
      \\ imp_res_tac evaluate_mono
      \\ fs [SUBMAP_DEF,FLOOKUP_DEF])
    \\ simp[Once dec_clock_def]
    \\ simp[evaluate_def,evaluate_GENLIST_Var_tra]
    \\ simp[find_code_def]
    \\ simp[Once dec_clock_def]
    \\ simp[Once dec_clock_def]
    \\ `FLOOKUP t'.code (x + 1) = FLOOKUP t.code (x + 1)` by
      (imp_res_tac evaluate_mono \\ fs [SUBMAP_DEF,FLOOKUP_DEF]) \\ fs[]
    \\ IF_CASES_TAC
    >- (
      fs[] \\ strip_tac \\ rveq \\ fs[]
      \\ `t'.clock = LENGTH ev2 - ck''` by decide_tac
      \\ fs[] \\ strip_tac
      \\ qpat_x_assum`evaluate(es,env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
      \\ disch_then(qspec_then`ck'`mp_tac) \\ simp[] \\ strip_tac
      \\ qexists_tac`ck+ck'` \\ simp[])
    \\ fs[NOT_LESS,NOT_LESS_EQUAL]
    \\ strip_tac
    \\ fs[dec_clock_def,TAKE_APPEND1]
    \\ IF_CASES_TAC \\ fs[]
    >- (
      strip_tac \\ rveq \\ fs[]
      \\ qpat_x_assum`evaluate(es,env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
      \\ disch_then(qspec_then`ck'`mp_tac) \\ simp[] \\ strip_tac
      \\ qexists_tac`ck+ck'` \\ simp[]
      \\ match_mp_tac state_rel_with_clock
      \\ metis_tac[state_rel_subg] )
    \\ fs[NOT_LESS]
    \\ strip_tac
    \\ qpat_x_assum`evaluate(es,env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
    \\ disch_then(qspec_then`ck''+ck'`mp_tac) \\ simp[] \\ strip_tac
    \\ qexists_tac`ck+ck'+ck''` \\ simp[]
    \\ qpat_x_assum`evaluate([_],env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
    \\ disch_then(qspec_then`ck''`mp_tac) \\ simp[] \\ strip_tac
    \\ simp[TAKE_APPEND1]
    \\ ntac 2 (pop_assum kall_tac)
    \\ ntac 2 (qpat_x_assum`_ = (_,_)`mp_tac)
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ TRY BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ TRY BasicProvers.TOP_CASE_TAC \\ fs[])
  (* Tick *)
  \\ conj_tac >- (
    fs [evaluate_def,calls_def] \\ rpt strip_tac
    \\ Cases_on `s.clock = 0` \\ fs [] THEN1
     (fs [PUSH_EXISTS_IMP,GSYM PULL_EXISTS]
      \\ pairarg_tac \\ fs [] \\ rw []
      \\ `t0.clock = s.clock` by fs [state_rel_def]
      \\ fs [evaluate_def]
      \\ `[HD e1] = e1` by (imp_res_tac calls_sing \\ fs [])
      \\ qexists_tac `0` \\ fs [state_rel_def,code_inv_def])
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ fs [dec_clock_def]
    \\ first_x_assum drule \\ fs [code_locs_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ fs [GSYM PULL_FORALL]
    \\ impl_tac THEN1 fs [wfv_state_def]
    \\ disch_then (qspecl_then [`env2`,`t0 with clock := t0.clock-1`] mp_tac)
    \\ strip_tac \\ fs []
    \\ fs [PUSH_EXISTS_IMP,GSYM PULL_EXISTS] \\ rw [] \\ fs []
    \\ `[HD e1] = e1` by (imp_res_tac calls_sing \\ fs []) \\ fs []
    \\ qpat_x_assum `_ ==> _` mp_tac
    \\ impl_tac THEN1
     (fs [state_rel_def,env_rel_def]
      \\ IF_CASES_TAC \\ fs [] \\ fs []
      \\ ntac 2 strip_tac \\ first_x_assum match_mp_tac
      \\ Cases_on `e1` \\ fs [] \\ rw []
      \\ `!x t y. fv1 x (Tick t y) = fv1 x y` by (EVAL_TAC \\ fs []) \\ fs [])
    \\ strip_tac
    \\ `t0.clock = s.clock` by fs [state_rel_def]
    \\ fs [evaluate_def]
    \\ qexists_tac `ck` \\ fs [dec_clock_def]
    \\ `ck + s.clock − 1 = ck + (s.clock − 1)` by decide_tac
    \\ qpat_x_assum `_ = (_,_)` mp_tac
    \\ pop_assum (fn th => simp_tac std_ss [th])
    \\ fs [])
  (* Call *)
  \\ conj_tac >- (
    rw[evaluate_def,calls_def,code_locs_def,ALL_DISTINCT_APPEND]
    \\ pairarg_tac \\ fs[]
    \\ qpat_x_assum`_ = (res,s)`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ rveq \\ fs[] \\ strip_tac
    \\ `r.code = FEMPTY`
    by (
      CCONTR_TAC \\ fs []
      \\ Cases_on `q` \\ fs [case_eq_thms,pair_case_eq]
      \\ rveq \\ fs [] \\ rfs []
      \\ first_x_assum drule
      \\ disch_then drule \\ fs []
      \\ fs[wfv_state_def])
    \\ qpat_x_assum `_ = (_,_)` mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    >- ( simp[find_code_def] )
    \\ strip_tac \\ rveq \\ rfs[]
    \\ rw[evaluate_def]
    \\ first_x_assum drule
    \\ disch_then drule \\ fs[]
    \\ simp[RIGHT_EXISTS_IMP_THM,RIGHT_EXISTS_AND_THM,FORALL_AND_THM]
    \\ strip_tac \\ fs[] \\ strip_tac \\ fs[]
    \\ `env_rel (v_rel g1 l1) env env2 0 (MAP (λx. (0,x)) xs')`
    by ( fsrw_tac[ETA_ss][env_rel_def,fv1_thm,EXISTS_MAP,fv_exists] )
    \\ first_x_assum drule
    \\ rpt(disch_then drule) \\ rw[]
    \\ qexists_tac`ck`
    \\ rw[] )
  \\ conj_tac >- ( rw[evaluate_def] \\ qexists_tac`0` \\ rw[RIGHT_EXISTS_IMP_THM,RIGHT_EXISTS_AND_THM] )
  (* app cons *)
  \\ simp[evaluate_def]
  \\ rpt gen_tac \\ strip_tac
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  >- (
    simp[PULL_EXISTS]
    \\ rpt gen_tac \\ strip_tac
    \\ simp[RIGHT_EXISTS_AND_THM,RIGHT_EXISTS_IMP_THM]
    \\ conj_asm1_tac
    >- (
      every_case_tac \\ fs[] \\ rveq \\ fs[]
      \\ match_mp_tac (GEN_ALL dest_closure_partial_wfv)
      \\ asm_exists_tac \\ fs[] )
    \\ conj_asm1_tac
    >- (
      every_case_tac \\ fs[] \\ rveq \\ fs[]
      \\ fs[wfv_state_def,dec_clock_def] )
    \\ qmatch_goalsub_rename_tac`aaa = _ ::_`
    \\ Cases_on`aaa` \\ fs[]
    \\ simp[RIGHT_EXISTS_IMP_THM,RIGHT_EXISTS_AND_THM]
    \\ strip_tac
    \\ simp[evaluate_app_rw]
    \\ drule (GEN_ALL dest_closure_v_rel)
    \\ disch_then drule \\ fs[PULL_EXISTS]
    \\ disch_then drule \\ disch_then drule
    \\ strip_tac \\ fs[]
    \\ imp_res_tac state_rel_clock \\ fs[]
    \\ imp_res_tac state_rel_max_app \\ fs[]
    \\ qexists_tac`0` \\ fs[]
    \\ imp_res_tac LIST_REL_LENGTH
    \\ rw[] \\ fs[] \\ rw[dec_clock_def]
    \\ match_mp_tac state_rel_with_clock \\ fs[] )
  \\ fs[PULL_EXISTS]
  \\ rpt gen_tac \\ strip_tac
  \\ simp[RIGHT_EXISTS_AND_THM,RIGHT_EXISTS_IMP_THM]
  \\ qpat_x_assum`_ = (res,_)`mp_tac
  \\ IF_CASES_TAC
  >- (
    simp[] \\ strip_tac \\ rveq \\ fs[]
    \\ conj_tac >- fs[wfv_state_def]
    \\ qexists_tac`0` \\ fs[]
    \\ qmatch_goalsub_rename_tac`aaa = _ ::_`
    \\ Cases_on`aaa` \\ fs[]
    \\ simp[RIGHT_EXISTS_AND_THM,RIGHT_EXISTS_IMP_THM]
    \\ rw[evaluate_app_rw]
    \\ drule (GEN_ALL dest_closure_v_rel)
    \\ disch_then drule \\ fs[PULL_EXISTS]
    \\ rpt (disch_then drule) \\ strip_tac
    \\ simp[]
    \\ imp_res_tac state_rel_clock
    \\ imp_res_tac state_rel_max_app
    \\ imp_res_tac LIST_REL_LENGTH \\ fs[]
    \\ match_mp_tac state_rel_with_clock \\ fs[] )
  \\ BasicProvers.TOP_CASE_TAC \\ fs[] \\ rfs[]
  \\ strip_tac
  \\ qmatch_abbrev_tac`c1 ∧ c2 ∧ _`
  \\ qmatch_asmsub_rename_tac`wfv g1 l1`
  \\ qmatch_asmsub_rename_tac`Full_app e args rest`
  \\ `c1 ∧ c2 ∧ EVERY (wfv g1 l1) (args++rest)` by
   (drule (GEN_ALL dest_closure_full_wfv) \\ fs[]
    \\ rpt (disch_then drule) \\ strip_tac
    \\ qmatch_asmsub_rename_tac`err ≠ Rerr _`
    \\ Cases_on`err = Rerr (Rabort Rtype_error)` \\ fs[]
    \\ rveq
    \\ fs[recclosure_rel_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ qmatch_asmsub_abbrev_tac`COND b`
    \\ Cases_on`b` \\ fs[Abbr`c1`,Abbr`c2`] \\ rveq >- (
      qhdtm_x_assum`calls`kall_tac
      \\ drule calls_replace_SND
      \\ disch_then(qspec_then`insert_each' (SND g1) loc (LENGTH fns1) g0`mp_tac)
      \\ simp[FST_insert_each']
      \\ imp_res_tac calls_IS_SUFFIX
      \\ fs[IS_SUFFIX_APPEND] \\ strip_tac
      \\ drule (GEN_ALL calls_el_sing)
      \\ disch_then(qspec_then`i`mp_tac)
      \\ impl_tac
      >- (
        fs[MAP_FST_insert_each',recclosure_wf_def]
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
      \\ simp[EL_MAP] \\ strip_tac
      \\ first_x_assum drule
      \\ disch_then(qspecl_then[`ARB`,`ARB`,`l1`,`g1`]mp_tac)
      \\ impl_tac >- (
        fs[recclosure_wf_def]
        \\ fs[code_locs_map,recclosure_wf_def]
        \\ imp_res_tac ALL_DISTINCT_FLAT_EVERY >>
        fs[Q.SPEC`MAP _ _`every_Fn_SOME_EVERY,
           Q.SPEC`MAP _ _`every_Fn_vs_NONE_EVERY,
           EVERY_MAP,EVERY_MEM,NOT_LESS_EQUAL]
        \\ `∃n. MEM (n,SND (EL i fns1)) fns1` by metis_tac[MEM_EL,SND,PAIR]
        \\ fs[EVERY_MAP,EVERY_MEM]
        \\ fs[IN_DISJOINT,SUBSET_DEF,MEM_FLAT,PULL_EXISTS,MEM_MAP]
        \\ rpt(first_x_assum drule) \\ simp[]
        \\ fs[wfv_state_def,dec_clock_def]
        \\ ntac 4 strip_tac
        \\ conj_tac >- (
          match_mp_tac subg_trans \\ asm_exists_tac \\ fs []
          \\ match_mp_tac subg_trans \\ once_rewrite_tac [CONJ_COMM]
          \\ asm_exists_tac \\ fs []
          \\ match_mp_tac subg_insert_each' \\ fs []
          \\ imp_res_tac calls_length \\ fs []
          \\ asm_exists_tac \\ fs []
          \\ conj_tac
          >- (
            fs[wfg_def]
            \\ qpat_x_assum`_ = IMAGE SUC (domain (FST g0))`(assume_tac o SYM)
            \\ fs[]
            \\ fs[IN_DISJOINT,MEM_GENLIST,MEM_MAP] )
          \\ conj_tac
          >- (
            `ALL_DISTINCT (MAP FST (SND new_g))`
            by (
              match_mp_tac calls_ALL_DISTINCT
              \\ asm_exists_tac \\ fs[]
              \\ fs[wfg_def,ALL_DISTINCT_APPEND,code_locs_map]
              \\ qpat_x_assum`_ = IMAGE SUC (domain (FST g0))`(assume_tac o SYM)
              \\ fs[] \\ fs[IN_DISJOINT,MEM_MAP,MEM_FLAT,PULL_EXISTS] )
            \\ rfs[ALL_DISTINCT_APPEND,wfg_def]
            \\ simp[IN_DISJOINT]
            \\ metis_tac[] )
          \\ qpat_x_assum`subg _ g1` mp_tac
          \\ rw[subg_def,SND_code_list_ZIP]
          \\ first_x_assum match_mp_tac
          \\ simp[ALOOKUP_APPEND]
          \\ BasicProvers.CASE_TAC
          >- (
            rfs[REVERSE_ZIP,ALOOKUP_ZIP_FAIL,MEM_GENLIST]
            \\ metis_tac[ADD_ASSOC,ADD_COMM] )
          \\ CONV_TAC(REWR_CONV(GSYM SOME_11))
          \\ pop_assum (SUBST_ALL_TAC o SYM)
          \\ match_mp_tac ALOOKUP_ALL_DISTINCT_MEM
          \\ simp[MAP_REVERSE,MAP_ZIP,ALL_DISTINCT_GENLIST]
          \\ simp[MEM_ZIP]
          \\ asm_exists_tac \\ simp[EL_ZIP,EL_MAP] )
        \\ metis_tac[] )
      \\ strip_tac
      \\ reverse(Cases_on`err`) \\ fs[]
      >- ( rveq \\ fs[] )
      \\ imp_res_tac evaluate_SING \\ fs[]
      \\ rfs[]
      \\ first_x_assum drule \\ simp[]
      \\ simp[RIGHT_EXISTS_AND_THM,RIGHT_EXISTS_IMP_THM] )
    \\ drule (GEN_ALL calls_el_sing)
    \\ disch_then(qspec_then`i`mp_tac)
    \\ impl_tac
    >- ( rfs[wfg_def,recclosure_wf_def] )
    \\ simp[EL_MAP] \\ strip_tac
    \\ first_x_assum drule
    \\ disch_then(qspecl_then[`ARB`,`ARB`,`l1`,`g1`]mp_tac)
    \\ impl_tac
    >- (
      fs[recclosure_wf_def]
      \\ fs[code_locs_map,recclosure_wf_def]
      \\ imp_res_tac ALL_DISTINCT_FLAT_EVERY >>
      fs[Q.SPEC`MAP _ _`every_Fn_SOME_EVERY,
         Q.SPEC`MAP _ _`every_Fn_vs_NONE_EVERY,
         EVERY_MAP,EVERY_MEM,NOT_LESS_EQUAL]
      \\ `∃n. MEM (n,SND (EL i fns1)) fns1` by metis_tac[MEM_EL,SND,PAIR]
      \\ fs[EVERY_MAP,EVERY_MEM]
      \\ fs[IN_DISJOINT,SUBSET_DEF,MEM_FLAT,PULL_EXISTS,MEM_MAP]
      \\ rpt(first_x_assum drule) \\ simp[]
      \\ fs[wfv_state_def,dec_clock_def]
      \\ ntac 4 strip_tac
      \\ conj_tac
      >- (
        match_mp_tac subg_trans
        \\ first_assum(part_match_exists_tac (last o strip_conj) o concl)
        \\ fs[] )
      \\ metis_tac[] )
    \\ strip_tac \\ fs[]
    \\ Cases_on`err` \\ fs[] \\ rveq \\ fs[]
    \\ imp_res_tac evaluate_SING \\ fs[] \\ rfs[]
    \\ first_x_assum drule \\ fs[]
    \\ simp[RIGHT_EXISTS_AND_THM,RIGHT_EXISTS_IMP_THM] )
  \\ qmatch_goalsub_rename_tac`aaa = _ ::_`
  \\ Cases_on`aaa` \\ fs[Abbr`c1`,Abbr`c2`]
  \\ simp[RIGHT_EXISTS_AND_THM,RIGHT_EXISTS_IMP_THM]
  \\ strip_tac
  \\ drule (GEN_ALL dest_closure_v_rel) \\ fs[PULL_EXISTS]
  \\ rpt (disch_then drule)
  \\ strip_tac
  \\ simp[evaluate_app_rw]
  \\ qpat_x_assum`_ = (res,_)`mp_tac
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ imp_res_tac evaluate_length_imp
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
  \\ rveq \\ strip_tac
  \\ rveq \\ fs[] \\ rfs[]
  \\ fs[PULL_EXISTS] \\ rfs[]
  \\ fs[recclosure_rel_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ qmatch_assum_rename_tac`v_rel g1 l1 f f'`
  \\ qmatch_assum_rename_tac`LIST_REL _ rest1 rest2`
  \\ first_x_assum(qspecl_then[`g1`,`l1`]mp_tac o CONV_RULE(RESORT_FORALL_CONV List.rev))
  \\ ((fn g as (asl,w) =>
      let
        val (fa,_) = dest_imp w
        val (_,b) = strip_forall fa
        val (tm,_) = dest_imp b
        val tms = find_terms (fn x => type_of x = bool andalso free_in x fa) tm
      in
        SUBGOAL_THEN (list_mk_conj tms) strip_assume_tac
      end g)
  >- (
    fs[code_locs_map,recclosure_wf_def]
    \\ imp_res_tac ALL_DISTINCT_FLAT_EVERY >>
    fs[Q.SPEC`MAP _ _`every_Fn_SOME_EVERY,
       Q.SPEC`MAP _ _`every_Fn_vs_NONE_EVERY,
       EVERY_MAP,EVERY_MEM,NOT_LESS_EQUAL]
    \\ `MEM (n,e) fns1` by metis_tac[MEM_EL]
    \\ fs[EVERY_MAP,EVERY_MEM]
    \\ fs[IN_DISJOINT,SUBSET_DEF,MEM_FLAT,PULL_EXISTS,MEM_MAP]
    \\ rpt(first_x_assum drule) \\ simp[]
    \\ fs[wfv_state_def,dec_clock_def] ))
  \\ simp[]
  \\ qmatch_asmsub_abbrev_tac`COND b`
  \\ imp_res_tac calls_length \\ fs[]
  \\ `env_rel (v_rel g1 l1) args args2 0 [(0, SND (EL i fns2))]`
  by (
    qhdtm_x_assum`env_rel`mp_tac
    \\ `n = FST (EL i fns2)`
    by ( Cases_on`b` \\ fs[calls_list_MAPi,EL_ZIP,EL_MAP] )
    \\ reverse IF_CASES_TAC \\ fs[]
    >- (
      strip_tac
      \\ match_mp_tac env_rel_DROP_args
      \\ simp[] \\ fs[] )
    \\ ONCE_REWRITE_TAC[ADD_COMM]
    \\ simp[GSYM DROP_DROP]
    \\ strip_tac \\ drule env_rel_DROP
    \\ impl_tac
    >- (
      simp[]
      \\ fs[LIST_REL_EL_EQN]
      \\ rfs[EL_TAKE,EL_DROP] )
    \\ strip_tac
    \\ match_mp_tac env_rel_DROP_args
    \\ simp[] \\ fs[]
    \\ fs[LIST_REL_EL_EQN]
    \\ rfs[EL_TAKE])
  \\ (reverse(Cases_on`b`) \\ fs[] \\ rveq
  >- (
    rveq \\ drule (GEN_ALL calls_el_sing)
    \\ disch_then (qspec_then`i`mp_tac)
    \\ impl_tac >- fs[wfg_def,recclosure_wf_def]
    \\ simp[EL_MAP] \\ strip_tac
    \\ disch_then drule
    \\ qmatch_goalsub_abbrev_tac`dec_clock dk s0`
    \\ disch_then(qspecl_then[`dec_clock dk t0`,`args2`]mp_tac)
    \\ impl_tac
    >- (
      fs[dec_clock_def]
      \\ conj_tac >- metis_tac[subg_trans]
      \\ fs[SUBSET_DEF])
    \\ strip_tac
    \\ imp_res_tac calls_length \\ fs[]
    \\ simp[EL_ZIP]
    \\ fs[dec_clock_def]
    \\ qpat_x_assum`_ ⇒ _`mp_tac
    \\ impl_tac
    >- (
      qhdtm_x_assum`env_rel`mp_tac
      \\ simp[EL_ZIP]
      \\ metis_tac[state_rel_with_clock,code_includes_subg,state_rel_def] )
    \\ strip_tac \\ fs[] \\ rveq
    \\ imp_res_tac state_rel_clock \\ fs[]
    \\ imp_res_tac state_rel_max_app \\ fs[]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs[]
    \\ rfs[EL_ZIP]
    \\ TRY (
        first_x_assum drule \\ fs[]
      \\ simp[RIGHT_EXISTS_AND_THM,RIGHT_EXISTS_IMP_THM,FORALL_AND_THM]
      \\ rpt(disch_then drule)
      \\ strip_tac
      \\ drule evaluate_add_clock \\ fs[]
      \\ disch_then(qspec_then`ck'`assume_tac)
      \\ qexists_tac`ck+ck'` \\ simp[] \\ rfs[] )
    \\ qexists_tac`ck` \\ simp[] \\ rfs[] ))
  \\ imp_res_tac state_rel_max_app \\ fs[]
  \\ REWRITE_TAC[calls_list_MAPi]
  \\ simp[]
  \\ simp[evaluate_def,evaluate_GENLIST_Var_tra]
  \\ simp[find_code_def]
  \\ `n ≤ LENGTH args2`
  by (
    qpat_x_assum`_ ≤ LENGTH args2`mp_tac
    \\ IF_CASES_TAC \\ fs[] )
  \\ simp[EVAL``(closSem$dec_clock _ _).code``]
  \\ qmatch_assum_abbrev_tac`subg gd g1`
  \\ `code_includes (SND gd) t0.code`
  by ( metis_tac[code_includes_subg,state_rel_def] )
  \\ pop_assum mp_tac
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
  \\ qpat_x_assum`calls _ _ = (es,_)`assume_tac
  \\ drule calls_replace_SND
  \\ disch_then(qspec_then`insert_each' (SND g1) loc (LENGTH fns1) g0`mp_tac)
  \\ simp[FST_insert_each']
  \\ drule calls_IS_SUFFIX
  \\ simp[IS_SUFFIX_APPEND]
  \\ strip_tac \\ simp[]
  \\ strip_tac
  \\ drule (GEN_ALL calls_el_sing)
  \\ disch_then(qspec_then`i`mp_tac)
  \\ (impl_tac
  >- (
    fs[MAP_FST_insert_each',recclosure_wf_def]
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
    \\ metis_tac[numTheory.INV_SUC,DECIDE``2 * i + SUC loc = SUC (2*i+loc)``,ADD1] ))
  \\ simp[EL_MAP]
  \\ strip_tac
  \\ first_x_assum drule
  \\ qmatch_goalsub_abbrev_tac`dec_clock dk s0`
  \\ qmatch_asmsub_abbrev_tac`(n,e)`
  \\ disch_then(qspecl_then[`dec_clock dk t0`,`TAKE n args2`]mp_tac)
  \\ (impl_tac >- (
    fs[dec_clock_def]
    \\ conj_tac >- (
      match_mp_tac subg_trans \\ asm_exists_tac \\ fs []
      \\ match_mp_tac subg_trans \\ once_rewrite_tac [CONJ_COMM]
      \\ asm_exists_tac \\ fs []
      \\ unabbrev_all_tac
      \\ match_mp_tac subg_insert_each' \\ fs []
      \\ imp_res_tac calls_length \\ fs []
      \\ asm_exists_tac \\ fs []
      \\ conj_tac
      >- (
        fs[wfg_def]
        \\ qpat_x_assum`_ = IMAGE SUC (domain (FST g0))`(assume_tac o SYM)
        \\ fs[]
        \\ fs[IN_DISJOINT,MEM_GENLIST,MEM_MAP] )
      \\ conj_tac
      >- (
        `ALL_DISTINCT (MAP FST (SND new_g))`
        by (
          match_mp_tac calls_ALL_DISTINCT
          \\ asm_exists_tac \\ fs[]
          \\ fs[wfg_def,ALL_DISTINCT_APPEND,recclosure_wf_def])
        \\ rfs[ALL_DISTINCT_APPEND,wfg_def]
        \\ simp[IN_DISJOINT]
        \\ metis_tac[] )
      \\ qpat_x_assum`subg _ g1` mp_tac
      \\ rw[subg_def,SND_code_list_ZIP]
      \\ first_x_assum match_mp_tac
      \\ simp[ALOOKUP_APPEND]
      \\ BasicProvers.CASE_TAC
      >- (
        rfs[REVERSE_ZIP,ALOOKUP_ZIP_FAIL,MEM_GENLIST]
        \\ metis_tac[ADD_ASSOC,ADD_COMM] )
      \\ CONV_TAC(REWR_CONV(GSYM SOME_11))
      \\ pop_assum (SUBST_ALL_TAC o SYM)
      \\ match_mp_tac ALOOKUP_ALL_DISTINCT_MEM
      \\ simp[MAP_REVERSE,MAP_ZIP,ALL_DISTINCT_GENLIST]
      \\ simp[MEM_ZIP]
      \\ asm_exists_tac \\ simp[EL_ZIP,EL_MAP] )
    \\ fs[SUBSET_DEF] ))
  \\ simp[RIGHT_EXISTS_AND_THM,RIGHT_EXISTS_IMP_THM]
  \\ strip_tac \\ pop_assum mp_tac
  \\ (impl_tac >- (
    rfs[wfg_def,EL_ZIP]
    \\ conj_tac >- (
      `∀v. has_var v (SND (free [EL i es])) ⇒ v < n`
      by (
        fs[markerTheory.Abbrev_def,LIST_REL_EL_EQN]
        \\ first_x_assum(qspec_then`i`mp_tac) \\ simp[] )
      \\ qspec_then`[EL i es]`mp_tac free_thm
      \\ simp[] \\ pairarg_tac \\  fs[] \\ strip_tac
      \\ fs[env_rel_def]
      \\ imp_res_tac LIST_REL_LENGTH
      \\ IF_CASES_TAC
      >- ( every_case_tac \\ fs[TAKE_LENGTH_ID_rwt] )
      \\ ntac 2 strip_tac
      \\ res_tac
      \\ simp[EL_TAKE]
      \\ Cases_on`LENGTH args = LENGTH args2` >- fs[LIST_REL_EL_EQN]
      \\ fs[]
      \\ qmatch_asmsub_rename_tac`is_Recclosure v1`
      \\ reverse(Cases_on`is_Recclosure v1`\\fs[])
      >- fs[LIST_REL_EL_EQN,EL_TAKE]
      \\ rfs[LIST_REL_EL_EQN] \\ fs[EL_TAKE]
      \\ last_x_assum match_mp_tac
      \\ res_tac \\ simp[] )
    \\ imp_res_tac state_rel_clock
    \\ fs[dec_clock_def]
    \\ conj_tac
    >- ( match_mp_tac state_rel_with_clock \\ fs[] )
    \\ qpat_x_assum `code_includes _ _` mp_tac
    \\ match_mp_tac code_includes_subg
    \\ match_mp_tac subg_trans
    \\ asm_exists_tac \\ fs []
    \\ unabbrev_all_tac
    \\ match_mp_tac subg_insert_each' \\ fs []
    \\ imp_res_tac calls_length \\ fs []
    \\ asm_exists_tac \\ fs []
    \\ conj_asm1_tac >- fs[wfg_def]
    \\ conj_tac
    >- (
      `ALL_DISTINCT (MAP FST (SND new_g))`
      by (
        match_mp_tac calls_ALL_DISTINCT
        \\ asm_exists_tac \\ fs[]
        \\ fs[wfg_def,ALL_DISTINCT_APPEND,recclosure_wf_def])
      \\ rfs[ALL_DISTINCT_APPEND,wfg_def]
      \\ simp[IN_DISJOINT]
      \\ metis_tac[] )
    \\ qpat_x_assum`subg _ g1` mp_tac
    \\ rw[subg_def,SND_code_list_ZIP]
    \\ first_x_assum match_mp_tac
    \\ simp[ALOOKUP_APPEND]
    \\ BasicProvers.CASE_TAC
    >- (
      rfs[REVERSE_ZIP,ALOOKUP_ZIP_FAIL,MEM_GENLIST]
      \\ metis_tac[ADD_ASSOC,ADD_COMM] )
    \\ CONV_TAC(REWR_CONV(GSYM SOME_11))
    \\ pop_assum (SUBST_ALL_TAC o SYM)
    \\ match_mp_tac ALOOKUP_ALL_DISTINCT_MEM
    \\ simp[MAP_REVERSE,MAP_ZIP,ALL_DISTINCT_GENLIST]
    \\ simp[MEM_ZIP]
    \\ asm_exists_tac \\ simp[EL_ZIP,EL_MAP]))
  \\ fs[dec_clock_def]
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`_:num < dk'`
  \\ `dk' = dk`
  by (
    unabbrev_all_tac
    \\ imp_res_tac LIST_REL_LENGTH
    \\ simp[] )
  \\ qunabbrev_tac`dk'` \\ fs[]
  \\ imp_res_tac state_rel_clock
  \\ `∀ck. ¬(SUC ck + t0.clock ≤ dk)` by simp[]
  \\ TRY (
    qmatch_asmsub_rename_tac`Rerr err`
    \\ Cases_on`err = Rabort Rtimeout_error`
    >- ( fs[] \\ qexists_tac`SUC ck` \\ simp[ADD1] \\ rfs[] )
    \\ drule evaluate_add_clock \\ fs []
    \\ disch_then (qspec_then `1` assume_tac)
    \\ qexists_tac `SUC ck` \\ simp[ADD1] \\ rfs[] )
  \\ first_x_assum drule
  \\ rpt (disch_then drule)
  \\ simp[RIGHT_EXISTS_AND_THM,RIGHT_EXISTS_IMP_THM]
  \\ rpt (disch_then drule)
  \\ strip_tac
  \\ drule evaluate_add_clock \\ fs[]
  \\ disch_then(qspec_then`ck'`assume_tac)
  \\ qexists_tac`ck+ck'+1` \\ simp[]);

val code_locs_calls_list = Q.prove(`
  ∀ls n tr i. code_locs (MAP SND (calls_list tr i n ls)) = []`,
  Induct>>fs[calls_list_def,FORALL_PROD,Once code_locs_cons]>>
  rw[Once code_locs_def])

val code_locs_code_list_MEM = Q.prove(`
  ∀ls n rest x.
  MEM x (code_locs (MAP (SND o SND) (SND (code_list n ls rest)))) ⇔
  MEM x (code_locs (MAP (SND o SND) (SND rest)++MAP SND ls))`,
  Induct>>fs[code_list_def,FORALL_PROD,Once code_locs_cons,code_locs_append]>>
  rw[]>>EVAL_TAC>>
  rw[EQ_IMP_THM]>>
  fs[Once code_locs_cons,code_locs_def])

val code_locs_code_list_ALL_DISTINCT = Q.prove(`
  ∀ls n rest.
  ALL_DISTINCT (code_locs (MAP (SND o SND) (SND (code_list n ls rest)))) ⇔
  ALL_DISTINCT (code_locs (MAP (SND o SND) (SND rest)++MAP SND ls))`,
  Induct>>fs[code_list_def,FORALL_PROD,Once code_locs_cons,code_locs_append]>>
  rw[]>>EVAL_TAC>>
  fs[ALL_DISTINCT_APPEND]>>
  rw[EQ_IMP_THM]>>
  fs[Once code_locs_cons,ALL_DISTINCT_APPEND,code_locs_def]>>
  metis_tac[])

(* All code_locs come from the original code,
   and therefore, are all even
*)
val calls_code_locs_MEM = Q.store_thm("calls_code_locs_MEM",
  `∀xs g0 ys g. calls xs g0 = (ys,g) ⇒
   ∀x.
    (MEM x (code_locs ys) ∨
    MEM x (code_locs (MAP (SND o SND) (SND g)))) ⇒
    (MEM x (code_locs xs) ∨
    MEM x (code_locs (MAP (SND o SND) (SND g0))))`,
  ho_match_mp_tac calls_ind>>rw[]>>
  fs[calls_def,code_locs_def]>>
  rpt(pairarg_tac>>fs[])>>
  rpt var_eq_tac>>fs[code_locs_def,code_locs_append]>>
  imp_res_tac calls_sing>>fs[]>>
  TRY(metis_tac[])>>
  qpat_x_assum`A=(ys,g)` mp_tac>> rpt(IF_CASES_TAC>>fs[])>>
  rw[]>>rpt(var_eq_tac)>>
  fs[code_locs_def,code_locs_append,Once code_locs_cons,code_locs_calls_list]>>
  TRY(metis_tac[])>>
  fs[code_locs_append,code_locs_code_list_MEM]>>
  imp_res_tac calls_length>>fs[MAP_ZIP]>>
  metis_tac[]);

(* the all distinctness of code_locs is preserved *)
val calls_code_locs_ALL_DISTINCT = Q.store_thm("calls_code_locs_ALL_DISTINCT",
  `∀xs g0 ys g. calls xs g0 = (ys,g) ⇒
    ALL_DISTINCT (code_locs xs ++ code_locs (MAP (SND o SND) (SND g0))) ⇒
    ALL_DISTINCT (code_locs ys ++ code_locs (MAP (SND o SND) (SND g)))`,
  ho_match_mp_tac calls_ind>>
  rw[calls_def,code_locs_def]>>
  EVAL_TAC>>fs[]>>
  rpt(pairarg_tac>>fs[])>>
  rpt var_eq_tac>>
  fs[code_locs_append,ALL_DISTINCT_APPEND,code_locs_def]>>
  imp_res_tac calls_sing>>fs[]>>
  imp_res_tac calls_code_locs_MEM>>
  fs[]>>TRY(metis_tac[])>>
  qpat_x_assum`A=(ys,g)` mp_tac>> rpt(IF_CASES_TAC>>fs[])>>
  rw[]>>rpt(var_eq_tac)>>
  fs[code_locs_def,code_locs_append,Once code_locs_cons,code_locs_calls_list,ALL_DISTINCT_APPEND,code_locs_code_list_ALL_DISTINCT,code_locs_code_list_MEM]>>
  imp_res_tac calls_length>>fs[MAP_ZIP]>>
  rw[]>>
  metis_tac[]);

(*
val opt_init_state_rel_def = Define`
  opt_init_state_rel do_call s t ⇔
    if do_call then
      state_rel (LN,[]) {} s t ∧
      wfv_state (LN,[]) {} s
    else t = s`;

val opt_state_rel_def = Define`
  opt_state_rel do_call s t ⇔
    if do_call then
      ∃g1 l1. state_rel g1 l1 s t
    else t = s`;

val opt_result_rel_def = Define`
  opt_result_rel do_call r1 r2 ⇔
    if do_call then
      ∃g1 l1. result_rel (LIST_REL (v_rel g1 l1)) (v_rel g1 l1) r1 r2
    else r2 = r1`;
*)

(*
val compile_correct = Q.store_thm("compile_correct",
  `∀b e1 s1 s2 r1 t1 e2 code.
    evaluate (e1,[],s1) = (r1,t1) ∧
    r1 ≠ Rerr (Rabort Rtype_error) ∧
    every_Fn_SOME e1 ∧ every_Fn_vs_NONE e1 ∧
    ALL_DISTINCT (code_locs e1) ∧
    opt_init_state_rel b s1 s2 ∧
    compile b e1 = (e2,code) ∧
    code_includes code s2.code
    ⇒
    ∃ck r2 t2 g1 l1.
    evaluate (e2,[],s2 with clock := ck + s2.clock) = (r2,t2) ∧
    opt_result_rel b r1 r2 ∧
    opt_state_rel b t1 t2`,
  Cases \\ rw[compile_def,opt_state_rel_def,opt_init_state_rel_def,opt_result_rel_def] \\ rw[]
  \\ TRY (qexists_tac`0` \\ simp[] \\ NO_TAC)
  \\ pairarg_tac \\ fs[]
  \\ drule (CONJUNCT1 calls_correct |> SIMP_RULE (srw_ss())[])
  \\ simp[] \\ disch_then drule
  \\ disch_then(qspec_then`[]`mp_tac)
  \\ simp[env_rel_def]
  \\ simp[Once wfg_def]
  \\ qmatch_goalsub_abbrev_tac`l1 ⊆ _`
  \\ disch_then(qspecl_then[`s2`,`l1`,`g`]mp_tac)
  \\ `subg (LN,[]) g`
  by (
    match_mp_tac calls_subg
    \\ asm_exists_tac \\ fs[] )
  \\ impl_tac
  >- (
    simp[]
    \\ `wfg g`
    by (
      match_mp_tac calls_wfg
      \\ asm_exists_tac \\ fs[]
      \\ fs[wfg_def] )
    \\ fs[]
    \\ conj_tac
    >- (
      fs[wfv_state_def,EVERY_MEM,FEVERY_ALL_FLOOKUP]
      \\ conj_tac \\ (gen_tac \\ Cases ORELSE Cases) \\ fs[]
      \\ rw[] \\ first_x_assum drule \\ fs[EVERY_MEM] \\ rw[]
      \\ TRY (first_x_assum drule \\ rw[])
      \\ match_mp_tac wfv_subg \\ asm_exists_tac \\ fs[])
    \\ conj_tac
    >- (
      match_mp_tac subg_refl
      \\ fs[wfg_def] )
    \\ simp[Abbr`l1`,IN_DISJOINT]
    \\ metis_tac[] )
  \\ strip_tac \\ rfs[]
  \\ `state_rel g l1 s1 s2`
  by (
    match_mp_tac (GEN_ALL state_rel_subg)
    \\ asm_exists_tac \\ fs[]
    \\ asm_exists_tac \\ fs[] )
  \\ fs[]
  \\ asm_exists_tac \\ fs[]
  \\ metis_tac[]);
*)

val semantics_calls = Q.store_thm("semantics_calls",
  `semantics (ffi:'ffi ffi_state) max_app FEMPTY co cc x <> Fail ==>
   compile T x = (y,aux) /\ every_Fn_SOME x ∧ every_Fn_vs_NONE x /\
   ALL_DISTINCT (code_locs x) /\
   code_inv FEMPTY cc co (FEMPTY |++ aux) cc1 co1 ==>
   semantics (ffi:'ffi ffi_state) max_app (FEMPTY |++ aux) co1 cc1 y =
   semantics (ffi:'ffi ffi_state) max_app FEMPTY co cc x`,
  strip_tac
  \\ ho_match_mp_tac IMP_semantics_eq
  \\ fs [] \\ fs [eval_sim_def] \\ rw []
  \\ fs [compile_def]
  \\ rveq \\ fs [FUPDATE_LIST]
  \\ pairarg_tac \\ fs [] \\ rveq \\ fs []
  \\ drule (calls_correct |> SIMP_RULE std_ss [] |> CONJUNCT1)
  \\ rpt (disch_then drule) \\ fs [EVAL ``wfg (LN,[])``]
  \\ disch_then (qspecl_then [`[]`,
      `initial_state ffi max_app (FOLDL $|+ FEMPTY (SND g)) co1 cc1 k`,
      `set (code_locs x) DIFF domain (FST g)`,`g`] mp_tac)
  \\ simp []
  \\ `wfg g` by
   (match_mp_tac calls_wfg
    \\ asm_exists_tac \\ fs []
    \\ EVAL_TAC \\ fs [])
  \\ impl_tac THEN1
   (fs [subg_def] \\ reverse (rpt conj_tac)
    THEN1 (fs [IN_DISJOINT,IN_DIFF] \\ metis_tac [])
    THEN1 (match_mp_tac calls_ALL_DISTINCT
           \\ asm_exists_tac \\ fs [])
    \\ fs [wfv_state_def,initial_state_def,FEVERY_DEF,code_inv_def])
  \\ strip_tac
  \\ pop_assum mp_tac \\ impl_tac
  THEN1
   (fs [env_rel_def,state_rel_def,initial_state_def,code_includes_def]
    \\ full_simp_tac std_ss [GSYM FUPDATE_LIST]
    \\ rpt strip_tac
    \\ match_mp_tac mem_to_flookup
    \\ fs [ALOOKUP_MEM]
    \\ match_mp_tac calls_ALL_DISTINCT
    \\ asm_exists_tac \\ fs [])
  \\ qmatch_goalsub_abbrev_tac `(y,[],s4)`
  \\ strip_tac
  \\ qexists_tac `ck` \\ fs []
  \\ qmatch_goalsub_abbrev_tac `(y,[],s5)`
  \\ `s4 = s5` by (unabbrev_all_tac \\ fs [initial_state_def])
  \\ rveq \\ fs []
  \\ fs [state_rel_def]
  \\ Cases_on `res1` \\ fs []
  \\ Cases_on `e` \\ fs []);

val semantics_compile = Q.store_thm("semantics_compile",
  `semantics ffi max_app FEMPTY co cc x ≠ Fail ∧
   compile do_call x = (y,aux) ∧
   (if do_call then
    syntax_ok x ∧
    code_inv FEMPTY cc co (FEMPTY |++ aux) cc1 co1
    else cc = state_cc (CURRY I) cc1 ∧
         co1 = state_co (CURRY I) co) ⇒
   semantics ffi max_app (FEMPTY |++ aux) co1 cc1 y
   =
   semantics ffi max_app FEMPTY co cc x`,
  reverse(Cases_on`do_call`)
  \\ rw[compile_def]
  \\ fs[FUPDATE_LIST_THM]
  >- ( match_mp_tac semantics_CURRY_I \\ fs[] )
  \\ irule semantics_calls
  \\ fs[compile_def, syntax_ok_def]);

(* Preservation of some label properties
  every_Fn_SOME xs ∧ every_Fn_vs_NONE xs
*)
val every_Fn_GENLIST_Var = Q.store_thm("every_Fn_GENLIST_Var",
  `∀n i t. every_Fn_SOME (GENLIST_Var t i n) ∧
       every_Fn_vs_NONE (GENLIST_Var t i n)`,
  Induct \\ rw[] \\ rw[Once GENLIST_Var_def] \\
  simp[Once every_Fn_vs_NONE_EVERY,Once every_Fn_SOME_EVERY,EVERY_SNOC]
  \\ simp[GSYM every_Fn_vs_NONE_EVERY,GSYM every_Fn_SOME_EVERY]);

val every_Fn_calls_list = Q.store_thm("every_Fn_calls_list",
  `∀ls n i t. every_Fn_SOME (MAP SND (calls_list t i n ls)) ∧
         every_Fn_vs_NONE (MAP SND (calls_list t i n ls))`,
  Induct>>fs[calls_list_def,FORALL_PROD]>>
  simp[Once every_Fn_vs_NONE_EVERY,Once every_Fn_SOME_EVERY,EVERY_SNOC,every_Fn_GENLIST_Var] \\
  simp[GSYM every_Fn_vs_NONE_EVERY,GSYM every_Fn_SOME_EVERY])

val every_Fn_code_list = Q.store_thm("every_Fn_code_list",
  `∀ls n rest.
  (every_Fn_SOME (MAP (SND o SND) (SND (code_list n ls rest))) ⇔
  every_Fn_SOME (MAP SND ls) ∧
  every_Fn_SOME (MAP (SND o SND) (SND rest))) ∧
  (every_Fn_vs_NONE (MAP (SND o SND) (SND (code_list n ls rest))) ⇔
  every_Fn_vs_NONE (MAP SND ls) ∧
  every_Fn_vs_NONE (MAP (SND o SND) (SND rest)))`,
  Induct>>fs[code_list_def,FORALL_PROD]>>
  rw[EQ_IMP_THM]>>fs[Once every_Fn_SOME_EVERY,Once every_Fn_vs_NONE_EVERY])

val calls_preserves_every_Fn_SOME = Q.store_thm("calls_preserves_every_Fn_SOME",
  `∀xs g0 ys g. calls xs g0 = (ys,g) ⇒
    every_Fn_SOME xs ∧ every_Fn_SOME (MAP (SND o SND) (SND g0)) ⇒
    every_Fn_SOME ys ∧ every_Fn_SOME (MAP (SND o SND) (SND g))`,
  ho_match_mp_tac calls_ind>>
  (* There is a bad automatic rewrite somewhere *)
  rpt strip_tac>>
  fs[calls_def]>>
  rpt (pairarg_tac>>fs[])>>
  TRY(qpat_x_assum`A=(ys,g)` mp_tac>> every_case_tac>>fs[]>>strip_tac)>>
  rveq>>simp[]>>
  imp_res_tac calls_sing>>fs[every_Fn_GENLIST_Var,every_Fn_code_list,every_Fn_calls_list]>>
  simp[Once every_Fn_SOME_EVERY]>>
  simp[GSYM every_Fn_SOME_EVERY]>>
  imp_res_tac calls_length>>
  fs[MAP_ZIP]);

val calls_preserves_every_Fn_vs_NONE = Q.store_thm("calls_preserves_every_Fn_vs_NONE",
  `∀xs g0 ys g. calls xs g0 = (ys,g) ⇒
    every_Fn_vs_NONE xs ∧ every_Fn_vs_NONE (MAP (SND o SND) (SND g0)) ⇒
    every_Fn_vs_NONE ys ∧ every_Fn_vs_NONE (MAP (SND o SND) (SND g))`,
  ho_match_mp_tac calls_ind>>
  (* There is a bad automatic rewrite somewhere *)
  rpt strip_tac>>
  fs[calls_def]>>
  rpt (pairarg_tac>>fs[])>>
  TRY(qpat_x_assum`A=(ys,g)` mp_tac>> every_case_tac>>fs[]>>strip_tac)>>
  rveq>>simp[]>>
  imp_res_tac calls_sing>>fs[every_Fn_GENLIST_Var,every_Fn_code_list,every_Fn_calls_list]>>
  simp[Once every_Fn_vs_NONE_EVERY]>>
  simp[GSYM every_Fn_vs_NONE_EVERY]>>
  imp_res_tac calls_length>>
  fs[MAP_ZIP]);

(*
val tm = ``closLang$Let [Op (Const 0) []; Op (Const 0) []]
             (App NONE (Fn (SOME 1) NONE 1 (Fn (SOME 2) NONE 1 (Op (Const 1) []))) [Op (Const 2) []])``
val res1 = EVAL``evaluate ([^tm],[],<|clock := 1|>)``
val (ctm,ctab) = EVAL``clos_call$compile T ^tm`` |> concl |> rhs |> dest_pair
val res2 = EVAL``evaluate ([^ctm],[],<|clock := 2; code := (alist_to_fmap ^ctab)|>)``

val tm2 = ``closLang$Let [Op (Const 0) []; Op (Const 0) []]
             (Fn (SOME 1) NONE 1 (App NONE (Fn (SOME 2) NONE 1 (Op (Const 1) [])) [Op (Const 2) []]))``
val res3 = EVAL``evaluate ([^tm2],[],<|clock := 1|>)``
val (ctm2,ctab2) = EVAL``clos_call$compile T ^tm2`` |> concl |> rhs |> dest_pair
val res4 = EVAL``evaluate ([^ctm2],[],<|clock := 2; code := (alist_to_fmap ^ctab2)|>)``
*)

val _ = export_theory();
