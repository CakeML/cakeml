(*
  Correctness proof for clos_call
*)

open preamble backendPropsTheory match_goal
     closSemTheory closPropsTheory
     clos_callTheory db_varsTheory

val _ = new_theory"clos_callProof";

(* TODO These are the same. Put in closLang? *)
val _ = temp_bring_to_front_overload "free" {Name="free", Thy="clos_call"};
val _ = temp_bring_to_front_overload "closed" {Name="closed", Thy="clos_call"};
val _ = temp_bring_to_front_overload "compile" {Name="compile", Thy="clos_call"};

val _ = temp_bring_to_front_overload"lookup"{Name="lookup",Thy="sptree"};
val _ = temp_bring_to_front_overload"insert"{Name="insert",Thy="sptree"};
val _ = temp_bring_to_front_overload"delete"{Name="delete",Thy="sptree"};
val _ = temp_bring_to_front_overload"map"{Name="map",Thy="sptree"};
val _ = temp_bring_to_front_overload"wf"{Name="wf",Thy="sptree"};

(* TODO: move *)

val PUSH_EXISTS_IMP = SPEC_ALL RIGHT_EXISTS_IMP_THM;

val v_size_lemma = Q.prove(
  `MEM (v:closSem$v) vl ⇒ v_size v < v1_size vl`,
  Induct_on `vl` >> dsimp[v_size_def] >> rpt strip_tac >>
  res_tac >> simp[]);

Theorem code_locs_GENLIST_Var[simp]:
   ∀n t i. code_locs (GENLIST_Var t i n) = []
Proof
  Induct \\ simp[code_locs_def,Once GENLIST_Var_def,code_locs_append]
QED

Theorem fv_GENLIST_Var_tra:
   ∀n tra i. fv v (GENLIST_Var tra i n) ⇔ v < n
Proof
  Induct \\ simp[fv_def,Once GENLIST_Var_def,SNOC_APPEND]
QED

Theorem evaluate_GENLIST_Var_tra:
   ∀n tr i.
   evaluate (GENLIST_Var tr i n,env,s) =
   if n ≤ LENGTH env then (Rval (TAKE n env),s)
   else (Rerr (Rabort Rtype_error),s)
Proof
  Induct \\ rw[Once GENLIST_Var_def,evaluate_def,evaluate_append] \\
  simp[TAKE_EL_SNOC,ADD1]
QED

val evaluate_add_clock =
  evaluate_add_to_clock
  |> SIMP_RULE (srw_ss()) []
  |> CONJUNCT1 |> GEN_ALL
  |> REWRITE_RULE[GSYM AND_IMP_INTRO]

val is_Recclosure_def = Define`
  is_Recclosure (Recclosure _ _ _ _ _) = T ∧
  is_Recclosure _ = F`;
val _ = export_rewrites["is_Recclosure_def"];

val every_refv_def = Define
  `(every_refv P (ValueArray vs) ⇔ EVERY P vs) ∧
   (every_refv P _ ⇔ T)`
val _ = export_rewrites["every_refv_def"];

val IMP_EXISTS_IFF = Q.prove(
  `!xs. (!x. MEM x xs ==> (P x <=> Q x)) ==>
         (EXISTS P xs <=> EXISTS Q xs)`,
  Induct \\ fs []);

(* -- *)

(* correctness of free *)

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

Theorem subg_refl:
   ∀g. ALL_DISTINCT (MAP FST (SND g)) ⇒ subg g g
Proof
  rw[subg_def]
QED

Theorem subg_trans:
   ∀g1 g2 g3. subg g1 g2 ∧ subg g2 g3 ⇒ subg g1 g3
Proof
  rw[subg_def] \\ metis_tac[subspt_trans,IS_SUFFIX_TRANS]
QED

val wfg'_def = Define`
  wfg' g ⇔
    set (MAP FST (SND g)) ⊆ IMAGE SUC (domain (FST g))`;

val wfg_def = Define`
  wfg g ⇔
    set (MAP FST (SND g)) = IMAGE SUC (domain (FST g)) ∧
    ALL_DISTINCT (MAP FST (SND g))`;

val make_g_def = Define `
  make_g d code =
    if IMAGE SUC (domain d) ⊆ (FDOM code) then
      SOME (d, MAP (\k. (FST k + 1, THE (FLOOKUP code (FST k + 1)))) (toAList d))
    else NONE`;

val ALL_DISTINCT_MAP_FST_ADD1 = prove(
  ``!xs. ALL_DISTINCT (MAP (λk. FST k + 1n) xs) =
         ALL_DISTINCT (MAP FST xs)``,
  Induct \\ fs [MEM_MAP]);

Theorem make_g_wfg:
   make_g d code = SOME g ==> wfg g
Proof
  rw [make_g_def,wfg_def] \\ fs [MAP_MAP_o,o_DEF]
  \\ fs [ALL_DISTINCT_MAP_FST_ADD1,ALL_DISTINCT_MAP_FST_toAList]
  \\ fs [EXTENSION,MEM_MAP,ADD1,EXISTS_PROD,MEM_toAList,domain_lookup]
  \\ fs [PULL_EXISTS]
QED

Theorem make_g_subg:
   make_g cfg (FEMPTY |++ aux) = SOME new /\ wfg (cfg,aux) ==>
    subg (cfg,aux) new
Proof
  rw [] \\ imp_res_tac make_g_wfg \\ fs [wfg_def,subg_def]
  \\ fs [make_g_def] \\ rveq \\ fs [FDOM_FUPDATE_LIST]
  \\ rw[]
  \\ match_mp_tac ALOOKUP_ALL_DISTINCT_MEM \\ fs[]
  \\ last_assum(mp_then Any mp_tac FUPDATE_LIST_ALL_DISTINCT_REVERSE)
  \\ disch_then(qspec_then`FEMPTY`(SUBST1_TAC o SYM))
  \\ drule (GEN_ALL FLOOKUP_FUPDATE_LIST_ALOOKUP_SOME)
  \\ disch_then(qspec_then`FEMPTY`mp_tac) \\ strip_tac
  \\ fs[MEM_MAP, PULL_EXISTS, MEM_toAList, EXISTS_PROD]
  \\ imp_res_tac ALOOKUP_MEM
  \\ fsrw_tac[DNF_ss][EXTENSION, MEM_MAP, PULL_EXISTS, EXISTS_PROD, EQ_IMP_THM]
  \\ res_tac \\ fs[ADD1, domain_lookup]
QED

Theorem make_g_make_g_eq:
   !x1 x2 y1 y2 g0 g1.
      FST g0 = FST g1 /\ subg g0 g1 /\
      make_g x1 x2 = SOME g0 /\ make_g y1 y2 = SOME g1 ==> g0 = g1
Proof
  fs [make_g_def,subg_def] \\ rw [MAP_EQ_f]
  \\ rename [`MEM kk _`]
  \\ PairCases_on `kk`
  \\ `lookup kk0 x1 = SOME kk1` by fs [MEM_toAList]
  \\ fs [MEM_SPLIT] \\ fs []
  \\ full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ fs [ALOOKUP_APPEND,ALL_DISTINCT_APPEND,ALL_DISTINCT]
  \\ first_x_assum (qspec_then `kk0+1` mp_tac)
  \\ fs [] \\ rw [] \\ fs [GSYM ALOOKUP_NONE]
  \\ first_x_assum (qspec_then `kk0+1` mp_tac) \\ fs []
  \\ fs [option_case_eq] \\ strip_tac
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ pop_assum match_mp_tac \\ fs []
  \\ Cases_on `ALOOKUP (MAP (λk.
       (FST k + 1,THE (FLOOKUP x2 (FST k + 1)))) l1) (kk0 + 1)` \\ fs []
  \\ imp_res_tac ALOOKUP_MEM \\ fs [MEM_MAP]
QED

Theorem make_g_IMP_subg:
   make_g (r0:num_set) code = SOME g0 /\
    DISJOINT (FDOM code) (set (MAP FST progs1)) /\
    ALL_DISTINCT (MAP FST progs1) /\
    make_g r1 (code |++ progs1) = SOME g1 /\ subspt r0 r1 /\
    set (MAP FST progs1) SUBSET IMAGE SUC (domain r1) ==>
    subg (r1,progs1 ⧺ SND g0) g1
Proof
  rw [] \\ imp_res_tac make_g_wfg
  \\ fs [make_g_def] \\ rveq \\ fs [] \\ fs [subg_def,wfg_def]
  \\ fs [ALOOKUP_APPEND,option_case_eq]
  \\ strip_tac \\ Cases_on `ALOOKUP progs1 k` \\ fs [] THEN1
   (fs [GSYM MEM_ALOOKUP] \\ fs [MEM_MAP,EXISTS_PROD,MEM_toAList]
    \\ rw [] \\ fs []
    \\ imp_res_tac subspt_lookup \\ fs [FLOOKUP_FUPDATE_LIST_ALOOKUP_NONE]
    \\ `ALOOKUP (REVERSE progs1) (p_1 + 1) = NONE` by
          fs [ALOOKUP_NONE,MAP_REVERSE,MEM_REVERSE]
    \\ drule (GEN_ALL FLOOKUP_FUPDATE_LIST_ALOOKUP_NONE) \\ fs [])
  \\ drule (GEN_ALL FLOOKUP_FUPDATE_LIST_ALOOKUP_SOME)
  \\ disch_then(qspec_then`code`mp_tac) \\ strip_tac
  \\ fs [GSYM MEM_ALOOKUP]
  \\ fs [MEM_MAP,EXISTS_PROD]
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs [SUBSET_DEF,MEM_MAP,FORALL_PROD,PULL_EXISTS,ADD1]
  \\ first_x_assum drule \\ strip_tac
  \\ fs [domain_lookup,MEM_toAList]
  \\ fs [flookup_update_list_some]
  \\ rfs [alookup_distinct_reverse]
  \\ rveq \\ fs [flookup_fupdate_list]
  \\ fs [alookup_distinct_reverse]
QED

val recclosure_wf_def = Define`
  recclosure_wf loc fns ⇔
    every_Fn_SOME (MAP SND fns) ∧
    every_Fn_vs_NONE (MAP SND fns) ∧
    DISJOINT (set (GENLIST (λi. 2 * i + loc) (LENGTH fns))) (set (code_locs (MAP SND fns))) ∧
    ALL_DISTINCT (code_locs (MAP SND fns))`;

val code_includes_def = Define`
  code_includes al code ⇔
    ∀k v. ALOOKUP al k = SOME v ⇒ FLOOKUP code k = SOME v`;

val recclosure_rel_def = Define`
  recclosure_rel g l code loc fns1 fns2 ⇔ ∃g0.
     recclosure_wf loc fns1 ∧
     wfg g0 ∧
     DISJOINT (IMAGE SUC (set (code_locs (MAP SND fns1)))) (set (MAP FST (SND g0))) ∧
     DISJOINT (set (GENLIST (λi. 2*i+loc+1) (LENGTH fns1))) (set (MAP FST (SND g0))) ∧
     let (es,new_g) = calls (MAP SND fns1) (insert_each loc (LENGTH fns1) g0) in
     if EVERY2 (λ(n,_) p. ∀v. has_var v (SND (free [p])) ⇒ v < n) fns1 es
     then
       (∃tra n. fns2 = calls_list tra n loc fns1) ∧
       subg (code_list loc (ZIP (MAP FST fns1,es)) new_g) g ∧
       set (code_locs (MAP SND fns1)) DIFF domain (FST new_g) ⊆ l ∧
       code_includes (SND (code_list loc (ZIP (MAP FST fns1,es)) new_g)) code
     else
       let (es,new_g) = calls (MAP SND fns1) g0 in
       fns2 = ZIP (MAP FST fns1, es) ∧
       subg new_g g ∧
       set (code_locs (MAP SND fns1)) DIFF domain (FST new_g) ⊆ l ∧
       set (GENLIST (λi. 2*i+loc) (LENGTH fns1)) ⊆ l ∧
       code_includes (SND new_g) code`;

val env_rel_def = Define`
  env_rel R env1 env2 a es ⇔
    if LENGTH env1 = LENGTH env2 then LIST_REL R env1 env2 else
    ∀x. EXISTS (λ(n,p). fv1 (n+a+x) p) es ⇒
        x < LENGTH env1 ∧ x < LENGTH env2 ∧
        R (EL x env1) (EL x env2)`;

Theorem env_rel_mono[mono]:
   (∀x y. MEM x env1 ∧ MEM y env2 ∧ R x y ⇒ R' x y) ⇒
   env_rel R env1 env2 a es ⇒
   env_rel R' env1 env2 a es
Proof
  rw[env_rel_def,MEM_EL,PULL_EXISTS,LIST_REL_EL_EQN]
QED

Theorem env_rel_cong[defncong]:
   (∀x y. MEM x env1 ∧ MEM y env2 ⇒ (R x y ⇔ R' x y))
   ⇒ env_rel R env1 env2 a es = env_rel R' env1 env2 a es
Proof
  rw[env_rel_def,MEM_EL,PULL_EXISTS,EQ_IMP_THM,LIST_REL_EL_EQN]
QED

val v_rel_def = tDefine"v_rel"`
  (v_rel g l code (Number i) v ⇔ v = Number i) ∧
  (v_rel g l code (Word64 w) v ⇔ v = Word64 w) ∧
  (v_rel g l code (Block n vs) v ⇔
    ∃vs'. v = Block n vs' ∧ LIST_REL (v_rel g l code) vs vs') ∧
  (v_rel g l code (ByteVector ws) v ⇔ v = ByteVector ws) ∧
  (v_rel g l code (RefPtr n) v ⇔ v = RefPtr n) ∧
  (v_rel g l code (Closure loco vs1 env1 n bod1) v ⇔
     ∃loc vs2 env2 bod2.
       recclosure_rel g l code loc [(n,bod1)] [(n,bod2)] ∧
       v = Closure (SOME loc) vs2 env2 n bod2 ∧ loco = SOME loc ∧
       LIST_REL (v_rel g l code) vs1 vs2 ∧
       env_rel (v_rel g l code) env1 env2 0 [(n,bod2)]) ∧
  (v_rel g l code (Recclosure loco vs1 env1 fns1 i) v ⇔
     ∃loc vs2 env2 fns2.
       recclosure_rel g l code loc fns1 fns2 ∧
       v = Recclosure (SOME loc) vs2 env2 fns2 i ∧ loco = SOME loc ∧
       LIST_REL (v_rel g l code) vs1 vs2 ∧
       env_rel (v_rel g l code) env1 env2 (LENGTH fns2) fns2)`
  (WF_REL_TAC `measure (v_size o FST o SND o SND o SND)` >> simp[v_size_def] >>
   rpt strip_tac >> imp_res_tac v_size_lemma >> simp[]);

val v_rel_ind = theorem"v_rel_ind";

val wfv_def = tDefine"wfv"`
  (wfv g l code (Closure NONE _ _ _ _) ⇔ F) ∧
  (wfv g l code (Recclosure NONE _ _ _ _) ⇔ F) ∧
  (wfv g l code (Closure (SOME loc) vs env n bod) ⇔
    EVERY (wfv g l code) vs ∧ EVERY (wfv g l code) env ∧
    ∃fns2.
    recclosure_rel g l code loc [(n,bod)] fns2) ∧
  (wfv g l code (Recclosure (SOME loc) vs env fns i) ⇔
    EVERY (wfv g l code) vs ∧ EVERY (wfv g l code) env ∧
    ∃fns2.
    recclosure_rel g l code loc fns fns2) ∧
  (wfv g l code (Block _ vs) ⇔ EVERY (wfv g l code) vs) ∧
  (wfv _ _ _ _ ⇔ T)`
  (WF_REL_TAC `measure (v_size o SND o SND o SND)` >> simp[v_size_def] >>
   rpt strip_tac >> imp_res_tac v_size_lemma >> simp[]);
val _ = export_rewrites["wfv_def"];

val wfv_ind = theorem"wfv_ind";

val wfv_state_def = Define`
  wfv_state g l code s ⇔
    EVERY (OPTION_ALL (wfv g l code)) s.globals ∧
    FEVERY (every_refv (wfv g l code) o SND) s.refs ∧
    s.code = FEMPTY`;

val _ = temp_type_abbrev("calls_state",
          ``:num_set # (num, num # closLang$exp) alist``);

val _ = temp_type_abbrev("abs_calls_state",``:num_set``);

val correct_l_def = Define `
  correct_l l g <=> l = UNIV DIFF domain (FST g)`;

val state_rel_def = Define`
  state_rel g l (s:(abs_calls_state # 'c,'ffi) closSem$state) (t:('c,'ffi) closSem$state) ⇔
    (s.ffi = t.ffi) ∧
    (s.clock = t.clock) ∧
    (s.max_app = t.max_app) ∧
    LIST_REL (OPTREL (v_rel g l t.code)) s.globals t.globals ∧
    fmap_rel (ref_rel (v_rel g l t.code)) s.refs t.refs ∧
    s.code = FEMPTY ∧ correct_l l g`;

Theorem state_rel_max_app:
   state_rel g l s t ⇒ s.max_app = t.max_app
Proof
  rw[state_rel_def]
QED

Theorem state_rel_clock:
   state_rel g l s t ⇒ s.clock = t.clock
Proof
  rw[state_rel_def]
QED

Theorem state_rel_with_clock:
   state_rel g l s t ⇒ state_rel g l (s with clock := k) (t with clock := k)
Proof
  rw[state_rel_def]
QED

Theorem state_rel_flookup_refs:
   state_rel g l s t ∧ FLOOKUP s.refs k = SOME v ⇒
   ∃v'. FLOOKUP t.refs k = SOME v' ∧ ref_rel (v_rel g l t.code) v v'
Proof
  rw[state_rel_def,fmap_rel_OPTREL_FLOOKUP]
  \\ first_x_assum(qspec_then`k`mp_tac) \\ rw[OPTREL_def]
QED

(* syntactic properties of compiler *)

Theorem FST_code_list[simp]:
   ∀loc fns g. FST (code_list loc fns g) = FST g
Proof
  ho_match_mp_tac code_list_ind
  \\ rw[code_list_def]
QED

Theorem SND_insert_each[simp]:
   ∀p n g. SND (insert_each p n g) = SND g
Proof
  ho_match_mp_tac insert_each_ind
  \\ rw[insert_each_def]
QED

Theorem calls_list_MAPi:
   ∀loc tra n. calls_list tra n loc = MAPi (λi p. (FST p, Call (tra§n+i§0) 0 (loc+2*i+1) (GENLIST_Var (tra§n+i) 1 (FST p))))
Proof
  simp[FUN_EQ_THM]
  \\ CONV_TAC(RESORT_FORALL_CONV(List.rev))
  \\ Induct \\ simp[calls_list_def]
  \\ Cases \\ simp[calls_list_def]
  \\ simp[o_DEF,ADD1,LEFT_ADD_DISTRIB]
  \\ rw[] \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ simp[FUN_EQ_THM]
QED

Theorem calls_list_length[simp]:
   LENGTH (calls_list t n p fns) = LENGTH fns
Proof
  rw[calls_list_MAPi]
QED

Theorem domain_FST_insert_each:
   ∀p n g. domain (FST (insert_each p n g)) = set (GENLIST (λi. 2 * i + p) n) ∪ domain (FST g)
Proof
  ho_match_mp_tac insert_each_ind
  \\ rw[insert_each_def,GENLIST_CONS,o_DEF,ADD1,LEFT_ADD_DISTRIB]
  \\ simp[EXTENSION,MEM_GENLIST]
  \\ metis_tac[ADD_ASSOC,ADD_COMM]
QED

Theorem SND_code_list_change:
   ∀loc fns g g'. SND g = SND g' ⇒
    SND (code_list loc fns g) = SND (code_list loc fns g')
Proof
  ho_match_mp_tac code_list_ind
  \\ rw[code_list_def]
  \\ Cases_on`g'` \\ rw[code_list_def]
  \\ fs[FORALL_PROD]
QED

Theorem MAP_FST_code_list:
   ∀loc fns g.
    MAP FST (SND (code_list loc fns g)) =
    REVERSE (GENLIST (λi. loc + i*2 + 1) (LENGTH fns)) ++ MAP FST (SND g)
Proof
  ho_match_mp_tac code_list_ind
  \\ rw[code_list_def]
  \\ rw[GENLIST_CONS,MAP_REVERSE]
  \\ rw[o_DEF,ADD1]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ rw[FUN_EQ_THM]
QED

Theorem SND_code_list_ZIP:
   ∀loc fns g. SND (code_list loc fns g) =
   REVERSE(ZIP (GENLIST ($+ (loc+1) o $* 2) (LENGTH fns), fns)) ++ (SND g)
Proof
  ho_match_mp_tac code_list_ind
  \\ rw[code_list_def,GENLIST_CONS]
  \\ simp[REVERSE_ZIP,o_DEF,ADD1,LEFT_ADD_DISTRIB]
QED

Theorem ALOOKUP_code_list:
   ∀loc fns g k.
    ALOOKUP (SND (code_list loc fns g)) k =
    case some i. i < LENGTH fns ∧ k = loc + 2*i+1 of
    | SOME i => SOME (EL i fns)
    | NONE => ALOOKUP (SND g) k
Proof
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
  \\ DEEP_INTRO_TAC some_intro \\ rw[]
QED

Theorem insert_each_subspt:
   ∀p n g. subspt (FST g) (FST (insert_each p n g))
Proof
  ho_match_mp_tac insert_each_ind
  \\ rw[insert_each_def]
  \\ fs[subspt_def,lookup_insert]
  \\ rw[] \\ fs[domain_lookup]
QED

Theorem code_list_IS_SUFFIX:
   ∀loc fns g. IS_SUFFIX (SND (code_list loc fns g)) (SND g)
Proof
  ho_match_mp_tac code_list_ind
  \\ rw[code_list_def] \\ fs[IS_SUFFIX_APPEND]
QED

Theorem calls_subspt:
   ∀xs g0 ys g. calls xs g0 = (ys,g) ⇒ subspt (FST g0) (FST g)
Proof
  ho_match_mp_tac calls_ind
  \\ rw[calls_def] \\ rw[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ metis_tac[subspt_trans,insert_each_subspt]
QED

Theorem calls_code_subset:
   ∀xs g0 ys g. calls xs g0 = (ys,g) ⇒
      IMAGE SUC (domain (FST g0)) SUBSET IMAGE SUC (domain (FST g)) /\
      set (MAP FST (SND g0)) SUBSET set (MAP FST (SND g)) /\
      set (MAP FST (SND g)) SUBSET
        IMAGE SUC (domain (FST g)) UNION set (MAP FST (SND g0))
Proof
  ho_match_mp_tac calls_ind
  \\ rw[calls_def] \\ rw[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ fs [SUBSET_DEF,FST_code_list,domain_FST_insert_each]
  \\ fs [PULL_EXISTS,MAP_FST_code_list,MEM_GENLIST]
  \\ rw []
  \\ TRY (
    first_assum drule \\ reverse strip_tac \\ fs []
    THEN1 (metis_tac [EVAL ``SUC 0n``])
    \\ disj1_tac
    \\ qexists_tac `2 * i` \\ fs []
    \\ imp_res_tac LIST_REL_LENGTH
    \\ `LENGTH (MAP FST fns) = LENGTH fns` by fs []
    \\ full_simp_tac std_ss [LENGTH_ZIP]
    \\ metis_tac [])
  \\ TRY (
    first_assum drule \\ reverse strip_tac \\ fs []
    THEN1 (metis_tac [EVAL ``SUC 0n``])
    \\ disj1_tac
    \\ qexists_tac `2 * i + x` \\ fs []
    \\ imp_res_tac LIST_REL_LENGTH
    \\ `LENGTH (MAP FST fns) = LENGTH fns` by fs []
    \\ full_simp_tac std_ss [LENGTH_ZIP]
    \\ metis_tac [])
  \\ metis_tac [EVAL ``SUC 0n``]
QED

Theorem calls_IS_SUFFIX:
   ∀xs g0 ys g. calls xs g0 = (ys,g) ⇒ IS_SUFFIX (SND g) (SND g0)
Proof
  ho_match_mp_tac calls_ind
  \\ rw[calls_def] \\ rw[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ metis_tac[IS_SUFFIX_TRANS,IS_SUFFIX_CONS,code_list_IS_SUFFIX]
QED

Theorem calls_add_SUC_code_locs:
   ∀xs g0 ys g. calls xs g0 = (ys,g) ⇒
    set (MAP FST (SND g)) ⊆
    set (MAP FST (SND g0)) ∪ IMAGE SUC (set (code_locs xs))
Proof
  ho_match_mp_tac calls_ind
  \\ rw[calls_def,code_locs_def]
  \\ rpt (pairarg_tac \\ fs[]) \\ rw[]
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ imp_res_tac calls_length
  \\ fs[MAP_FST_code_list,LIST_TO_SET_GENLIST]
  \\ fs[SUBSET_DEF,PULL_EXISTS,ADD1]
  \\ metis_tac[]
QED

Theorem calls_ALL_DISTINCT:
   ∀xs g0 ys g.
    calls xs g0 = (ys,g) ∧ ALL_DISTINCT (MAP FST (SND g0)) ∧
    ALL_DISTINCT (code_locs xs) ∧
    DISJOINT (IMAGE SUC (set (code_locs xs))) (set (MAP FST (SND g0)))
    ⇒ ALL_DISTINCT (MAP FST (SND g))
Proof
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
  \\ metis_tac[numTheory.INV_SUC,DECIDE``2 * i + SUC loc = SUC (2*i+loc)``]
QED

Theorem compile_ALL_DISTINCT:
   compile do_call x = (y,g,aux) ∧
   ALL_DISTINCT (code_locs x)
  ⇒
   ALL_DISTINCT (MAP FST aux)
Proof
  Cases_on`do_call` \\ rw[compile_def] \\ rw[]
  \\ pairarg_tac \\ fs[]
  \\ drule calls_ALL_DISTINCT
  \\ rw[]
QED

Theorem calls_subg:
   ∀xs g0 ys g.
    calls xs g0 = (ys,g) ∧
    ALL_DISTINCT (MAP FST (SND g0)) ∧
    ALL_DISTINCT (code_locs xs) ∧
    DISJOINT (IMAGE SUC (set (code_locs xs))) (set (MAP FST (SND g0)))
    ⇒ subg g0 g
Proof
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
  \\ metis_tac[FST]
QED

Theorem calls_domain:
   ∀xs g0 ys g. calls xs g0 = (ys,g) ⇒
    domain (FST g) ⊆ domain (FST g0) ∪ IMAGE PRE (set (MAP FST (SND g)))
Proof
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
  \\ metis_tac[numTheory.INV_SUC,prim_recTheory.PRE,EVAL``PRE 1``]
QED

Theorem wfg'_insert_each:
   ∀n g loc. wfg' g ⇒ wfg' (insert_each loc n g)
Proof
  Induct \\ Cases \\ rw[insert_each_def]
  \\ first_x_assum match_mp_tac
  \\ fs[wfg'_def,SUBSET_DEF,IN_EVEN]
  \\ metis_tac[EVEN_ADD,EVAL``EVEN 2``]
QED

Theorem wfg'_code_list:
   ∀ls g loc.
      wfg' g ∧ set (GENLIST (λi. loc + 2 * i) (LENGTH ls)) ⊆ domain (FST g)
      ⇒ wfg' (code_list loc ls g)
Proof
  rw[wfg'_def,SUBSET_DEF,MEM_GENLIST,MAP_FST_code_list]
  >- (
    fs[ADD1,PULL_EXISTS]
    \\ metis_tac[ADD_ASSOC] )
  \\ metis_tac[]
QED

Theorem closed_Fn:
   closed (Fn t loco vs args e) ⇔
   ∀v. has_var v (SND (free [e])) ⇒ v < args
Proof
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
  \\ res_tac \\ fs[]
QED

Theorem closed_Fn_fv:
   closed (Fn t loco vs args e) ⇔
   ∀v. fv v [e] ⇒ v < args
Proof
  rw[closed_Fn]
  \\ qspec_then`[e]`mp_tac free_thm
  \\ simp[] \\ pairarg_tac \\ fs[]
QED

Theorem calls_wfg':
   ∀xs g0 ys g.
    calls xs g0 = (ys,g) ∧
    every_Fn_SOME xs ∧ wfg' g0 ⇒
    wfg' g
Proof
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
  \\ simp[Abbr`d`,domain_FST_insert_each]
QED

Theorem calls_wfg:
   ∀xs g0 ys g.
    calls xs g0 = (ys,g) ∧
    ALL_DISTINCT (code_locs xs) ∧
    DISJOINT (IMAGE SUC (set (code_locs xs))) (set (MAP FST (SND g0))) ∧
    every_Fn_SOME xs ∧ wfg g0
    ⇒
    wfg g
Proof
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
  \\ rw[] \\ rfs[]
QED

Theorem calls_fv1_subset:
   ∀xs g0 ys g. calls xs g0 = (ys,g) ⇒
    LIST_REL (λx y. (combin$C fv1) y ⊆ (combin$C fv1) x) xs ys
Proof
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
  \\ metis_tac[]
QED

Theorem calls_fv_imp:
   calls xs g0 = (ys,g) ∧ fv v ys ⇒ fv v xs
Proof
  rw[] \\ imp_res_tac calls_fv1_subset
  \\ fs[LIST_REL_EL_EQN,fv_exists,EXISTS_MEM,MEM_EL,SUBSET_DEF,IN_DEF]
  \\ metis_tac[]
QED

Theorem FST_insert_each_same:
   ∀p n g0 g0'.
    FST g0 = FST g0' ⇒ FST (insert_each p n g0) = FST (insert_each p n g0')
Proof
  ho_match_mp_tac insert_each_ind
  \\ rw[insert_each_def] \\ fs[FORALL_PROD]
  \\ Cases_on`g0'` \\ fs[insert_each_def]
QED

Theorem code_list_replace_SND:
   ∀loc fns g0 g g0' ls.
   code_list loc fns g0 = g ∧
   FST g0 = FST g0' ∧
   SND g = ls ++ SND g0
   ⇒
   code_list loc fns g0' = (FST g, ls ++ SND g0')
Proof
  ho_match_mp_tac code_list_ind
  \\ rw[code_list_def] \\ fs[] \\ rw[]
  \\ Cases_on`g0'` \\ fs[code_list_def]
  \\ fs[FORALL_PROD]
  \\ qmatch_asmsub_abbrev_tac`SND (code_list l2 fns g)`
  \\ qispl_then[`l2`,`fns`,`g`]strip_assume_tac code_list_IS_SUFFIX
  \\ fs[IS_SUFFIX_APPEND,Abbr`g`] \\ fs[] \\ rw[] \\ fs[]
QED

Theorem calls_replace_SND:
   ∀xs g0 ys g g0' ls.
    calls xs g0 = (ys,g) ∧
    FST g0 = FST g0' ∧
    SND g = ls ++ SND g0
    ⇒
    calls xs g0' = (ys,(FST g,ls ++ SND g0'))
Proof
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
  \\ metis_tac[SND,FST,PAIR,APPEND_ASSOC,CONS_11,IS_SOME_DEF]
QED

val insert_each'_def = Define`
  (insert_each' gt p 0 g = g) ∧
  (insert_each' gt p (SUC n) (g1,g2) =
   insert_each' gt (p+2) n (insert p () g1, ((p+1,THE(ALOOKUP gt (p+1)))::g2)))`;

val insert_each'_ind = theorem"insert_each'_ind";

Theorem wfg_insert_each':
   ∀gt p n g.
    wfg g ∧
    DISJOINT (set (GENLIST (λi. p+2*i) n)) (domain (FST g))
    ⇒ wfg (insert_each' gt p n g)
Proof
  ho_match_mp_tac insert_each'_ind
  \\ rw[insert_each'_def]
  \\ first_x_assum match_mp_tac
  \\ fs[wfg_def,GSYM ADD1]
  \\ fs[IN_DISJOINT,MEM_GENLIST,IN_EVEN,EVEN_ADD]
  \\ fs[METIS_PROVE[]``x ∨ y ⇔ ¬x ⇒ y``,PULL_EXISTS]
  \\ rw[]
  \\ first_assum (qspec_then`0`mp_tac)
  \\ first_x_assum (qspec_then`SUC i`mp_tac)
  \\ simp[ADD1,LEFT_ADD_DISTRIB]
QED

Theorem FST_insert_each':
   ∀gt p n g. FST (insert_each' gt p n g) = FST (insert_each p n g)
Proof
  ho_match_mp_tac insert_each'_ind
  \\ rw[insert_each'_def,insert_each_def]
  \\ match_mp_tac FST_insert_each_same
  \\ rw[]
QED

Theorem MAP_FST_insert_each':
   ∀gt p n g.
   MAP FST (SND (insert_each' gt p n g)) =
   REVERSE (GENLIST (λi. p + i * 2 + 1) n) ++
   MAP FST (SND g)
Proof
  ho_match_mp_tac insert_each'_ind
  \\ rw[insert_each'_def,GENLIST_CONS,o_DEF,ADD1,LEFT_ADD_DISTRIB]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ simp[FUN_EQ_THM]
QED

Theorem SND_insert_each':
   ∀gt p n g. SND (insert_each' gt p n g) =
    REVERSE (GENLIST (λi. (2*i+p+1,THE(ALOOKUP gt (2*i+p+1)))) n) ++ SND g
Proof
  ho_match_mp_tac insert_each'_ind
  \\ rw[insert_each'_def]
  \\ rw[GENLIST_CONS,o_DEF,ADD1]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ simp[FUN_EQ_THM,LEFT_ADD_DISTRIB]
QED

Theorem calls_el_sing:
   ∀xs g0 ys g i.
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
       (set (code_locs [EL i xs]) DIFF (domain (FST gb))) ⊆ (set (code_locs xs) DIFF (domain (FST g)))
Proof
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
  \\ fs[code_locs_def,ALL_DISTINCT_APPEND]
QED

fun pairmaparg_tac (g as (asl,w)) =
  (tryfind
    (Lib.partial(mk_HOL_ERR"clos_callProofTheory""pairmaparg_tac""not found")
        (bvk_find_term
          (fn (bvs,tm) =>
            is_comb tm andalso
            pairSyntax.is_pair_map (rator tm) andalso
            HOLset.isEmpty
              (HOLset.intersection (FVL bvs empty_tmset,
                                    FVL [rand tm] empty_tmset)) andalso
            not (pairSyntax.is_pair (rand tm)))
          (fn tm => Cases_on [ANTIQUOTE (rand tm)])))
    (w::asl)) g

Theorem insert_each_pair_arg:
   insert_each x y (p,q) = (FST (insert_each x y (p,q')), q)
Proof
  Cases_on`insert_each x y (p,q)` \\ rw[]
  \\ metis_tac[SND_insert_each, SND, FST_insert_each_same, FST]
QED

val calls_acc_0 = Q.prove(
  `!xs tmp x r.
     x ++ r = SND tmp ⇒
     calls xs tmp = (I ## I ## (combin$C (++) r)) (calls xs (FST tmp, x))`,
  recInduct calls_ind
  \\ rw[calls_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rveq \\ fs[]
  \\ TRY (
    first_x_assum drule
    \\ pairmaparg_tac \\ fs[]
    \\ strip_tac \\ rveq \\ fs[]
    \\ pairmaparg_tac \\ fs[]
    \\ pairmaparg_tac \\ fs[]
    \\ fsrw_tac[DNF_ss][APPEND_EQ_APPEND]
    \\ first_x_assum(qspecl_then[`r''`,`[]`]mp_tac)
    \\ simp[]
    \\ strip_tac \\ rveq \\ fs[]
    \\ pairmaparg_tac \\ fs[]
    \\ last_x_assum(qspecl_then[`r'''`,`r`]mp_tac)
    \\ simp[]
    \\ NO_TAC )
  >- (
    first_x_assum drule
    \\ pairmaparg_tac \\ fs[]
    \\ strip_tac \\ rveq \\ fs[]
    \\ pairmaparg_tac \\ fs[]
    \\ pairmaparg_tac \\ fs[]
    \\ pairmaparg_tac \\ fs[]
    \\ fs[bool_case_eq] \\ rveq \\ fs[]
    \\ first_x_assum(qspecl_then[`r'`,`r`]mp_tac)
    \\ simp[] )
  >- (
    pairmaparg_tac \\ fs[]
    \\ pairmaparg_tac \\ fs[]
    \\ first_x_assum drule
    \\ pairmaparg_tac \\ fs[]
    \\ strip_tac \\ rveq \\ fs[]
    \\ qmatch_asmsub_abbrev_tac`insert_each p s (FST g, x)`
    \\ `insert_each p s (FST g, x) = (FST (insert_each p s g), x)` by metis_tac[insert_each_pair_arg, PAIR]
    \\ fs[] \\ rveq
    \\ fs[bool_case_eq] \\ rveq \\ fs[]
    \\ first_x_assum drule
    \\ pairmaparg_tac \\ fs[] )
  >- (
    pairmaparg_tac \\ fs[]
    \\ pairmaparg_tac \\ fs[]
    \\ first_x_assum drule
    \\ pairmaparg_tac \\ fs[]
    \\ strip_tac \\ rveq \\ fs[]
    \\ qmatch_asmsub_abbrev_tac`insert_each p s (FST g, x)`
    \\ `insert_each p s (FST g, x) = (FST (insert_each p s g), x)` by metis_tac[insert_each_pair_arg, PAIR]
    \\ fs[] \\ rveq
    \\ reverse (fs[bool_case_eq]) \\ rveq \\ fs[]
    >- (
      first_x_assum drule
      \\ pairmaparg_tac \\ fs[]
      \\ rveq \\ fs[]
      \\ pairmaparg_tac \\ fs[]
      \\ pairmaparg_tac \\ fs[]
      \\ strip_tac \\ rveq \\ fs[]
      \\ first_x_assum(qspecl_then[`r'`,`r`]mp_tac)
      \\ simp[] )
    \\ pairmaparg_tac \\ fs[]
    \\ qmatch_asmsub_abbrev_tac`code_list p ff`
    \\ Q.ISPECL_THEN[`p`,`ff`,`q,r'`]mp_tac code_list_replace_SND
    \\ simp[]
    \\ disch_then(qspec_then`q,r'++r`mp_tac) \\ fs[]
    \\ Cases_on`code_list p ff (q,r')` \\ fs[]
    \\ `∃ls. r''' = ls ++ r'` by metis_tac[SND_code_list_ZIP, SND] \\ fs[]
    \\ strip_tac \\ fs[]
    \\ first_x_assum(qspecl_then[`ls++r'`,`r`]mp_tac)
    \\ simp[]
    \\ pairmaparg_tac \\ fs[]
    \\ strip_tac \\ rveq \\ fs[]
    \\ pairmaparg_tac \\ fs[]
    \\ `q'' = q` by metis_tac[FST_code_list, FST]
    \\ fs[] ));

Theorem calls_acc:
   !xs d old res d1 aux.
      calls xs (d, []) = (res, d1, aux) ==>
      calls xs (d, old) = (res, d1, aux ++ old)
Proof
  rw[]
  \\ qspecl_then[`xs`,`d,old`,`[]`,`old`]mp_tac calls_acc_0
  \\ simp[]
QED

(* properties of value relation *)

Theorem v_rel_exists:
   ∀v1. wfv g l code v1 ⇒ ∃v2. v_rel g l code v1 v2
Proof
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
    \\ metis_tac[SKOLEM_THM] )
QED

Theorem v_rel_subg:
   ∀g l code v1 v2 g' l'.
    v_rel g l code v1 v2 ∧ subg g g' ∧ l ⊆ l' ⇒
    v_rel g' l' code v1 v2
Proof
  ho_match_mp_tac v_rel_ind
  \\ rw[v_rel_def,env_rel_def,recclosure_rel_def]
  \\ Cases_on`LENGTH env1 = LENGTH env2`
  \\ fsrw_tac[ETA_ss][PULL_FORALL,PULL_EXISTS]
  \\ rpt(
    qmatch_assum_abbrev_tac`LIST_REL (v_rel g l code) l1 l2`
    \\ `LIST_REL (v_rel g' l' code) l1 l2`
    by (
      match_mp_tac EVERY2_MEM_MONO
      \\ first_assum(part_match_exists_tac (last o strip_conj) o concl)
      \\ simp[FORALL_PROD]
      \\ imp_res_tac LIST_REL_LENGTH
      \\ simp[MEM_ZIP,PULL_EXISTS]
      \\ metis_tac[MEM_EL] )
    \\ qpat_x_assum`LIST_REL (v_rel g l code) l1 l2` kall_tac
    \\ map_every qunabbrev_tac[`l2`,`l1`])
  \\ fs[]
  \\ qexists_tac`g0`
  \\ rpt(pairarg_tac \\ fs[])
  \\ imp_res_tac calls_length
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
  \\ rveq \\ fs[]
  \\ CASE_TAC \\ fs[] \\ rfs[]
  \\ fs[EXISTS_MEM,EXISTS_PROD]
  \\ metis_tac[subg_trans,SUBSET_DEF,MEM_EL]
QED

Theorem code_includes_subg:
   subg g1 g2 ⇒ code_includes (SND g2) code ⇒ code_includes (SND g1) code
Proof
  rw[subg_def,code_includes_def,IS_SUFFIX_APPEND]
  \\ first_x_assum match_mp_tac
  \\ rw[ALOOKUP_APPEND]
  \\ BasicProvers.CASE_TAC
  \\ imp_res_tac ALOOKUP_MEM
  \\ rfs[ALL_DISTINCT_APPEND,MEM_MAP,PULL_EXISTS]
  \\ res_tac \\ fs[]
  \\ metis_tac[FST]
QED

Theorem code_includes_ALOOKUP:
   code_includes al code ∧ ALOOKUP al loc = SOME r ⇒ FLOOKUP code loc = SOME r
Proof
  rw[code_includes_def]
QED

Theorem dest_closure_v_rel_lookup:
   dest_closure max_app (SOME loc) v1 env1 = SOME x ∧
   v_rel g l code v1 v2 ∧
   LIST_REL (v_rel g l code) env1 env2 ∧
   wfg g ∧ loc ∈ domain (FST g) ∧ loc ∉ l  ⇒
   ∃e l1 xs n ls g01 g1 l1' tra i.
     x = Full_app e (env1++l1) [] ∧ EL n xs = (LENGTH env1,e) ∧
     calls (MAP SND xs) g01 = (ls,g1) ∧ n < LENGTH ls ∧
     subg (code_list (loc - 2*n) (ZIP (MAP FST xs,ls)) g1) g ∧
     ALOOKUP (SND g) (loc+1) = SOME (LENGTH env1,EL n ls) ∧
     dest_closure max_app (SOME loc) v2 env2 =
       SOME (Full_app (Call (tra§i§0) 0 (loc+1)
         (GENLIST_Var (tra§i) 1 (LENGTH env1))) (env2++l1') []) ∧
     code_includes (SND (code_list (loc - 2*n) (ZIP (MAP FST xs,ls)) g1)) code
Proof
  rw[dest_closure_def]
  \\ every_case_tac \\ fs[v_rel_def,recclosure_rel_def]
  \\ rw[] \\ fs[check_loc_def] \\ rw[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ rfs[]
  \\ fs[LENGTH_NIL] \\ rveq
  \\ imp_res_tac LIST_REL_LENGTH \\ fs[]
  \\ fs[DROP_LENGTH_NIL_rwt,revtakerev]
  >- (
    qpat_abbrev_tac`ele = (_,_)`
    \\ qexists_tac`[ele]` \\ simp[Abbr`ele`]
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
  \\ simp[revtakerev,revdroprev,TAKE_APPEND]
  \\ TRY (match_mp_tac EVERY2_APPEND_suff)
  \\ fsrw_tac[ETA_ss][]
  \\ simp[LIST_REL_GENLIST]
  \\ simp[v_rel_def,recclosure_rel_def]
  \\ fsrw_tac[ETA_ss][]
  \\ simp[calls_list_MAPi]
  \\ rw[]
  \\ qexists_tac`g0`
  \\ simp[]
QED

Theorem dest_closure_v_rel:
   dest_closure max_app loco v1 env1 = SOME x1 ∧
   v_rel g l code v1 v2 ∧
   LIST_REL (v_rel g l code) env1 env2
   ⇒
   ∃x2.
   dest_closure max_app loco v2 env2 = SOME x2 ∧
   (case x1 of Partial_app c1 =>
     ∃c2. x2 = Partial_app c2 ∧ v_rel g l code c1 c2
    | Full_app e1 args1 rest1 =>
      ∃fns1 loc i fns2 args2 rest2 n.
        x2 = Full_app (SND (EL i fns2)) args2 rest2 ∧
        (let m = if is_Recclosure v2 then LENGTH fns2 else 0 in
         n+m ≤ LENGTH args1 ∧ n+m ≤ LENGTH args2 ∧
         LIST_REL (v_rel g l code) (TAKE (n+m) args1) (TAKE (n+m) args2) ∧
         env_rel (v_rel g l code) (DROP (n+m) args1)
                                  (DROP (n+m) args2) m [EL i fns2]) ∧
        LIST_REL (v_rel g l code) rest1 rest2 ∧
        recclosure_rel g l code loc fns1 fns2 ∧
        i < LENGTH fns1 ∧
        EL i fns1 = (n,e1))
Proof
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
  \\ simp[]
QED

Theorem dest_closure_partial_wfv:
   dest_closure max_app loco v env = SOME (Partial_app x) ∧
   EVERY (wfv g l code) env ∧ wfv g l code v ⇒ wfv g l code x
Proof
  rw[dest_closure_def]
  \\ every_case_tac \\ fs[]
  \\ rw[]
  \\ rpt(pairarg_tac \\ fs[])
  \\ every_case_tac \\ fs[]
  \\ (qmatch_asmsub_rename_tac`Closure lopt` ORELSE
      qmatch_asmsub_rename_tac`Recclosure lopt`)
  \\ Cases_on`lopt` \\ fs[] \\ rveq
  \\ fsrw_tac[ETA_ss][]
  \\ metis_tac[]
QED

Theorem dest_closure_full_wfv:
   dest_closure max_app loco v env = SOME (Full_app e args rest) ∧
   wfv g l code v ∧ EVERY (wfv g l code) env
   ⇒
   ∃ys g01 loc fns1 fns2 i.
     EVERY (wfv g l code) args ∧ EVERY (wfv g l code) rest ∧
     recclosure_rel g l code loc fns1 fns2 ∧
     SND (EL i fns1) = e ∧ i < LENGTH fns1
Proof
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
  \\ metis_tac[PAIR,SND,EL,HD]
QED

Theorem env_rel_DROP:
   env_rel R (DROP x l1) (DROP x l2) x es ∧
   LIST_REL R (TAKE x l1) (TAKE x l2) ∧
   x ≤ LENGTH l1 ∧ x ≤ LENGTH l2
   ⇒
   env_rel R l1 l2 0 es
Proof
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
  \\ rfs[EL_DROP]
QED

Theorem env_rel_DROP_args:
   env_rel R (DROP n l1) (DROP n l2) a [(n,e)] ∧
   LIST_REL R (TAKE n l1) (TAKE n l2) ∧
   n ≤ LENGTH l1 ∧ n ≤ LENGTH l2 ⇒
   env_rel R l1 l2 a [(0,e)]
Proof
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
  \\ rfs[EL_DROP]
QED

Theorem subg_insert_each':
   !gb fns1 es g1.
      subg gb (FST new_g,l ++ SND (insert_each' g1 loc (LENGTH fns1) g)) /\
      SND new_g = l ++ SND g /\ LENGTH fns1 = LENGTH es
      ∧ wfg g ∧
      DISJOINT (set (GENLIST (λi. 2*i+loc+1) (LENGTH fns1))) (IMAGE SUC (domain (FST g))) ∧
      DISJOINT (set (MAP FST l)) (IMAGE SUC (domain (FST g))) ∧
      (∀i. i < LENGTH fns1 ⇒ ALOOKUP g1 (2*i+loc+1) = SOME (FST (EL i fns1), EL i es))
      ==>
      subg (FST new_g,l ++ SND (insert_each' g1 loc (LENGTH fns1) g))
        (code_list loc (ZIP (MAP FST fns1,es)) new_g)
Proof
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
  \\ metis_tac[ADD_ASSOC,ADD_COMM]
QED

val code_includes_SUBMAP = prove(
  ``code_includes x y1 /\ y1 SUBMAP y2 ==> code_includes x y2``,
  fs [code_includes_def,SUBMAP_DEF,FLOOKUP_DEF] \\ metis_tac []);

Theorem wfv_subg:
   ∀g l code v g' l' code'.
     wfv g l code v ∧ code SUBMAP code' ∧ subg g g' ∧ l ⊆ l' ⇒ wfv g' l' code' v
Proof
  ho_match_mp_tac wfv_ind \\ rw[]
  \\ fsrw_tac[ETA_ss][]
  \\ fs[EVERY_MEM]
  \\ fs[recclosure_rel_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["g0'"]))
  \\ qexists_tac`g0`\\fs[]
  \\ CASE_TAC \\ fs[SUBSET_DEF]
  \\ rveq \\ fs[]
  \\ metis_tac[subg_trans,code_includes_SUBMAP]
QED

Theorem wfv_SUBMAP:
   !g1 l1 code v code1.
      wfv g1 l1 code v /\ code SUBMAP code1 ==> wfv g1 l1 code1 v
Proof
  ho_match_mp_tac wfv_ind \\ rw[]
  \\ fsrw_tac[ETA_ss][]
  \\ fs[EVERY_MEM]
  \\ fs[recclosure_rel_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["g0'"]))
  \\ qexists_tac`g0`\\fs[]
  \\ CASE_TAC \\ fs[SUBSET_DEF]
  \\ rveq \\ fs[]
  \\ metis_tac[subg_trans,code_includes_SUBMAP]
QED

Theorem EVERY_wfv_SUBMAP:
   EVERY (wfv g1 l1 code) env /\ code SUBMAP code1 ==>
    EVERY (wfv g1 l1 code1) env
Proof
  fs [EVERY_MEM] \\ metis_tac [wfv_SUBMAP]
QED

Theorem wfv_state_SUBMAP:
   !g1 l1 code s code1.
      wfv_state g1 l1 code s /\ code SUBMAP code1 ==>
      wfv_state g1 l1 code1 s
Proof
  rw[wfv_state_def, EVERY_MEM, FEVERY_ALL_FLOOKUP]
  \\ metis_tac[OPTION_ALL_MONO, wfv_SUBMAP, every_refv_def,
               MONO_EVERY, ref_nchotomy]
QED

Theorem v_rel_SUBMAP:
   !g1 l1 code v1 v2 code1.
      v_rel g1 l1 code v1 v2 /\ code SUBMAP code1 ==> v_rel g1 l1 code1 v1 v2
Proof
  ho_match_mp_tac v_rel_ind \\ rw[]
  \\ fsrw_tac[ETA_ss][v_rel_def]
  \\ fs [MEM_EL,PULL_EXISTS,PULL_FORALL,AND_IMP_INTRO]
  \\ fs[env_rel_def, recclosure_rel_def, LIST_REL_EL_EQN]
  \\ rw[]
  \\ TRY (
    qexists_tac`g0` \\ fs[]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rw[] \\ rfs[] )
  \\ metis_tac[code_includes_SUBMAP]
QED

Theorem LIST_REL_v_rel_SUBMAP:
   !g1 l1 code v1 v2 code1.
      LIST_REL (v_rel g1 l1 code) v1 v2 /\ code SUBMAP code1 ==>
      LIST_REL (v_rel g1 l1 code1) v1 v2
Proof
  metis_tac[LIST_REL_mono, v_rel_SUBMAP]
QED

Theorem env_rel_SUBMAP:
   !code code' g1 l1 env1 env2 n vars.
      env_rel (v_rel g1 l1 code) env1 env2 n vars /\ code SUBMAP code' ==>
      env_rel (v_rel g1 l1 code') env1 env2 n vars
Proof
  rw[env_rel_def, EXISTS_MEM, PULL_EXISTS, UNCURRY]
  \\ metis_tac[LIST_REL_mono, v_rel_SUBMAP]
QED

(* semantic functions respect relation *)

Theorem v_rel_Unit[simp]:
   v_rel g1 l1 code Unit Unit
Proof
  EVAL_TAC \\ fs []
QED

Theorem v_to_list_thm:
   !h h' x.
      v_to_list h = SOME x /\ v_rel g1 l1 code h h' ==>
      ?x'. v_to_list h' = SOME x' /\ LIST_REL (v_rel g1 l1 code) x x'
Proof
  recInduct v_to_list_ind \\ rw [] \\ fs [v_to_list_def] \\ rw []
  \\ fs [v_rel_def,v_to_list_def] \\ rw []
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ res_tac \\ fs [] \\ rw []
QED

val v_rel_IMP_v_to_bytes_lemma = prove(
  ``!x y c g code.
      v_rel c g code x y ==>
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
      v_rel c g code x y ==>
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

Theorem v_to_bytes_thm:
   !h h' x.
      v_to_bytes h = SOME x /\ v_rel g1 l1 code h h' ==>
      v_to_bytes h' = SOME x
Proof
  rw [v_to_bytes_def] \\ drule v_rel_IMP_v_to_bytes_lemma \\ fs []
  \\ rw [] \\ fs []
QED

Theorem v_to_words_thm:
   !h h' x.
      v_to_words h = SOME x /\ v_rel g1 l1 code h h' ==>
      v_to_words h' = SOME x
Proof
  rw [v_to_words_def] \\ drule v_rel_IMP_v_to_words_lemma \\ fs []
  \\ rw [] \\ fs []
QED

Theorem v_to_list_wfv:
   !h x. v_to_list h = SOME x /\ wfv g1 l1 code h ==> EVERY (wfv g1 l1 code) x
Proof
  recInduct v_to_list_ind \\ rw [] \\ fs [v_to_list_def] \\ rw []
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ res_tac \\ fs [] \\ rw []
QED

Theorem wfv_Boolv:
   wfv g1 l1 code (Boolv b) /\ wfv g1 l1 code Unit
Proof
  Cases_on `b` \\ EVAL_TAC
QED

Theorem vrel_list_to_v:
   !xs1 xs2 ys1 ys2.
     LIST_REL (v_rel g l code) xs1 xs2 /\
     LIST_REL (v_rel g l code) ys1 ys2 /\
     v_rel g l code (list_to_v xs1) (list_to_v xs2) /\
     v_rel g l code (list_to_v ys1) (list_to_v ys2) ==>
       v_rel g l code (list_to_v (xs1 ++ ys1)) (list_to_v (xs2 ++ ys2))
Proof
  Induct >- rw [list_to_v_def] \\ gen_tac
  \\ Induct \\ rw [list_to_v_def] \\ fs [v_rel_def]
QED

Theorem vrel_v2l_l2v:
   !x y xs ys.
     v_rel g l code x y /\
     v_to_list x = SOME xs /\
     v_to_list y = SOME ys ==>
       v_rel g l code (list_to_v xs) (list_to_v ys)
Proof
  ho_match_mp_tac v_to_list_ind \\ rw [v_to_list_def, v_rel_def]
  \\ fs [list_to_v_def] \\ rveq
  \\ fs [v_to_list_def] \\ rveq
  \\ fs [list_to_v_def, case_eq_thms, v_rel_def] \\ rveq
  \\ fs [list_to_v_def, v_rel_def]
  \\ res_tac
QED

Theorem wfv_v2l_l2v:
   !x y xs ys. wfv g l code x /\ v_to_list x = SOME xs ==>
               wfv g l code (list_to_v xs)
Proof
  ho_match_mp_tac v_to_list_ind \\ rw [v_to_list_def, wfv_def]
  \\ fs [list_to_v_def, case_eq_thms]
  \\ rw [list_to_v_def]
QED

Theorem wfv_v2l:
   !x y xs ys.
   wfv g l code x /\ wfv g l code y /\
   v_to_list x = SOME xs /\ v_to_list y = SOME ys ==>
     ?z. wfv g l code z /\ v_to_list z = SOME (xs ++ ys)
Proof
  ho_match_mp_tac v_to_list_ind \\ rw [v_to_list_def] \\ fs []
  >- metis_tac []
  \\ fs [case_eq_thms] \\ rw []
  \\ first_x_assum drule
  \\ disch_then drule \\ fs [] \\ rw []
  \\ Cases_on `z` \\ fs [v_to_list_def]
  \\ qexists_tac `Block cons_tag [h; Block n l']`
  \\ fs [wfv_def, v_to_list_def]
QED

Theorem do_app_thm:
   case do_app op (REVERSE a) (r:(abs_calls_state # 'c,'ffi) closSem$state) of
      Rerr (Rraise _) => F
    | Rerr (Rabort e) =>
      (e = Rtype_error \/
       (?f. e = Rffi_error f
            /\ (LIST_REL (v_rel g1 l1 t.code) a v /\ state_rel g1 l1 r t
            ==> do_app op (REVERSE v) t = Rerr(Rabort (Rffi_error f)))))
    | Rval (w,s) =>
       (wfv_state g1 l1 t.code r /\ EVERY (wfv g1 l1 t.code) a ==>
        wfv_state g1 l1 t.code s /\ wfv g1 l1 t.code w) /\
       (LIST_REL (v_rel g1 l1 t.code) a v /\ state_rel g1 l1 r t ==>
        ?w' s'. (do_app op (REVERSE v) t = Rval (w',s')) /\
                v_rel g1 l1 t.code w w' /\ state_rel g1 l1 s s')
Proof
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
                |> INST_TYPE [alpha|->``:abs_calls_state # 'c``])
    \\ pop_assum (qspecl_then [`REVERSE v`,`REVERSE a`,
                `v_rel g1 l1 t.code`,
                `t`,`\s u. state_rel g1 l1 s u /\ u.code = t.code`,
                `r`,`op`] mp_tac)
    \\ fs [GSYM AND_IMP_INTRO]
    \\ impl_tac THEN1
     (fs [simple_val_rel_def] \\ rpt strip_tac
      \\ Cases_on `x` \\ fs [v_rel_def]
      \\ eq_tac \\ fs []
      \\ fs [LIST_REL_EL_EQN])
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
                 |> INST_TYPE [gamma|->``:abs_calls_state # 'c``]
                 |> INST_TYPE [alpha|->``:abs_calls_state # 'c``])
  \\ pop_assum (qspecl_then [`REVERSE a`,`REVERSE a`,
                `\v1 v2. wfv g1 l1 t.code v1 /\ v1 = v2`,
                `r`,`\s1 s2. wfv_state g1 l1 t.code s1 /\ s1 = s2`,
                `r`,`op`] mp_tac)
  \\ fs [GSYM AND_IMP_INTRO]
  \\ impl_tac THEN1
   (fs [simple_val_rel_def] \\ rpt strip_tac
    \\ eq_tac \\ fs []
    \\ rw [] \\ fs []
    \\ TRY (fs [LIST_REL_EL_EQN,EVERY_EL] \\ NO_TAC)
    \\ pop_assum mp_tac \\ qspec_tac (`p`,`p`)
    \\ Induct_on `xs` \\ fs [PULL_EXISTS])
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
  \\ fs [AC CONJ_ASSOC CONJ_COMM]
  \\ rpt (disch_then assume_tac) \\ fs [AND_IMP_INTRO]
  \\ first_x_assum match_mp_tac
  \\ pop_assum mp_tac
  \\ rw [] \\ fs []
  \\ pop_assum mp_tac \\ rpt (pop_assum kall_tac)
  \\ Induct_on `a` \\ fs []
QED

Theorem NOT_IN_domain_FST_g:
   ALL_DISTINCT (code_locs xs ++ code_locs ys) ⇒
    calls ys g' = (e2,g) ⇒
    wfg g' ⇒
    MEM x (code_locs xs) ⇒
    x ∉ domain (FST g') ⇒
    x ∉ domain (FST g)
Proof
  rw [] \\ imp_res_tac calls_domain
  \\ fs [SUBSET_DEF,DISJOINT_DEF,EXTENSION] \\ rw []
  \\ CCONTR_TAC \\ fs [] \\ res_tac \\ rveq \\ fs []
  \\ drule calls_add_SUC_code_locs \\ fs [SUBSET_DEF]
  \\ asm_exists_tac \\ fs [] \\ CCONTR_TAC \\ fs []
  \\ rfs [wfg_def,SUBSET_DEF,EXTENSION] \\ rveq \\ fs []
  \\ fs [ALL_DISTINCT_APPEND] \\ res_tac
QED

Theorem v_rel_Boolv[simp]:
   v_rel g1 l1 code (Boolv b) v <=> (v = Boolv b)
Proof
  Cases_on `b` \\ Cases_on `v` \\ fs [v_rel_def,Boolv_def]
QED

val env_rel_Op_Install = prove(
  ``env_rel r env env2 0 [(0,Op v6 Install e1)] <=>
    env_rel r env env2 0 (MAP (λx. (0,x)) e1)``,
  fs [env_rel_def] \\ rw [] \\ fs [fv1_thm,EXISTS_MAP]
  \\ qsuff_tac `!x. EXISTS (λx'. fv1 x x') e1 = fv x e1` \\ fs []
  \\ Induct_on `e1` \\ fs []);

val syntax_ok_def = Define`
  syntax_ok x ⇔ every_Fn_SOME x ∧ every_Fn_vs_NONE x ∧ ALL_DISTINCT (code_locs x)`;

val compile_inc_def = Define `
  compile_inc d (e,xs) =
    let (ea, d1, new_code) = calls e (d,[]) in
      (d1, ea, new_code)`;

val co_ok_def = Define `
  co_ok code co full_gs k <=>
    if k = 0 then T else
      let g = FST (FST (co 0)) in
      let (cfg,exp,aux) = co 0 in
      let (g',exp',aux1) = compile_inc g (exp,aux) in
        FST (FST (co 1)) = g' /\
        make_g g code = SOME (full_gs 0) /\
        (∀i. subg (full_gs 0) (full_gs i)) /\
        (∀x i. MEM x (code_locs exp) ∧ x ∉ domain g' ==>
               x ∉ domain (FST (FST (co i)))) /\
        DISJOINT (set (code_locs exp)) (domain g) /\
        DISJOINT (FDOM code) (set (MAP FST aux1)) /\
        ALL_DISTINCT (MAP FST aux1) /\
        co_ok (code |++ aux1) (shift_seq 1 co) (shift_seq 1 full_gs) (k-1n)`

Theorem co_ok_IMP_full_gs_eq_shift_seq:
   ∀k code co g full_gs.
      co_ok code co full_gs (k+1) ==>
      FST (FST (shift_seq k co 0)) = FST (full_gs k)
Proof
  Induct \\ simp [Once co_ok_def]
  \\ rw [] \\ rpt (pairarg_tac \\ fs [])
  THEN1
   (Cases_on `full_gs 0` \\ fs [shift_seq_def]
    \\ fs [make_g_def] \\ rveq \\ fs [shift_seq_def])
  \\ fs [ADD1]
  \\ first_x_assum drule
  \\ fs [shift_seq_def]
QED

Theorem co_ok_IMP_wfg_full_gs:
   ∀k code co g full_gs. co_ok code co full_gs (k+1) ==> wfg (full_gs k)
Proof
  Induct \\ simp [Once co_ok_def]
  \\ rw [] \\ rpt (pairarg_tac \\ fs [])
  \\ imp_res_tac make_g_wfg
  \\ fs [ADD1] \\ res_tac
  \\ fs [shift_seq_def]
QED

Theorem co_ok_IMP_make_g:
   ∀k code co g full_gs.
      co_ok code co full_gs (k+1) ==>
      ?x1 x2. make_g x1 x2 = SOME (full_gs k)
Proof
  Induct \\ simp [Once co_ok_def]
  \\ rw [] \\ rpt (pairarg_tac \\ fs [])
  \\ fs [ADD1] \\ res_tac
  \\ fs [shift_seq_def]
  \\ asm_exists_tac \\ fs []
QED

val code_inv_def = Define `
  code_inv g1_opt (s_code:num |-> num # closLang$exp) s_cc s_co t_code t_cc t_co <=>
    s_code = FEMPTY /\
    s_cc = state_cc compile_inc t_cc /\
    t_co = state_co compile_inc s_co /\
    ?full_gs.
      (!g1. g1_opt = SOME g1 ==> ?k. full_gs k = g1) /\
      (!k. co_ok t_code s_co full_gs k) /\
      (∀k. let (cfg,exp,aux) = s_co (k:num) in
             aux = [] /\
             every_Fn_SOME exp /\
             every_Fn_vs_NONE exp /\
             ALL_DISTINCT (code_locs exp))`

val dummy_code_inv = mk_var("code_inv",
  type_of(#1(strip_comb(lhs(concl(SPEC_ALL code_inv_def))))))
val code_inv_def = Define`
  ^dummy_code_inv g1_opt s_code
     s_cc s_co t_code t_cc t_co ⇔ (s_code = FEMPTY)`;

Theorem SUBMAP_FUPDATE_LIST:
   !f xs. ALL_DISTINCT (MAP FST xs) ∧ DISJOINT (FDOM f) (set (MAP FST xs)) ⇒ f SUBMAP (f |++ xs)
Proof
  Induct_on`xs` \\ simp[FORALL_PROD] \\ rw[FUPDATE_LIST_THM]
  \\ simp[FUPDATE_FUPDATE_LIST_COMMUTES]
  \\ match_mp_tac SUBMAP_TRANS
  \\ res_tac
  \\ asm_exists_tac \\ fs[]
  \\ fs[FDOM_FUPDATE_LIST]
QED

val includes_state_def = Define `
  includes_state g1 s_compile_oracle <=>
    ?k:num. FST (FST (s_compile_oracle k)) = FST g1`;

val dummy_includes_state = mk_var("includes_state",
  type_of(#1(strip_comb(lhs(concl(SPEC_ALL includes_state_def))))))
val includes_state_def = Define`
  ^dummy_includes_state g1_s compile_oracle ⇔ T`;

(*
Theorem code_rel_state_rel_install = Q.prove(`
  code_inv (SOME g1)
      r.code r.compile r.compile_oracle t.code t.compile t.compile_oracle /\
    includes_state g1 (shift_seq 1 r.compile_oracle) /\
    state_rel g1 l1 r t /\
    r.compile cfg (exp',aux) =
        SOME (bytes,data,FST (shift_seq 1 r.compile_oracle 0)) /\
    DISJOINT (FDOM r.code) (set (MAP FST aux)) /\
    ALL_DISTINCT (MAP FST aux) /\
    r.compile_oracle 0 = (cfg,exp',aux) /\
    t.compile_oracle 0 = (cfg',progs) ==>
    DISJOINT (FDOM t.code) (set (MAP FST (SND progs))) ∧
    ALL_DISTINCT (MAP FST (SND progs)) /\
    t.compile cfg' progs = SOME (bytes,data,FST (shift_seq 1 t.compile_oracle 0)) /\
    ?g4 exp1 aux1 g5 exp5 aux5 other.
      progs = (exp1,aux1) /\
      make_g (FST cfg) t.code = SOME g4 /\
      calls exp' g4 = (exp1,g5) /\ subg g5 g1 /\
      state_rel g1 l1
       (r with
        <|compile_oracle := shift_seq 1 r.compile_oracle;
          code := r.code |++ aux|>)
       (t with
        <|compile_oracle := shift_seq 1 t.compile_oracle;
          code := t.code |++ aux1|>) ∧
      code_inv (SOME g1) (r.code |++ aux) r.compile (shift_seq 1 r.compile_oracle)
               (t.code |++ aux1) t.compile (shift_seq 1 t.compile_oracle) /\
      r.compile_oracle 1 = ((FST g5,other),exp5,aux5) /\
      t.code SUBMAP (t.code |++ aux1) /\
      code_includes (SND g5) (t.code |++ aux1)`,
  strip_tac \\ fs [code_inv_def]
  \\ Cases_on `calls exp' (full_gs 0)` \\ fs []
  \\ imp_res_tac calls_sing \\ rveq \\ fs []
  \\ PairCases_on `progs` \\ fs []
  \\ fs [code_inv_def] \\ rfs []
  \\ pop_assum mp_tac
  \\ pop_assum mp_tac
  \\ simp [Once state_co_def] \\ fs []
  \\ qpat_x_assum `_ = SOME _` mp_tac
  \\ simp [Once state_cc_def] \\ fs []
  \\ PairCases_on `cfg` \\ fs []
  \\ simp [Once compile_inc_def] \\ fs [] \\ rveq \\ fs []
  \\ simp [Once compile_inc_def] \\ fs [] \\ rveq \\ fs []
  \\ `?x1 x2 x3. calls exp' (cfg0,[]) = (x1,x2,x3)` by metis_tac [PAIR] \\ fs []
  \\ drule calls_acc
  \\ `make_g (FST (FST (r.compile_oracle 0))) t.code = SOME (full_gs 0) /\
      Abbrev (cfg0 = FST (FST (r.compile_oracle 0)))` by
   (qpat_x_assum `!k. co_ok _ _ _ k` (qspec_then `1` mp_tac)
    \\ simp [Once co_ok_def] \\ rpt (pairarg_tac \\ fs [markerTheory.Abbrev_def]))
  \\ disch_then (qspec_then `SND (full_gs 0)` mp_tac)
  \\ `(cfg0,SND (full_gs 0)) = (full_gs 0)` by
        (fs [make_g_def] \\ Cases_on `full_gs 0` \\ fs [] \\ rfs [])
  \\ fs [] \\ pop_assum kall_tac
  \\ simp [option_case_eq,pair_case_eq]
  \\ ntac 4 strip_tac \\ rveq \\ fs []
  \\ rename [`t.compile cfg2 (output,_) = SOME xx`]
  \\ PairCases_on `xx` \\ fs []
  \\ fs [shift_seq_def] \\ rveq \\ fs []
  \\ fs [compile_inc_def]
  \\ simp [Once state_co_def] \\ fs []
  \\ Cases_on `r.compile_oracle 1` \\ fs [] \\ rveq \\ fs []
  \\ rename [`r.compile_oracle 1 = ((r1,xx2),r2)`]
  \\ Cases_on `r2` \\ fs [compile_inc_def]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []
  \\ `aux = []` by (first_x_assum (qspec_then `0` mp_tac) \\ fs [])
  \\ fs [FUPDATE_LIST,state_co_def,state_rel_def]
  \\ rewrite_tac [GSYM FUPDATE_LIST]
  \\ qpat_assum `!k. co_ok _ _ _ k` (qspec_then `2` mp_tac)
  \\ CONV_TAC (RATOR_CONV (SIMP_CONV std_ss [Once co_ok_def]))
  \\ fs [compile_inc_def] \\ strip_tac
  \\ `?m. full_gs k = full_gs (m+1)` by
   (reverse (Cases_on `k`) THEN1 (fs [ADD1] \\ metis_tac [])
    \\ qpat_x_assum `includes_state (full_gs 0) _` mp_tac
    \\ fs [includes_state_def] \\ strip_tac
    \\ qpat_assum `!k. co_ok _ _ _ k` (qspec_then `(i+1)+1` assume_tac)
    \\ drule co_ok_IMP_full_gs_eq_shift_seq
    \\ drule co_ok_IMP_make_g
    \\ fs [shift_seq_def] \\ rpt strip_tac
    \\ qexists_tac `i`
    \\ match_mp_tac make_g_make_g_eq \\ fs []
    \\ asm_exists_tac \\ fs []
    \\ asm_exists_tac \\ fs [])
  \\ fs []
  \\ conj_asm1_tac THEN1
   (match_mp_tac subg_trans \\ qexists_tac `full_gs 1`
    \\ qpat_x_assum `co_ok _ _ _ 1n` mp_tac
    \\ once_rewrite_tac [co_ok_def] \\ fs []
    \\ rpt (pairarg_tac \\ fs []) \\ fs []
    \\ fs [shift_seq_def]
    \\ imp_res_tac make_g_wfg
    \\ rpt strip_tac
    \\ match_mp_tac (GEN_ALL make_g_IMP_subg)
    \\ asm_exists_tac \\ fs []
    \\ imp_res_tac calls_subspt \\ fs []
    \\ imp_res_tac calls_code_subset \\ fs [])
  \\ `t.code ⊑ t.code |++ progs1` by (match_mp_tac SUBMAP_FUPDATE_LIST \\ fs [])
  \\ fs [] \\ conj_tac THEN1
   (conj_tac THEN1
     (match_mp_tac (GEN_ALL (MP_CANON LIST_REL_mono))
      \\ first_assum(part_match_exists_tac (last o strip_conj) o concl) \\ rw[]
      \\ match_mp_tac (GEN_ALL (MP_CANON OPTREL_MONO))
      \\ first_assum(part_match_exists_tac (last o strip_conj) o concl) \\ fs []
      \\ rw [] \\ match_mp_tac (GEN_ALL v_rel_SUBMAP) \\ asm_exists_tac \\ fs [])
    \\ match_mp_tac (GEN_ALL (MP_CANON fmap_rel_mono))
    \\ first_assum(part_match_exists_tac (last o strip_conj) o concl) \\ rw[]
    \\ Cases_on `x` \\ fs []
    \\ match_mp_tac (GEN_ALL (MP_CANON LIST_REL_mono))
    \\ first_assum(part_match_exists_tac (last o strip_conj) o concl) \\ rw[]
    \\ match_mp_tac (GEN_ALL v_rel_SUBMAP) \\ asm_exists_tac \\ fs [])
  \\ conj_tac THEN1
   (fs [PULL_EXISTS] \\ qexists_tac `shift_seq 1 full_gs`
    \\ fs [shift_seq_def]
    \\ qexists_tac `m` \\ fs []
    \\ rpt strip_tac
    \\ rename [`co_ok _ _ _ kk`]
    \\ qpat_assum `!k. co_ok _ _ _ k` (qspec_then `kk+1` mp_tac)
    \\ CONV_TAC (RATOR_CONV (SIMP_CONV std_ss [Once co_ok_def]))
    \\ fs [compile_inc_def,shift_seq_def])
  \\ qabbrev_tac `g0 = full_gs 0`
  \\ fs [make_g_def] \\ rveq \\ fs [code_includes_def]
  \\ fs [flookup_update_list_some,ALOOKUP_APPEND,option_case_eq]
  \\ fs [alookup_distinct_reverse]
  \\ rw [] \\ fs []
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs [MEM_MAP] \\ rename [`MEM kk _`]
  \\ PairCases_on `kk` \\ rveq \\ fs []
  \\ fs [MEM_toAList,SUBSET_DEF,PULL_EXISTS,ADD1,FLOOKUP_DEF,domain_lookup]) |> GEN_ALL;
*)

Theorem fv_GENLIST_Var_alt:
   ∀n i tra. fv v (GENLIST_Var tra i n) ⇔ v < n
Proof
  Induct \\ rw [] \\ once_rewrite_tac [GENLIST_Var_def] \\ fs [fv1_thm]
QED

Theorem env_rel_env_exists:
   !vars. EVERY (wfv g1 l1 code) env ==>
           ?env5. env_rel (v_rel g1 l1 code) env env5 0 vars /\
                  LENGTH env5 = LENGTH env
Proof
  strip_tac \\ Induct_on `env`
  THEN1 (fs [env_rel_def] \\ metis_tac [])
  \\ rw [] \\ res_tac \\ fs []
  \\ imp_res_tac v_rel_exists
  \\ qexists_tac `v2::env5`
  \\ fs [env_rel_def]
QED

Theorem evaluate_includes_state:
   !xs env s res s1 g1.
      includes_state g1 s1.compile_oracle /\
      closSem$evaluate (xs,env,s) = (res,s1) ==>
      includes_state g1 s.compile_oracle
Proof
  rw [] \\ drule closPropsTheory.evaluate_code \\ rw []
  \\ fs [includes_state_def,shift_seq_def] \\ rw []
  \\ qexists_tac `k+n` \\ fs []
QED

Theorem evaluate_app_includes_state:
   !xs env s res s1 g1.
      includes_state g1 s1.compile_oracle /\
      closSem$evaluate_app loco x vs s = (res,s1) ==>
      includes_state g1 s.compile_oracle
Proof
  rw [] \\ drule closPropsTheory.evaluate_app_code \\ rw []
  \\ fs [includes_state_def,shift_seq_def] \\ rw []
  \\ qexists_tac `k+n` \\ fs []
QED

Theorem evaluate_app_mono:
   evaluate_app x y z s1 = (vs,s2) ⇒ s1.code ⊑ s2.code
Proof
  strip_tac \\ imp_res_tac evaluate_app_code \\ fs[]
  \\ match_mp_tac SUBMAP_FUPDATE_LIST \\ fs[]
QED

Theorem calls_pure:
   ∀xs g es g1.
    EVERY pure xs /\ calls xs g = (es,g1) ==> EVERY pure es
Proof
  ho_match_mp_tac calls_ind
  \\ rw[calls_def] \\ fs[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
  \\ imp_res_tac calls_sing \\ fs[closLangTheory.pure_def]
  \\ fsrw_tac[ETA_ss][bool_case_eq,closLangTheory.pure_def]
QED

Theorem calls_pure_sing:
   pure x1 /\ calls [x1] g = ([e1],g1) ==> pure e1
Proof
  metis_tac[calls_pure,calls_sing,HD,EVERY_DEF]
QED

(* compiler correctness *)

val t0 = ``t0:('c,'ffi) closSem$state``;

(*
max_print_depth := 8
max_print_depth := 80
max_print_depth := 800
*)

fun say0 pfx s g = (print (pfx ^ ": " ^ s ^ "\n"); ALL_TAC g)
val say = say0 "calls_correct";

Theorem calls_correct:
  (∀tmp xs env1 s0 g0 g env2 ^t0 ys res s l l1 g1.
    tmp = (xs,env1,s0) ∧
    evaluate (xs,env1,s0) = (res,s) ∧
    res ≠ Rerr (Rabort Rtype_error) ∧
    calls xs g0 = (ys,g) ∧
    every_Fn_SOME xs ∧ every_Fn_vs_NONE xs ∧
    EVERY (wfv g1 l1 t0.code) env1 ∧ wfv_state g1 l1 t0.code s0 ∧ wfg g0 ∧
    ALL_DISTINCT (code_locs xs) ∧
    DISJOINT (IMAGE SUC (set (code_locs xs))) (set (MAP FST (SND g0))) ∧
    l = set (code_locs xs) DIFF domain (FST g) ∧
    subg g g1 ∧ l ⊆ l1 ∧ DISJOINT l1 (domain (FST g1)) ∧ wfg g1 ∧
    env_rel (v_rel g1 l1 t0.code) env1 env2 0 (MAP (λx. (0,x)) ys) ∧
    state_rel g1 l1 s0 t0 ∧ code_includes (SND g) t0.code ∧
    code_inv (SOME g1) s0.code s0.compile s0.compile_oracle
                       t0.code t0.compile t0.compile_oracle ∧
    includes_state g1 s.compile_oracle
    ⇒
    ∃ck res' t.
      every_result (EVERY (wfv g1 l1 t.code)) (wfv g1 l1 t.code) res ∧
      wfv_state g1 l1 t.code s ∧
      evaluate (ys,env2,t0 with clock := t0.clock + ck) = (res',t) ∧
      state_rel g1 l1 s t ∧
      code_inv (SOME g1) s.code s.compile s.compile_oracle
                         t.code t.compile t.compile_oracle ∧
      result_rel (LIST_REL (v_rel g1 l1 t.code)) (v_rel g1 l1 t.code) res res') ∧
  (∀loco f args s0 loc g l ^t0 res s f' args'.
    evaluate_app loco f args s0 = (res,s) ∧
    res ≠ Rerr (Rabort Rtype_error) ∧
    wfv g l t0.code f ∧ EVERY (wfv g l t0.code) args ∧
    wfv_state g l t0.code s0 ∧
    wfg g ∧ DISJOINT l (domain (FST g)) ∧
    v_rel g l t0.code f f' ∧ LIST_REL (v_rel g l t0.code) args args' ∧
    state_rel g l s0 t0 ∧
    code_inv (SOME g) s0.code s0.compile s0.compile_oracle
                      t0.code t0.compile t0.compile_oracle ∧
    includes_state g s.compile_oracle ⇒
    ∃ck res' t.
      every_result (EVERY (wfv g l t.code)) (wfv g l t.code) res ∧
      wfv_state g l t.code s ∧
      evaluate_app loco f' args' (t0 with clock := t0.clock + ck) = (res',t) ∧
      state_rel g l s t ∧
      code_inv (SOME g) s.code s.compile s.compile_oracle
                        t.code t.compile t.compile_oracle ∧
      result_rel (LIST_REL (v_rel g l t.code)) (v_rel g l t.code) res res')
Proof
  ho_match_mp_tac evaluate_ind
  \\ conj_tac >- (
    rw[]
    \\ qexists_tac`0`
    \\ fs[calls_def,evaluate_def]
    \\ rveq \\ fs[evaluate_def]
    \\ fs[code_locs_def]
    \\ simp[RIGHT_EXISTS_IMP_THM]
    \\ metis_tac[SUBSET_REFL])
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
      \\ rpt (disch_then drule \\ fs []))
    \\ simp [PULL_FORALL]
    \\ disch_then (qspecl_then [`env2`] mp_tac)
    \\ simp [AND_IMP_INTRO]
    \\ impl_tac THEN1
     (imp_res_tac code_includes_subg \\ fs []
      \\ reverse conj_tac THEN1
       (fs [semanticPrimitivesTheory.result_case_eq,pair_case_eq]
        \\ rveq \\ fs []
        \\ drule evaluate_includes_state \\ fs []
        \\ disch_then drule \\ fs [])
      \\ fs [env_rel_def] \\ IF_CASES_TAC \\ fs []
      \\ metis_tac [])
    \\ strip_tac
    \\ reverse (Cases_on `q`) \\ fs [] \\ rveq \\ fs []
    THEN1 (fs [evaluate_def] \\ rw [] \\ qexists_tac `ck` \\ fs [])
    \\ Cases_on `evaluate (y::xs,env,r)` \\ fs []
    \\ `q ≠ Rerr (Rabort Rtype_error)` by (CCONTR_TAC \\ fs []) \\ fs []
    \\ first_x_assum drule \\ fs []
    \\ `ALL_DISTINCT (code_locs (y::xs))` by
          (fs [code_locs_def,ALL_DISTINCT_APPEND] \\ NO_TAC)
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
    \\ `EVERY (wfv g1 l1 t.code) env` by
     (match_mp_tac (GEN_ALL EVERY_wfv_SUBMAP) \\ asm_exists_tac
      \\ imp_res_tac evaluate_mono \\ fs [])
    \\ disch_then drule \\ fs []
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
    \\ fs [AND_IMP_INTRO] \\ impl_tac THEN1
     (fs [code_locs_def,ALL_DISTINCT_APPEND,wfg_def] \\ rfs []
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ fs [DISJOINT_IMAGE_SUC] \\ fs [IN_DISJOINT]
      \\ CCONTR_TAC \\ fs [] \\ rfs [IMAGE_SUC_SUBSET_UNION]
      \\ fs [SUBSET_DEF]
      \\ TRY(first_x_assum drule) \\ CCONTR_TAC \\ fs [] \\ metis_tac [])
    \\ fs [PULL_FORALL]
    \\ disch_then (qspecl_then [`env2`] mp_tac)
    \\ fs [AND_IMP_INTRO,GSYM CONJ_ASSOC]
    \\ `t0.code SUBMAP t.code` by (imp_res_tac evaluate_mono \\ fs [])
    \\ impl_tac THEN1
     (conj_tac THEN1
       (drule env_rel_SUBMAP \\ disch_then drule
        \\ fs [env_rel_def] \\ IF_CASES_TAC \\ fs []
        \\ ntac 3 strip_tac
        \\ first_x_assum match_mp_tac \\ fs [])
      \\ qpat_x_assum `_ = (Rval _,t)` assume_tac
      \\ drule evaluate_mono \\ fs [] \\ strip_tac
      \\ imp_res_tac code_includes_SUBMAP \\ fs []
      \\ fs [semanticPrimitivesTheory.result_case_eq,pair_case_eq])
    \\ strip_tac
    \\ qpat_x_assum `_ = (Rval _,t)` assume_tac
    \\ drule evaluate_add_clock \\ fs []
    \\ disch_then (qspec_then `ck'` assume_tac)
    \\ fs [PULL_EXISTS]
    \\ qexists_tac `ck+ck'` \\ fs [AC ADD_COMM ADD_ASSOC]
    \\ fs [evaluate_def]
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_SING \\ fs [] \\ rveq
    \\ imp_res_tac evaluate_mono \\ fs []
    \\ imp_res_tac SUBMAP_TRANS \\ fs []
    \\ imp_res_tac wfv_SUBMAP \\ fs []
    \\ imp_res_tac v_rel_SUBMAP \\ fs [])
  (* Var *)
  \\ conj_tac >- (
    say "Var"
    \\ fs [evaluate_def,calls_def] \\ rw []
    \\ fs[env_rel_def,fv1_thm]
    \\ every_case_tac
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ qexists_tac `0` \\ fs []
    \\ fs [LIST_REL_EL_EQN,EVERY_MEM,MEM_EL,PULL_EXISTS,RIGHT_EXISTS_IMP_THM])
  (* If *)
  \\ conj_tac >- (
    say "If"
    \\ fs [evaluate_def,calls_def] \\ rw []
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
    \\ `includes_state g1 r.compile_oracle` by
     (fs [semanticPrimitivesTheory.result_case_eq,pair_case_eq,bool_case_eq]
      \\ metis_tac [evaluate_includes_state])
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
    \\ simp [PULL_FORALL]
    \\ disch_then (qspecl_then [`env2`] mp_tac)
    \\ simp [AND_IMP_INTRO]
    \\ impl_tac THEN1
     (imp_res_tac code_includes_subg
      \\ fs [env_rel_def] \\ IF_CASES_TAC \\ fs []
      \\ ntac 2 strip_tac
      \\ first_x_assum match_mp_tac \\ pop_assum mp_tac
      \\ EVAL_TAC \\ fs [])
    \\ strip_tac
    \\ reverse (Cases_on `q`) \\ fs [] \\ rveq \\ fs []
    THEN1 (fs [evaluate_def] \\ rw [] \\ qexists_tac `ck` \\ fs [])
    \\ `?a1. a = [a1]` by (imp_res_tac evaluate_SING \\ rw [])
    \\ rveq \\ fs []
    \\ Cases_on `a1 = Boolv T` \\ fs [] \\ rveq THEN1
     (first_x_assum drule \\ fs []
      \\ `EVERY (wfv g1 l1 t.code) env` by
        (match_mp_tac (GEN_ALL EVERY_wfv_SUBMAP) \\ asm_exists_tac \\ fs []
         \\ imp_res_tac evaluate_mono \\ fs [])
      \\ `wfv_state g1 l1 t.code r` by
        (match_mp_tac (GEN_ALL wfv_state_SUBMAP) \\ asm_exists_tac \\ fs []
         \\ imp_res_tac evaluate_mono \\ fs [])
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
      \\ simp [PULL_FORALL]
      \\ rename [`env_rel (v_rel g1 l1 t0.code) env env2 0 [(0,If args y7 y8 y)]`]
      \\ `env_rel (v_rel g1 l1 t.code) env env2 0 [(0,If args y7 y8 y)]` by
        (match_mp_tac (GEN_ALL env_rel_SUBMAP) \\ asm_exists_tac \\ fs []
         \\ imp_res_tac evaluate_mono \\ fs [])
      \\ disch_then (qspecl_then [`env2`] mp_tac)
      \\ rewrite_tac [GSYM AND_IMP_INTRO]
      \\ impl_tac THEN1
       (imp_res_tac subg_trans \\ imp_res_tac code_includes_subg
        \\ fs [env_rel_def] \\ IF_CASES_TAC \\ fs []
        \\ ntac 2 strip_tac \\ first_x_assum match_mp_tac
        \\ pop_assum mp_tac \\ EVAL_TAC \\ fs [])
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
      \\ `EVERY (wfv g1 l1 t.code) env` by
        (match_mp_tac (GEN_ALL EVERY_wfv_SUBMAP) \\ asm_exists_tac \\ fs []
         \\ imp_res_tac evaluate_mono \\ fs [])
      \\ `wfv_state g1 l1 t.code r` by
        (match_mp_tac (GEN_ALL wfv_state_SUBMAP) \\ asm_exists_tac \\ fs []
         \\ imp_res_tac evaluate_mono \\ fs [])
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
      \\ simp [PULL_FORALL]
      \\ rename [`env_rel (v_rel g1 l1 t0.code) env env2 0 [(0,If args y7 y8 y)]`]
      \\ `env_rel (v_rel g1 l1 t.code) env env2 0 [(0,If args y7 y8 y)]` by
        (match_mp_tac (GEN_ALL env_rel_SUBMAP) \\ asm_exists_tac \\ fs []
         \\ imp_res_tac evaluate_mono \\ fs [])
      \\ disch_then (qspecl_then [`env2`] mp_tac)
      \\ rewrite_tac [GSYM AND_IMP_INTRO]
      \\ impl_tac THEN1
       (imp_res_tac subg_trans \\ imp_res_tac code_includes_subg
        \\ fs [env_rel_def] \\ IF_CASES_TAC \\ fs []
        \\ ntac 2 strip_tac \\ first_x_assum match_mp_tac
        \\ pop_assum mp_tac \\ EVAL_TAC \\ fs [])
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
    say "Let"
    \\ fs [evaluate_def,calls_def] \\ rw []
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
    \\ `includes_state g1 r.compile_oracle` by
     (fs [semanticPrimitivesTheory.result_case_eq,pair_case_eq,bool_case_eq]
      \\ metis_tac [evaluate_includes_state])
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
    \\ simp [PULL_FORALL]
    \\ disch_then (qspecl_then [`env2`] mp_tac)
    \\ simp [AND_IMP_INTRO]
    \\ impl_tac THEN1
     (imp_res_tac code_includes_subg
      \\ fs [env_rel_def] \\ IF_CASES_TAC \\ fs []
      \\ ntac 2 strip_tac \\ first_x_assum match_mp_tac \\ fs []
      \\ pop_assum mp_tac \\ fs [EXISTS_MAP]
      \\ EVAL_TAC \\ fs [fv_exists]
      \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
    \\ strip_tac
    \\ reverse (Cases_on `q`) \\ fs [] \\ rveq \\ fs []
    THEN1 (fs [evaluate_def] \\ rw [] \\ qexists_tac `ck` \\ fs [])
    \\ first_x_assum drule \\ fs []
    \\ `ALL_DISTINCT (code_locs [x2])` by
          (fs [code_locs_def,ALL_DISTINCT_APPEND] \\ NO_TAC)
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
    \\ `EVERY (wfv g1 l1 t.code) env` by
        (match_mp_tac (GEN_ALL EVERY_wfv_SUBMAP) \\ asm_exists_tac \\ fs []
         \\ imp_res_tac evaluate_mono \\ fs [])
    \\ rename [`env_rel (v_rel g1 l1 t0.code) env env2 0 [(0,Let x1 e1 y)]`]
    \\ `env_rel (v_rel g1 l1 t.code) env env2 0 [(0,Let x1 e1 y)]` by
        (match_mp_tac (GEN_ALL env_rel_SUBMAP) \\ asm_exists_tac \\ fs []
         \\ imp_res_tac evaluate_mono \\ fs [])
    \\ disch_then drule \\ fs []
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
    \\ fs [AND_IMP_INTRO] \\ impl_tac THEN1
     (fs [code_locs_def,ALL_DISTINCT_APPEND,wfg_def] \\ rfs []
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ fs [DISJOINT_IMAGE_SUC] \\ fs [IN_DISJOINT]
      \\ CCONTR_TAC \\ fs [] \\ rfs [IMAGE_SUC_SUBSET_UNION]
      \\ fs [SUBSET_DEF]
      \\ TRY(first_x_assum drule) \\ CCONTR_TAC \\ fs [] \\ metis_tac [])
    \\ fs [PULL_FORALL]
    \\ disch_then (qspecl_then [`v' ++ env2`] mp_tac)
    \\ simp [AND_IMP_INTRO]
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
    say "Raise"
    \\ fs [evaluate_def,calls_def] \\ rw []
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ fs [evaluate_def]
    \\ `[HD e1] = e1` by (imp_res_tac calls_sing \\ fs [])
    \\ fs [dec_clock_def] \\ pop_assum kall_tac
    \\ Cases_on `evaluate ([x1],env,s)` \\ fs []
    \\ `q ≠ Rerr (Rabort Rtype_error)` by (CCONTR_TAC \\ fs []) \\ fs []
    \\ `includes_state g1 r.compile_oracle` by
     (fs [semanticPrimitivesTheory.result_case_eq,pair_case_eq,bool_case_eq]
      \\ metis_tac [evaluate_includes_state])
    \\ fs [GSYM PULL_EXISTS,PUSH_EXISTS_IMP,GSYM PULL_FORALL]
    \\ first_x_assum drule \\ fs [code_locs_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ fs [GSYM PULL_FORALL] \\ strip_tac
    \\ first_x_assum (qspecl_then [`env2`] mp_tac) \\ fs [AND_IMP_INTRO]
    \\ impl_tac THEN1
     (imp_res_tac calls_sing \\ fs [env_rel_def]
      \\ IF_CASES_TAC \\ fs [] \\ ntac 2 strip_tac
      \\ first_x_assum match_mp_tac
      \\ pop_assum mp_tac \\ EVAL_TAC)
    \\ `[HD e1] = e1` by (imp_res_tac calls_sing \\ fs [])
    \\ pop_assum SUBST_ALL_TAC
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_SING \\ rveq \\ fs []
    \\ strip_tac \\ fs []
    \\ qexists_tac `ck` \\ fs []
    \\ every_case_tac
    \\ fs [semanticPrimitivesPropsTheory.result_rel_def,PULL_EXISTS])
  (* Handle *)
  \\ conj_tac >- (
    say "Handle"
    \\ fs [evaluate_def,calls_def] \\ rw []
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
    \\ `includes_state g1 r.compile_oracle` by
     (fs [semanticPrimitivesTheory.result_case_eq,pair_case_eq,bool_case_eq,
          semanticPrimitivesTheory.error_result_case_eq]
      \\ metis_tac [evaluate_includes_state])
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
    \\ simp [PULL_FORALL]
    \\ disch_then (qspecl_then [`env2`] mp_tac)
    \\ simp [AND_IMP_INTRO]
    \\ impl_tac THEN1
     (imp_res_tac code_includes_subg
      \\ fs [env_rel_def] \\ IF_CASES_TAC \\ fs []
      \\ ntac 2 strip_tac \\ first_x_assum match_mp_tac \\ fs []
      \\ pop_assum mp_tac \\ fs [EXISTS_MAP]
      \\ EVAL_TAC \\ fs [fv_exists]
      \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    THEN1 (fs [evaluate_def] \\ rw [] \\ qexists_tac `ck` \\ fs [])
    \\ reverse (Cases_on `e`) \\ rveq \\ fs [] \\ rveq \\ fs []
    THEN1 (fs [evaluate_def] \\ rw [] \\ qexists_tac `ck` \\ fs [])
    \\ strip_tac
    \\ first_x_assum drule \\ fs []
    \\ `ALL_DISTINCT (code_locs [x2])` by
          (fs [code_locs_def,ALL_DISTINCT_APPEND] \\ NO_TAC)
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO] \\ rveq \\ fs []
    \\ disch_then drule \\ fs []
    \\ `EVERY (wfv g1 l1 t.code) env` by
        (match_mp_tac (GEN_ALL EVERY_wfv_SUBMAP) \\ asm_exists_tac \\ fs []
         \\ imp_res_tac evaluate_mono \\ fs [])
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
    \\ fs [AND_IMP_INTRO] \\ impl_tac THEN1
     (fs [code_locs_def,ALL_DISTINCT_APPEND,wfg_def] \\ rfs []
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ fs [DISJOINT_IMAGE_SUC] \\ fs [IN_DISJOINT]
      \\ CCONTR_TAC \\ fs [] \\ rfs [IMAGE_SUC_SUBSET_UNION]
      \\ fs [SUBSET_DEF]
      \\ TRY(first_x_assum drule) \\ CCONTR_TAC \\ fs [] \\ metis_tac [])
    \\ fs [PULL_FORALL,AND_IMP_INTRO]
    \\ `env_rel (v_rel g1 l1 t.code) env env2 0 [(0,Handle v5 y' y)]` by
        (match_mp_tac (GEN_ALL env_rel_SUBMAP) \\ asm_exists_tac \\ fs []
         \\ imp_res_tac evaluate_mono \\ fs [])
    \\ disch_then (qspecl_then [`v'::env2`] mp_tac)
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
  \\ conj_tac >- (
    say "Op"
    \\ fs [evaluate_def,calls_def] \\ rw []
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ fs [evaluate_def]
    \\ Cases_on `evaluate (xs,env,s)` \\ fs []
    \\ `q ≠ Rerr (Rabort Rtype_error)` by (CCONTR_TAC \\ fs []) \\ fs []
    \\ `includes_state g1 r.compile_oracle` by
     (fs [semanticPrimitivesTheory.result_case_eq,option_case_eq,
          pair_case_eq,bool_case_eq,do_install_def,list_case_eq]
      \\ imp_res_tac do_app_const \\ fs []
      \\ TRY pairarg_tac \\ fs []
      \\ fs [semanticPrimitivesTheory.result_case_eq,option_case_eq,
           pair_case_eq,bool_case_eq,do_install_def,list_case_eq]
      \\ rveq \\ fs []
      \\ TRY (drule evaluate_includes_state \\ disch_then drule)
      \\ fs [includes_state_def,shift_seq_def]
      \\ imp_res_tac do_app_const \\ fs []
      \\ metis_tac [])
    \\ first_x_assum drule \\ fs [code_locs_def]
    \\ rpt (disch_then drule \\ fs[])
    \\ fs [GSYM PULL_EXISTS,PUSH_EXISTS_IMP,GSYM PULL_FORALL]
    \\ disch_then (qspecl_then [`env2`] mp_tac)
    \\ impl_tac THEN1
     (fs [env_rel_def] \\ IF_CASES_TAC \\ fs []
      \\ ntac 2 strip_tac
      \\ first_x_assum match_mp_tac
      \\ pop_assum mp_tac
      \\ fs [EXISTS_MAP,fv_exists]
      \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs []
      \\ EVAL_TAC \\ fs [fv_exists])
    \\ strip_tac
    \\ reverse (Cases_on `q`) \\ fs []
    THEN1 (rw [] \\ qexists_tac `ck` \\ fs [])
    \\ reverse (Cases_on `op = Install`) THEN1
     (fs [] \\ reverse (Cases_on `do_app op (REVERSE a) r`) \\ fs []
      THEN1
       (rveq \\ mp_tac (Q.GENL [`v`,`t`] do_app_thm) \\ fs []
        \\ Cases_on `e` \\ fs [] \\ strip_tac \\ rveq \\ fs []
        \\ rename [`_ = Rerr (Rabort aa)`] \\ Cases_on `aa` \\ fs []
        \\ fs[] \\ rw[]
        \\ first_x_assum drule \\ fs []
        \\ simp[] \\ strip_tac \\ fs[]
        \\ qexists_tac`ck` \\ simp[] \\ rw[])
      \\ rename1 `do_app op (REVERSE a) r = Rval z`
      \\ PairCases_on `z` \\ fs [] \\ rveq
      \\ mp_tac (Q.GENL [`t`,`v`] do_app_thm) \\ fs [] \\ rpt strip_tac
      \\ qexists_tac `ck` \\ fs []
      \\ first_x_assum (qspecl_then [`t`,`v'`] mp_tac) \\ fs []
      \\ strip_tac \\ pop_assum mp_tac \\ fs []
      \\ imp_res_tac do_app_const \\ fs [])
    \\ rveq \\ fs []
    (*
    \\ fs [pair_case_eq]
    \\ rveq \\ fs []
    \\ qpat_x_assum `do_install _ r = _` mp_tac
    \\ Cases_on `v = Rerr (Rabort Rtype_error)` \\ fs []
    \\ simp [Once do_install_def]
    \\ simp [option_case_eq,list_case_eq,PULL_EXISTS,pair_case_eq,bool_case_eq]
    \\ pairarg_tac
    \\ fs [SWAP_REVERSE_SYM,bool_case_eq,option_case_eq,pair_case_eq,PULL_EXISTS]
    \\ rpt gen_tac \\ strip_tac \\ rveq \\ fs []
    \\ `aux = []` by
      (fs [code_inv_def] \\ first_x_assum (qspec_then `0` mp_tac) \\ fs [])
    THEN1
     (rpt strip_tac \\ fs [] \\ rveq \\ fs []
      \\ imp_res_tac v_to_bytes_thm
      \\ imp_res_tac v_to_words_thm
      \\ fs [] \\ rveq \\ fs []
      \\ `?cfg' progs. t.compile_oracle 0 = (cfg',progs)` by metis_tac [PAIR]
      \\ drule code_rel_state_rel_install
      \\ fs [shift_seq_def]
      \\ rpt (disch_then drule) \\ strip_tac
      \\ `exp1 <> []` by
        (CCONTR_TAC \\ imp_res_tac calls_length \\ fs [] \\ rveq \\ fs [])
      \\ qabbrev_tac `t1 = t with
          <|clock := 0; compile_oracle := shift_seq 1 t.compile_oracle;
            code := t.code |++ aux1|>`
      \\ qexists_tac `ck`
      \\ qexists_tac `t1`
      \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs []
      \\ qunabbrev_tac `t1` \\ fs [FUPDATE_LIST]
      \\ conj_tac THEN1
       (`wfv_state g1 l1 t.code
           (r with
            <| clock := 0; compile_oracle := shift_seq 1 r.compile_oracle;
               code := r.code |>)` by fs [wfv_state_def,shift_seq_def]
        \\ fs [shift_seq_def,FUPDATE_LIST]
        \\ match_mp_tac wfv_state_SUBMAP \\ asm_exists_tac \\ fs [])
      \\ fs [do_install_def]
      \\ fs [shift_seq_def]
      \\ `t.clock = 0` by fs [state_rel_def] \\ fs []
      \\ rfs [state_rel_def,FUPDATE_LIST])
    \\ rveq \\ fs [FUPDATE_LIST,shift_seq_def]
    \\ imp_res_tac v_to_bytes_thm
    \\ imp_res_tac v_to_words_thm
    \\ fs [] \\ rveq \\ fs []
    \\ ntac 2 (qpat_x_assum `!x._` kall_tac)
    \\ `?x23 x34. t.compile_oracle 0 = (x23,x34)` by metis_tac [PAIR]
    \\ drule code_rel_state_rel_install
    \\ `includes_state g1 (shift_seq 1 r.compile_oracle)` by
     (qpat_x_assum `includes_state g1 r.compile_oracle` kall_tac
      \\ drule evaluate_includes_state
      \\ fs [case_eq_thms,pair_case_eq] \\ rveq \\ fs []
      \\ disch_then drule
      \\ fs [shift_seq_def])
    \\ fs [shift_seq_def]
    \\ rpt (disch_then drule) \\ strip_tac
    \\ imp_res_tac make_g_wfg
    \\ `t.clock <> 0` by fs [state_rel_def] \\ fs []
    \\ fs [state_rel_def,FUPDATE_LIST]
    \\ Cases_on `evaluate
              (exps,[],
               r with
               <|clock := t.clock − 1;
                 compile_oracle := (λi. r.compile_oracle (i + 1));
                 code := FEMPTY|>)` \\ fs [] \\ rveq \\ fs []
    \\ `q ≠ Rerr (Rabort Rtype_error)` by (every_case_tac \\ fs [] \\ rveq \\ fs [])
    \\ fs []
    \\ first_x_assum drule
    \\ disch_then (qspecl_then [`[]`,`t with
          <|clock := t.clock − 1;
            compile_oracle := (λi. t.compile_oracle (i + 1));
            code := FOLDL $|+ t.code aux1|>`,`l1`,`g1`] mp_tac)
    \\ simp [] \\ rfs []
    \\ `exp1 <> []` by
      (CCONTR_TAC \\ imp_res_tac calls_length \\ fs [] \\ rveq \\ fs [])
    \\ reverse impl_tac THEN1
     (strip_tac \\ fs [] \\ rveq \\ fs []
      \\ qpat_x_assum `_ = (Rval _,t)` assume_tac
      \\ drule evaluate_add_clock
      \\ disch_then (qspec_then `ck'` mp_tac) \\ fs [] \\ strip_tac
      \\ qexists_tac `ck+ck'` \\ fs [] \\ rfs []
      \\ fs [do_install_def,shift_seq_def,FUPDATE_LIST]
      \\ TOP_CASE_TAC \\ fs []
      \\ FULL_CASE_TAC \\ fs [] \\ rveq \\ fs []
      \\ imp_res_tac evaluate_IMP_LENGTH
      \\ rename [`EVERY _ aa`]
      \\ `aa = [] ∨ ∃x l. aa = SNOC x l` by metis_tac [SNOC_CASES]
      THEN1 fs [] \\ full_simp_tac std_ss [LAST_SNOC] \\ fs [EVERY_SNOC]
      \\ `a = [] ∨ ∃x l. a = SNOC x l` by metis_tac [SNOC_CASES]
      THEN1 fs [] \\ full_simp_tac std_ss [LAST_SNOC] \\ fs [EVERY_SNOC]
      \\ fs [LIST_REL_SNOC])
    \\ simp [env_rel_def] \\ rveq \\ fs []
    \\ ntac 2 (conj_tac THEN1 (fs [code_inv_def]
               \\ rpt (first_x_assum (qspec_then `0` mp_tac)) \\ fs []))
    \\ conj_tac THEN1
     (`wfv_state g1 l1 t.code (r with
        <|clock := t.clock − 1;
          compile_oracle := (λi. r.compile_oracle (i + 1)); code := FEMPTY|>)`
            by fs [code_inv_def,wfv_state_def]
      \\ match_mp_tac wfv_state_SUBMAP
      \\ asm_exists_tac \\ fs [GSYM FUPDATE_LIST])
    \\ rpt (conj_tac THEN1 (fs [code_inv_def]
               \\ rpt (first_x_assum (qspec_then `0` mp_tac)) \\ fs []))
    \\ fs [correct_l_def]
    \\ fs [SUBSET_DEF]
    \\ fs [code_inv_def]
    \\ `FST cfg = FST g4` by (fs [make_g_def] \\ rveq \\ fs []) \\ fs []
    \\ qpat_x_assum `∀k. co_ok t.code r.compile_oracle _ k` mp_tac
    \\ disch_then (qspec_then `1` mp_tac)
    \\ once_rewrite_tac [co_ok_def] \\ fs [compile_inc_def]
    \\ qpat_x_assum `includes_state g1 r.compile_oracle` mp_tac
    \\ simp [includes_state_def] \\ strip_tac \\ rveq
    \\ `?y1 y2 y3. (calls exps (FST g4,[])) = (y1,y2,y3)` by metis_tac [PAIR] \\ fs []
    \\ `r' = s'` by (every_case_tac \\ fs []) \\ rveq \\ fs []
    \\ drule calls_acc
    \\ disch_then (qspec_then `SND g4` mp_tac) \\ fs []
    \\ strip_tac \\ rveq \\ fs []
    \\ rpt strip_tac
    THEN1 (imp_res_tac make_g_wfg \\ rveq \\ fs []
           \\ fs [wfg_def,DISJOINT_IMAGE_SUC])
    \\ TRY (first_x_assum drule \\ disch_then drule \\ fs [])
    \\ qpat_x_assum `includes_state g1 s'.compile_oracle` mp_tac
    \\ simp [includes_state_def] \\ strip_tac
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_code \\ rw [] \\ fs [shift_seq_def]
    \\ metis_tac []*))
  (* Fn *)
  \\ conj_tac >- (
    say "Fn"
    \\ rw[evaluate_def]
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
    \\ asm_exists_tac \\ fs []
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
    \\ fs[calls_list_def,GSYM ADD1]
    \\ imp_res_tac state_rel_max_app \\ fs[]
    \\ fs[env_rel_def,fv1_thm]
    \\ IF_CASES_TAC \\ fs [fv_GENLIST_Var_alt])
  (* Letrec *)
  \\ conj_tac >- (
    say "Letrec"
    \\ rw[evaluate_def] \\ fs[IS_SOME_EXISTS]
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
    \\ `ys = [Letrec (if b then tr § 0 else tr ) (SOME x) NONE
                     (if b then fns2 else fns0) (if b then b2 else b0)]`
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
    \\ qunabbrev_tac`bo`\\fs[]
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
      \\ disch_then (qspecl_then [`env2`] mp_tac)
      \\ fs [] \\ disch_then match_mp_tac
      \\ fs[env_rel_def,fv1_thm])
    \\ first_x_assum(qspec_then`if b then g2 else g3`mp_tac)
    \\ disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars["ys'","g'"])))
    \\ disch_then(qspecl_then[`if b then [b2] else [b0]`,`if b then g4 else g5`]mp_tac)
    \\ simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM]
    \\ impl_tac >- rw[]
    \\ disch_then(qspecl_then[`g1`,`l1`]mp_tac o
         CONV_RULE(RESORT_FORALL_CONV(List.rev)))
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
    \\ disch_then (qspec_then `t0` mp_tac) \\ fs []
    \\ `∀i. i < LENGTH fns ⇒ recclosure_rel g1 l1 t0.code x fns fns4`
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
      \\ rewrite_tac [CONJ_ASSOC]
      \\ (reverse conj_tac THEN1
           (match_mp_tac (GEN_ALL (MP_CANON code_includes_subg))
            \\ asm_exists_tac \\ fs []))
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
    \\ disch_then(qspecl_then[`env3`]mp_tac)
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
      \\ qpat_x_assum `!x:num. _` kall_tac
      \\ first_x_assum(qspec_then`a - LENGTH fns`mp_tac)
      \\ impl_tac THEN1 (rw [] \\ fs [fv1_thm])
      \\ fs [])
    \\ simp [AND_IMP_INTRO]
    \\ impl_tac >- (FULL_CASE_TAC \\ fs[])
    \\ strip_tac
    \\ qexists_tac`ck` \\ simp[]
    \\ simp[RIGHT_EXISTS_AND_THM,RIGHT_EXISTS_IMP_THM]
    \\ rpt strip_tac
    \\ imp_res_tac state_rel_max_app
    \\ FULL_CASE_TAC \\ fs[])
  (* App *)
  \\ conj_tac >- (
    say "App"
    \\ rw[evaluate_def,calls_def]
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
    \\ strip_tac
    \\ `includes_state g1 s.compile_oracle /\
        includes_state g1 r.compile_oracle` by
     (fs [semanticPrimitivesTheory.result_case_eq,pair_case_eq,bool_case_eq]
      \\ metis_tac [evaluate_includes_state,evaluate_app_includes_state])
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
    \\ `(~(IS_SOME loco /\
          IS_SOME (lookup (case loco of NONE => 0 | SOME loc => loc) (FST g)) /\
          pure x1) ==> env_rel (v_rel g1 l1 t0.code) env env2 0 (MAP (λx. (0,x)) e1))`
    by (every_case_tac \\ fs []
        \\ imp_res_tac calls_sing \\ fs [] \\ rveq \\ fs []
        \\ qpat_x_assum `env_rel _ _ _ _ _` mp_tac
        \\ simp [env_rel_def,fv1_thm,EXISTS_MAP,fv_exists]
        \\ IF_CASES_TAC \\ fs [])
    \\ pop_assum mp_tac
    \\ `env_rel (v_rel g1 l1 t0.code) env env2 0 (MAP (λx. (0,x)) es)`
    by (every_case_tac \\ fs []
        \\ imp_res_tac calls_sing \\ fs [] \\ rveq \\ fs []
        \\ qpat_x_assum `env_rel _ _ _ _ _` mp_tac
        \\ simp [env_rel_def,fv1_thm,EXISTS_MAP,fv_exists]
        \\ IF_CASES_TAC \\ fs []
        \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
    \\ strip_tac
    \\ qpat_x_assum `_ = (_,_)` mp_tac
    \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      strip_tac \\ rveq \\ rfs[]
      \\ first_x_assum drule \\ fs[DISJOINT_SYM,ALL_DISTINCT_APPEND]
      \\ rpt(disch_then drule)
      \\ disch_then(qspecl_then[`env2`]mp_tac)
      \\ impl_tac
      >- (
        conj_tac >- metis_tac[subg_trans]
        \\ simp[]
        \\ reverse conj_tac THEN1 metis_tac [code_includes_subg]
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
      \\ `state_rel g1 l1 r t ∧ code_includes (SND g') t0.code`
      by metis_tac[code_includes_subg]
      \\ fs[] \\ rfs[] \\ rveq
      \\ `exc_rel (v_rel g1 l1 t.code) e e'`
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
    \\ disch_then(qspecl_then[`env2`]mp_tac)
    \\ impl_tac
    >- (
      conj_tac >- metis_tac[subg_trans]
      \\ simp[]
      \\ reverse conj_tac THEN1 metis_tac [code_includes_subg]
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
    \\ qpat_x_assum`_ = (ys,_)`mp_tac
    \\ qmatch_goalsub_abbrev_tac`COND b`
    \\ reverse IF_CASES_TAC \\ fs[] >- (
      `env_rel (v_rel g1 l1 t0.code) env env2 0 (MAP (λx. (0,x)) e1)` by
         (first_x_assum match_mp_tac \\ fs [markerTheory.Abbrev_def])
      \\ strip_tac
      \\ disch_then(qspecl_then[`env2`,`t`]mp_tac)
      \\ disch_then(qspecl_then[`l1`,`g1`]mp_tac)
      \\ `set (code_locs [x1]) DIFF domain (FST g) ⊆ l1` by fs [SUBSET_DEF]
      \\ `code_includes (SND g) t.code` by
           (imp_res_tac evaluate_mono \\ fs[]
            \\ fs[env_rel_def,fv1_thm]
            \\ metis_tac[code_includes_SUBMAP])
      \\ `EVERY (wfv g1 l1 t.code) env` by
        (match_mp_tac (GEN_ALL EVERY_wfv_SUBMAP) \\ asm_exists_tac \\ fs []
         \\ imp_res_tac evaluate_mono \\ fs [])
      \\ `env_rel (v_rel g1 l1 t.code) env env2 0 (MAP (λx. (0,x)) e1)` by
        (match_mp_tac (GEN_ALL env_rel_SUBMAP) \\ asm_exists_tac \\ fs []
         \\ imp_res_tac evaluate_mono \\ fs [])
      \\ fs []
      \\ strip_tac \\ rveq
      \\ strip_tac \\ rveq
      \\ `includes_state g1 r'.compile_oracle` by
       (fs [semanticPrimitivesTheory.result_case_eq,pair_case_eq,bool_case_eq]
        \\ metis_tac [evaluate_includes_state,evaluate_app_includes_state])
      \\ fs [] \\ rveq
      \\ qpat_x_assum `_ = (_,_)` mp_tac
      \\ simp[evaluate_def]
      \\ imp_res_tac calls_length
      \\ simp[]
      \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
      \\ rveq \\ fs[]
      \\ strip_tac
      \\ qpat_x_assum`_ ⇒ _`mp_tac
      \\ impl_tac THEN1
         (imp_res_tac evaluate_mono \\ fs[]
          \\ fs[env_rel_def,fv1_thm]
          \\ metis_tac[code_includes_SUBMAP])
      \\ strip_tac \\ rveq \\ fs []
      \\ qpat_x_assum `_ = _` mp_tac
      \\ reverse BasicProvers.TOP_CASE_TAC \\ fs []
      >- (
        strip_tac \\ rveq \\ fs[]
        \\ simp[RIGHT_EXISTS_IMP_THM,RIGHT_EXISTS_AND_THM]
        \\ fs[] \\ rfs[] \\ rveq \\ fs []
        \\ qpat_x_assum`evaluate(es,env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
        \\ disch_then(qspec_then`ck'`mp_tac) \\ simp[] \\ strip_tac
        \\ fs [PULL_EXISTS]
        \\ qexists_tac`ck+ck'` \\ fs[])
      \\ imp_res_tac evaluate_SING \\ rveq \\ fs [] \\ rveq \\ fs []
      \\ strip_tac \\ fs[] \\ rfs[]
      \\ first_x_assum drule
      \\ `EVERY (wfv g1 l1 t'.code) a` by
        (match_mp_tac (GEN_ALL EVERY_wfv_SUBMAP) \\ asm_exists_tac \\ fs []
         \\ imp_res_tac evaluate_mono \\ fs [])
      \\ `wfv_state g1 l1 t'.code r'` by
        (match_mp_tac (GEN_ALL wfv_state_SUBMAP) \\ asm_exists_tac \\ fs []
         \\ imp_res_tac evaluate_mono \\ fs [])
      \\ rename [`LIST_REL (v_rel _ _ _) a v55`]
      \\ `LIST_REL (v_rel g1 l1 t'.code) a v55` by
        (match_mp_tac (GEN_ALL LIST_REL_v_rel_SUBMAP) \\ asm_exists_tac \\ fs []
         \\ imp_res_tac evaluate_mono \\ fs [])
      \\ rpt(disch_then drule)
      \\ strip_tac \\ fs []
      \\ qmatch_assum_rename_tac`LIST_REL (v_rel _ _ _) ev1 ev2`
      \\ qpat_x_assum`evaluate(es,env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
      \\ disch_then(qspec_then`ck'+ck''`mp_tac) \\ simp[] \\ strip_tac
      \\ qpat_x_assum`evaluate([_],env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
      \\ disch_then(qspec_then`ck''`mp_tac) \\ simp[] \\ strip_tac
      \\ qexists_tac`ck+ck'+ck''` \\ fs[]
      \\ match_mp_tac (GEN_ALL wfv_state_SUBMAP) \\ asm_exists_tac \\ fs []
      \\ imp_res_tac evaluate_app_mono \\ fs [])
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
      `?env5. env_rel (v_rel g1 l1 t0.code) env env5 0 (MAP (λx. (0,x)) e1)` by
          metis_tac [env_rel_env_exists]
      \\ disch_then(qspecl_then[`env5`,`t`]mp_tac)
      \\ disch_then(qspecl_then[`l1`,`g1`]mp_tac)
      \\ `set (code_locs [x1]) DIFF domain (FST g) ⊆ l1` by fs [SUBSET_DEF]
      \\ `code_includes (SND g) t.code` by
           (imp_res_tac evaluate_mono \\ fs[]
            \\ fs[env_rel_def,fv1_thm]
            \\ metis_tac[code_includes_SUBMAP])
      \\ `EVERY (wfv g1 l1 t.code) env` by
        (match_mp_tac (GEN_ALL EVERY_wfv_SUBMAP) \\ asm_exists_tac \\ fs []
         \\ imp_res_tac evaluate_mono \\ fs [])
      \\ `env_rel (v_rel g1 l1 t.code) env env5 0 (MAP (λx. (0,x)) e1)` by
        (match_mp_tac (GEN_ALL env_rel_SUBMAP) \\ asm_exists_tac \\ fs []
         \\ imp_res_tac evaluate_mono \\ fs [])
      \\ fs []
      \\ strip_tac \\ rveq
      \\ drule (Q.GEN`s`pure_correct
                |> INST_TYPE [``:'c``|->``:abs_calls_state # 'c``])
      \\ disch_then(qspec_then`r`mp_tac)
      \\ simp[]
      \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
      >- (CASE_TAC \\ fs[])
      \\ ntac 2 strip_tac \\ rveq
      \\ fs[quantHeuristicsTheory.LIST_LENGTH_2] \\ rveq
      \\ rfs[] \\ rveq
      \\ qmatch_assum_rename_tac`LIST_REL (v_rel g1 l1 _) ev1 ev2`
      \\ Cases_on`ev1 = []`
      \\ imp_res_tac evaluate_length_imp \\ rfs[]
      \\ fs[evaluate_app_rw]
      \\ qpat_x_assum`_ = (res,_)`mp_tac
      \\ BasicProvers.TOP_CASE_TAC \\ fs[]
      \\ strip_tac
      \\ drule (GEN_ALL dest_closure_v_rel_lookup)
      \\ qmatch_assum_rename_tac`dest_closure _ _ f1 ev1 = _`
      \\ rename [`v_rel g1 l1 t1.code f1 f2`]
      \\ disch_then drule
      \\ `LIST_REL (v_rel g1 l1 t1.code) ev1 ev2` by
        (match_mp_tac (GEN_ALL LIST_REL_v_rel_SUBMAP) \\ asm_exists_tac \\ fs []
         \\ imp_res_tac evaluate_mono \\ fs [])
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
      \\ `t1.code = t.code` by
       (imp_res_tac calls_sing \\ rveq \\ fs []
        \\ drule (GEN_ALL calls_pure_sing)
        \\ disch_then drule \\ strip_tac
        \\ qpat_x_assum `evaluate ([y],_) = (Rval [f2],t1)` assume_tac
        \\ qmatch_assum_abbrev_tac `evaluate ([y],env77,t6) = _`
        \\ drule (GEN_ALL pure_correct)
        \\ disch_then (qspecl_then [`t6`,`env77`] mp_tac)
        \\ fs [] \\ rw [] \\ unabbrev_all_tac \\ fs [])
      \\ fs []
      \\ first_x_assum drule
      \\ disch_then drule
      \\ qpat_x_assum`state_rel g1 l1 r t`assume_tac
      \\ disch_then drule
      \\ disch_then drule
      \\ strip_tac
      \\ imp_res_tac LIST_REL_LENGTH \\ fs[]
      \\ Cases_on`ev2 = []` \\ fs[]
      \\ rfs []
      \\ first_x_assum drule
      \\ rpt (disch_then drule)
      \\ strip_tac \\ fs []
      \\ rfs[evaluate_app_rw]
      \\ qpat_x_assum`_ = (res,_)`mp_tac
      \\ imp_res_tac state_rel_clock \\ fs[]
      \\ imp_res_tac state_rel_max_app \\ fs[]
      \\ IF_CASES_TAC \\ fs[] >- (
        strip_tac \\ rveq
        \\ qexists_tac`ck` \\ simp[find_code_def]
        \\ fs [wfv_state_def]
        \\ match_mp_tac state_rel_with_clock
        \\ metis_tac[] )
      \\ strip_tac
      \\ simp[evaluate_def,evaluate_GENLIST_Var_tra]
      \\ simp[find_code_def]
      \\ simp[Once dec_clock_def]
      \\ qpat_x_assum`evaluate(es,env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
      \\ disch_then(qspec_then`ck''`mp_tac) \\ simp[] \\ strip_tac
      \\ qexists_tac`ck+ck''` \\ simp[dec_clock_def]
      \\ rpt (goal_assum (first_x_assum o mp_then Any mp_tac))
      \\ rfs [] \\ fs []
      \\ fs [evaluate_def,evaluate_GENLIST_Var_tra,dec_clock_def,
             TAKE_APPEND1,find_code_def] \\ rfs []
      \\ IF_CASES_TAC \\ fs []
      \\ ntac 2 (qpat_x_assum`_ _ _ = (_,_)`mp_tac)
      \\ TOP_CASE_TAC \\ fs []
      \\ TOP_CASE_TAC \\ fs []
      \\ imp_res_tac evaluate_SING \\ rveq \\ fs []
      \\ strip_tac \\ rveq \\ fs []
      \\ imp_res_tac evaluate_mono \\ fs [] \\ rw []
      \\ match_mp_tac (GEN_ALL wfv_state_SUBMAP) \\ asm_exists_tac \\ fs [])
    \\ `env_rel (v_rel g1 l1 t0.code) env env2 0 (MAP (λx. (0,x)) e1)` by fs []
    \\ `env_rel (v_rel g1 l1 t.code) env env2 0 (MAP (λx. (0,x)) e1)` by
        (match_mp_tac (GEN_ALL env_rel_SUBMAP) \\ asm_exists_tac \\ fs []
         \\ imp_res_tac evaluate_mono \\ fs [])
    \\ disch_then(qspecl_then[`env2`,`t`]mp_tac)
    \\ disch_then(qspecl_then[`l1`,`g1`]mp_tac)
    \\ `set (code_locs [x1]) DIFF domain (FST g) ⊆ l1` by fs [SUBSET_DEF]
    \\ `code_includes (SND g) t.code` by
         (imp_res_tac evaluate_mono \\ fs[]
          \\ fs[env_rel_def,fv1_thm]
          \\ metis_tac[code_includes_SUBMAP])
    \\ `EVERY (wfv g1 l1 t.code) env` by
        (match_mp_tac (GEN_ALL EVERY_wfv_SUBMAP) \\ asm_exists_tac \\ fs []
         \\ imp_res_tac evaluate_mono \\ fs [])
    \\ fs []
    \\ strip_tac \\ rveq
    \\ strip_tac \\ rveq
    \\ `includes_state g1 r'.compile_oracle` by
     (fs [semanticPrimitivesTheory.result_case_eq,pair_case_eq,bool_case_eq]
      \\ metis_tac [evaluate_includes_state,evaluate_app_includes_state])
    \\ fs [] \\ rveq
    \\ qpat_x_assum `_ = (_,_)` mp_tac
    \\ simp[evaluate_append]
    \\ imp_res_tac calls_length
    \\ fs[quantHeuristicsTheory.LIST_LENGTH_2,evaluate_GENLIST_Var_tra]
    \\ rveq \\ fs[]
    \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      rw[] \\ fs[]
      \\ simp[RIGHT_EXISTS_IMP_THM,RIGHT_EXISTS_AND_THM]
      \\ qpat_x_assum`evaluate(es,env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
      \\ disch_then(qspec_then`ck'`mp_tac) \\ simp[] \\ strip_tac
      \\ qexists_tac`ck+ck'` \\ simp[])
    \\ strip_tac \\ fs[]
    \\ simp[evaluate_GENLIST_Var_tra]
    \\ drule evaluate_SING \\ strip_tac \\ rveq \\ fs []
    \\ fs [] \\ rfs [] \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ rpt(disch_then drule)
    \\ simp[RIGHT_EXISTS_IMP_THM,RIGHT_EXISTS_AND_THM,FORALL_AND_THM]
    \\ strip_tac
    \\ qmatch_assum_rename_tac`LIST_REL (v_rel g1 l1 _) ev1 ev2`
    \\ Cases_on`ev1 = []` \\ fs[]
    \\ fs[evaluate_app_rw]
    \\ Cases_on`ev2 = []` \\ fs[]
    \\ fs[evaluate_app_rw]
    \\ qpat_x_assum`_ = (res,_)`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ drule (GEN_ALL dest_closure_v_rel_lookup)
    \\ disch_then drule
    \\ `LIST_REL (v_rel g1 l1 t'.code) ev1 ev2` by
        (match_mp_tac (GEN_ALL LIST_REL_v_rel_SUBMAP) \\ asm_exists_tac \\ fs []
         \\ imp_res_tac evaluate_mono \\ fs [])
    \\ disch_then drule
    \\ impl_tac >- rw[]
    \\ strip_tac \\ fs[]
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
    \\ strip_tac \\ rfs[]
    \\ pop_assum mp_tac
    \\ imp_res_tac code_includes_ALOOKUP \\ fs[]
    \\ IF_CASES_TAC \\ fs[]
    >- (
      strip_tac \\ rveq
      \\ qpat_x_assum`evaluate(es,env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
      \\ disch_then(qspec_then`ck'`mp_tac) \\ simp[] \\ strip_tac
      \\ qexists_tac`ck+ck'` \\ simp[find_code_def]
      \\ imp_res_tac evaluate_mono
      \\ fs [SUBMAP_DEF,FLOOKUP_DEF]
      \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
      \\ fs [state_rel_def]
      \\ match_mp_tac (GEN_ALL wfv_state_SUBMAP)
      \\ fs [wfv_state_def]
      \\ asm_exists_tac \\ fs [])
    \\ `EVERY (wfv g1 l1 t'.code) ev1` by
        (match_mp_tac (GEN_ALL EVERY_wfv_SUBMAP) \\ asm_exists_tac \\ fs []
         \\ imp_res_tac evaluate_mono \\ fs [])
    \\ `LIST_REL (v_rel g1 l1 t'.code) ev1 ev2` by
        (match_mp_tac (GEN_ALL LIST_REL_v_rel_SUBMAP) \\ asm_exists_tac \\ fs []
         \\ imp_res_tac evaluate_mono \\ fs [])
    \\ first_x_assum drule
    \\ disch_then drule
    \\ disch_then drule
    \\ strip_tac
    \\ Cases_on `ev2 = []` THEN1 fs []
    \\ fs [evaluate_app_rw]
    \\ simp[Once dec_clock_def]
    \\ simp[evaluate_def,evaluate_GENLIST_Var_tra,TAKE_APPEND1,find_code_def]
    \\ qpat_x_assum`_ = (res',_)`mp_tac
    \\ imp_res_tac state_rel_clock \\ fs[]
    \\ imp_res_tac state_rel_max_app \\ fs[]
    \\ simp[evaluate_def,evaluate_GENLIST_Var_tra,TAKE_APPEND1,find_code_def,
            dec_clock_def]
    \\ `FLOOKUP t'.code (x + 1) = FLOOKUP t.code (x + 1)` by
      (imp_res_tac evaluate_mono \\ fs [SUBMAP_DEF,FLOOKUP_DEF]) \\ fs[]
    \\ IF_CASES_TAC \\ fs[] >- (
      strip_tac \\ rveq \\ rw []
      \\ qexists_tac`ck+ck'` \\ simp[find_code_def]
      \\ qpat_x_assum `evaluate (es,_) = _` assume_tac
      \\ drule evaluate_add_clock
      \\ disch_then (qspec_then `ck'` mp_tac) \\ fs []
      \\ imp_res_tac LIST_REL_LENGTH \\ fs []
      \\ imp_res_tac evaluate_IMP_LENGTH \\ fs [])
    \\ strip_tac
    \\ simp[evaluate_def,evaluate_GENLIST_Var_tra]
    \\ simp[find_code_def]
    \\ simp[Once dec_clock_def]
    \\ qpat_x_assum`evaluate(es,env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
    \\ disch_then(qspec_then`ck'+ck''`mp_tac) \\ simp[] \\ rpt strip_tac
    \\ qpat_x_assum`evaluate([_],env2,_) = _`(mp_tac o MATCH_MP evaluate_add_clock)
    \\ disch_then(qspec_then`ck''`mp_tac) \\ simp[] \\ rpt strip_tac
    \\ qexists_tac`ck+ck'+ck''` \\ simp[dec_clock_def]
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
    \\ rpt (goal_assum (first_x_assum o mp_then Any mp_tac))
    \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
    \\ fs [TAKE_APPEND1]
    \\ ntac 2 (qpat_x_assum`_ _ _ = (_,_)` (mp_tac o GSYM))
    \\ fs [] \\ rpt strip_tac
    \\ rpt (pop_assum kall_tac)
    \\ every_case_tac \\ fs [])
  (* Tick *)
  \\ conj_tac >- (
    say "Tick"
    \\ fs [evaluate_def,calls_def] \\ rpt strip_tac
    \\ Cases_on `s.clock = 0` \\ fs [] THEN1
     (fs [PUSH_EXISTS_IMP,GSYM PULL_EXISTS]
      \\ pairarg_tac \\ fs [] \\ rw []
      \\ `t0.clock = s.clock` by fs [state_rel_def]
      \\ fs [evaluate_def]
      \\ `[HD e1] = e1` by (imp_res_tac calls_sing \\ fs [])
      \\ qexists_tac `0` \\ fs [state_rel_def,code_inv_def,PULL_EXISTS]
      \\ asm_exists_tac \\ fs [])
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ fs [dec_clock_def]
    \\ first_x_assum drule \\ fs [code_locs_def]
    \\ disch_then (qspecl_then [`env2`,`dec_clock 1 t0`] mp_tac)
    \\ fs [dec_clock_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ fs [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
    \\ impl_tac THEN1 fs [wfv_state_def]
    \\ fs [PULL_FORALL,AND_IMP_INTRO]
    \\ `includes_state g1 s.compile_oracle` by
          (imp_res_tac evaluate_includes_state \\ fs [])
    \\ fs [PULL_FORALL,AND_IMP_INTRO]
    \\ impl_tac THEN1 (fs [state_rel_def,env_rel_def,fv1_thm] \\ rfs []
                       \\ imp_res_tac calls_sing \\ fs [])
    \\ strip_tac \\ fs []
    \\ fs [PUSH_EXISTS_IMP,GSYM PULL_EXISTS] \\ rw [] \\ fs []
    \\ `[HD e1] = e1` by (imp_res_tac calls_sing \\ fs [])
    \\ pop_assum SUBST_ALL_TAC
    \\ `t0.clock = s.clock` by fs [state_rel_def]
    \\ fs [evaluate_def]
    \\ qexists_tac `ck` \\ fs [dec_clock_def]
    \\ `ck + s.clock − 1 = ck + (s.clock − 1)` by decide_tac
    \\ qpat_x_assum `_ = (_,_)` mp_tac
    \\ pop_assum (fn th => simp_tac std_ss [th])
    \\ `[HD e1] = e1` by (imp_res_tac calls_sing \\ fs [])
    \\ pop_assum SUBST_ALL_TAC
    \\ fs [])
  (* Call *)
  \\ conj_tac >- (
    say "Call"
    \\ rw[evaluate_def,calls_def,code_locs_def,ALL_DISTINCT_APPEND]
    \\ pairarg_tac \\ fs[]
    \\ qpat_x_assum`_ = (res,s)`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ rveq \\ fs[] \\ strip_tac
    \\ Cases_on `q = Rerr (Rabort Rtype_error)` \\ fs []
    \\ `includes_state g1 r.compile_oracle` by
     (fs [semanticPrimitivesTheory.result_case_eq,pair_case_eq,
          bool_case_eq,option_case_eq] \\ rveq \\ fs []
      \\ first_x_assum (assume_tac o SYM)
      \\ imp_res_tac evaluate_includes_state \\ fs [dec_clock_def])
    \\ first_x_assum drule
    \\ rpt (disch_then drule)
    \\ rpt (disch_then (first_x_assum o mp_then Any mp_tac))
    \\ disch_then (qspec_then `env2` mp_tac)
    \\ impl_tac THEN1
     (fs [env_rel_def] \\ IF_CASES_TAC \\ fs [fv1_thm,EXISTS_MAP]
      \\ gen_tac \\ strip_tac \\ first_x_assum match_mp_tac
      \\ fs [fv_exists] \\ pop_assum mp_tac
      \\ fs [EXISTS_MEM])
    \\ strip_tac \\ fs []
    \\ `r.code = FEMPTY` by fs [state_rel_def]
    \\ fs [find_code_def]
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ qexists_tac `ck` \\ fs [evaluate_def])
  \\ say "evaluate_app_NIL"
  \\ conj_tac >- ( rw[evaluate_def] \\ qexists_tac`0`
                   \\ rw[RIGHT_EXISTS_IMP_THM,RIGHT_EXISTS_AND_THM] )
  (* app cons *)
  \\ say "evaluate_app_CONS"
  \\ simp[evaluate_def]
  \\ rpt gen_tac \\ strip_tac
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  >- (
    simp[PULL_EXISTS]
    \\ rpt gen_tac \\ strip_tac
    \\ rename [`_ (x1::xs) = _`]
    \\ qabbrev_tac `t1 = if s0.clock < SUC (LENGTH xs) then t0 with clock := 0
                         else dec_clock (SUC (LENGTH xs)) t0`
    \\ `every_result (EVERY (wfv g l t1.code)) (wfv g l t1.code) res` by (
      every_case_tac \\ fs[] \\ rveq \\ fs[Abbr`t1`,dec_clock_def]
      \\ match_mp_tac (GEN_ALL dest_closure_partial_wfv)
      \\ asm_exists_tac \\ fs[] )
    \\ asm_exists_tac \\ fs []
    \\ simp[RIGHT_EXISTS_AND_THM,RIGHT_EXISTS_IMP_THM]
    \\ conj_asm1_tac
    >- (
      every_case_tac \\ fs[Abbr`t1`] \\ rveq \\ fs[]
      \\ fs[wfv_state_def,dec_clock_def] )
    \\ simp[evaluate_app_rw]
    \\ drule (GEN_ALL dest_closure_v_rel)
    \\ disch_then drule \\ fs[PULL_EXISTS]
    \\ disch_then drule \\ disch_then drule
    \\ strip_tac \\ fs[]
    \\ imp_res_tac state_rel_clock \\ fs[]
    \\ imp_res_tac state_rel_max_app \\ fs[]
    \\ qexists_tac`0` \\ fs[]
    \\ imp_res_tac LIST_REL_LENGTH
    \\ rw[] \\ fs[] \\ rw[dec_clock_def] \\ fs [Abbr`t1`,dec_clock_def]
    \\ match_mp_tac state_rel_with_clock \\ fs[] )
  \\ fs[PULL_EXISTS]
  \\ rpt gen_tac \\ strip_tac
  \\ simp[RIGHT_EXISTS_AND_THM,RIGHT_EXISTS_IMP_THM]
  \\ qpat_x_assum`_ = (res,_)`mp_tac
  \\ IF_CASES_TAC
  >- (
    simp[] \\ strip_tac \\ rveq \\ fs[]
    \\ simp[RIGHT_EXISTS_AND_THM,RIGHT_EXISTS_IMP_THM]
    \\ qexists_tac`0` \\ fs[]
    \\ qexists_tac`t0 with clock := 0` \\ fs[]
    \\ conj_tac >- fs[wfv_state_def]
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
  \\ `includes_state g r.compile_oracle` by
     (pop_assum (assume_tac o GSYM)
      \\ fs [semanticPrimitivesTheory.result_case_eq,pair_case_eq,
          bool_case_eq,option_case_eq,list_case_eq] \\ rveq \\ fs []
      \\ imp_res_tac evaluate_includes_state
      \\ imp_res_tac evaluate_app_includes_state
      \\ fs [dec_clock_def])
  \\ qmatch_asmsub_rename_tac`wfv g1 l1`
  \\ qmatch_asmsub_rename_tac`Full_app e args rest`
  \\ simp[RIGHT_EXISTS_AND_THM,RIGHT_EXISTS_IMP_THM]
  \\ drule (GEN_ALL dest_closure_v_rel) \\ fs[PULL_EXISTS]
  \\ rpt (disch_then drule)
  \\ strip_tac
  \\ simp[evaluate_app_rw]
  \\ imp_res_tac state_rel_max_app \\ fs[]
  \\ qpat_x_assum`_ = (res,_)`mp_tac
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ imp_res_tac evaluate_length_imp
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
  \\ rveq \\ strip_tac
  \\ rveq \\ fs[] \\ rfs[]
  \\ fs[PULL_EXISTS] \\ rfs[]
  \\ fs[recclosure_rel_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ qmatch_assum_rename_tac`v_rel g1 l1 _ f f'`
  \\ qmatch_assum_rename_tac`LIST_REL _ rest1 rest2`
  \\ first_x_assum(qspecl_then[`g1`,`l1`]mp_tac o
        CONV_RULE(RESORT_FORALL_CONV List.rev))
  \\ `EVERY (wfv g1 l1 t0.code) args /\ EVERY (wfv g1 l1 t0.code) rest1` by
   (last_assum (mp_then (Pos hd) mp_tac (GEN_ALL dest_closure_full_wfv))
    \\ disch_then drule \\ impl_tac THEN1 fs [] \\ rw [] \\ fs [])
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
  \\ rveq \\ fs []
  \\ imp_res_tac calls_length \\ fs[]
  \\ `env_rel (v_rel g1 l1 t0.code) args args2 0 [(0, SND (EL i fns2))]`
  by (
    qhdtm_x_assum`env_rel`mp_tac
    \\ `n = FST (EL i fns2)`
    by ( Cases_on`b` \\ fs[calls_list_MAPi,EL_ZIP,EL_MAP] )
    \\ reverse IF_CASES_TAC \\ fs[]
    >- (
      strip_tac
      \\ match_mp_tac env_rel_DROP_args
      \\ simp[] \\ fs[]
      \\ qpat_x_assum `EL i fns1 = _` (assume_tac o GSYM) \\ fs [])
    \\ qpat_x_assum `EL i fns1 = _` (assume_tac o GSYM) \\ fs []
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
  \\ (reverse(Cases_on`b`) \\ fs[] \\ rveq >- (
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
      \\ conj_tac >- fs [wfv_state_def]
      \\ conj_tac >- metis_tac[subg_trans]
      \\ conj_tac >- fs[SUBSET_DEF]
      \\ qhdtm_x_assum`env_rel`mp_tac \\ simp[EL_ZIP] \\ rw []
      THEN1 metis_tac[state_rel_with_clock,code_includes_subg,state_rel_def]
      \\ match_mp_tac (MP_CANON (GEN_ALL code_includes_subg))
      \\ asm_exists_tac \\ fs [])
    \\ strip_tac
    \\ imp_res_tac calls_length \\ fs[]
    \\ simp[EL_ZIP]
    \\ fs[dec_clock_def]
    \\ imp_res_tac state_rel_clock \\ fs[]
    \\ imp_res_tac state_rel_max_app \\ fs[]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs[]
    \\ rfs[EL_ZIP]
    \\ TRY (qexists_tac`ck` \\ simp[] \\ rfs[] \\ NO_TAC)
    \\ first_x_assum drule
    \\ `EVERY (wfv g1 l1 t.code) rest1` by
      (match_mp_tac (GEN_ALL EVERY_wfv_SUBMAP) \\ asm_exists_tac
       \\ imp_res_tac evaluate_mono \\ fs [])
    \\ `wfv_state g1 l1 t.code r` by
      (match_mp_tac (GEN_ALL wfv_state_SUBMAP) \\ asm_exists_tac
       \\ imp_res_tac evaluate_mono \\ fs [])
    \\ `LIST_REL (v_rel g1 l1 t.code) rest1 rest2` by
      (match_mp_tac (GEN_ALL LIST_REL_v_rel_SUBMAP) \\ asm_exists_tac
       \\ imp_res_tac evaluate_mono \\ fs [])
    \\ rpt (disch_then (first_assum o mp_then Any mp_tac))
    \\ rw [] \\ fs []
    \\ rpt (goal_assum (first_assum o mp_then Any mp_tac)) \\ fs []
    \\ drule evaluate_add_clock
    \\ disch_then (qspec_then `ck'` mp_tac)
    \\ fs [] \\ rw []
    \\ qexists_tac `ck+ck'` \\ fs []))
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
  \\ qpat_x_assum `code_includes (SND gd) t0.code` assume_tac
  \\ pop_assum mp_tac
  \\ `ALOOKUP (SND gd) (2 * i + loc + 1) = SOME (EL i (ZIP (MAP FST fns1,es)))`
  by (
    simp[Abbr`gd`]
    \\ simp[ALOOKUP_code_list]
    \\ DEEP_INTRO_TAC some_intro \\ simp[]
    \\ imp_res_tac evaluate_IMP_LENGTH
    \\ fs [LENGTH_ZIP_MIN]
    \\ fs [markerTheory.Abbrev_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
  \\ strip_tac
  \\ drule (GEN_ALL code_includes_ALOOKUP)
  \\ disch_then drule
  \\ `LENGTH fns1 = LENGTH es` by
   (fs [markerTheory.Abbrev_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
  \\ fs[EL_ZIP,EL_MAP]
  \\ simp[] \\ strip_tac
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
  \\ disch_then drule
  \\ qmatch_asmsub_abbrev_tac`dec_clock dk s0`
  \\ qmatch_asmsub_abbrev_tac`(n,e)`
  \\ disch_then(qspecl_then[`dec_clock dk t0`,`TAKE n args2`]mp_tac)
  \\ (impl_tac >- (
    fs[dec_clock_def]
    \\ conj_tac >- fs [wfv_state_def]
    \\ conj_tac >- (
      match_mp_tac subg_trans \\ asm_exists_tac \\ fs []
      \\ match_mp_tac subg_trans \\ once_rewrite_tac [CONJ_COMM]
      \\ asm_exists_tac \\ fs []
      \\ unabbrev_all_tac
      \\ qpat_x_assum `LENGTH fns1 = LENGTH es` (assume_tac o GSYM) \\ fs []
      \\ match_mp_tac (GEN_ALL subg_insert_each') \\ fs []
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
    \\ conj_tac >- fs[SUBSET_DEF]
    \\ rfs[wfg_def,EL_ZIP]
    \\ qpat_x_assum `LENGTH fns1 = LENGTH es` (assume_tac o GSYM) \\ fs []
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
      \\ res_tac \\ simp[])
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
  \\ TRY (drule evaluate_add_clock \\ fs[]
          \\ disch_then(qspec_then`ck'`assume_tac)
          \\ qexists_tac`ck+1` \\ simp[]
          \\ `ck + (t0.clock − dk) = ck + t0.clock − dk` by decide_tac
          \\ fs [] \\ NO_TAC)
  \\ first_x_assum drule
  \\ `EVERY (wfv g1 l1 t.code) rest1` by
    (match_mp_tac (GEN_ALL EVERY_wfv_SUBMAP) \\ asm_exists_tac \\ fs []
     \\ imp_res_tac evaluate_mono \\ fs [])
  \\ `LIST_REL (v_rel g1 l1 t.code) rest1 rest2` by
    (match_mp_tac (GEN_ALL LIST_REL_v_rel_SUBMAP) \\ asm_exists_tac \\ fs []
     \\ imp_res_tac evaluate_mono \\ fs [])
  \\ rpt (disch_then drule) \\ fs []
  \\ rw [] \\ fs [ADD1]
  \\ rpt (goal_assum (first_x_assum o mp_then Any mp_tac))
  \\ qexists_tac`ck+ck'+1` \\ simp[]
  \\ drule evaluate_add_clock \\ fs[]
  \\ disch_then(qspec_then`ck'`assume_tac) \\ fs []
  \\ qmatch_assum_abbrev_tac `closSem$evaluate (_,_,(_ with clock := ck11)) = _`
  \\ qmatch_goalsub_abbrev_tac `_ with clock := ck22`
  \\ qsuff_tac `ck11 = ck22` \\ rw [] \\ fs []
  \\ unabbrev_all_tac \\ fs []
QED

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
Theorem calls_code_locs_MEM:
   ∀xs g0 ys g. calls xs g0 = (ys,g) ⇒
   ∀x.
    (MEM x (code_locs ys) ∨
    MEM x (code_locs (MAP (SND o SND) (SND g)))) ⇒
    (MEM x (code_locs xs) ∨
    MEM x (code_locs (MAP (SND o SND) (SND g0))))
Proof
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
  metis_tac[]
QED

(* the all distinctness of code_locs is preserved *)
Theorem calls_code_locs_ALL_DISTINCT:
   ∀xs g0 ys g. calls xs g0 = (ys,g) ⇒
    ALL_DISTINCT (code_locs xs ++ code_locs (MAP (SND o SND) (SND g0))) ⇒
    ALL_DISTINCT (code_locs ys ++ code_locs (MAP (SND o SND) (SND g)))
Proof
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
  metis_tac[]
QED

val extra_code_assum_def = Define `
  extra_code_assum prog g0 co =
    ∀n m. MEM n (code_locs prog) ∧ n ∉ domain g0 ⇒
          n ∉ domain (FST (FST (co m)))`;

Theorem semantics_calls:
   semantics (ffi:'ffi ffi_state) max_app FEMPTY co cc x <> Fail ==>
   compile T x = (y,g0,aux) /\ every_Fn_SOME x ∧ every_Fn_vs_NONE x /\
   ALL_DISTINCT (code_locs x) /\ FST (FST (co 0)) = g0 /\
   extra_code_assum x g0 co /\
   code_inv NONE FEMPTY cc co (FEMPTY |++ aux) cc1 co1 ==>
   semantics (ffi:'ffi ffi_state) max_app (FEMPTY |++ aux) co1 cc1 y =
   semantics (ffi:'ffi ffi_state) max_app FEMPTY co cc x
Proof
  strip_tac
  \\ ho_match_mp_tac IMP_semantics_eq
  \\ fs [] \\ fs [eval_sim_def] \\ rw []
  \\ fs [compile_def]
  \\ rveq \\ fs [FUPDATE_LIST]
  \\ pairarg_tac \\ fs [] \\ rveq \\ fs []
  \\ drule (calls_correct |> SIMP_RULE std_ss [] |> CONJUNCT1)
  \\ rpt (disch_then drule) \\ fs [EVAL ``wfg (LN,[])``]
  \\ ntac 2 (pop_assum mp_tac)
  \\ simp [Once code_inv_def]
  \\ (*ntac 2*) strip_tac
  \\ drule evaluate_code
  \\ strip_tac \\ fs [initial_state_def]
  (*
  \\ disch_then (qspecl_then [`[]`,
      `initial_state ffi max_app (FOLDL $|+ FEMPTY aux) co1 cc1 k`,
      `UNIV DIFF domain (FST (FST (s2.compile_oracle 0)))`,
      `full_gs n`] mp_tac)
  *)
  \\ disch_then (qspecl_then [`[]`,
      `initial_state ffi max_app (FOLDL $|+ FEMPTY aux) co1 cc1 k`,
      `UNIV DIFF domain (FST (FST (co 0)))`,
      `FST (FST (co 0)),aux`] mp_tac)
  \\ simp []
  \\ `wfg (FST (FST (co 0)),aux)` by
   (match_mp_tac calls_wfg
    \\ asm_exists_tac \\ fs []
    \\ EVAL_TAC \\ fs [])
  \\ fs []
  \\ reverse impl_tac THEN1
   (strip_tac
    \\ qmatch_asmsub_abbrev_tac `(y,[],s4)`
    \\ qexists_tac `ck` \\ fs []
    \\ qmatch_goalsub_abbrev_tac `(y,[],s5)`
    \\ `s4 = s5` by (unabbrev_all_tac \\ fs [initial_state_def])
    \\ rveq \\ fs []
    \\ fs [state_rel_def]
    \\ Cases_on `res1` \\ fs []
    \\ Cases_on `e` \\ fs [])
  \\ fs [env_rel_def,state_rel_def,initial_state_def,code_includes_def]
  (*
  \\ `FST (FST (shift_seq n co 0)) = FST (full_gs n)` by
       metis_tac [co_ok_IMP_full_gs_eq_shift_seq]
  *)
  \\ fs [correct_l_def]
  \\ conj_tac THEN1 (fs [wfv_state_def,initial_state_def,FEVERY_DEF,code_inv_def])
  (*
  THEN1
   (match_mp_tac subg_trans
    \\ qexists_tac `full_gs 0`
    \\ qpat_x_assum `!x. _` kall_tac
    \\ first_x_assum (qspec_then `1` mp_tac)
    \\ once_rewrite_tac [co_ok_def] \\ simp []
    \\ rpt (pairarg_tac \\ fs [])
    \\ strip_tac \\ imp_res_tac make_g_wfg
    \\ imp_res_tac make_g_subg
    \\ fs [FUPDATE_LIST])
  *)
  \\ conj_tac THEN1 (
    match_mp_tac subg_refl
    \\ fs[] \\ fs[wfg_def] )
  \\ conj_tac THEN1
   (fs [SUBSET_DEF]
    \\ drule evaluate_code \\ strip_tac
    \\ fs [shift_seq_def,extra_code_assum_def]
    \\ metis_tac [])
  \\ conj_tac THEN1 (fs [IN_DISJOINT,IN_DIFF,shift_seq_def])
  (*
  \\ conj_tac THEN1 (metis_tac [co_ok_IMP_wfg_full_gs])
  *)
  \\ conj_tac THEN1
   (full_simp_tac std_ss [GSYM FUPDATE_LIST]
    \\ rpt strip_tac
    \\ match_mp_tac mem_to_flookup
    \\ fs [ALOOKUP_MEM]
    \\ `aux = SND (FST (FST (co 0)),aux)` by fs []
    \\ pop_assum (fn th => once_rewrite_tac [th])
    \\ match_mp_tac calls_ALL_DISTINCT
    \\ asm_exists_tac \\ fs [])
  \\ conj_tac THEN1 (fs [code_inv_def] \\ metis_tac [])
  \\ fs [includes_state_def] \\ qexists_tac `0` \\ fs []
QED

Theorem semantics_compile:
   semantics ffi max_app FEMPTY co cc x ≠ Fail ∧
   compile do_call x = (y,g1,aux) ∧
   (if do_call then
    syntax_ok x ∧ FST (FST (co 0)) = g1 ∧
    extra_code_assum x g1 co /\
    code_inv NONE FEMPTY cc co (FEMPTY |++ aux) cc1 co1
    else cc = state_cc (CURRY I) cc1 ∧
         co1 = state_co (CURRY I) co) ⇒
   semantics ffi max_app (FEMPTY |++ aux) co1 cc1 y
   =
   semantics ffi max_app FEMPTY co cc x
Proof
  reverse(Cases_on`do_call`)
  \\ rw[compile_def]
  \\ fs[FUPDATE_LIST_THM]
  >- ( match_mp_tac semantics_CURRY_I \\ fs[] )
  \\ irule semantics_calls
  \\ fs[compile_def, syntax_ok_def]
QED

(* lemmas to help proving co_ok *)

val make_gs_def = Define `
  (make_gs code co 0 =
    let g = FST (FST (co 0)) in
      make_g g code) /\
  (make_gs code co (SUC n) =
    let g = FST (FST (co 0)) in
    let (cfg,exp,aux) = co 0 in
    let (g',exp',aux1) = compile_inc g (exp,aux) in
      make_gs (FUNION code (FEMPTY |++ aux1)) (shift_seq 1 co) n)`

val nth_code_def = Define `
  nth_code code co 0 = code /\
  nth_code code co (SUC k) =
    let (cfg,exp,aux) = co 0 in
    let (g',exp',aux') = compile_inc (FST cfg) (exp,aux) in
      nth_code (code |++ aux') (shift_seq 1 co) k`

(* TODO: move *)
Theorem FUNION_FEMPTY_FUPDATE_LIST:
   DISJOINT (FDOM code) (set (MAP FST aux)) ==>
    FUNION code (FEMPTY |++ aux) = code |++ aux
Proof
  rw [fmap_EXT] \\ fs [FDOM_FUPDATE_LIST,FUNION_DEF]
  \\ fs [IN_DISJOINT]
  THEN1
   (`~MEM x (MAP FST aux)` by metis_tac []
    \\ fs [FUPDATE_LIST_APPLY_NOT_MEM])
  \\ `~(x ∈ FDOM code)` by metis_tac [] \\ fs []
  \\ match_mp_tac FUPDATE_SAME_LIST_APPLY \\ fs []
QED

Theorem ALL_DISTINCT_make_gs:
   !i code co2.
      IS_SOME (make_gs code co2 i) ==>
      ALL_DISTINCT (MAP FST (SND (THE (make_gs code co2 i))))
Proof
  Induct \\ fs [make_gs_def] \\ rw [] THEN1
   (Cases_on `make_g (FST (FST (co2 0))) code` \\ fs []
    \\ imp_res_tac make_g_wfg \\ fs [wfg_def])
  \\ rpt (pairarg_tac \\ fs [])
QED

(*
Theorem ALOOKUP_make_gs:
   !i v code co2.
       (∀k. IS_SOME (make_gs code co2 k)) /\
       ALOOKUP (SND (THE (make_gs code co2 0))) k = SOME v ⇒
       ALOOKUP (SND (THE (make_gs code co2 i))) k = SOME v
Proof
  Induct \\ fs [] \\ fs [make_gs_def] \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ first_x_assum match_mp_tac
  \\ conj_tac THEN1
   (rw [] \\ first_x_assum (qspec_then `SUC k'` mp_tac)
    \\ fs [make_gs_def])
  \\ first_assum (qspec_then `SUC 0` mp_tac)
  \\ first_x_assum (qspec_then `0` mp_tac)
  \\ fs [make_gs_def]
  \\ rw []
  \\ fs [IS_SOME_EXISTS]
  \\ imp_res_tac make_g_wfg \\ fs [wfg_def]
  \\ fs [make_g_def]
  \\ rveq \\ fs []
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs [GSYM MEM_ALOOKUP]
  \\ fs [MEM_MAP,FLOOKUP_FUNION]
  \\ qexists_tac `k'` \\ fs []
  \\ rveq \\ fs []
  \\ ... (* this proof needs a slightly different approach *)
QED
*)

Theorem FST_THE_make_gs:
   !k code co2.
      IS_SOME (make_gs code co2 k) ==>
      FST (THE (make_gs code co2 k)) = FST (FST (co2 k))
Proof
  Induct \\ fs [make_gs_def,make_g_def] \\ rw []
  \\ rpt (pairarg_tac \\ fs []) \\ fs [shift_seq_def,ADD1]
QED

(*
Theorem IMP_co_ok:
   !code co2 k.
      (!i. let (cfg,exp,aux) = co2 i in
           let (g',exp',aux') = compile_inc (FST cfg) (exp,aux) in
             FST (FST (co2 (i+1))) = g' /\
             (!x j. MEM x (code_locs exp) /\ ~(x IN domain g') ==>
                    x ∉ domain (FST (FST (co2 (i + j))))) /\
             ALL_DISTINCT (MAP FST aux') /\
             IMAGE SUC (domain (FST cfg)) ⊆ FDOM (nth_code code co2 i) /\
             DISJOINT (FDOM (nth_code code co2 i)) (set (MAP FST aux')) /\
             DISJOINT (set (code_locs exp)) (domain (FST cfg))) ==>
      co_ok code co2 (THE o make_gs code co2) k
Proof
  Induct_on `k` \\ simp [Once co_ok_def]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ simp [Once make_gs_def]
  \\ `FUNION code (FEMPTY |++ aux1) = code |++ aux1` by
   (match_mp_tac FUNION_FEMPTY_FUPDATE_LIST
    \\ first_x_assum (qspec_then `0` mp_tac)
    \\ fs [nth_code_def])
  \\ `shift_seq 1 (THE o make_gs code co2) =
      THE o make_gs (code |++ aux1) (shift_seq 1 co2)` by
   (fs [shift_seq_def,FUN_EQ_THM] \\ rewrite_tac [GSYM ADD1, make_gs_def]
    \\ fs [shift_seq_def,ADD1]) \\ fs []
  \\ rewrite_tac [CONJ_ASSOC]
  \\ reverse conj_tac THEN1
   (first_x_assum match_mp_tac \\ fs [shift_seq_def] \\ rw []
    \\ first_x_assum (qspec_then `i+1` mp_tac) \\ fs []
    \\ fs [nth_code_def,GSYM ADD1,shift_seq_def])
  \\ first_assum (qspec_then `0` assume_tac) \\ fs []
  \\ rewrite_tac [GSYM CONJ_ASSOC] \\ strip_tac
  \\ fs [nth_code_def] \\ rfs []
  \\ conj_tac THEN1 fs [make_g_def]
  \\ rw [] \\ fs [subg_def]
  \\ `!k. IS_SOME (make_gs code co2 k)` by
   (qpat_x_assum `!i. f (co2 i)` mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ simp [PULL_FORALL]
    \\ qspec_tac (`code`,`code`)
    \\ qspec_tac (`co2`,`co2`)
    \\ Induct_on `k` THEN1
     (rw [] \\ fs [make_gs_def]
      \\ pop_assum (qspec_then `0` mp_tac)
      \\ rpt (pairarg_tac \\ fs [nth_code_def])
      \\ fs [make_g_def])
    \\ rw [] \\ fs [make_gs_def]
    \\ rpt (pairarg_tac \\ fs [nth_code_def])
    \\ first_x_assum match_mp_tac \\ fs [shift_seq_def]
    \\ rw []
    \\ rpt (pairarg_tac \\ fs [nth_code_def])
    \\ first_assum (qspec_then `0` assume_tac)
    \\ first_x_assum (qspec_then `i+1` mp_tac)
    \\ fs []
    \\ fs [GSYM ADD1,nth_code_def,shift_seq_def]
    \\ fs [GSYM PULL_FORALL] \\ strip_tac
    \\ qsuff_tac `code ⊌ (FEMPTY |++ aux1) = code |++ aux1` \\ fs []
    \\ match_mp_tac FUNION_FEMPTY_FUPDATE_LIST
    \\ rfs [])
  \\ rewrite_tac [CONJ_ASSOC]
  \\ reverse conj_tac THEN1
   (pop_assum (qspec_then `i` mp_tac)
    \\ fs [make_gs_def,ALL_DISTINCT_make_gs])
  \\ reverse (rw [])
  THEN1 (match_mp_tac ALOOKUP_make_gs \\ fs [])
  \\ fs [FST_THE_make_gs]
  \\ qsuff_tac `!i. subspt (FST (FST (co2 i))) (FST (FST (co2 (i+1))))`
  THEN1
   (`FST cfg = (FST (FST (co2 0)))` by fs []
    \\ pop_assum (fn th => rewrite_tac [th])
    \\ rpt (pop_assum kall_tac)
    \\ Induct_on `i` \\ fs [ADD1]
    \\ rw [] \\ fs []
    \\ match_mp_tac (GEN_ALL subspt_trans)
    \\ asm_exists_tac \\ fs [])
  \\ rw []
  \\ qpat_x_assum `!i. f (co2 i)` (qspec_then `i` mp_tac)
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [compile_inc_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ imp_res_tac calls_subspt \\ fs []
QED
*)

(* Preservation of some label properties
  every_Fn_SOME xs ∧ every_Fn_vs_NONE xs
*)
Theorem every_Fn_GENLIST_Var:
   ∀n i t. every_Fn_SOME (GENLIST_Var t i n) ∧
       every_Fn_vs_NONE (GENLIST_Var t i n)
Proof
  Induct \\ rw[] \\ rw[Once GENLIST_Var_def] \\
  simp[Once every_Fn_vs_NONE_EVERY,Once every_Fn_SOME_EVERY,EVERY_SNOC]
  \\ simp[GSYM every_Fn_vs_NONE_EVERY,GSYM every_Fn_SOME_EVERY]
QED

Theorem every_Fn_calls_list:
   ∀ls n i t. every_Fn_SOME (MAP SND (calls_list t i n ls)) ∧
         every_Fn_vs_NONE (MAP SND (calls_list t i n ls))
Proof
  Induct>>fs[calls_list_def,FORALL_PROD]>>
  simp[Once every_Fn_vs_NONE_EVERY,Once every_Fn_SOME_EVERY,EVERY_SNOC,every_Fn_GENLIST_Var] \\
  simp[GSYM every_Fn_vs_NONE_EVERY,GSYM every_Fn_SOME_EVERY]
QED

Theorem every_Fn_code_list:
   ∀ls n rest.
  (every_Fn_SOME (MAP (SND o SND) (SND (code_list n ls rest))) ⇔
  every_Fn_SOME (MAP SND ls) ∧
  every_Fn_SOME (MAP (SND o SND) (SND rest))) ∧
  (every_Fn_vs_NONE (MAP (SND o SND) (SND (code_list n ls rest))) ⇔
  every_Fn_vs_NONE (MAP SND ls) ∧
  every_Fn_vs_NONE (MAP (SND o SND) (SND rest)))
Proof
  Induct>>fs[code_list_def,FORALL_PROD]>>
  rw[EQ_IMP_THM]>>fs[Once every_Fn_SOME_EVERY,Once every_Fn_vs_NONE_EVERY]
QED

Theorem calls_preserves_every_Fn_SOME:
   ∀xs g0 ys g. calls xs g0 = (ys,g) ⇒
    every_Fn_SOME xs ∧ every_Fn_SOME (MAP (SND o SND) (SND g0)) ⇒
    every_Fn_SOME ys ∧ every_Fn_SOME (MAP (SND o SND) (SND g))
Proof
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
  fs[MAP_ZIP]
QED

Theorem calls_preserves_every_Fn_vs_NONE:
   ∀xs g0 ys g. calls xs g0 = (ys,g) ⇒
    every_Fn_vs_NONE xs ∧ every_Fn_vs_NONE (MAP (SND o SND) (SND g0)) ⇒
    every_Fn_vs_NONE ys ∧ every_Fn_vs_NONE (MAP (SND o SND) (SND g))
Proof
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
  fs[MAP_ZIP]
QED

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

(* obeys_max_app and no_Labels *)

val state_syntax_def = Define `
  state_syntax f ((g,xs):calls_state) = EVERY (\(x1,x2,x3). f x3) xs`;

Theorem state_syntax_insert_each:
   !k1 loc g.
      state_syntax f (insert_each loc k1 g) = state_syntax f g
Proof
  Induct \\ Cases_on `g` \\ fs [insert_each_def,state_syntax_def]
QED

Theorem state_syntax_code_list:
   !n xs g.
      state_syntax f (code_list n xs g) <=>
      state_syntax f g /\ EVERY f (MAP SND xs)
Proof
  Induct_on `xs` \\ fs [FORALL_PROD,code_list_def,state_syntax_def]
  \\ rw [] \\ eq_tac \\ rw []
QED

Theorem obeys_max_app_GENLIST_Var:
   !n l w. EVERY (obeys_max_app k) (GENLIST_Var n l w)
Proof
  Induct_on `w` \\ once_rewrite_tac [GENLIST_Var_def] \\ rw []
QED

Theorem obeys_max_app_calls_list:
   !t k1 loc fns. EVERY (obeys_max_app k) (MAP SND (calls_list t k1 loc fns))
Proof
  Induct_on `fns` \\ fs [FORALL_PROD,calls_list_def,obeys_max_app_GENLIST_Var]
QED

Theorem calls_obeys_max_app:
   !xs g ys g1.
      calls xs g = (ys,g1) /\ state_syntax (obeys_max_app k) g /\
      EVERY (obeys_max_app k) xs ==>
      EVERY (obeys_max_app k) ys /\ state_syntax (obeys_max_app k) g1
Proof
  ho_match_mp_tac calls_ind \\ rpt strip_tac \\ fs [calls_def] \\ rveq \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ imp_res_tac calls_sing \\ rveq \\ fs []
  \\ imp_res_tac calls_length \\ fs []
  \\ fs [bool_case_eq] \\ rveq \\ fs [obeys_max_app_GENLIST_Var]
  \\ fs [state_syntax_def,state_syntax_insert_each]
  \\ fs [state_syntax_code_list,MAP_ZIP,obeys_max_app_calls_list]
  \\ rename [`SND g5`] \\ PairCases_on `g5` \\ fs [state_syntax_def]
QED

Theorem no_Labels_GENLIST_Var:
   !n l w. EVERY no_Labels (GENLIST_Var n l w)
Proof
  Induct_on `w` \\ once_rewrite_tac [GENLIST_Var_def] \\ rw []
QED

Theorem no_Labels_calls_list:
   !t k1 loc fns. EVERY no_Labels (MAP SND (calls_list t k1 loc fns))
Proof
  Induct_on `fns` \\ fs [FORALL_PROD,calls_list_def,no_Labels_GENLIST_Var]
QED

Theorem calls_no_Labels:
   !xs g ys g1.
      calls xs g = (ys,g1) /\ state_syntax no_Labels g /\
      EVERY no_Labels xs ==>
      EVERY no_Labels ys /\ state_syntax no_Labels g1
Proof
  ho_match_mp_tac calls_ind \\ rpt strip_tac \\ fs [calls_def] \\ rveq \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ imp_res_tac calls_sing \\ rveq \\ fs []
  \\ imp_res_tac calls_length \\ fs []
  \\ fs [bool_case_eq] \\ rveq \\ fs [no_Labels_GENLIST_Var]
  \\ fs [state_syntax_def,state_syntax_insert_each]
  \\ fs [state_syntax_code_list,MAP_ZIP,no_Labels_calls_list]
  \\ rename [`SND g5`] \\ PairCases_on `g5` \\ fs [state_syntax_def]
QED

(* names *)

(*
Theorem app_call_dests_GENLIST_Var:
   !t i num_args. app_call_dests opt (GENLIST_Var t i num_args) = {}
Proof
  Induct_on `num_args`
  \\ once_rewrite_tac [clos_callTheory.GENLIST_Var_def]
  \\ fs [app_call_dests_append]
QED

val pure_code_locs = Q.store_thm("pure_code_locs", (* DUPLCATED! clos_annotate *)
  `!xs. pure xs ==> code_locs [xs] = [] /\
                    app_call_dests opt [xs] = {}`,
  recInduct closLangTheory.pure_ind
  \\ rw[closLangTheory.pure_def, closPropsTheory.code_locs_def]
  \\ fsrw_tac[ETA_ss][EVERY_MEM]
  \\ Q.ISPEC_THEN`es`mp_tac code_locs_map
  \\ disch_then(qspec_then`I`mp_tac)
  \\ simp[FLAT_EQ_NIL, EVERY_MAP, EVERY_MEM]
  \\ ...);

Theorem call_dests_code_list_SUBSET:
   !xs n g.
      call_dests (MAP SND xs) ⊆ set (MAP FST (SND g)) /\
      call_dests (MAP (λx. SND (SND x)) (SND g)) ⊆ set (MAP FST (SND g)) ==>
      call_dests (MAP (λx. SND (SND x)) (SND (code_list n xs g))) ⊆
      set (MAP FST (SND (code_list n xs g)))
Proof
  Induct \\ fs [FORALL_PROD] THEN1 (EVAL_TAC \\ fs [])
  \\ fs [code_list_def] \\ rw []
  \\ first_x_assum match_mp_tac \\ fs []
  \\ rpt (pop_assum mp_tac)
  \\ once_rewrite_tac [app_call_dests_cons] \\ fs []
  \\ fs [SUBSET_DEF]
QED

Theorem code_locs_MAP_SND_calls_list:
   !t x y fns. code_locs (MAP SND (calls_list t x y fns)) = []
Proof
  Induct_on `fns` \\ fs [calls_list_def,FORALL_PROD]
  \\ once_rewrite_tac [code_locs_cons]
  \\ fs [code_locs_def]
QED

Theorem calls_locs:
   !known_code g call_code g1.
      calls known_code g = (call_code,g1) /\
      call_dests known_code = ∅ /\
      call_dests (MAP (SND ∘ SND) (SND g)) ⊆ set (MAP FST (SND g)) ==>
      set (MAP FST (SND g)) ⊆ set (MAP FST (SND g1)) ∧
      call_dests (MAP (SND ∘ SND) (SND g)) ⊆
      call_dests (MAP (SND ∘ SND) (SND g1)) ∧
      call_dests call_code ⊆ set (MAP FST (SND g1)) ∧
      call_dests (MAP (SND ∘ SND) (SND g1)) ⊆ set (MAP FST (SND g1)) ∧
      app_dests call_code UNION app_dests (MAP (SND ∘ SND) (SND g1))
        ⊆ app_dests known_code UNION app_dests (MAP (SND ∘ SND) (SND g)) ∧
      set (code_locs call_code) ∪ set (code_locs (MAP (SND ∘ SND) (SND g1))) =
      set (code_locs known_code) ∪ set (code_locs (MAP (SND ∘ SND) (SND g)))
Proof
  ...
QED

(*

  recInduct calls_ind
  \\ rpt conj_tac

  \\ TRY (

    full_simp_tac std_ss [calls_def,LET_THM,app_call_dests_def,
            every_Fn_SOME_def,MAP,LIST_TO_SET,UNION_EMPTY,
            BIGUNION_INSERT,BIGUNION_EMPTY,
            AC UNION_COMM UNION_ASSOC,SUBSET_REFL,EMPTY_SUBSET]
    \\ rpt gen_tac \\ strip_tac
    \\ rpt gen_tac \\ strip_tac
    \\ rpt (pairarg_tac \\ full_simp_tac std_ss [])
    \\ imp_res_tac calls_sing \\ rveq
    \\ rveq \\ full_simp_tac std_ss [APPEND,bool_case_eq,EMPTY_UNION]
    \\ rveq \\ full_simp_tac std_ss [APPEND,code_locs_def,
                  LET_THM,LIST_TO_SET,LIST_TO_SET_APPEND]
    \\ TRY CASE_TAC \\ full_simp_tac std_ss [APPEND]
    \\ once_rewrite_tac [app_call_dests_cons,code_locs_cons]
    \\ rveq \\ full_simp_tac std_ss [app_call_dests_def,UNION_EMPTY,LIST_TO_SET,
         code_locs_def,APPEND_NIL,LIST_TO_SET_APPEND,LET_THM,
         MAP,o_DEF]
    \\ rpt (pop_assum mp_tac)
    \\ once_rewrite_tac [app_call_dests_cons,code_locs_cons]
    \\ rveq \\ full_simp_tac std_ss [app_call_dests_def,UNION_EMPTY,LIST_TO_SET,
         code_locs_def,APPEND_NIL,LIST_TO_SET_APPEND]
    \\ rpt (disch_then assume_tac)
    \\ full_simp_tac std_ss [calls_def,LET_THM,
          every_Fn_SOME_def,MAP,LIST_TO_SET,UNION_EMPTY,
          BIGUNION_INSERT,BIGUNION_EMPTY,HD,
          IS_SOME_EXISTS,SND_insert_each,app_call_dests_GENLIST_Var,
          code_locs_GENLIST_Var]
    \\ rev_full_simp_tac std_ss []
    \\ TRY (qpat_x_assum `_ ==> _` mp_tac \\ impl_tac
            THEN1 (match_mp_tac call_dests_code_list_SUBSET
                   \\ imp_res_tac calls_length \\ fs [MAP_ZIP])
            \\ disch_then strip_assume_tac)
    \\ imp_res_tac calls_length \\ fs [MAP_ZIP,calls_list_length]
    \\ imp_res_tac calls_pure_sing
    \\ imp_res_tac pure_code_locs \\ fs []
    \\ full_simp_tac std_ss [AC UNION_ASSOC UNION_COMM,
         code_locs_MAP_SND_calls_list]

    \\ once_rewrite_tac [app_call_dests_cons,code_locs_cons]
    \\ rveq \\ full_simp_tac std_ss [app_call_dests_def,UNION_EMPTY,LIST_TO_SET,
         code_locs_def,APPEND_NIL,LIST_TO_SET_APPEND,GSYM ADD1]
    \\ rpt conj_tac
    \\ rveq \\ full_simp_tac std_ss [APPEND]
    \\ TRY CASE_TAC \\ full_simp_tac std_ss [APPEND]
    \\ full_simp_tac std_ss [SUBSET_DEF,IN_UNION,IN_INSERT,NOT_IN_EMPTY,IN_IMAGE,
          MAP,LIST_TO_SET,SUBSET_DEF,BIGUNION_INSERT,BIGUNION_EMPTY,EXTENSION]
    \\ metis_tac []

)

  remaining cases:
     App -- almost works (problem with relating FST g with SND g
                          because they can be out-of-sync, i.e.
                          statement above needs updating)
     Letrec -- needs some work

*)

Theorem call_compile_locs:
   clos_call$compile b known_code = (call_code,g,aux) /\
    call_dests known_code = ∅ ==>
    call_dests call_code ∪ call_dests (MAP (SND ∘ SND) aux) ⊆
    set (MAP FST aux) /\
    app_dests call_code ∪ app_dests (MAP (SND ∘ SND) aux) ⊆
    app_dests known_code /\
    set (code_locs call_code) ∪ set (code_locs (MAP (SND ∘ SND) aux)) =
    set (code_locs known_code)
Proof
  reverse (Cases_on `b`) \\ fs [clos_callTheory.compile_def]
  THEN1 (strip_tac \\ rveq \\ fs [closPropsTheory.code_locs_def])
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ rveq \\ fs []
  \\ drule calls_locs \\ fs [EVAL ``(code_locs [])``]
QED
*)

val _ = export_theory();
