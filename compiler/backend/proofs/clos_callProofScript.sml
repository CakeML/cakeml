open preamble match_goal dep_rewrite
     closSemTheory closPropsTheory
     clos_callTheory
     db_varsTheory clos_freeProofTheory;

val _ = new_theory"clos_callProof";

(* value relation *)

(* TODO: move *)

val IS_SUFFIX_TRANS = Q.store_thm("IS_SUFFIX_TRANS",
  `∀l1 l2 l3. IS_SUFFIX l1 l2 ∧ IS_SUFFIX l2 l3 ⇒ IS_SUFFIX l1 l3`,
  rw[IS_SUFFIX_APPEND] \\ metis_tac[APPEND_ASSOC]);

val IN_EVEN = SIMP_CONV std_ss [IN_DEF] ``x ∈ EVEN``;
(*
val LIST_RELi_mono = Q.store_thm("LIST_RELi_mono",
  `∀l1 l2.
   LIST_RELi P l1 l2 ⇒
   (∀i. i < LENGTH l1 ⇒ P i (EL i l1) (EL i l2) ⇒ Q i (EL i l1) (EL i l2))
   ⇒ LIST_RELi Q l1 l2`,
  rw[indexedListsTheory.LIST_RELi_EL_EQN]);
*)

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

(* -- *)

val subg_def = Define`
  subg g0 g1 ⇔
    subspt (FST g0) (FST g1) ∧
    IS_SUFFIX (SND g1) (SND g0) ∧
    ALL_DISTINCT (MAP FST (SND g1))`;

(*
val v_rel_def = tDefine"v_rel"`
  (v_rel g (Number i) v ⇔ v = Number i) ∧
  (v_rel g (Word64 w) v ⇔ v = Word64 w) ∧
  (v_rel g (Block n vs) v ⇔
    ∃vs'. v = Block n vs' ∧ LIST_REL (v_rel g) vs vs') ∧
  (v_rel g (RefPtr n) v ⇔ v = RefPtr n) ∧
  (v_rel g (Closure loco vs1 env1 n bod1) v ⇔
     ∃loc vs2 env2 bod2 g0.
       loco = SOME loc ∧ EVEN loc ∧
       LIST_REL (v_rel g) vs1 vs2 ∧ LIST_REL (v_rel g) env1 env2 ∧
       v = Closure loco vs2 env2 n bod2 ∧
       let (es,new_g) = calls [bod1] (insert_each loc 1 g0) in
       if (∀v. has_var v (SND (free es)) ⇒ v < n) then
         bod2 = Call (loc+1) (GENLIST Var n) ∧
         subg (FST new_g,(loc+1,n,HD es)::SND new_g) g
       else
         let (e1,new_g) = calls [bod1] g0 in
         bod2 = HD e1 ∧ subg new_g g (*∧
         loc ∉ domain (FST g)*)) ∧
  (v_rel g (Recclosure loco vs1 env1 fns1 i) v ⇔
     ∃loc vs2 env2 fns2 g0.
       loco = SOME loc ∧ EVEN loc ∧
       LIST_REL (v_rel g) vs1 vs2 ∧ LIST_REL (v_rel g) env1 env2 ∧
       v = Recclosure loco vs2 env2 fns2 i ∧
       let (es,new_g) = calls (MAP SND fns1) (insert_each loc (LENGTH fns1) g0) in
       if EVERY2 (λ(n,_) p. ∀v. has_var v (SND (free [p])) ⇒ v < n) fns1 es
       then
         fns2 = calls_list loc fns1 ∧
         subg (code_list loc (ZIP (MAP FST fns1,es)) new_g) g
       else
         let (es,new_g) = calls (MAP SND fns1) g0 in
         fns2 = ZIP (MAP FST fns1, es) ∧
         subg new_g g (*∧
         DISJOINT (set (GENLIST (λi. 2*i+loc) (LENGTH fns1))) (domain (FST g))*))`
  (WF_REL_TAC `measure (v_size o FST o SND)` >> simp[v_size_def] >>
   rpt strip_tac >> imp_res_tac v_size_lemma >> simp[]);
*)

val v_rel_def = tDefine"v_rel"`
  (v_rel g l (Number i) v ⇔ v = Number i) ∧
  (v_rel g l (Word64 w) v ⇔ v = Word64 w) ∧
  (v_rel g l (Block n vs) v ⇔
    ∃vs'. v = Block n vs' ∧ LIST_REL (v_rel g l) vs vs') ∧
  (v_rel g l (RefPtr n) v ⇔ v = RefPtr n) ∧
  (v_rel g l (Closure loco vs1 env1 n bod1) v ⇔
     ∃loc vs2 env2 bod2 g0.
       loco = SOME loc ∧ EVEN loc ∧
       LIST_REL (v_rel g l) vs1 vs2 ∧ LIST_REL (v_rel g l) env1 env2 ∧
       v = Closure loco vs2 env2 n bod2 ∧
       let (es,new_g) = calls [bod1] (insert_each loc 1 g0) in
       if (∀v. has_var v (SND (free es)) ⇒ v < n) then
         bod2 = Call 0 (loc+1) (GENLIST Var n) ∧
         subg (FST new_g,(loc+1,n,HD es)::SND new_g) g
       else
         let (e1,new_g) = calls [bod1] g0 in
         bod2 = HD e1 ∧ subg new_g g ∧ loc ∈ l) ∧
  (v_rel g l (Recclosure loco vs1 env1 fns1 i) v ⇔
     ∃loc vs2 env2 fns2 g0.
       loco = SOME loc ∧ EVEN loc ∧
       LIST_REL (v_rel g l) vs1 vs2 ∧ LIST_REL (v_rel g l) env1 env2 ∧
       v = Recclosure loco vs2 env2 fns2 i ∧
       let (es,new_g) = calls (MAP SND fns1) (insert_each loc (LENGTH fns1) g0) in
       if EVERY2 (λ(n,_) p. ∀v. has_var v (SND (free [p])) ⇒ v < n) fns1 es
       then
         fns2 = calls_list loc fns1 ∧
         subg (code_list loc (ZIP (MAP FST fns1,es)) new_g) g
       else
         let (es,new_g) = calls (MAP SND fns1) g0 in
         fns2 = ZIP (MAP FST fns1, es) ∧
         subg new_g g ∧
         set (GENLIST (λi. 2*i+loc) (LENGTH fns1)) ⊆ l)`
  (WF_REL_TAC `measure (v_size o FST o SND o SND)` >> simp[v_size_def] >>
   rpt strip_tac >> imp_res_tac v_size_lemma >> simp[]);

val v_rel_ind = theorem"v_rel_ind";

val wfg'_def = Define`
  wfg' g ⇔
    domain (FST g) ⊆ EVEN ∧
    set (MAP FST (SND g)) ⊆ IMAGE SUC (domain (FST g))`;

val wfg_def = Define`
  wfg g ⇔
    domain (FST g) ⊆ EVEN ∧
    set (MAP FST (SND g)) = IMAGE SUC (domain (FST g))`;

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
  rw[subg_def] \\ metis_tac[calls_IS_SUFFIX,calls_subspt,calls_ALL_DISTINCT]);

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
      wfg' g ∧ set (GENLIST (λi. loc + 2 * i) (LENGTH ls)) ⊆ domain (FST g)
      ⇒ wfg' (code_list loc ls g)`,
  rw[wfg'_def,SUBSET_DEF,MEM_GENLIST,MAP_FST_code_list]
  >- (
    fs[ADD1,PULL_EXISTS]
    \\ metis_tac[ADD_ASSOC] )
  \\ metis_tac[]);

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
    \\ fs[wfg'_def,ADD1]
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
  \\ rw[] \\ first_x_assum match_mp_tac
  \\ qmatch_abbrev_tac`lookup k d = SOME _`
  \\ `k ∈ domain d` suffices_by simp[domain_lookup]
  \\ simp[Abbr`d`,domain_FST_insert_each]);

val calls_wfg = Q.store_thm("calls_wfg",
  `∀xs g0 ys g.
    calls xs g0 = (ys,g) ∧
    set (code_locs xs) ⊆ EVEN ∧
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
  \\ fs[SUBSET_DEF,IS_SUFFIX_APPEND] \\ rw[]
  \\ res_tac \\ rw[]
  \\ res_tac \\ rw[] \\ fs[]
  \\ rw[] \\ rfs[]);

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

(* alternative definition of calls which tracks more information

val exp_size_def = closLangTheory.exp_size_def;
val exp1_size_lemma = closLangTheory.exp1_size_lemma;
val EL_MEM_LEMMA = prove(
  ``!xs i x. i < LENGTH xs /\ (x = EL i xs) ==> MEM x xs``,
  Induct \\ fs [] \\ REPEAT STRIP_TAC \\ Cases_on `i` \\ fs []);
val exp3_size_MAP_SND = prove(
  ``!fns. exp3_size (MAP SND fns) <= exp1_size fns``,
  Induct \\ fs [exp_size_def,FORALL_PROD]);
val calls2_def = tDefine "calls2" `
  (calls2 [] g = ([],g)) /\
  (calls2 ((x:closLang$exp)::y::xs) g =
     let (e1,g) = calls2 [x] g in
     let (e2,g) = calls2 (y::xs) g in
       (e1 ++ e2,g)) /\
  (calls2 [Var v] g =
     ([Var v],g)) /\
  (calls2 [If x1 x2 x3] g =
     let (e1,g) = calls2 [x1] g in
     let (e2,g) = calls2 [x2] g in
     let (e3,g) = calls2 [x3] g in
     let e1 = HD e1 in
     let e2 = HD e2 in
     let e3 = HD e3 in
       ([If e1 e2 e3],g)) /\
  (calls2 [Let xs x2] g =
     let (e1,g) = calls2 xs g in
     let (e2,g) = calls2 [x2] g in
     let e2 = HD e2 in
       ([Let e1 e2],g)) /\
  (calls2 [Raise x1] g =
     let (e1,g) = calls2 [x1] g in
     let e1 = HD e1 in
       ([Raise e1],g)) /\
  (calls2 [Tick x1] g =
     let (e1,g) = calls2 [x1] g in
     let e1 = HD e1 in
       ([Tick e1],g)) /\
  (calls2 [Handle x1 x2] g =
     let (e1,g) = calls2 [x1] g in
     let (e2,g) = calls2 [x2] g in
     let e1 = HD e1 in
     let e2 = HD e2 in
       ([Handle e1 e2],g)) /\
  (calls2 [Call dest xs] g =
     let (xs,g) = calls2 xs g in
       ([Call dest xs],g)) /\
  (calls2 [Op op xs] g =
     let (e1,g) = calls2 xs g in
       ([Op op e1],g)) /\
  (calls2 [App loc_opt x xs] g =
     let (es,g) = calls2 xs g in
     let (e1,g) = calls2 [x] g in
     let e1 = HD e1 in
     let loc = (case loc_opt of SOME loc => loc | NONE => 0) in
       if IS_SOME loc_opt /\ loc ∈ (FST (FST g)) then
         if pure x then ([Call (loc+1) es],g) else
           ([Let (SNOC e1 es)
              (Call (loc+1) (GENLIST Var (LENGTH es)))],g)
       else ([App loc_opt e1 es],g)) /\
  (calls2 [Fn loc_opt ws num_args x1] g =
     let loc = (case loc_opt of SOME loc => loc | NONE => 0) in
     let new_g = ((loc INSERT (FST (FST g)),SND(FST g)),SND g) in
     let (e1,new_g) = calls2 [x1] new_g in
     let new_g = (FST new_g,(loc+1,num_args,HD e1)::SND new_g) in
       if closed (Fn loc_opt ws num_args (HD e1)) then
         ([Fn loc_opt ws num_args
             (Call (loc+1) (GENLIST Var num_args))],new_g)
       else
         let g = ((FST(FST g),(loc INSERT (SND (FST g)))),SND g) in
         let (e1,g) = calls2 [x1] g in
           ([Fn loc_opt ws num_args (HD e1)],g)) /\
  (calls2 [Letrec loc_opt ws fns x1] g =
     let loc = (case loc_opt of SOME loc => loc | NONE => 0) in
     let new_g = ((set (GENLIST (λi. 2*i+loc) (LENGTH fns)) ∪ (FST(FST g)),SND (FST g)), SND g) in
     let (fns1,new_g) = calls2 (MAP SND fns) new_g in
       if EVERY2 (\(n,_) p. closed (Fn NONE NONE n p)) fns fns1 then
         let new_g = code_list loc (ZIP (MAP FST fns,fns1)) new_g in
         let (e1,g) = calls2 [x1] new_g in
           ([Letrec loc_opt ws (calls_list loc fns) (HD e1)],new_g)
       else
         let g = ((FST(FST g),(set (GENLIST (λi. 2*i+loc) (LENGTH fns)) ∪ (SND (FST g)))),SND g) in
         let (fns1,g) = calls2 (MAP SND fns) g in
         let (e1,g) = calls2 [x1] g in
           ([Letrec loc_opt ws (ZIP (MAP FST fns,fns1)) (HD e1)],g))`
 (WF_REL_TAC `measure (exp3_size o FST)`
  \\ REPEAT STRIP_TAC
  \\ fs [GSYM NOT_LESS]
  \\ IMP_RES_TAC EL_MEM_LEMMA
  \\ IMP_RES_TAC exp1_size_lemma
  \\ assume_tac (SPEC_ALL exp3_size_MAP_SND)
  \\ DECIDE_TAC);

val calls2_ind = theorem"calls2_ind";

val calls_calls2 = Q.store_thm("calls_calls2",
  `∀xs g0 ys g g02.
    calls xs g0 = (ys,g)
    ⇒
    (*let g2 = set (code_locs xs) DIFF (domain (FST g) DIFF domain (FST g0)) in *)
    ∃g2.
    calls2 xs ((domain(FST g0),g02),SND g0) = (ys,((domain (FST g), g2),SND g))(* ∧
    DISJOINT g02 g2 ∧
    DISJOINT g2 (domain (FST g) DIFF domain (FST g0)) *)`,
  ho_match_mp_tac calls_ind
  \\ rw[calls_def,calls2_def,code_locs_def]
  \\ rpt(pairarg_tac \\ fs[]) \\ rveq
  \\ TRY (
    first_x_assum(qspec_then`g02`mp_tac)\\rw[]
    \\ first_x_assum(qspec_then`g2`mp_tac)\\rw[]
    \\ first_x_assum(qspec_then`g2'`mp_tac)\\rw[])
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ TRY (
    first_x_assum(qspec_then`g02`mp_tac)\\rw[]
    \\ first_x_assum(qspec_then`g2`mp_tac)\\rw[]
    \\ NO_TAC)
  \\ TRY (
    fs[domain_FST_insert_each,GSYM INSERT_SING_UNION]
    \\ first_x_assum(qspec_then`g02`mp_tac)\\rw[]
    \\ spose_not_then strip_assume_tac \\ fs[] \\ rw[]
    \\ first_x_assum(qspec_then`g2`mp_tac)\\rw[]
    \\ spose_not_then strip_assume_tac \\ fs[] \\ rw[]
    \\ fs[domain_lookup] \\ rfs[IS_SOME_EXISTS]
    \\ NO_TAC)
  \\ TRY (
    first_x_assum(qspec_then`0 INSERT g02`mp_tac) \\ rw[]
    \\ fs[domain_FST_insert_each,GSYM INSERT_SING_UNION]
    \\ first_x_assum(qspec_then`g02`mp_tac) \\ rw[]
    \\ fs[] \\ NO_TAC)
  \\ TRY (
    first_x_assum(qspec_then`x INSERT g02`mp_tac) \\ rw[]
    \\ fs[domain_FST_insert_each,GSYM INSERT_SING_UNION]
    \\ first_x_assum(qspec_then`g02`mp_tac) \\ rw[]
    \\ fs[] \\ NO_TAC)
  \\ TRY (
    fs[domain_FST_insert_each]
    \\ last_x_assum(qspec_then`g02`mp_tac) \\ rw[]
    \\ qpat_assum`calls2 _ (code_list _ _ _) = _`mp_tac
    \\ CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV(REWR_CONV (GSYM PAIR)))))
    \\ PURE_REWRITE_TAC[FST_code_list]
    \\ simp[]
    \\ qmatch_goalsub_abbrev_tac`code_list ll ff (g1,SND gg)`
    \\ qispl_then[`ll`,`ff`,`(g1,SND gg)`,`gg`]mp_tac SND_code_list_change
    \\ simp[] \\ disch_then kall_tac \\ unabbrev_all_tac
    \\ first_x_assum(qspec_then`g2`mp_tac)\\rw[] \\ fs[]
    \\ CONV_TAC(QUANT_CONV(LAND_CONV(REWR_CONV(GSYM PAIR))))
    \\ PURE_REWRITE_TAC[FST_code_list]
    \\ simp[]
    \\ match_mp_tac SND_code_list_change
    \\ simp[] )
  \\ TRY (
   fs[domain_FST_insert_each]
   \\ first_x_assum(qspec_then`g02`mp_tac) \\ rw[]
   \\ qmatch_asmsub_abbrev_tac`g01 ∪ g02`
   \\ first_x_assum(qspec_then`g01 ∪ g02`mp_tac)
   \\ rw[]
   \\ first_x_assum(qspec_then`g2'`mp_tac) \\ rw[] ));

(*
val calls2_disjoint = Q.store_thm("calls2_disjoint",
  `∀xs g0 ys g.
    calls2 xs g0 = (ys,g) ∧
    DISJOINT (FST (FST g0)) (SND (FST g0)) ∧
    every_Fn_SOME xs ∧
    DISJOINT (FST (FST g0)) (set (code_locs xs)) ∧
    DISJOINT (SND (FST g0)) (set (code_locs xs))
    ⇒
    DISJOINT (FST (FST g)) (SND (FST g))`,
  ho_match_mp_tac calls2_ind
  \\ rw[calls2_def] \\ fs[code_locs_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ first_x_assum match_mp_tac
*)
*)

(* properties of value relation *)

val subg_refl = Q.store_thm("subg_refl",
  `∀g. ALL_DISTINCT (MAP FST (SND g)) ⇒ subg g g`,
  rw[subg_def]);

val subg_trans = Q.store_thm("subg_trans",
  `∀g1 g2 g3. subg g1 g2 ∧ subg g2 g3 ⇒ subg g1 g3`,
  rw[subg_def] \\ metis_tac[subspt_trans,IS_SUFFIX_TRANS]);

val v_rel_subg = Q.store_thm("v_rel_subg",
  `∀g l v1 v2 g' l'.
    v_rel g l v1 v2 ∧ subg g g' ∧ l ⊆ l' ⇒
    v_rel g' l' v1 v2`,
  ho_match_mp_tac v_rel_ind
  \\ rw[v_rel_def]
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
   ∃e l1 l2 xs n ls g01 g1 l1' l2'.
     x = Full_app e l1 l2 ∧ EL n xs = (LENGTH env1,e) ∧
     calls (MAP SND xs) g01 = (ls,g1) ∧ n < LENGTH ls ∧
     subg (code_list (loc - 2*n) (ZIP (MAP FST xs,ls)) g1) g ∧
     ALOOKUP (SND g) (loc+1) = SOME (LENGTH env1,EL n ls) ∧
     dest_closure (SOME loc) v2 env2 = SOME (Full_app (Call 0 (loc+1) (GENLIST Var (LENGTH env1))) l1' l2') ∧
     LIST_REL (v_rel g l) l1 l1' ∧ LIST_REL (v_rel g l) l2 l2' ∧
     LENGTH env1 ≤ LENGTH l1`,
  rw[dest_closure_def]
  \\ every_case_tac \\ fs[v_rel_def]
  \\ rw[] \\ fs[check_loc_def] \\ rw[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ rfs[]
  \\ fs[LENGTH_NIL] \\ rveq
  \\ imp_res_tac LIST_REL_LENGTH \\ fs[]
  >- (
    qpat_abbrev_tac`el = (_,_)`
    \\ qexists_tac`[el]` \\ simp[Abbr`el`]
    \\ last_assum(part_match_exists_tac(el 2 o strip_conj) o concl)
    \\ qexists_tac`0` \\ simp[]
    \\ imp_res_tac calls_length \\ fs[]
    \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
    \\ conj_tac
    >- ( Cases_on`new_g` \\ fs[code_list_def,subg_def,IS_SUFFIX_APPEND] )
    \\ conj_tac
    >- (
      fs[subg_def,IS_SUFFIX_APPEND]
      \\ simp[ALOOKUP_APPEND]
      \\ BasicProvers.CASE_TAC
      \\ imp_res_tac ALOOKUP_MEM
      \\ rfs[ALL_DISTINCT_APPEND,MEM_MAP,PULL_EXISTS]
      \\ res_tac \\ fs[] )
    \\ rveq \\ fs[] \\ rveq \\ fs[]
    \\ simp[LIST_REL_REVERSE_EQ,TAKE_APPEND2,REVERSE_APPEND,DROP_APPEND2]
    \\ match_mp_tac EVERY2_APPEND_suff
    \\ fsrw_tac[ETA_ss][])
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
    fs[subg_def,IS_SUFFIX_APPEND]
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
  \\ simp[revtakerev,revdroprev]
  \\ match_mp_tac EVERY2_APPEND_suff
  \\ fsrw_tac[ETA_ss][]
  \\ match_mp_tac EVERY2_APPEND_suff
  \\ simp[LIST_REL_GENLIST]
  \\ simp[v_rel_def]
  \\ fsrw_tac[ETA_ss][]
  \\ simp[calls_list_MAPi] \\ rw[]
  \\ qexists_tac`g0` \\ simp[]);

(* compiler correctness *)

val calls_correct = Q.store_thm("calls_correct",
  `(∀tmp xs env1 (s0:'ffi closSem$state) g0 g env2 t0 ys res s l0 l.
    tmp = (xs,env1,s0) ∧
    evaluate (xs,env1,s0) = (res,s) ∧
    res ≠ Rerr (Rabort Rtype_error) ∧
    calls xs g0 = (ys,g) ∧
    every_Fn_SOME xs ∧ every_Fn_vs_NONE xs ∧
    set (code_locs xs) ⊆ EVEN ∧
    wfg g0 ∧
    ALL_DISTINCT (MAP FST (SND g0)) ∧
    ALL_DISTINCT (code_locs xs) ∧
    DISJOINT (IMAGE SUC (set (code_locs xs))) (set (MAP FST (SND g0))) ∧
    LIST_REL (v_rel g0 l0) env1 env2 ∧
    DISJOINT l0 (domain (FST g0)) ∧ DISJOINT l0 (set (code_locs xs)) ∧
    l = l0 ∪ (set (code_locs xs) DIFF domain (FST g)) ∧
    state_rel g0 l0 s0 t0 ∧ code_includes (SND g) t0.code
    ⇒
    ∃res' t.
    evaluate (ys,env2,t0) = (res',t) ∧
    state_rel g l s t ∧
    result_rel (LIST_REL (v_rel g l)) (v_rel g l) res res') ∧
  (∀loco f args (s0:'ffi closSem$state) loc g l t0 res s f' args'.
    evaluate_app loco f args s0 = (res,s) ∧
    res ≠ Rerr (Rabort Rtype_error) ∧
    v_rel g l f f' ∧
    LIST_REL (v_rel g l) args args' ∧
    state_rel g l s0 t0
    ⇒
    ∃res' t.
    evaluate_app loco f' args' t0 = (res',t) ∧
    state_rel g l s t ∧
    result_rel (LIST_REL (v_rel g l)) (v_rel g l) res res')`,
  ho_match_mp_tac evaluate_ind
  \\ conj_tac
  >- (
    rw[]
    \\ fs[calls_def,evaluate_def]
    \\ rveq \\ fs[evaluate_def]
    \\ simp[code_locs_def]
    \\ metis_tac[state_rel_subg])
  \\ conj_tac
  >- (
    rw[evaluate_def,calls_def]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[] \\ rveq
    \\ last_assum(fn th => mp_tac (MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO]calls_subg) th))
    \\ fs[code_locs_def,ALL_DISTINCT_APPEND] \\ strip_tac
    \\ drule calls_subg
    \\ impl_tac
    >- (
      last_assum(fn th => mp_tac (MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO]calls_ALL_DISTINCT) th))
      \\ rw[]
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ fs[IN_DISJOINT,SUBSET_DEF]
      \\ metis_tac[numTheory.INV_SUC] )
    \\ strip_tac
    \\ imp_res_tac calls_length
    \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
    \\ cheat )
  (* Var *)
  \\ conj_tac >- cheat
  (* If *)
  \\ conj_tac >- cheat
  (* Let *)
  \\ conj_tac >- cheat
  (* Raise *)
  \\ conj_tac >- cheat
  (* Handle *)
  \\ conj_tac >- cheat
  (* Op *)
  \\ conj_tac >- cheat
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
    \\ simp[v_rel_def]
    \\ fs[code_locs_def,IN_EVEN]
    \\ fsrw_tac[ETA_ss][PULL_EXISTS]
    \\ fs[closed_Fn]
    \\ CONV_TAC(RESORT_EXISTS_CONV(List.rev))
    \\ `subg g0 (insert_each x 1 g0)`
    by ( simp[subg_def,insert_each_subspt] )
    \\ `subg g0 g`
    by (
      every_case_tac \\ fs[] \\ rw[]
      \\ drule calls_subg
      \\ qhdtm_x_assum`calls`kall_tac
      \\ drule calls_subg
      \\ (impl_tac >- fs[ALL_DISTINCT_APPEND])
      \\ strip_tac
      \\ (impl_tac >- fs[ALL_DISTINCT_APPEND])
      \\ strip_tac \\ fs[]
      \\ match_mp_tac subg_trans
      \\ last_assum (part_match_exists_tac (hd o strip_conj) o concl)
      \\ simp[]
      \\ match_mp_tac subg_trans
      \\ asm_exists_tac \\ simp[]
      \\ fs[subg_def]
      \\ fs[IS_SUFFIX_APPEND,GSYM ADD1]
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ rfs[SUBSET_DEF]
      \\ fs[ALL_DISTINCT_APPEND]
      \\ metis_tac[numTheory.INV_SUC] )
    \\ qpat_abbrev_tac`l = l0 ∪ _`
    \\ `l0 ⊆ l` by simp[Abbr`l`]
    \\ `state_rel g l s t0` by metis_tac[state_rel_subg]
    \\ `subspt (FST g0) (FST g)` by fs[subg_def]
    \\ qexists_tac`g0` \\ fs[]
    \\ imp_res_tac calls_length
    \\ fs[quantHeuristicsTheory.LIST_LENGTH_2] \\ rveq
    \\ fs[]
    \\ CASE_TAC \\ fs[] \\ rveq
    \\ simp[evaluate_def]
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
          by ( imp_res_tac calls_wfg \\ fs[wfg_def] )
          \\ fs[SUBSET_DEF]
          \\ metis_tac[numTheory.INV_SUC] ))
      \\ match_mp_tac subg_refl \\ fs[subg_def] ))
    \\ match_mp_tac (GEN_ALL (MP_CANON LIST_REL_mono))
    \\ first_assum(part_match_exists_tac (last o strip_conj) o concl)
    \\ metis_tac[v_rel_subg])
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
    \\ impl_keep_tac >- fs[ALL_DISTINCT_APPEND] \\ strip_tac
    \\ drule calls_subg
    \\ impl_keep_tac >- (
      imp_res_tac calls_add_SUC_code_locs
      \\ fs[subg_def,ALL_DISTINCT_APPEND,IN_DISJOINT,SUBSET_DEF]
      \\ metis_tac[numTheory.INV_SUC] )
    \\ strip_tac
    \\ `g'' = g` by (every_case_tac \\ fs[])
    \\ rveq \\ fs[]
    \\ qpat_abbrev_tac`l = l0 ∪ _`
    \\ `l0 ⊆ l` by simp[Abbr`l`]
    \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      strip_tac \\ rveq \\ rfs[]
      \\ first_x_assum drule \\ fs[DISJOINT_SYM]
      \\ rpt(disch_then drule)
      \\ impl_tac >- ( metis_tac[code_includes_subg] )
      \\ qpat_abbrev_tac`l' = l0 ∪ _`
      \\ `l' ⊆ l`
      by (
        rw[Abbr`l'`,Abbr`l`,SUBSET_DEF]
        \\ spose_not_then strip_assume_tac
        \\ imp_res_tac calls_add_SUC_code_locs
        \\ `x ∉ set (code_locs [x1])` by (fs[ALL_DISTINCT_APPEND]\\ metis_tac[])
        \\ `MEM (SUC x) (MAP FST (SND g))`
        by ( imp_res_tac calls_wfg \\ fs[wfg_def] )
        \\ `¬MEM (SUC x) (MAP FST (SND g'))`
        by (
          imp_res_tac calls_wfg
          \\ fs[wfg_def]
          \\ fs[SET_EQ_SUBSET,SUBSET_DEF,PULL_EXISTS]
          \\ metis_tac[] )
        \\ fs[SUBSET_DEF]
        \\ metis_tac[numTheory.INV_SUC] )
      \\ strip_tac
      \\ imp_res_tac calls_length
      \\ `state_rel g l r t` by metis_tac[state_rel_subg,evaluate_const]
      \\ `exc_rel (v_rel g l) e e'`
      by ( Cases_on`e`\\fs[] \\ metis_tac[v_rel_subg])
      \\ every_case_tac \\ fs[] \\ rw[evaluate_def]
      \\ simp[evaluate_append])
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ qmatch_asmsub_rename_tac`err ≠ Rerr _`
    \\ Cases_on`err = Rerr (Rabort Rtype_error)` \\ fs[]
    \\ first_x_assum drule \\ fs[]
    \\ first_x_assum drule \\ fs[DISJOINT_SYM]
    \\ rpt(disch_then drule)
    \\ impl_tac >- metis_tac[code_includes_subg]
    \\ strip_tac \\ fs[]
    \\ qmatch_asmsub_abbrev_tac`v_rel g' l'`
    \\ `l' ⊆ l`
    by (
      rw[Abbr`l'`,Abbr`l`,SUBSET_DEF]
      \\ spose_not_then strip_assume_tac
      \\ imp_res_tac calls_add_SUC_code_locs
      \\ `x ∉ set (code_locs [x1])` by (fs[ALL_DISTINCT_APPEND]\\ metis_tac[])
      \\ `MEM (SUC x) (MAP FST (SND g))`
      by ( imp_res_tac calls_wfg \\ fs[wfg_def] )
      \\ `¬MEM (SUC x) (MAP FST (SND g'))`
      by (
        imp_res_tac calls_wfg
        \\ fs[wfg_def]
        \\ fs[SET_EQ_SUBSET,SUBSET_DEF,PULL_EXISTS]
        \\ metis_tac[] )
      \\ fs[SUBSET_DEF]
      \\ metis_tac[numTheory.INV_SUC] )
    \\ disch_then(qspecl_then[`env2`,`t`,`l'`]mp_tac)
    \\ `DISJOINT l' (domain (FST g'))`
    by (
      fs[Abbr`l'`,IN_DISJOINT]
      \\ reverse conj_tac >- metis_tac[]
      \\ spose_not_then strip_assume_tac
      \\ `x ∉ domain (FST g0)` by metis_tac[]
      \\ `¬MEM (SUC x) (MAP FST (SND g0))` by fs[wfg_def]
      \\ `wfg g'` by imp_res_tac calls_wfg
      \\ `MEM (SUC x) (MAP FST (SND g'))` by fs[wfg_def]
      \\ `MEM x (code_locs args)`
      by (
        imp_res_tac calls_add_SUC_code_locs
        \\ fs[SUBSET_DEF]
        \\ metis_tac[numTheory.INV_SUC])
      \\ metis_tac[])
    \\ `DISJOINT l' (set (code_locs [x1]))`
    by (
      fs[Abbr`l'`,IN_DISJOINT]
      \\ spose_not_then strip_assume_tac
      \\ fs[ALL_DISTINCT_APPEND]
      \\ metis_tac[] )
    \\ `l0 ⊆ l'` by simp[Abbr`l'`]
    \\ impl_tac
    >- ( metis_tac[LIST_REL_mono,v_rel_subg,subg_trans,evaluate_const,calls_wfg] )
    \\ strip_tac \\ rveq
    \\ qmatch_assum_abbrev_tac`state_rel g ll _ _`
    \\ `ll ⊆ l`
    by ( simp[Abbr`ll`,Abbr`l`,SUBSET_DEF] )
    \\ `l' ⊆ ll ` by simp[Abbr`ll`]
    \\ `subg g g`
    by (
      match_mp_tac subg_refl
      \\ imp_res_tac calls_ALL_DISTINCT
      \\ rfs[DISJOINT_SYM] )
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
        \\ conj_tac >- metis_tac[state_rel_subg,evaluate_const]
        \\ Cases_on`e` \\ fs[]
        \\ metis_tac[v_rel_subg])
      \\ strip_tac \\ fs[] \\ rfs[]
      \\ imp_res_tac evaluate_length_imp
      \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
      \\ rveq \\ fs[]
      \\ first_x_assum drule
      \\ qmatch_assum_rename_tac `LIST_REL (v_rel g' l') ev1 ev2`
      \\ `LIST_REL (v_rel g ll) ev1 ev2` by metis_tac[LIST_REL_mono,v_rel_subg]
      \\ disch_then drule
      \\ disch_then drule
      \\ strip_tac \\ simp[]
      \\ conj_tac >- metis_tac[state_rel_subg,state_rel_def]
      \\ Cases_on`res` \\ fs[] \\ TRY (Cases_on`e` \\ fs[])
      \\ TRY (match_mp_tac (GEN_ALL (MP_CANON LIST_REL_mono)))
      \\ metis_tac[v_rel_subg])
    \\ qpat_assum`Abbrev(IS_SOME _ ∧ _)`mp_tac
    \\ simp[markerTheory.Abbrev_def,IS_SOME_EXISTS]
    \\ strip_tac \\ rveq \\ fs[]
    \\ `x ∈ domain (FST g)` by simp[domain_lookup]
    \\ `wfg g` by imp_res_tac calls_wfg
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
      \\ first_x_assum drule
      \\ qmatch_assum_rename_tac `LIST_REL (v_rel g' l') ev1 ev2`
      \\ `LIST_REL (v_rel g ll) ev1 ev2` by metis_tac[LIST_REL_mono,v_rel_subg]
      \\ rpt(disch_then drule)
      \\ strip_tac
      \\ simp[find_code_def]
      \\ Cases_on`ev1 = []`
      >- ( imp_res_tac evaluate_length_imp \\ rfs[] )
      \\ fs[evaluate_app_rw]
      \\ qpat_assum`_ = (res,_)`mp_tac
      \\ BasicProvers.TOP_CASE_TAC \\ fs[]
      \\ drule (GEN_ALL dest_closure_v_rel_lookup)
      \\ disch_then drule
      \\ disch_then drule
      \\ impl_tac >- rw[]
      \\ strip_tac
      \\ drule (GEN_ALL code_includes_ALOOKUP)
      \\ disch_then drule \\ strip_tac
      \\ `t.code = t0.code` by metis_tac[evaluate_const]
      \\ simp[]
      \\ imp_res_tac LIST_REL_LENGTH \\ simp[]
      \\ Cases_on`ev2 = []` \\ fs[]
      \\ fs[evaluate_app_rw]
      \\ qpat_assum`_ = (res',_)`mp_tac
      \\ imp_res_tac state_rel_clock \\ fs[]
      \\ IF_CASES_TAC \\ fs[]
      >- (
        strip_tac \\ rveq
        \\ strip_tac \\ rveq \\ fs[]
        \\ imp_res_tac evaluate_length_imp \\ fs[]
        \\ match_mp_tac state_rel_with_clock
        \\ metis_tac[state_rel_subg] )
      \\ simp[evaluate_def,evaluate_GENLIST_Var]
      \\ simp[find_code_def]
      \\ simp[Once dec_clock_def]
      \\ `t'.code = t.code` by metis_tac[evaluate_const]
      \\ fs[]
      \\ simp[Once dec_clock_def]
      \\ cheat )
    \\ simp[evaluate_append]
    \\ imp_res_tac calls_length
    \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
    \\ rveq \\ fs[]
    \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      rw[] \\ rw[]
      \\ TRY(Cases_on`e`\\fs[])
      \\ metis_tac[state_rel_subg,state_rel_def,v_rel_subg])
    \\ strip_tac \\ fs[]
    \\ simp[evaluate_GENLIST_Var]
    \\ imp_res_tac evaluate_length_imp
    \\ simp[TAKE_APPEND1,TAKE_LENGTH_ID_rwt]
    \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
    \\ rveq \\ rfs[]
    \\ first_x_assum drule
    \\ qmatch_assum_rename_tac `LIST_REL (v_rel g' l') ev1 ev2`
    \\ `LIST_REL (v_rel g ll) ev1 ev2` by metis_tac[LIST_REL_mono,v_rel_subg]
    \\ rpt(disch_then drule)
    \\ strip_tac
    \\ simp[find_code_def]
    \\ `t'.code = t0.code` by metis_tac[evaluate_const]
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
    \\ imp_res_tac code_includes_ALOOKUP \\ fs[]
    \\ IF_CASES_TAC \\ fs[]
    >- (
      strip_tac \\ rveq
      \\ strip_tac \\ rveq
      \\ fs[]
      \\ match_mp_tac state_rel_with_clock
      \\ metis_tac[state_rel_subg])
    \\ simp[evaluate_def,evaluate_GENLIST_Var]
    \\ simp[find_code_def]
    \\ simp[Once dec_clock_def]
    \\ simp[Once dec_clock_def]
    \\ cheat)
  (* Tick *)
  \\ conj_tac >- cheat
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
    \\ disch_then drule
    \\ rw[] \\ rw[] )
  \\ conj_tac >- ( rw[evaluate_def] \\ rw[] )
  (* app cons *)
  \\ simp[evaluate_def]
  \\ rpt gen_tac \\ strip_tac
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ BasicProvers.TOP_CASE_TAC
  >- (
    rw[] \\ rw[evaluate_def]
    \\ cheat)
  \\ rw[] \\ fs[]
  \\ cheat);

val _ = export_theory();
