open preamble match_goal
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
(* -- *)

val subg_def = Define`
  subg g0 g1 ⇔
    subspt (FST g0) (FST g1) ∧
    IS_SUFFIX (SND g1) (SND g0) ∧
    ALL_DISTINCT (MAP FST (SND g1))`;

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
         bod2 = HD e1 ∧ subg new_g g) ∧
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
         subg new_g g)`
  (WF_REL_TAC `measure (v_size o FST o SND)` >> simp[v_size_def] >>
   rpt strip_tac >> imp_res_tac v_size_lemma >> simp[]);

val v_rel_ind = theorem"v_rel_ind";

val code_includes_def = Define`
  code_includes al code ⇔
    ∀k v. ALOOKUP al k = SOME v ⇒ FLOOKUP code k = SOME v`;

val state_rel_def = Define`
  state_rel g (s:'ffi closSem$state) (t:'ffi closSem$state) ⇔
    (s.ffi = t.ffi) ∧
    (s.clock = t.clock) ∧
    LIST_REL (OPTREL (v_rel g)) s.globals t.globals ∧
    fmap_rel (ref_rel (v_rel g)) s.refs t.refs ∧
    s.code = FEMPTY ∧ code_includes (SND g) t.code`;

(* properties of value relation *)

val subg_refl = Q.store_thm("subg_refl",
  `∀g. ALL_DISTINCT (MAP FST (SND g)) ⇒ subg g g`,
  rw[subg_def]);

val subg_trans = Q.store_thm("subg_trans",
  `∀g1 g2 g3. subg g1 g2 ∧ subg g2 g3 ⇒ subg g1 g3`,
  rw[subg_def] \\ metis_tac[subspt_trans,IS_SUFFIX_TRANS]);

val v_rel_subg = Q.store_thm("v_rel_subg",
  `∀g v1 v2 g'.
    v_rel g v1 v2 ∧ subg g g' ⇒
    v_rel g' v1 v2`,
  ho_match_mp_tac v_rel_ind
  \\ rw[v_rel_def]
  \\ fsrw_tac[ETA_ss][PULL_FORALL]
  \\ rpt(
    qmatch_assum_abbrev_tac`LIST_REL (v_rel g) l1 l2`
    \\ `LIST_REL (v_rel g') l1 l2`
    by (
      match_mp_tac EVERY2_MEM_MONO
      \\ first_assum(part_match_exists_tac (last o strip_conj) o concl)
      \\ simp[FORALL_PROD]
      \\ imp_res_tac LIST_REL_LENGTH
      \\ simp[MEM_ZIP,PULL_EXISTS]
      \\ metis_tac[MEM_EL] )
    \\ qpat_assum`LIST_REL (v_rel g) l1 l2` kall_tac
    \\ map_every qunabbrev_tac[`l2`,`l1`])
  \\ fs[]
  \\ qexists_tac`g0`
  \\ rpt(pairarg_tac \\ fs[])
  \\ IF_CASES_TAC \\ fs[]
  \\ metis_tac[subg_trans]);

val state_rel_subg = Q.store_thm("state_rel_subg",
  `subg g0 g ∧ state_rel g0 s t ∧ code_includes (SND g) t.code ⇒ state_rel g s t`,
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

(*
val dest_closure_v_rel_lookup = Q.store_thm("dest_closure_v_rel_lookup",
  `dest_closure (SOME loc) v1 env = SOME x ∧
   v_rel g v1 v2 ∧ loc ∈ domain (FST g) ⇒
   ∃e2. ALOOKUP (SND g) (loc+1) = SOME (LENGTH env,e2)`,
  rw[dest_closure_def]
  \\ every_case_tac \\ fs[v_rel_def]
  \\ rw[] \\ fs[check_loc_def] \\ rw[]
  \\ rpt(pairarg_tac \\ fs[])
*)

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
    qcase_tac`MEM 1n _`
    \\ imp_res_tac calls_add_SUC_code_locs
    \\ fs[ALL_DISTINCT_APPEND,SUBSET_DEF]
    \\ metis_tac[ONE,numTheory.INV_SUC] )
  \\ TRY (
    qcase_tac`MEM (_ + 1n) _`
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

(* compiler correctness *)

val calls_correct = Q.store_thm("calls_correct",
  `(∀tmp xs env1 (s0:'ffi closSem$state) g0 g env2 t0 ys res s.
    tmp = (xs,env1,s0) ∧
    evaluate (xs,env1,s0) = (res,s) ∧
    res ≠ Rerr (Rabort Rtype_error) ∧
    calls xs g0 = (ys,g) ∧
    every_Fn_SOME xs ∧ every_Fn_vs_NONE xs ∧
    set (code_locs xs) ⊆ EVEN ∧
    ALL_DISTINCT (MAP FST (SND g0)) ∧
    ALL_DISTINCT (code_locs xs) ∧
    DISJOINT (IMAGE SUC (set (code_locs xs))) (set (MAP FST (SND g0))) ∧
    (*
    subg g00 g0 ∧ LIST_REL (v_rel g00) env1 env2 ∧ state_rel g00 s0 t0 ∧
    *)
    LIST_REL (v_rel g0) env1 env2 ∧
    state_rel g0 s0 t0 ∧ code_includes (SND g) t0.code
    ⇒
    ∃res' t.
    evaluate (ys,env2,t0) = (res',t) ∧
    state_rel g s t ∧
    result_rel (LIST_REL (v_rel g)) (v_rel g) res res') ∧
  (∀loco f args (s0:'ffi closSem$state) loc g t0 res s f' args'.
    evaluate_app loco f args s0 = (res,s) ∧
    res ≠ Rerr (Rabort Rtype_error) ∧
    v_rel g f f' ∧
    LIST_REL (v_rel g) args args' ∧
    state_rel g s0 t0
    ⇒
    ∃res' t.
    evaluate_app loco f' args' t0 = (res',t) ∧
    state_rel g s t ∧
    result_rel (LIST_REL (v_rel g)) (v_rel g) res res')`,
  ho_match_mp_tac evaluate_ind
  \\ conj_tac
  >- (
    rw[]
    \\ fs[calls_def,evaluate_def]
    \\ rveq \\ fs[evaluate_def]
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
    \\ `state_rel g s t0` by metis_tac[state_rel_subg]
    \\ `subspt (FST g0) (FST g)` by fs[subg_def]
    \\ qexists_tac`g0` \\ fs[]
    \\ imp_res_tac calls_length
    \\ fs[quantHeuristicsTheory.LIST_LENGTH_2] \\ rveq
    \\ fs[]
    \\ CASE_TAC \\ fs[] \\ rveq
    \\ simp[evaluate_def]
    \\ TRY ( reverse conj_tac >- (
      match_mp_tac subg_refl \\ fs[subg_def] ))
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
    \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      strip_tac \\ rveq \\ rfs[]
      \\ first_x_assum drule \\ simp[]
      \\ rpt(disch_then drule)
      \\ impl_tac >- ( metis_tac[code_includes_subg] )
      \\ strip_tac
      \\ imp_res_tac calls_length
      \\ `state_rel g r t` by metis_tac[state_rel_subg,evaluate_const]
      \\ `exc_rel (v_rel g) e e'`
      by ( Cases_on`e`\\fs[] \\ metis_tac[v_rel_subg])
      \\ every_case_tac \\ fs[] \\ rw[evaluate_def]
      \\ simp[evaluate_append])
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ qmatch_asmsub_rename_tac`err ≠ Rerr _`
    \\ Cases_on`err = Rerr (Rabort Rtype_error)` \\ fs[]
    \\ first_x_assum drule \\ fs[]
    \\ first_x_assum drule \\ fs[]
    \\ rpt(disch_then drule)
    \\ impl_tac >- metis_tac[code_includes_subg]
    \\ strip_tac \\ fs[]
    \\ disch_then(qspecl_then[`env2`,`t`]mp_tac)
    \\ impl_tac
    >- ( metis_tac[LIST_REL_mono,v_rel_subg,subg_trans,evaluate_const] )
    \\ strip_tac \\ rveq
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
      >- ( strip_tac \\ rveq \\ fs[] )
      \\ strip_tac \\ fs[] \\ rfs[]
      \\ imp_res_tac evaluate_length_imp
      \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
      \\ rveq \\ fs[]
      \\ first_x_assum drule
      \\ qmatch_assum_rename_tac `LIST_REL (v_rel g') ev1 ev2`
      \\ `LIST_REL (v_rel g) ev1 ev2` by metis_tac[LIST_REL_mono,v_rel_subg]
      \\ fs[markerTheory.Abbrev_def]
      \\ Cases_on`loco` \\ fs[domain_lookup])
    \\ fs[markerTheory.Abbrev_def,IS_SOME_EXISTS]
    \\ rveq \\ fs[]
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
      \\ qmatch_assum_rename_tac `LIST_REL (v_rel g') ev1 ev2`
      \\ `LIST_REL (v_rel g) ev1 ev2` by metis_tac[LIST_REL_mono,v_rel_subg]
      \\ rpt(disch_then drule)
      \\ strip_tac
      \\ simp[find_code_def]
      \\ Cases_on`ev1 = []`
      >- ( imp_res_tac evaluate_length_imp \\ rfs[] )
      \\ fs[evaluate_app_rw]
      \\ qpat_assum`_ = (res,_)`mp_tac
      \\ BasicProvers.TOP_CASE_TAC \\ fs[]
      \\ rfs[domain_lookup]
      \\ cheat )
    \\ simp[evaluate_append]
    \\ imp_res_tac calls_length
    \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
    \\ rveq \\ fs[]
    \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
    >- ( rw[] \\ rw[] )
    \\ strip_tac \\ fs[]
    \\ simp[evaluate_GENLIST_Var]
    \\ imp_res_tac evaluate_length_imp
    \\ simp[TAKE_APPEND1,TAKE_LENGTH_ID_rwt]
    \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
    \\ rveq \\ rfs[]
    \\ first_x_assum drule
    \\ qmatch_assum_rename_tac `LIST_REL (v_rel g') ev1 ev2`
    \\ `LIST_REL (v_rel g) ev1 ev2` by metis_tac[LIST_REL_mono,v_rel_subg]
    \\ rpt(disch_then drule)
    \\ strip_tac
    \\ simp[find_code_def]
    \\ imp_res_tac evaluate_const \\ fs[]
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
    \\ disch_then drule
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
