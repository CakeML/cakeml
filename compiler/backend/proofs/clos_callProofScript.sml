open preamble match_goal
     closSemTheory closPropsTheory
     clos_callTheory;

val _ = new_theory"clos_callProof";

(* value relation *)

open clos_knownProofTheory

(* TODO: above open is just for subspt *)

(* TODO: move *)

val IS_SUFFIX_TRANS = Q.store_thm("IS_SUFFIX_TRANS",
  `∀l1 l2 l3. IS_SUFFIX l1 l2 ∧ IS_SUFFIX l2 l3 ⇒ IS_SUFFIX l1 l3`,
  rw[IS_SUFFIX_APPEND] \\ metis_tac[APPEND_ASSOC]);

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

val v_rel_def = tDefine"v_rel"`
  (v_rel g (Number i) v ⇔ v = Number i) ∧
  (v_rel g (Word64 w) v ⇔ v = Word64 w) ∧
  (v_rel g (Block n vs) v ⇔
    ∃vs'. v = Block n vs' ∧ LIST_REL (v_rel g) vs vs') ∧
  (v_rel g (RefPtr n) v ⇔ v = RefPtr n) ∧
  (v_rel g (Closure loco vs1 env1 n bod1) v ⇔
     ∃loc vs2 env2 n bod2 g0.
       loco = SOME loc ∧ EVEN loc ∧
       LIST_REL (v_rel g) vs1 vs2 ∧ LIST_REL (v_rel g) env1 env2 ∧
       v = Closure loco vs2 env2 n bod2 ∧
       subspt (FST g0) (FST g) ∧
       let es = FST(calls [bod1] g0) in
       if (∀v. has_var v (SND (free es)) ⇒ v < n) then
         bod2 = Call (loc+1) (GENLIST Var n) ∧
         ALOOKUP (SND g) (loc+1) = SOME (n, HD es)
       else
         bod2 = HD(FST(calls [bod1] g0))) ∧
  (v_rel g (Recclosure loco vs1 env1 fns1 i) v ⇔
     ∃loc vs2 env2 fns2 g0.
       loco = SOME loc ∧ EVEN loc ∧
       LIST_REL (v_rel g) vs1 vs2 ∧ LIST_REL (v_rel g) env1 env2 ∧
       v = Recclosure loco vs2 env2 fns2 i ∧
       subspt (FST g0) (FST g) ∧
       let es = FST (calls (MAP SND fns1) (insert_each loc (LENGTH fns1) g0)) in
       if EVERY2 (λ(n,_) p. ∀v. has_var v (SND (free [p])) ⇒ v < n) fns1 es then
         fns2 = calls_list loc fns1 ∧
         LIST_RELi (λi (n,_) p. ALOOKUP (SND g) (loc + 2*i) = SOME (n,p)) fns1 es
       else
         fns2 = ZIP (MAP FST fns1, FST (calls (MAP SND fns1) g0)))`
  (WF_REL_TAC `measure (v_size o FST o SND)` >> simp[v_size_def] >>
   rpt strip_tac >> imp_res_tac v_size_lemma >> simp[]);

val v_rel_ind = theorem"v_rel_ind";

val state_rel_def = Define`
  state_rel g (s:'ffi closSem$state) (t:'ffi closSem$state) ⇔
    (s.ffi = t.ffi) ∧
    (s.clock = t.clock) ∧
    LIST_REL (OPTREL (v_rel g)) s.globals t.globals ∧
    fmap_rel (ref_rel (v_rel g)) s.refs t.refs ∧
    s.code = FEMPTY ∧ t.code = FEMPTY |++ SND g`;

(* properties of value relation *)

val subg_def = Define`
  subg g0 g1 ⇔
    subspt (FST g0) (FST g1) ∧
    IS_SUFFIX (SND g1) (SND g0) ∧
    (ALL_DISTINCT (MAP FST (SND g0)) ⇒ ALL_DISTINCT (MAP FST (SND g1)))`;

(*
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
  \\ fs[subg_def]
  \\ imp_res_tac subspt_trans
  \\ asm_exists_tac \\ fs[]
  \\ qmatch_goalsub_abbrev_tac`COND test`
  \\ rw[] \\ fs[]
  \\ fs[indexedListsTheory.LIST_RELi_EL_EQN]
  \\ rw[]
  \\ TRY (first_x_assum drule \\ rw[] \\ pairarg_tac \\ fs[])
  \\ metis_tac[ALOOKUP_prefix,IS_SUFFIX_APPEND]
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

(*
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
  \\ metis_tac[]

val calls_ALL_DISTINCT = Q.store_thm("calls_ALL_DISTINCT",
  `∀xs g0 ys g.
    calls xs g0 = (ys,g) ∧ ALL_DISTINCT (MAP FST (SND g0)) ∧
    DISJOINT (IMAGE SUC (set (code_locs xs))) (set (MAP FST (SND g0)))
    ⇒ ALL_DISTINCT (MAP FST (SND g))`,
  ho_match_mp_tac calls_ind
  \\ rw[calls_def] \\ rw[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
  \\ fs[code_locs_def]
  \\ every_case_tac \\ fs[] \\ rw[]

val calls_subg = Q.store_thm("calls_subg",
  `∀xs g0 ys g. calls xs g0 = (ys,g) ⇒ subg g0 g`,
  rw[subg_def] \\ metis_tac[calls_IS_SUFFIX,calls_subspt]);
*)

(* compiler correctness *)

(*
val calls_correct = Q.store_thm("calls_correct",
  `(∀tmp xs env1 (s0:'ffi closSem$state) g0 g env2 t0 ys res s.
    tmp = (xs,env1,s0) ∧
    evaluate (xs,env1,s0) = (res,s) ∧
    calls xs g0 = (ys,g) ∧
    LIST_REL (v_rel g) env1 env2 ∧
    state_rel g s0 t0
    ⇒
    ∃res' t.
    evaluate (ys,env2,t0) = (res',t) ∧
    state_rel g s t ∧
    result_rel (LIST_REL (v_rel g)) (v_rel g) res res') ∧
  (∀loco f args (s0:'ffi closSem$state) loc g0 g t0 res s f' args'.
    evaluate_app loco f args s0 = (res,s) ∧
    v_rel g f f' ∧ loco = SOME loc ∧ EVEN loc ∧
    LIST_REL (v_rel g) args args' ∧
    state_rel g s0 t0
    ⇒
    ∃res' t.
    evaluate_app loco f' args' t0 = (res',t) ∧
    state_rel g s t ∧
    result_rel (LIST_REL (v_rel g)) (v_rel g) res res')`,
  ho_match_mp_tac evaluate_ind
  \\ conj_tac
  >- ( simp[evaluate_def,calls_def] )
  \\ conj_tac
  >- (
    rw[evaluate_def,calls_def]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[] \\ rveq
    \\ every_case_tac \\ fs[] \\ rveq \\ fs[] \\ rfs[]
    \\ first_x_assum drule
    \\ simp[GSYM AND_IMP_INTRO]
    \\ rpt (disch_then drule)
  );
*)

val _ = export_theory();
