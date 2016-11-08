open preamble
     bvlSemTheory bvlPropsTheory
     bvl_inlineTheory;

val _ = new_theory"bvl_inlineProof";

val code_rel_def = Define `
  code_rel (:'ffi) c1 c2 <=>
    !n arity e1.
      lookup n c1 = SOME (arity,e1) ==>
      ?e2. lookup n c2 = SOME (arity,e2) /\
           !(s:'ffi bvlSem$state) env res t.
             LENGTH env = arity /\ res <> Rerr (Rabort Rtype_error) /\
             evaluate ([e1],env,s with code := c1) = (res,t with code := c1) ==>
             evaluate ([e2],env,s with code := c2) = (res,t with code := c2)`

val code_rel_refl = Q.store_thm("code_rel_refl",
  `!c. code_rel (:'ffi) c c`,
  fs [code_rel_def]);

val code_rel_trans = Q.store_thm("code_rel_trans",
  `!c1 c2 c3.
      code_rel (:'ffi) c1 c2 /\ code_rel (:'ffi) c2 c3 ==>
      code_rel (:'ffi) c1 c3`,
  fs [code_rel_def] \\ rw [] \\ res_tac
  \\ first_x_assum drule \\ rw [] \\ fs []);

val exp_rel_def = Define `
  exp_rel (:'ffi) c e1 e2 <=>
    !(s:'ffi bvlSem$state) env res t.
      evaluate ([e1],env,s) = (res,t) /\ s.code = c /\
      res <> Rerr (Rabort Rtype_error) ==>
      evaluate ([e2],env,s) = (res,t)`

val evaluate_code_insert = Q.store_thm("evaluate_code_insert",
  `!xs env (s:'ffi bvlSem$state) res t e1 e2 n arity c.
      evaluate (xs,env,s) = (res,t) /\
      exp_rel (:'ffi) (insert n (arity,e2) c) e1 e2 /\
      res ≠ Rerr (Rabort Rtype_error) /\
      lookup n c = SOME (arity,e1) /\
      s.code = c ==>
      evaluate (xs,env,s with code := insert n (arity,e2) c) =
                  (res,t with code := insert n (arity,e2) c)`,
  recInduct bvlSemTheory.evaluate_ind \\ reverse (rw [])
  \\ fs [bvlSemTheory.evaluate_def]
  THEN1 (* Call *)
   (Cases_on `evaluate (xs,env,s1)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ fs [] \\ first_x_assum drule
    \\ disch_then drule \\ fs []
    \\ Cases_on `q` \\ fs [] \\ rw []
    \\ Cases_on `find_code dest a (insert n (arity,e2) s1.code) =
                 find_code dest a r.code` \\ fs []
    THEN1
     (BasicProvers.TOP_CASE_TAC \\ fs []
      \\ PairCases_on `x` \\ fs [] \\ IF_CASES_TAC \\ fs [] \\ rw [] \\ fs []
      \\ rfs [] \\ imp_res_tac evaluate_code \\ fs [])
    \\ reverse (Cases_on `dest`) \\ fs [] THEN1
     (fs [find_code_def,lookup_insert]
      \\ Cases_on `lookup x r.code` \\ fs []
      \\ Cases_on `x'` \\ fs []
      \\ Cases_on `LENGTH a = q` \\ fs []
      \\ Cases_on `x = n` \\ fs []
      \\ rveq \\ fs [] \\ imp_res_tac evaluate_code \\ fs []
      \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
      \\ first_x_assum drule
      \\ disch_then drule
      \\ fs [exp_rel_def] \\ rw [])
    \\ fs [find_code_def,lookup_insert] \\ IF_CASES_TAC \\ fs []
    \\ Cases_on `LAST a` \\ fs []
    \\ Cases_on `lookup n' r.code` \\ fs []
    \\ PairCases_on `x` \\ fs []
    \\ Cases_on `LENGTH a = x0 + 1` \\ fs []
    \\ Cases_on `n' = n` \\ fs []
    \\ fs [] \\ rveq \\ fs [] \\ imp_res_tac evaluate_code \\ fs []
    \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule
    \\ fs [exp_rel_def] \\ rw [])
  \\ TRY (IF_CASES_TAC \\ fs [] \\ NO_TAC)
  THEN1
   (Cases_on `evaluate (xs,env,s)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ fs [] \\ imp_res_tac evaluate_code \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule \\ fs []
    \\ Cases_on `q` \\ fs []
    \\ Cases_on `do_app op (REVERSE a) r` \\ fs []
    \\ TRY (Cases_on `a'` \\ fs [] \\ rveq \\ fs []) \\ rveq \\ fs []
    \\ TRY (drule (GEN_ALL bvlPropsTheory.do_app_with_code) ORELSE
            drule (GEN_ALL bvlPropsTheory.do_app_with_code_err))
    \\ disch_then (qspec_then `insert n (arity,e2) s.code` mp_tac)
    \\ (impl_tac THEN1 fs [domain_insert,SUBSET_DEF])
    \\ rw [] \\ fs [])
  \\ TRY
   (Cases_on `evaluate ([x1],env,s)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs [] \\ NO_TAC)
  \\ TRY
   (Cases_on `evaluate ([x1],env,s1)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs [] \\ NO_TAC)
  THEN1
   (Cases_on `evaluate ([x1],env,s1)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ every_case_tac \\ fs [] \\ rfs []
    \\ first_x_assum drule \\ fs []
    \\ imp_res_tac evaluate_code \\ fs [])
  THEN1
   (Cases_on `evaluate (xs,env,s)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ first_x_assum drule \\ fs []
    \\ imp_res_tac evaluate_code \\ fs [])
  THEN1
   (Cases_on `evaluate ([x1],env,s)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ rpt (IF_CASES_TAC \\ fs [])
    \\ first_x_assum drule \\ fs []
    \\ imp_res_tac evaluate_code \\ fs [])
  THEN1
   (Cases_on `evaluate ([x],env,s)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ Cases_on `evaluate (y::xs,env,r)` \\ fs []
    \\ first_x_assum drule \\ fs []
    \\ imp_res_tac evaluate_code \\ fs []
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []));

val code_rel_insert = Q.store_thm("code_rel_insert",
  `lookup n c = SOME (arity,e1) /\
    exp_rel (:'ffi) (insert n (arity,e2) c) e1 e2 ==>
    code_rel (:'ffi) c (insert n (arity,e2) c)`,
  fs [code_rel_def] \\ rw [lookup_insert] \\ rw [] \\ fs [] \\ rw []
  \\ TRY (drule evaluate_code_insert \\ fs [] \\ NO_TAC)
  \\ drule evaluate_code_insert \\ fs []
  \\ disch_then drule \\ fs [] \\ rw []
  \\ qpat_x_assum `exp_rel (:'ffi) _ e1 e2` (fn th => mp_tac th \\ assume_tac th)
  \\ simp_tac std_ss [exp_rel_def]
  \\ disch_then drule \\ fs []);

fun split_tac q = Cases_on q \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [];

val evaluate_inline = Q.store_thm("evaluate_inline",
  `!cs xs s env.
     subspt cs s.code /\
     FST (evaluate (xs,env,s)) <> Rerr(Rabort Rtype_error) ==>
     (evaluate (inline cs xs,env,s) = evaluate (xs,env,s))`,
  recInduct inline_ind \\ reverse (REPEAT STRIP_TAC)
  \\ POP_ASSUM MP_TAC \\ SIMP_TAC std_ss [Once inline_def,LET_DEF] \\ RES_TAC
  THEN1
   (Cases_on `dest` \\ fs [] THEN1
     (ONCE_REWRITE_TAC [evaluate_def] \\ ASM_SIMP_TAC std_ss [HD_inline]
      \\ Cases_on `evaluate (xs,env,s)` \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF])
    \\ Cases_on `lookup x cs` \\ fs [] THEN1
     (ONCE_REWRITE_TAC [evaluate_def] \\ ASM_SIMP_TAC std_ss [HD_inline]
      \\ Cases_on `evaluate (xs,env,s)` \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF])
    \\ rename1 `lookup x cs = SOME args`
    \\ PairCases_on `args` \\ fs []
    \\ ONCE_REWRITE_TAC [evaluate_def] \\ ASM_SIMP_TAC std_ss [HD_inline]
    \\ Cases_on `evaluate (xs,env,s)` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
    \\ IMP_RES_TAC evaluate_code
    \\ `lookup x s.code = SOME (args0,args1)` by fs [subspt_def,domain_lookup]
    \\ fs [find_code_def]
    \\ IMP_RES_TAC evaluate_IMP_LENGTH \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ SIMP_TAC std_ss [evaluate_mk_tick] \\ SRW_TAC [] [] \\ fs [ADD1]
    \\ MATCH_MP_TAC evaluate_expand_env \\ FULL_SIMP_TAC std_ss [])
  \\ ONCE_REWRITE_TAC [evaluate_def] \\ ASM_SIMP_TAC std_ss [HD_inline]
  \\ TRY (SRW_TAC [] [] \\ FIRST_X_ASSUM MATCH_MP_TAC
          \\ FULL_SIMP_TAC (srw_ss()) [dec_clock_def] \\ NO_TAC)
  \\ TRY (split_tac `evaluate (xs,env,s)`
     \\ IMP_RES_TAC evaluate_code \\ FULL_SIMP_TAC (srw_ss()) [] \\ NO_TAC)
  \\ TRY (split_tac `evaluate ([x1],env,s)` \\ SRW_TAC [] []
     \\ IMP_RES_TAC evaluate_code \\ FULL_SIMP_TAC (srw_ss()) []
     \\ Cases_on`e`>>fs[]>>NO_TAC)
  THEN1 (Cases_on `inline cs (y::xs)` THEN1
      (`LENGTH (inline cs (y::xs)) = 0` by METIS_TAC [LENGTH]
       \\ FULL_SIMP_TAC std_ss [LENGTH_inline,LENGTH] \\ `F` by DECIDE_TAC)
     \\ SIMP_TAC std_ss [Once evaluate_def,HD_inline]
     \\ POP_ASSUM (fn th => FULL_SIMP_TAC std_ss [GSYM th])
     \\ split_tac `evaluate ([x],env,s)` \\ split_tac `evaluate (y::xs,env,r)`
     \\ IMP_RES_TAC evaluate_code \\ FULL_SIMP_TAC (srw_ss()) []));

val exp_rel_inline = Q.store_thm("exp_rel_inline",
  `subspt cs c ==> exp_rel (:'ffi) c e (HD (inline cs [e]))`,
  fs [exp_rel_def] \\ rw []
  \\ qpat_x_assum `_ = (_,_)` (fn th => assume_tac th THEN
        once_rewrite_tac [GSYM th])
  \\ match_mp_tac evaluate_inline \\ fs []);

val code_rel_insert_inline = Q.store_thm("code_rel_insert_inline",
  `lookup n c = SOME (arity,e1) /\ subspt cs c /\ ~(n IN domain cs) ==>
    code_rel (:'ffi) c (insert n (arity,(HD (inline cs [e1]))) c)`,
  rw [] \\ match_mp_tac code_rel_insert \\ fs []
  \\ match_mp_tac exp_rel_inline
  \\ fs [subspt_def,domain_lookup,PULL_EXISTS,lookup_insert]
  \\ rw [] \\ res_tac \\ fs []);

val code_rel_insert_insert_inline = Q.store_thm("code_rel_insert_insert_inline",
  `subspt cs (insert n (arity,e1) c) /\ ~(n IN domain cs) ==>
    code_rel (:'ffi) (insert n (arity,e1) c)
                     (insert n (arity,(HD (inline cs [e1]))) c)`,
  `insert n (arity,HD (inline cs [e1])) c =
   insert n (arity,HD (inline cs [e1])) (insert n (arity,e1) c)` by fs [insert_shadow]
  \\ pop_assum (fn th => once_rewrite_tac [th]) \\ rw []
  \\ match_mp_tac code_rel_insert_inline \\ fs []);

val inline_all_acc = Q.store_thm("inline_all_acc",
  `!xs ys cs limit.
      inline_all limit cs xs ys = REVERSE ys ++ inline_all limit cs xs []`,
  Induct \\ fs [inline_all_def] \\ strip_tac \\ PairCases_on `h` \\ fs []
  \\ once_rewrite_tac [inline_all_def] \\ simp_tac std_ss [LET_THM]
  \\ rpt strip_tac \\ IF_CASES_TAC
  \\ qpat_x_assum `!x._` (fn th => once_rewrite_tac [th]) \\ fs []);

val fromAList_SWAP = Q.prove(
  `!xs x ys.
      ALL_DISTINCT (FST x::MAP FST xs) ==>
      fromAList (xs ++ x::ys) = fromAList (x::(xs ++ ys))`,
  Induct \\ fs [] \\ rw []
  \\ PairCases_on `h` \\ fs [fromAList_def]
  \\ PairCases_on `x` \\ fs [fromAList_def]
  \\ fs [spt_eq_thm,wf_insert,wf_fromAList]
  \\ rw [lookup_insert]);

val code_rel_rearrange_lemma = Q.store_thm("code_rel_rearrange_lemma",
  `ALL_DISTINCT (FST x::MAP FST xs) /\
    MAP FST zs = MAP FST xs /\
    code_rel (:'ffi) (fromAList (xs++x::ys)) (fromAList (zs++x::ys)) ==>
    code_rel (:'ffi) (fromAList (x::(xs++ys))) (fromAList (x::(zs++ys))) `,
  metis_tac [fromAList_SWAP,APPEND]);

val MAP_FST_inline_all = Q.store_thm("MAP_FST_inline_all",
  `!xs cs. MAP FST (inline_all limit cs xs []) = MAP FST xs`,
  Induct \\ fs [inline_all_def] \\ strip_tac
  \\ PairCases_on `h` \\ fs [inline_all_def] \\ rw []
  \\ once_rewrite_tac [inline_all_acc] \\ fs []);

val MEM_IMP_ALOOKUP_SOME = Q.store_thm("MEM_IMP_ALOOKUP_SOME",
  `!xs x y.
      ALL_DISTINCT (MAP FST xs) /\ MEM (x,y) xs ==>
      ALOOKUP xs x = SOME y`,
  Induct \\ fs [FORALL_PROD] \\ rw []
  \\ res_tac \\ fs [MEM_MAP,FORALL_PROD] \\ rfs []);

val code_rel_inline_all = Q.store_thm("code_rel_inline_all",
  `!xs ys cs.
      (!x y. lookup x cs = SOME y ==> MEM (x,y) ys /\ !y. ~MEM (x,y) xs) /\
      ALL_DISTINCT (MAP FST (ys ++ xs)) ==>
      code_rel (:'ffi)
        (fromAList (xs ++ ys))
        (fromAList (inline_all limit cs xs [] ++ ys))`,
  Induct \\ fs [inline_all_def,code_rel_refl]
  \\ strip_tac \\ PairCases_on `h` \\ fs []
  \\ reverse (rw [inline_all_def])
  \\ once_rewrite_tac [inline_all_acc] \\ fs []
  \\ qpat_abbrev_tac `zs = inline_all limit _ xs []`
  \\ match_mp_tac code_rel_trans
  \\ qexists_tac `fromAList ((h0,h1,HD (inline cs [h2]))::(xs ++ ys))`
  \\ rpt strip_tac
  \\ TRY
   (fs [fromAList_def]
    \\ match_mp_tac code_rel_insert_insert_inline
    \\ fs [domain_lookup,subspt_def,PULL_EXISTS,lookup_insert]
    \\ reverse (rpt strip_tac) THEN1 (res_tac \\ fs [])
    \\ IF_CASES_TAC \\ fs [] \\ rveq THEN1 (res_tac \\ fs [])
    \\ qexists_tac `v` \\ fs [] \\ res_tac
    \\ fs [lookup_fromAList]
    \\ match_mp_tac MEM_IMP_ALOOKUP_SOME \\ fs []
    \\ fs [ALL_DISTINCT_APPEND] \\ metis_tac [])
  \\ match_mp_tac code_rel_rearrange_lemma \\ fs []
  \\ unabbrev_all_tac \\ fs [MAP_FST_inline_all]
  \\ fs [ALL_DISTINCT_APPEND,ALL_DISTINCT]
  \\ first_x_assum match_mp_tac
  \\ fs [ALL_DISTINCT_APPEND,ALL_DISTINCT]
  \\ (reverse conj_tac THEN1 metis_tac [])
  THEN1 metis_tac []
  \\ fs [lookup_insert] \\ rw []
  \\ fs [MEM_MAP,FORALL_PROD,PULL_EXISTS]
  \\ Cases_on `y'` \\ fs [])
  |> Q.SPECL [`xs`,`[]`] |> SIMP_RULE std_ss [APPEND_NIL];

val code_rel_compile_prog = Q.store_thm("code_rel_compile_prog",
  `ALL_DISTINCT (MAP FST prog) ==>
    code_rel (:'ffi) (fromAList prog) (fromAList (compile_prog limit prog))`,
  fs [compile_prog_def] \\ rw [code_rel_refl]
  \\ match_mp_tac code_rel_inline_all \\ fs [lookup_def]);

val code_rel_IMP_semantics_EQ = Q.store_thm("code_rel_IMP_semantics_EQ",
  `!(ffi:'ffi ffi_state) c1 c2 start.
      code_rel (:'ffi) c1 c2 /\ semantics ffi c1 start <> Fail ==>
      semantics ffi c2 start = semantics ffi c1 start`,
  rewrite_tac [GSYM AND_IMP_INTRO]
  \\ ntac 5 strip_tac \\ simp[bvlSemTheory.semantics_def]
  \\ IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  `∀k. evaluate ([Call 0 (SOME start) []],[],initial_state ffi c2 k) =
    let (r,s) = bvlSem$evaluate ([Call 0 (SOME start) []],
         [],initial_state ffi c1 k) in
      (r, s with code := c2)` by
   (fs [evaluate_def,find_code_def]
    \\ Cases_on `lookup start c1` \\ fs []
    \\ PairCases_on `x` \\ fs []
    \\ IF_CASES_TAC \\ fs [] \\ rveq
    \\ strip_tac \\ fs [code_rel_def]
    \\ first_x_assum drule \\ strip_tac \\ fs [LENGTH_NIL]
    \\ IF_CASES_TAC \\ fs []
    \\ qpat_x_assum `!x. _ <> _` (qspec_then `k` mp_tac) \\ fs [] \\ rw []
    \\ Cases_on `evaluate ([x1],[],dec_clock 1 (initial_state ffi c1 k))`
    \\ fs [] \\ first_x_assum drule
    \\ disch_then (qspec_then `dec_clock 1 (initial_state ffi c1 k)` mp_tac)
    \\ `dec_clock 1 (initial_state ffi c1 k) with code := c1 =
        dec_clock 1 (initial_state ffi c1 k) /\
        dec_clock 1 (initial_state ffi c1 k) with code := c2 =
        dec_clock 1 (initial_state ffi c2 k)` by
          fs [dec_clock_def,initial_state_def]
    \\ fs [] \\ disch_then (qspec_then `r` mp_tac)
    \\ impl_tac THEN1
     (imp_res_tac evaluate_code
      \\ fs [dec_clock_def,initial_state_def,bvlSemTheory.state_component_equality])
    \\ fs [])
  \\ simp []
  \\ qpat_x_assum `code_rel (:'ffi) _ _` kall_tac
  \\ DEEP_INTRO_TAC some_intro >> simp[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  full_simp_tac(srw_ss())[UNCURRY,LET_THM] >>
  reverse conj_tac >- (
    simp_tac(srw_ss()++QUANT_INST_ss[pair_default_qp])[] ) >>
  gen_tac >> strip_tac >> var_eq_tac >>
  asm_simp_tac(srw_ss()++QUANT_INST_ss[pair_default_qp])[] >>
  reverse conj_tac >- METIS_TAC[] >>
  gen_tac >> strip_tac >>
  strip_tac >> full_simp_tac(srw_ss())[] >>
  qpat_abbrev_tac`abb2 = bvlSem$evaluate _` >>
  qpat_abbrev_tac`abb1 = bvlSem$evaluate _` >>
  qmatch_assum_abbrev_tac`Abbrev(abb2 = evaluate (e1,v1,s1))` >>
  qmatch_assum_abbrev_tac`Abbrev(abb1 = evaluate (e1,v1,s2))` >>
  map_every qunabbrev_tac[`abb1`,`abb2`] >>
  qmatch_assum_rename_tac`Abbrev(s1 = _ _ _ k1)` >>
  qmatch_assum_rename_tac`Abbrev(s2 = _ _ _ k2)` >>
  (fn g => subterm(fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >> full_simp_tac(srw_ss())[] >>
  (fn g => subterm(fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >> full_simp_tac(srw_ss())[] >>
  Q.ISPECL_THEN[`e1`,`v1`,`s1`]mp_tac bvlPropsTheory.evaluate_add_to_clock_io_events_mono >>
  disch_then(qspec_then`k2`mp_tac) >>
  Q.ISPECL_THEN[`e1`,`v1`,`s2`]mp_tac bvlPropsTheory.evaluate_add_to_clock_io_events_mono >>
  disch_then(qspec_then`k1`mp_tac) >>
  simp[bvlPropsTheory.inc_clock_def,Abbr`s1`,Abbr`s2`] >>
  ntac 2 strip_tac >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac bvlPropsTheory.evaluate_add_clock >>
  rpt(first_x_assum (fn th => mp_tac th >> impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[]))) >>
  simp[bvlPropsTheory.inc_clock_def] >>
  TRY (
    disch_then(qspec_then`k1`strip_assume_tac) >>
    disch_then(qspec_then`k2`strip_assume_tac) >>
    fsrw_tac[ARITH_ss][bvlSemTheory.state_component_equality] ) >>
  TRY (
    qexists_tac`k1` >>
    spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[] >> NO_TAC) >>
  TRY (
    qexists_tac`k2` >>
    spose_not_then strip_assume_tac >> fsrw_tac[ARITH_ss][] >>
    rev_full_simp_tac(srw_ss())[] >> NO_TAC) >>
  srw_tac[][] >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]);

val compile_prog_semantics = save_thm("compile_prog_semantics",
  MATCH_MP (code_rel_IMP_semantics_EQ |> REWRITE_RULE [GSYM AND_IMP_INTRO])
   (code_rel_compile_prog |> UNDISCH) |> SPEC_ALL
  |> DISCH_ALL |> REWRITE_RULE [AND_IMP_INTRO]);

val MAP_FST_compile_prog = Q.store_thm("MAP_FST_compile_prog",
  `MAP FST (bvl_inline$compile_prog limit prog) = MAP FST prog`,
  fs [bvl_inlineTheory.compile_prog_def] \\ rw [MAP_FST_inline_all]);

val _ = export_theory();
