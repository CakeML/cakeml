open HolKernel bossLib boolLib boolSimps lcsymtacs listTheory pairTheory rich_listTheory pred_setTheory arithmeticTheory finite_mapTheory relationTheory sortingTheory stringTheory sptreeTheory alistTheory
open miscLib miscTheory bigStepTheory astTheory semanticPrimitivesTheory evalPropsTheory bigClockTheory replTheory printTheory terminationTheory
open bytecodeTheory bytecodeExtraTheory bytecodeEvalTheory bytecodeClockTheory bytecodeLabelsTheory bytecodeTerminationTheory
open modLangTheory conLangTheory decLangTheory exhLangTheory modLangProofTheory conLangProofTheory decLangProofTheory exhLangProofTheory patLangProofTheory pat_to_closTheory clos_numberTheory clos_annotateTheory clos_to_bvlTheory bvlBytecodeTheory bvlTheory printingTheory compilerTerminationTheory
open newcompilerTheory
open free_varsTheory

val _ = new_theory"compilerProof"

(* misc (TODO: move?) *)

val GENLIST_eq_nil = store_thm("GENLIST_eq_nil",
  ``(GENLIST x y = []) <=> (y = 0)``,
  SRW_TAC[][EQ_IMP_THM] THEN
  Cases_on`y` THEN FULL_SIMP_TAC(srw_ss())[GENLIST])

val global_env_inv_inclusion = store_thm("global_env_inv_inclusion",
  ``∀genv mods tops menv s env.
     global_env_inv genv mods tops menv s env ⇒
     set (MAP FST env) DIFF s ⊆ FDOM tops ∧
     set (MAP FST menv) ⊆ FDOM mods``,
  rw[Once v_to_i1_cases,SUBSET_DEF] >>
  TRY (
    (alistTheory.ALOOKUP_NONE
     |> SPEC_ALL |> EQ_IMP_RULE |> fst
     |> CONTRAPOS
     |> SIMP_RULE std_ss []
     |> imp_res_tac) >>
    fs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS] >>
    res_tac >> fs[FLOOKUP_DEF] >> NO_TAC) >>
  last_x_assum mp_tac >>
  simp[Once v_to_i1_cases] >> strip_tac >>
  (alistTheory.ALOOKUP_NONE
   |> SPEC_ALL |> EQ_IMP_RULE |> fst
   |> CONTRAPOS
   |> SIMP_RULE std_ss []
   |> imp_res_tac) >>
  fs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS] >>
  res_tac >> fs[FLOOKUP_DEF] >> NO_TAC)

val to_i1_invariant_change_clock = store_thm("to_i1_invariant_change_clock",
  ``to_i1_invariant genv mods tops menv env s s_i1 mod_names ∧
    SND s' = SND s ∧ SND s_i1' = SND s_i1 ∧ FST s' = FST s_i1'
    ⇒
    to_i1_invariant genv mods tops menv env s' s_i1' mod_names``,
  simp[to_i1_invariant_def] >>
  rw[Once s_to_i1_cases] >>
  rw[Once s_to_i1_cases] >>
  metis_tac[pair_CASES,PAIR_EQ,SND,FST])

val to_i2_invariant_change_clock = store_thm("to_i2_invariant_change_clock",
  ``to_i2_invariant mods tids envC exh tagenv_st gtagenv s s_i2 genv genv_i2 ∧
    SND s' = SND s ∧ SND s_i2' = SND s_i2 ∧ FST s' = FST s_i2'
    ⇒
    to_i2_invariant mods tids envC exh tagenv_st gtagenv s' s_i2' genv genv_i2``,
  simp[to_i2_invariant_def] >>
  rw[Once s_to_i2_cases] >>
  rw[Once s_to_i2_cases] >>
  metis_tac[pair_CASES,PAIR_EQ,SND,FST])

val to_i1_invariant_change_store = store_thm("to_i1_invariant_change_store",
  ``to_i1_invariant genv mods tops menv env s s_i1 mod_names ∧
    s_to_i1 genv s' s_i1'
    ⇒
    to_i1_invariant genv mods tops menv env s' s_i1' mod_names``,
  simp[to_i1_invariant_def])

val to_i2_invariant_change_store = store_thm("to_i2_invariant_change_store",
  ``to_i2_invariant mods tids envC exh tagenv_st gtagenv s s_i2 genv genv_i2 ∧
    s_to_i2 gtagenv s' s_i2'
    ⇒
    to_i2_invariant mods tids envC exh tagenv_st gtagenv s' s_i2' genv genv_i2``,
  simp[to_i2_invariant_def] >> metis_tac[])

val evaluate_prompt_i1_success_globals = store_thm("evaluate_prompt_i1_success_globals",
  ``∀ck genv cenv s prompt_i1 s' cenv' new_genv.
    evaluate_prompt_i1 ck genv cenv s prompt_i1 (s',cenv',new_genv,NONE) ⇒
    EVERY IS_SOME new_genv``,
  rw[evaluate_prompt_i1_cases] >> rw[EVERY_MAP])

val csg_to_pat_MAP = store_thm("csg_to_pat_MAP",
  ``csg_to_pat = map_count_store_genv v_to_pat``,
  simp[FUN_EQ_THM,FORALL_PROD,csg_to_pat_def,map_count_store_genv_def] >>
  simp[MAP_EQ_f] >> gen_tac >> Cases >> simp[])

val val_rel_add_code = store_thm("val_rel_add_code",
  ``∀x y. val_rel f r c x y ⇒ val_rel f r (union c new) x y``,
  ho_match_mp_tac val_rel_ind >>
  srw_tac[ETA_ss][val_rel_SIMP] >- (
    simp[val_rel_cases] )
  >- (
    simp[val_rel_cases] )
  >- (
    first_assum(match_exists_tac o concl) >>
    fs[code_installed_def] >>
    simp[lookup_union] >>
    fs[EVERY_MEM,UNCURRY] )
  >- (
    disj1_tac >>
    first_assum(match_exists_tac o concl) >>
    fs[code_installed_def] >>
    simp[lookup_union] >>
    fs[EVERY_MEM,UNCURRY] )
  >- (
    disj2_tac >>
    qexists_tac`exps_ps` >> simp[] >>
    qexists_tac`r'`>>fs[] >>
    fs[closure_code_installed_def] >>
    simp[lookup_union] >>
    fs[EVERY_MEM,UNCURRY,code_installed_def,lookup_union] >>
    rw[] >> res_tac >>
    first_assum(match_exists_tac o concl) >>
    simp[]))

val state_rel_add_code = store_thm("state_rel_add_code",
  ``state_rel f s t ⇒ state_rel f s (t with code := union t.code new)``,
  simp[clos_to_bvlTheory.state_rel_def,LIST_REL_EL_EQN] >> rw[] >- (
    last_x_assum(qspec_then`n`mp_tac) >> simp[] >>
    simp[opt_val_rel_elim] >>
    simp[optionTheory.OPTREL_def] >>
    strip_tac >> simp[val_rel_add_code] )
  >- (
    res_tac >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    fs[ref_rel_cases,LIST_REL_EL_EQN,val_rel_add_code] )
  >- (
    fs[lookup_union,code_installed_def,EVERY_MEM,FORALL_PROD] >>
    res_tac >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    rw[] >> res_tac >> fs[] ))

val Clt = prove(
  ``combin$C prim_rec$< = $>``,
  simp[FUN_EQ_THM])

val code_locs_FLAT_MAP = store_thm("code_locs_FLAT_MAP",
  ``∀ls. code_locs ls = FLAT (MAP (λx. code_locs [x]) ls)``,
  Induct >> simp[code_locs_def] >>
  simp[Once code_locs_cons])

val code_locs_FLAT_MAP2 = store_thm("code_locs_FLAT_MAP2",
  ``∀ls. clos_number$code_locs ls = FLAT (MAP (λx. code_locs [x]) ls)``,
  Induct >> simp[clos_numberTheory.code_locs_def] >>
  simp[Once clos_numberTheory.code_locs_cons])

val good_code_env_union = store_thm("good_code_env_union",
  ``good_code_env locs1 il c1 code ∧
    good_code_env locs2 il c2 (code ++ more) ∧
    DISJOINT (domain locs1) (domain locs2) ∧
    DISJOINT (domain locs1) { l | ∃ptr arity exp. MEM l (code_locs [exp]) ∧ lookup ptr c2 = SOME (arity,exp) } ∧
    DISJOINT (domain locs2) { l | ∃ptr arity exp. MEM l (code_locs [exp]) ∧ lookup ptr c1 = SOME (arity,exp) }
  ⇒
    good_code_env (union locs1 locs2) il (union c1 c2) (code ++ more)``,
  simp[good_code_env_def,lookup_union] >> strip_tac >> rpt gen_tac >>
  BasicProvers.CASE_TAC >> rw[] >>
  first_x_assum(fn th => first_assum (strip_assume_tac o MATCH_MP th)) >>
  map_every qexists_tac[`cs`,`l0`,`cc`] >> simp[] >>
  TRY (
    reverse BasicProvers.CASE_TAC >- (
      PROVE_TAC[domain_lookup,IN_DISJOINT] )) >>
  first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM) >>
  AP_TERM_TAC >>
  match_mp_tac bvl_bc_code_locs >>
  simp[EVERY_MEM,lookup_union] >> rw[] >>
  BasicProvers.CASE_TAC >>
  fs[IN_DISJOINT,Once code_locs_FLAT_MAP,MEM_FLAT,MEM_MAP,EXISTS_PROD,MEM_toList] >>
  metis_tac[domain_lookup,optionTheory.option_CASES,PAIR])

val bvl_to_bc_value_union = store_thm("bvl_to_bc_value_union",
  ``∀f v f2. closed_locs f v ⇒
    (bvl_to_bc_value (union f f2) v = bvl_to_bc_value f v)``,
  ho_match_mp_tac closed_locs_ind >>
  simp[bvl_to_bc_value_def,tlookup_def,lookup_union,MAP_EQ_f,EVERY_MEM] >>
  rw[] >> BasicProvers.EVERY_CASE_TAC >> fs[] >>
  fs[domain_lookup])

val s_to_Cs_unpair = save_thm("s_to_Cs_unpair",
  REWRITE_CONV[s_to_Cs_def] ``s_to_Cs ((FST(FST csg),SND(FST csg)),SND csg)``
  |> SIMP_RULE std_ss [])

val closed_locs_union = store_thm("closed_locs_union",
  ``∀f v. closed_locs f v ⇒ closed_locs (union f g) v``,
  ho_match_mp_tac closed_locs_ind >>
  rw[domain_union] >> fs[EVERY_MEM])

val bc_fetch_with_output = store_thm("bc_fetch_with_output",
  ``bc_fetch (s with output := x) = bc_fetch s``,
  rw[bc_fetch_def])

val bc_find_loc_with_output = store_thm("bc_find_loc_with_output",
  ``bc_find_loc (s with output := x) = bc_find_loc s``,
  simp[FUN_EQ_THM] >> Cases >> rw[bc_find_loc_def])

val bc_next_prepend_output = store_thm("bc_next_prepend_output",
  ``∀x y. bc_next x y ⇒ bc_next (x with output := ls++x.output) (y with output := ls++y.output)``,
  ho_match_mp_tac bc_next_ind >>
  rw[bc_eval1_thm] >>
  simp[bc_eval1_def,bc_fetch_with_output,bump_pc_def,bc_fetch_with_stack,bc_find_loc_with_output] >>
  rw[bc_state_component_equality,IMPLODE_EXPLODE_I,wordsTheory.w2n_lt,REPLICATE_GENLIST] >>
  fs[bc_eval_stack_thm] >>
  TRY (
    simp[EL_REVERSE,EL_APPEND1,EL_APPEND2,PRE_SUB1,bc_state_component_equality,TAKE_APPEND1,TAKE_REVERSE,LASTN_APPEND1,LASTN] >>
    simp[combinTheory.K_DEF] >> NO_TAC) >>
  TRY (
    BasicProvers.CASE_TAC >>
    simp[bc_state_component_equality] >>
    NO_TAC))

val RTC_bc_next_prepend_output = store_thm("RTC_bc_next_prepend_output",
  ``∀ls x y. RTC bc_next x y ⇒ RTC bc_next (x with output := ls++x.output) (y with output := ls++y.output)``,
  rw[] >> (
     RTC_lifts_monotonicities
  |> Q.GEN`R` |> Q.ISPEC `bc_next`
  |> Q.GEN`f` |> Q.ISPEC `λs:bc_state. s with output := ls ++ s.output`
  |> strip_assume_tac) >> fs[] >> pop_assum (match_mp_tac o MP_CANON) >>
  rw[bc_next_prepend_output])

(* env_rs *)

val state_rel_def = Define`
  state_rel f s1 s2 ⇔
    (IS_SOME s2.clock ⇒ s2.clock = SOME s1.clock) ∧
    s2.globals = MAP (OPTION_MAP (bvl_to_bc_value f)) s1.globals ∧
    s2.refs = refv_map (bvl_to_bc_value f) o_f s1.refs ∧
    EVERY (OPTION_EVERY (closed_locs f)) s1.globals ∧
    FEVERY (refv_every (closed_locs f) o SND) s1.refs ∧
    good_code_env f s2.inst_length s1.code s2.code ∧
    s2.stack = [] ∧
    (* s2.output = s1.output ∧ *)
    domain f = domain s1.code`

val env_rs_def = Define`
  env_rs ((envM,envC,envE):all_env) (((cnt,s),tids,mods)) (genv,gtagenv)
    (rs:compiler_state) (bs:bc_state)
  ⇔
    good_labels rs.rnext_label bs.code ∧
    rs.next_global = LENGTH genv ∧
    rs.next_addr = next_addr bs.inst_length bs.code ∧
    bs.inst_length = real_inst_length ∧
    ∃s1 s2 genv2 s3 sp s4 s5 s6 f1 locs.
      to_i1_invariant
        genv (FST rs.globals_env) (SND rs.globals_env)
        envM envE (cnt,s) (cnt,s1) mods ∧
      to_i2_invariant
        mods tids envC rs.exh rs.contags_env gtagenv
        (cnt,s1) (cnt,s2) genv genv2 ∧
      csg_rel (v_to_exh rs.exh) ((cnt,s2),genv2) s3 ∧
      csg_rel v_pat (csg_to_pat s3) sp ∧
      clos_number$state_rel (s_to_Cs sp) s4 ∧
      clos_annotate$state_rel s4 s5 ∧
      state_rel f1 s5 s6 ∧
      (∀k. k ∈ domain s6.code ⇒ k < rs.next_loc) ∧
      (∀ptr arity exp. lookup ptr s6.code = SOME (arity,exp) ⇒ EVERY ($> rs.next_loc) (code_locs [exp])) ∧
      state_rel locs s6 bs`

val env_rs_change_clock = store_thm("env_rs_change_clock",
   ``∀env stm grd rs bs stm' ck bs' new_clock.
     env_rs env stm grd rs bs ∧ stm' = ((ck,SND(FST stm)),SND stm) ∧
     (bs' = bs with clock := new_clock) ∧
     (new_clock = NONE ∨ new_clock = SOME ck)
     ⇒
     env_rs env stm' grd rs bs'``,
  qx_gen_tac`p` >> PairCases_on`p` >>
  qx_gen_tac`q` >> PairCases_on`q` >>
  qx_gen_tac`r` >> PairCases_on`r` >>
  simp[env_rs_def] >>
  rpt gen_tac >>
  Q.PAT_ABBREV_TAC`d = (a ∨ b)` >>
  strip_tac >>
  map_every qexists_tac[`s1`] >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    metis_tac[to_i1_invariant_change_clock,FST,SND] ) >>
  map_every qexists_tac[`s2`,`genv2`] >>
  conj_tac >- (
    metis_tac[to_i2_invariant_change_clock,FST,SND] ) >>
  simp[PULL_EXISTS] >>
  PairCases_on`s3` >>
  qexists_tac`((ck,s31),s32)` >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- fs[csg_rel_def] >>
  qexists_tac`((ck,SND(FST sp)),SND sp)` >>
  conj_tac >- fs[csg_rel_unpair,csg_to_pat_MAP,map_count_store_genv_def] >>
  qexists_tac`s4 with clock := ck` >>
  conj_tac >- (
    fs[csg_to_pat_MAP,s_to_Cs_unpair,clos_numberTheory.state_rel_def] ) >>
  qexists_tac`s5 with clock := ck` >>
  conj_tac >- (
    fs[clos_annotateTheory.state_rel_def] ) >>
  map_every qexists_tac [`s6 with clock := ck`,`f1`] >>
  conj_tac >- (
    fs[clos_to_bvlTheory.state_rel_def] ) >>
  simp[] >>
  fs[state_rel_def] >>
  Cases_on`new_clock`>>fs[] >>
  metis_tac[])

val env_rs_with_bs_irr = store_thm("env_rs_with_bs_irr",
  ``∀env cs grd rs bs bs'.
    env_rs env cs grd rs bs
    ∧ bs'.globals = bs.globals
    ∧ bs'.stack = bs.stack
    ∧ bs'.refs = bs.refs
    ∧ bs'.clock = bs.clock
    ∧ bs'.code = bs.code
    ∧ bs'.inst_length = bs.inst_length
    ∧ bs'.output = bs.output
    ⇒
    env_rs env cs grd rs bs'``,
  simp[FORALL_PROD] >> rw[env_rs_def] >>
  rpt(CHANGED_TAC(first_assum(match_exists_tac o concl) >> simp[])) >>
  fs[state_rel_def] >> metis_tac[])

val good_code_env_append_code = store_thm("good_code_env_append_code",
  ``∀f il cmap ls c.
      good_code_env f il cmap ls ⇒
      good_code_env f il cmap (ls ++ c)``,
  rw[good_code_env_def] >> res_tac >> rw[] >>
  first_assum(match_exists_tac o concl) >> rw[] >>
  first_assum(match_exists_tac o concl) >> rw[])

val env_rs_append_code = store_thm("env_rs_append_code",
  ``∀env cs grd rs bs bs' rs' c nl.
    env_rs env cs grd rs bs ∧
    bs' = bs with code := bs.code ++ c ∧
    rs' = rs with <| rnext_label := nl; next_addr := rs.next_addr + next_addr bs.inst_length c |> ∧
    good_labels nl bs'.code
    ⇒
    env_rs env cs grd rs' bs'``,
  simp[FORALL_PROD] >>
  simp[env_rs_def,next_addr_append] >>
  rpt gen_tac >> strip_tac  >>
  rpt(CHANGED_TAC(first_assum(match_exists_tac o concl) >> simp[])) >>
  fs[state_rel_def] >>
  qexists_tac`locs` >> simp[] >>
  metis_tac[good_code_env_append_code])

(* compile_top *)

(*
val compile_top_labels = store_thm("compile_top_labels",
  ``∀types rs top.
      (FST(SND(compile_top types rs top))).rnext_label = (FST(compile_top types rs top)).rnext_label ∧
      between_labels (SND(SND(compile_top types rs top))) rs.rnext_label (FST(compile_top types rs top)).rnext_label ∧
      code_labels_ok (SND(SND(compile_top types rs top)))``,
   rpt gen_tac >> conj_tac >- ( simp[compile_top_def,UNCURRY] ) >>
   rw[compile_top_def] >>
   unabbrev_all_tac >> fs[] >>
   ntac 6 (rw[] >> fs[]) >>

   simp[compile_top_def,UNCURRY]
   rw[compile_top_def] >> rw[] >- (
     unabbrev_all_tac >> rw[] >>
     compile_print_top_thm
     rw[Abbr`cs`,Abbr`cs'`]
   simp[compile_top_def,UNCURRY,pair_CASE_def] >>
   rpt gen_tac >> strip_tac >>
   specl_args_of_then``compile_Cexp``compile_Cexp_thm mp_tac >>
   discharge_hyps >- (
     simp[] >>
     qmatch_abbrev_tac`x = []` >>
     qsuff_tac`set x ⊆ {}` >- rw[] >>
     qunabbrev_tac`x` >>
     specl_args_of_then``exp_to_pat``(CONJUNCT1 free_vars_pat_exp_to_pat)mp_tac >>
     match_mp_tac(METIS_PROVE[]``(p ∧ (p ∧ q ⇒ r)) ⇒ ((p ⇒ q) ⇒ r)``) >>
     conj_tac >- (
       simp[] >>
       Q.PAT_ABBREV_TAC`p = prompt_to_i3 X Y Z A` >>
       PairCases_on`p` >> fs[markerTheory.Abbrev_def] >>
       pop_assum(ASSUME_TAC o SYM) >>
       imp_res_tac free_vars_i2_prompt_to_i3 >> simp[] >>
       Q.PAT_ABBREV_TAC`p = prompt_to_i2 X A` >>
       PairCases_on`p` >> fs[markerTheory.Abbrev_def] >>
       pop_assum(ASSUME_TAC o SYM) >>
       imp_res_tac free_vars_prompt_to_i2 >> simp[] >>
       Q.PAT_ABBREV_TAC`p = top_to_i1 A B C D` >>
       PairCases_on`p` >> fs[markerTheory.Abbrev_def] >>
       pop_assum(ASSUME_TAC o SYM) >>
       imp_res_tac FV_top_to_i1 >>
       simp[Once EXTENSION] >> fs[SUBSET_DEF] >>
       Cases_on`rs.globals_env`>> fs[global_dom_def] >>
       rw[] >> CCONTR_TAC >> fs[] >> res_tac >> fs[] ) >>
     strip_tac >> rfs[] ) >>
   Q.PAT_ABBREV_TAC`Cexp = exp_to_Cexp Z` >>
   simp[] >> strip_tac >>
   specl_args_of_then``compile_print_top``compile_print_top_thm mp_tac >>
   simp[] >> strip_tac >>
   simp[] >>
   pop_assum kall_tac >>
   conj_tac >- (
     rpt(rator_x_assum`between_labels`mp_tac) >>
     rpt(rator_x_assum`code_labels_ok`mp_tac) >>
     rpt (pop_assum kall_tac) >>
     simp[between_labels_def,FILTER_APPEND,FILTER_REVERSE,ALL_DISTINCT_APPEND,ALL_DISTINCT_REVERSE,MAP_REVERSE,EVERY_REVERSE] >>
     simp[EVERY_MAP,EVERY_FILTER,is_Label_rwt,PULL_EXISTS] >>
     simp[EVERY_MEM,MEM_FILTER,is_Label_rwt,PULL_EXISTS] >>
     rw[] >> res_tac >> fsrw_tac[ARITH_ss][between_def] >>
     spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
   REWRITE_TAC[GSYM APPEND_ASSOC] >>
   match_mp_tac code_labels_ok_append >>
   simp[code_labels_ok_REVERSE] >>
   REWRITE_TAC[GSYM REVERSE_APPEND] >>
   simp[code_labels_ok_REVERSE] >>
   fs[local_labels_def,code_labels_ok_def,uses_label_thm,EXISTS_MEM,MEM_FILTER,PULL_EXISTS] >>
   metis_tac[])
*)

val tac1 =
  PairCases_on`csgh` >> fs[csg_rel_def,store_to_exh_csg_rel] >>
  conj_tac >>
  match_mp_tac (MP_CANON (GEN_ALL EVERY2_mono)) >>
  HINT_EXISTS_TAC >>
  simp[sv_to_exh_sv_rel] >>
  metis_tac[optionTheory.OPTREL_MONO,v_to_exh_extend_disjoint,FUNION_COMM,sv_rel_mono,DISJOINT_SYM]

val tac2 =
  simp[Abbr`xs`] >>
  simp[contains_Call_cAnnotate,contains_App_SOME_cAnnotate,contains_Op_Label_cAnnotate] >>
  imp_res_tac contains_Call_renumber_code_locs >>
  imp_res_tac contains_App_SOME_renumber_code_locs >>
  imp_res_tac contains_Op_Label_renumber_code_locs >>
  fs[pComp_contains_Call,pComp_contains_App_SOME,pComp_contains_Op_Label]

val tac3 =
  simp[env_rel_def,code_installed_def,state_rel_add_code] >>
  simp[Abbr`new_code`,lookup_union] >>
  simp[lookup_fromAList,ALOOKUP_MAP] >>
  simp[EVERY_MEM,FORALL_PROD] >>
  qx_genl_tac[`k`,`z`] >> rw[] >>
  `ALOOKUP aux k = SOME z` by
    metis_tac[ALOOKUP_ALL_DISTINCT_MEM,ALL_DISTINCT_REVERSE] >>
  simp[] >> BasicProvers.CASE_TAC >>
  `rs.next_loc ≤ k` by (
    fs[EVERY_MEM] >>
    first_x_assum match_mp_tac >>
    metis_tac[MEM_REVERSE,MEM_MAP,FST] ) >>
  `k ∈ domain s6.code` by metis_tac[domain_lookup] >>
  res_tac >> `F` suffices_by rw[] >> DECIDE_TAC

val tac4 =
  simp[EVERY_MEM,lookup_union] >> rw[] >>
  BasicProvers.CASE_TAC >>
  qmatch_assum_rename_tac`MEM loc (code_locs e2)` >>
  qmatch_assum_rename_tac`renumber_code_locs nl _ = (l,e1)` >>
  `MEM loc (code_locs [e1])` suffices_by (
    fs[EVERY_MEM] >> rw[] >> res_tac >>
    `loc ∈ domain s6.code` suffices_by (
      strip_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
    fs[state_rel_def] >>
    metis_tac[domain_lookup] ) >>
  ONCE_REWRITE_TAC[GSYM (Q.SPEC`0`cAnnotate_code_locs)] >>
  match_mp_tac(MP_CANON(code_locs_cComp |> SIMP_RULE std_ss [SUBSET_DEF])) >>
  qexists_tac`[]`>>simp[]

val tac5 =
  TRY(first_x_assum(qspec_then`bs`kall_tac)) >>
  simp[REVERSE_APPEND,Abbr`na`] >>
  ntac 2 (match_mp_tac good_code_env_append_code) >>
  match_mp_tac good_code_env_union >>
  conj_tac >- ( rfs[state_rel_def] ) >>
  conj_tac >- (
    match_mp_tac(GEN_ALL(MP_CANON(MATCH_MP bvl_bc_table_good real_inst_length_ok))) >>
    qexists_tac`rs.rnext_label` >> simp[] >>
    fs[good_labels_def,EVERY_MAP,combinTheory.o_DEF] ) >>
  simp[] >>
  fs[state_rel_def] >>
  simp[IN_DISJOINT] >>
  rw[] >> spose_not_then strip_assume_tac >- (
    `x < rs.next_loc` by PROVE_TAC[] >>
    fs[code_locs_def,Abbr`new_code`,lookup_fromAList,ALOOKUP_MAP] >>
    imp_res_tac ALOOKUP_MEM >>
    `MEM x (FLAT (MAP (λx. code_locs [x]) (MAP SND aux)))` by (
      simp[MEM_FLAT,MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
      PROVE_TAC[] ) >>
    fs[GSYM code_locs_FLAT_MAP,SUBSET_DEF,EVERY_MEM] >>
    `rs.next_loc ≤ x` by PROVE_TAC[] >>
    fsrw_tac[ARITH_ss][] ) >>
  fs[EVERY_MEM] >>
  `rs.next_loc > x` by PROVE_TAC[] >>
  `rs.next_loc ≤ x` by PROVE_TAC[] >>
  fsrw_tac[ARITH_ss][]

val tac6 =
  TRY(first_x_assum(qspec_then`bs`kall_tac)) >>
  fs[state_rel_def] >>
  ONCE_REWRITE_TAC[CONJ_ASSOC] >>
  conj_tac >- (
    fs[good_labels_def] >>
    simp[FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,EVERY_REVERSE] >>
    fs[EVERY_MEM,between_def,MEM_FILTER,PULL_EXISTS,is_Label_rwt] >>
    rw[] >> res_tac >> fsrw_tac[ARITH_ss][] >>
    spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][]) >>
  conj_tac >- (
    simp[MAP_EQ_f] >>
    Cases >> simp[] >> strip_tac >>
    match_mp_tac EQ_SYM >>
    match_mp_tac bvl_to_bc_value_union >>
    fs[EVERY_MEM] >> res_tac >> fs[] ) >>
  simp[fmap_eq_flookup,FLOOKUP_o_f] >>
  gen_tac >> BasicProvers.CASE_TAC >>
  Cases_on`x`>>simp[MAP_EQ_f] >> rw[] >>
  match_mp_tac EQ_SYM >>
  match_mp_tac bvl_to_bc_value_union >>
  imp_res_tac FEVERY_FLOOKUP >> fs[EVERY_MEM]

val tac7 =
  qpat_assum`bs2 = X`(fn th => assume_tac(EQ_MP (SYM(ISPEC(concl th)markerTheory.Abbrev_def)) th)) >> fs[] >>
  rator_x_assum`v_to_exh`mp_tac >>
  simp[Once v_to_exh_cases,vs_to_exh_MAP] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  ntac 2 (rator_x_assum`v_pat`mp_tac) >>
  simp[Once v_pat_cases] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  simp[Once v_pat_cases] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  rator_x_assum`clos_number$val_rel`mp_tac >>
  simp[Once clos_numberTheory.val_rel_cases] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  rator_x_assum`clos_annotate$val_rel`mp_tac >>
  simp[Once clos_annotateTheory.val_rel_cases] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  rator_x_assum`clos_to_bvl$val_rel`mp_tac >>
  simp[Once clos_to_bvlTheory.val_rel_cases] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC

val tac8 =
  fs[good_labels_def,between_labels_def,FILTER_APPEND,ALL_DISTINCT_APPEND
    ,MEM_FILTER,is_Label_rwt,PULL_EXISTS,EVERY_FILTER,EVERY_MEM,PULL_FORALL
    ,MEM_MAP,between_def,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
  rw[] >> res_tac >> fsrw_tac[ARITH_ss][] >>
  spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][]

val tac9 =
  simp[print_result_def,Abbr`bs2`,Abbr`bs2'`] >>
  `t6.output = ""` by (
    fs[clos_to_bvlTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_numberTheory.state_rel_def,s_to_Cs_unpair] ) >>
  simp[] >>
  qmatch_abbrev_tac`THE(bv_to_string bv) = print_v a` >>
  `THE (bv_to_string bv) = print_bv (Infer_Tuvar 0) bv` by (
    simp[print_bv_def] ) >>
  pop_assum SUBST1_TAC >>
  qunabbrev_tac`bv` >>
  match_mp_tac (MP_CANON print_bv_print_v) >> simp[] >>
  fs[result_to_i1_cases,result_to_i2_cases] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  rpt BasicProvers.VAR_EQ_TAC >> fs[] >> BasicProvers.VAR_EQ_TAC >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  imp_res_tac v_pat_trans >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  first_assum(match_exists_tac o concl) >> simp[]

val tac10 =
  rpt (rator_x_assum`good_labels`mp_tac) >> simp[Abbr`bs2`,Abbr`bs2'`] >>
  rpt (rator_x_assum`between_labels`mp_tac) >>
  rpt (BasicProvers.VAR_EQ_TAC) >>
  rpt (pop_assum kall_tac) >>
  simp[good_labels_def,FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,PULL_EXISTS
      ,EVERY_FILTER,between_labels_def,EVERY_MAP,EVERY_MEM,between_def,PULL_FORALL] >>
  rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][]

val tac11 =
  conj_tac >- (
    rpt(BasicProvers.VAR_EQ_TAC) >> simp[] >>
    rator_x_assum`to_i2_invariant`mp_tac >>
    simp[to_i2_invariant_def] >> strip_tac >>
    imp_res_tac EVERY2_LENGTH >> rfs[] ) >>
  conj_tac >- (
    rpt(BasicProvers.VAR_EQ_TAC) >> simp[Abbr`bs2`,Abbr`bs2'`] >>
    simp[next_addr_append] >>
    simp[FILTER_REVERSE,SUM_REVERSE,MAP_REVERSE] ) >>
  conj_tac >- simp[Abbr`bs2`,Abbr`bs2'`] >>
  rpt BasicProvers.VAR_EQ_TAC >> simp[] >> fs[] >>
  `FST s2_i1 = s20'` by (
    rator_x_assum`to_i1_invariant`mp_tac >>
    simp[to_i1_invariant_def] >>
    simp[Once s_to_i1_cases,PULL_EXISTS] ) >>
  first_assum(split_pair_match o concl) >> fs[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  fs[merge_alist_mod_env_def] >>
  `FST s2_i2 = s20'` by (
    rator_x_assum`to_i2_invariant`mp_tac >>
    simp[to_i2_invariant_def] >>
    simp[Once s_to_i2_cases,PULL_EXISTS] ) >>
  PairCases_on`s2_i2`>>fs[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  fs[store_to_exh_csg_rel] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  fs[GSYM csg_to_pat_MAP] >>
  imp_res_tac(
    MATCH_MP csg_rel_trans (SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO] v_pat_trans)) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  first_assum(Q.ISPEC_THEN`union locs f`mp_tac o
    MATCH_MP(GEN_ALL(ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]bEval_closed_locs))) >>
  discharge_hyps >- (
    simp[domain_union] >>
    fs[state_rel_def] >>
    conj_tac >- (
      match_mp_tac (GEN_ALL (MP_CANON MONO_EVERY)) >>
      ONCE_REWRITE_TAC[CONJ_COMM] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      Cases >> simp[closed_locs_union] ) >>
    fs[FEVERY_ALL_FLOOKUP] >>
    gen_tac >> Cases >> simp[] >> strip_tac >>
    res_tac >> fs[] >>
    match_mp_tac (GEN_ALL (MP_CANON MONO_EVERY)) >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    simp[closed_locs_union] ) >>
  simp[] >> strip_tac >>
  imp_res_tac bEval_code >>
  fs[domain_union,lookup_union] >>
  conj_tac >- (
    rw[] >- (
      res_tac >>
      imp_res_tac renumber_code_locs_imp_inc >>
      simp[] ) >>
    fs[EVERY_MEM] >> res_tac >> simp[] ) >>
  conj_tac >- (
    rpt gen_tac >>
    BasicProvers.CASE_TAC >- (
      simp[Abbr`new_code`,lookup_fromAList,ALOOKUP_MAP] >> strip_tac >>
      qpat_assum`X ⊆ Y`mp_tac >>
      simp[code_locs_def] >>
      simp[Once code_locs_FLAT_MAP] >>
      simp[SUBSET_DEF,MEM_FLAT,MEM_MAP,PULL_EXISTS,EVERY_MEM] >> rw[] >>
      imp_res_tac ALOOKUP_MEM >> res_tac >> fs[] >>
      res_tac >> fs[EVERY_MEM] ) >>
    rw[] >> res_tac >>
    fs[EVERY_MEM] >> rw[] >>
    imp_res_tac renumber_code_locs_imp_inc >>
    res_tac >> simp[] ) >>
  fs[state_rel_def] >>
  simp[Abbr`bs2`,Abbr`bs2'`] >>
  qexists_tac`union locs f` >> simp[] >>
  simp[domain_union] >>
  fs[REVERSE_APPEND]

val tac12 =
  first_assum (mp_tac o MATCH_MP (CONJUNCT1 pComp_correct)) >>
  discharge_hyps >- rfs[] >> strip_tac >>
  first_x_assum(mp_tac o MATCH_MP renumber_code_locs_correct) >>
  simp[pComp_contains_App_SOME,GSYM csg_to_pat_MAP] >>
  disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
  disch_then(qspec_then`rs.next_loc`mp_tac) >>
  simp[clos_numberTheory.res_rel_simp,PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  first_assum (mp_tac o MATCH_MP (GEN_ALL(ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] cAnnotate_correct))) >>
  rfs[] >> rfs[] >> fs[clos_numberTheory.res_rel_simp] >>
  disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
  disch_then(qspec_then`[]`mp_tac) >>
  simp[clos_annotateTheory.res_rel_simp,PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  first_assum (mp_tac o MATCH_MP (GEN_ALL(ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] cComp_correct))) >>
  simp[] >>
  disch_then(qspec_then`[]`mp_tac) >>
  simp[renumber_code_locs_def] >>
  qmatch_assum_abbrev_tac`bvl_bc_table real_inst_length na rs.rnext_label new_code = (f,r)` >>
  disch_then(qspecl_then[`s6 with code := union s6.code new_code`,`[]`,`f1`]mp_tac) >>
  qmatch_assum_abbrev_tac`cComp xs [] = X` >>
  qspecl_then[`xs`,`[]`]mp_tac cComp_code_locs >>
  `¬contains_Op_Label xs ∧
   ¬contains_App_SOME xs ∧
   ¬contains_Call xs` by tac2 >>
  qspecl_then[`xs`,`[]`]mp_tac code_locs_cComp_aux >>
  simp[Abbr`X`,Abbr`xs`,cAnnotate_code_locs] >>
  ntac 2 strip_tac >>
  `domain new_code = set (code_locs [e'])` by (
    simp[Abbr`new_code`,domain_fromAList,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] ) >>
  qmatch_assum_abbrev_tac`renumber_code_locs nn ee = X` >>
  qspecl_then[`nn`,`ee`]mp_tac renumber_code_locs_distinct >>
  simp[Abbr`nn`,Abbr`ee`,Abbr`X`] >> strip_tac >>
  discharge_hyps >- tac3 >>
  simp[clos_to_bvlTheory.res_rel_cases,PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  `domain f = domain new_code` by metis_tac[bvl_bc_table_thm] >>
  `DISJOINT (domain locs) (domain f)` by (
    simp[IN_DISJOINT] >> spose_not_then strip_assume_tac >>
    rfs[state_rel_def] >> res_tac >>
    fs[EVERY_MEM] >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
  ((
  qpat_assum`X = bc`mp_tac >>
  qspec_then`union locs f`(C(specl_args_of_then``bvl_bc``)mp_tac)bvl_bc_code_locs
  ) ORELSE
  qpat_assum`bs.code = X`mp_tac >>
  qspec_then`union locs f`(C(specl_args_of_then``bvl_bc``)mp_tac)bvl_bc_code_locs
  ) >>
  discharge_hyps >- tac4 >>
  strip_tac >> simp[] >>
  specl_args_of_then``bvl_bc``bvl_bc_append_out strip_assume_tac >>
  ((
  specl_args_of_then``compile_print_top``compile_print_top_thm mp_tac
  ) ORELSE (
  specl_args_of_then``compile_print_err``compile_print_err_thm mp_tac >>
  Q.PAT_ABBREV_TAC`ccode:bc_inst list = REVERSE (X Y)` >>
  simp[] >> strip_tac >>
  `∃ccode2. ccode = REVERSE r.out ++ REVERSE bc ++ ccode2` by (
    simp[Abbr`ccode`,emit_def] >>
    BasicProvers.CASE_TAC >> simp[] ) >>
  qunabbrev_tac`ccode` >>
  pop_assum mp_tac) ORELSE
  (
  simp[emit_def] >> pop_assum mp_tac
  )) >>
  simp[] >> ntac 2 strip_tac >>
  first_assum(fn th => qspecl_then[`bs`,`bc0`]mp_tac (CONJUNCT2 (MATCH_MP bvl_bc_table_thm th)) >> assume_tac th) >>
  BasicProvers.VAR_EQ_TAC >> simp[] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next bs bs1` >>
  first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO](Q.GENL[`f`]bvl_bc_correct))) >>
  simp[good_env_def] >>
  disch_then(qspecl_then[`union locs f`,`bs1 with output := s6.output`,`TCNonTail`,`0`,`r`]mp_tac o
    CONV_RULE (RESORT_FORALL_CONV(sort_vars["f'","bs1'","t","sz","cs"]))) >>
  simp[Once SWAP_REVERSE,Abbr`bs1`] >>
  disch_then(qspecl_then[`bc0++REVERSE r.out`]mp_tac) >>
  simp[AND_IMP_INTRO,GSYM CONJ_ASSOC] >>
  simp[Once (GSYM AND_IMP_INTRO)] >>
  discharge_hyps_keep >- tac5 >>
  discharge_hyps >- tac6 >>
  strip_tac >>
  `bs2.inst_length = bs.inst_length ∧
   bs2.code = bs.code` by (
    imp_res_tac RTC_bc_next_preserves >> fs[] ) >>
  fs[]

val tac14 =
  first_x_assum(strip_assume_tac o MATCH_MP evaluate_prompt_i1_success_globals) >>
  simp[Abbr`bs2`,Abbr`bs2'`] >> rw[] >>
  imp_res_tac RTC_bc_next_gvrel >>
  fs[Abbr`bs1'`,Abbr`bs5`] >>
  fs[gvrel_def,EVERY_MEM,MEM_EL,PULL_EXISTS] >>
  PairCases_on`grd'`>>Cases_on`s2`>>
  fs[env_rs_def] >>
  fs[to_i2_invariant_def,to_i1_invariant_def] >>
  fs[clos_numberTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_to_bvlTheory.state_rel_def,state_rel_def] >>
  fs[LIST_REL_EL_EQN,optionTheory.OPTREL_def,opt_val_rel_elim] >>
  rw[] >>
  Cases_on`n < LENGTH bs.globals` >- metis_tac[IS_SOME_EXISTS] >>
  qpat_assum`MAP X t6.globals = Z`mp_tac >>
  simp[LIST_EQ_REWRITE] >> strip_tac >>
  first_x_assum(qspec_then`n`mp_tac) >> simp[] >>
  disch_then(SUBST1_TAC o SYM) >>
  qpat_assum`∀n. n < LENGTH t5.globals ⇒ Y`(qspec_then`n`mp_tac) >> simp[] >>
  qpat_assum`∀n. n < LENGTH t2.globals ⇒ Y`(qspec_then`n`mp_tac) >> simp[] >>
  qpat_assum`∀n. n < LENGTH (s_to_Cs (FST res4)).globals ⇒ Y`(qspec_then`n`mp_tac) >> simp[] >>
  fs[csg_rel_unpair,s_to_Cs_unpair,store_to_exh_csg_rel,csg_to_pat_MAP,map_count_store_genv_def] >>
  simp[EL_MAP] >>
  qpat_assum`LIST_REL X Y (SND(FST res4))`mp_tac >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  first_x_assum(qspec_then`n`mp_tac) >> simp[optionTheory.OPTREL_def,EL_MAP] >>
  qpat_assum`LIST_REL X Y (SND(FST res3))`mp_tac >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  first_x_assum(qspec_then`n`mp_tac) >> simp[optionTheory.OPTREL_def,EL_MAP] >>
  qpat_assum`LIST_REL X (genv2++Z) Y`mp_tac >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  first_x_assum(qspec_then`n`mp_tac) >> simp[optionTheory.OPTREL_def,EL_MAP] >>
  qpat_assum`∀n. n < LENGTH grd0 + Y ⇒ X`(qspec_then`n`mp_tac) >>
  qpat_assum`X + Z = LENGTH Y`(assume_tac o SYM) >> simp[] >>
  `LENGTH grd0 ≤ n` by (
    imp_res_tac LIST_REL_LENGTH >> fs[] >>
    fs[LIST_EQ_REWRITE] >>
    DECIDE_TAC ) >>
  qpat_assum`∀n. n < LENGTH new_genv ⇒ Y`(qspec_then`n - LENGTH grd0`mp_tac) >>
  simp[IS_SOME_EXISTS,EL_APPEND2,PULL_EXISTS]

val _ = Parse.hide"new_env";

fun btotal f x = f x handle Interrupt => raise Interrupt | _ => false
fun named_var s = btotal (equal s o fst o dest_var)
fun filter_asms_varname s = POP_ASSUM_LIST(fn ls => map_every assume_tac (filter (can (find_term (named_var s) o concl)) ls))

val compile_top_thm = store_thm("compile_top_thm",
  ``∀ck env stm top res. evaluate_top ck env stm top res ⇒
     ∀rs types grd rss rsf bc bs bc0.
      env_rs env stm grd rs (bs with code := bc0) ∧
      (compile_top types rs top = (rss,rsf,bc)) ∧
      (case (SND(SND res)) of
       | Rval(_,envE) => IS_SOME types ⇒
           LIST_REL (λ(y,_,t) (x,v).
             y = x ∧
             (∀n. t ≠ Infer_Tuvar n) ∧
             (inf_type_to_string t = type_to_string (convert_t t)) ∧
             (t = Infer_Tapp [] TC_word8 ⇔ ∃w. v = Litv(Word8 w)) ∧
             (t = Infer_Tapp [] TC_char ⇔ ∃c. v = Litv(Char c)))
           (THE types) envE
       | Rerr(Rraise v) => ∀l. v ≠ Litv l
       | _ => T) ∧
      (bs.code = bc0 ++ REVERSE bc) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      ck ∧ IS_SOME bs.clock ∧
      SND(SND res) ≠ Rerr Rtype_error ∧
      SND(SND res) ≠ Rerr Rtimeout_error
      ⇒
      case res of (s,envC,env_or_err) =>
        ∃bs' grd'.
        bc_next^* bs bs' ∧
        let (new_env,rs',success,str) =
          case env_or_err of Rval(envM,envE) =>
            ((envM++FST env,merge_alist_mod_env envC (FST(SND env)),envE ++ (SND(SND env))),rss,T,
             (case types of NONE => "" | SOME t =>
              print_result (convert_env2 t) top env_or_err))
          | Rerr(Rraise _) =>
            (env,rsf,F,
             print_result (convert_env2 (THE types)) top env_or_err) in
        bc_fetch bs' = SOME (Stop success) ∧
        bs'.output = bs.output ++ str ∧
        (success ∧ EVERY IS_SOME bs.globals ⇒ EVERY IS_SOME bs'.globals) ∧
        env_rs new_env s grd' rs' bs'``,
  ho_match_mp_tac evaluate_top_ind >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >>
    simp[compile_top_def] >>
    Q.PAT_ABBREV_TAC`non = (none_tag,(X:tid_or_exn option))` >>
    Q.PAT_ABBREV_TAC`som = (some_tag,(X:tid_or_exn option))` >>
    strip_tac >>
    `∃m10 m20. rs.globals_env = (m10,m20)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    qspecl_then[`m10`,`m20`,`Tdec d`]mp_tac top_to_i1_correct >>
    PairCases_on`grd`>>PairCases_on`env`>>PairCases_on`s1`>>fs[env_rs_def] >>
    REWRITE_TAC[Once CONJ_COMM] >>
    REWRITE_TAC[Once (GSYM CONJ_ASSOC)] >>
    REWRITE_TAC[Once (GSYM AND_IMP_INTRO)] >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    `∃v m1 m2 p1. top_to_i1 rs.next_global m10 m20 (Tdec d) = (v,m1,m2,p1)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    simp[Once evaluate_top_cases] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    disch_then(mp_tac o CONJUNCT1) >> rfs[] >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    disch_then(qx_choosel_then[`s2_i1`,`new_genv`]strip_assume_tac) >>
    `∃c exh p. prompt_to_i2 rs.contags_env p1 = (c,exh,p)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    first_assum (mp_tac o (MATCH_MP (
      CONV_RULE (
        ONCE_REWRITE_CONV[CONJ_ASSOC] THENC
        ONCE_REWRITE_CONV[CONJ_COMM] THENC
        ONCE_REWRITE_CONV[GSYM CONJ_ASSOC] THENC
        ONCE_REWRITE_CONV[GSYM AND_IMP_INTRO]) prompt_to_i2_correct))) >>
    REWRITE_TAC[Once EQ_SYM_EQ] >>
    REWRITE_TAC[Once (GSYM CONJ_ASSOC)] >>
    REWRITE_TAC[Once (GSYM AND_IMP_INTRO)] >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    REWRITE_TAC[Once (GSYM AND_IMP_INTRO)] >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    simp[] >>
    disch_then(qx_choosel_then[`new_genv_i2`,`s2_i2`,`gtagenv2`]strip_assume_tac) >>
    `∃n e. prompt_to_i3 non som (LENGTH grd0) p = (n,e)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    first_assum (mp_tac o (MATCH_MP (
      ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
        prompt_to_i3_correct))) >>
    simp[] >>
    `LENGTH genv2 = LENGTH grd0` by (
      fs[to_i2_invariant_def] >>
      imp_res_tac EVERY2_LENGTH >>
      fs[] ) >>
    simp[] >>
    simp[Once result_to_i3_cases] >>
    strip_tac >>
    first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_exh_correct)) >>
    simp[] >> simp[env_to_exh_MAP] >>
    qmatch_assum_rename_tac`csg_rel (v_to_exh rs.exh) ((s10,s20),genv2) csgh` >>
    `store_to_exh (exh ⊌ rs.exh) ((s10,s20),genv2) csgh` by tac1 >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    simp[Once result_to_exh_cases] >>
    disch_then(qspec_then`exh ⊌ rs.exh`mp_tac) >> simp[] >>
    strip_tac >>
    first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_pat_correct)) >>
    simp[] >>
    disch_then(qx_choosel_then[`res3`]strip_assume_tac) >>
    first_assum (qspec_then`[]`mp_tac o MATCH_MP (CONJUNCT1 evaluate_pat_exp_pat)) >>
    Q.PAT_ABBREV_TAC`ep = exp_to_pat X Y` >>
    disch_then(qspecl_then[`sp`,`ep`]mp_tac) >>
    discharge_hyps >- (
      simp[CONJUNCT1 exp_pat_refl] >> fs[csg_to_pat_MAP] ) >>
    disch_then(qx_choosel_then[`res4`]strip_assume_tac) >>
    ntac 3 (first_assum(split_applied_pair_tac o lhs o concl) >> fs[]) >>
    tac12 >> tac7 >>
    first_x_assum(qspec_then`bs2`mp_tac) >>
    simp[Abbr`bs2`,bvl_to_bc_value_def,Abbr`non`] >>
    disch_then(qspec_then`none_tag+1`mp_tac)>>simp[] >>
    qmatch_assum_rename_tac`state_rel f2 t5 t6` >>
    qabbrev_tac`bvs = MAP (λv. bvl_to_bc_value (union locs f) (THE (EL (m2 ' v) t6.globals))) (new_dec_vs d)` >>
    disch_then(qspec_then`bvs`mp_tac) >>
    ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
    discharge_hyps_keep >- tac8 >>
    qmatch_abbrev_tac`(Q ⇒ R) ⇒ Z` >>
    `Q ∧
      LIST_REL (v_bv (grd0 ++ new_genv, gtagenv2, rs.exh ⊌ exh, t6.refs, t6.code, union locs f))
                  (MAP SND new_env) bvs` by (
      simp[Abbr`Q`,Abbr`R`,Abbr`Z`] >>
      last_x_assum mp_tac >>
      Cases_on`d`>>fs[] >>
      simp[Once evaluate_dec_cases,PULL_EXISTS] >>
      simp[FST_triple] >>
      simp[build_rec_env_MAP] >>
      rpt gen_tac >> strip_tac >>
      `LENGTH bvs = LENGTH new_env` by (
        simp[Abbr`bvs`] >>
        imp_res_tac pmatch_dom >> fs[] >>
        metis_tac[LENGTH_MAP] ) >>
      rfs[Abbr`bvs`] >>
      simp[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS,EL_MAP] >>
      simp[FLOOKUP_DEF,libTheory.el_check_def] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      TRY (BasicProvers.CASE_TAC >> fs[] >> NO_TAC) >>
      `LENGTH t6.globals = LENGTH grd0 + LENGTH new_genv` by (
        fs[gvrel_def,clos_numberTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_to_bvlTheory.state_rel_def] >>
        fs[store_to_exh_csg_rel,csg_rel_unpair,map_count_store_genv_def] >>
        imp_res_tac EVERY2_LENGTH >> fs[] >> rw[] >>
        rator_x_assum`to_i2_invariant`mp_tac >>
        simp[to_i2_invariant_def] >> strip_tac >>
        imp_res_tac EVERY2_LENGTH >> fs[] >>
        fs[s_to_Cs_unpair]) >>
      (conj_asm2_tac >- (
        BasicProvers.CASE_TAC >> fs[] >>
        fs[LIST_REL_EL_EQN] >>
        simp[MEM_ZIP,PULL_EXISTS,EL_MAP] >>
        qx_gen_tac`n`>>strip_tac >>
        first_x_assum(qspec_then`n`mp_tac) >>
        first_x_assum(qspec_then`n`mp_tac) >>
        simp[] >>
        simp[UNCURRY] >> simp[v_bv_def] >>
        ntac 2 strip_tac >>
        ((Q.PAT_ABBREV_TAC`pv:string = EL n X` >>
          `FST (EL n new_env) = pv` by (
            imp_res_tac pmatch_dom >>
            fs[Abbr`pv`] >>
            pop_assum mp_tac >>
            simp[Once LIST_EQ_REWRITE,EL_MAP] ))
          ORELSE
         (simp[EL_MAP,UNCURRY] >>
          Q.PAT_ABBREV_TAC`pv:string = FST(EL n X)`)) >>
        fs[gvrel_def,clos_numberTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_to_bvlTheory.state_rel_def] >>
        rator_x_assum`to_i1_invariant`mp_tac >>
        simp[to_i1_invariant_def] >>
        simp[Once v_to_i1_cases] >>
        simp[Once v_to_i1_cases] >>
        fs[] >>
        simp[alistTheory.ALOOKUP_APPEND] >>
        disch_then(qspec_then`pv`mp_tac o CONJUNCT1 o CONJUNCT1 o CONJUNCT2) >>
        (BasicProvers.CASE_TAC >- (
          imp_res_tac alistTheory.ALOOKUP_NONE >>
          imp_res_tac pmatch_dom >>
          fs[MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX,MEM_MAP,PULL_EXISTS] >>
          metis_tac[MEM_EL,EL_MAP,LENGTH_MAP] )) >>
        simp[FLOOKUP_DEF] >> strip_tac >> simp[] >>
        qpat_assum`LIST_REL R X gv`mp_tac >>
        simp[EVERY2_EVERY,GSYM AND_IMP_INTRO,EVERY_MEM,MEM_ZIP,PULL_EXISTS] >>
        simp[opt_val_rel_elim,optionTheory.OPTREL_def] >> strip_tac >>
        disch_then(qspec_then`m2 ' pv`mp_tac) >> simp[] >>
        (reverse strip_tac >- (
           simp[EL_MAP] >> fs[] >>
           TRY conj_tac >- (
             metis_tac[can_print] ) >>
           conj_tac >>
           rpt strip_tac >> fs[] >>
           rpt BasicProvers.VAR_EQ_TAC >>
           TRY(rfs[EL_MAP,UNCURRY] >> NO_TAC) >>
           fs[Q.SPECL[`X`,`Litv Y`] (CONJUNCT1 v_to_i1_cases)] >>
           BasicProvers.VAR_EQ_TAC >>
           fs[Q.SPECL[`X`,`Litv_i1 Y`] (CONJUNCT1 v_to_i2_cases)] >>
           BasicProvers.VAR_EQ_TAC >>
           fs[Q.SPECL[`X`,`Litv_i2 Y`] (CONJUNCT1 v_to_exh_cases)] >>
           BasicProvers.VAR_EQ_TAC >>
           fs[] >> BasicProvers.VAR_EQ_TAC >>
           fs[clos_numberTheory.val_rel_simp] >>
           BasicProvers.VAR_EQ_TAC >>
           fs[clos_annotateTheory.val_rel_simp] >>
           BasicProvers.VAR_EQ_TAC >>
           fs[clos_to_bvlTheory.val_rel_SIMP] >>
           BasicProvers.VAR_EQ_TAC >>
           simp[bvl_to_bc_value_def] >>
           simp[ORD_11])) >>
        simp[EL_MAP] >>
        rator_x_assum`to_i2_invariant`mp_tac >>
        simp[to_i2_invariant_def] >>
        ntac 5 disj2_tac >> disj1_tac >>
        simp[LIST_REL_EL_EQN] >> disj2_tac >>
        qexists_tac`m2 ' pv` >> simp[optionTheory.OPTREL_def] >>
        fs[gvrel_def,clos_numberTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_to_bvlTheory.state_rel_def] >>
        fs[store_to_exh_csg_rel,csg_rel_unpair,map_count_store_genv_def] >>
        fs[s_to_Cs_unpair] >>
        rpt(qpat_assum`LIST_REL(OPTREL X)Y Z`mp_tac) >>
        simp[LIST_REL_EL_EQN,optionTheory.OPTREL_def,map_count_store_genv_def,EL_MAP] >>
        rpt strip_tac >>
        rpt(first_x_assum(qspec_then`m2 ' pv`mp_tac)) >>
        simp[optionTheory.OPTREL_def] >>
        metis_tac[optionTheory.NOT_NONE_SOME] )) >>
      qx_gen_tac`n`>>strip_tac >>
      ((CHANGED_TAC (imp_res_tac pmatch_dom) >>
        Q.PAT_ABBREV_TAC`pv:string = EL n (X Y)` >>
        `FST(EL n new_env) = pv` by (
          simp[Abbr`pv`] >>
          pop_assum mp_tac >>
          simp[Once LIST_EQ_REWRITE,EL_MAP] ))
       ORELSE
       (simp[EL_MAP,UNCURRY] >>
        Q.PAT_ABBREV_TAC`pv:string = FST(EL n X)`)) >>
      fs[] >>
      simp[v_bv_def] >>
      rator_x_assum`to_i1_invariant`mp_tac >>
      simp[to_i1_invariant_def] >>
      simp[Once v_to_i1_cases] >>
      simp[Once v_to_i1_cases] >>
      fs[] >>
      simp[alistTheory.ALOOKUP_APPEND] >>
      disch_then(qspec_then`pv`mp_tac o CONJUNCT1 o CONJUNCT1 o CONJUNCT2) >>
      (BasicProvers.CASE_TAC >- (
        imp_res_tac alistTheory.ALOOKUP_NONE >>
        imp_res_tac pmatch_dom >>
        fs[MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX,MEM_MAP,PULL_EXISTS] >>
        metis_tac[MEM_EL,EL_MAP,LENGTH_MAP] )) >>
      ((qmatch_assum_abbrev_tac`ALOOKUP (MAP X ls) pv = Z` >>
        `ALL_DISTINCT (MAP FST (MAP X ls))` by (
          simp[MAP_MAP_o,Abbr`X`,Abbr`ls`,combinTheory.o_DEF,UNCURRY,ETA_AX] ) >>
        map_every qunabbrev_tac[`ls`,`Z`] >>
        imp_res_tac alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
        pop_assum kall_tac >> pop_assum mp_tac >>
        simp[MEM_MAP,Abbr`X`,PULL_EXISTS,UNCURRY] >>
        qmatch_assum_rename_tac`Abbrev(pv = FST (EL n l1))` >>
        disch_then(qspec_then`EL n l1`mp_tac) >>
        discharge_hyps >- metis_tac[MEM_EL] >>
        simp[] >> strip_tac >> rpt gen_tac)
       ORELSE
       (`MEM (EL n new_env) new_env` by metis_tac[MEM_EL] >>
        `ALL_DISTINCT (MAP FST new_env)` by metis_tac[] >>
        imp_res_tac alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
        pop_assum(qspecl_then[`SND (EL n new_env)`,`FST (EL n new_env)`]mp_tac))) >>
      simp[] >> strip_tac >>
      TRY strip_tac >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      rator_x_assum`to_i2_invariant`mp_tac >>
      simp[to_i2_invariant_def] >>
      strip_tac >>
      rator_x_assum`LIST_REL`mp_tac >>
      simp[LIST_REL_EL_EQN] >> strip_tac >>
      pop_assum(fn th => first_assum(mp_tac o MATCH_MP th)) >>
      simp[optionTheory.OPTREL_def] >> strip_tac >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      rator_x_assum`store_to_exh`mp_tac >>
      simp[store_to_exh_csg_rel,csg_rel_unpair] >> strip_tac >>
      rator_x_assum`LIST_REL`mp_tac >>
      simp[LIST_REL_EL_EQN] >> strip_tac >> fs[] >> rfs[] >>
      pop_assum(fn th => first_assum(mp_tac o MATCH_MP th)) >>
      simp[optionTheory.OPTREL_def] >> strip_tac >>
      imp_res_tac FUNION_COMM >>
      pop_assum(SUBST1_TAC o SYM) >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      rator_x_assum`csg_rel`mp_tac >>
      rator_x_assum`csg_rel`mp_tac >>
      simp[csg_rel_unpair,map_count_store_genv_def] >>
      ntac 2 strip_tac >>
      qpat_assum`LIST_REL (OPTREL X) Y Z`mp_tac >>
      qpat_assum`LIST_REL (OPTREL X) Y Z`mp_tac >>
      simp[LIST_REL_EL_EQN] >>
      ntac 2 strip_tac >>
      fs[FLOOKUP_DEF] >>
      first_x_assum(qspec_then`m2 ' pv`mp_tac) >>
      first_x_assum(qspec_then`m2 ' pv`mp_tac) >>
      simp[EL_MAP,optionTheory.OPTREL_def] >> strip_tac >>
      simp[] >> strip_tac >>
      imp_res_tac v_pat_trans >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      rator_x_assum`clos_number$state_rel`mp_tac >>
      simp[clos_numberTheory.state_rel_def,s_to_Cs_unpair] >> strip_tac >>
      qpat_assum`LIST_REL (OPTREL X) Y Z`mp_tac >>
      simp[LIST_REL_EL_EQN] >> strip_tac >>
      first_x_assum(qspec_then`m2 ' pv`mp_tac) >>
      simp[EL_MAP,optionTheory.OPTREL_def] >> strip_tac >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      rator_x_assum`clos_annotate$state_rel`mp_tac >>
      simp[clos_annotateTheory.state_rel_def] >> strip_tac >>
      qpat_assum`LIST_REL (OPTREL X) Y Z`mp_tac >>
      simp[LIST_REL_EL_EQN] >> strip_tac >>
      first_x_assum(qspec_then`m2 ' pv`mp_tac) >>
      simp[EL_MAP,optionTheory.OPTREL_def] >> strip_tac >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      rator_x_assum`clos_to_bvl$state_rel`mp_tac >>
      simp[clos_to_bvlTheory.state_rel_def,opt_val_rel_elim] >> strip_tac >>
      qpat_assum`LIST_REL (OPTREL X) Y Z`mp_tac >>
      simp[LIST_REL_EL_EQN] >> strip_tac >>
      first_x_assum(qspec_then`m2 ' pv`mp_tac) >>
      simp[EL_MAP,optionTheory.OPTREL_def] >> strip_tac >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      NO_TAC) >>
    simp[Abbr`Q`,Abbr`R`,Abbr`Z`] >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next bs bs1` >>
    qmatch_assum_abbrev_tac`bc_next^* bs5' bs2'` >>
    qpat_assum`bc_next^* bs5' bs2'`mp_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs1' bs5` >>
    `bs5' = bs5` by (
      simp[Abbr`bs5`,Abbr`bs5'`,bvl_to_bc_value_def]) >>
    strip_tac >>
    `bc_next^* bs1' bs2'` by metis_tac[RTC_TRANSITIVE,transitive_def] >>
    pop_assum(mp_tac o MATCH_MP RTC_bc_next_prepend_output) >>
    disch_then(qspec_then`bs.output`assume_tac) >>
    qmatch_assum_abbrev_tac`bc_next^* bs1'' bs2` >>
    `bs1'' = bs1` by (
      simp[Abbr`bs1''`,Abbr`bs1'`,Abbr`bs1`,bc_state_component_equality] >>
      fs[clos_to_bvlTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_numberTheory.state_rel_def,s_to_Cs_unpair] ) >>
    qexists_tac`bs2` >>
    simp[RIGHT_EXISTS_AND_THM] >>
    conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
    conj_tac >- (
      fs[Abbr`bs2`,bc_fetch_with_output] ) >>
    conj_tac >- (
      simp[Abbr`bs2`,Abbr`bs2'`] >>
      simp[optionTheory.option_case_compute] >>
      Q.PAT_ABBREV_TAC`b = IS_SOME Z` >>
      `t6.output = ""` by (
        fs[clos_to_bvlTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_numberTheory.state_rel_def,s_to_Cs_unpair] ) >>
      Cases_on`b = F` >> simp[] >>
      qunabbrev_tac`b` >>
      fs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS] >>
      last_x_assum mp_tac >>
      simp[print_result_def] >>
      BasicProvers.CASE_TAC >>
      simp[Once evaluate_dec_cases] >>
      simp[] >> strip_tac >>
      simp[(*print_envC_def,*)print_envE_def] >>
      TRY (
        rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
        qunabbrev_tac`bvs` >> fs[print_envE_def,inferPropsTheory.convert_env2_def] >>
        NO_TAC ) >>
      match_mp_tac print_bv_list_print_envE >>
      rpt BasicProvers.VAR_EQ_TAC >>
      HINT_EXISTS_TAC >>
      imp_res_tac pmatch_dom >> fs[] >>
      qpat_assum`LIST_REL X x' Y`mp_tac >>
      simp[inferPropsTheory.convert_env2_def,EVERY2_MAP,EVERY_MAP] >>
      simp[LIST_REL_EL_EQN,EVERY_MEM,MEM_EL,PULL_EXISTS] >>
      strip_tac >>
      imp_res_tac LIST_REL_LENGTH >> fs[build_rec_env_MAP] >>
      simp[GSYM IMP_CONJ_THM,GSYM FORALL_AND_THM] >>
      qx_gen_tac`n` >> strip_tac >>
      first_x_assum(qspec_then`n`mp_tac) >> simp[] >>
      simp[EL_MAP,UNCURRY] >>
      fs[EVERY2_MAP,LIST_REL_EL_EQN,UNCURRY] >>
      rw[] >>
      first_x_assum(qspec_then`n`mp_tac) >>
      first_x_assum(qspec_then`n`mp_tac) >>
      simp[] >> ntac 2 strip_tac >>
      ((qmatch_rename_tac`convert_t tt = _ ⇔ _` >>
        Cases_on`tt`>>fs[inferPropsTheory.convert_t_def])
       ORELSE
       (qmatch_rename_tac`convert_t tt ≠ _` >>
       Cases_on`tt`>>fs[inferPropsTheory.convert_t_def] ))) >>
    conj_asm2_tac >- tac14 >>
    simp[EXISTS_PROD,merge_alist_mod_env_def] >>
    PairCases_on`s2` >> simp[env_rs_def] >>
    simp[RIGHT_EXISTS_AND_THM] >>
    conj_asm1_tac >- tac10 >>
    qexists_tac`grd0 ++ new_genv` >>
    tac11) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >>
    simp[compile_top_def] >>
    Q.PAT_ABBREV_TAC`non = (none_tag,(X:tid_or_exn option))` >>
    Q.PAT_ABBREV_TAC`som = (some_tag,(X:tid_or_exn option))` >>
    strip_tac >>
    `∃m10 m20. rs.globals_env = (m10,m20)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    qspecl_then[`m10`,`m20`,`Tdec d`]mp_tac top_to_i1_correct >>
    PairCases_on`grd`>>PairCases_on`env`>>PairCases_on`s1`>>fs[env_rs_def] >>
    REWRITE_TAC[Once CONJ_COMM] >>
    REWRITE_TAC[Once (GSYM CONJ_ASSOC)] >>
    REWRITE_TAC[Once (GSYM AND_IMP_INTRO)] >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    `∃v m1 m2 p1. top_to_i1 rs.next_global m10 m20 (Tdec d) = (v,m1,m2,p1)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    simp[Once evaluate_top_cases] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    disch_then(mp_tac o CONJUNCT2) >> rfs[] >>
    ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    discharge_hyps >- simp[] >>
    disch_then(qx_choosel_then[`s2_i1`,`new_genv`,`err_i1`]strip_assume_tac) >>
    `∃c exh p. prompt_to_i2 rs.contags_env p1 = (c,exh,p)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    first_assum (mp_tac o (MATCH_MP (
      CONV_RULE (
        ONCE_REWRITE_CONV[CONJ_ASSOC] THENC
        ONCE_REWRITE_CONV[CONJ_COMM] THENC
        ONCE_REWRITE_CONV[GSYM CONJ_ASSOC] THENC
        ONCE_REWRITE_CONV[GSYM AND_IMP_INTRO]) prompt_to_i2_correct))) >>
    REWRITE_TAC[Once EQ_SYM_EQ] >>
    REWRITE_TAC[Once (GSYM CONJ_ASSOC)] >>
    REWRITE_TAC[Once (GSYM AND_IMP_INTRO)] >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    REWRITE_TAC[Once (GSYM AND_IMP_INTRO)] >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    simp[] >>
    discharge_hyps >- (
      fs[result_to_i1_cases] >> fs[] >>
      fs[top_to_i1_def,LET_THM,UNCURRY] >>
      rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
      simp[dec_to_i1_def] >>
      BasicProvers.CASE_TAC >> simp[not_mod_decs_def] ) >>
    disch_then(qx_choosel_then[`new_genv_i2`,`s2_i2`,`res_i2`,`gtagenv2`]strip_assume_tac) >>
    `∃n e. prompt_to_i3 non som (LENGTH grd0) p = (n,e)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    first_assum (mp_tac o (MATCH_MP (
      ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
        prompt_to_i3_correct))) >>
    simp[] >>
    `LENGTH genv2 = LENGTH grd0` by (
      fs[to_i2_invariant_def] >>
      imp_res_tac EVERY2_LENGTH >>
      fs[] ) >>
    simp[] >>
    simp[Once result_to_i3_cases] >>
    discharge_hyps >- (
      fs[result_to_i2_cases,result_to_i1_cases] >> fs[] ) >>
    reverse strip_tac >- (
      fs[result_to_i2_cases,result_to_i1_cases] >> fs[] ) >>
    first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_exh_correct)) >>
    simp[] >> simp[env_to_exh_MAP] >>
    qmatch_assum_rename_tac`csg_rel (v_to_exh rs.exh) ((s10,s20),genv2) csgh` >>
    `store_to_exh (exh ⊌ rs.exh) ((s10,s20),genv2) csgh` by tac1 >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    simp[Once result_to_exh_cases] >>
    disch_then(qspec_then`exh ⊌ rs.exh`mp_tac) >> simp[] >>
    strip_tac >>
    first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_pat_correct)) >>
    simp[] >>
    disch_then(qx_choosel_then[`res3`]strip_assume_tac) >>
    first_assum (qspec_then`[]`mp_tac o MATCH_MP (CONJUNCT1 evaluate_pat_exp_pat)) >>
    Q.PAT_ABBREV_TAC`ep = exp_to_pat X Y` >>
    disch_then(qspecl_then[`sp`,`ep`]mp_tac) >>
    discharge_hyps >- (
      simp[CONJUNCT1 exp_pat_refl] >> fs[csg_to_pat_MAP] ) >>
    disch_then(qx_choosel_then[`res4`]strip_assume_tac) >>
    ntac 3 (first_assum(split_applied_pair_tac o lhs o concl) >> fs[]) >>
    tac12 >> tac7 >>
    first_x_assum(qspec_then`bs2`mp_tac) >>
    simp[Abbr`bs2`,bvl_to_bc_value_def,Abbr`som`] >>
    disch_then(qspec_then`some_tag+1`mp_tac)>>simp[] >>
    qmatch_assum_rename_tac`state_rel f2 t5 t6` >>
    `some_tag ≠ none_tag` by EVAL_TAC >> simp[] >>
    ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
    discharge_hyps_keep >- tac8 >>
    qmatch_assum_abbrev_tac`bc_next bs bs1` >>
    qmatch_assum_abbrev_tac`bc_next^* bs1' bs5` >>
    discharge_hyps >- (
      rpt BasicProvers.VAR_EQ_TAC >>
      metis_tac[can_print] ) >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs5' bs2'` >>
    `bs5' = bs5` by (
      simp[Abbr`bs5`,Abbr`bs5'`,bvl_to_bc_value_def]) >>
    `bc_next^* bs1' bs2'` by metis_tac[RTC_TRANSITIVE,transitive_def] >>
    pop_assum(mp_tac o MATCH_MP RTC_bc_next_prepend_output) >>
    disch_then(qspec_then`bs.output`assume_tac) >>
    qmatch_assum_abbrev_tac`bc_next^* bs1'' bs2` >>
    `bs1'' = bs1` by (
      simp[Abbr`bs1''`,Abbr`bs1'`,Abbr`bs1`,bc_state_component_equality] >>
      fs[clos_to_bvlTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_numberTheory.state_rel_def,s_to_Cs_unpair] ) >>
    qexists_tac`bs2` >>
    simp[RIGHT_EXISTS_AND_THM] >>
    conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
    Cases_on`err`>>fs[] >>
    simp[RIGHT_EXISTS_AND_THM] >>
    conj_tac >- (
      fs[Abbr`bs2`,bc_fetch_with_output] ) >>
    conj_tac >- tac9 >>
    PairCases_on`s2` >> simp[env_rs_def,Once EXISTS_PROD] >>
    simp[RIGHT_EXISTS_AND_THM] >>
    conj_asm1_tac >- tac10 >>
    qexists_tac`grd0 ++ new_genv` >>
    tac11) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >>
    simp[compile_top_def] >>
    Q.PAT_ABBREV_TAC`non = (none_tag,(X:tid_or_exn option))` >>
    Q.PAT_ABBREV_TAC`som = (some_tag,(X:tid_or_exn option))` >>
    strip_tac >>
    `∃m10 m20. rs.globals_env = (m10,m20)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    qspecl_then[`m10`,`m20`,`Tmod mn specs ds`]mp_tac top_to_i1_correct >>
    PairCases_on`grd`>>PairCases_on`env`>>PairCases_on`s1`>>fs[env_rs_def] >>
    REWRITE_TAC[Once CONJ_COMM] >>
    REWRITE_TAC[Once (GSYM CONJ_ASSOC)] >>
    REWRITE_TAC[Once (GSYM AND_IMP_INTRO)] >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    `∃v m1 m2 p1. top_to_i1 rs.next_global m10 m20 (Tmod mn specs ds) = (v,m1,m2,p1)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    simp[Once evaluate_top_cases] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    disch_then(mp_tac o CONJUNCT1) >> rfs[] >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    disch_then(qx_choosel_then[`s2_i1`,`new_genv`]strip_assume_tac) >>
    `∃c exh p. prompt_to_i2 rs.contags_env p1 = (c,exh,p)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    first_assum (mp_tac o (MATCH_MP (
      CONV_RULE (
        ONCE_REWRITE_CONV[CONJ_ASSOC] THENC
        ONCE_REWRITE_CONV[CONJ_COMM] THENC
        ONCE_REWRITE_CONV[GSYM CONJ_ASSOC] THENC
        ONCE_REWRITE_CONV[GSYM AND_IMP_INTRO]) prompt_to_i2_correct))) >>
    REWRITE_TAC[Once EQ_SYM_EQ] >>
    REWRITE_TAC[Once (GSYM CONJ_ASSOC)] >>
    REWRITE_TAC[Once (GSYM AND_IMP_INTRO)] >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    REWRITE_TAC[Once (GSYM AND_IMP_INTRO)] >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    simp[] >>
    disch_then(qx_choosel_then[`new_genv_i2`,`s2_i2`,`gtagenv2`]strip_assume_tac) >>
    `∃n e. prompt_to_i3 non som (LENGTH grd0) p = (n,e)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    first_assum (mp_tac o (MATCH_MP (
      ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
        prompt_to_i3_correct))) >>
    simp[] >>
    `LENGTH genv2 = LENGTH grd0` by (
      fs[to_i2_invariant_def] >>
      imp_res_tac EVERY2_LENGTH >>
      fs[] ) >>
    simp[] >>
    simp[Once result_to_i3_cases] >>
    strip_tac >>
    first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_exh_correct)) >>
    simp[] >> simp[env_to_exh_MAP] >>
    qmatch_assum_rename_tac`csg_rel (v_to_exh rs.exh) ((s10,s20),genv2) csgh` >>
    `store_to_exh (exh ⊌ rs.exh) ((s10,s20),genv2) csgh` by tac1 >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    simp[Once result_to_exh_cases] >>
    disch_then(qspec_then`exh ⊌ rs.exh`mp_tac) >> simp[] >>
    strip_tac >>
    first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_pat_correct)) >>
    simp[] >>
    disch_then(qx_choosel_then[`res3`]strip_assume_tac) >>
    first_assum (qspec_then`[]`mp_tac o MATCH_MP (CONJUNCT1 evaluate_pat_exp_pat)) >>
    Q.PAT_ABBREV_TAC`ep = exp_to_pat X Y` >>
    disch_then(qspecl_then[`sp`,`ep`]mp_tac) >>
    discharge_hyps >- (
      simp[CONJUNCT1 exp_pat_refl] >> fs[csg_to_pat_MAP] ) >>
    disch_then(qx_choosel_then[`res4`]strip_assume_tac) >>
    ntac 3 (first_assum(split_applied_pair_tac o lhs o concl) >> fs[]) >>
    tac12 >> tac7 >>
    first_x_assum(qspec_then`bs2`mp_tac) >>
    simp[Abbr`bs2`,bvl_to_bc_value_def,Abbr`non`] >>
    disch_then(qspec_then`none_tag+1`mp_tac)>>simp[] >>
    qmatch_assum_rename_tac`state_rel f2 t5 t6` >>
    discharge_hyps_keep >- tac8 >>
    qmatch_assum_abbrev_tac`bc_next bs bs1` >>
    qmatch_assum_abbrev_tac`bc_next^* bs1' bs5` >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs5' bs2'` >>
    `bs5' = bs5` by (
      simp[Abbr`bs5`,Abbr`bs5'`,bvl_to_bc_value_def]) >>
    `bc_next^* bs1' bs2'` by metis_tac[RTC_TRANSITIVE,transitive_def] >>
    pop_assum(mp_tac o MATCH_MP RTC_bc_next_prepend_output) >>
    disch_then(qspec_then`bs.output`assume_tac) >>
    qmatch_assum_abbrev_tac`bc_next^* bs1'' bs2` >>
    `bs1'' = bs1` by (
      simp[Abbr`bs1''`,Abbr`bs1'`,Abbr`bs1`,bc_state_component_equality] >>
      fs[clos_to_bvlTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_numberTheory.state_rel_def,s_to_Cs_unpair] ) >>
    qexists_tac`bs2` >>
    simp[RIGHT_EXISTS_AND_THM] >>
    conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
    conj_tac >- (
      fs[Abbr`bs2`,bc_fetch_with_output] ) >>
    conj_tac >- tac9 >>
    conj_asm2_tac >- tac14 >>
    simp[EXISTS_PROD,merge_alist_mod_env_def] >>
    PairCases_on`s2` >> simp[env_rs_def] >>
    simp[RIGHT_EXISTS_AND_THM] >>
    conj_asm1_tac >- tac10 >>
    qexists_tac`grd0 ++ new_genv` >>
    tac11) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >>
    simp[compile_top_def] >>
    Q.PAT_ABBREV_TAC`non = (none_tag,(X:tid_or_exn option))` >>
    Q.PAT_ABBREV_TAC`som = (some_tag,(X:tid_or_exn option))` >>
    strip_tac >>
    `∃m10 m20. rs.globals_env = (m10,m20)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    qspecl_then[`m10`,`m20`,`Tmod mn specs ds`]mp_tac top_to_i1_correct >>
    PairCases_on`grd`>>PairCases_on`env`>>PairCases_on`s1`>>fs[env_rs_def] >>
    REWRITE_TAC[Once CONJ_COMM] >>
    REWRITE_TAC[Once (GSYM CONJ_ASSOC)] >>
    REWRITE_TAC[Once (GSYM AND_IMP_INTRO)] >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    `∃v m1 m2 p1. top_to_i1 rs.next_global m10 m20 (Tmod mn specs ds) = (v,m1,m2,p1)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    simp[Once evaluate_top_cases] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    disch_then(mp_tac o CONJUNCT2) >> rfs[] >>
    ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    discharge_hyps >- simp[] >>
    disch_then(qx_choosel_then[`s2_i1`,`new_genv`,`err_i1`]strip_assume_tac) >>
    `∃c exh p. prompt_to_i2 rs.contags_env p1 = (c,exh,p)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    first_assum (mp_tac o (MATCH_MP (
      CONV_RULE (
        ONCE_REWRITE_CONV[CONJ_ASSOC] THENC
        ONCE_REWRITE_CONV[CONJ_COMM] THENC
        ONCE_REWRITE_CONV[GSYM CONJ_ASSOC] THENC
        ONCE_REWRITE_CONV[GSYM AND_IMP_INTRO]) prompt_to_i2_correct))) >>
    REWRITE_TAC[Once EQ_SYM_EQ] >>
    REWRITE_TAC[Once (GSYM CONJ_ASSOC)] >>
    REWRITE_TAC[Once (GSYM AND_IMP_INTRO)] >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    REWRITE_TAC[Once (GSYM AND_IMP_INTRO)] >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    simp[] >>
    discharge_hyps >- (
      fs[result_to_i1_cases] >> fs[] >>
      fs[top_to_i1_def,LET_THM,UNCURRY] >>
      rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
      MATCH_ACCEPT_TAC mod_decs_decs_to_i1) >>
    disch_then(qx_choosel_then[`new_genv_i2`,`s2_i2`,`res_i2`,`gtagenv2`]strip_assume_tac) >>
    `∃n e. prompt_to_i3 non som (LENGTH grd0) p = (n,e)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    first_assum (mp_tac o (MATCH_MP (
      ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
        prompt_to_i3_correct))) >>
    simp[] >>
    `LENGTH genv2 = LENGTH grd0` by (
      fs[to_i2_invariant_def] >>
      imp_res_tac EVERY2_LENGTH >>
      fs[] ) >>
    simp[] >>
    simp[Once result_to_i3_cases] >>
    discharge_hyps >- (
      fs[result_to_i2_cases,result_to_i1_cases] >> fs[] ) >>
    reverse strip_tac >- (
      fs[result_to_i2_cases,result_to_i1_cases] >> fs[] ) >>
    first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_exh_correct)) >>
    simp[] >> simp[env_to_exh_MAP] >>
    qmatch_assum_rename_tac`csg_rel (v_to_exh rs.exh) ((s10,s20),genv2) csgh` >>
    `store_to_exh (exh ⊌ rs.exh) ((s10,s20),genv2) csgh` by tac1 >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    simp[Once result_to_exh_cases] >>
    disch_then(qspec_then`exh ⊌ rs.exh`mp_tac) >> simp[] >>
    strip_tac >>
    first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_pat_correct)) >>
    simp[] >>
    disch_then(qx_choosel_then[`res3`]strip_assume_tac) >>
    first_assum (qspec_then`[]`mp_tac o MATCH_MP (CONJUNCT1 evaluate_pat_exp_pat)) >>
    Q.PAT_ABBREV_TAC`ep = exp_to_pat X Y` >>
    disch_then(qspecl_then[`sp`,`ep`]mp_tac) >>
    discharge_hyps >- (
      simp[CONJUNCT1 exp_pat_refl] >> fs[csg_to_pat_MAP] ) >>
    disch_then(qx_choosel_then[`res4`]strip_assume_tac) >>
    ntac 3 (first_assum(split_applied_pair_tac o lhs o concl) >> fs[]) >>
    tac12 >> tac7 >>
    first_x_assum(qspec_then`bs2`mp_tac) >>
    simp[Abbr`bs2`,bvl_to_bc_value_def,Abbr`som`] >>
    disch_then(qspec_then`some_tag+1`mp_tac)>>simp[] >>
    qmatch_assum_rename_tac`state_rel f2 t5 t6` >>
    `some_tag ≠ none_tag` by EVAL_TAC >> simp[] >>
    ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
    discharge_hyps_keep >- tac8 >>
    qmatch_assum_abbrev_tac`bc_next bs bs1` >>
    qmatch_assum_abbrev_tac`bc_next^* bs1' bs5` >>
    discharge_hyps >- (
      rpt BasicProvers.VAR_EQ_TAC >>
      metis_tac[can_print] ) >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs5' bs2'` >>
    `bs5' = bs5` by (
      simp[Abbr`bs5`,Abbr`bs5'`,bvl_to_bc_value_def]) >>
    `bc_next^* bs1' bs2'` by metis_tac[RTC_TRANSITIVE,transitive_def] >>
    pop_assum(mp_tac o MATCH_MP RTC_bc_next_prepend_output) >>
    disch_then(qspec_then`bs.output`assume_tac) >>
    qmatch_assum_abbrev_tac`bc_next^* bs1'' bs2` >>
    `bs1'' = bs1` by (
      simp[Abbr`bs1''`,Abbr`bs1'`,Abbr`bs1`,bc_state_component_equality] >>
      fs[clos_to_bvlTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_numberTheory.state_rel_def,s_to_Cs_unpair] ) >>
    qexists_tac`bs2` >>
    simp[RIGHT_EXISTS_AND_THM] >>
    conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
    Cases_on`err`>>fs[] >>
    simp[RIGHT_EXISTS_AND_THM] >>
    conj_tac >- (
      fs[Abbr`bs2`,bc_fetch_with_output] ) >>
    conj_tac >- tac9 >>
    PairCases_on`s2` >> simp[env_rs_def,Once EXISTS_PROD] >>
    simp[RIGHT_EXISTS_AND_THM] >>
    conj_asm1_tac >- tac10 >>
    qexists_tac`grd0 ++ new_genv` >>
    tac11) >>
  strip_tac >- simp[] >>
  simp[])

val compile_top_divergence = store_thm("compile_top_divergence",
  ``∀env stm top rs grd types bc0 bs ss sf code.
      (∀res. ¬evaluate_top F env stm top res) ∧
      env_rs env stm grd rs (bs with code := bc0) ∧
      (compile_top types rs top = (ss,sf,code)) ∧
      bs.code = bc0 ++ REVERSE code ∧
      bs.pc = next_addr bs.inst_length bc0 ∧
      IS_SOME bs.clock
      ⇒
      ∃bs'. bc_next^* bs bs' ∧ bc_fetch bs' = SOME Tick ∧ bs'.clock = SOME 0 ∧ bs'.output = bs.output``,
  rw[] >>
  imp_res_tac not_evaluate_top_timeout >>
  fs[compile_top_def,LET_THM] >>
  rpt(first_assum (split_applied_pair_tac o lhs o concl) >> fs[]) >>
  PairCases_on`env` >>
  PairCases_on`stm` >>
  PairCases_on`r` >>
  (top_to_i1_correct
   |> CONV_RULE
     ((lift_conjunct_conv(equal``evaluate_top`` o fst o strip_comb))
      |> LAND_CONV |> STRIP_QUANT_CONV)
   |> ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO]
   |> (fn th => first_assum (mp_tac o MATCH_MP th))) >>
  fs[] >>
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  PairCases_on`grd`>>fs[env_rs_def] >> rfs[] >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  strip_tac >>
  (prompt_to_i2_correct
   |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
   |> (fn th => first_assum (mp_tac o MATCH_MP th))) >>
  fs[result_to_i1_cases] >>
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  ONCE_REWRITE_TAC[EQ_SYM_EQ] >>
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  strip_tac >>
  (prompt_to_i3_correct
   |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
   |> (fn th => first_assum (mp_tac o MATCH_MP th))) >>
  fs[result_to_i2_cases] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp[] >>
  ONCE_REWRITE_TAC[EQ_SYM_EQ] >>
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  `LENGTH genv2 = LENGTH grd0` by (
    fs[to_i2_invariant_def] >>
    imp_res_tac EVERY2_LENGTH >>
    fs[] ) >>
  simp[] >>
  strip_tac >>
  (exp_to_exh_correct
   |> CONJUNCT1
   |> (fn th => first_assum (mp_tac o MATCH_MP th))) >>
  fs[result_to_i3_cases] >>
  simp[env_to_exh_MAP] >>
  qmatch_assum_rename_tac`csg_rel (v_to_exh rs.exh) ((s10,s20),genv2) csgh` >>
  `store_to_exh (exh ⊌ rs.exh) ((s10,s20),genv2) csgh` by tac1 >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
  simp[Once result_to_exh_cases] >>
  disch_then(qspec_then`exh ⊌ rs.exh`mp_tac) >> simp[] >>
  strip_tac >>
  first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_pat_correct)) >>
  simp[] >>
  disch_then(qx_choosel_then[`res3`]strip_assume_tac) >>
  first_assum (qspec_then`[]`mp_tac o MATCH_MP (CONJUNCT1 evaluate_pat_exp_pat)) >>
  Q.PAT_ABBREV_TAC`ep = exp_to_pat X Y` >>
  disch_then(qspecl_then[`sp`,`ep`]mp_tac) >>
  discharge_hyps >- (
    simp[CONJUNCT1 exp_pat_refl] >> fs[csg_to_pat_MAP] ) >>
  disch_then(qx_choosel_then[`res4`]strip_assume_tac) >>
  tac12 >>
  qmatch_assum_abbrev_tac`bc_next bs bs1` >>
  qmatch_assum_abbrev_tac`bc_next^* bs1' bs2` >>
  first_x_assum(mp_tac o MATCH_MP RTC_bc_next_prepend_output) >>
  disch_then(qspec_then`bs.output`assume_tac) >>
  qmatch_assum_abbrev_tac`bc_next^* bs1'' bs2'` >>
  `bs1'' = bs1` by (
    simp[Abbr`bs1''`,Abbr`bs1'`,Abbr`bs1`,bc_state_component_equality] >>
    fs[clos_to_bvlTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_numberTheory.state_rel_def,s_to_Cs_unpair] ) >>
  qexists_tac`bs2'` >>
  conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
  simp[Abbr`bs2'`,bc_fetch_with_output] >>
  fs[clos_to_bvlTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_numberTheory.state_rel_def,s_to_Cs_unpair] )

(* compile_prog *)

val compile_prog_thm = store_thm("compile_prog_thm",
  ``∀ck env stm prog res. evaluate_whole_prog ck env stm prog res ⇒
     ∀grd rs rss rsf bc bs bc0.
      FLOOKUP rs.exh (Short "option") = SOME (insert some_tag () (insert none_tag () LN)) ∧
      env_rs env stm grd rs (bs with code := bc0) ∧
      (∀p. "it" ∈ FDOM (FST(SND(SND(prog_to_i1 rs.next_global (FST rs.globals_env) (SND rs.globals_env) prog)))) ∧
           SND(SND(res)) = Rval p ⇒ ∃v. ALOOKUP (SND p) "it" = SOME v ∧ (∀w. v ≠ Litv (Word8 w)) ∧ (∀c. v ≠ Litv (Char c))) ∧
      (∀v. SND(SND(res)) = Rerr(Rraise v) ⇒ ∀l. v ≠ Litv l) ∧
      (bs.code = bc0 ++ compile_prog rs prog) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      ck ∧ IS_SOME bs.clock ∧
      SND(SND res) ≠ Rerr Rtype_error ∧
      SND(SND res) ≠ Rerr Rtimeout_error
      ⇒
      case res of (s,envC,env_or_err) =>
        ∃bs' grd'.
        bc_next^* bs bs' ∧
        let (success,str) =
          case env_or_err of Rval(envM,envE) =>
            (T,(case ALOOKUP envE "it" of NONE => "" | SOME v => (print_v v)++"\n"))
          | Rerr(Rraise v) =>
            (F,"raise "++(print_v v)++"\n") in
        bc_fetch bs' = SOME (Stop success) ∧
        bs'.output = bs.output ++ str``,
  simp[compile_prog_def] >> rw[] >>
  first_assum (split_applied_pair_tac o rand o rhs o concl) >> fs[] >>
  `∃v1 v2 v3 p0. prog_to_i1 rs.next_global m1 m2 prog = (v1,v2,v3,p0)` by simp[GSYM EXISTS_PROD] >> fs[] >>
  `∃v exh p. prog_to_i2 rs.contags_env p0 = (v,exh,p)` by simp[GSYM EXISTS_PROD] >> fs[] >>
  rpt(first_assum (split_applied_pair_tac o rand o rhs o concl) >> fs[]) >>
  `∃s envC env_or_err. res = (s,envC,env_or_err)` by metis_tac[PAIR] >> fs[] >>
  PairCases_on`s` >>
  PairCases_on`stm` >> PairCases_on`env` >>
  (whole_prog_to_i1_correct
   |> ONCE_REWRITE_RULE[CONJ_COMM]
   |> ONCE_REWRITE_RULE[GSYM CONJ_ASSOC]
   |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
   |> (fn th => first_assum (mp_tac o MATCH_MP th))) >>
  ONCE_REWRITE_TAC[GSYM CONJ_ASSOC] >>
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  PairCases_on`grd` >> fs[env_rs_def] >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  qpat_assum`X = LENGTH grd0`(assume_tac o SYM) >> fs[] >>
  strip_tac >>
  (whole_prog_to_i2_correct
   |> ONCE_REWRITE_RULE[GSYM CONJ_ASSOC]
   |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
   |> (fn th => first_assum (mp_tac o MATCH_MP th))) >>
  simp[] >>
  ONCE_REWRITE_TAC[CONJ_COMM] >>
  ONCE_REWRITE_TAC[GSYM CONJ_ASSOC] >>
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  `∃x y z. rs.contags_env = (x,y,z)` by metis_tac[pair_CASES] >> fs[] >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  pop_assum(assume_tac o SYM) >> fs[] >>
  pop_assum kall_tac >>
  PairCases_on`v`>>simp[] >>
  discharge_hyps >- (
    Cases_on`env_or_err`>>TRY(PairCases_on`a`)>>fs[result_to_i1_cases] >> rw[] ) >>
  strip_tac >>
  (prog_to_i3_correct
   |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
   |> (fn th => first_assum (mp_tac o MATCH_MP th))) >>
  `LENGTH genv2 = LENGTH grd0` by (
    fs[to_i2_invariant_def] >>
    imp_res_tac EVERY2_LENGTH >>
    fs[] ) >>
  simp[] >>
  (discharge_hyps >- (
     simp[alistTheory.flookup_fupdate_list,FLOOKUP_FUNION] >>
     Cases_on`env_or_err`>>fs[GSYM FORALL_PROD] >>
     TRY (conj_tac >- (fs[result_to_i2_cases,result_to_i1_cases] >> rw[])) >>
     BasicProvers.CASE_TAC >>
     fs[IN_DISJOINT,FLOOKUP_DEF] >>
     fs[FDOM_FUPDATE_LIST] >> metis_tac[])) >>
  simp[result_to_i3_cases] >- (
    rw[] >> Cases_on`env_or_err` >> fs[] >>
    PairCases_on`a`>>fs[]>>
    first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_exh_correct)) >>
    simp[env_to_exh_MAP] >>
    qmatch_assum_rename_tac`csg_rel (v_to_exh rs.exh) ((s10,s20),genv2) csgh` >>
    `store_to_exh (exh ⊌ rs.exh) ((s10,s20),genv2) csgh` by tac1 >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    simp[Once result_to_exh_cases] >>
    disch_then(qspec_then`exh ⊌ rs.exh`mp_tac) >> simp[] >>
    strip_tac >>
    first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_pat_correct)) >>
    simp[] >>
    disch_then(qx_choosel_then[`res3`]strip_assume_tac) >>
    first_assum (qspec_then`[]`mp_tac o MATCH_MP (CONJUNCT1 evaluate_pat_exp_pat)) >>
    Q.PAT_ABBREV_TAC`ep = exp_to_pat X Y` >>
    disch_then(qspecl_then[`sp`,`ep`]mp_tac) >>
    discharge_hyps >- (
      simp[CONJUNCT1 exp_pat_refl] >> fs[csg_to_pat_MAP] ) >>
    disch_then(qx_choosel_then[`res4`]strip_assume_tac) >>
    tac12 >> tac7 >>
    first_x_assum(qspec_then`bs2 with code := bc0 ++ REVERSE r.out ++ REVERSE bc ++ code`mp_tac) >>
    simp[] >>
    simp[Abbr`bs2`,bvl_to_bc_value_def] >>
    disch_then(qspec_then`none_tag+1`mp_tac)>>simp[]>>
    qmatch_assum_rename_tac`state_rel f2 t5 t6` >>
    discharge_hyps_keep >- tac8 >>
    qmatch_assum_abbrev_tac`bc_next bs bs1` >>
    qmatch_assum_abbrev_tac`bc_next^* bs1' bs5` >>
    `∃ccode3. ccode2 = code ++ ccode3` by (
      qpat_assum`REVERSE X = Y`mp_tac >>
      BasicProvers.CASE_TAC >> simp[emit_def] >> rw[] >> simp[] ) >>
    disch_then(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]RTC_bc_next_append_code)) >>
    disch_then(qspec_then`ccode3`mp_tac o CONV_RULE(RESORT_FORALL_CONV(List.rev))) >> simp[] >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs5' bs2'` >>
    `bs5' = bs5` by (
      simp[Abbr`bs5`,Abbr`bs5'`,bvl_to_bc_value_def] >>
      simp[bc_state_component_equality]) >>
    `bc_next^* bs1' bs2'` by metis_tac[RTC_TRANSITIVE,transitive_def] >>
    pop_assum(mp_tac o MATCH_MP RTC_bc_next_prepend_output) >>
    disch_then(qspec_then`bs.output`assume_tac) >>
    qmatch_assum_abbrev_tac`bc_next^* bs1'' bs2` >>
    `bs1'' = bs1` by (
      simp[Abbr`bs1''`,Abbr`bs1'`,Abbr`bs1`,bc_state_component_equality] >>
      fs[clos_to_bvlTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_numberTheory.state_rel_def,s_to_Cs_unpair] ) >>
    BasicProvers.CASE_TAC >> simp[] >- (
      qexists_tac`bs2` >>
      reverse conj_tac >- (
        reverse conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
        simp[Abbr`bs2`,Abbr`bs2'`] >>
        fs[clos_to_bvlTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_numberTheory.state_rel_def,s_to_Cs_unpair] ) >>
      simp[Abbr`bs2`,bc_fetch_with_output] >>
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs2'`] >>
      qexists_tac`bc0 ++ REVERSE r.out ++ REVERSE bc ++ code` >>
      simp[] >>
      qpat_assum`REVERSE X = Y`mp_tac >>
      BasicProvers.CASE_TAC >> simp[emit_def] >> rw[] >> simp[] >>
      rator_x_assum`to_i1_invariant`mp_tac >>
      simp[to_i1_invariant_def] >>
      CCONTR_TAC >> fs[] >>
      imp_res_tac global_env_inv_inclusion >>
      fs[FLOOKUP_DEF,SUBSET_DEF, MEM_MAP]) >>
    rator_x_assum`to_i1_invariant`mp_tac >>
    simp[to_i1_invariant_def] >> strip_tac >>
    rator_x_assum`global_env_inv`mp_tac >>
    simp[Once v_to_i1_cases] >> strip_tac >>
    rator_x_assum`global_env_inv_flat`mp_tac >>
    simp[Once v_to_i1_cases] >>
    disch_then(qspec_then`"it"`mp_tac) >>
    simp[ALOOKUP_APPEND] >> strip_tac >>
    qpat_assum`REVERSE X = Y`mp_tac >>
    simp[emit_def] >> strip_tac >>
    `bc_fetch bs2 = SOME (Gread n)` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs2`,Abbr`bs2'`] >>
      qexists_tac`bc0++REVERSE r.out++REVERSE bc++code` >>
      simp[] >> rw[] ) >>
    srw_tac[DNF_ss][Once RTC_CASES_RTC_TWICE] >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`bs2` >>
    `bc_next^* bs bs2` by metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
    simp[] >>
    srw_tac[DNF_ss][Once RTC_CASES1] >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    rator_x_assum`to_i2_invariant`mp_tac >>
    simp[to_i2_invariant_def] >> strip_tac >>
    rfs[EVERY2_EVERY] >> fs[EVERY_MEM] >>
    qpat_assum`LENGTH genv2 = X`assume_tac >>
    qpat_assum`LENGTH grd0 = X`assume_tac >>
    fs[MEM_ZIP,PULL_EXISTS] >>
    first_x_assum(qspec_then`n`mp_tac) >>
    simp[optionTheory.OPTREL_def] >> strip_tac >>
    rator_x_assum`store_to_exh`mp_tac >>
    simp[store_to_exh_csg_rel,csg_rel_unpair] >>
    strip_tac >>
    rfs[EVERY2_EVERY] >> fs[EVERY_MEM] >>
    qpat_assum`LENGTH genv2 = X`assume_tac >>
    fsrw_tac[ARITH_ss][MEM_ZIP,PULL_EXISTS] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP th)) >>
    simp[optionTheory.OPTREL_def] >> strip_tac >>
    ntac 2 (rator_x_assum`csg_rel`mp_tac) >>
    simp[csg_rel_unpair] >> rpt strip_tac >>
    rfs[EVERY2_EVERY] >> fs[EVERY_MEM,map_count_store_genv_def] >>
    fs[MEM_ZIP,PULL_EXISTS] >>
    last_x_assum(fn th => first_assum(mp_tac o MATCH_MP th)) >>
    simp[EL_MAP,optionTheory.OPTREL_def] >> strip_tac >>
    last_x_assum(fn th => first_assum(mp_tac o MATCH_MP th)) >>
    simp[EL_MAP,optionTheory.OPTREL_def] >> strip_tac >>
    rator_x_assum`clos_number$state_rel`mp_tac >>
    simp[s_to_Cs_unpair] >>
    CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[clos_numberTheory.state_rel_def,LIST_REL_EL_EQN])) >>
    strip_tac >>
    last_x_assum(fn th => first_assum(mp_tac o MATCH_MP th)) >>
    qpat_assum`"" = X`(assume_tac o SYM) >>
    simp[EL_MAP,optionTheory.OPTREL_def] >> strip_tac >>
    fs[] >>
    rator_x_assum`clos_annotate$state_rel`mp_tac >>
    CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[clos_annotateTheory.state_rel_def,LIST_REL_EL_EQN])) >>
    strip_tac >>
    last_x_assum(fn th => first_assum(mp_tac o MATCH_MP th)) >>
    simp[optionTheory.OPTREL_def] >> strip_tac >>
    fs[] >>
    rator_x_assum`clos_to_bvl$state_rel`mp_tac >>
    CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[clos_to_bvlTheory.state_rel_def,LIST_REL_EL_EQN])) >>
    strip_tac >>
    last_x_assum(fn th => first_assum(mp_tac o MATCH_MP th)) >>
    simp[opt_val_rel_elim,optionTheory.OPTREL_def] >> strip_tac >>
    simp[Abbr`bs2`,Abbr`bs2'`,EL_MAP] >>
    Q.PAT_ABBREV_TAC`bs2:bc_state = X Y` >>
    `bc_fetch bs2 = SOME Print` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs2`] >>
      qexists_tac`bc0++REVERSE r.out++REVERSE bc++code++[Gread n]` >>
      simp[SUM_APPEND,FILTER_APPEND] ) >>
    srw_tac[DNF_ss][Once RTC_CASES1] >>
    simp[Once bc_eval1_thm] >> simp[bc_eval1_def,bump_pc_def] >>
    simp[Abbr`bs2`,PULL_EXISTS] >>
    Q.PAT_ABBREV_TAC`sss = bv_to_string X` >>
    `∃str. sss = SOME str` by (
      metis_tac[can_print,IS_SOME_EXISTS] ) >>
    simp[Abbr`sss`] >>
    Q.PAT_ABBREV_TAC`bs2:bc_state = X Y` >>
    `bc_fetch bs2 = SOME (PrintC #"\n")` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs2`] >>
      qexists_tac`bc0++REVERSE r.out++REVERSE bc++code++[Gread n;Print]` >>
      simp[SUM_APPEND,FILTER_APPEND] ) >>
    srw_tac[DNF_ss][Once RTC_CASES1] >>
    simp[Once bc_eval1_thm] >> simp[bc_eval1_def,bump_pc_def] >>
    simp[Abbr`bs2`,IMPLODE_EXPLODE_I] >>
    Q.PAT_ABBREV_TAC`bs2:bc_state = X Y` >>
    qexists_tac`bs2`>>simp[] >>
    conj_tac >- (
      match_mp_tac bc_fetch_next_addr >> simp[] >>
      CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`[]` >>
      simp[Abbr`bs2`,SUM_APPEND,FILTER_APPEND] ) >>
    qmatch_assum_abbrev_tac`bv_to_string bv = SOME str` >>
    `str = print_bv (Infer_Tuvar 0) bv` by simp[print_bv_def] >>
    simp[Abbr`bs2`] >>
    `t6.output = ""` by (
      fs[clos_to_bvlTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_numberTheory.state_rel_def,s_to_Cs_unpair] ) >>
    simp[Abbr`bv`] >>
    match_mp_tac (MP_CANON print_bv_print_v) >>
    simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    imp_res_tac v_pat_trans >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    fs[FLOOKUP_DEF] ) >>
  Cases_on`env_or_err`>>
  fs[result_to_i2_cases,result_to_i1_cases,GSYM FORALL_PROD] >>
  fs[] >> rw[] >>
  first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_exh_correct)) >>
  simp[env_to_exh_MAP] >>
  qmatch_assum_rename_tac`csg_rel (v_to_exh rs.exh) ((s10,s20),genv2) csgh` >>
  `store_to_exh (exh ⊌ rs.exh) ((s10,s20),genv2) csgh` by tac1 >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
  simp[Once result_to_exh_cases] >>
  disch_then(qspec_then`exh ⊌ rs.exh`mp_tac) >> simp[] >>
  strip_tac >>
  first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_pat_correct)) >>
  simp[] >>
  disch_then(qx_choosel_then[`res3`]strip_assume_tac) >>
  first_assum (qspec_then`[]`mp_tac o MATCH_MP (CONJUNCT1 evaluate_pat_exp_pat)) >>
  Q.PAT_ABBREV_TAC`ep = exp_to_pat X Y` >>
  disch_then(qspecl_then[`sp`,`ep`]mp_tac) >>
  discharge_hyps >- (
    simp[CONJUNCT1 exp_pat_refl] >> fs[csg_to_pat_MAP] ) >>
  disch_then(qx_choosel_then[`res4`]strip_assume_tac) >>
  tac12 >> tac7 >>
  first_x_assum(qspec_then`bs2 with code := bc0 ++ REVERSE r.out ++ REVERSE bc ++ code`mp_tac) >>
  simp[] >>
  simp[Abbr`bs2`,bvl_to_bc_value_def] >>
  disch_then(qspec_then`some_tag+1`mp_tac)>>simp[]>>
  qmatch_assum_rename_tac`state_rel f2 t5 t6` >>
  `some_tag ≠ none_tag` by EVAL_TAC >> simp[] >>
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  discharge_hyps_keep >- tac8 >>
  qmatch_assum_abbrev_tac`bc_next bs bs1` >>
  qmatch_assum_abbrev_tac`bc_next^* bs1' bs5` >>
  discharge_hyps >- (
    rpt BasicProvers.VAR_EQ_TAC >>
    metis_tac[can_print] ) >>
  strip_tac >>
  `∃ccode3. ccode2 = code ++ ccode3` by (
    qpat_assum`REVERSE X = Y`mp_tac >>
    BasicProvers.CASE_TAC >> simp[emit_def] >> rw[] >> simp[] ) >>
  first_x_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]RTC_bc_next_append_code)) >>
  disch_then(qspec_then`ccode3`mp_tac o CONV_RULE(RESORT_FORALL_CONV(List.rev))) >> simp[] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs5' bs2'` >>
  `bs5' = bs5` by (
    simp[Abbr`bs5`,Abbr`bs5'`,bvl_to_bc_value_def] >>
    simp[bc_state_component_equality]) >>
  `bc_next^* bs1' bs2'` by metis_tac[RTC_TRANSITIVE,transitive_def] >>
  pop_assum(mp_tac o MATCH_MP RTC_bc_next_prepend_output) >>
  disch_then(qspec_then`bs.output`assume_tac) >>
  qmatch_assum_abbrev_tac`bc_next^* bs1'' bs2` >>
  `bs1'' = bs1` by (
    simp[Abbr`bs1''`,Abbr`bs1'`,Abbr`bs1`,bc_state_component_equality] >>
    fs[clos_to_bvlTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_numberTheory.state_rel_def,s_to_Cs_unpair] ) >>
  qexists_tac`bs2` >>
  conj_tac >- (
    simp[Abbr`bs2`,bc_fetch_with_output] >> fs[] >>
    imp_res_tac bc_fetch_append_code >>
    first_x_assum(qspec_then`ccode3`mp_tac) >>
    simp[] ) >>
  conj_tac >- (
    simp[Abbr`bs2`,Abbr`bs2'`] >>
    `t6.output = ""` by (
      fs[clos_to_bvlTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_numberTheory.state_rel_def,s_to_Cs_unpair] ) >>
    Q.PAT_ABBREV_TAC`str = bv_to_string X` >>
    `∃s. str = SOME s` by metis_tac[can_print,IS_SOME_EXISTS] >>
    simp[Abbr`str`] >>
    qmatch_assum_abbrev_tac`bv_to_string bv = SOME str` >>
    `str = print_bv (Infer_Tuvar 0) bv` by simp[print_bv_def] >>
    simp[Abbr`bv`] >>
    match_mp_tac (MP_CANON print_bv_print_v) >>
    simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    imp_res_tac v_pat_trans >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] ) >>
  metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET])

val compile_prog_divergence = store_thm("compile_prog_divergence",
  ``∀env stm prog rs grd types bc0 bs.
      (∀res. ¬evaluate_whole_prog F env stm prog res) ∧
      FLOOKUP rs.exh (Short "option") = SOME (insert some_tag () (insert none_tag () LN)) ∧
      env_rs env stm grd rs (bs with code := bc0) ∧
      bs.code = bc0 ++ compile_prog rs prog ∧
      bs.pc = next_addr bs.inst_length bc0 ∧
      IS_SOME bs.clock
      ⇒
      ∃bs'. bc_next^* bs bs' ∧ bc_fetch bs' = SOME Tick ∧ bs'.clock = SOME 0 ∧ bs'.output = bs.output``,
  rw[] >>
  imp_res_tac not_evaluate_whole_prog_timeout >>
  fs[compile_prog_def,LET_THM] >>
  first_assum (split_applied_pair_tac o rand o rhs o concl) >> fs[] >>
  `∃v1 v2 v3 p0. prog_to_i1 rs.next_global m1 m2 prog = (v1,v2,v3,p0)` by simp[GSYM EXISTS_PROD] >> fs[] >>
  `∃v exh p. prog_to_i2 rs.contags_env p0 = (v,exh,p)` by simp[GSYM EXISTS_PROD] >> fs[] >>
  first_assum (split_applied_pair_tac o rand o rhs o concl) >> fs[] >>
  first_assum (split_applied_pair_tac o rand o rhs o concl) >> fs[] >>
  first_assum (split_applied_pair_tac o rand o rhs o concl) >> fs[] >>
  first_assum (split_applied_pair_tac o rand o rhs o concl) >> fs[] >>
  PairCases_on`env` >>
  PairCases_on`stm` >>
  PairCases_on`r` >>
  (whole_prog_to_i1_correct
   |> CONV_RULE
     ((lift_conjunct_conv(equal``evaluate_whole_prog`` o fst o strip_comb))
      |> LAND_CONV |> STRIP_QUANT_CONV)
   |> ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO]
   |> (fn th => first_assum (mp_tac o MATCH_MP th))) >>
  fs[] >>
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  PairCases_on`grd`>>fs[env_rs_def] >> rfs[] >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  strip_tac >>
  (whole_prog_to_i2_correct
   |> CONV_RULE
     ((lift_conjunct_conv(equal``evaluate_whole_prog_i1`` o fst o strip_comb))
      |> LAND_CONV |> STRIP_QUANT_CONV)
   |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
   |> (fn th => first_assum (mp_tac o MATCH_MP th))) >>
  fs[result_to_i1_cases] >>
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  `∃x y z. rs.contags_env = (x,y,z)` by metis_tac[pair_CASES] >> fs[] >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  pop_assum(assume_tac o SYM) >> fs[] >>
  pop_assum kall_tac >>
  PairCases_on`v`>>simp[]>>
  strip_tac >>
  (prog_to_i3_correct
   |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
   |> (fn th => first_assum (mp_tac o MATCH_MP th))) >>
  fs[result_to_i2_cases] >>
  simp[FLOOKUP_UPDATE,FLOOKUP_FUNION] >>
  reverse BasicProvers.CASE_TAC >- (
    fs[IN_DISJOINT,FLOOKUP_DEF,FDOM_FUPDATE_LIST] >>
    metis_tac[]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  `LENGTH genv2 = LENGTH grd0` by (
    fs[to_i2_invariant_def] >>
    imp_res_tac EVERY2_LENGTH >>
    fs[] ) >>
  simp[] >>
  strip_tac >>
  (exp_to_exh_correct
   |> CONJUNCT1
   |> (fn th => first_assum (mp_tac o MATCH_MP th))) >>
  fs[result_to_i3_cases] >>
  simp[env_to_exh_MAP] >>
  qmatch_assum_rename_tac`csg_rel (v_to_exh rs.exh) ((s10,s20),genv2) csgh` >>
  `store_to_exh (exh ⊌ rs.exh) ((s10,s20),genv2) csgh` by tac1 >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
  simp[Once result_to_exh_cases] >>
  disch_then(qspec_then`exh ⊌ rs.exh`mp_tac) >> simp[] >>
  strip_tac >>
  first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_pat_correct)) >>
  simp[] >>
  disch_then(qx_choosel_then[`res3`]strip_assume_tac) >>
  first_assum (qspec_then`[]`mp_tac o MATCH_MP (CONJUNCT1 evaluate_pat_exp_pat)) >>
  Q.PAT_ABBREV_TAC`ep = exp_to_pat X Y` >>
  disch_then(qspecl_then[`sp`,`ep`]mp_tac) >>
  discharge_hyps >- (
    simp[CONJUNCT1 exp_pat_refl] >> fs[csg_to_pat_MAP] ) >>
  disch_then(qx_choosel_then[`res4`]strip_assume_tac) >>
  tac12 >>
  qmatch_assum_abbrev_tac`bc_next bs bs1` >>
  qmatch_assum_abbrev_tac`bc_next^* bs1' bs2` >>
  first_x_assum(mp_tac o MATCH_MP RTC_bc_next_prepend_output) >>
  disch_then(qspec_then`bs.output`assume_tac) >>
  qmatch_assum_abbrev_tac`bc_next^* bs1'' bs2'` >>
  `bs1'' = bs1` by (
    simp[Abbr`bs1''`,Abbr`bs1'`,Abbr`bs1`,bc_state_component_equality] >>
    fs[clos_to_bvlTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_numberTheory.state_rel_def,s_to_Cs_unpair] ) >>
  qexists_tac`bs2'` >>
  conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
  simp[Abbr`bs2'`,bc_fetch_with_output] >>
  fs[clos_to_bvlTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_numberTheory.state_rel_def,s_to_Cs_unpair] )

(*
val compile_Cexp_code_ok_thm = prove(
  ``∀renv rsz cs exp cs'.
    (compile_Cexp renv rsz cs exp = cs') ⇒
    set (free_vars exp) ⊆ count (LENGTH renv) ∧
    no_labs exp ∧ (cs.out = []) ⇒
    code_labels_ok (local_labels cs'.out)``,
  rw[] >>
  qspecl_then[`renv`,`rsz`,`cs`,`exp`]mp_tac compile_Cexp_thm >>
  simp[] >> strip_tac >> simp[] >>
  PROVE_TAC[REVERSE_APPEND,code_labels_ok_REVERSE])

(* TODO: fix?

val compile_print_err_code_ok_thm = prove(
  ``∀cs cs'. (compile_print_err cs = cs') ⇒
             code_labels_ok cs.out ⇒
             code_labels_ok cs'.out``,
  rw[] >>
  qspec_then`cs`mp_tac compile_print_err_thm >>
  simp[] >> strip_tac >> simp[] >>
  match_mp_tac code_labels_ok_append >>
  simp[code_labels_ok_REVERSE])

val compile_prog_code_labels_ok = store_thm("compile_prog_code_labels_ok",
  ``∀prog code.
      (compile_prog prog = code) ∧ closed_prog prog ⇒
      code_labels_ok code``,
    rw[compile_prog_def] >>
    `∃a b c d. prog_to_i1 n m1 m2 prog = (a,b,c,d)` by simp[GSYM EXISTS_PROD] >>simp[] >>
    `∃e f g. prog_to_i2 init_compiler_state.contags_env d = (e,f,g)` by simp[GSYM EXISTS_PROD] >>simp[] >>
    (fn(g as (_,w)) => split_pair_case_tac (rand w) g) >> simp[] >>
    match_mp_tac code_labels_ok_append >>
    reverse conj_tac >- (match_mp_tac code_labels_ok_cons >> simp[]) >>
    simp[code_labels_ok_REVERSE] >>
    BasicProvers.CASE_TAC >> simp[] >>
    rpt(match_mp_tac code_labels_ok_cons >> simp[]) >>
    match_mp_tac (MP_CANON compile_print_err_code_ok_thm) >>
    (fn(g as (_,w)) => exists_tac (w |> dest_exists |> snd |> dest_conj |> fst |> rhs |> rand) g) >>
    simp[] >>
    match_mp_tac (MP_CANON compile_Cexp_code_ok_thm) >>
    (fn(g as (_,w)) => map_every exists_tac (w |> strip_exists |> snd |> dest_conj |> fst |> rhs |> strip_comb |> snd) g) >>
    simp[] >>
    specl_args_of_then``exp_to_pat``(CONJUNCT1 free_vars_pat_exp_to_pat)mp_tac >>
    simp[] >> disch_then match_mp_tac >>
    imp_res_tac free_vars_i2_prog_to_i3 >>
    imp_res_tac free_vars_prog_to_i2 >>
    imp_res_tac FV_prog_to_i1 >>
    simp[] >>
    fs[closed_prog_def,all_env_dom_def,SUBSET_DEF,PULL_EXISTS])
*)
*)

(* compile_special, for the repl *)

(*
val mod_tagenv_lemma = prove(
  ``mod_tagenv NONE FEMPTY x = x``,
  Cases_on`x`>>simp[mod_tagenv_def,FUNION_FEMPTY_1])

val disjoint_set_lemma = prove(
  ``a = b ∪ a ∧ DISJOINT b a ⇒ b = {}``,
  rw[EXTENSION,IN_DISJOINT] >> metis_tac[])

val lookup_tag_env_NONE = prove(
  ``lookup_tag_env NONE x = (tuple_tag,NONE)``,
  Cases_on`x`>>simp[lookup_tag_env_def])
*)

(* not true because of empty Letrecs
val renumber_code_locs_nil = store_thm("renumber_code_locs_nil",
  ``(∀n xs. clos_number$code_locs xs = [] ⇒ renumber_code_locs_list n xs = (n,xs)) ∧
    (∀n x. clos_number$code_locs [x] = [] ⇒ renumber_code_locs n x = (n,x))``,
  ho_match_mp_tac renumber_code_locs_ind >>
  rpt conj_tac >>
  TRY (
    simp[clos_numberTheory.code_locs_def,renumber_code_locs_def] >>
    rw[] >> fs[Once clos_numberTheory.code_locs_cons] >>
    NO_TAC) >>
  rpt gen_tac >> strip_tac >>
  simp[clos_numberTheory.code_locs_def,GENLIST_eq_nil,LENGTH_NIL] >>
  strip_tac >> fs[] >>
  REWRITE_TAC[renumber_code_locs_def]
*)

val renumber_code_locs_nil = store_thm("renumber_code_locs_nil",
  ``(∀n xs. renumber_code_locs_list n xs = (n,xs) ⇒ code_locs xs = []) ∧
    (∀n x. renumber_code_locs n x = (n,x) ⇒ code_locs [x] = [])``,
  ho_match_mp_tac renumber_code_locs_ind >>
  simp[clos_numberTheory.code_locs_def,renumber_code_locs_def] >>
  rw[] >>
  rpt(first_assum(split_applied_pair_tac o lhs o concl) >> fs[]) >> rw[] >>
  imp_res_tac renumber_code_locs_imp_inc >>
  TRY ( first_x_assum match_mp_tac >> DECIDE_TAC ) >>
  simp[Once clos_numberTheory.code_locs_cons] >>
  simp[UNCURRY,GENLIST_eq_nil] >>
  spose_not_then strip_assume_tac >> fs[] >> rw[] >>
  Cases_on`renumber_code_locs n x` >>
  imp_res_tac renumber_code_locs_imp_inc >>
  fs[] >> DECIDE_TAC)

(*
val cAnnotate_code_locs_nil = store_thm("cAnnotate_code_locs_nil",
  ``∀xs. code_locs xs = [] ⇒ ∀n. cAnnotate n xs = xs``,
  ho_match_mp_tac clos_numberTheory.code_locs_ind >>
  simp[cAnnotate_def,cShift_def,cFree_def,clos_numberTheory.code_locs_def] >>
  rw[get_var_def] >> rw[clos_annotateTheory.tlookup_def,lookup_def] >>
  fs[GENLIST_eq_nil,LENGTH_NIL,cFree_def,
     db_varsTheory.vars_to_list_def,
     db_varsTheory.db_to_set_def,
     db_varsTheory.db_to_set_acc_def,
     toAList_def,foldi_def] >>
  simp[UNCURRY,cShift_def] >>
  f"cfree"
*)

(*
val compile_special_thm = store_thm("compile_special_thm",
  ``∀ck env stm top res. evaluate_top ck env stm top res ⇒
     ∀rs grd bc bc0 bs s0 tm s.
      env_rs env stm grd rs bs ∧
      (compile_special rs top = bc) ∧
      (∀d. top = Tdec d ⇒
            let res =
              decs_to_i2 (rs.contags_env,FEMPTY)
                [SND(SND(dec_to_i1 (LENGTH(FST grd)) NONE (FST rs.globals_env) (SND rs.globals_env) d))] in
            let ep =
              (exp_to_pat []
                (exp_to_exh (FST(SND res) ⊌ rs.exh)
                  (decs_to_i3 (LENGTH (FST grd)) (SND(SND res)))))
           in renumber_code_locs ARB (pComp ep) = (ARB,pComp ep) ∧
              cAnnotate 0 [pComp ep] = [pComp ep]) ∧
      FILTER is_Label bc = [] ∧
      (bs.code = bc0 ++ REVERSE bc) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      ck ∧ IS_SOME bs.clock ∧
      stm = (s0,tm) ∧
      res = ((s,tm), ([],[]), Rval([],[]))
      ⇒
        ∃bs' grd'.
        bc_next^* bs bs' ∧
        bc_fetch bs' = SOME (Stop T) ∧
        bs'.output = bs.output ∧
        bs'.handler = bs.handler ∧
        (EVERY IS_SOME bs.globals ⇒ bs'.globals = bs.globals) ∧
        env_rs env (s,tm) grd' rs bs'``,
  ho_match_mp_tac evaluate_top_ind >> simp[] >>
  simp[compile_special_def] >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `∃m1 m2. rs.globals_env = (m1,m2)` by simp[GSYM EXISTS_PROD] >> fs[] >>
  qspecl_then[`m1`,`m2`,`Tdec d`]mp_tac top_to_i1_correct >>
  fs[] >>
  rpt BasicProvers.VAR_EQ_TAC >> rpt(qpat_assum`T`kall_tac) >>
  PairCases_on`grd`>>PairCases_on`env`>>PairCases_on`s1`>>fs[env_rs_def] >>
  REWRITE_TAC[Once CONJ_COMM] >>
  REWRITE_TAC[Once (GSYM CONJ_ASSOC)] >>
  REWRITE_TAC[Once (GSYM AND_IMP_INTRO)] >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  `∃v w z p1. top_to_i1 rs.next_global m1 m2 (Tdec d) = (v,w,z,p1)` by simp[GSYM EXISTS_PROD] >> fs[] >>
  simp[Once evaluate_top_cases] >>
  simp_tac(srw_ss()++DNF_ss)[] >>
  disch_then(mp_tac o CONJUNCT1) >> rfs[] >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  disch_then(qx_choosel_then[`s2_i1`,`new_genv`]strip_assume_tac) >>
  `∃c exh p. prompt_to_i2 rs.contags_env p1 = (c,exh,p)` by simp[GSYM EXISTS_PROD] >> fs[] >>
  first_assum (mp_tac o (MATCH_MP (
    CONV_RULE (
      ONCE_REWRITE_CONV[CONJ_ASSOC] THENC
      ONCE_REWRITE_CONV[CONJ_COMM] THENC
      ONCE_REWRITE_CONV[GSYM CONJ_ASSOC] THENC
      ONCE_REWRITE_CONV[GSYM AND_IMP_INTRO]) prompt_to_i2_correct))) >>
  REWRITE_TAC[Once EQ_SYM_EQ] >>
  REWRITE_TAC[Once (GSYM CONJ_ASSOC)] >>
  REWRITE_TAC[Once (GSYM AND_IMP_INTRO)] >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  REWRITE_TAC[Once (GSYM AND_IMP_INTRO)] >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  simp[] >>
  disch_then(qx_choosel_then[`new_genv_i2`,`s2_i2`,`gtagenv2`]strip_assume_tac) >>
  Cases_on`p` >>
  fs[evaluate_prompt_i2_cases] >>
  first_x_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO]decs_to_i3_correct)) >>
  `new_dec_vs d = []` by (
    imp_res_tac evaluate_dec_new_dec_vs >> fs[] ) >>
  `num_defs l = 0` by (
    fs[top_to_i1_def,LET_THM] >>
    first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >> rw[] >>
    fs[prompt_to_i2_def,LET_THM] >>
    first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >> rw[] >>
    fs[decs_to_i2_def] >>
    Cases_on`d` >> fs[dec_to_i1_def,LET_THM] >> rw[] >> fs[] >> rw[num_defs_def] >>
    rfs[pat_bindings_def,LENGTH_NIL_SYM,funs_to_i1_MAP,funs_to_i2_MAP] ) >>
  simp[dec_result_to_i3_cases] >>
  strip_tac >>
  first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_exh_correct)) >>
  simp[env_to_exh_MAP,result_to_exh_cases,PULL_EXISTS] >>
  qmatch_assum_rename_tac`csg_rel (v_to_exh rs.exh) ((s10,s20),genv2) csgh` >>
  `store_to_exh (exh ⊌ rs.exh) ((s10,s20),genv2) csgh` by tac1 >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
  simp[Once result_to_exh_cases] >>
  disch_then(qspec_then`exh ⊌ rs.exh`mp_tac) >> simp[] >>
  strip_tac >>
  first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_pat_correct)) >>
  simp[] >>
  disch_then(qx_choosel_then[`res3`]strip_assume_tac) >>
  first_assum (qspec_then`[]`mp_tac o MATCH_MP (CONJUNCT1 evaluate_pat_exp_pat)) >>
  Q.PAT_ABBREV_TAC`ep = exp_to_pat X Y` >>
  disch_then(qspecl_then[`sp`,`ep`]mp_tac) >>
  discharge_hyps >- (
    simp[CONJUNCT1 exp_pat_refl] >> fs[csg_to_pat_MAP] ) >>
  disch_then(qx_choosel_then[`res4`]strip_assume_tac) >>
  first_assum (mp_tac o MATCH_MP (CONJUNCT1 pComp_correct)) >>
  discharge_hyps >- rfs[] >> strip_tac >>
  `LENGTH genv2 = LENGTH grd0` by (
    fs[to_i2_invariant_def] >>
    imp_res_tac EVERY2_LENGTH >>
    fs[] ) >>
  first_x_assum(mp_tac o MATCH_MP renumber_code_locs_correct) >>
  simp[pComp_contains_App_SOME,GSYM csg_to_pat_MAP] >>
  disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
  disch_then(qspec_then`ARB`mp_tac) >>
  simp[renumber_code_locs_def,UNCURRY] >>
  rfs[clos_numberTheory.res_rel_simp,PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >>
  first_assum (mp_tac o MATCH_MP (GEN_ALL(ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] cAnnotate_correct))) >>
  rfs[] >> rfs[] >> fs[clos_numberTheory.res_rel_simp] >>
  disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
  disch_then(qspec_then`[]`mp_tac) >>
  simp[clos_annotateTheory.res_rel_simp,PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  first_assum (mp_tac o MATCH_MP (GEN_ALL(ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] cComp_correct))) >>
  `renumber_code_locs ARB (pComp ep) = (ARB,pComp ep) ∧
   cAnnotate 0 [pComp ep] = [pComp ep]` by (
    fs[prompt_to_i2_def,top_to_i1_def] >>
    Cases_on`p1`>>fs[LET_THM] >>
    first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >>
    first_assum(split_applied_pair_tac o lhs o concl) >> fs[] ) >>
  rfs[] >>
  `code_locs [pComp ep] = []` by (imp_res_tac renumber_code_locs_nil) >>
  disch_then(qspec_then`[]`mp_tac) >> fs[] >>
  Cases_on`cComp [pComp ep] []`>>fs[] >>
  `r = []` by (
    pop_assum mp_tac >>
    `r = r ++ []` by simp[] >>
    pop_assum SUBST1_TAC >> strip_tac >>
    imp_res_tac cComp_code_locs >> rfs[] ) >>
  simp[code_installed_def] >>
  disch_then(qspecl_then[`s6`,`[]`,`f1`]mp_tac) >>
  simp[env_rel_def] >>
  strip_tac >>
  first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO](Q.GENL[`f`]bvl_bc_correct))) >>
  rfs[clos_to_bvlTheory.res_rel_cases] >>
  simp[good_env_def]
  rpt BasicProvers.VAR_EQ_TAC >>
  rpt(qpat_assum`cAnnotate 0 X = Y`kall_tac) >>
  rpt(qpat_assum`renumber_code_locs Z X = Y`kall_tac) >>
  disch_then(qspecl_then[`locs`,`bs with output := s6.output`,`bc0`]mp_tac) >> simp[] >>
  disch_then(qspecl_then[`TCNonTail`,`0`,`<|next_label := rs.rnext_label; out := []|>`]mp_tac o
             CONV_RULE(RESORT_FORALL_CONV(sort_vars["t","sz","cs"]))) >> simp[] >>
  simp[Once SWAP_REVERSE] >>
  specl_args_of_then``bvl_bc``(Q.SPEC`locs`bvl_bc_code_locs) mp_tac >>
  discharge_hyps >- (
    qspecl_then[`[pComp ep]`,`[]`]mp_tac code_locs_cComp >>
    simp[pComp_contains_Call,pComp_contains_App_SOME,pComp_contains_Op_Label] ) >>
  strip_tac >> fs[] >>
  simp[emit_def] >>
  simp[AND_IMP_INTRO] >>
  discharge_hyps >- (
    fs[state_rel_def,good_labels_def,emit_def,FILTER_APPEND,ALL_DISTINCT_APPEND] >>
    rator_x_assum`good_code_env`mp_tac >>
    simp[] >>
    metis_tac[APPEND,APPEND_ASSOC] ) >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs' bs2` >>
  first_x_assum(mp_tac o MATCH_MP RTC_bc_next_prepend_output) >>
  disch_then(qspec_then`bs.output`mp_tac) >> strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs'' bs1` >>
  `bs'' = bs` by (
    simp[Abbr`bs''`,Abbr`bs'`,bc_state_component_equality] >>
    fs[clos_numberTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_to_bvlTheory.state_rel_def,s_to_Cs_unpair] ) >>
  `bs2.inst_length = real_inst_length` by (
    imp_res_tac RTC_bc_next_preserves >> fs[Abbr`bs1`] ) >> fs[] >>
  qpat_assum`bs2 = X`(fn th => assume_tac(EQ_MP (SYM(ISPEC(concl th)markerTheory.Abbrev_def)) th)) >> fs[] >>
  `bc_fetch bs1 = SOME (Stack Pop)` by (
    match_mp_tac bc_fetch_next_addr >>
    simp[Abbr`bs1`,Abbr`bs2`,emit_def] >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`[Stop T]` >> simp[]) >>
  srw_tac[DNF_ss][Once RTC_CASES2] >> disj2_tac >>
  first_assum(match_exists_tac o concl) >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp[Abbr`bs1`,bc_eval_stack_def,Abbr`bs2`,bump_pc_def] >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    match_mp_tac bc_fetch_next_addr >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`[]`>>simp[emit_def] >>
    simp[SUM_APPEND,FILTER_APPEND] ) >>
  conj_tac >- (
    fs[clos_numberTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_to_bvlTheory.state_rel_def,s_to_Cs_unpair] ) >>
  qmatch_assum_rename_tac`state_rel f2 t5 t6` >>
  conj_asm2_tac >- (
tac14
    first_x_assum(strip_assume_tac o MATCH_MP evaluate_prompt_i1_success_globals) >>
    rw[] >>
    imp_res_tac RTC_bc_next_gvrel >>
    fs[gvrel_def,EVERY_MEM,MEM_EL,PULL_EXISTS] >>
    PairCases_on`grd'`>>Cases_on`s2`>>
    fs[env_rs_def] >>
    fs[to_i2_invariant_def,to_i1_invariant_def] >>
    fs[clos_numberTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_to_bvlTheory.state_rel_def,state_rel_def] >>
    fs[LIST_REL_EL_EQN,optionTheory.OPTREL_def,opt_val_rel_elim] >>
    rw[] >>
    Cases_on`n < LENGTH bs.globals` >- metis_tac[IS_SOME_EXISTS] >>
    qpat_assum`MAP X t6.globals = Z`mp_tac >>
    simp[LIST_EQ_REWRITE] >> strip_tac >>
    first_x_assum(qspec_then`n`mp_tac) >> simp[] >>
    disch_then(SUBST1_TAC o SYM) >>
    qpat_assum`∀n. n < LENGTH t5.globals ⇒ Y`(qspec_then`n`mp_tac) >> simp[] >>
    qpat_assum`∀n. n < LENGTH t2.globals ⇒ Y`(qspec_then`n`mp_tac) >> simp[] >>
    qpat_assum`∀n. n < LENGTH (s_to_Cs (FST res4)).globals ⇒ Y`(qspec_then`n`mp_tac) >> simp[] >>
    fs[csg_rel_unpair,s_to_Cs_unpair,store_to_exh_csg_rel,csg_to_pat_MAP,map_count_store_genv_def] >>
    simp[EL_MAP] >>
    qpat_assum`LIST_REL X Y (SND(FST res4))`mp_tac >>
    simp[LIST_REL_EL_EQN] >> strip_tac >>
    first_x_assum(qspec_then`n`mp_tac) >> simp[optionTheory.OPTREL_def,EL_MAP] >>
    qpat_assum`LIST_REL X Y (SND(FST res3))`mp_tac >>
    simp[LIST_REL_EL_EQN] >> strip_tac >>
    first_x_assum(qspec_then`n`mp_tac) >> simp[optionTheory.OPTREL_def,EL_MAP] >>
    qpat_assum`LIST_REL X (genv2++Z) Y`mp_tac >>
    simp[LIST_REL_EL_EQN] >> strip_tac >>
    first_x_assum(qspec_then`n`mp_tac) >> simp[optionTheory.OPTREL_def,EL_MAP] >>
    qpat_assum`∀n. n < LENGTH grd0 + Y ⇒ X`(qspec_then`n`mp_tac) >>
    qpat_assum`X + Z = LENGTH Y`(assume_tac o SYM) >> simp[] >>
    `LENGTH grd0 ≤ n` by (
      imp_res_tac LIST_REL_LENGTH >> fs[] >>
      fs[LIST_EQ_REWRITE] >>
      DECIDE_TAC ) >>
    qpat_assum`∀n. n < LENGTH new_genv ⇒ Y`(qspec_then`n - LENGTH grd0`mp_tac) >>
    simp[IS_SOME_EXISTS,EL_APPEND2,PULL_EXISTS]

    imp_res_tac RTC_bc_next_gvrel >> fs[] >> strip_tac >>
    match_mp_tac EQ_SYM >>
    match_mp_tac same_length_gvrel_same >>
    simp[] >>
    PairCases_on`grd'` >> Cases_on`s2` >>
    fs[env_rs_def,Cenv_bs_def,s_refs_def] >>
    imp_res_tac LIST_REL_LENGTH >>
    fs[Abbr`Csg`] >>
    fs[to_i2_invariant_def,to_i1_invariant_def] >>
    imp_res_tac LIST_REL_LENGTH >> fs[] ) >>
  simp[EXISTS_PROD] >>
  Cases_on`s2`>> simp[env_rs_def,PULL_EXISTS] >>
  rator_x_assum`to_i1_invariant`assume_tac >>
  fs[top_to_i1_def,LET_THM] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >>
  imp_res_tac dec_to_i1_new_dec_vs >> rfs[] >> fs[LENGTH_NIL] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[Once evaluate_prompt_i1_cases] >>
  fs[Once evaluate_decs_i1_cases] >>
  fs[Once evaluate_decs_i1_cases] >>
  fs[] >>
  rator_x_assum`to_i2_invariant`assume_tac >>
  fs[merge_alist_mod_env_def] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  `(*env = [] ∧*) exh = FEMPTY ∧ c = rs.contags_env` by (
    unabbrev_all_tac >>
    qpat_assum`∀x. Y`kall_tac >>
    qpat_assum`∀x. Y`kall_tac >>
    qpat_assum`∀x. Y`kall_tac >>
    rator_x_assum`bc_fetch`kall_tac>>
    rator_x_assum`Cenv_bs`kall_tac>>
    rator_x_assum`Cv_bv`kall_tac>>
    rator_x_assum`RTC`kall_tac>>
    rator_x_assum`closed_vlabs`kall_tac>>
    rator_x_assum`Cevaluate`kall_tac>>
    rator_x_assum`Cevaluate`kall_tac>>
    rator_x_assum`free_vars_pat`kall_tac>>
    rator_x_assum`free_vars`kall_tac>>
    rator_x_assum`evaluate_pat`kall_tac>>
    rator_x_assum`EVERY`kall_tac>>
    rator_x_assum`EVERY`kall_tac>>
    rator_x_assum`all_labs`kall_tac>>
    rator_x_assum`ALL_DISTINCT`kall_tac>>
    fs[prompt_to_i2_def,LET_THM] >>
    first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    fs[decs_to_i2_def,LET_THM] >>
    Cases_on`d`>>fs[dec_to_i1_def,LET_THM,LENGTH_NIL]>>
    rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
    simp[get_tagenv_def,mod_tagenv_lemma] >> rfs[] >>
    fs[alloc_defs_GENLIST,ZIP_EQ_NIL,LENGTH_NIL_SYM] >>
    fs[build_exh_env_def,FUNION_FEMPTY_1,FUPDATE_LIST_EQ_FEMPTY] >>
    fs[Once evaluate_dec_i1_cases] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    imp_res_tac disjoint_set_lemma >>
    fs[type_defs_to_new_tdecs_def,alloc_tags_def] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    simp[mod_tagenv_lemma,get_tagenv_def] >>
    rfs[] >> fs[]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[FUNION_FEMPTY_1] >>
  `env = []` by (
    fs[to_i2_invariant_def] >>
    imp_res_tac LIST_REL_LENGTH >>
    rfs[] >>
    REWRITE_TAC[GSYM LENGTH_NIL] >>
    DECIDE_TAC ) >>
  BasicProvers.VAR_EQ_TAC >> fs[] >>
  qexists_tac`grd0` >> simp[] >>
  qexists_tac`gtagenv2` >>
  qexists_tac`rd'` >>
  qexists_tac`SND s2_i1` >>
  qexists_tac`SND s2_i2` >>
  qexists_tac`genv2` >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    unabbrev_all_tac >>
    rator_x_assum`bc_fetch`kall_tac >>
    rator_x_assum`Cenv_bs`kall_tac >>
    rator_x_assum`Cv_bv`kall_tac >>
    rator_x_assum`RTC`kall_tac >>
    rator_x_assum`closed_vlabs`kall_tac >>
    rator_x_assum`Cevaluate`kall_tac >>
    first_x_assum(mp_tac o MATCH_MP evaluate_dec_closed) >>
    simp[] >> disch_then match_mp_tac >>
    fs[closed_top_def] >>
    simp[all_env_closed_def] ) >>
  conj_tac >- (
    rator_x_assum`to_i1_invariant`mp_tac >>
    Cases_on`s2_i1` >>
    simp[to_i1_invariant_def] >>
    simp[s_to_i1_cases] ) >>
  conj_tac >- (
    rator_x_assum`to_i2_invariant`mp_tac >>
    Cases_on`s2_i1` >>
    Cases_on`s2_i2` >>
    simp[to_i2_invariant_def] >>
    strip_tac >>
    conj_tac >- metis_tac[] >>
    rator_x_assum`s_to_i2`mp_tac >>
    simp[s_to_i2_cases] ) >>
  rator_x_assum`store_to_exh`mp_tac >>
  simp[store_to_exh_csg_rel,csg_rel_unpair,LIST_REL_O,sv_rel_O] >>
  strip_tac >> simp[PULL_EXISTS] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  rpt(rator_x_assum`csg_rel`mp_tac) >>
  simp[map_count_store_genv_def,csg_rel_unpair] >>
  rpt strip_tac >>
  simp[LIST_REL_O,OPTREL_O,sv_rel_O,PULL_EXISTS] >>
  simp[Once(GSYM CONJ_ASSOC)] >>
  qexists_tac`SND(FST q)` >>
  qexists_tac`SND q` >>
  qexists_tac`SND s'` >>
  simp[Once(CONJ_ASSOC)] >>
  simp[Once(CONJ_ASSOC)] >>
  conj_tac >- (
    reverse conj_tac >- (
      match_mp_tac LIST_REL_OPTREL_exh_Cv_syneq_trans >>
      HINT_EXISTS_TAC >> simp[] >>
      match_mp_tac LIST_REL_OPTREL_exh_Cv_syneq_trans >>
      HINT_EXISTS_TAC >> simp[] >>
      fs[EVERY2_MAP] >>
      match_mp_tac EVERY2_MEM_MONO >>
      HINT_EXISTS_TAC >> simp[] >>
      simp[UNCURRY,optionTheory.OPTREL_def] >>
      rw[exh_Cv_def] >> rw[] >>
      HINT_EXISTS_TAC >> simp[] >>
      first_x_assum(mp_tac o MATCH_MP (CONJUNCT1 evaluate_pat_closed)) >>
      simp[csg_closed_pat_def] >>
      simp[EVERY_MEM] >>
      imp_res_tac EVERY2_LENGTH >>
      imp_res_tac MEM_ZIP_MEM_MAP >>
      rfs[] >>
      disch_then(fn th => first_x_assum (mp_tac o MATCH_MP (CONJUNCT2 (CONJUNCT1 th)))) >>
      simp[] ) >>
    match_mp_tac LIST_REL_sv_rel_exh_Cv_syneq_trans >>
    HINT_EXISTS_TAC >> simp[] >>
    match_mp_tac LIST_REL_sv_rel_exh_Cv_syneq_trans >>
    HINT_EXISTS_TAC >> simp[] >>
    fs[EVERY2_MAP] >>
    match_mp_tac EVERY2_MEM_MONO >>
    HINT_EXISTS_TAC >> simp[] >>
    simp[FORALL_PROD] >>
    Cases >> Cases >> simp[sv_rel_cases] >>
    simp[EVERY2_MAP] >> strip_tac >>
    TRY(match_mp_tac EVERY2_MEM_MONO >> HINT_EXISTS_TAC >>
      imp_res_tac LIST_REL_LENGTH >> simp[MEM_ZIP,PULL_EXISTS]) >>
    rw[exh_Cv_def] >> rw[] >>
    HINT_EXISTS_TAC >> simp[] >>
    first_x_assum(mp_tac o MATCH_MP (CONJUNCT1 evaluate_pat_closed)) >>
    simp[csg_closed_pat_def] >>
    simp[EVERY_MEM] >>
    imp_res_tac EVERY2_LENGTH >>
    imp_res_tac MEM_ZIP_MEM_MAP >>
    rfs[] >>
    metis_tac[sv_every_def,MEM_EL,EVERY_MEM]) >>
  conj_tac >- (
    rator_x_assum`Cevaluate`mp_tac >>
    specl_args_of_then``Cevaluate``Cevaluate_closed_vlabs mp_tac >>
    ntac 2 strip_tac >>
    first_x_assum(qspec_then`bc0++YY++ZZ`mp_tac) >>
    simp[] >>
    simp[closed_vlabs_def] >>
    PairCases_on`q`>>simp[all_vlabs_csg_def,vlabs_csg_def] >>
    discharge_hyps >- metis_tac[EVERY_MEM] >>
    strip_tac >> simp[] >>
    metis_tac[] ) >>
  `q' = FST(FST q)` by (
    fs[to_i1_invariant_def,s_to_i1_cases] >>
    fs[to_i2_invariant_def,s_to_i2_cases] >>
    rfs[] ) >>
  BasicProvers.VAR_EQ_TAC >>
  ntac 5 (pop_assum kall_tac) >>
  match_mp_tac Cenv_bs_with_irr >>
  Q.PAT_ABBREV_TAC`bs1:bc_state = X Y` >>
  qexists_tac`bs1 with pc := next_addr bs.inst_length (bc0++YY)` >>
  simp[Abbr`bs1`] >>
  match_mp_tac Cenv_bs_imp_decsz >>
  simp[] >>
  qexists_tac`y` >>
  match_mp_tac Cenv_bs_with_irr >>
  first_assum(match_exists_tac o concl) >>
  simp[])
*)

(* compile_initial_prog for known-successful (initial) programs *)

val evaluate_decs_i2_num_defs = store_thm("evaluate_decs_i2_num_defs",
  ``∀ck exh genv s l res.
      evaluate_decs_i2 ck exh genv s l res ⇒
      SND(SND res) = NONE ⇒
        LENGTH (FST(SND res)) = num_defs l``,
  ho_match_mp_tac evaluate_decs_i2_ind >>
  rw[num_defs_def] >>
  fs[Once evaluate_dec_i2_cases] >>
  rw[num_defs_def])

val prog_to_i3_initial_correct = store_thm("prog_to_i3_initial_correct",
  ``∀ck (exh:exh_ctors_env) genv s p res.
      evaluate_prog_i2 ck exh genv s p res ⇒
      ∀s' new_env next' e.
        (res = (s',new_env,NONE)) ∧
        (prog_to_i3_initial (LENGTH genv) p = (next',e)) ⇒
        (next' = LENGTH genv + LENGTH new_env) ∧
        evaluate_i3 ck (exh,[]) (s,genv) e ((s',genv++new_env),Rval (Litv_i2 Unit))``,
  ho_match_mp_tac evaluate_prog_i2_ind >>
  conj_tac >- (
    simp[prog_to_i3_initial_def] >>
    simp[Once evaluate_i3_cases] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >> simp[] >>
    simp[prog_to_i3_initial_def] >>
    rpt gen_tac >> strip_tac >>
    first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >>
    first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    Cases_on`prompt` >>
    fs[prompt_to_i3_initial_def,LET_THM] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    fs[evaluate_prompt_i2_cases] >>
    rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
    imp_res_tac evaluate_decs_i2_num_defs >> fs[] >>
    simp[Once evaluate_i3_cases,libTheory.opt_bind_def] >>
    simp[Once evaluate_i3_cases] >>
    simp[Once evaluate_i3_cases,libTheory.opt_bind_def] >>
    first_x_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO]decs_to_i3_correct)) >>
    simp[dec_result_to_i3_cases] >> rw[] >>
    first_assum(match_exists_tac o concl) >> rw[]) >>
  rw[])

val to_i1_invariant_clocks_match = prove(
  ``to_i1_invariant a b c d e f g h ⇒ FST f = FST g``,
  rw[to_i1_invariant_def,s_to_i1_cases] >> rw[])

val to_i2_invariant_clocks_match = prove(
  ``to_i2_invariant a b c d e i f g h k ⇒ FST f = FST g``,
  rw[to_i2_invariant_def,s_to_i2_cases] >> rw[])

val compile_initial_prog_thm = store_thm("compile_initial_prog_thm",
  ``∀ck env stm prog res. evaluate_whole_prog ck env stm prog res ⇒
     ∀grd rs rs' bc bs bc0 s envC envM envE.
      res = (s,envC,Rval (envM,envE)) ∧
      env_rs env stm grd rs (bs with code := bc0) ∧
      (compile_initial_prog rs prog = (rs',bc)) ∧
      (bs.code = bc0 ++ REVERSE bc) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      ck ∧ IS_SOME bs.clock
      ⇒
      ∃bs' grd'.
      bc_next^* bs bs' ∧
      bc_fetch bs' = NONE ∧
      bs'.pc = next_addr bs.inst_length bs.code ∧
      bs'.output = bs.output ∧
      env_rs (envM++FST env,merge_alist_mod_env envC (FST(SND env)),envE++(SND(SND env))) s grd' rs' bs'``,
  simp[compile_initial_prog_def] >> rw[] >>
  first_assum (split_applied_pair_tac o lhs o concl) >> fs[] >>
  `∃v1 v2 v3 p0. prog_to_i1 rs.next_global m1 m2 prog = (v1,v2,v3,p0)` by simp[GSYM EXISTS_PROD] >> fs[] >>
  rpt(first_assum (split_applied_pair_tac o lhs o concl) >> fs[]) >>
  PairCases_on`stm` >> PairCases_on`env` >> PairCases_on`s` >>
  (whole_prog_to_i1_correct
   |> ONCE_REWRITE_RULE[CONJ_COMM]
   |> ONCE_REWRITE_RULE[GSYM CONJ_ASSOC]
   |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
   |> (fn th => first_assum (mp_tac o MATCH_MP th))) >>
  ONCE_REWRITE_TAC[GSYM CONJ_ASSOC] >>
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  PairCases_on`grd` >> fs[env_rs_def] >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  qpat_assum`X = LENGTH grd0`(assume_tac o SYM) >> fs[] >>
  strip_tac >>
  (whole_prog_to_i2_correct
   |> ONCE_REWRITE_RULE[GSYM CONJ_ASSOC]
   |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
   |> (fn th => first_assum (mp_tac o MATCH_MP th))) >>
  simp[] >>
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  `∃x y z. rs.contags_env = (x,y,z)` by metis_tac[pair_CASES] >> fs[] >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  pop_assum(assume_tac o SYM) >> fs[] >>
  pop_assum kall_tac >>
  PairCases_on`c`>>simp[] >>
  strip_tac >>
  (prog_to_i3_initial_correct
   |> (fn th => first_assum (mp_tac o MATCH_MP th))) >>
  `LENGTH genv2 = LENGTH grd0` by (
    fs[to_i2_invariant_def] >>
    imp_res_tac EVERY2_LENGTH >>
    fs[] ) >>
  simp[] >> strip_tac >>
  first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_exh_correct)) >>
  simp[env_to_exh_MAP] >>
  qmatch_assum_rename_tac`csg_rel (v_to_exh rs.exh) ((s10,s20),genv2) csgh` >>
  `store_to_exh (exh ⊌ rs.exh) ((s10,s20),genv2) csgh` by tac1 >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
  simp[Once result_to_exh_cases] >>
  disch_then(qspec_then`exh ⊌ rs.exh`mp_tac) >> simp[] >>
  strip_tac >>
  first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_pat_correct)) >>
  simp[] >>
  disch_then(qx_choosel_then[`res3`]strip_assume_tac) >>
  first_assum (qspec_then`[]`mp_tac o MATCH_MP (CONJUNCT1 evaluate_pat_exp_pat)) >>
  Q.PAT_ABBREV_TAC`ep = exp_to_pat X Y` >>
  disch_then(qspecl_then[`sp`,`ep`]mp_tac) >>
  discharge_hyps >- (
    simp[CONJUNCT1 exp_pat_refl] >> fs[csg_to_pat_MAP] ) >>
  disch_then(qx_choosel_then[`res4`]strip_assume_tac) >>
  tac12 >>
  qpat_assum`bs2 = X`(fn th => assume_tac(EQ_MP (SYM(ISPEC(concl th)markerTheory.Abbrev_def)) th)) >> fs[] >>
  qmatch_assum_abbrev_tac`bc_next^* bs0 bs2` >>
  first_x_assum(mp_tac o MATCH_MP RTC_bc_next_prepend_output) >>
  disch_then(qspec_then`bs.output`strip_assume_tac) >>
  qmatch_assum_abbrev_tac`bc_next^* bs1' bs3` >>
  qmatch_assum_abbrev_tac`bc_next bs bs1` >>
  `bs1' = bs1` by (
    simp[Abbr`bs1'`,Abbr`bs0`,bc_state_component_equality,Abbr`bs1`] >>
    fs[clos_numberTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_to_bvlTheory.state_rel_def,s_to_Cs_unpair] ) >>
  `bc_next^* bs bs3` by metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
  `bc_fetch bs3 = SOME (Stack Pop)` by (
    match_mp_tac bc_fetch_next_addr >>
    simp[Abbr`bs3`,Abbr`bs2`] >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`[]` >> simp[]) >>
  srw_tac[DNF_ss][Once RTC_CASES2] >> disj2_tac >>
  first_assum(match_exists_tac o concl) >>
  simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
  simp[Abbr`bs3`,Abbr`bs2`,bc_eval_stack_def] >>
  ntac 2 (pop_assum kall_tac) >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    simp[bc_fetch_def] >>
    match_mp_tac bc_fetch_aux_end_NONE >>
    REWRITE_TAC[SUM_APPEND,FILTER_APPEND,MAP_APPEND] >>
    simp[] ) >>
  conj_tac >- (
    REWRITE_TAC[SUM_APPEND,FILTER_APPEND,MAP_APPEND,REVERSE_APPEND] >>
    simp[] ) >>
  conj_tac >- (
    fs[clos_numberTheory.state_rel_def,clos_annotateTheory.state_rel_def,clos_to_bvlTheory.state_rel_def,s_to_Cs_unpair] ) >>
  qpat_assum`bc_next^* bs1 X`kall_tac >>
  simp[Once EXISTS_PROD,env_rs_def] >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_asm1_tac >- (
    rpt (rator_x_assum`good_labels`mp_tac) >>
    rpt (rator_x_assum`between_labels`mp_tac) >>
    rpt (BasicProvers.VAR_EQ_TAC) >>
    simp[good_labels_def,FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,PULL_EXISTS
        ,EVERY_FILTER,between_labels_def,EVERY_MAP,EVERY_MEM,between_def,PULL_FORALL,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
    unabbrev_all_tac >>
    ntac 2 (pop_assum kall_tac) >>
    fs[PULL_EXISTS,EVERY_MEM,MEM_FILTER,is_Label_rwt,between_def,MEM_MAP] >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][]) >>
  cheat)

(*
  fs[evaluate_whole_prog_def] >>
  simp[] >> strip_tac >>
  imp_res_tac to_i1_invariant_clocks_match >>
  CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(same_const``to_i1_invariant`` o fst o strip_comb))) >>
  first_assum (split_pair_match o concl) >> fs[] >>
  first_assum (match_exists_tac o concl) >> simp[] >>
  imp_res_tac to_i2_invariant_clocks_match >>
  CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(same_const``to_i2_invariant`` o fst o strip_comb))) >>
  first_assum (split_pair_match o concl) >> fs[] >>
  first_assum (match_exists_tac o concl) >> simp[] >> rw[] >>
  rator_x_assum`RTC`kall_tac>>
  rator_x_assum`RTC`kall_tac>>
  fs[to_i2_invariant_def] >>
  imp_res_tac LIST_REL_LENGTH >> fs[] >>
  rator_x_assum`store_to_exh`mp_tac >>
  simp[store_to_exh_csg_rel,csg_rel_unpair] >> strip_tac >>
  rpt(rator_x_assum`csg_rel`mp_tac) >>
  simp[csg_rel_unpair,map_count_store_genv_def] >>
  rpt strip_tac >>
  simp[LIST_REL_O,sv_rel_O,OPTREL_O,PULL_EXISTS] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(can (match_term ``LIST_REL (OPTREL (v_to_exh X)) Y Z``)))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  fs[evaluate_whole_prog_i1_def] >>
  qexists_tac`rd'` >>
  qexists_tac`SND(FST s'')` >>
  qexists_tac`SND s''` >>
  CONV_TAC(lift_conjunct_conv(same_const``closed_vlabs`` o fst o strip_comb)) >>
  conj_tac >- (
    rator_x_assum `closed_vlabs`mp_tac >>
    simp[closed_vlabs_def] >> strip_tac >> rw[] >>
    match_mp_tac code_env_cd_append >>
    conj_asm2_tac >- (
      match_mp_tac code_env_cd_append >>
      fs[FILTER_APPEND,ALL_DISTINCT_APPEND] >>
      metis_tac[] ) >>
    fs[good_labels_def] ) >>
  CONV_TAC(lift_conjunct_conv(same_const``Cenv_bs`` o fst o strip_comb)) >>
  conj_tac >- (
    match_mp_tac Cenv_bs_imp_decsz >> simp[] >>
    qexists_tac`Block 2 []` >>
    match_mp_tac Cenv_bs_append_code >>
    Q.PAT_ABBREV_TAC`bs1:bc_state = X Y` >>
    qexists_tac`bs1 with code := bc0++c0'` >>
    simp[Abbr`bs1`,bc_state_component_equality] >>
    match_mp_tac Cenv_bs_with_irr >>
    HINT_EXISTS_TAC >> simp[] ) >>
  reverse conj_tac >- (
    rator_x_assum`contains_primitives`mp_tac >>
    rator_x_assum`good_labels`mp_tac >>
    simp[good_labels_def] >> strip_tac >>
    simp[contains_primitives_def] >> strip_tac >>
    rw[] >> metis_tac[APPEND_ASSOC]) >>
  conj_tac >- tac7 >>
  first_x_assum(qspec_then`bs2`mp_tac) >>
  first_assum(mp_tac o MATCH_MP evaluate_prog_i1_closed) >> simp[] >>
  disch_then match_mp_tac >>
  reverse conj_tac >- (
    fs[to_i1_invariant_def,EVERY_sv_every_EVERY_store_vs,s_to_i1_cases] >>
    (v_to_i1_closed |> CONJUNCT2 |> CONJUNCT1 |> MP_CANON |> match_mp_tac) >>
    simp[vs_to_i1_MAP] >>
    fs[sv_to_i1_sv_rel] >>
    imp_res_tac LIST_REL_store_vs_intro >>
    first_assum(match_exists_tac o concl) >> simp[]) >>
  imp_res_tac FV_prog_to_i1 >> simp[])

val compile_initial_prog_code_labels_ok = store_thm("compile_initial_prog_code_labels_ok",
  ``∀init_compiler_state prog res code.
      (compile_initial_prog init_compiler_state prog = (res,code)) ∧ closed_prog prog ⇒
      code_labels_ok (local_labels code)``,
    rw[compile_initial_prog_def] >> fs[LET_THM] >>
    first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >>
    `∃a b c d. prog_to_i1 init_compiler_state.next_global m1 m2 prog = (a,b,c,d)` by simp[GSYM EXISTS_PROD] >>fs[] >>
    first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >>
    first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >>
    rw[local_labels_cons] >>
    match_mp_tac code_labels_ok_cons >> simp[] >>
    match_mp_tac (MP_CANON compile_Cexp_code_ok_thm) >>
    (fn(g as (_,w)) => map_every exists_tac (w |> strip_exists |> snd |> dest_conj |> fst |> rhs |> strip_comb |> snd) g) >>
    simp[] >>
    specl_args_of_then``exp_to_pat``(CONJUNCT1 free_vars_pat_exp_to_pat)mp_tac >>
    simp[] >> disch_then match_mp_tac >>
    imp_res_tac free_vars_i2_prog_to_i3_initial >>
    imp_res_tac free_vars_prog_to_i2 >>
    imp_res_tac FV_prog_to_i1 >>
    simp[] >>
    fs[closed_prog_def,all_env_dom_def,SUBSET_DEF,PULL_EXISTS])
*)

val _ = export_theory()
