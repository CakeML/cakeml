open preamble initSemEnvTheory semanticsPropsTheory
     backendTheory
     source_to_modProofTheory
     mod_to_conProofTheory
     con_to_decProofTheory
     dec_to_exhProofTheory
     exh_to_patProofTheory
     pat_to_closProofTheory
     clos_to_bvlProofTheory
     bvl_to_bviProofTheory
     bvi_to_bvpProofTheory
     bvp_to_wordProofTheory
     word_to_stackProofTheory
     stack_to_labProofTheory
     lab_to_targetProofTheory
local open compilerComputeLib bvpPropsTheory in end

val _ = new_theory"backendProof";

(* TODO: move *)

fun Abbrev_intro th =
  EQ_MP (SYM(SPEC(concl th)markerTheory.Abbrev_def)) th

val pair_CASE_eq = Q.store_thm("pair_CASE_eq",
  `pair_CASE p f = a ⇔ ∃x y. p = (x,y) ∧ f x y = a`,
  Cases_on`p`>>rw[]);

(* -- *)


(* --- composing bvp-to-target --- *)

val implements_intro_final = prove(
  ``(b /\ x <> Fail ==> y = {x}) ==> b ==> implements y {x}``,
  fs [implements_def] \\ rw [] \\ fs []
  \\ fs [semanticsPropsTheory.extend_with_resource_limit_def]);

val from_stack = let
  val lemma1 = lab_to_targetProofTheory.semantics_compile
    |> REWRITE_RULE [CONJ_ASSOC]
    |> MATCH_MP implements_intro_final
    |> REWRITE_RULE [GSYM CONJ_ASSOC] |> UNDISCH_ALL
    |> Q.INST [`code`|->`code2`]
  val lemma2 = stack_to_labProofTheory.full_make_init_semantics |> UNDISCH
    |> Q.INST [`code`|->`code1`]
  in simple_match_mp (MATCH_MP implements_trans lemma2) lemma1 end

val from_stack_fail = let
  val lemma1 = lab_to_targetProofTheory.semantics_compile
    |> REWRITE_RULE [CONJ_ASSOC]
    |> MATCH_MP implements_intro_final
    |> REWRITE_RULE [GSYM CONJ_ASSOC] |> UNDISCH_ALL
    |> Q.INST [`code`|->`code2`]
  val lemma2 = stack_to_labProofTheory.full_make_init_semantics_fail |> UNDISCH
    |> Q.INST [`code`|->`code1`]
  val th = EVAL ``(make_init mc_conf ffi save_regs io_regs t ms code2).ffi``
  in simple_match_mp (MATCH_MP implements_trans lemma2) lemma1
     |> REWRITE_RULE [th] end

val from_word = let
  val lemma1 = word_to_stackProofTheory.compile_semantics
    |> REWRITE_RULE [CONJ_ASSOC]
    |> MATCH_MP implements_intro_ext
    |> REWRITE_RULE [GSYM CONJ_ASSOC] |> UNDISCH_ALL
    |> Q.INST [`code`|->`code3`]
  in simple_match_mp (MATCH_MP implements_trans lemma1) from_stack end

val from_bvp = let
  val lemma1 = bvp_to_wordProofTheory.compile_semantics
    |> REWRITE_RULE [CONJ_ASSOC]
    |> MATCH_MP implements_intro_ext
    |> REWRITE_RULE [GSYM CONJ_ASSOC] |> UNDISCH_ALL
    |> Q.INST [`code`|->`code4`]
  in simple_match_mp (MATCH_MP implements_trans lemma1) from_word end

val from_bvp_fail = let
  val th = bvpPropsTheory.Resource_limit_hit_implements_semantics
  val th = MATCH_MP implements_trans th
  val th = MATCH_MP th from_stack_fail
  val target = from_bvp |> concl
  val curr = concl th
  val i = fst (match_term curr target)
  in INST i th end

val full_make_init_code =
  ``(^(full_make_init_def |> SPEC_ALL |> concl |> dest_eq |> fst)).code``
  |> SIMP_CONV (srw_ss()) [full_make_init_def,stack_allocProofTheory.make_init_def]

fun define_abbrev name tm = let
  val vs = free_vars tm |> sort
    (fn v1 => fn v2 => fst (dest_var v1) <= fst (dest_var v2))
  val vars = foldr mk_pair (last vs) (butlast vs)
  val n = mk_var(name,mk_type("fun",[type_of vars, type_of tm]))
  in Define `^n ^vars = ^tm` end

val machine_sem_implements_bvp_sem = save_thm("machine_sem_implements_bvp_sem",let
  val th = from_bvp |> DISCH_ALL
           |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC,full_make_init_code]
           |> Q.INST [`code1`|->`SND (compile asm_conf code3)`]
           |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> UNDISCH_ALL
  val th_fail = from_bvp_fail |> DISCH_ALL
           |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC,full_make_init_code]
           |> Q.INST [`code1`|->`codeN`]
           |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> UNDISCH_ALL
  val hs1 = hyp th
  val hs2 = hyp th_fail
  fun inter xs ys = filter (fn y => mem y ys) xs
  fun diff xs ys = filter (fn y => not (mem y ys)) xs
  val hs = inter hs1 hs2
  fun disch_assums thi =
    foldr (fn (tm,th) => DISCH tm th) thi (diff (hyp thi) hs)
     |> PURE_REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC]
  val th1 = disch_assums th
  val th2 = disch_assums th_fail
  val lemma = METIS_PROVE [] ``(b1 ==> x) /\ (b2 ==> x) ==> (b1 \/ b2 ==> x)``
  val th = simple_match_mp lemma (CONJ th1 th2)
           |> DISCH_ALL
           |> PURE_REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC]
  val (lhs,rhs) = dest_imp (concl th)
  fun diff xs ys = filter (fn x => not (mem x ys)) xs
  val vs = diff (free_vars lhs) (free_vars rhs) |> sort
    (fn v1 => fn v2 => fst (dest_var v1) <= fst (dest_var v2))
  val lemma = METIS_PROVE [] ``(!x. P x ==> Q) <=> ((?x. P x) ==> Q)``
  val th = GENL vs th |> SIMP_RULE std_ss [lemma]
  val def = define_abbrev "machine_sem_implements_bvp_pre"
               (th |> concl |> dest_imp |> fst)
  val th = th |> REWRITE_RULE [GSYM def]
  in th end);

(* --- composing source-to-target --- *)

val c = compilerComputeLib.the_compiler_compset
val () = computeLib.add_thms[prim_config_def] c
val () = computeLib.add_thms[initialProgramTheory.prim_types_program_def] c

val prim_config_eq = save_thm("prim_config_eq",
  computeLib.CBV_CONV c ``prim_config``);

val id_CASE_eq_SOME = Q.prove(
  `id_CASE x f (λa b. NONE) = SOME z ⇔ ∃y. x = Short y ∧ f y = SOME z`,
  Cases_on`x`>>rw[])

val option_CASE_eq_SOME = Q.prove(
  `option_CASE x NONE z = SOME y ⇔ ∃a. x = SOME a ∧ z a = SOME y`,
  Cases_on`x`>>rw[]);

val else_NONE_eq_SOME = Q.store_thm("else_NONE_eq_SOME",
  `(((if t then y else NONE) = SOME z) ⇔ (t ∧ (y = SOME z)))`,
  rw[])

val COND_eq_SOME = Q.store_thm("COND_eq_SOME",
  `((if t then SOME a else b) = SOME x) ⇔ ((t ∧ (a = x)) ∨ (¬t ∧ b = SOME x))`,
  rw[])

val compile_correct = Q.store_thm("compile_correct",
  `let (s,env) = THE (prim_sem_env (ffi:'ffi ffi_state)) in
   (c:'a backend$config).source_conf = (prim_config:'a backend$config).source_conf ∧
   c.mod_conf = prim_config.mod_conf ∧ c.clos_conf = prim_config.clos_conf ∧
   good_dimindex (:α) ∧
   ¬semantics_prog s env prog Fail ∧
   compile c prog = SOME (bytes,c') ∧
   machine_sem_implements_bvp_pre (ffi,mc,ms,SND(to_bvp c prog),(FST(to_bvp c prog)).clos_conf.start) ⇒
     machine_sem mc ffi ms ⊆
       extend_with_resource_limit (semantics_prog s env prog)`,
  srw_tac[][compile_eq_from_source,from_source_def] >>
  drule(GEN_ALL(MATCH_MP SWAP_IMP source_to_modProofTheory.compile_correct)) >>
  fs[initSemEnvTheory.prim_sem_env_eq] >>
  qpat_assum`_ = s`(assume_tac o Abbrev_intro o SYM) >>
  qpat_assum`_ = env`(assume_tac o Abbrev_intro o SYM) >>
  `∃s2 env2 gtagenv.
     precondition s env c.source_conf s2 env2 ∧
     FST env2.c = [] ∧
     s2.globals = [] ∧
     s2.ffi = ffi ∧
     s2.refs = [] ∧
     s2.defined_types = s.defined_types ∧
     s2.defined_mods = s.defined_mods ∧
     envC_tagged env2.c prim_config.mod_conf.tag_env gtagenv ∧
     exhaustive_env_correct prim_config.mod_conf.exh_ctors_env gtagenv ∧
     gtagenv_wf gtagenv ∧
     next_inv (IMAGE (SND o SND) (FRANGE (SND( prim_config.mod_conf.tag_env))))
       prim_config.mod_conf.next_exception gtagenv` by (
    simp[source_to_modProofTheory.precondition_def] >>
    simp[Abbr`env`,Abbr`s`] >>
    srw_tac[QUANT_INST_ss[pair_default_qp,record_default_qp]][] >>
    rw[source_to_modProofTheory.invariant_def] >>
    rw[source_to_modProofTheory.s_rel_cases] >>
    rw[source_to_modProofTheory.v_rel_cases] >>
    rw[prim_config_eq] >>
    Cases_on`ffi`>>rw[ffiTheory.ffi_state_component_equality] >>
    CONV_TAC(PATH_CONV"brrrllr"(REWRITE_CONV[DOMSUB_FUPDATE_THM] THENC EVAL)) >>
    rpt(CHANGED_TAC(CONV_TAC(PATH_CONV"brrrllr"(REWRITE_CONV[FRANGE_FUPDATE,DRESTRICT_FUPDATE] THENC EVAL)))) >>
    rw[DRESTRICT_DRESTRICT] >>
    rw[envC_tagged_def,
       semanticPrimitivesTheory.lookup_alist_mod_env_def,
       mod_to_conTheory.lookup_tag_env_def,
       mod_to_conTheory.lookup_tag_flat_def,
       FLOOKUP_DEF] >>
    simp[id_CASE_eq_SOME,PULL_EXISTS] >>
    simp[option_CASE_eq_SOME] >>
    simp[astTheory.id_to_n_def] >>
    simp[FAPPLY_FUPDATE_THM] >>
    simp[pair_CASE_eq,PULL_EXISTS] >>
    simp[COND_eq_SOME] >>
    srw_tac[DNF_ss][] >>
    (fn g =>
       let
         val tms = g |> #2 |> dest_exists |> #2
                     |> dest_conj |> #1
                     |> strip_conj |> filter is_eq
         val fm = tms |> hd |> lhs |> rator |> rand
         val ps = map ((rand ## I) o dest_eq) tms
         val tm = finite_mapSyntax.list_mk_fupdate
                  (finite_mapSyntax.mk_fempty (finite_mapSyntax.dest_fmap_ty(type_of fm)),
                   map pairSyntax.mk_pair ps)
       in exists_tac tm end g) >>
    simp[FAPPLY_FUPDATE_THM] >>
    conj_tac >- (
      simp[exhaustive_env_correct_def,IN_FRANGE,FLOOKUP_UPDATE,PULL_EXISTS] >>
      srw_tac[DNF_ss][] >>
      EVAL_TAC >>
      pop_assum mp_tac >> rw[] >>
      EVAL_TAC >>
      simp[PULL_EXISTS]) >>
    conj_tac >- (
      EVAL_TAC >> rw[] >> fs[semanticPrimitivesTheory.same_tid_def] ) >>
    simp[next_inv_def,PULL_EXISTS] >>
    simp[FLOOKUP_UPDATE] >>
    rw[] >> EVAL_TAC >>
    srw_tac[QUANT_INST_ss[std_qp]][]) >>
  disch_then drule >> strip_tac >>
  rator_x_assum`from_mod`mp_tac >>
  srw_tac[][from_mod_def,Abbr`c'''`,mod_to_conTheory.compile_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qmatch_assum_abbrev_tac`semantics_prog s env prog sem2` >>
  `sem2 ≠ Fail` by metis_tac[] >>
  `semantics_prog s env prog = { sem2 }` by (
    simp[EXTENSION,IN_DEF] >>
    metis_tac[semantics_prog_deterministic] ) >>
  qunabbrev_tac`sem2` >>
  drule (GEN_ALL mod_to_conProofTheory.compile_prog_semantics) >>
  fs[] >> rveq >>
  simp[AND_IMP_INTRO] >> simp[Once CONJ_COMM] >>
  disch_then drule >>
  simp[mod_to_conProofTheory.invariant_def,
       mod_to_conTheory.get_exh_def,
       mod_to_conTheory.get_tagenv_def] >>
  simp[mod_to_conProofTheory.s_rel_cases] >>
  CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++QUANT_INST_ss[record_default_qp,pair_default_qp])[])) >>
  simp[mod_to_conProofTheory.cenv_inv_def] >>
  disch_then(qspec_then`gtagenv`mp_tac)>>
  discharge_hyps >- (
    rw[Abbr`s`,prim_config_eq] >>
    fs[prim_config_eq] >>
    rator_x_assum`next_inv`mp_tac >>
    rpt(pop_assum kall_tac) >>
    REWRITE_TAC[FRANGE_FUPDATE,DRESTRICT_FUPDATE,DOMSUB_FUPDATE_THM] >>
    EVAL_TAC >> rw[SUBSET_DEF] >> fs[PULL_EXISTS] >>
    res_tac >> fs[] >>
    pop_assum mp_tac >>
    rpt(CHANGED_TAC(REWRITE_TAC[FRANGE_FUPDATE,DRESTRICT_FUPDATE,DOMSUB_FUPDATE_THM] >> EVAL_TAC)) >>
    rw[DRESTRICT_DRESTRICT] >> rw[]) >>
  strip_tac >>
  pop_assum(assume_tac o SYM) >> simp[] >>
  qunabbrev_tac`c''''`>>
  rator_x_assum`from_con`mp_tac >>
  srw_tac[][from_con_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  rfs[] >> fs[] >>
  drule(GEN_ALL(MATCH_MP SWAP_IMP (REWRITE_RULE[GSYM AND_IMP_INTRO]con_to_decProofTheory.compile_semantics))) >>
  simp[] >>
  discharge_hyps >- (
    rator_x_assum`mod_to_con$compile_prog`mp_tac >>
    simp[prim_config_eq] >> EVAL_TAC >>
    `semantics env2 s2 p ≠ Fail` by simp[] >>
    pop_assum mp_tac >>
    simp_tac(srw_ss())[modSemTheory.semantics_def] >>
    IF_CASES_TAC >> simp[] >> disch_then kall_tac >>
    pop_assum mp_tac >>
    simp[modSemTheory.evaluate_prog_def] >>
    BasicProvers.TOP_CASE_TAC >> simp[] >> strip_tac >> fs[] >>
    `¬MEM "option" (prog_to_top_types p)` by (
      fs[modSemTheory.no_dup_top_types_def,IN_DISJOINT,MEM_MAP] >>
      fs[Abbr`s`] >> metis_tac[] ) >>
    strip_tac >>
    match_mp_tac compile_prog_exh_unchanged >>
    asm_exists_tac >> simp[] >>
    qmatch_assum_abbrev_tac`compile_prog st p = _` >>
    qexists_tac`st`>>simp[Abbr`st`,mod_to_conTheory.get_exh_def] >>
    simp[FLOOKUP_UPDATE]) >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  rator_x_assum`from_dec`mp_tac >> srw_tac[][from_dec_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  rator_x_assum`con_to_dec$compile`mp_tac >>
  `c''.next_global = 0` by (
    fs[source_to_modTheory.compile_def,LET_THM] >>
    split_pair_tac >> fs[] >>
    split_pair_tac >> fs[] >>
    rveq >> simp[prim_config_eq] ) >> fs[] >>
  strip_tac >> fs[] >>
  qunabbrev_tac`c'''`>>fs[] >>
  qmatch_abbrev_tac`_ ⊆ _ { decSem$semantics env3 st3 es3 }` >>
  (dec_to_exhProofTheory.compile_exp_semantics
    |> Q.GENL[`sth`,`envh`,`es`,`st`,`env`]
    |> qispl_then[`env3`,`st3`,`es3`]mp_tac) >>
  simp[Abbr`env3`] >>
  simp[Once dec_to_exhProofTheory.v_rel_cases] >>
  simp[dec_to_exhProofTheory.state_rel_def] >>
  fs[Abbr`st3`,con_to_decProofTheory.compile_state_def] >>
  CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++QUANT_INST_ss[record_default_qp,pair_default_qp])[])) >>
  simp[Abbr`es3`,dec_to_exhTheory.compile_exp_def] >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  rator_x_assum`from_exh`mp_tac >>
  srw_tac[][from_exh_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  fs[exh_to_patTheory.compile_def] >>
  qmatch_abbrev_tac`_ ⊆ _ { exhSem$semantics env3 st3 es3 }` >>
  (exh_to_patProofTheory.compile_exp_semantics
   |> Q.GENL[`es`,`st`,`env`]
   |> qispl_then[`env3`,`st3`,`es3`]mp_tac) >>
  simp[Abbr`es3`,Abbr`env3`] >>
  fs[exh_to_patProofTheory.compile_state_def,Abbr`st3`] >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  rator_x_assum`from_pat`mp_tac >>
  srw_tac[][from_pat_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qmatch_abbrev_tac`_ ⊆ _ { patSem$semantics env3 st3 es3 }` >>
  (pat_to_closProofTheory.compile_semantics
   |> Q.GENL[`es`,`st`,`env`]
   |> qispl_then[`env3`,`st3`,`es3`]mp_tac) >>
  simp[Abbr`env3`,Abbr`es3`] >>
  fs[pat_to_closProofTheory.compile_state_def,Abbr`st3`] >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  rator_x_assum`from_clos`mp_tac >>
  srw_tac[][from_clos_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qmatch_abbrev_tac`_ ⊆ _ { closSem$semantics [] st3 [e3] }` >>
  (clos_to_bvlProofTheory.compile_semantics
   |> GEN_ALL
   |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s","e","c"]))
   |> qispl_then[`st3`,`e3`,`c.clos_conf`]mp_tac) >>
  simp[] >>
  discharge_hyps >- (
    simp[CONJ_ASSOC] >>
    conj_tac >- (
      unabbrev_all_tac >>
      simp[pat_to_closProofTheory.compile_contains_App_SOME] >>
      simp[pat_to_closProofTheory.compile_every_Fn_vs_NONE] >>
      simp[prim_config_eq] >> EVAL_TAC) >>
    simp[Abbr`st3`,clos_to_bvlProofTheory.full_state_rel_def] >>
    simp[Once clos_relationTheory.state_rel_rw] >>
    gen_tac >>
    qho_match_abbrev_tac`∃sa. P sa` >>
    srw_tac[QUANT_INST_ss[record_qp false (fn v => (K (type_of v = ``:'ffi closSem$state``))),pair_default_qp]][] >>
    simp[Abbr`P`] >>
    simp[clos_numberProofTheory.state_rel_def] >>
    qho_match_abbrev_tac`∃sa. P sa` >>
    srw_tac[QUANT_INST_ss[record_qp false (fn v => (K (type_of v = ``:'ffi closSem$state``))),pair_default_qp]][] >>
    simp[Abbr`P`] >>
    qho_match_abbrev_tac`∃sa. P sa` >>
    srw_tac[QUANT_INST_ss[record_qp false (fn v => (K (type_of v = ``:'ffi closSem$state``))),pair_default_qp]][] >>
    simp[Abbr`P`] >>
    simp[Once clos_relationTheory.state_rel_rw] >>
    simp[FEVERY_DEF] >>
    simp[clos_annotateProofTheory.state_rel_def] >>
    qho_match_abbrev_tac`∃sa. P sa` >>
    srw_tac[QUANT_INST_ss[record_qp false (fn v => (K (type_of v = ``:'ffi closSem$state``))),pair_default_qp]][] >>
    simp[Abbr`P`] >>
    qexists_tac`FEMPTY`>>simp[] >>
    simp[clos_to_bvlProofTheory.state_rel_def,FDOM_EQ_EMPTY] >>
    qexists_tac`FEMPTY`>>simp[] >>
    `∃c. p'' = toAList init_code ++ c` by (
      rator_x_assum`clos_to_bvl$compile`mp_tac >>
      rpt(pop_assum kall_tac) >>
      srw_tac[][clos_to_bvlTheory.compile_def] >>
      pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
      fs[] >> rveq >> rw[] ) >>
    rveq >>
    simp[lookup_fromAList,ALOOKUP_APPEND,ALOOKUP_toAList] >>
    strip_assume_tac init_code_ok >> simp[]) >>
  simp[Abbr`e3`] >>
  fs[Abbr`st3`] >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  rator_x_assum`from_bvl`mp_tac >>
  srw_tac[][from_bvl_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  Q.ISPEC_THEN`s2.ffi`drule(Q.GEN`ffi0` bvl_to_bviProofTheory.compile_semantics) >>
  qunabbrev_tac`c''''`>>fs[] >>
  discharge_hyps >- (
    (clos_to_bvlProofTheory.compile_all_distinct_locs
     |> ONCE_REWRITE_RULE[CONJ_ASSOC,CONJ_COMM]
     |> ONCE_REWRITE_RULE[CONJ_COMM]
     |> drule) >>
    disch_then match_mp_tac >>
    simp[prim_config_eq] >>
    EVAL_TAC ) >>
  disch_then(SUBST_ALL_TAC o SYM) >>
  rator_x_assum`from_bvi`mp_tac >>
  srw_tac[][from_bvi_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qmatch_abbrev_tac`_ ⊆ _ { bviSem$semantics ffi (fromAList p3) s3 }` >>
  (bvi_to_bvpProofTheory.compile_prog_semantics
   |> GEN_ALL
   |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["prog","start"]))
   |> qispl_then[`p3`,`s3`,`ffi`]mp_tac) >>
  discharge_hyps >- simp[] >>
  disch_then (SUBST_ALL_TAC o SYM) >>
  drule machine_sem_implements_bvp_sem
  \\ simp[implements_def]
  \\ `to_bvp c prog = (c''''',p'''')`
  by (
    simp[to_bvp_def,to_bvi_def,to_bvl_def,to_clos_def,to_pat_def,to_exh_def,to_dec_def,to_con_def,to_mod_def]
    \\ fs[mod_to_conTheory.compile_def]
    \\ fs[clos_to_bvlTheory.compile_def]
    \\ unabbrev_all_tac \\ fs[exh_to_patTheory.compile_def] )
  \\ simp[Abbr`c'''''`]
  \\ disch_then match_mp_tac
  \\ spose_not_then (strip_assume_tac o SYM)
  \\ fs[]
  (* TODO: bvp_to_wordProofTheory.inter_insert why is this theorem in that theory? it should be moved *));

val _ = export_theory();
