open preamble word_to_wordTheory wordSemTheory word_simpProofTheory
     wordPropsTheory word_allocProofTheory word_instProofTheory
     word_removeProofTheory;

val good_dimindex_def = labPropsTheory.good_dimindex_def;

val _ = new_theory "word_to_wordProof";

val _ = bring_to_front_overload"Call"{Thy="wordLang",Name="Call"};

val is_phy_var_tac =
    full_simp_tac(srw_ss())[reg_allocTheory.is_phy_var_def]>>
    `0<2:num` by DECIDE_TAC>>
    `∀k.(2:num)*k=k*2` by DECIDE_TAC>>
    metis_tac[arithmeticTheory.MOD_EQ_0];

val rmd_thms = (remove_dead_conventions |>SIMP_RULE std_ss [LET_THM,FORALL_AND_THM])|>CONJUNCTS

(*Chains up compile_single theorems*)
val compile_single_lem = store_thm("compile_single_lem",``
  ∀prog n st.
  domain st.locals = set(even_list n)
  ⇒
  ∃perm'.
  let (res,rst) = evaluate(prog,st with permute:=perm') in
  let (_,_,cprog) = (compile_single t k a c ((name,n,prog),col)) in
  if (res = SOME Error) then T else
  let (res',rcst) = evaluate(cprog,st) in
    res = res' ∧
    word_state_eq_rel rst rcst ∧
    case res of
      SOME _ => rst.locals = rcst.locals
    | _ => T``,
  full_simp_tac(srw_ss())[compile_single_def,LET_DEF]>>srw_tac[][]>>
  qpat_abbrev_tac`p1 = inst_select A B C`>>
  qpat_abbrev_tac`p2 = full_ssa_cc_trans n p1`>>
  TRY(
    qpat_abbrev_tac`p3 = FST (remove_dead p2 LN)`>>
    qpat_abbrev_tac`p4 = three_to_two_reg p3`)>>
  TRY(qpat_abbrev_tac`p4 = FST (remove_dead p2 LN)`)>>
  Q.ISPECL_THEN [`a`,`p4`,`k`,`col`,`st`] mp_tac word_alloc_correct>>
  (impl_tac>-
      (full_simp_tac(srw_ss())[even_starting_locals_def]>>
      srw_tac[][word_allocTheory.even_list_def,MEM_GENLIST,reg_allocTheory.is_phy_var_def]
      >-
        is_phy_var_tac
      >>
        unabbrev_all_tac>>fs[full_ssa_cc_trans_wf_cutsets]>>
        TRY(ho_match_mp_tac three_to_two_reg_wf_cutsets)>>
        match_mp_tac (el 5 rmd_thms)>>
        fs[full_ssa_cc_trans_wf_cutsets]))>>
  rw[]>>
  Q.ISPECL_THEN [`p1`,`st with permute:= perm'`,`n`] assume_tac full_ssa_cc_trans_correct>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  qexists_tac`perm''`>>
  Cases_on`evaluate(prog,st with permute:=perm'')`>>
  Cases_on`q=SOME Error`>>full_simp_tac(srw_ss())[]>>
  Q.ISPECL_THEN [`c`,`max_var (word_simp$compile_exp prog) +1`,`word_simp$compile_exp prog`,`st with permute:=perm''`,`q`,`r`,`st.locals`] mp_tac inst_select_thm>>
  (impl_tac >-
    (drule (GEN_ALL word_simpProofTheory.compile_exp_thm) \\ fs [] \\ strip_tac \\
    simp[locals_rel_def]>>
    Q.SPEC_THEN `word_simp$compile_exp prog` assume_tac max_var_max>>
    match_mp_tac every_var_mono>>
    HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[]>>
    DECIDE_TAC) >>
  srw_tac[][])>>
  `∀perm. st with <|locals:=st.locals;permute:=perm|> = st with permute:=perm` by full_simp_tac(srw_ss())[state_component_equality]>>
  full_simp_tac(srw_ss())[]>>
  qpat_x_assum`(λ(x,y). _) _`mp_tac >>
  pairarg_tac>>fs[]>>
  strip_tac>>
  Cases_on`remove_dead p2 LN`>>fs[]>>
  Q.ISPECL_THEN [`p2`,`LN:num_set`,`q'`,`r'`,`st with permute := perm'`,`st.locals`,`res'`,`rcst`] mp_tac evaluate_remove_dead>>
  impl_tac>>fs[strong_locals_rel_def]>>
  strip_tac
  >-
    (Q.ISPECL_THEN[`p3`,`st with permute:=perm'`,`res'`,`rcst with locals:=t'`] mp_tac three_to_two_reg_correct>>
    impl_tac>-
      (rev_full_simp_tac(srw_ss())[]>>
      unabbrev_all_tac>>rpt var_eq_tac >> fs[]>>
      metis_tac[full_ssa_cc_trans_distinct_tar_reg,el 4 rmd_thms,FST,PAIR])>>
    srw_tac[][]>>
    full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
    Cases_on`q`>>full_simp_tac(srw_ss())[])
  >>
    pairarg_tac>>full_simp_tac(srw_ss())[word_state_eq_rel_def,state_component_equality]>>
    FULL_CASE_TAC>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]);

val get_vars_code_frame = Q.prove(`
  ∀ls.
  get_vars ls (st with code:=l) =
  get_vars ls st`,
  Induct>>full_simp_tac(srw_ss())[get_vars_def,get_var_def])

(*TODO: Move to wordProps so there're no scoping problems..*)
val word_exp_code_frame = prove(``
  ∀(s:('a,'b) wordSem$state) exp. word_exp (s with code:=l) exp =
          word_exp s (exp:'a wordLang$exp)``,
  ho_match_mp_tac wordSemTheory.word_exp_ind>>srw_tac[][word_exp_def]
  >-
    (every_case_tac>>full_simp_tac(srw_ss())[mem_load_def])
  >>
    ntac 2 AP_THM_TAC >>
    ntac 2 AP_TERM_TAC >>
    full_simp_tac(srw_ss())[MAP_EQ_f])

val tac =
    full_simp_tac(srw_ss())[evaluate_def,LET_THM,state_component_equality]>>
    qexists_tac`st.permute`>>full_simp_tac(srw_ss())[alloc_def,get_var_def,gc_def,LET_THM,push_env_def,set_store_def,env_to_list_def,pop_env_def,has_space_def,call_env_def,set_var_def,get_var_def,dec_clock_def,jump_exc_def,get_vars_perm,get_vars_code_frame,set_vars_def,word_exp_perm,word_exp_code_frame,mem_store_def]>>
    every_case_tac>>full_simp_tac(srw_ss())[state_component_equality]

val rm_perm = Q.prove(`
  s with permute:= s.permute = s`,full_simp_tac(srw_ss())[state_component_equality])

val size_tac= (full_simp_tac(srw_ss())[wordLangTheory.prog_size_def]>>DECIDE_TAC);

val find_code_thm = prove(``
  (!n v. lookup n st.code = SOME v ==>
         ∃t k a c col.
         lookup n l = SOME (SND (compile_single t k a c ((n,v),col)))) ∧
  find_code o1 (add_ret_loc o' x) st.code = SOME (args,prog) ⇒
  ∃t k a c col n prog'.
  SND(compile_single t k a c ((n,LENGTH args,prog),col)) = (LENGTH args,prog') ∧
  find_code o1 (add_ret_loc o' x) l = SOME(args,prog')``,
  Cases_on`o1`>>simp[find_code_def]>>srw_tac[][]
  >-
    (ntac 2 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
    Cases_on`lookup n st.code`>>full_simp_tac(srw_ss())[]>>res_tac>>
    Cases_on`x'`>> full_simp_tac(srw_ss())[compile_single_def,LET_THM]>>
    qsuff_tac`q = LENGTH args`>-
     metis_tac[]>>
    qpat_x_assum`A=args` sym_sub_tac>>
    Cases_on`add_ret_loc o' x`>>full_simp_tac(srw_ss())[LENGTH_FRONT,ADD1])
  >>
    Cases_on`lookup x' st.code`>>full_simp_tac(srw_ss())[]>>res_tac>>
    Cases_on`x''`>>full_simp_tac(srw_ss())[compile_single_def,LET_THM]>>
    metis_tac[])

val push_env_code_frame = Q.prove(`
  (push_env a b c).code = c.code`,
  Cases_on`b`>>TRY(PairCases_on`x`)>>full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def])

val pop_env_termdep = Q.prove(`
  pop_env rst = SOME x ⇒ x.termdep = rst.termdep`,
  full_simp_tac(srw_ss())[pop_env_def]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[state_component_equality])

val compile_single_correct = prove(``
  ∀prog st l.
  (!n v. lookup n st.code = SOME v ==>
         ∃t k a c col.
         lookup n l = SOME (SND (compile_single t k a c ((n,v),col)))) ==>
  ∃perm'.
    let (res,rst) = evaluate (prog,st with permute := perm') in
      if res = SOME Error then T
      else
        let (res1,rst1) = evaluate (prog,st with code := l) in
          res1 = res ∧
          rst.code = st.code ∧
          rst1 = rst with code:=l``,
  (*recInduct doesn't seem to give a nice induction thm*)
  completeInduct_on`((st:('a,'b)wordSem$state).termdep)`>>
  completeInduct_on`((st:('a,'b)wordSem$state).clock)`>>
  simp[PULL_FORALL]>>
  completeInduct_on`prog_size (K 0) (prog:'a wordLang$prog)`>>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[PULL_FORALL,evaluate_def]>>
  Cases_on`prog`
  >- tac
  >- tac
  >- (Cases_on`i`>>full_simp_tac(srw_ss())[evaluate_def,inst_def,state_component_equality,assign_def,word_exp_code_frame,word_exp_perm,mem_load_def,get_var_perm,mem_store_def,get_var_def,get_vars_perm,LET_THM,get_vars_code_frame]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[set_var_def])
  >- tac
  >- tac
  >- tac
  >- tac
  >-
    (full_simp_tac(srw_ss())[evaluate_def,LET_THM,AND_IMP_INTRO]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    last_x_assum(qspecl_then[`st with <|clock:=n;termdep:=st.termdep-1|>`,`p`,`l`] mp_tac)>>
    impl_tac>-
      simp[]>>
    srw_tac[][]>>
    qexists_tac`perm'`>>full_simp_tac(srw_ss())[]>>
    pop_assum mp_tac >>
    pairarg_tac>>full_simp_tac(srw_ss())[]>>
    pairarg_tac>>full_simp_tac(srw_ss())[]>>
    pairarg_tac>>full_simp_tac(srw_ss())[]>>
    pairarg_tac>>full_simp_tac(srw_ss())[]>>
    rw[] >> ntac 3 (pop_assum mp_tac) >>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    rw[] >> rw[])
  >- (*Call -- the hard case*)
    (full_simp_tac(srw_ss())[evaluate_def,LET_THM,get_vars_perm,get_vars_code_frame]>>
    TOP_CASE_TAC>>full_simp_tac(srw_ss())[]>>
    TOP_CASE_TAC>>full_simp_tac(srw_ss())[]>>
    Cases_on`find_code o1 (add_ret_loc o' x) st.code`>>full_simp_tac(srw_ss())[]>>
    Cases_on`o'`>>full_simp_tac(srw_ss())[]>>
    Cases_on`x'`>>simp[]>>
    imp_res_tac find_code_thm>>
    ntac 2 (pop_assum kall_tac)>>
    full_simp_tac(srw_ss())[]
    >- (*Tail calls*)
      (ntac 2 (IF_CASES_TAC>>full_simp_tac(srw_ss())[])
      >- simp[call_env_def,state_component_equality]>>
      qabbrev_tac`stt = call_env q(dec_clock st)`>>
      first_x_assum(qspecl_then[`stt`,`prog'`,`l`] mp_tac)>>
      simp[AND_IMP_INTRO]>>
      impl_tac>-
        (full_simp_tac(srw_ss())[Abbr`stt`,dec_clock_def,call_env_def]>>
        DECIDE_TAC)>>
      srw_tac[][]>>
      Q.ISPECL_THEN [`n`,`r`,`LENGTH q`,`stt with permute:=perm'`] mp_tac (Q.GEN `name` compile_single_lem)>>
      impl_tac>-
        (full_simp_tac(srw_ss())[Abbr`stt`,call_env_def]>>
        simp[domain_fromList2,word_allocTheory.even_list_def])>>
      qpat_abbrev_tac`A = compile_single t k a c B`>>
      PairCases_on`A`>>srw_tac[][]>>full_simp_tac(srw_ss())[LET_THM]>>
      pop_assum mp_tac>>
      pairarg_tac>>full_simp_tac(srw_ss())[Abbr`stt`] >>
      strip_tac
      >-
        (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def,call_env_def])>>
      Cases_on`res`>>full_simp_tac(srw_ss())[]
      >-
        (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def,call_env_def])>>
      Cases_on`x' = Error`>>full_simp_tac(srw_ss())[]
      >-
        (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def,call_env_def])>>
      ntac 2 (pop_assum mp_tac) >>
      pairarg_tac>>full_simp_tac(srw_ss())[]>>
      ntac 2 strip_tac >>
      rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>
      qpat_x_assum`(λ(x,y). _) _`mp_tac >>
      pairarg_tac>>full_simp_tac(srw_ss())[]>>
      strip_tac >> rveq >>
      Q.ISPECL_THEN [`r`,`call_env q (dec_clock st) with permute:=perm''`,`rcst.permute`] mp_tac permute_swap_lemma>>full_simp_tac(srw_ss())[LET_THM]>>
      srw_tac[][]>>
      qexists_tac`perm'''`>>
      full_simp_tac(srw_ss())[call_env_def,dec_clock_def,word_state_eq_rel_def,state_component_equality])
    >>
    PairCases_on`x''`>>full_simp_tac(srw_ss())[]>>
    TOP_CASE_TAC>>full_simp_tac(srw_ss())[]>>
    TOP_CASE_TAC>>full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC>-
      full_simp_tac(srw_ss())[call_env_def,state_component_equality]>>
    full_simp_tac(srw_ss())[]>>
    qabbrev_tac`stt = call_env q(push_env x' o0 (dec_clock st))`>>
    first_assum(qspecl_then[`stt`,`prog'`,`l`] mp_tac)>>
    impl_tac>-
      (full_simp_tac(srw_ss())[Abbr`stt`,dec_clock_def]>>
      DECIDE_TAC)>>
    impl_tac>-
      (full_simp_tac(srw_ss())[Abbr`stt`,push_env_code_frame,call_env_def,dec_clock_def]>>
      Cases_on`o0`>>TRY(PairCases_on`x''`)>>simp[push_env_def,env_to_list_def])>>
    impl_tac>-
      full_simp_tac(srw_ss())[Abbr`stt`,push_env_code_frame,call_env_def,dec_clock_def]>>
    srw_tac[][]>>
    Q.ISPECL_THEN [`n`,`r`,`LENGTH q`,`stt with permute:=perm'`] mp_tac (Q.GEN `name` compile_single_lem)>>
    impl_tac>-
      (full_simp_tac(srw_ss())[Abbr`stt`,call_env_def]>>
      simp[domain_fromList2,word_allocTheory.even_list_def])>>
    qpat_abbrev_tac`A = compile_single t k a c B`>>
    PairCases_on`A`>>srw_tac[][]>>full_simp_tac(srw_ss())[LET_THM]>>
    pop_assum mp_tac >>
    pairarg_tac>>full_simp_tac(srw_ss())[Abbr`stt`] >>
    strip_tac
    >-
      (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on`x''`)>>
      full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,ETA_AX])>>
    Cases_on`res`>>full_simp_tac(srw_ss())[]
    >-
      (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on`x''`)>>
      full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,ETA_AX])>>
    Cases_on`x''`>>full_simp_tac(srw_ss())[]
    >-
      (*Manual simulation for Result*)
      (Cases_on`w ≠ Loc x''3 x''4`>>full_simp_tac(srw_ss())[]
      >-
        (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
        Cases_on`o0`>>TRY(PairCases_on`x''`)>>
        full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,ETA_AX])
      >>
      Cases_on`pop_env rst`>>full_simp_tac(srw_ss())[]
      >-
        (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
        Cases_on`o0`>>TRY(PairCases_on`x''`)>>
        full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,ETA_AX])
      >>
      reverse (Cases_on`domain x''.locals = domain x'`)>>full_simp_tac(srw_ss())[]
      >-
        (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
        Cases_on`o0`>>TRY(PairCases_on`x'''`)>>
        full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,ETA_AX])
      >>
      qpat_x_assum`(λ(x,y). _) _`mp_tac >>
      pairarg_tac>>full_simp_tac(srw_ss())[]>>
      strip_tac >>
      last_x_assum(qspecl_then[`(set_var x''0 w0 x'') with permute:=rcst.permute`,`x''2`,`l`]kall_tac)>>
      last_x_assum(qspecl_then[`(set_var x''0 w0 x'') with permute:=rcst.permute`,`x''2`,`l`]mp_tac)>>
      impl_tac>-
        (simp[set_var_def]>>
        (*Monotonicity on 12, and dec_clock*)
        `rst.clock < st.clock` by
          (imp_res_tac evaluate_clock>>
          full_simp_tac(srw_ss())[call_env_def,dec_clock_def]>>
          DECIDE_TAC)>>
        qpat_x_assum`A=SOME x''` mp_tac>>full_simp_tac(srw_ss())[pop_env_def]>>
        EVERY_CASE_TAC>>srw_tac[][state_component_equality]>>
        simp[])>>
      impl_tac>-
        (simp[set_var_def]>>
        imp_res_tac evaluate_clock>>full_simp_tac(srw_ss())[]>>
        imp_res_tac evaluate_clock>>
        Cases_on`o0`>>TRY(PairCases_on`x'''`)>>full_simp_tac(srw_ss())[call_env_def,push_env_def,LET_THM,dec_clock_def,env_to_list_def]>>
        imp_res_tac pop_env_termdep>>
        full_simp_tac(srw_ss())[])>>
      impl_tac>-
        (simp[set_var_def]>>
        qsuff_tac`x''.code = st.code`>>full_simp_tac(srw_ss())[]>>
        `x''.code =rst.code` by
          (qpat_x_assum`A=SOME x''` mp_tac>>full_simp_tac(srw_ss())[pop_env_def]>>
          EVERY_CASE_TAC>>srw_tac[][state_component_equality]>>simp[])>>
        pairarg_tac>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>
        full_simp_tac(srw_ss())[]>>
        full_simp_tac(srw_ss())[state_component_equality,word_state_eq_rel_def,call_env_def,push_env_code_frame,dec_clock_def])>>
      srw_tac[][]>>
      qspecl_then[`r`,`call_env q(push_env x' o0 (dec_clock st)) with permute:=perm''`,`perm'''`] assume_tac permute_swap_lemma>>
      rev_full_simp_tac(srw_ss())[LET_THM]>>
      qexists_tac`λn. if n = 0:num then st.permute 0 else perm'''' (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on `x'''`)>>
      (full_simp_tac(srw_ss())[call_env_def,push_env_def,dec_clock_def,LET_THM,env_to_list_def,ETA_AX,pop_env_perm,set_var_perm]>>
      qpat_x_assum`((λ(res',rcst). P) A)` mp_tac>>
      qpat_x_assum`((λ(res',rcst). P) A)` mp_tac>>
      pairarg_tac>>rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[]>>
      `pop_env (rcst with code:=l) = SOME (x'' with <|code:=l;permute:=rcst.permute|>)` by
        (full_simp_tac(srw_ss())[pop_env_def,word_state_eq_rel_def]>>
        EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
        qpat_x_assum`A=x''` sym_sub_tac>>
        full_simp_tac(srw_ss())[state_component_equality])>>
      simp[]>>
      srw_tac[][]>>pairarg_tac>>full_simp_tac(srw_ss())[]>>
      pairarg_tac>>full_simp_tac(srw_ss())[set_var_def]>>
      `x''.code = rst.code` by
       (qpat_x_assum`A=SOME x''` mp_tac>>full_simp_tac(srw_ss())[pop_env_def]>>
        EVERY_CASE_TAC>>srw_tac[][state_component_equality]>>simp[])>>
      metis_tac[word_state_eq_rel_def]))
    >-
      (*Manual simulation for Exceptions*)
      (Cases_on`o0`>>full_simp_tac(srw_ss())[]
      >-
        (pop_assum mp_tac >> pairarg_tac>>full_simp_tac(srw_ss())[]>>
         strip_tac >>
        qmatch_assum_abbrev_tac `evaluate(r,A) = _`>>
        Q.ISPECL_THEN [`r`,`A`,`rcst.permute`] mp_tac permute_swap_lemma>>
        simp[LET_THM,Abbr`A`]>>
        impl_tac>-
          (qpat_x_assum`B=res'` sym_sub_tac>>full_simp_tac(srw_ss())[])>>
        srw_tac[][]>>
        qexists_tac`λn. if n = 0:num then st.permute 0 else perm''' (n-1)`>>
        full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,ETA_AX]>>
        qpat_x_assum`(λ(x,y). _) _`mp_tac >>
        pairarg_tac>>rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[]>>
        srw_tac[][]>>full_simp_tac(srw_ss())[word_state_eq_rel_def,state_component_equality])
      >>
      PairCases_on`x''`>>full_simp_tac(srw_ss())[]>>
      Cases_on`w ≠ Loc x''2' x''3'`
      >-
        (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
        full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,ETA_AX])>>
      Cases_on`domain rst.locals ≠ domain x'`
      >-
        (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
        full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,ETA_AX])
      >>
      qpat_x_assum`((λ(res',rcst). P) A)` mp_tac>>
      pairarg_tac>>full_simp_tac(srw_ss())[]>>strip_tac>>
      last_x_assum(qspecl_then[`(set_var x''0' w0 rst) with permute:=rcst.permute`,`x''1'`,`l`]kall_tac)>>
      last_x_assum(qspecl_then[`(set_var x''0' w0 rst) with permute:=rcst.permute`,`x''1'`,`l`]mp_tac)>>
      impl_tac>-
        (simp[set_var_def]>>
        imp_res_tac evaluate_clock>>
        full_simp_tac(srw_ss())[call_env_def,dec_clock_def]>>
        DECIDE_TAC)>>
      impl_tac>-
        (imp_res_tac evaluate_clock>>
        full_simp_tac(srw_ss())[set_var_def,call_env_def,push_env_def,dec_clock_def,LET_THM,env_to_list_def])>>
      impl_tac>-
        (simp[set_var_def]>>
        pairarg_tac>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>
        full_simp_tac(srw_ss())[]>>
        full_simp_tac(srw_ss())[state_component_equality,word_state_eq_rel_def,call_env_def,push_env_code_frame,dec_clock_def])>>
      srw_tac[][]>>
      qspecl_then[`r`,`call_env q(push_env x' (SOME (x''0',x''1',x''2',x''3')) (dec_clock st)) with permute:=perm''`,`perm'''`] assume_tac permute_swap_lemma>>
      rev_full_simp_tac(srw_ss())[LET_THM]>>
      qexists_tac`λn. if n = 0:num then st.permute 0 else perm'''' (n-1)`>>
      full_simp_tac(srw_ss())[call_env_def,push_env_def,dec_clock_def,LET_THM,env_to_list_def,ETA_AX,pop_env_perm,set_var_perm]>>
      rpt(pairarg_tac >> fs[]) >> rw[] >> fs[set_var_def] >> rfs[] >>
      qmatch_assum_abbrev_tac`evaluate (_,A) = (res1,_)` >>
      qmatch_assum_abbrev_tac`evaluate (_,B) = (res,_)` >>
      `A = B` by
         (unabbrev_all_tac>>
         full_simp_tac(srw_ss())[word_state_eq_rel_def,state_component_equality])>>
      full_simp_tac(srw_ss())[]>>
      metis_tac[word_state_eq_rel_def])
    >>
      TRY(pop_assum mp_tac >> pairarg_tac>>full_simp_tac(srw_ss())[]>>
      Q.ISPECL_THEN [`r`,`call_env q (push_env x' o0 (dec_clock st)) with permute:=perm''`,`rcst.permute`] mp_tac permute_swap_lemma>>full_simp_tac(srw_ss())[LET_THM]>>
      srw_tac[][]>>
      qexists_tac`λn. if n = 0:num then st.permute 0 else perm''' (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on`x''`)>>
      full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,ETA_AX]>>
      qpat_x_assum`(λ(a,b). _) _`mp_tac >>
      pairarg_tac>>rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[]>>
      srw_tac[][]>>full_simp_tac(srw_ss())[word_state_eq_rel_def,state_component_equality]>>NO_TAC)
    >>
      qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on`x''`)>>
      full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,ETA_AX])
  >- (*Seq, inductive*)
    (full_simp_tac(srw_ss())[evaluate_def,LET_THM,AND_IMP_INTRO]>>
    first_assum(qspecl_then[`p`,`st`,`l`] mp_tac)>>
    impl_tac>-size_tac>> srw_tac[][]>>
    pop_assum mp_tac >>
    pairarg_tac>>full_simp_tac(srw_ss())[]
    >> strip_tac
    >- (qexists_tac`perm'`>>srw_tac[][]) >>
    pop_assum mp_tac >>
    pairarg_tac>>full_simp_tac(srw_ss())[]>>
    strip_tac >>
    reverse (Cases_on`res`)>>full_simp_tac(srw_ss())[]
    >- (qexists_tac`perm'`>>full_simp_tac(srw_ss())[])>>
    (*Clock monotonicity*)
    `rst.clock ≤ st.clock ∧ rst.termdep = st.termdep` by
      (imp_res_tac evaluate_clock>>
      full_simp_tac(srw_ss())[state_component_equality])>>
    Cases_on`rst.clock = st.clock`>>
    TRY(first_assum(qspecl_then[`p0`,`rst`,`l`] mp_tac)>>
      impl_tac>-
      size_tac)>>
    TRY(first_assum(qspecl_then[`rst`,`p0`,`l`] mp_tac)>>
      impl_tac>-size_tac)>>
    srw_tac[][]>>
    qspecl_then[`p`,`st with permute:=perm'`,`perm''`]
      assume_tac permute_swap_lemma>>
    rev_full_simp_tac(srw_ss())[LET_THM]>>
    qexists_tac`perm'''`>>srw_tac[][]>>full_simp_tac(srw_ss())[])
  >-
    (simp[evaluate_def,get_var_def,get_var_imm_def]>>
    ntac 2 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
    Cases_on`r`>>full_simp_tac(srw_ss())[get_var_imm_def,get_var_def]>>
    rpt(TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
    TRY(qpat_abbrev_tac`prog = p`)>>
    TRY(qpat_abbrev_tac`prog = p0`)>>
    first_x_assum(qspecl_then[`prog`,`st`,`l`] mp_tac)>>
    (impl_tac>-size_tac>>srw_tac[][]))
  >-
    (qexists_tac`st.permute`>>full_simp_tac(srw_ss())[rm_perm]>>
    full_simp_tac(srw_ss())[evaluate_def,get_var_perm,get_var_def]>>
    ntac 2 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
    full_simp_tac(srw_ss())[alloc_def]>>
    TOP_CASE_TAC>>full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,set_store_def,gc_def]>>
    qpat_abbrev_tac`A = st.gc_fun B`>>
    Cases_on`A`>>full_simp_tac(srw_ss())[]>>
    PairCases_on`x'`>>full_simp_tac(srw_ss())[]>>
    qpat_abbrev_tac`A = dec_stack B C`>>
    Cases_on`A`>>full_simp_tac(srw_ss())[pop_env_def]>>
    Cases_on`x'`>>full_simp_tac(srw_ss())[]>>Cases_on`h`>>full_simp_tac(srw_ss())[]>>
    EVERY_CASE_TAC>>full_simp_tac(srw_ss())[has_space_def]>>
    rev_full_simp_tac(srw_ss())[call_env_def])
  >- tac
  >- tac
  >- tac
  >- (
    tac
    \\ fs[domain_lookup]
    \\ metis_tac[] )
  >- (tac>>
     Cases_on`call_FFI st.ffi n x'`>>simp[]));

val compile_word_to_word_thm = store_thm("compile_word_to_word_thm",
  ``(!n v. lookup n (st:('a,'ffi)wordSem$state).code = SOME v ==>
           ∃t k a c col.
           lookup n l = SOME (SND (full_compile_single t k a c ((n,v),col)))) ==>
    ?perm' clk.
      let prog = Call NONE (SOME start) [0] NONE in
      let (res,rst) = evaluate (prog,st with permute := perm') in
        if res = SOME Error then T else
          let (res1,rst1) = evaluate (prog,st with <|code := l;clock:=st.clock+clk;termdep:=0|>) in
            res1 = res /\ rst1.clock = rst.clock /\ rst1.ffi = rst.ffi``,
  simp[LET_THM]>>
  srw_tac[][]>>
  (*namely, l' is some map over st.code that replicates l everywhere except
  it doesn't do the last remove_must_terminate*)
  `∃l'.
    (!n v p. lookup n l' = SOME (v,p) ==>
     lookup n l = SOME (v,remove_must_terminate p)) ∧
    !n v.
      lookup n st.code = SOME v ⇒
      ∃t k a c col.
        lookup n l' = SOME (SND (compile_single t k a c ((n,v),col)))` by
      (qexists_tac`
      let ls = toAList st.code in
      let ls' = MAP (λn,v.
        n, @res.
        ∃t k a c col. lookup n l = SOME (SND (full_compile_single t k a c ((n,v),col))) ∧
        res = SND(compile_single t k a c ((n,v),col))) ls in
          fromAList ls'`>>
      simp[lookup_fromAList]>>srw_tac[][]
      >-
        (imp_res_tac ALOOKUP_MEM>>
        full_simp_tac(srw_ss())[MEM_MAP]>>pairarg_tac>>
        full_simp_tac(srw_ss())[]>>
        qpat_x_assum`(v,p) = A` mp_tac>>
        SELECT_ELIM_TAC>>srw_tac[][]>>
        full_simp_tac(srw_ss())[MEM_toAList,full_compile_single_def,LET_THM]>>
        pairarg_tac>>full_simp_tac(srw_ss())[])
      >>
        res_tac>>
        simp[ALOOKUP_MAP_gen,ALOOKUP_toAList]>>
        SELECT_ELIM_TAC>>srw_tac[][]>>
        metis_tac[])>>
  qpat_abbrev_tac`prog = Call A B C D`>>
  imp_res_tac compile_single_correct>>
  first_x_assum(qspec_then`prog` assume_tac)>>full_simp_tac(srw_ss())[LET_THM]>>
  qexists_tac`perm'`>>pairarg_tac>>full_simp_tac(srw_ss())[]>>
  pairarg_tac>>full_simp_tac(srw_ss())[]>>
  Cases_on`res=SOME Error`>>full_simp_tac(srw_ss())[]>>
  imp_res_tac word_remove_correct>>
  pop_assum kall_tac>>
  rev_full_simp_tac(srw_ss())[]>>
  pop_assum(qspec_then`l` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
  full_simp_tac(srw_ss())[Abbr`prog`,word_removeTheory.remove_must_terminate_def,LET_THM]>>
  qexists_tac`clk`>>full_simp_tac(srw_ss())[ADD_COMM])

val rmt_thms = (remove_must_terminate_conventions|>SIMP_RULE std_ss [LET_THM,FORALL_AND_THM])|>CONJUNCTS

(* syntax going into stackLang
  inst_ok_less and two_reg_inst are IGNORED for now
  since we still have an exit check in lab_to_target
*)
val compile_conventions = store_thm("compile_to_word_conventions",``
  (*addr_offset_ok 0w ac ∧ EVERY (λ(n,m,prog). every_inst (λi. F) prog) p ⇒*)
  let (_,progs) = compile wc ac p in
  MAP FST progs = MAP FST p ∧
  EVERY2 PERM (MAP (extract_labels o SND o SND) progs)
              (MAP (extract_labels o SND o SND) p) ∧
  EVERY (λ(n,m,prog).
    flat_exp_conventions prog ∧
    post_alloc_conventions (ac.reg_count - (5+LENGTH ac.avoid_regs)) prog
    (*full_inst_ok_less ac prog ∧
    (ac.two_reg_arith ⇒ every_inst two_reg_inst prog)*)) progs``,
  fs[compile_def]>>pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>rveq>>rw[]>>
  `LENGTH n_oracles = LENGTH p` by
    (fs[next_n_oracle_def]>>metis_tac[LENGTH_GENLIST])
  >-
    (match_mp_tac LIST_EQ>>
    fs[EL_MAP,full_compile_single_def]>>
    rw[]>>
    qpat_abbrev_tac`q = EL x A`>>
    fs[markerTheory.Abbrev_def]>>PairCases_on`q`>>
    pop_assum (assume_tac o SYM)>>
    fs[compile_single_def]>>
    pop_assum mp_tac>>
    fs[EL_MAP,EL_ZIP])
  >-
    (simp[LIST_REL_EL_EQN,EL_MAP,full_compile_single_def]>>
    rw[]>>
    qpat_abbrev_tac`q = EL x A`>>
    fs[markerTheory.Abbrev_def]>>PairCases_on`q`>>
    pop_assum (mp_tac o SYM)>>
    fs[EL_MAP,EL_ZIP]>>
    fs[compile_single_def]>>
    fs[GSYM (el 5 rmt_thms),GSYM word_alloc_lab_pres]>>
    IF_CASES_TAC>>
    fs[GSYM three_to_two_reg_lab_pres,GSYM full_ssa_cc_trans_lab_pres,GSYM inst_select_lab_pres,GSYM (el 6 rmd_thms)])>>
  fs[EVERY_MAP,EVERY_MEM,MEM_ZIP,FORALL_PROD]>>rw[]>>
  fs[full_compile_single_def,compile_single_def]>>
  CONJ_TAC>-
    (match_mp_tac (el 1 rmt_thms)>>
    match_mp_tac word_alloc_flat_exp_conventions>>
    IF_CASES_TAC>>
    TRY(match_mp_tac three_to_two_reg_flat_exp_conventions)>>
    match_mp_tac (el 1 rmd_thms)>>
    match_mp_tac full_ssa_cc_trans_flat_exp_conventions>>
    fs[inst_select_flat_exp_conventions])>>
  match_mp_tac (el 3 rmt_thms)>>
  match_mp_tac pre_post_conventions_word_alloc>>
  IF_CASES_TAC>>
  TRY(match_mp_tac three_to_two_reg_pre_alloc_conventions)>>
  match_mp_tac (el 3 rmd_thms)>>
  fs[full_ssa_cc_trans_pre_alloc_conventions])
  (* Rest of the proof for the other two conventions
    (match_mp_tac (el 2 rmt_thms)>>
    match_mp_tac word_alloc_full_inst_ok_less>>
    IF_CASES_TAC>>
    TRY(match_mp_tac three_to_two_reg_full_inst_ok_less)>>
    match_mp_tac full_ssa_cc_trans_full_inst_ok_less>>
    match_mp_tac inst_select_full_inst_ok_less>>
    metis_tac[EL_MEM])>>
  rw[]>>
  match_mp_tac (el 4 rmt_thms)>>
  match_mp_tac word_alloc_two_reg_inst>>
  fs[three_to_two_reg_two_reg_inst]*)

val _ = export_theory();
