open preamble BasicProvers word_to_wordTheory wordSemTheory
     wordPropsTheory word_allocProofTheory word_instProofTheory word_removeProofTheory;

val good_dimindex_def = labPropsTheory.good_dimindex_def;

val _ = new_theory "word_to_wordProof";

val is_phy_var_tac =
    full_simp_tac(srw_ss())[reg_allocTheory.is_phy_var_def]>>
    `0<2:num` by DECIDE_TAC>>
    `∀k.(2:num)*k=k*2` by DECIDE_TAC>>
    metis_tac[arithmeticTheory.MOD_EQ_0];

(*Chains up compile_single theorems*)
val compile_single_lem = prove(``
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
  TRY(
    qpat_abbrev_tac`p2 = full_ssa_cc_trans n p1`>>
    qpat_abbrev_tac`p3 = three_to_two_reg p2`)>>
  TRY(qpat_abbrev_tac`p3= full_ssa_cc_trans n p1`)>>
  Q.ISPECL_THEN [`a`,`p3`,`k`,`col`,`st`] mp_tac word_alloc_correct>>
  (discharge_hyps>-
      (full_simp_tac(srw_ss())[even_starting_locals_def]>>
      srw_tac[][word_allocTheory.even_list_def,MEM_GENLIST,reg_allocTheory.is_phy_var_def]
      >-
        is_phy_var_tac
      >>
        unabbrev_all_tac>>fs[full_ssa_cc_trans_wf_cutsets]>>
        ho_match_mp_tac three_to_two_reg_wf_cutsets>>
        fs[full_ssa_cc_trans_wf_cutsets]))>>
  rw[LET_THM]>>
  Q.ISPECL_THEN [`p1`,`st with permute:= perm'`,`n`] assume_tac full_ssa_cc_trans_correct>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  qexists_tac`perm''`>>
  Cases_on`evaluate(prog,st with permute:=perm'')`>>
  Cases_on`q=SOME Error`>>full_simp_tac(srw_ss())[]>>
  Q.ISPECL_THEN [`c`,`max_var prog +1`,`prog`,`st with permute:=perm''`,`q`,`r`,`st.locals`] mp_tac inst_select_thm>>
  (discharge_hyps>-
    (simp[locals_rel_def]>>
    Q.SPEC_THEN `prog` assume_tac max_var_max>>
    match_mp_tac every_var_mono>>
    HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[]>>
    DECIDE_TAC)>>
  srw_tac[][])>>
  `st with <|locals:=st.locals;permute:=perm''|> = st with permute:=perm''` by full_simp_tac(srw_ss())[state_component_equality]>>
  full_simp_tac(srw_ss())[]
  >-
    (split_pair_tac>>full_simp_tac(srw_ss())[]>>
    Q.ISPECL_THEN[`p2`,`st with permute:=perm'`,`res'`,`rcst`] mp_tac three_to_two_reg_correct>>
    discharge_hyps>-
      (rev_full_simp_tac(srw_ss())[]>>
      metis_tac[full_ssa_cc_trans_distinct_tar_reg])>>
    srw_tac[][]>>
    full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
    Cases_on`q`>>full_simp_tac(srw_ss())[])
  >>
    split_pair_tac>>full_simp_tac(srw_ss())[]>>
    split_pair_tac>>full_simp_tac(srw_ss())[word_state_eq_rel_def]
    >- metis_tac[]>>
    FULL_CASE_TAC>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]);

val get_vars_code_frame = prove(``
  ∀ls.
  get_vars ls (st with code:=l) =
  get_vars ls st``,
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

val rm_perm = prove(``
  s with permute:= s.permute = s``,full_simp_tac(srw_ss())[state_component_equality])

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
    qpat_assum`A=args` sym_sub_tac>>
    Cases_on`add_ret_loc o' x`>>full_simp_tac(srw_ss())[LENGTH_FRONT,ADD1])
  >>
    Cases_on`lookup x' st.code`>>full_simp_tac(srw_ss())[]>>res_tac>>
    Cases_on`x''`>>full_simp_tac(srw_ss())[compile_single_def,LET_THM]>>
    metis_tac[])

(*Adapted from a proof in wordProps*)
val domain_fromList2 = prove(``
  ∀q.
  domain(fromList2 q) = set(even_list (LENGTH q))``,
  recInduct SNOC_INDUCT >> srw_tac[][] >>
  full_simp_tac(srw_ss())[fromList2_def,word_allocTheory.even_list_def]>>
  simp[FOLDL_SNOC]>>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)>>
  full_simp_tac(srw_ss())[GSYM fromList2_def,FOLDL_SNOC]>>
  `!k. FST (FOLDL (λ(i,t) a. (i + 2,insert i a t)) (k,LN) l) =
        k + LENGTH l * 2` by
   (qspec_tac (`LN`,`t`) \\ qspec_tac (`l`,`l`) \\ Induct \\ full_simp_tac(srw_ss())[FOLDL]
    \\ full_simp_tac(srw_ss())[MULT_CLAUSES, AC ADD_COMM ADD_ASSOC])>>
  srw_tac[][]>>
  full_simp_tac(srw_ss())[MEM_GENLIST,EXTENSION]>>srw_tac[][]>>
  EQ_TAC>>srw_tac[][]
  >-
    (qexists_tac`LENGTH l`>>simp[])
  >-
    (qexists_tac`x'`>>simp[])
  >>
    Cases_on`x' = LENGTH l`>>simp[]>>
    `x' < LENGTH l` by DECIDE_TAC>>
    metis_tac[])

val push_env_code_frame = prove(``
  (push_env a b c).code = c.code``,
  Cases_on`b`>>TRY(PairCases_on`x`)>>full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def])

val pop_env_termdep = prove(``
  pop_env rst = SOME x ⇒ x.termdep = rst.termdep``,
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
  completeInduct_on`((st:('a,'b)state).termdep)`>>
  completeInduct_on`((st:('a,'b)state).clock)`>>
  simp[PULL_FORALL]>>
  completeInduct_on`prog_size (K 0) (prog:'a wordLang$prog)`>>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[PULL_FORALL,evaluate_def]>>
  Cases_on`prog`
  >- tac
  >- tac
  >- (Cases_on`i`>>full_simp_tac(srw_ss())[evaluate_def,inst_def,state_component_equality,assign_def,word_exp_code_frame,word_exp_perm,mem_load_def,get_var_perm,mem_store_def,get_var_def]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[set_var_def])
  >- tac
  >- tac
  >- tac
  >- tac
  >-
    (full_simp_tac(srw_ss())[evaluate_def,LET_THM,AND_IMP_INTRO]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    last_x_assum(qspecl_then[`st with <|clock:=n;termdep:=st.termdep-1|>`,`p`,`l`] mp_tac)>>
    discharge_hyps>-
      simp[]>>
    srw_tac[][]>>
    qexists_tac`perm'`>>full_simp_tac(srw_ss())[]>>
    split_pair_tac>>full_simp_tac(srw_ss())[]>>
    split_pair_tac>>full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[])
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
      discharge_hyps>-
        (full_simp_tac(srw_ss())[Abbr`stt`,dec_clock_def,call_env_def]>>
        DECIDE_TAC)>>
      srw_tac[][]>>
      Q.ISPECL_THEN [`n`,`r`,`LENGTH q`,`stt with permute:=perm'`] mp_tac (Q.GEN `name` compile_single_lem)>>
      discharge_hyps>-
        (full_simp_tac(srw_ss())[Abbr`stt`,call_env_def]>>
        simp[domain_fromList2])>>
      qpat_abbrev_tac`A = compile_single t k a c B`>>
      PairCases_on`A`>>srw_tac[][]>>full_simp_tac(srw_ss())[LET_THM]>>
      split_pair_tac>>full_simp_tac(srw_ss())[Abbr`stt`]
      >-
        (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def,call_env_def])>>
      Cases_on`res`>>full_simp_tac(srw_ss())[]
      >-
        (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def,call_env_def])>>
      Cases_on`x' = Error`>>full_simp_tac(srw_ss())[]
      >-
        (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def,call_env_def])>>
      split_pair_tac>>full_simp_tac(srw_ss())[]>>
      rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>
      split_pair_tac>>full_simp_tac(srw_ss())[]>>
      Q.ISPECL_THEN [`r`,`call_env q (dec_clock st) with permute:=perm''`,`rcst.permute`] mp_tac permute_swap_lemma>>full_simp_tac(srw_ss())[LET_THM]>>
      discharge_hyps>-
        (qpat_assum`A=res'` sym_sub_tac>>full_simp_tac(srw_ss())[])>>
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
    discharge_hyps>-
      (full_simp_tac(srw_ss())[Abbr`stt`,dec_clock_def]>>
      DECIDE_TAC)>>
    discharge_hyps>-
      (full_simp_tac(srw_ss())[Abbr`stt`,push_env_code_frame,call_env_def,dec_clock_def]>>
      Cases_on`o0`>>TRY(PairCases_on`x''`)>>simp[push_env_def,env_to_list_def])>>
    discharge_hyps>-
      full_simp_tac(srw_ss())[Abbr`stt`,push_env_code_frame,call_env_def,dec_clock_def]>>
    srw_tac[][]>>
    Q.ISPECL_THEN [`n`,`r`,`LENGTH q`,`stt with permute:=perm'`] mp_tac (Q.GEN `name` compile_single_lem)>>
    discharge_hyps>-
      (full_simp_tac(srw_ss())[Abbr`stt`,call_env_def]>>
      simp[domain_fromList2])>>
    qpat_abbrev_tac`A = compile_single t k a c B`>>
    PairCases_on`A`>>srw_tac[][]>>full_simp_tac(srw_ss())[LET_THM]>>
    split_pair_tac>>full_simp_tac(srw_ss())[Abbr`stt`]
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
      split_pair_tac>>full_simp_tac(srw_ss())[]>>
      last_x_assum(qspecl_then[`(set_var x''0 w0 x'') with permute:=rcst.permute`,`x''2`,`l`]kall_tac)>>
      last_x_assum(qspecl_then[`(set_var x''0 w0 x'') with permute:=rcst.permute`,`x''2`,`l`]mp_tac)>>
      discharge_hyps>-
        (simp[set_var_def]>>
        (*Monotonicity on 12, and dec_clock*)
        `rst.clock < st.clock` by
          (imp_res_tac evaluate_clock>>
          full_simp_tac(srw_ss())[call_env_def,dec_clock_def]>>
          DECIDE_TAC)>>
        qpat_assum`A=SOME x''` mp_tac>>full_simp_tac(srw_ss())[pop_env_def]>>
        EVERY_CASE_TAC>>srw_tac[][state_component_equality]>>
        simp[])>>
      discharge_hyps>-
        (simp[set_var_def]>>
        imp_res_tac evaluate_clock>>full_simp_tac(srw_ss())[]>>
        imp_res_tac evaluate_clock>>
        Cases_on`o0`>>TRY(PairCases_on`x'''`)>>full_simp_tac(srw_ss())[call_env_def,push_env_def,LET_THM,dec_clock_def,env_to_list_def]>>
        imp_res_tac pop_env_termdep>>
        full_simp_tac(srw_ss())[])>>
      discharge_hyps>-
        (simp[set_var_def]>>
        qsuff_tac`x''.code = st.code`>>full_simp_tac(srw_ss())[]>>
        `x''.code =rst.code` by
          (qpat_assum`A=SOME x''` mp_tac>>full_simp_tac(srw_ss())[pop_env_def]>>
          EVERY_CASE_TAC>>srw_tac[][state_component_equality]>>simp[])>>
        split_pair_tac>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>
        full_simp_tac(srw_ss())[]>>
        split_pair_tac>>
        full_simp_tac(srw_ss())[state_component_equality,word_state_eq_rel_def,call_env_def,push_env_code_frame,dec_clock_def])>>
      srw_tac[][]>>
      qspecl_then[`r`,`call_env q(push_env x' o0 (dec_clock st)) with permute:=perm''`,`perm'''`] assume_tac permute_swap_lemma>>
      rev_full_simp_tac(srw_ss())[LET_THM]>>
      qexists_tac`λn. if n = 0:num then st.permute 0 else perm'''' (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on `x'''`)>>
      (full_simp_tac(srw_ss())[call_env_def,push_env_def,dec_clock_def,LET_THM,env_to_list_def,ETA_AX,pop_env_perm,set_var_perm]>>
      qpat_assum`((λ(res',rcst). P) A)` mp_tac>>
      split_pair_tac>>rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[]>>
      `pop_env (rcst with code:=l) = SOME (x'' with <|code:=l;permute:=rcst.permute|>)` by
        (full_simp_tac(srw_ss())[pop_env_def,word_state_eq_rel_def]>>
        EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
        qpat_assum`A=x''` sym_sub_tac>>
        full_simp_tac(srw_ss())[state_component_equality])>>
      simp[]>>
      srw_tac[][]>>split_pair_tac>>full_simp_tac(srw_ss())[]>>
      split_pair_tac>>full_simp_tac(srw_ss())[set_var_def]>>
      `x''.code = rst.code` by
       (qpat_assum`A=SOME x''` mp_tac>>full_simp_tac(srw_ss())[pop_env_def]>>
        EVERY_CASE_TAC>>srw_tac[][state_component_equality]>>simp[])>>
      metis_tac[word_state_eq_rel_def]))
    >-
      (*Manual simulation for Exceptions*)
      (Cases_on`o0`>>full_simp_tac(srw_ss())[]
      >-
        (split_pair_tac>>full_simp_tac(srw_ss())[]>>
        qmatch_assum_abbrev_tac `evaluate(r,A) = _`>>
        Q.ISPECL_THEN [`r`,`A`,`rcst.permute`] mp_tac permute_swap_lemma>>
        simp[LET_THM,Abbr`A`]>>
        discharge_hyps>-
          (qpat_assum`B=res'` sym_sub_tac>>full_simp_tac(srw_ss())[])>>
        srw_tac[][]>>
        qexists_tac`λn. if n = 0:num then st.permute 0 else perm''' (n-1)`>>
        full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,ETA_AX]>>
        split_pair_tac>>rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[]>>
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
      split_pair_tac>>full_simp_tac(srw_ss())[]>>
      last_x_assum(qspecl_then[`(set_var x''0' w0 rst) with permute:=rcst.permute`,`x''1'`,`l`]kall_tac)>>
      last_x_assum(qspecl_then[`(set_var x''0' w0 rst) with permute:=rcst.permute`,`x''1'`,`l`]mp_tac)>>
      discharge_hyps>-
        (simp[set_var_def]>>
        imp_res_tac evaluate_clock>>
        full_simp_tac(srw_ss())[call_env_def,dec_clock_def]>>
        DECIDE_TAC)>>
      discharge_hyps>-
        (imp_res_tac evaluate_clock>>
        full_simp_tac(srw_ss())[set_var_def,call_env_def,push_env_def,dec_clock_def,LET_THM,env_to_list_def])>>
      discharge_hyps>-
        (simp[set_var_def]>>
        split_pair_tac>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>
        full_simp_tac(srw_ss())[]>>
        split_pair_tac>>
        full_simp_tac(srw_ss())[state_component_equality,word_state_eq_rel_def,call_env_def,push_env_code_frame,dec_clock_def])>>
      srw_tac[][]>>
      qspecl_then[`r`,`call_env q(push_env x' (SOME (x''0',x''1',x''2',x''3')) (dec_clock st)) with permute:=perm''`,`perm'''`] assume_tac permute_swap_lemma>>
      rev_full_simp_tac(srw_ss())[LET_THM]>>
      qexists_tac`λn. if n = 0:num then st.permute 0 else perm'''' (n-1)`>>
      full_simp_tac(srw_ss())[call_env_def,push_env_def,dec_clock_def,LET_THM,env_to_list_def,ETA_AX,pop_env_perm,set_var_perm]>>
      split_pair_tac>>rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[]>>
      srw_tac[][]>>split_pair_tac>>full_simp_tac(srw_ss())[]>>
      split_pair_tac>>full_simp_tac(srw_ss())[set_var_def]>>
      qmatch_assum_abbrev_tac`evaluate(_,A) = (res1,rst1)`>>
      qpat_abbrev_tac`B = rcst with <|locals:=C;code:=l|>`>>
      `A = B` by
         (unabbrev_all_tac>>
         full_simp_tac(srw_ss())[word_state_eq_rel_def,state_component_equality])>>
      full_simp_tac(srw_ss())[]>>
      metis_tac[word_state_eq_rel_def])
    >>
      TRY(split_pair_tac>>full_simp_tac(srw_ss())[]>>
      Q.ISPECL_THEN [`r`,`call_env q (push_env x' o0 (dec_clock st)) with permute:=perm''`,`rcst.permute`] mp_tac permute_swap_lemma>>full_simp_tac(srw_ss())[LET_THM]>>
      discharge_hyps>-
        (qpat_assum`A=res'` sym_sub_tac>>full_simp_tac(srw_ss())[])>>
      srw_tac[][]>>
      qexists_tac`λn. if n = 0:num then st.permute 0 else perm''' (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on`x''`)>>
      full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,ETA_AX]>>
      split_pair_tac>>rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[]>>
      srw_tac[][]>>full_simp_tac(srw_ss())[word_state_eq_rel_def,state_component_equality]>>NO_TAC)
    >>
      qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on`x''`)>>
      full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,ETA_AX])
  >- (*Seq, inductive*)
    (full_simp_tac(srw_ss())[evaluate_def,LET_THM,AND_IMP_INTRO]>>
    first_assum(qspecl_then[`p`,`st`,`l`] mp_tac)>>
    discharge_hyps>-size_tac>> srw_tac[][]>>
    split_pair_tac>>full_simp_tac(srw_ss())[]
    >- (qexists_tac`perm'`>>srw_tac[][]) >>
    split_pair_tac>>full_simp_tac(srw_ss())[]>>
    reverse (Cases_on`res`)>>full_simp_tac(srw_ss())[]
    >- (qexists_tac`perm'`>>full_simp_tac(srw_ss())[])>>
    (*Clock monotonicity*)
    `rst.clock ≤ st.clock ∧ rst.termdep = st.termdep` by
      (imp_res_tac evaluate_clock>>
      full_simp_tac(srw_ss())[state_component_equality])>>
    Cases_on`rst.clock = st.clock`>>
    TRY(first_assum(qspecl_then[`p0`,`rst`,`l`] mp_tac)>>
      discharge_hyps>-
      size_tac)>>
    TRY(first_assum(qspecl_then[`rst`,`p0`,`l`] mp_tac)>>
      discharge_hyps>-size_tac)>>
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
    (discharge_hyps>-size_tac>>srw_tac[][]))
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
  >- tac
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
        full_simp_tac(srw_ss())[MEM_MAP]>>split_pair_tac>>
        full_simp_tac(srw_ss())[]>>
        qpat_assum`(v,p) = A` mp_tac>>
        SELECT_ELIM_TAC>>srw_tac[][]>>
        full_simp_tac(srw_ss())[MEM_toAList,full_compile_single_def,LET_THM]>>
        split_pair_tac>>full_simp_tac(srw_ss())[])
      >>
        res_tac>>
        simp[ALOOKUP_MAP_gen,ALOOKUP_toAList]>>
        SELECT_ELIM_TAC>>srw_tac[][]>>
        metis_tac[])>>
  qpat_abbrev_tac`prog = Call A B C D`>>
  imp_res_tac compile_single_correct>>
  first_x_assum(qspec_then`prog` assume_tac)>>full_simp_tac(srw_ss())[LET_THM]>>
  qexists_tac`perm'`>>split_pair_tac>>full_simp_tac(srw_ss())[]>>
  split_pair_tac>>full_simp_tac(srw_ss())[]>>
  Cases_on`res=SOME Error`>>full_simp_tac(srw_ss())[]>>
  imp_res_tac word_remove_correct>>
  pop_assum kall_tac>>
  rev_full_simp_tac(srw_ss())[]>>
  pop_assum(qspec_then`l` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
  full_simp_tac(srw_ss())[Abbr`prog`,word_removeTheory.remove_must_terminate_def,LET_THM]>>
  qexists_tac`clk`>>full_simp_tac(srw_ss())[ADD_COMM])

val _ = export_theory();
