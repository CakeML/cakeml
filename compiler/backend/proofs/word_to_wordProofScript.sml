open preamble BasicProvers word_to_wordTheory wordSemTheory
     wordPropsTheory word_allocProofTheory word_instProofTheory;

val good_dimindex_def = labPropsTheory.good_dimindex_def;

val _ = new_theory "word_to_wordProof";

val is_phy_var_tac =
    fs[reg_allocTheory.is_phy_var_def]>>
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
  fs[compile_single_def,LET_DEF]>>rw[]>>
  qpat_abbrev_tac`p1 = inst_select A B C`>>
  TRY(
    qpat_abbrev_tac`p2 = full_ssa_cc_trans n p1`>>
    qpat_abbrev_tac`p3 = three_to_two_reg p2`)>>
  TRY(qpat_abbrev_tac`p3= full_ssa_cc_trans n p1`)>>
  Q.ISPECL_THEN [`a`,`p3`,`k`,`col`,`st`] mp_tac word_alloc_correct>>
  (discharge_hyps>-
      (fs[even_starting_locals_def]>>
      rw[word_allocTheory.even_list_def,MEM_GENLIST,reg_allocTheory.is_phy_var_def]>>
      is_phy_var_tac)>>rw[LET_THM]>>
  Q.ISPECL_THEN [`p1`,`st with permute:= perm'`,`n`] assume_tac full_ssa_cc_trans_correct>>
  rfs[LET_THM]>>
  qexists_tac`perm''`>>
  Cases_on`evaluate(prog,st with permute:=perm'')`>>
  Cases_on`q=SOME Error`>>fs[]>>
  Q.ISPECL_THEN [`c`,`max_var prog +1`,`prog`,`st with permute:=perm''`,`q`,`r`,`st.locals`] mp_tac inst_select_thm)>>
  (discharge_hyps>-
    (simp[locals_rel_def]>>
    Q.SPEC_THEN `prog` assume_tac max_var_max>>
    match_mp_tac every_var_mono>>
    HINT_EXISTS_TAC>>fs[]>>
    DECIDE_TAC)>>
  rw[])>>
  `st with <|locals:=st.locals;permute:=perm''|> = st with permute:=perm''` by fs[state_component_equality]>>
  fs[]
  >-
    (split_pair_tac>>fs[]>>
    Q.ISPECL_THEN[`p2`,`st with permute:=perm'`,`res'`,`rcst`] mp_tac three_to_two_reg_correct>>
    discharge_hyps>-
      (rfs[]>>
      metis_tac[full_ssa_cc_trans_distinct_tar_reg])>>
    rw[]>>
    fs[word_state_eq_rel_def]>>
    Cases_on`q`>>fs[])
  >>
    split_pair_tac>>fs[]>>
    split_pair_tac>>fs[word_state_eq_rel_def]
    >- metis_tac[]>>
    FULL_CASE_TAC>>fs[]>>rfs[]);

val get_vars_code_frame = prove(``
  ∀ls.
  get_vars ls (st with code:=l) =
  get_vars ls st``,
  Induct>>fs[get_vars_def,get_var_def])

(*TODO: Move to wordProps so there're no scoping problems..*)
val word_exp_code_frame = prove(``
  ∀(s:('a,'b) wordSem$state) exp. word_exp (s with code:=l) exp =
          word_exp s (exp:'a wordLang$exp)``,
  ho_match_mp_tac wordSemTheory.word_exp_ind>>rw[word_exp_def]
  >-
    (every_case_tac>>fs[mem_load_def])
  >>
    `ws=ws'` by
      (unabbrev_all_tac>>
      fs[MAP_EQ_f])>>
    fs[])

val tac =
    fs[evaluate_def,LET_THM,state_component_equality]>>
    qexists_tac`st.permute`>>fs[alloc_def,get_var_def,gc_def,LET_THM,push_env_def,set_store_def,env_to_list_def,pop_env_def,has_space_def,call_env_def,set_var_def,get_var_def,dec_clock_def,jump_exc_def,get_vars_perm,get_vars_code_frame,set_vars_def,word_exp_perm,word_exp_code_frame,mem_store_def]>>
    every_case_tac>>fs[state_component_equality]

val rm_perm = prove(``
  s with permute:= s.permute = s``,fs[state_component_equality])

val size_tac= (fs[wordLangTheory.prog_size_def]>>DECIDE_TAC);

val find_code_thm = prove(``
  (!n v. lookup n st.code = SOME v ==>
         ∃t k a c col.
         lookup n l = SOME (SND (compile_single t k a c ((n,v),col)))) ∧
  find_code o1 (add_ret_loc o' x) st.code = SOME (args,prog) ⇒
  ∃t k a c col n prog'.
  SND(compile_single t k a c ((n,LENGTH args,prog),col)) = (LENGTH args,prog') ∧
  find_code o1 (add_ret_loc o' x) l = SOME(args,prog')``,
  Cases_on`o1`>>simp[find_code_def]>>rw[]
  >-
    (ntac 2 (TOP_CASE_TAC>>fs[])>>
    Cases_on`lookup n st.code`>>fs[]>>res_tac>>
    Cases_on`x'`>> fs[compile_single_def,LET_THM]>>
    qsuff_tac`q = LENGTH args`>-
     metis_tac[]>>
    qpat_assum`A=args` sym_sub_tac>>
    Cases_on`add_ret_loc o' x`>>fs[LENGTH_FRONT,ADD1])
  >>
    Cases_on`lookup x' st.code`>>fs[]>>res_tac>>
    Cases_on`x''`>>fs[compile_single_def,LET_THM]>>
    metis_tac[])

(*Adapted from a proof in wordProps*)
val domain_fromList2 = prove(``
  ∀q.
  domain(fromList2 q) = set(even_list (LENGTH q))``,
  recInduct SNOC_INDUCT >> rw [] >>
  fs[fromList2_def,word_allocTheory.even_list_def]>>
  simp[FOLDL_SNOC]>>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)>>
  fs [GSYM fromList2_def,FOLDL_SNOC]>>
  `!k. FST (FOLDL (λ(i,t) a. (i + 2,insert i a t)) (k,LN) l) =
        k + LENGTH l * 2` by
   (qspec_tac (`LN`,`t`) \\ qspec_tac (`l`,`l`) \\ Induct \\ fs [FOLDL]
    \\ fs [MULT_CLAUSES, AC ADD_COMM ADD_ASSOC])>>
  rw[]>>
  fs[MEM_GENLIST,EXTENSION]>>rw[]>>
  EQ_TAC>>rw[]
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
  Cases_on`b`>>TRY(PairCases_on`x`)>>fs[push_env_def,LET_THM,env_to_list_def])

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
  completeInduct_on`((st:('a,'b)state).clock)`>>
  simp[PULL_FORALL]>>
  completeInduct_on`prog_size (K 0) (prog:'a wordLang$prog)`>>
  rpt strip_tac>>
  fs[PULL_FORALL,evaluate_def]>>
  Cases_on`prog`
  >- tac
  >- tac
  >- cheat
  >- tac
  >- tac
  >- tac
  >- tac
  >- (*Call -- the hard case*)
    (fs[evaluate_def,LET_THM,get_vars_perm,get_vars_code_frame]>>
    Cases_on`get_vars l' st`>>fs[]>>
    Cases_on`find_code o1 (add_ret_loc o' x) st.code`>>fs[]>>
    Cases_on`o'`>>fs[]>>
    Cases_on`x'`>>simp[]>>
    imp_res_tac find_code_thm>>
    ntac 2 (pop_assum kall_tac)>>
    fs[]
    >- (*Tail calls*)
      (ntac 2 (IF_CASES_TAC>>fs[])
      >- simp[call_env_def,state_component_equality]>>
      qabbrev_tac`stt = call_env q(dec_clock st)`>>
      first_x_assum(qspecl_then[`stt`,`prog'`,`l`] mp_tac)>>
      discharge_hyps>-
        (fs[Abbr`stt`,dec_clock_def]>>
        DECIDE_TAC)>>
      discharge_hyps>-
        (fs[Abbr`stt`,call_env_def,dec_clock_def])>>
      rw[]>>
      Q.ISPECL_THEN [`n`,`r`,`LENGTH q`,`stt with permute:=perm'`] mp_tac (Q.GEN `name` compile_single_lem)>>
      discharge_hyps>-
        (fs[Abbr`stt`,call_env_def]>>
        simp[domain_fromList2])>>
      qpat_abbrev_tac`A = compile_single t k a c B`>>
      PairCases_on`A`>>rw[]>>fs[LET_THM]>>
      split_pair_tac>>fs[Abbr`stt`]
      >-
        (qexists_tac`perm''`>>fs[dec_clock_def,call_env_def])>>
      Cases_on`res`>>fs[]
      >-
        (qexists_tac`perm''`>>fs[dec_clock_def,call_env_def])>>
      Cases_on`x' = Error`>>fs[]
      >-
        (qexists_tac`perm''`>>fs[dec_clock_def,call_env_def])>>
      split_pair_tac>>fs[]>>
      rfs[]>>fs[]>>rfs[]>>
      split_pair_tac>>fs[]>>
      Q.ISPECL_THEN [`r`,`call_env q (dec_clock st) with permute:=perm''`,`rcst.permute`] mp_tac permute_swap_lemma>>fs[LET_THM]>>
      discharge_hyps>-
        (qpat_assum`A=res'` sym_sub_tac>>fs[])>>
      rw[]>>
      qexists_tac`perm'''`>>
      fs[call_env_def,dec_clock_def,word_state_eq_rel_def,state_component_equality])
    >>
    PairCases_on`x''`>>fs[]>>
    TOP_CASE_TAC>>fs[]>>
    IF_CASES_TAC>-
      fs[call_env_def,state_component_equality]>>
    fs[]>>
    qabbrev_tac`stt = call_env q(push_env x' o0 (dec_clock st))`>>
    first_assum(qspecl_then[`stt`,`prog'`,`l`] mp_tac)>>
    discharge_hyps>-
      (fs[Abbr`stt`,dec_clock_def]>>
      DECIDE_TAC)>>
    discharge_hyps>-
      fs[Abbr`stt`,push_env_code_frame,call_env_def,dec_clock_def]>>
    rw[]>>
    Q.ISPECL_THEN [`n`,`r`,`LENGTH q`,`stt with permute:=perm'`] mp_tac (Q.GEN `name` compile_single_lem)>>
    discharge_hyps>-
      (fs[Abbr`stt`,call_env_def]>>
      simp[domain_fromList2])>>
    qpat_abbrev_tac`A = compile_single t k a c B`>>
    PairCases_on`A`>>rw[]>>fs[LET_THM]>>
    split_pair_tac>>fs[Abbr`stt`]
    >-
      (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on`x''`)>>
      fs[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,ETA_AX])>>
    Cases_on`res`>>fs[]
    >-
      (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on`x''`)>>
      fs[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,ETA_AX])>>
    Cases_on`x''`>>fs[]
    >-
      (*Manual simulation for Result*)
      (Cases_on`w ≠ Loc x''3 x''4`>>fs[]
      >-
        (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
        Cases_on`o0`>>TRY(PairCases_on`x''`)>>
        fs[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,ETA_AX])
      >>
      Cases_on`pop_env rst`>>fs[]
      >-
        (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
        Cases_on`o0`>>TRY(PairCases_on`x''`)>>
        fs[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,ETA_AX])
      >>
      reverse (Cases_on`domain x''.locals = domain x'`)>>fs[]
      >-
        (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
        Cases_on`o0`>>TRY(PairCases_on`x'''`)>>
        fs[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,ETA_AX])
      >>
      split_pair_tac>>fs[]>>
      last_x_assum(qspecl_then[`(set_var x''0 w0 x'') with permute:=rcst.permute`,`x''2`,`l`]mp_tac)>>
      discharge_hyps>-
        (simp[set_var_def]>>
        (*Monotonicity on 12, and dec_clock*)
        `rst.clock < st.clock` by
          (imp_res_tac evaluate_clock>>
          fs[call_env_def,dec_clock_def]>>
          DECIDE_TAC)>>
        qpat_assum`A=SOME x''` mp_tac>>fs[pop_env_def]>>
        EVERY_CASE_TAC>>rw[state_component_equality]>>
        simp[])>>
      discharge_hyps>-
        (simp[set_var_def]>>
        qsuff_tac`x''.code = st.code`>>fs[]>>
        `x''.code =rst.code` by
          (qpat_assum`A=SOME x''` mp_tac>>fs[pop_env_def]>>
          EVERY_CASE_TAC>>rw[state_component_equality]>>simp[])>>
        split_pair_tac>>fs[]>>rfs[]>>
        fs[]>>
        split_pair_tac>>
        fs[state_component_equality,word_state_eq_rel_def,call_env_def,push_env_code_frame,dec_clock_def])>>
      rw[]>>
      qspecl_then[`r`,`call_env q(push_env x' o0 (dec_clock st)) with permute:=perm''`,`perm'''`] assume_tac permute_swap_lemma>>
      rfs[LET_THM]>>
      qexists_tac`λn. if n = 0:num then st.permute 0 else perm'''' (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on `x'''`)>>
      (fs[call_env_def,push_env_def,dec_clock_def,LET_THM,env_to_list_def,ETA_AX,pop_env_perm,set_var_perm]>>
      qpat_assum`((λ(res',rcst). P) A)` mp_tac>>
      split_pair_tac>>rfs[]>>fs[]>>
      `pop_env (rcst with code:=l) = SOME (x'' with <|code:=l;permute:=rcst.permute|>)` by
        (fs[pop_env_def,word_state_eq_rel_def]>>
        EVERY_CASE_TAC>>fs[]>>
        qpat_assum`A=x''` sym_sub_tac>>
        fs[state_component_equality])>>
      simp[]>>
      rw[]>>split_pair_tac>>fs[]>>
      split_pair_tac>>fs[set_var_def]>>
      `x''.code = rst.code` by
       (qpat_assum`A=SOME x''` mp_tac>>fs[pop_env_def]>>
        EVERY_CASE_TAC>>rw[state_component_equality]>>simp[])>>
      metis_tac[word_state_eq_rel_def]))
    >-
      cheat
    >>
      TRY(split_pair_tac>>fs[]>>
      Q.ISPECL_THEN [`r`,`call_env q (push_env x' o0 (dec_clock st)) with permute:=perm''`,`rcst.permute`] mp_tac permute_swap_lemma>>fs[LET_THM]>>
      discharge_hyps>-
        (qpat_assum`A=res'` sym_sub_tac>>fs[])>>
      rw[]>>
      qexists_tac`λn. if n = 0:num then st.permute 0 else perm''' (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on`x''`)>>
      fs[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,ETA_AX]>>
      split_pair_tac>>rfs[]>>fs[]>>
      rw[]>>fs[word_state_eq_rel_def,state_component_equality]>>NO_TAC)
    >>
      qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on`x''`)>>
      fs[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,ETA_AX])
  >- (*Seq, inductive*)
    (fs[evaluate_def,LET_THM,AND_IMP_INTRO]>>
    first_assum(qspecl_then[`p`,`st`,`l`] mp_tac)>>
    discharge_hyps>-size_tac>> rw[]>>
    split_pair_tac>>fs[]
    >- (qexists_tac`perm'`>>rw[]) >>
    split_pair_tac>>fs[]>>
    reverse (Cases_on`res`)>>fs[]
    >- (qexists_tac`perm'`>>fs[])>>
    (*Clock monotonicity*)
    `rst.clock ≤ st.clock` by
      (imp_res_tac evaluate_clock>>
      fs[state_component_equality])>>
    Cases_on`rst.clock = st.clock`>>
    TRY(first_assum(qspecl_then[`p0`,`rst`,`l`] mp_tac)>>
      discharge_hyps>-
      size_tac)>>
    TRY(first_assum(qspecl_then[`rst`,`p0`,`l`] mp_tac)>>
      discharge_hyps>-size_tac)>>
    rw[]>>
    qspecl_then[`p`,`st with permute:=perm'`,`perm''`]
      assume_tac permute_swap_lemma>>
    rfs[LET_THM]>>
    qexists_tac`perm'''`>>rw[]>>fs[])
  >- cheat
  >-
    (qexists_tac`st.permute`>>fs[rm_perm]>>
    fs[evaluate_def,get_var_perm,get_var_def]>>
    ntac 2 (TOP_CASE_TAC>>fs[])>>
    fs[alloc_def]>>
    TOP_CASE_TAC>>fs[]>>
    fs[push_env_def,env_to_list_def,LET_THM,set_store_def,gc_def]>>
    qpat_abbrev_tac`A = st.gc_fun B`>>
    Cases_on`A`>>fs[]>>
    PairCases_on`x'`>>fs[]>>
    qpat_abbrev_tac`A = dec_stack B C`>>
    Cases_on`A`>>fs[pop_env_def]>>
    Cases_on`x'`>>fs[]>>Cases_on`h`>>fs[]>>
    EVERY_CASE_TAC>>fs[has_space_def]>>
    rfs[call_env_def])
  >- tac
  >- tac
  >- tac
  >- (tac>>
     Cases_on`call_FFI st.ffi n x'`>>simp[]));

val compile_word_to_word_thm = store_thm("compile_word_to_word_thm",
  ``(!n v. lookup n st.code = SOME v ==>
           ∃t k a c col.
           lookup n l = SOME (SND (compile_single t k a c ((n,v),col)))) ==>
    ?perm'.
      let prog = Call NONE (SOME start) [0] NONE in
      let (res,rst) = evaluate (prog,st with permute := perm') in
        if res = SOME Error then T else
          let (res1,rst1) = evaluate (prog,st with code := l) in
            res1 = res /\ rst1.clock = rst.clock /\ rst1.ffi = rst.ffi``,
  simp[LET_THM]>>
  rw[]>>
  imp_res_tac compile_single_correct>>
  qpat_abbrev_tac`prog = Call A B C D`>>
  first_x_assum(qspec_then`prog` assume_tac)>>fs[LET_THM]>>
  qexists_tac`perm'`>>split_pair_tac>>fs[]>>
  split_pair_tac>>fs[]>>
  Cases_on`res`>>TRY(Cases_on`x`)>>fs[])
  |> SIMP_RULE std_ss [Once LET_THM]

val _ = export_theory();
