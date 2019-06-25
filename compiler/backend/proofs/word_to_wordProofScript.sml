(*
  Correctness proof for word_to_word
*)
open preamble word_to_wordTheory wordSemTheory word_simpProofTheory
     wordPropsTheory word_allocProofTheory word_instProofTheory
     word_removeProofTheory;

val good_dimindex_def = labPropsTheory.good_dimindex_def;

val _ = new_theory "word_to_wordProof";

val _ = bring_to_front_overload "Call" {Thy="wordLang",Name="Call"};
(*"*)

val is_phy_var_tac =
    full_simp_tac(srw_ss())[reg_allocTheory.is_phy_var_def]>>
    `0<2:num` by DECIDE_TAC>>
    `∀k.(2:num)*k=k*2` by DECIDE_TAC>>
    metis_tac[arithmeticTheory.MOD_EQ_0];

val rmd_thms = (remove_dead_conventions |>SIMP_RULE std_ss [LET_THM,FORALL_AND_THM])|>CONJUNCTS

Theorem FST_compile_single[simp]:
   FST (compile_single a b c d e) = FST (FST e)
Proof
  PairCases_on`e` \\ EVAL_TAC
QED

(*Chains up compile_single theorems*)
Theorem compile_single_lem:
    ∀prog n st.
  domain st.locals = set(even_list n) ∧
  gc_fun_const_ok st.gc_fun
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
    | _ => T
Proof
  full_simp_tac(srw_ss())[compile_single_def,LET_DEF]>>srw_tac[][]>>
  qpat_abbrev_tac`p1 = inst_select A B C`>>
  qpat_abbrev_tac`p2 = full_ssa_cc_trans n p1`>>
  TRY(
    qpat_abbrev_tac`p3 = FST (remove_dead p2 LN)`>>
    qpat_abbrev_tac`p4 = three_to_two_reg p3`)>>
  TRY(qpat_abbrev_tac`p4 = FST (remove_dead p2 LN)`)>>
  Q.ISPECL_THEN [`name`,`c`,`a`,`p4`,`k`,`col`,`st`] mp_tac word_alloc_correct>>
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
  pairarg_tac>>fs[]>>
  Cases_on`res=SOME Error`>>full_simp_tac(srw_ss())[]>>
  Q.ISPECL_THEN [`c`,`max_var (word_simp$compile_exp prog) +1`,`word_simp$compile_exp prog`,`st with permute:=perm''`,`res`,`rst`,`st.locals`] mp_tac inst_select_thm>>
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
  Q.ISPECL_THEN [`p2`,`LN:num_set`,`q`,`r`,`st with permute := perm'`,`st.locals`,`res'`,`rcst`] mp_tac evaluate_remove_dead>>
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
    Cases_on`res`>>full_simp_tac(srw_ss())[])
  >>
    pairarg_tac>>full_simp_tac(srw_ss())[word_state_eq_rel_def,state_component_equality]>>
    FULL_CASE_TAC>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]
QED

val tac =
    fs[evaluate_def,state_component_equality]>>
    qexists_tac`st.permute`>>
    fs[alloc_def,get_var_def,gc_def,push_env_def,set_store_def,env_to_list_def,pop_env_def,has_space_def,call_env_def,set_var_def,get_var_def,dec_clock_def,jump_exc_def,set_vars_def,mem_store_def]>>
    every_case_tac>>fs[state_component_equality]

val rm_perm = Q.prove(`
  s with permute:= s.permute = s`,full_simp_tac(srw_ss())[state_component_equality])

val size_tac= (full_simp_tac(srw_ss())[wordLangTheory.prog_size_def]>>DECIDE_TAC);

val find_code_thm = Q.prove(`
  (!n v. lookup n st.code = SOME v ==>
         ∃t k a c col.
         lookup n l = SOME (SND (compile_single t k a c ((n,v),col)))) ∧
  find_code o1 (add_ret_loc o' x) st.code = SOME (args,prog) ⇒
  ∃t k a c col n prog'.
  SND(compile_single t k a c ((n,LENGTH args,prog),col)) = (LENGTH args,prog') ∧
  find_code o1 (add_ret_loc o' x) l = SOME(args,prog')`,
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
    metis_tac[]);

val pop_env_termdep = Q.prove(`
  pop_env rst = SOME x ⇒ x.termdep = rst.termdep`,
  full_simp_tac(srw_ss())[pop_env_def]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[state_component_equality])

(* The t k a c parameters don't need to be existentially quantified *)
val code_rel_def = Define`
  code_rel stc ttc ⇔
  (!n v. lookup n stc = SOME v ==>
         ∃col t k a c.
         lookup n ttc = SOME (SND (compile_single t k a c ((n,v),col))))`

val compile_single_eta = Q.prove(`
  compile_single t k a c ((p,x),y) =
  (p,SND (compile_single t k a c ((p,x),y)))`,
  Cases_on`x`>>fs[compile_single_def]);

val code_rel_union_fromAList = Q.prove(`
  ∀s l ls.
  code_rel s l ∧
  domain s = domain l
  ⇒
  code_rel (union s (fromAList ls)) (union l (fromAList (MAP (λp. compile_single t k a c (p,NONE)) ls)))`,
  rw[code_rel_def]>>
  fs[lookup_union,case_eq_thms]
  >-
    (`lookup n l = NONE` by
      (fs[EXTENSION,domain_lookup]>>
      metis_tac[option_CLAUSES])>>
    fs[lookup_fromAList]>>
    simp[Once LAMBDA_PROD,Once compile_single_eta]>>
    simp[ALOOKUP_MAP_2]>>
    metis_tac[])
  >>
    first_x_assum drule>>rw[]>>
    simp[]>>metis_tac[]);

val compile_single_correct = Q.prove(`
  ∀prog (st:('a,'c,'ffi) wordSem$state) l coracle cc.
  code_rel st.code l /\
  (domain st.code = domain l) ∧
  (st.compile = λconf progs.
    cc conf (MAP (λp. compile_single tt kk aa co (p,NONE)) progs)) /\
  (coracle = (I ## MAP (λp. compile_single tt kk aa co (p,NONE))) o st.compile_oracle) ∧
  gc_fun_const_ok st.gc_fun
  ==>
  ∃perm'.
    let (res,rst) = evaluate (prog,st with <|permute := perm'|>) in
      if res = SOME Error then T
      else
        let (res1,rst1) = evaluate (prog,
          st with <|code := l; compile_oracle := coracle; compile:= cc|>) in
          res1 = res ∧
          code_rel rst.code rst1.code ∧
          domain rst.code = domain rst1.code ∧
          rst1 = rst with <|
            code:=rst1.code ;
            compile_oracle := (I ## MAP (λp. compile_single tt kk aa co (p,NONE))) o rst.compile_oracle;
            compile:=cc |>`, (* todo: rst1.perm? *)

  (*recInduct doesn't seem to give a nice induction thm*)
  completeInduct_on`((st:('a,'c,'ffi)wordSem$state).termdep)`>>
  completeInduct_on`((st:('a,'c,'ffi)wordSem$state).clock)`>>
  simp[PULL_FORALL]>>
  completeInduct_on`prog_size (K 0) (prog:'a wordLang$prog)`>>
  rpt strip_tac>>
  fs[PULL_FORALL,evaluate_def]>>
  Cases_on`prog`
  >- tac
  >- tac
  >- (Cases_on`i`>>
     fs[evaluate_def,inst_def,state_component_equality,assign_def,word_exp_perm,mem_load_def,get_var_perm,mem_store_def,get_var_def,get_vars_perm,LET_THM,get_fp_var_def]>>
     EVERY_CASE_TAC>>
     fs[set_var_def,set_fp_var_def]>>
     rw[])
  >- tac
  >- tac
  >- tac
  >- tac
  >-
    (* Must_Terminate *)
    (fs[evaluate_def,AND_IMP_INTRO]>>
    IF_CASES_TAC>>
    fs[]>>
    last_x_assum(qspecl_then[`st with <|clock:=MustTerminate_limit(:'a);termdep:=st.termdep-1|>`,`p`,`l`,`cc`] mp_tac)>>
    simp[]>>
    rw[]>>
    qexists_tac`perm'`>>fs[]>>
    pop_assum mp_tac >>
    rpt(pairarg_tac >> fs[])>>
    rw[]>> ntac 5 (pop_assum mp_tac) >>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    rw[] >> rw[]>>
    fs[state_component_equality])
  >- (*Call -- the hard case*)
    (fs[evaluate_def]>>
    TOP_CASE_TAC>>full_simp_tac(srw_ss())[]>>
    TOP_CASE_TAC>>full_simp_tac(srw_ss())[]>>
    Cases_on`find_code o1 (add_ret_loc o' x) st.code`>>full_simp_tac(srw_ss())[]>>
    Cases_on`o'`>>full_simp_tac(srw_ss())[]>>
    Cases_on`x'`>>simp[]>>
    imp_res_tac find_code_thm>>
    pop_assum(qspec_then`l` mp_tac)>>
    (impl_tac>-
      (fs[code_rel_def]>>
      metis_tac[]))>>
    rw[]>>
    rfs[]
    >- (*Tail calls*)
      (
      ntac 2 (IF_CASES_TAC>>full_simp_tac(srw_ss())[])
      >- simp[call_env_def,state_component_equality]>>
      qabbrev_tac`stt = call_env q(dec_clock st)`>>
      first_x_assum(qspecl_then[`stt`,`prog'`,`l`,`cc`] mp_tac)>>
      simp[AND_IMP_INTRO]>>
      impl_tac>-
        (full_simp_tac(srw_ss())[Abbr`stt`,dec_clock_def,call_env_def]>>
        DECIDE_TAC)>>
      srw_tac[][]>>
      Q.ISPECL_THEN [`n`,`r`,`LENGTH q`,`stt with permute:=perm'`] mp_tac (Q.GEN `name` compile_single_lem)>>
      impl_tac>-
        (full_simp_tac(srw_ss())[Abbr`stt`,call_env_def]>>
        simp[domain_fromList2,word_allocTheory.even_list_def,dec_clock_def])>>
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
      rw[]>>
      qpat_x_assum`(λ(x,y). _) _`mp_tac >>
      pairarg_tac>>fs[]>>
      qpat_x_assum`Abbrev( (_,_,_) = _)` (mp_tac o GSYM)>>
      simp[Once markerTheory.Abbrev_def]>>rw[]>>
      rw[]>>fs[dec_clock_def,call_env_def]>>
      qmatch_asmsub_abbrev_tac`evalute(r,stt)`>>
      Q.ISPECL_THEN [`r`,`stt`,`rcst.permute`] mp_tac permute_swap_lemma>>
      fs[]>>rw[]>>
      qexists_tac`perm'''`>>
      fs[Abbr`stt`,word_state_eq_rel_def,state_component_equality]>>
      fs[code_rel_def]>>
      metis_tac[])
    >>
    rename [‘find_code _ (add_ret_loc (SOME xx) _)’] >>
    ‘∃xn xnames xrh xl1 xl2. xx = (xn, xnames, xrh, xl1, xl2)’
       by (PairCases_on`xx`>>simp[]) >> rveq >> full_simp_tac(srw_ss())[]>>
    TOP_CASE_TAC>>full_simp_tac(srw_ss())[]>>
    TOP_CASE_TAC>>full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC>-
      fs[call_env_def,state_component_equality]>>
    fs[]>>
    qabbrev_tac`stt = call_env q(push_env x' o0 (dec_clock st))`>>
    first_assum(qspecl_then[`stt`,`prog'`,`l`,`cc`] mp_tac)>>
    impl_tac>-
      (fs[Abbr`stt`,dec_clock_def]>>
      DECIDE_TAC)>>
    impl_tac>-
      fs[Abbr`stt`,call_env_def,push_env_const,dec_clock_def]>>
    impl_tac>-
      fs[Abbr`stt`,call_env_def,dec_clock_def,push_env_gc_fun]>>
    rw[]>>
    Q.ISPECL_THEN [`n`,`r`,`LENGTH q`,`stt with permute:=perm'`] mp_tac (Q.GEN `name` compile_single_lem)>>
    impl_tac>-
      (full_simp_tac(srw_ss())[Abbr`stt`,call_env_def]>>
      simp[domain_fromList2,word_allocTheory.even_list_def,push_env_gc_fun,dec_clock_def])>>
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
      (Cases_on`w ≠ Loc xl1 xl2`>>full_simp_tac(srw_ss())[]
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
      last_x_assum kall_tac>>
      qpat_x_assum`(λ(x,y). _) _`mp_tac >>
      pairarg_tac>>full_simp_tac(srw_ss())[]>>
      strip_tac >>
      last_x_assum(qspecl_then[`(set_var xn w0 x'') with permute:=rcst.permute`,`xrh`,`rst1.code`,`cc`]mp_tac)>>
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
        imp_res_tac pop_env_code_gc_fun_clock>>fs[]>>
        imp_res_tac evaluate_consts>>fs[dec_clock_def]>>
        fs[word_state_eq_rel_def]>>
        metis_tac[])>>
      rw[]>>
      Q.ISPECL_THEN[`r`,`call_env q(push_env x' o0 (dec_clock st)) with permute:=perm''`,`perm'''`] assume_tac permute_swap_lemma>>
      rfs[]>>
      qexists_tac`λn. if n = 0:num then st.permute 0 else perm'''' (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on `x'''`)>>
      (fs[call_env_def,push_env_def,dec_clock_def,env_to_list_def,ETA_AX,pop_env_perm,set_var_perm]>>
      qpat_x_assum`((λ(res',rcst). P) A)` mp_tac>>
      pairarg_tac>>rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[]>>
      `pop_env rst1 =
        SOME (x'' with <|compile:= cc;
                         compile_oracle :=
           (I ## MAP (λp. compile_single tt kk aa co (p,NONE))) ∘
           x''.compile_oracle;
           code:=rst1.code; permute:=rcst.permute|>)` by
        (fs[pop_env_def,word_state_eq_rel_def]>>
        qpat_x_assum`rst1 = _` SUBST_ALL_TAC>>
        simp[]>>
        EVERY_CASE_TAC>>fs[state_component_equality])>>
      simp[]>>
      rw[]>>
      pairarg_tac>>fs[set_var_def]))
    >-
      (*Manual simulation for Exceptions*)
      (Cases_on`o0`>>full_simp_tac(srw_ss())[]
      >-
        (pop_assum mp_tac >> pairarg_tac>>full_simp_tac(srw_ss())[]>>
        strip_tac >>
        qmatch_assum_abbrev_tac `evaluate(r,A) = _`>>
        Q.ISPECL_THEN [`r`,`A`,`rcst.permute`] mp_tac permute_swap_lemma>>
        simp[Abbr`A`]>>
        impl_tac>-
          (qpat_x_assum`B=res'` sym_sub_tac>>full_simp_tac(srw_ss())[])>>
        rw[]>>
        qexists_tac`λn. if n = 0:num then st.permute 0 else perm''' (n-1)`>>
        fs[push_env_def,env_to_list_def,dec_clock_def,call_env_def,ETA_AX]>>
        qpat_x_assum`(λ(x,y). _) _`mp_tac >>
        pairarg_tac>>rfs[]>>fs[]>>
        rw[]>>fs[word_state_eq_rel_def,state_component_equality]>>
        metis_tac[])
      >>
      qmatch_goalsub_rename_tac`push_env _ (SOME p)` >>
      PairCases_on`p`>>full_simp_tac(srw_ss())[]>>
      Cases_on`w ≠ Loc p2 p3`
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
      last_x_assum kall_tac>>
      qpat_x_assum`(λ(x,y). _) _`mp_tac >>
      pairarg_tac>>full_simp_tac(srw_ss())[]>>
      strip_tac >>
      last_x_assum(qspecl_then[`(set_var p0 w0 rst) with permute:=rcst.permute`,`p1`,`rst1.code`,`cc`]mp_tac)>>
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
        imp_res_tac pop_env_code_gc_fun_clock>>fs[]>>
        imp_res_tac evaluate_consts>>fs[dec_clock_def]>>
        fs[word_state_eq_rel_def]>>
        metis_tac[])>>
      rw[]>>
      Q.ISPECL_THEN[`r`,`call_env q(push_env x' (SOME (p0,p1,p2,p3)) (dec_clock st)) with permute:=perm''`,`perm'''`] assume_tac permute_swap_lemma>>
      rfs[]>>
      qexists_tac`λn. if n = 0:num then st.permute 0 else perm'''' (n-1)`>>
      fs[call_env_def,push_env_def,dec_clock_def,env_to_list_def,ETA_AX,pop_env_perm,set_var_perm]>>
      `domain rst1.locals = domain x'` by
        (qpat_x_assum`rst1=_` SUBST_ALL_TAC>>rw[])>>
      simp[]>>
      pairarg_tac>>fs[]>>
      qpat_x_assum`rst1=_` SUBST_ALL_TAC>>fs[]>>
      rpt(pairarg_tac>>fs[])>>
      fs[set_var_def]>>
      pop_assum mp_tac>>
      qmatch_goalsub_abbrev_tac`_ (evaluate (_,A))`>>
      qmatch_asmsub_abbrev_tac`_ (evaluate (_,B))`>>
      strip_tac>>
      `A = B` by
        (unabbrev_all_tac>>fs[state_component_equality,word_state_eq_rel_def])>>
      rfs[]>>
      unabbrev_all_tac>>fs[])
    >>
      TRY(
      pop_assum mp_tac >> pairarg_tac>>
      fs[]>>
      Q.ISPECL_THEN [`r`,`call_env q (push_env x' o0 (dec_clock st)) with permute:=perm''`,`rcst.permute`] mp_tac permute_swap_lemma>>
      fs[]>>rw[]>>
      qexists_tac`λn. if n = 0:num then st.permute 0 else perm''' (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on`x''`)>>
      fs[push_env_def,env_to_list_def,dec_clock_def,call_env_def,ETA_AX]>>
      qpat_x_assum`(λ(a,b). _) _`mp_tac >>
      pairarg_tac>>rfs[]>>
      fs[]>>rw[]>>
      fs[word_state_eq_rel_def,state_component_equality]>>
      metis_tac[])
    >>
      qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on`x''`)>>
      fs[push_env_def,env_to_list_def,dec_clock_def,call_env_def,ETA_AX])

  >- (*Seq, inductive*)
    (fs[evaluate_def,LET_THM,AND_IMP_INTRO]>>
    first_assum(qspecl_then[`p`,`st`,`l`,`cc`] mp_tac)>>
    impl_tac>-
      size_tac>>
    rw[]>>
    pop_assum mp_tac >>
    pairarg_tac>>fs[]>>
    strip_tac
    >- (qexists_tac`perm'`>>srw_tac[][]) >>
    pop_assum mp_tac >>
    pairarg_tac>>fs[]>>
    strip_tac >>
    reverse (Cases_on`res`)>>fs[]
    >- (qexists_tac`perm'`>>fs[])>>
    full_simp_tac std_ss [GSYM PULL_FORALL]>>
    (*Clock monotonicity*)
    `rst.clock ≤ st.clock ∧ rst.termdep = st.termdep` by
      (imp_res_tac evaluate_clock>>
      full_simp_tac(srw_ss())[state_component_equality])>>
    Cases_on`rst.clock = st.clock`
    >-
      (first_x_assum(qspecl_then[`p0`,`rst`,`rst1.code`,`cc`] mp_tac)>>
      impl_tac>-(
        imp_res_tac evaluate_consts>>
        fs[]>>
        size_tac)>>
      rw[]>>
      Q.ISPECL_THEN[`p`,`st with permute:=perm'`,`perm''`]
        assume_tac permute_swap_lemma>>
      rfs[]>>
      qexists_tac`perm'''`>>
      rw[]>>fs[]>>
      pairarg_tac>>fs[]>>
      qpat_x_assum`rst1 = _` SUBST_ALL_TAC>>fs[])
    >>
      first_x_assum(qspecl_then[`rst`,`p0`,`rst1.code`,`cc`] mp_tac)>>
      impl_tac>- (
        imp_res_tac evaluate_consts>>
        fs[]>>
        size_tac)>>
      rw[]>>
      Q.ISPECL_THEN[`p`,`st with permute:=perm'`,`perm''`]
        assume_tac permute_swap_lemma>>
      rfs[]>>
      qexists_tac`perm'''`>>
      rw[]>>fs[]>>
      pairarg_tac>>fs[]>>
      qpat_x_assum`rst1 = _` SUBST_ALL_TAC>>fs[])
  >-
    (simp[evaluate_def,get_var_def,get_var_imm_def]>>
    ntac 2 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
    Cases_on`r`>>full_simp_tac(srw_ss())[get_var_imm_def,get_var_def]>>
    rpt(TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
    TRY(qpat_abbrev_tac`prog = p`)>>
    TRY(qpat_abbrev_tac`prog = p0`)>>
    first_x_assum(qspecl_then[`prog`,`st`,`l`,`cc`] mp_tac)>>
    (impl_tac>-size_tac>>srw_tac[][]))
  >-
    (qexists_tac`st.permute`>>fs[rm_perm]>>
    fs[evaluate_def,get_var_def]>>
    ntac 2 (TOP_CASE_TAC>>fs[])>>
    fs[alloc_def]>>
    TOP_CASE_TAC>>fs[]>>
    fs[push_env_def,env_to_list_def,set_store_def,gc_def]>>
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
  >- (tac \\ fs[domain_lookup] \\ metis_tac[] )
  >- (* Install *)
    (qexists_tac`st.permute`>>fs[rm_perm]>>
    ntac 3 (last_x_assum kall_tac)>>
    simp[evaluate_def]>>
    ntac 9 (TOP_CASE_TAC>>fs[])>>
    Cases_on`st.compile_oracle 0`>>fs[]>>
    ntac 4 (TOP_CASE_TAC>>fs[])>>
    Cases_on`r`>>fs[]>>
    ntac 3 (TOP_CASE_TAC>>fs[])>>
    PairCases_on`h`>>fs[compile_single_def,shift_seq_def]>>
    TOP_CASE_TAC>>fs[]>>
    conj_tac>-
      (drule (GEN_ALL code_rel_union_fromAList)>>
      simp[]>>
      disch_then(qspecl_then[`tt`,`kk`,`co`,`aa`,`(h0,h1,h2)::t`] assume_tac)>>
      fs[compile_single_def])>>
    conj_tac>-
      (simp[domain_union]>>AP_TERM_TAC>>
      simp[domain_fromAList]>>AP_TERM_TAC>>
      simp[EXTENSION,MAP_MAP_o,compile_single_def,MEM_MAP,EXISTS_PROD])>>
    simp[state_component_equality,o_DEF])
  >- (*CBW*) tac
  >- (*DBW*) tac
  >- (*FFI*)
    (tac>>
     Cases_on`call_FFI st.ffi s x'' x'`>>simp[]));

Theorem compile_word_to_word_thm:
     code_rel (st:('a,'c,'ffi) wordSem$state).code l ∧
  (domain st.code = domain l) ∧
  (st.compile = λconf progs.
    cc conf (MAP (λp. full_compile_single tt kk aa co (p,NONE)) progs)) ∧
  (coracle = (I ## MAP (λp. full_compile_single tt kk aa co (p,NONE))) o st.compile_oracle) ∧
  gc_fun_const_ok st.gc_fun ==>
  ?perm' clk.
    let prog = Call NONE (SOME start) [0] NONE in
    let (res,rst) = evaluate (prog,st with permute := perm') in
      if res = SOME Error then T else
      let (res1,rst1) = evaluate (prog,
        st with <|code           := map (I ## remove_must_terminate) l;
                  clock          :=st.clock+clk;
                  termdep        :=0;
                  compile        := cc;
                  compile_oracle := coracle
                  |>)
      in
        res1 = res /\ rst1.clock = rst.clock /\ rst1.ffi = rst.ffi
Proof
  simp[]>>rw[]>>
  qpat_abbrev_tac`prog = Call _ _ _ _`>>
  drule compile_single_correct>>fs[]>>
  disch_then(qspecl_then[`prog`,`λconf. cc conf o ((MAP (I ## I ## remove_must_terminate)))`] mp_tac)>>
  impl_tac>-(
    simp[FUN_EQ_THM,full_compile_single_def,LAMBDA_PROD,MAP_MAP_o,o_DEF]>>
    rw[]>>AP_TERM_TAC>>
    simp[MAP_EQ_f,FORALL_PROD]>>rw[]>>
    pairarg_tac>>fs[])>>
  rw[]>>
  qexists_tac`perm'`>>pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  Cases_on`res=SOME Error`>>fs[]>>
  drule (GEN_ALL word_remove_correct)>>fs[]>>
  disch_then(qspec_then`cc` assume_tac)>>rfs[]>>
  qexists_tac`clk`>>
  fs[Abbr`prog`,word_removeTheory.remove_must_terminate_def,compile_state_def]>>
  qmatch_asmsub_abbrev_tac`evaluate (_,sa) = (res,_)`>>
  qmatch_goalsub_abbrev_tac`evaluate (_,sb)`>>
  `sa = sb` by
    (unabbrev_all_tac>>fs[state_component_equality,FUN_EQ_THM]>>rw[]>>
    Cases_on`st.compile_oracle x`>>
    fs[MAP_MAP_o,o_DEF,LAMBDA_PROD,full_compile_single_def]>>
    rw[MAP_EQ_f,FORALL_PROD]>>pairarg_tac>>fs[])>>
  fs[]>>fs[state_component_equality]
QED

val rmt_thms = (remove_must_terminate_conventions|>SIMP_RULE std_ss [LET_THM,FORALL_AND_THM])|>CONJUNCTS

(* syntax going into stackLang *)
Theorem compile_to_word_conventions:
    let (_,progs) = compile wc ac p in
  MAP FST progs = MAP FST p ∧
  EVERY2 labels_rel (MAP (extract_labels o SND o SND) p)
                    (MAP (extract_labels o SND o SND) progs) ∧
  EVERY (λ(n,m,prog).
    flat_exp_conventions prog ∧
    post_alloc_conventions (ac.reg_count - (5+LENGTH ac.avoid_regs)) prog ∧
    (EVERY (λ(n,m,prog). every_inst (inst_ok_less ac) prog) p ∧
     addr_offset_ok ac 0w ⇒ full_inst_ok_less ac prog) ∧
    (ac.two_reg_arith ⇒ every_inst two_reg_inst prog)) progs
Proof
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
  CONJ_TAC>-
    (match_mp_tac (el 3 rmt_thms)>>
    match_mp_tac pre_post_conventions_word_alloc>>
    IF_CASES_TAC>>
    TRY(match_mp_tac three_to_two_reg_pre_alloc_conventions)>>
    match_mp_tac (el 3 rmd_thms)>>
    fs[full_ssa_cc_trans_pre_alloc_conventions])>>
  CONJ_TAC>-
    (rw[]>>match_mp_tac (el 2 rmt_thms)>>
    match_mp_tac word_alloc_full_inst_ok_less>>
    TRY(match_mp_tac three_to_two_reg_full_inst_ok_less)>>
    match_mp_tac (el 2 rmd_thms)>>
    match_mp_tac full_ssa_cc_trans_full_inst_ok_less>>
    match_mp_tac inst_select_full_inst_ok_less>>
    fs[]>>
    metis_tac[compile_exp_no_inst,MEM_EL])>>
  rw[]>>
  match_mp_tac (el 4 rmt_thms)>>
  match_mp_tac word_alloc_two_reg_inst>>
  fs[three_to_two_reg_two_reg_inst]
QED

val _ = export_theory();
