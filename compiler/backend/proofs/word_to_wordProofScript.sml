(*
  Correctness proof for word_to_word
*)
Theory word_to_wordProof
Ancestors
  word_to_word wordSem word_simpProof wordProps wordConvs
  word_allocProof word_instProof word_unreach word_removeProof
  word_cseProof word_elim word_elimProof word_unreachProof
  word_copyProof wordConvsProof
Libs
  preamble

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val _ = bring_to_front_overload "Call" {Thy="wordLang",Name="Call"};

val is_phy_var_tac =
    full_simp_tac(srw_ss())[reg_allocTheory.is_phy_var_def]>>
    `0<2:num` by DECIDE_TAC>>
    `∀k.(2:num)*k=k*2` by DECIDE_TAC>>
    metis_tac[arithmeticTheory.MOD_EQ_0];

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
  fs[compile_single_def,LET_DEF]>>
  rpt strip_tac>>
  qpat_abbrev_tac`p0 = word_simp$compile_exp prog`>>
  qpat_abbrev_tac`p1 = inst_select A B C`>>
  qpat_abbrev_tac`p2 = full_ssa_cc_trans n p1`>>
  qpat_abbrev_tac`p3 = remove_dead_prog p2`>>
  qpat_abbrev_tac`p4 = copy_prop (word_common_subexp_elim p3)`>>
  qpat_abbrev_tac`p5 = three_to_two_reg_prog _ p4`>>
  qpat_abbrev_tac`p6 = remove_unreach p5`>>
  qpat_abbrev_tac`p7 = remove_dead_prog p6`>>
  Q.ISPECL_THEN [`name`,`c`,`a`,`p7`,`k`,`col`,`st`]
    mp_tac word_alloc_correct>>
  impl_tac >- (
    fs[even_starting_locals_def]>>
    rw[word_allocTheory.even_list_def,MEM_GENLIST,reg_allocTheory.is_phy_var_def]
    >- is_phy_var_tac>>
    unabbrev_all_tac>>fs[full_ssa_cc_trans_wf_cutsets]>>
    irule (remove_dead_prog_conventions |> CONJUNCTS |> el 5)>>
    irule wf_cutsets_remove_unreach >>
    irule three_to_two_reg_prog_wf_cutsets>>
    irule wf_cutsets_copy_prop>>
    irule wf_cutsets_word_common_subexp_elim >>
    irule (remove_dead_prog_conventions |> CONJUNCTS |> el 5)>>
    fs[full_ssa_cc_trans_wf_cutsets])>>
  rw[]>>

  (* SSA *)
  Q.ISPECL_THEN [`p1`,`st with permute:= perm'`,`n`] assume_tac full_ssa_cc_trans_correct>>
  gvs[]>>
  qexists_tac`perm''`>>
  pairarg_tac>>fs[]>>
  Cases_on`res=SOME Error`>>gs[]>>

  (* inst select *)
  Q.ISPECL_THEN [`c`,`max_var p0 +1`,`p0`,`st with permute:=perm''`,`res`,`rst`,`st.locals`] mp_tac inst_select_thm>>
  impl_tac >- (
    old_drule (GEN_ALL word_simpProofTheory.compile_exp_thm) \\ fs [] \\ strip_tac \\
    simp[locals_rel_def]>>
    Q.SPEC_THEN `p0` assume_tac max_var_max>>
    irule every_var_mono>>
    first_x_assum (irule_at Any)>>
    fs[])>>
  rw[]>>
  `∀perm. st with <|locals:=st.locals;permute:=perm|> = st with permute:=perm`
    by fs[state_component_equality]>>
  gvs[]>>
  qpat_x_assum`(λ(x,y). _) _`mp_tac >>
  pairarg_tac>>fs[]>>
  strip_tac>>
  rw[]>>

  (* first remove_dead *)
  drule_at (Pos (el 2)) evaluate_remove_dead_prog>>
  simp[]>>
  impl_keep_tac >- (
    (* requires flat_exp_conventions up to p2 *)
    unabbrev_all_tac >>
    irule full_ssa_cc_trans_flat_exp_conventions >>
    fs [inst_select_flat_exp_conventions])>>
  rw[]>>

  (* word cse *)
  old_drule word_common_subexp_elim_correct >>
  impl_keep_tac >- (
    fs [] >>
    (* requires flat_exp_conventions up to p3 *)
    unabbrev_all_tac >>
    irule (remove_dead_prog_conventions |> CONJUNCTS |> el 1)>>
    fs[])>>
  gvs [] >>

  (* word_copy *)
  strip_tac >>
  `evaluate (p4, st with permute := perm') = (res, rcst with locals := t')` by
    (simp[Abbr `p4`] >> simp[Once evaluate_copy_prop] >> gvs[]) >>
  (* three_to_two_reg_prog *)
  old_drule evaluate_three_to_two_reg_prog>>
  simp[]>>
  impl_tac >- (
    (* requires every_inst distinct_tar_reg up to p4 *)
    gvs[]>>
    unabbrev_all_tac>>
    irule every_inst_distinct_tar_reg_copy_prop>>
    irule every_inst_distinct_tar_reg_word_common_subexp_elim >>
    irule (remove_dead_prog_conventions |> CONJUNCTS |> el 4)>>
    fs [full_ssa_cc_trans_distinct_tar_reg])>>
  rw[]>>

  (* word_unreach *)
  `evaluate (p6,st with permute := perm') = (res,rcst with locals:=t')` by (
    rw[Abbr`p6`]>>
    simp[evaluate_remove_unreach])>>

  (* second remove_dead *)
  drule_at (Pos (el 2)) evaluate_remove_dead_prog>>
  simp[]>>
  impl_tac >- (
    unabbrev_all_tac >>
    irule flat_exp_conventions_remove_unreach>>
    irule three_to_two_reg_prog_flat_exp_conventions>>
    irule flat_exp_conventions_copy_prop>>
    irule flat_exp_conventions_word_common_subexp_elim>>
    fs[])>>
  simp[]>>
  strip_tac>>
  pairarg_tac>>gvs[word_state_eq_rel_def]>>
  every_case_tac>>gvs[]
QED

Theorem rm_perm[local]:
  s with permute:= s.permute = s
Proof
  full_simp_tac(srw_ss())[state_component_equality]
QED

val size_tac= (full_simp_tac(srw_ss())[wordLangTheory.prog_size_def]>>DECIDE_TAC);

Theorem find_code_thm[local]:
  (!n v. lookup n st.code = SOME v ==>
         ∃t k a c col.
         lookup n l = SOME (SND (compile_single t k a c ((n,v),col)))) ∧
  find_code o1 (add_ret_loc o' x) st.code st.stack_size = SOME (args,prog, locsize) ⇒
  ∃t k a c col n prog'.
  SND(compile_single t k a c ((n,LENGTH args,prog),col)) = (LENGTH args,prog') ∧
  find_code o1 (add_ret_loc o' x) l st.stack_size = SOME(args,prog', locsize)
Proof
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
    metis_tac[]
QED

Theorem pop_env_termdep[local]:
  pop_env rst = SOME x ⇒ x.termdep = rst.termdep
Proof
  full_simp_tac(srw_ss())[pop_env_def]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[state_component_equality]
QED

(* The t k a c parameters don't need to be existentially quantified *)
Definition code_rel_def:
  code_rel stc ttc ⇔
  (!n v. lookup n stc = SOME v ==>
         ∃col t k a c.
         lookup n ttc = SOME (SND (compile_single t k a c ((n,v),col))))
End

Theorem compile_single_eta[local]:
  compile_single t k a c ((p,x),y) =
  (p,SND (compile_single t k a c ((p,x),y)))
Proof
  Cases_on`x`>>fs[compile_single_def]
QED


Theorem code_rel_union_fromAList[local]:
  ∀s l ls.
  code_rel s l ∧
  domain s = domain l
  ⇒
  code_rel (union s (fromAList ls)) (union l (fromAList (MAP (λp. compile_single t k a c (p,NONE)) ls)))
Proof
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
    first_x_assum old_drule>>rw[]>>
    simp[]>>metis_tac[]
QED

Theorem compile_single_correct[local]:
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
            compile:=cc |> (* todo: rst1.perm? *)
Proof
  (*recInduct doesn't seem to give a nice induction thm*)
  completeInduct_on`((st:('a,'c,'ffi)wordSem$state).termdep)`>>
  completeInduct_on`((st:('a,'c,'ffi)wordSem$state).clock)`>>
  simp[PULL_FORALL]>>
  completeInduct_on`prog_size (K 0) (prog:'a wordLang$prog)`>>
  rpt strip_tac>>
  fs[PULL_FORALL,evaluate_def]>>
  Cases_on`prog`
  >- fs[evaluate_def,state_component_equality]
  >- (fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
      simp[state_component_equality])
  >- (fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
      old_drule inst_const_full >> simp[state_component_equality])
  >- (fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
      simp[state_component_equality])
  >- (fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
      simp[state_component_equality])
  >- (fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
      simp[state_component_equality])
  >- (fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
      old_drule mem_store_const >> simp[state_component_equality])
  >- (
    (* Must_Terminate *)
    fs[evaluate_def,AND_IMP_INTRO]>>
    rpt (TOP_CASE_TAC >> fs[]) >>
    last_x_assum(qspecl_then[`st with <|clock:=MustTerminate_limit(:'a);termdep:=st.termdep-1|>`,`p`,`l`,`cc`] mp_tac)>>
    impl_tac >-  simp[]>>
    rw[]>>
    qexists_tac`perm'`>>fs[]>>
    pop_assum mp_tac >>
    rpt(pairarg_tac >> fs[])>>
    rw[]>> ntac 5 (pop_assum mp_tac) >>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    rw[] >> rw[]>>
    fs[state_component_equality])
  >- ( (*Call -- the hard case*)
    fs[evaluate_def,AND_IMP_INTRO]>>
    ntac 2 (TOP_CASE_TAC>> fs[]) >>
    Cases_on`find_code o1 (add_ret_loc o' x) st.code st.stack_size`>>
    fs []>>
    Cases_on`o'`>>full_simp_tac(srw_ss())[]>>
    Cases_on`x'`>>simp[]>>
    Cases_on `r` >> simp [] >>
    imp_res_tac find_code_thm>>
    pop_assum(qspec_then`l` mp_tac)>>
    (impl_tac>-
      (fs[code_rel_def]>>
      metis_tac[]))>>
    rw[]>> rfs[]
    >- ( (*Tail calls*)
      ntac 2 (TOP_CASE_TAC >>full_simp_tac(srw_ss())[])
      >- simp[flush_state_def,state_component_equality] >>
      qabbrev_tac`stt = call_env q r' (dec_clock st)`>>
      first_x_assum(qspecl_then[`stt`,`prog'`,`l`,`cc`] mp_tac)>>
      impl_tac>-
        (full_simp_tac(srw_ss())[Abbr`stt`,dec_clock_def]>>
        DECIDE_TAC)>>
      srw_tac[][]>>
      Q.ISPECL_THEN [`n`,`q'`,`LENGTH q`,`stt with permute:=perm'`]
       mp_tac (Q.GEN `name` compile_single_lem)>>
      impl_tac>-
        (full_simp_tac(srw_ss())[Abbr`stt`,call_env_def]>>
        simp[domain_fromList2,word_allocTheory.even_list_def])>>
      qpat_abbrev_tac`A = compile_single t k a c B`>>
      PairCases_on`A`>>srw_tac[][]>>full_simp_tac(srw_ss())[LET_THM]>>
      pop_assum mp_tac>>
      pairarg_tac>>full_simp_tac(srw_ss())[Abbr`stt`] >>
      strip_tac
      >-
        (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def])>>
      Cases_on`res`>>full_simp_tac(srw_ss())[]
      >-
        (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def])>>
      Cases_on`x' = Error`>>full_simp_tac(srw_ss())[]
      >-
        (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def])>>
      ntac 2 (pop_assum mp_tac) >>
      pairarg_tac>>full_simp_tac(srw_ss())[]>>
      rw[]>>
      qpat_x_assum`(λ(x,y). _) _`mp_tac >>
      pairarg_tac>>fs[]>>
      qpat_x_assum`Abbrev( (_,_,_) = _)` (mp_tac o GSYM)>>
      simp[Once markerTheory.Abbrev_def]>>rw[]>>
      rw[]>>fs[dec_clock_def,call_env_def,flush_state_def]>>
      qmatch_asmsub_abbrev_tac`evaluate (q',stt)`>>
      Q.ISPECL_THEN [`q'`,`stt`,`rcst.permute`] mp_tac permute_swap_lemma>>
      fs[]>>rw[]>>
      qexists_tac`perm'''`>>
      fs[Abbr`stt`,word_state_eq_rel_def,state_component_equality]>>
      fs[code_rel_def]>>
      metis_tac[]) >>
    rename [‘find_code _ (add_ret_loc (SOME xx) _)’] >>
    ‘∃xn xnames xrh xl1 xl2. xx = (xn, xnames, xrh, xl1, xl2)’
       by (PairCases_on`xx`>>simp[]) >> rveq >> full_simp_tac(srw_ss())[]>>
    ntac 2 (TOP_CASE_TAC>>fs[]) >>
    IF_CASES_TAC>-
      (Cases_on `o0` >> TRY (PairCases_on `x''`) >>
       fs[call_env_def,flush_state_def,state_component_equality,
        stack_size_def, stack_size_frame_def, push_env_def, env_to_list_def, LET_THM])>>
    fs[]>>
    qabbrev_tac`stt = call_env q r' (push_env x' o0 (dec_clock st))`>>
    first_assum(qspecl_then[`stt`,`prog'`,`l`,`cc`] mp_tac)>>
    impl_tac>-
      (fs[Abbr`stt`,dec_clock_def]>>
      DECIDE_TAC)>>
    rw[]>>
    Q.ISPECL_THEN [`n`,`q'`,`LENGTH q`,`stt with permute:=perm'`] mp_tac
      (Q.GEN `name` compile_single_lem)>>
    impl_tac>-
      (full_simp_tac(srw_ss())[Abbr`stt`,call_env_def] >>
      simp[domain_fromList2,word_allocTheory.even_list_def])>>
    qpat_abbrev_tac`A = compile_single t k a c B`>>
    PairCases_on`A`>>srw_tac[][]>>full_simp_tac(srw_ss())[LET_THM]>>
    pop_assum mp_tac >>
    pairarg_tac>>full_simp_tac(srw_ss())[Abbr`stt`] >>
    strip_tac
    >-
      (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on`x''`)>>
      full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,flush_state_def,ETA_AX])>>
    Cases_on`res`>>full_simp_tac(srw_ss())[]
    >-
      (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on`x''`)>>
      full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,flush_state_def,ETA_AX])>>
    Cases_on`x''`>>full_simp_tac(srw_ss())[]
    >-
      (*Manual simulation for Result*)
      (Cases_on`w = Loc xl1 xl2 ⇒ LENGTH l'' ≠ LENGTH xn`>>full_simp_tac(srw_ss())[]
      >-
        (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
        Cases_on`o0`>>TRY(PairCases_on`x''`)>>
        full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,flush_state_def,ETA_AX])
      >>
      Cases_on`pop_env rst`>>full_simp_tac(srw_ss())[]
      >-
        (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
        Cases_on`o0`>>TRY(PairCases_on`x''`)>>
        full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,flush_state_def,ETA_AX])
      >>
      reverse (Cases_on`domain x''.locals = domain (FST x') ∪ domain (SND x')`)>>full_simp_tac(srw_ss())[]
      >-
        (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
        Cases_on`o0`>>TRY(PairCases_on`x'''`)>>
        full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,flush_state_def,ETA_AX])
      >>
      qpat_x_assum`(λ(x,y). _) _`mp_tac >>
      pairarg_tac>>full_simp_tac(srw_ss())[]>>
      strip_tac >>
      last_x_assum kall_tac>>
      qpat_x_assum`(λ(x,y). _) _`mp_tac >>
      pairarg_tac>>full_simp_tac(srw_ss())[]>>
      strip_tac >>
      last_x_assum(qspecl_then[`(set_vars xn l'' x'') with permute:=rcst.permute`,`xrh`,`rst1.code`,`cc`]mp_tac)>>
      impl_tac>-
        (simp[]>>
        (*Monotonicity on 12, and dec_clock*)
        `rst.clock < st.clock` by
          (imp_res_tac evaluate_clock>>
          full_simp_tac(srw_ss())[call_env_def,flush_state_def,dec_clock_def]>>
          DECIDE_TAC)>>
       (*Why are there 3 different lemmas*)
        old_drule pop_env_const >> fs[] >> disch_then kall_tac >>
        old_drule pop_env_termdep>> fs[] >> disch_then kall_tac >>
        old_drule pop_env_code_gc_fun_clock >>
        disch_then (mp_tac o LIST_CONJ o (map SYM) o CONJUNCTS) >>
        fs[] >> disch_then kall_tac >>
        (*Yet another duplication*)
        imp_res_tac evaluate_consts >> fs[] >>
        imp_res_tac evaluate_clock >> fs[] >>
        fs[word_allocProofTheory.word_state_eq_rel_def]>>
        gs[])>>
      rw[]>>
      Q.ISPECL_THEN[`q'`,`call_env q r' (push_env x' o0 (dec_clock st)) with permute:=perm''`,`perm'''`] assume_tac permute_swap_lemma>>
      rfs[]>>
      qexists_tac`λn. if n = 0:num then st.permute 0 else perm'''' (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on `x'''`)>>
      (fs[call_env_def,flush_state_def,push_env_def,dec_clock_def,env_to_list_def,ETA_AX]>>
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
        qmatch_assum_abbrev_tac `evaluate(q',A) = _`>>
        Q.ISPECL_THEN [`q'`,`A`,`rcst.permute`] mp_tac permute_swap_lemma>>
        simp[Abbr`A`]>>
        impl_tac>-
          (qpat_x_assum`B=res'` sym_sub_tac>>full_simp_tac(srw_ss())[])>>
        rw[]>>
        qexists_tac`λn. if n = 0:num then st.permute 0 else perm''' (n-1)`>>
        fs[push_env_def,env_to_list_def,dec_clock_def,call_env_def,flush_state_def,ETA_AX]>>
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
        full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,flush_state_def,ETA_AX])>>
      Cases_on`domain rst.locals ≠ domain (FST x') ∪ domain (SND x')`
      >-
        (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
        full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,flush_state_def,ETA_AX])
      >>
      qpat_x_assum`((λ(res',rcst). P) A)` mp_tac>>
      pairarg_tac>>full_simp_tac(srw_ss())[]>>strip_tac>>
      last_x_assum kall_tac>>
      qpat_x_assum`(λ(x,y). _) _`mp_tac >>
      pairarg_tac>>full_simp_tac(srw_ss())[]>>
      strip_tac >>
      last_x_assum(qspecl_then[`(set_var p0 w0 rst) with permute:=rcst.permute`,`p1`,`rst1.code`,`cc`]mp_tac)>>
      impl_tac>-
        (simp[]>>
        imp_res_tac evaluate_clock>> fs[] >>
        imp_res_tac evaluate_consts>>fs[dec_clock_def]>>
        fs[word_state_eq_rel_def]>>
        gs[]) >>
      rw[]>>
      Q.ISPECL_THEN[`q'`,`call_env q r' (push_env x' (SOME (p0,p1,p2,p3)) (dec_clock st)) with permute:=perm''`,`perm'''`] assume_tac permute_swap_lemma>>
      rfs[]>>
      qexists_tac`λn. if n = 0:num then st.permute 0 else perm'''' (n-1)`>>
      fs[call_env_def,flush_state_def,push_env_def,dec_clock_def,env_to_list_def,ETA_AX]>>
      `domain rst1.locals = domain (FST x') ∪ domain (SND x')` by
        (qpat_x_assum`rst1=_` SUBST_ALL_TAC>>rw[])>>
      simp[]>>
      pairarg_tac>>fs[]>>
      qpat_x_assum`rst1=_` SUBST_ALL_TAC>>fs[]>>
      rpt(pairarg_tac>>fs[])>>
      fs[]>>
      pop_assum mp_tac>>
      qmatch_goalsub_abbrev_tac`_ (evaluate (_,A))`>>
      qmatch_asmsub_abbrev_tac`_ (evaluate (_,B))`>>
      strip_tac>>
      `A = B` by
        (unabbrev_all_tac>>fs[state_component_equality,word_state_eq_rel_def] >>
        simp[set_var_def])>>
      rfs[]>>
      unabbrev_all_tac>>fs[])
    >>
      TRY(
      pop_assum mp_tac >> pairarg_tac>>
      fs[]>>
      Q.ISPECL_THEN [`q'`,`call_env q r' (push_env x' o0 (dec_clock st)) with permute:=perm''`,`rcst.permute`] mp_tac permute_swap_lemma>>
      fs[]>>rw[]>>
      qexists_tac`λn. if n = 0:num then st.permute 0 else perm''' (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on`x''`)>>
      fs[push_env_def,env_to_list_def,dec_clock_def,call_env_def,flush_state_def,ETA_AX]>>
      qpat_x_assum`(λ(a,b). _) _`mp_tac >>
      pairarg_tac>>rfs[]>>
      fs[]>>rw[]>>
      fs[word_state_eq_rel_def,state_component_equality]>>
      metis_tac[])
    >>
      qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on`x''`)>>
      fs[push_env_def,env_to_list_def,dec_clock_def,call_env_def,flush_state_def,ETA_AX]
     )
  >- (*Seq, inductive*)
    (fs[evaluate_def,LET_THM,AND_IMP_INTRO]>>
    first_assum(qspecl_then[`p`,`st`,`l`,`cc`] mp_tac)>>
    impl_tac>-
      size_tac>>
    strip_tac>>
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
  >- (* If *)
    (simp[evaluate_def,get_var_def,get_var_imm_def]>>
    ntac 2 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
    Cases_on`r`>>full_simp_tac(srw_ss())[get_var_imm_def,get_var_def]>>
    rpt(TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
    TRY(qpat_abbrev_tac`prog = p`)>>
    TRY(qpat_abbrev_tac`prog = p0`)>>
    first_x_assum(qspecl_then[`prog`,`st`,`l`,`cc`] mp_tac)>>
    (impl_tac>-size_tac>>srw_tac[][]))
  >- (* Alloc *)
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
    rfs[call_env_def,flush_state_def])
  >- (*Store_Consts*)
     (fs[evaluate_def,state_component_equality] >> every_case_tac >> fs[])
  >- (*Raise*)
     (fs[evaluate_def,jump_exc_def,state_component_equality] >> every_case_tac >> fs[])
  >- (*Return*)
     (fs[evaluate_def,flush_state_def,state_component_equality] >> every_case_tac >> fs[])
  >- (*Tick*)
     (fs[evaluate_def,flush_state_def,dec_clock_def,state_component_equality] >> every_case_tac >> fs[])
  >- (*OpCurrHeap*)
     (fs[evaluate_def,state_component_equality] >> every_case_tac >> fs[])
  >- (*LocValue*)
     (fs[evaluate_def,state_component_equality] >> every_case_tac >> fs[])
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
      (old_drule (GEN_ALL code_rel_union_fromAList)>>
      simp[]>>
      disch_then(qspecl_then[`tt`,`kk`,`co`,`aa`,`(h0,h1,h2)::t`] assume_tac)>>
      fs[compile_single_def])>>
    conj_tac>-
      (simp[domain_union]>>AP_TERM_TAC>>
      simp[domain_fromAList]>>AP_TERM_TAC>>
      simp[EXTENSION,MAP_MAP_o,compile_single_def,MEM_MAP,EXISTS_PROD])>>
    simp[state_component_equality,o_DEF])
  >- (*CodeBufferWrite*)
     (fs[evaluate_def,state_component_equality] >> every_case_tac >> fs[])
  >- (*DataBufferWrite*)
     (fs[evaluate_def,state_component_equality] >> every_case_tac >> fs[])
  >- (*FFI*)
     (fs[evaluate_def,flush_state_def,state_component_equality] >> every_case_tac >> fs[])
  >~ [`ShareInst`]
  >-
    (fs[evaluate_def,state_component_equality]>>
    qexists_tac`st.permute`>>
    rpt (TOP_CASE_TAC >> fs[state_component_equality]) >>
    fs[DefnBase.one_line_ify NONE share_inst_def,
      DefnBase.one_line_ify NONE sh_mem_set_var_def,
      sh_mem_load_def,sh_mem_load_byte_def,sh_mem_load32_def,
      sh_mem_load16_def,sh_mem_store16_def,
      sh_mem_store_def,sh_mem_store_byte_def,sh_mem_store32_def] >>
    rpt (TOP_CASE_TAC >>
      fs[state_component_equality,set_var_def,flush_state_def]))
QED

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
        res1 = res /\
        rst1.clock = rst.clock /\
        rst1.ffi = rst.ffi /\
        rst1.stack_max = rst.stack_max
Proof
  simp[]>>rw[]>>
  qpat_abbrev_tac`prog = Call _ _ _ _`>>
  old_drule compile_single_correct>>fs[]>>
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
  old_drule (GEN_ALL word_remove_correct)>>fs[]>>
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

val rmt_thms = (remove_must_terminate_conventions|>SIMP_RULE std_ss [LET_THM,FORALL_AND_THM])|>CONJUNCTS;

val rmd_thms = (remove_dead_prog_conventions|>SIMP_RULE std_ss [LET_THM,FORALL_AND_THM])|>CONJUNCTS;

Theorem cond16bit_inst_select_exp':
  x = inst_select_exp c t1 t2 exp ⇒
  (no_share_inst x ∨ c.ISA ≠ Ag32)
Proof
  map_every qid_spec_tac [‘x’,‘exp’,‘t2’,‘t1’,‘c’]>>
  ho_match_mp_tac word_instTheory.inst_select_exp_ind>>
  rw[no_share_inst_def,word_instTheory.inst_select_exp_def]>>
  rpt (CASE_TAC>>fs[no_share_inst_def])>>
  fs[no_share_inst_def,word_instTheory.inst_select_exp_def]
QED

val cond16bit_inst_select_exp = cond16bit_inst_select_exp' |> SIMP_RULE std_ss [];

Theorem cond16bit_inst_select:
  x = inst_select c n p ∧
  (no_share_inst p ∨ c.ISA ≠ Ag32) ⇒
  (no_share_inst x ∨ c.ISA ≠ Ag32)
Proof
  map_every qid_spec_tac [‘x’,‘p’,‘n’,‘c’]>>
  ho_match_mp_tac word_instTheory.inst_select_ind>>
  rw[no_share_inst_def,word_instTheory.inst_select_def]>>
  rpt (TOP_CASE_TAC>>fs[])>>
  gvs[no_share_inst_def,word_instTheory.inst_select_def,AllCaseEqs()]>>
  TRY (irule cond16bit_inst_select_exp>>metis_tac[])
QED

Theorem remove_must_terminate_no_share_inst:
  no_share_inst p ⇒ no_share_inst (remove_must_terminate p)
Proof
  qid_spec_tac ‘p’>>
  recInduct word_removeTheory.remove_must_terminate_ind>>
  rw[no_share_inst_def,
     word_removeTheory.remove_must_terminate_def]>>
  rpt (FULL_CASE_TAC>>fs[])
QED

Theorem full_compile_single_no_share_inst:
  no_share_inst (SND (SND (FST prog_info))) ==>
  no_share_inst
    (SND (SND (full_compile_single two_reg_arith reg_count alg c prog_info)))
Proof
  PairCases_on `prog_info`
  \\ rw []
  \\ fs [full_compile_single_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ gvs [PAIR_FST_SND_EQ]
  \\ irule remove_must_terminate_no_share_inst
  \\ fs [no_share_inst_subprogs_def]
  \\ simp [compile_single_not_created_subprogs]
QED

(* syntax going into stackLang *)
Theorem compile_to_word_conventions:
  EVERY (λ(_,_,prg). no_share_inst prg ∨ ac.ISA ≠ Ag32) p ⇒
  let (_,progs) = compile wc ac p in
  MAP FST progs = MAP FST p ∧
  EVERY2 labels_rel (MAP (extract_labels o SND o SND) p)
                    (MAP (extract_labels o SND o SND) progs) ∧
  EVERY (λ(n,m,prog).
    flat_exp_conventions prog ∧
    post_alloc_conventions (ac.reg_count - (5+LENGTH ac.avoid_regs)) prog ∧
    (EVERY (λ(n,m,prog). every_inst (inst_ok_less ac) prog) p ∧
     addr_offset_ok ac 0w ∧ hw_offset_ok ac 0w ∧ byte_offset_ok ac 0w ⇒
      full_inst_ok_less ac prog) ∧
    (ac.two_reg_arith ⇒ every_inst two_reg_inst prog) ∧
    (no_share_inst prog ∨ ac.ISA ≠ Ag32)) progs
Proof
  fs[compile_def]>>rw[]>>
  rpt(pairarg_tac>>fs[])>>
  gvs[]>>
  `LENGTH n_oracles = LENGTH p` by
    (fs[next_n_oracle_def]>>
    every_case_tac>>rw[]>>
    simp[LENGTH_TAKE,LENGTH_REPLICATE])>>
  CONJ_TAC >- (
    match_mp_tac LIST_EQ>>
    fs[EL_MAP,full_compile_single_def]>>
    rw[]>>
    qpat_abbrev_tac`q = EL x A`>>
    fs[markerTheory.Abbrev_def]>>PairCases_on`q`>>
    pop_assum (assume_tac o SYM)>>
    fs[compile_single_def]>>
    pop_assum mp_tac>>
    fs[EL_MAP,EL_ZIP])>>
  CONJ_TAC >- (
    simp[LIST_REL_EL_EQN,EL_MAP,full_compile_single_def]>>
    rw[]>>
    qpat_abbrev_tac`q = EL x A`>>
    fs[markerTheory.Abbrev_def]>>PairCases_on`q`>>
    pop_assum (mp_tac o SYM)>>
    fs[EL_MAP,EL_ZIP]>>
    fs[compile_single_def]>>
    fs[GSYM (el 5 rmt_thms),GSYM word_alloc_lab_pres]>>
    fs[GSYM (el 6 rmd_thms)]>>
    strip_tac>>
    irule_at Any (labels_rel_TRANS)>>
    irule_at (Pos last) labels_rel_remove_unreach>>
    simp[GSYM three_to_two_reg_prog_lab_pres]>>
    simp[extract_labels_copy_prop] >>
    simp[extract_labels_word_common_subexp_elim] >>
    simp[GSYM remove_dead_prog_conventions]>>
    simp[GSYM full_ssa_cc_trans_lab_pres] >>
    simp[GSYM inst_select_lab_pres] >>
    simp[extract_labels_compile_exp]
    )>>
  fs[EVERY_MAP,EVERY_MEM,MEM_ZIP,FORALL_PROD]>>rw[]>>
  fs[full_compile_single_def,compile_single_def]>>
  CONJ_TAC>- (
    match_mp_tac (el 1 rmt_thms)>>
    match_mp_tac word_alloc_flat_exp_conventions>>
    match_mp_tac (el 1 rmd_thms)>>
    match_mp_tac flat_exp_conventions_remove_unreach>>
    match_mp_tac three_to_two_reg_prog_flat_exp_conventions>>
    irule flat_exp_conventions_copy_prop>>
    irule flat_exp_conventions_word_common_subexp_elim >>
    match_mp_tac (el 1 rmd_thms)>>
    match_mp_tac full_ssa_cc_trans_flat_exp_conventions>>
    fs[inst_select_flat_exp_conventions])>>
  CONJ_TAC>- (
    match_mp_tac (el 3 rmt_thms)>>
    match_mp_tac pre_post_conventions_word_alloc>>
    match_mp_tac (el 3 rmd_thms)>>
    match_mp_tac pre_alloc_conventions_remove_unreach>>
    match_mp_tac three_to_two_reg_prog_pre_alloc_conventions >>
    (* pre_alloc_conventions *)
    irule pre_alloc_conventions_copy_prop>>
    irule pre_alloc_conventions_word_common_subexp_elim >>
    match_mp_tac (el 3 rmd_thms)>>
    fs[full_ssa_cc_trans_pre_alloc_conventions])>>
  CONJ_TAC>- (
    strip_tac>>
    match_mp_tac (el 2 rmt_thms)>>
    match_mp_tac word_alloc_full_inst_ok_less>>
    match_mp_tac (el 2 rmd_thms)>>
    match_mp_tac full_inst_ok_less_remove_unreach>>
    match_mp_tac three_to_two_reg_prog_full_inst_ok_less >>
    irule full_inst_ok_less_copy_prop>>
    irule full_inst_ok_less_word_common_subexp_elim >>
    match_mp_tac (el 2 rmd_thms)>>
    match_mp_tac full_ssa_cc_trans_full_inst_ok_less>>
    match_mp_tac inst_select_full_inst_ok_less>>
    fs[]>>
    metis_tac[compile_exp_no_inst,MEM_EL])>>
  rw[]
  >- (match_mp_tac (el 4 rmt_thms)>>
      match_mp_tac word_alloc_two_reg_inst>>
      match_mp_tac (el 4 rmd_thms)>>
      match_mp_tac every_inst_remove_unreach >>
      match_mp_tac three_to_two_reg_prog_two_reg_inst >>
      fs[])>>
  ‘no_share_inst (SND (SND (FST (EL n p,EL n n_oracles))))’ by
    (fs[MEM_EL]>>res_tac>>
     qpat_x_assum ‘_ = EL n p’ $ assume_tac o GSYM >> fs[])>>
  imp_res_tac full_compile_single_no_share_inst>>
  first_x_assum $ qspecl_then [‘ac.two_reg_arith’,‘ac.reg_count - (LENGTH ac.avoid_regs + 5)’,‘ac’, ‘wc.reg_alg’] assume_tac>>
  qpat_x_assum ‘_ = EL n p’ $ assume_tac o GSYM>>fs[]>>
  fs[full_compile_single_def,compile_single_def]
QED

(**** more on syntactic form restrictions ****)

Theorem code_rel_not_created_subprogs:
  find_code op args c1 sz = SOME v ∧
  code_rel c1 c2 ∧
  not_created_subprogs P (FST (SND v)) ∧
  find_code op args c2 sz = SOME v' ⇒
  not_created_subprogs P (FST (SND v'))
Proof
  gs[code_rel_def]>>Cases_on ‘op’>>
  gs[find_code_def]>>every_case_tac>>rw[]>>gs[]>>
  res_tac>>gs[]>>
  gvs[PAIR_FST_SND_EQ]>>
  irule compile_single_not_created_subprogs>>
  simp []
QED

Theorem code_rel_P[local] = Q.GEN `P` code_rel_not_created_subprogs;

Theorem code_rel_no_alloc[local] = code_rel_P |> Q.SPEC `(<>) (Alloc 0 (LN,LN))`
    |> REWRITE_RULE [GSYM no_alloc_subprogs_def]

Theorem code_rel_no_install[local] = code_rel_P |> Q.SPEC `(<>) (Install 0 0 0 0 (LN,LN))`
    |> REWRITE_RULE [GSYM no_install_subprogs_def]


(***** compile_single correctness for no_alloc & no_install ******)
Theorem no_install_no_alloc_compile_single_correct:
  ∀prog (st:('a,'c,'ffi) wordSem$state) l.
    code_rel st.code l ∧
    no_install prog ∧ no_alloc prog ∧
    no_install_code st.code ∧ no_alloc_code st.code ∧
    (domain st.code = domain l) ∧
    gc_fun_const_ok st.gc_fun
    ==>
    ∃perm'.
      let (res,rst) = evaluate (prog,st with <|permute := perm'|>) in
        if res = SOME Error then T
        else
          let (res1,rst1) = evaluate (prog, st with code := l) in
            res1 = res ∧
            code_rel rst.code rst1.code ∧
            domain rst.code = domain rst1.code ∧
            rst1 = rst with code:=rst1.code
Proof
  completeInduct_on`((st:('a,'c,'ffi)wordSem$state).termdep)`>>
                   completeInduct_on`((st:('a,'c,'ffi)wordSem$state).clock)`>>
                   simp_tac(srw_ss())[PULL_FORALL]>>
  completeInduct_on`prog_size (K 0) (prog:'a wordLang$prog)`>>
                   rpt strip_tac>>
  full_simp_tac(srw_ss())[PULL_FORALL,evaluate_def,AND_IMP_INTRO]>>
  Cases_on`prog`
  >- (fs[evaluate_def] >> simp[state_component_equality])
  >- (fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
      simp[state_component_equality])
  >- (fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
      old_drule inst_const_full >> simp[state_component_equality])
  >- (fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
      simp[state_component_equality])
  >- (fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
      simp[state_component_equality])
  >- (fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
      simp[state_component_equality])
  >- (fs[evaluate_def] >> rpt (TOP_CASE_TAC >> simp[]) >>
      old_drule mem_store_const >> simp[state_component_equality])
   (* Must_Terminate *)
  >- (fs[evaluate_def,no_install_def,no_alloc_def] >>
     rpt (TOP_CASE_TAC >> simp[]) >>
     last_x_assum(qspecl_then[`st with <|clock:=MustTerminate_limit(:'a);termdep:=st.termdep-1|>`,`p`,`l`] mp_tac)>>
     impl_tac >- simp[] >>
     disch_tac >> fs[] >>
     qexists_tac`perm'`>>fs[]>>
     rpt (pairarg_tac >> fs[]) >>
     fs[bool_case_eq] >>
     fs[state_component_equality])
  >- (*Call -- the hard case*)
   (
   fs[evaluate_def,no_alloc_def, no_install_def]>>
   ntac 2 (TOP_CASE_TAC >> fs[]) >>
   Cases_on`find_code o1 (add_ret_loc o' x) st.code st.stack_size`>>
   fs []>>
   Cases_on`o'`>>full_simp_tac(srw_ss())[]>>
   (*    Cases_on`o0`>>full_simp_tac(srw_ss())[]>>*)
   Cases_on`x'`>>simp[]>>
   Cases_on `r` >> simp [] >>
   imp_res_tac find_code_thm>>
   pop_assum(qspec_then`l` mp_tac)>>
   (impl_tac>-
     (fs[code_rel_def]>>
      metis_tac[]))>>
   rw[]>> rfs[]
   >- (*Tail calls*)
     (
     ntac 2 (TOP_CASE_TAC >> fs[])
     >-simp[flush_state_def,
            state_component_equality] >>
     qabbrev_tac`stt = call_env q r' (dec_clock st)`>>
     first_x_assum(qspecl_then[`stt`,`prog'`,`l`] mp_tac)>>
     simp[AND_IMP_INTRO]>>
     impl_tac>-
      (full_simp_tac(srw_ss())
       [Abbr`stt`,dec_clock_def,
        call_env_def,
        flush_state_def]>>
       conj_tac>-DECIDE_TAC>>
       qpat_x_assum ‘find_code _ _ st.code _ = _’ assume_tac>>
       old_drule (GEN_ALL code_rel_no_install)>>
       disch_then old_drule>>gs[]>>
       impl_tac
       >-(drule_all (INST_TYPE [beta|->alpha, gamma|->“:num”]
                     no_install_find_code)>>gs[])>>
       rw[]>>
       old_drule (GEN_ALL code_rel_no_alloc)>>
       disch_then old_drule>>gs[]>>
       impl_tac
       >-(drule_all (INST_TYPE [beta|->alpha, gamma|->“:num”]
                     no_alloc_find_code)>>gs[])>>
       rw[])>>
     srw_tac[][]>>
     Q.ISPECL_THEN [`n`,`q'`,`LENGTH q`,`stt with permute:=perm'`]
      mp_tac (Q.GEN `name` compile_single_lem) >>
     impl_tac >-
      (full_simp_tac(srw_ss())[Abbr`stt`,call_env_def,flush_state_def] >>
       simp[domain_fromList2,word_allocTheory.even_list_def,dec_clock_def]) >>
     qpat_abbrev_tac`A = compile_single t k a c B`>>
     PairCases_on`A`>>srw_tac[][]>>full_simp_tac(srw_ss())[LET_THM]>>
     pop_assum mp_tac>>
     pairarg_tac>>full_simp_tac(srw_ss())[Abbr`stt`] >>
     strip_tac
     >-
      (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def])>>
     Cases_on`res`>>full_simp_tac(srw_ss())[]
     >-
      (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def])>>
     Cases_on`x' = Error`>>full_simp_tac(srw_ss())[]
     >-
      (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def])>>
     ntac 2 (pop_assum mp_tac) >>
     pairarg_tac>>full_simp_tac(srw_ss())[]>>
     rw[]>>
     qpat_x_assum`(λ(x,y). _) _`mp_tac >>
     pairarg_tac>>fs[]>>
     qpat_x_assum`Abbrev ((_,_,_) = _)` mp_tac>>
     simp[Once markerTheory.Abbrev_def]>>rw[]>>
     rw[]>>fs[dec_clock_def]>>
     qmatch_asmsub_abbrev_tac`evaluate (q',stt)`>>
                             Q.ISPECL_THEN [`q'`,`stt`,`rcst.permute`] mp_tac wordPropsTheory.permute_swap_lemma>>
     fs[]>>rw[]>>
     qexists_tac`perm'''`>>
                fs[Abbr`stt`,word_allocProofTheory.word_state_eq_rel_def,state_component_equality]>>
     fs[code_rel_def]>>
     metis_tac[])
   >>
   rename [‘find_code _ (add_ret_loc (SOME xx) _)’] >>
   ‘∃xn xnames xrh xl1 xl2. xx = (xn, xnames, xrh, xl1, xl2)’
     by (PairCases_on`xx`>>simp[]) >> rveq >> full_simp_tac(srw_ss())[]>>
   ntac 2 (TOP_CASE_TAC>> fs [])>>
   IF_CASES_TAC>-
    (simp[state_component_equality,flush_state_def] >>
     simp[oneline push_env_def,call_env_def]) >>
   fs[]>>
   rename [`evaluate (_,call_env q r' (push_env x' o0 (dec_clock (st with permute := _))))`] >>
   qabbrev_tac`stt = call_env q r' (push_env x' o0 (dec_clock st))`>>
                              first_assum(qspecl_then[`stt`,`prog'`,`l`] mp_tac)>>
   impl_tac>-
    (
     fs[Abbr`stt`,dec_clock_def] >>
     qpat_x_assum ‘find_code _ _ st.code _ = _’ assume_tac>>
     old_drule (GEN_ALL code_rel_no_install)>>
     disch_then old_drule>>gs[]>>
     impl_tac
     >-(drule_all (INST_TYPE [beta|->alpha, gamma|->“:num”]
                   no_install_find_code)>>gs[])>>
     rw[]>>
     old_drule (GEN_ALL code_rel_no_alloc)>>
     disch_then old_drule>>gs[]>>
     impl_tac
     >-(drule_all (INST_TYPE [beta|->alpha, gamma|->“:num”]
                   no_alloc_find_code)>>gs[])>>
     rw[])>>
   rw[]>>
   Q.ISPECL_THEN [`n`,`q'`,`LENGTH q`,`stt with permute:=perm'`] mp_tac
    (Q.GEN `name` compile_single_lem)>>
   impl_tac>-
    (fs[Abbr`stt`,call_env_def] >>
     simp[domain_fromList2,word_allocTheory.even_list_def]) >>
   qpat_abbrev_tac`A = compile_single t k a c B`>>
   PairCases_on`A`>>srw_tac[][]>>full_simp_tac(srw_ss())[LET_THM]>>
   pop_assum mp_tac >>
   pairarg_tac>>full_simp_tac(srw_ss())[Abbr`stt`] >>
   strip_tac
   >-
    (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
     Cases_on`o0`>>TRY(PairCases_on`x''`)>>
     full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,flush_state_def,ETA_AX])>>
   Cases_on`res`>>full_simp_tac(srw_ss())[]
   >-
    (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
                                                                Cases_on`o0`>>TRY(PairCases_on`x''`)>>
     full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,
                             flush_state_def,ETA_AX])>>
    `!perm. dec_clock (st with permute := perm) = dec_clock st with permute := perm`
         by (EVAL_TAC >> simp[]) >> fs[] >>
    qrefine `λn. if n = 0:num then st.permute 0 else perm''' (n-1)` >>
   `!perm. push_env x' o0 (dec_clock st with permute := λn. if n = 0n then st.permute 0 else perm (n − 1)) =
    push_env x' o0 (dec_clock st) with permute := perm`
       by (fs[oneline push_env_def,env_to_list_def,ETA_AX] >>
       rpt (TOP_CASE_TAC >> fs[])) >> fs[] >>
   ntac 2 (pop_assum kall_tac) >>
   Cases_on`x''`>>full_simp_tac(srw_ss())[]
   >-
    (*Manual simulation for Result*)
    (
     rename [`evaluate (q', call_env q r' (push_env x' o0 (dec_clock st)) with permute := perm'') =
     (SOME (Result x ys),rst)`] >>
     Cases_on`x = Loc xl1 xl2 ⇒ LENGTH ys ≠ LENGTH xn`>>full_simp_tac(srw_ss())[]
     >-
      (qexists_tac`perm''`>> fs[])
     >>
     Cases_on`pop_env rst`>>full_simp_tac(srw_ss())[]
     >-
      (qexists_tac`perm''`>> fs[]) >>
     rename [`pop_env rst = SOME x''`]
     >>
     reverse (Cases_on`domain x''.locals = domain (FST x') ∪ domain (SND x')`)>>full_simp_tac(srw_ss())[]
     >-
      (qexists_tac`perm''`>> fs[])
     >>
     qpat_x_assum`(λ(x,y). _) _`mp_tac >>
     pairarg_tac>>full_simp_tac(srw_ss())[]>>
     strip_tac >>
     last_x_assum kall_tac>>
     qpat_x_assum`(λ(x,y). _) _`mp_tac >>
     pairarg_tac>>full_simp_tac(srw_ss())[]>>
     strip_tac >>
     last_x_assum(qspecl_then[`(set_vars xn ys x'') with permute:=rcst.permute`,`xrh`,`rst1.code`]mp_tac)>>
     impl_tac>-
      ((*TODO this is a mess*)
       (*Monotonicity on 12, and dec_clock*)
       `rst.clock < st.clock` by
         (imp_res_tac evaluate_clock>>
          full_simp_tac(srw_ss())[call_env_def,flush_state_def,dec_clock_def]>>
          DECIDE_TAC)>>
       (*Why are there 3 different lemmas*)
       old_drule pop_env_const >> fs[] >> disch_then kall_tac >>
       old_drule pop_env_termdep>> fs[] >> disch_then kall_tac >>
       old_drule pop_env_code_gc_fun_clock >>
       disch_then (mp_tac o LIST_CONJ o (map SYM) o CONJUNCTS) >>
       fs[] >> disch_then kall_tac >>
       (*Yet another duplication*)
       imp_res_tac evaluate_consts >> fs[] >>
       imp_res_tac evaluate_clock >> fs[] >>
       fs[word_allocProofTheory.word_state_eq_rel_def]>>
       gs[]>>
       gvs[] >>
       imp_res_tac no_install_evaluate_const_code >>
       imp_res_tac no_install_find_code >>
       gs []) >>
     rw[]>>
     Q.ISPECL_THEN[`q'`,`call_env q r' (push_env x' o0 (dec_clock st)) with permute:=perm''`,`perm'''`] assume_tac wordPropsTheory.permute_swap_lemma>>
      rfs[]>>
      qexists_tac `perm''''` >> fs[] >>
      qpat_x_assum`((λ(res',rcst). P) A)` mp_tac>>
      pairarg_tac>>rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[]>>
      `pop_env rst1 =
      SOME (x'' with <| code:=rst1.code; permute:=rcst.permute|>)` by
        (fs[pop_env_def,word_allocProofTheory.word_state_eq_rel_def]>>
         qpat_x_assum`rst1 = _` SUBST_ALL_TAC>>
         simp[]>>
         EVERY_CASE_TAC>>fs[state_component_equality])>>
      simp[]>>
      rw[]>>
      fs[dec_clock_def])
   >-
    (*Manual simulation for Exceptions*)
    (
     Cases_on`o0`>> fs[]
     >-
      (pop_assum mp_tac >> pairarg_tac>>full_simp_tac(srw_ss())[]>>
       strip_tac >>
       qmatch_assum_abbrev_tac `evaluate(q',A) = _`>>
                                                  Q.ISPECL_THEN [`q'`,`A`,`rcst.permute`] mp_tac wordPropsTheory.permute_swap_lemma>>
       simp[Abbr`A`]>>
       impl_tac>-
        (qpat_x_assum`B=res'` sym_sub_tac>>full_simp_tac(srw_ss())[])>>
       rw[]>>
       qexists_tac`perm'''`>>
       qpat_x_assum`(λ(x,y). _) _`mp_tac >>
       pairarg_tac>>rfs[]>>fs[]>>
       rw[]>>fs[word_allocProofTheory.word_state_eq_rel_def,state_component_equality]>>
       fs[dec_clock_def] >>
       metis_tac[])
     >>
     rename [`evaluate (q', call_env q r' (push_env x' (SOME p) (dec_clock st)) with
           permute := perm'') = (SOME (Exception w w0),rst)`] >>
     PairCases_on`p`>>full_simp_tac(srw_ss())[]>>
     Cases_on`w ≠ Loc p2 p3`
     >-
      (qexists_tac`perm''`>> fs[])
     >> Cases_on`domain rst.locals ≠ domain (FST x') ∪ domain (SND x')`
     >-
      (qexists_tac`perm''`>> fs[])
     >>
     qpat_x_assum`((λ(res',rcst). P) A)` mp_tac>>
     pairarg_tac>>full_simp_tac(srw_ss())[]>>strip_tac>>
     last_x_assum kall_tac>>
     qpat_x_assum`(λ(x,y). _) _`mp_tac >>
     pairarg_tac>>full_simp_tac(srw_ss())[]>>
     strip_tac >>
     last_x_assum(qspecl_then[`(set_var p0 w0 rst) with permute:=rcst.permute`,`p1`,`rst1.code`]mp_tac)>>
     impl_tac>-
      (simp[] >>
       imp_res_tac wordPropsTheory.evaluate_consts>>fs[dec_clock_def]>>
       imp_res_tac evaluate_clock>> fs[] >>
       fs[word_allocProofTheory.word_state_eq_rel_def]>>
       gs[]>>
       imp_res_tac no_install_evaluate_const_code >>
       imp_res_tac no_install_find_code >>
       gs []) >>
     rw[]>>
     Q.ISPECL_THEN[`q'`,`call_env q r' (push_env x' (SOME (p0,p1,p2,p3)) (dec_clock st)) with permute:=perm''`,`perm'''`] assume_tac wordPropsTheory.permute_swap_lemma>>
     rfs[]>>
     qexists_tac`perm''''` >>
     fs[dec_clock_def]>>
     `domain rst1.locals = domain (FST x') ∪ domain (SND x')` by
       (qpat_x_assum`rst1=_` SUBST_ALL_TAC>>rw[])>>
     simp[]>>
     pairarg_tac>>fs[]>>
     qpat_x_assum`rst1=_` SUBST_ALL_TAC>>fs[]>>
     rpt(pairarg_tac>>fs[])>>
     fs[]>>
     pop_assum mp_tac>>
     qmatch_goalsub_abbrev_tac`_ (evaluate (_,A))`>>
                              qmatch_asmsub_abbrev_tac`_ (evaluate (_,B))`>>
                              strip_tac>>
     `A = B` by
       (unabbrev_all_tac>>fs[set_var_def,
      state_component_equality,word_allocProofTheory.word_state_eq_rel_def])>>
     rfs[]>>
     unabbrev_all_tac>>fs[])
   >>
   TRY(
     pop_assum mp_tac >> pairarg_tac>>
     fs[]>>
     Q.ISPECL_THEN [`q'`,`call_env q r' (push_env x' o0 (dec_clock st)) with permute:=perm''`,`rcst.permute`] mp_tac wordPropsTheory.permute_swap_lemma>>
     fs[]>>rw[]>>
     qexists_tac`perm'''`>>
     fs[dec_clock_def] >>
     qpat_x_assum`(λ(a,b). _) _`mp_tac >>
     pairarg_tac>>rfs[]>>
     fs[word_allocProofTheory.word_state_eq_rel_def,state_component_equality]
     )
   >>
   qexists_tac`perm''`>> fs[dec_clock_def])
  >- (*Seq, inductive*)
   (fs[evaluate_def,LET_THM,AND_IMP_INTRO]>>
    gs[no_install_def, no_alloc_def]>>
    first_assum(qspecl_then[`p`,`st`,`l`] mp_tac)>>
    impl_tac>- size_tac>>
    strip_tac>>
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
     (gs[no_install_def, no_alloc_def]>>
      first_x_assum(qspecl_then[`p0`,`rst`,`rst1.code`] mp_tac)>>
      impl_tac>-(
       gs[no_install_def, no_alloc_def]>>
       ‘no_install_code rst.code ∧ no_alloc_code rst.code’
         by (qpat_assum ‘_ = (_, rst)’ assume_tac>>
             old_drule no_install_evaluate_const_code>>
             strip_tac>>gs[call_env_def,
                           push_env_def]>>
             qpat_x_assum ‘find_code _ _ st.code _ = _’ assume_tac>>
             drule_all (INST_TYPE [beta|->alpha, gamma|->“:num”]
                        no_alloc_find_code)>>gs[]>>
             drule_all (INST_TYPE [beta|->alpha, gamma|->“:num”]
                        no_install_find_code)>>gs[]>>
             ntac 2 strip_tac>>gs[])>>
       imp_res_tac wordPropsTheory.evaluate_consts>>
       fs[]>>size_tac)>>
      rw[]>>
      Q.ISPECL_THEN[`p`,`st with permute:=perm'`,`perm''`]
       assume_tac wordPropsTheory.permute_swap_lemma>>
      rfs[]>>
      qexists_tac`perm'''`>>
                 rw[]>>fs[]>>
      pairarg_tac>>fs[]>>
      qpat_x_assum`rst1 = _` SUBST_ALL_TAC>>fs[])
    >>
    first_x_assum(qspecl_then[`rst`,`p0`,`rst1.code`] mp_tac)>>
    impl_tac>- (
     imp_res_tac wordPropsTheory.evaluate_consts>>
     fs[]>>
     qpat_assum ‘_ = (_, rst)’ assume_tac>>
     old_drule no_install_evaluate_const_code>>
     strip_tac>>gs[call_env_def,
                   push_env_def]>>
     qpat_x_assum ‘find_code _ _ st.code _ = _’ assume_tac>>
     drule_all (INST_TYPE [beta|->alpha, gamma|->“:num”]
                no_alloc_find_code)>>gs[]>>
     drule_all (INST_TYPE [beta|->alpha, gamma|->“:num”]
                no_install_find_code)>>gs[]>>
     ntac 2 strip_tac>>gs[])>>
    rw[]>>
    Q.ISPECL_THEN[`p`,`st with permute:=perm'`,`perm''`]
     assume_tac wordPropsTheory.permute_swap_lemma>>
    rfs[]>>
    qexists_tac`perm'''`>>
               rw[]>>fs[]>>
    pairarg_tac>>fs[]>>
    qpat_x_assum`rst1 = _` SUBST_ALL_TAC>>fs[])
  >- (* If *)
   (simp[evaluate_def,get_var_def,get_var_imm_def]>>
    ntac 2 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
    Cases_on`r`>>full_simp_tac(srw_ss())[get_var_imm_def,get_var_def]>>
    rpt(TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
    TRY(qpat_abbrev_tac`prog = p`)>>
    TRY(qpat_abbrev_tac`prog = p0`)>>
    first_x_assum(qspecl_then[`prog`,`st`,`l`] mp_tac)>>
    gs[no_install_def, no_alloc_def]>>
    (impl_tac>-size_tac>>srw_tac[][]))
  >~ [`ShareInst`]
  >- (fs[evaluate_def,state_component_equality]>>
    qexists_tac`st.permute`>>
    rpt (TOP_CASE_TAC >> fs[state_component_equality]) >>
    fs[DefnBase.one_line_ify NONE share_inst_def,
      DefnBase.one_line_ify NONE sh_mem_set_var_def,
      sh_mem_load_def,sh_mem_load_byte_def,sh_mem_load32_def,
      sh_mem_load16_def,sh_mem_store16_def,
      sh_mem_store_def,sh_mem_store_byte_def,sh_mem_store32_def] >>
    rpt (TOP_CASE_TAC >>
      fs[state_component_equality,set_var_def,flush_state_def]))>>
  gs[no_alloc_def, no_install_def]>> (
  fs[evaluate_def,jump_exc_def,flush_state_def,dec_clock_def,state_component_equality] >>
  every_case_tac >> fs[])
QED

(******** more on no_mt **********)

Theorem no_mt_remove_must_terminate_const:
  no_mt prog ==> remove_must_terminate prog = prog
Proof
  qid_spec_tac ‘prog’>>
  recInduct word_removeTheory.remove_must_terminate_ind>>
  gs[word_removeTheory.remove_must_terminate_def, no_mt_def]>>
  rw[]>>every_case_tac>>gs[]
QED

Theorem no_mt_full_compile_single:
  no_mt (SND (SND (FST x))) ==>
  full_compile_single tt kk aa c x =
  compile_single tt kk aa c x
Proof
  fs[word_to_wordTheory.full_compile_single_def]>>
  rpt(pairarg_tac >> fs [])>>
  rw []>>
  irule no_mt_remove_must_terminate_const>>
  gvs [PAIR_FST_SND_EQ]>>
  fs[no_mt_subprogs_def]>>
  irule compile_single_not_created_subprogs >>
  simp []
QED

Theorem no_mt_code_full_compile_single:
  no_mt_code (fromAList progs) /\
  ALL_DISTINCT (MAP FST progs) /\
  LENGTH x = LENGTH progs ==>
  MAP (full_compile_single tt kk aa co) (ZIP (progs, x)) =
  MAP (compile_single tt kk aa co) (ZIP (progs, x))
Proof
  rw[no_mt_code_def]>>
  gs[lookup_fromAList, MAP_EQ_f]>>rpt strip_tac>>
  gs[MEM_ZIP]>>
  drule_all ALOOKUP_ALL_DISTINCT_EL>>strip_tac>>
  qmatch_goalsub_abbrev_tac ‘(prg, _)’>>PairCases_on ‘prg’>>gs[]>>
  last_x_assum (qspecl_then [‘prg0’, ‘prg1’, ‘prg2’] assume_tac)>>gs[]>>
  gs[no_mt_full_compile_single]
QED

(*** code_rel_ext ***)

Definition code_rel_ext_def:
  code_rel_ext code l ⇔
  (∀n p_1 p_2.
     SOME (p_1,p_2) = lookup n code ⇒
     ∃t' k' a' c' col.
       SOME
       (SND (full_compile_single t' k' a' c' ((n,p_1,p_2),col))) =
       lookup n l)
End

val code_rel_ext_def = definition"code_rel_ext_def";

Theorem code_rel_ext_word_to_word:
  ∀code c1 col code'.
    compile c1 c2 code = (col,code') ⇒
    code_rel_ext (fromAList code) (fromAList code')
Proof
  simp[word_to_wordTheory.compile_def,code_rel_ext_def] \\
  rw[]>>
  pairarg_tac>>fs[]>>rw[]>>
  `LENGTH n_oracles = LENGTH code` by
    (fs[word_to_wordTheory.next_n_oracle_def]>>
     every_case_tac>>rw[]>>fs[])>>
  last_x_assum mp_tac>>
  pop_assum mp_tac>>
  pop_assum kall_tac>>
  map_every qid_spec_tac [`n_oracles`,`p_1`,`p_2`,`n`]>>
  Induct_on`code` \\ rw[] \\
  fs[lookup_fromAList]>>
  Cases_on`n_oracles`>>fs[]>>
  Cases_on`h`>>fs[]>>
  simp[word_to_wordTheory.full_compile_single_def,SimpRHS] \\
  pairarg_tac \\ fs[] \\
  qmatch_asmsub_rename_tac`((q,p),h)` \\
  PairCases_on`p` \\ fs[word_to_wordTheory.compile_single_def] \\
  rveq \\ fs[] \\
  IF_CASES_TAC \\ fs[] \\
  simp[word_to_wordTheory.full_compile_single_def,word_to_wordTheory.compile_single_def]>>
  metis_tac[]
QED

Theorem no_mt_code_rel_ext:
  no_mt_code cd1 /\
  code_rel_ext cd1 cd2 ==>
  code_rel cd1 cd2
Proof
  gs[code_rel_ext_def,
     code_rel_def,
     no_mt_code_def]>>
  rpt strip_tac>>
  Cases_on ‘v’>>gs[]>>
  rename1 ‘lookup n cd1 = SOME (q, r)’>>
  res_tac>>
  first_x_assum (qspecl_then [‘n’, ‘q’, ‘r’] assume_tac)>>gs[]>>
  pop_assum (assume_tac o GSYM)>>gs[]>>
  qmatch_asmsub_abbrev_tac ‘full_compile_single _ _ _ _ x’>>
  ‘r = SND (SND (FST x))’ by gs[Abbr ‘x’]>>gs[]>>
  old_drule (GEN_ALL no_mt_full_compile_single)>>gs[]>>metis_tac[]
QED

(**** more on no_share_inst ****)

Theorem code_rel_no_share_inst:
  find_code op args c1 sz = SOME v ∧
  code_rel c1 c2 ∧
  no_share_inst (FST (SND v)) ∧
  find_code op args c2 sz = SOME v' ⇒
  no_share_inst (FST (SND v'))
Proof
  simp [no_share_inst_subprogs_def]
  \\ metis_tac [code_rel_not_created_subprogs]
QED

(***** word_to_word semantics correctness for Pancake *****)

Theorem panLang_compile_word_to_word_thm:
  code_rel (st:('a,'c,'ffi) wordSem$state).code l ∧
  no_install_code st.code /\ no_alloc_code st.code /\ no_mt_code st.code /\
  (domain st.code = domain l) /\
  gc_fun_const_ok st.gc_fun ==>
  ?perm' clk.
    let prog = Call NONE (SOME start) [0] NONE in
      let (res,rst) = evaluate (prog,st with permute := perm') in
        if res = SOME Error then T else
          let (res1,rst1) = evaluate (prog, st with code := l)
          in
            res1 = res ∧
            rst1.clock = rst.clock ∧
            rst1.ffi = rst.ffi ∧
            rst1.stack_max = rst.stack_max
Proof
  simp[]>>rw[]>>
  qpat_abbrev_tac`prog = wordLang$Call _ _ _ _` >>
  ‘no_install prog /\ no_alloc prog /\ no_mt prog’
    by gs[no_alloc_def, no_install_def, no_mt_def, Abbr ‘prog’]>>
  ‘no_install_code l /\ no_alloc_code l /\ no_mt_code l’
    by (gs[code_rel_def,
           no_alloc_code_def, no_mt_code_def, no_install_code_def]>>
        qpat_x_assum ‘domain _ = domain _’ (assume_tac o GSYM)>>
        gs[domain_eq]>>
        rw[]>>rename1 ‘lookup k l = SOME (n, p)’>>
        first_x_assum (qspec_then ‘k’ assume_tac)>>gs[]>>
        Cases_on ‘lookup k st.code’>>gs[]>>
        rename1 ‘lookup k st.code = SOME x’>>
        PairCases_on ‘x’>>gs[]>>
        first_x_assum (qspecl_then [‘k’, ‘(x0, x1)’] assume_tac)>>gs[]>>
        fs[no_mt_subprogs_def, no_install_subprogs_def, no_alloc_subprogs_def]>>
        gvs[PAIR_FST_SND_EQ]>>
        irule compile_single_not_created_subprogs >> res_tac >> gs [])>>
  old_drule no_install_no_alloc_compile_single_correct>>
  fs[]>>
  disch_then(qspec_then`prog`mp_tac)>>
  rpt (disch_then old_drule)>>
  rw[]>>
  qexists_tac`perm'`>>pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  Cases_on`res=SOME Error`>>fs[]>>
  ‘st with <|clock := st.clock; code := l|> = st with code := l’
    by gs[wordSemTheory.state_component_equality]>>
  gs[]>>
  gs[wordSemTheory.state_component_equality]
QED

Theorem word_to_word_compile_semantics:
  word_to_word$compile wconf acomf wprog0 = (col, wprog) ∧
  gc_fun_const_ok s.gc_fun ∧
  no_install_code (fromAList wprog0) ∧
  no_alloc_code (fromAList wprog0) ∧
  no_install_code s.code ∧ no_alloc_code s.code ∧
  no_mt_code (fromAList wprog0) ∧
  ALL_DISTINCT (MAP FST wprog0) ∧ s.stack = [] ∧
  (*
  start = lc + first_name ∧
  EL lc wprog0 = (start, v) ∧
  *)
  t.code = fromAList wprog ∧ lookup 0 t.locals = SOME (Loc 1 0) ∧
  t = s with code := t.code ∧
  s.code = fromAList wprog0 ∧
  wordSem$semantics (s:(α,β,'ffi) wordSem$state) start ≠ Fail ⇒
  wordSem$semantics s start =
  wordSem$semantics (t:(α,β,'ffi) wordSem$state) start
Proof
  strip_tac>>pop_assum mp_tac>>
  old_drule code_rel_ext_word_to_word>>
  strip_tac>>
  drule_all no_mt_code_rel_ext>>strip_tac>>
  gs[word_to_wordTheory.compile_def]>>
  pairarg_tac>>gs[]>>
  qpat_x_assum ‘_ = wprog’ (assume_tac o GSYM)>>gs[]>>
  ‘LENGTH n_oracles = LENGTH wprog0’ by
    (fs[word_to_wordTheory.next_n_oracle_def]>>
     every_case_tac>>rw[]>>fs[])>>
  drule_all no_mt_code_full_compile_single>>
  qmatch_goalsub_abbrev_tac ‘MAP (full_compile_single tt kk aa c) _’>>
  disch_then (qspecl_then [‘tt’, ‘kk’, ‘c’, ‘aa’] assume_tac)>>
  gs[]>>
  ‘domain s.code =
   domain (fromAList
           (MAP (compile_single tt kk aa c) (ZIP (wprog0,n_oracles))))’
    by (gs[domain_fromAList, MAP_MAP_o]>>
        ‘MAP (FST ∘ compile_single tt kk aa c) (ZIP (wprog0,n_oracles)) =
         MAP (FST o FST) (ZIP (wprog0,n_oracles))’
          by gs[MAP_EQ_f]>>gs[MAP_ZIP])>>
  qpat_x_assum ‘s.code = _’ (assume_tac o GSYM)>>gs[]>>
  gs[wordSemTheory.semantics_def]>>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac
  >- (
  qx_gen_tac`r`>>simp[]>>strip_tac>>
  strip_tac>>
  IF_CASES_TAC >- (
    full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
    last_x_assum(qspec_then`k'`mp_tac)>>simp[] >>
    (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
    gs[]>>
    qmatch_asmsub_abbrev_tac ‘FST ev’>>Cases_on ‘ev’>>gs[]>>
    ‘code_rel (s with clock := k').code
     (fromAList
      (MAP (compile_single tt kk aa acomf)
       (ZIP (wprog0,n_oracles))))’ by
      gs[wordSemTheory.state_component_equality]>>
    old_drule (GEN_ALL panLang_compile_word_to_word_thm)>>
    full_simp_tac(srw_ss())[] >>
    disch_then (qspec_then ‘start’ mp_tac)>>gs[]>>
    strip_tac>>
    Cases_on ‘ q = SOME Error’>>gs[]>>
    mp_tac (INST_TYPE [gamma |-> “:'ffi”] permute_swap_lemma3)>>
    disch_then (qspecl_then [‘Call NONE (SOME start) [0] NONE’,
                             ‘s with clock := k'’,
                             ‘perm'’] mp_tac)>>
    simp[no_alloc_def, no_install_def]>>
    strip_tac>>
    pairarg_tac>>gs[]>>
    pairarg_tac>>gs[])>>  (* IF CASE 1 *)
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac>- (
    strip_tac>>
    strip_tac>>gs[]>>
    last_x_assum(qspec_then`k'`assume_tac)>>
    qmatch_asmsub_abbrev_tac ‘FST ev’>>
    Cases_on ‘ev’>>gs[]>>
    qmatch_asmsub_abbrev_tac ‘Abbrev ((q, r''') = ev)’>>
    ‘ev = (q, r''')’ by gs[Abbr ‘ev’]>>gs[Abbr ‘ev’]>>
    ‘code_rel (s with clock := k').code
     (fromAList
      (MAP (compile_single tt kk aa acomf)
       (ZIP (wprog0,n_oracles))))’ by
      gs[wordSemTheory.state_component_equality]>>
    old_drule (GEN_ALL panLang_compile_word_to_word_thm)>>
    full_simp_tac(srw_ss())[] >>
    disch_then (qspec_then ‘start’ mp_tac)>>gs[]>>
    strip_tac>>
    Cases_on ‘ q = SOME Error’>>gs[]>>

    mp_tac (INST_TYPE [gamma |-> “:'ffi”] permute_swap_lemma3)>>
    disch_then (qspecl_then [‘Call NONE (SOME start) [0] NONE’,
                             ‘s with clock := k'’,
                             ‘perm'’] mp_tac)>>
    simp[no_alloc_def, no_install_def]>>
    strip_tac>>
    pairarg_tac>>gs[]>>
    qpat_x_assum ‘_ = (q, r''')’ assume_tac>>
    old_drule (GEN_ALL wordPropsTheory.evaluate_add_clock) >>
    simp[RIGHT_FORALL_IMP_THM] >>
    impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
    disch_then(qspec_then`k`mp_tac) >>
    strip_tac>>
    qpat_x_assum ‘_ = (r', t')’ assume_tac>>
    old_drule (GEN_ALL wordPropsTheory.evaluate_add_clock) >>
    simp[RIGHT_FORALL_IMP_THM] >>
    impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
    disch_then(qspec_then`k'`mp_tac) >>
    strip_tac>>

    gs[]>>every_case_tac>>gs[wordSemTheory.state_component_equality])>>
  (* IF2 conj1 done *)

  ‘code_rel (s with clock := k).code
   (fromAList
    (MAP (compile_single tt kk aa acomf)
     (ZIP (wprog0,n_oracles))))’ by
    gs[wordSemTheory.state_component_equality]>>
  old_drule (GEN_ALL panLang_compile_word_to_word_thm)>>
  full_simp_tac(srw_ss())[] >>
  disch_then (qspec_then ‘start’ mp_tac)>>gs[]>>

  strip_tac>>
  Cases_on ‘r' = SOME Error’>>gs[]>>
  mp_tac (INST_TYPE [gamma |-> “:'ffi”] permute_swap_lemma3)>>
  disch_then (qspecl_then [‘Call NONE (SOME start) [0] NONE’,
                           ‘s with clock := k’,
                           ‘perm'’] mp_tac)>>
  simp[no_alloc_def, no_install_def]>>
  strip_tac>>gs[]>>
  pairarg_tac>>gs[]>>
  qexists_tac ‘k’>>gs[]>>metis_tac[])>> (* top level conj 1 *)

  (****)

  rpt strip_tac>>gs[]>>
  IF_CASES_TAC>>gs[]
  >- (
  last_x_assum(qspec_then`k`assume_tac)>>gs[] >>
  last_x_assum(qspec_then`k`assume_tac)>>gs[] >>
  qmatch_asmsub_abbrev_tac ‘FST ev’>>Cases_on ‘ev’>>gs[]>>
  qmatch_asmsub_abbrev_tac ‘FST ev’>>Cases_on ‘ev’>>gs[]>>
  ‘q = q'’
    by (
    ‘code_rel (s with clock := k).code
     (fromAList
      (MAP (compile_single tt kk aa acomf)
       (ZIP (wprog0,n_oracles))))’ by
       gs[wordSemTheory.state_component_equality]>>
    old_drule (GEN_ALL panLang_compile_word_to_word_thm)>>
    full_simp_tac(srw_ss())[] >>
    disch_then (qspec_then ‘start’ mp_tac)>>gs[]>>
    strip_tac>>

    Cases_on ‘q = SOME Error’>>gs[]>>
    mp_tac (INST_TYPE [gamma |-> “:'ffi”] permute_swap_lemma3)>>
    disch_then (qspecl_then [‘Call NONE (SOME start) [0] NONE’,
                             ‘s with clock := k’,
                             ‘perm'’] mp_tac)>>
    simp[no_alloc_def, no_install_def]>>
    strip_tac>>gs[]>>
    pairarg_tac>>gs[])>>gs[])>>

  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac>- (
  rpt strip_tac>>
  gs[]>>
  rpt (last_x_assum(qspec_then`k`assume_tac)>>gs[])>>
  qmatch_asmsub_abbrev_tac ‘FST ev’>>Cases_on ‘ev’>>gs[]>>
  ‘q = r’
    by (
    ‘code_rel (s with clock := k).code
     (fromAList
      (MAP (compile_single tt kk aa acomf)
       (ZIP (wprog0,n_oracles))))’ by
       gs[wordSemTheory.state_component_equality]>>
    old_drule (GEN_ALL panLang_compile_word_to_word_thm)>>
    full_simp_tac(srw_ss())[] >>
    disch_then (qspec_then ‘start’ mp_tac)>>gs[]>>
    strip_tac>>

    Cases_on ‘q = SOME Error’>>gs[]>>
    mp_tac (INST_TYPE [gamma |-> “:'ffi”] permute_swap_lemma3)>>
    disch_then (qspecl_then [‘Call NONE (SOME start) [0] NONE’,
                             ‘s with clock := k’,
                             ‘perm'’] mp_tac)>>
    simp[no_alloc_def, no_install_def]>>
    strip_tac>>gs[]>>
    pairarg_tac>>gs[])>>gs[])>>
  rpt strip_tac>>
  AP_TERM_TAC>>
  irule IMAGE_CONG>>
  irule_at (Pos last) EQ_REFL>>
  rpt strip_tac>>gs[]>>
  rpt (first_x_assum (qspec_then ‘x’ assume_tac))>>
  qmatch_asmsub_abbrev_tac ‘FST ev’>>Cases_on ‘ev’>>gs[]>>
  qmatch_asmsub_abbrev_tac ‘FST ev’>>Cases_on ‘ev’>>gs[]>>
  qmatch_asmsub_abbrev_tac ‘Abbrev ((q, r) = ev)’>>
  ‘ev = (q, r)’ by gs[Abbr ‘ev’]>>gs[Abbr ‘ev’]>>
  rpt (FULL_CASE_TAC>>gs[])>>
  qmatch_asmsub_abbrev_tac ‘Abbrev ((_, r') = ev)’>>
  ‘ev = (SOME TimeOut, r')’ by gs[Abbr ‘ev’]>>gs[Abbr ‘ev’]>>
  qpat_x_assum ‘_ = (_, r)’ assume_tac>>

  ‘code_rel (s with clock := x).code
   (fromAList
    (MAP (compile_single tt kk aa acomf)
     (ZIP (wprog0,n_oracles))))’ by
    gs[wordSemTheory.state_component_equality]>>

  old_drule (GEN_ALL panLang_compile_word_to_word_thm)>>
  full_simp_tac(srw_ss())[] >>
  disch_then (qspec_then ‘start’ mp_tac)>>gs[]>>
  strip_tac>>gs[]>>
  mp_tac (INST_TYPE [gamma |-> “:'ffi”] permute_swap_lemma3)>>
  disch_then (qspecl_then [‘Call NONE (SOME start) [0] NONE’,
                           ‘s with clock := x’,
                           ‘perm'’] mp_tac)>>
  simp[no_alloc_def, no_install_def]>>
  strip_tac>>gs[]>>
  pairarg_tac>>gs[]
QED

