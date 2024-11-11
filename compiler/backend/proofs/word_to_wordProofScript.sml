(*
  Correctness proof for word_to_word
*)
open preamble word_to_wordTheory wordSemTheory word_simpProofTheory
     wordPropsTheory word_allocProofTheory word_instProofTheory word_unreachTheory
     word_removeProofTheory word_cseProofTheory word_elimTheory word_elimProofTheory word_unreachProofTheory word_copyProofTheory;

val _ = new_theory "word_to_wordProof";

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val _ = bring_to_front_overload "Call" {Thy="wordLang",Name="Call"};

val is_phy_var_tac =
    full_simp_tac(srw_ss())[reg_allocTheory.is_phy_var_def]>>
    `0<2:num` by DECIDE_TAC>>
    `∀k.(2:num)*k=k*2` by DECIDE_TAC>>
    metis_tac[arithmeticTheory.MOD_EQ_0];

val rmd_thms = (remove_dead_conventions |>SIMP_RULE std_ss [LET_THM,FORALL_AND_THM])|>CONJUNCTS

val drule = old_drule

Theorem FST_compile_single[simp]:
   FST (compile_single a b c d e) = FST (FST e)
Proof
  PairCases_on`e` \\ EVAL_TAC
QED

Theorem wf_cutsets_copy_prop_aux:
  ∀p cs. wf_cutsets p ⇒
    wf_cutsets (FST (copy_prop_prog p cs))
Proof
  ho_match_mp_tac word_copyTheory.copy_prop_prog_ind>>
  rw[word_copyTheory.copy_prop_prog_def]>>
  rpt(pairarg_tac>>gvs[])>>
  fs[wf_cutsets_def]
  >- (
    Cases_on‘i’>>
    rw[word_copyTheory.copy_prop_inst_def,wf_cutsets_def]
    >-(Cases_on‘a’>>
      rw[word_copyTheory.copy_prop_inst_def,wf_cutsets_def])
    >-(Cases_on‘m’>>Cases_on‘a’>>rw[word_copyTheory.copy_prop_inst_def,wf_cutsets_def])
    >-(Cases_on‘f’>>rw[word_copyTheory.copy_prop_inst_def,wf_cutsets_def])
  )
  >-
    (every_case_tac>>gvs[wf_cutsets_def])
QED

(* TODO: move to word_copyProof *)
Theorem wf_cutsets_copy_prop:
  wf_cutsets p ⇒ wf_cutsets (copy_prop p)
Proof
  metis_tac[wf_cutsets_copy_prop_aux,word_copyTheory.copy_prop_def]
QED

(* too strong; not true *)
(*
Theorem every_inst_distinct_tar_reg_copy_prop_aux:
  ∀p cs.
  every_inst distinct_tar_reg p ⇒
  every_inst distinct_tar_reg (FST (copy_prop_prog p cs))
Proof
  ho_match_mp_tac word_copyTheory.copy_prop_prog_ind
  >>rw[every_inst_def,word_copyTheory.copy_prop_prog_def]
  >>rpt(pairarg_tac>>fs[])
  >>rw[every_inst_def]
  (* Inst *)
  >-(
    Cases_on‘i’
    >-rw[word_copyTheory.copy_prop_inst_def,every_inst_def]
    >-rw[word_copyTheory.copy_prop_inst_def,every_inst_def]
    >-(
      Cases_on‘a’
      >>rw[word_copyTheory.copy_prop_inst_def,every_inst_def]
      >>fs[distinct_tar_reg_def]

    cheat
QED
*)

(* Not true. Consider:
(before copy prop)
    a := b;
    a := b+1;
(after)
    a := b;
    a := a+1;
*)
Theorem every_inst_distinct_tar_reg_copy_prop:
  every_inst distinct_tar_reg p ⇒
  every_inst distinct_tar_reg (copy_prop p)
Proof
  cheat
QED

(* may not prove goal fully *)
fun boring_tac def =
  ho_match_mp_tac word_copyTheory.copy_prop_prog_ind
  >>rw[word_copyTheory.copy_prop_prog_def,def]
  >>rpt(pairarg_tac>>fs[])
  >>rw[def]
  >-(
    qid_spec_tac‘cs’>>qid_spec_tac‘i’
    >>ho_match_mp_tac word_copyTheory.copy_prop_inst_ind
    >>rw[word_copyTheory.copy_prop_inst_def,_def]
  )
  >-(
    TOP_CASE_TAC>>rw[def]
  );

Theorem extract_labels_copy_prop_aux:
  ∀p cs.
  extract_labels (FST (copy_prop_prog p cs)) =
  extract_labels p
Proof
  boring_tac extract_labels_def
QED

Theorem extract_labels_copy_prop:
  extract_labels (copy_prop p) =
  extract_labels p
Proof
  metis_tac[extract_labels_copy_prop_aux,word_copyTheory.copy_prop_def]
QED

Theorem flat_exp_conventions_copy_prop_aux:
  ∀p cs.
  flat_exp_conventions p ⇒
  flat_exp_conventions (FST (copy_prop_prog p cs))
Proof
  boring_tac flat_exp_conventions_def
  >>Cases_on‘exp’
  >>fs[word_copyTheory.copy_prop_share_def,flat_exp_conventions_def]
  >>rpt(TOP_CASE_TAC>>rw[flat_exp_conventions_def])
QED

Theorem flat_exp_conventions_copy_prop:
  flat_exp_conventions p ⇒
  flat_exp_conventions (copy_prop p)
Proof
  metis_tac[flat_exp_conventions_copy_prop_aux,word_copyTheory.copy_prop_def]
QED

Theorem pre_alloc_conventions_copy_prop_aux:
  ∀p cs.
  pre_alloc_conventions is_x64 p ⇒
  pre_alloc_conventions is_x64 (FST (copy_prop_prog p cs))
Proof
  ho_match_mp_tac word_copyTheory.copy_prop_prog_ind
  >>rw[word_copyTheory.copy_prop_prog_def,pre_alloc_conventions_def]
  >>rpt(pairarg_tac>>fs[])
  >>fs[wordLangTheory.every_stack_var_def,call_arg_convention_def]
  >-(
    qid_spec_tac‘cs’>>qid_spec_tac‘i’
    >>ho_match_mp_tac word_copyTheory.copy_prop_inst_ind
    >>rw[wordLangTheory.every_stack_var_def,word_copyTheory.copy_prop_inst_def]
  )
  >-(
    pop_assum mp_tac
    >>qid_spec_tac‘cs’>>qid_spec_tac‘i’
    >>ho_match_mp_tac word_copyTheory.copy_prop_inst_ind
    >>rw[call_arg_convention_def,inst_arg_convention_def,word_copyTheory.copy_prop_inst_def]
    >>cheat(*OOPS*)
  )
QED

Theorem pre_alloc_conventions_copy_prop:
  pre_alloc_conventions p ⇒
  pre_alloc_conventions (copy_prop p)
Proof
  cheat
QED

Theorem full_inst_ok_less_copy_prop:
  full_inst_ok_less ac p ⇒
  full_inst_ok_less ac (copy_prop p)
Proof
  cheat
QED

(* TODO move to word_unreachProof *)
Theorem labels_rel_remove_unreach:
  labels_rel (extract_labels p) (extract_labels q) ⇒
  labels_rel (extract_labels p) (extract_labels (remove_unreach q))
Proof
  cheat
QED

Theorem pre_alloc_conventions_remove_unreach:
  pre_alloc_conventions p ⇒
  pre_alloc_conventions (remove_unreach p)
Proof
  cheat
QED

Theorem full_inst_ok_less_remove_unreach:
  full_inst_ok_less ac p ⇒
  full_inst_ok_less ac (remove_unreach p)
Proof
  cheat
QED

Theorem two_reg_inst_remove_unreach:
  every_inst two_reg_inst p ⇒
  every_inst two_reg_inst (remove_unreach p)
Proof
  cheat
QED

(* TODO move to word_removeProof *)
Theorem two_reg_inst_remove_dead:
  every_inst two_reg_inst p ⇒
  every_inst two_reg_inst (FST (remove_dead p t))
Proof
  cheat
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
  qpat_abbrev_tac`p1 = inst_select A B C`>>
  qpat_abbrev_tac`p2 = full_ssa_cc_trans n p1`>>
  qpat_abbrev_tac`p3 = copy_prop (word_common_subexp_elim p2)`>>
  qpat_abbrev_tac`p4 = if _ then _ p3 else p3`>>
  qpat_abbrev_tac`p5 = remove_unreach p4`>>
  qpat_abbrev_tac`p6 = FST (remove_dead p5 LN)`>>
  Q.ISPECL_THEN [`name`,`c`,`a`,`p6`,`k`,`col`,`st`]
    mp_tac word_alloc_correct>>
  impl_tac>- (
    fs[even_starting_locals_def]>>
    rw[word_allocTheory.even_list_def,MEM_GENLIST,reg_allocTheory.is_phy_var_def]
    >- is_phy_var_tac>>
    unabbrev_all_tac>>fs[full_ssa_cc_trans_wf_cutsets]>>
    match_mp_tac (el 5 rmd_thms)>>
    irule wf_cutsets_remove_unreach >>
    rw[]>>TRY(ho_match_mp_tac three_to_two_reg_wf_cutsets)>>
    irule wf_cutsets_copy_prop>>
    irule wf_cutsets_word_common_subexp_elim >>
    fs[full_ssa_cc_trans_wf_cutsets])>>
  rw[]>>
  (* SSA *)
  Q.ISPECL_THEN [`p1`,`st with permute:= perm'`,`n`] assume_tac full_ssa_cc_trans_correct>>
  gvs[]>>
  qexists_tac`perm''`>>
  pairarg_tac>>fs[]>>
  Cases_on`res=SOME Error`>>gs[]>>
  (* inst select *)
  Q.ISPECL_THEN [`c`,`max_var (word_simp$compile_exp prog) +1`,`word_simp$compile_exp prog`,`st with permute:=perm''`,`res`,`rst`,`st.locals`] mp_tac inst_select_thm>>
  impl_tac >- (
    drule (GEN_ALL word_simpProofTheory.compile_exp_thm) \\ fs [] \\ strip_tac \\
    simp[locals_rel_def]>>
    Q.SPEC_THEN `word_simp$compile_exp prog` assume_tac max_var_max>>
    match_mp_tac every_var_mono>>
    HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[]>>
    DECIDE_TAC) >>
  rw[]>>
  `∀perm. st with <|locals:=st.locals;permute:=perm|> = st with permute:=perm` by fs[state_component_equality]>>
  gvs[]>>
  qpat_x_assum`(λ(x,y). _) _`mp_tac >>
  pairarg_tac>>fs[]>>
  strip_tac>>
  Cases_on`remove_dead p5 LN`>>fs[]>>
  (* word cse *)
  drule word_common_subexp_elim_correct >>
  impl_tac >- (
    fs [] >>
    unabbrev_all_tac >>
    irule word_allocProofTheory.full_ssa_cc_trans_flat_exp_conventions >>
    fs [word_instProofTheory.inst_select_flat_exp_conventions]) >>
  gvs [] >>
  (* word_copy *)
  simp[Once (GSYM evaluate_copy_prop)]>>
  strip_tac >>
  `evaluate (p4,st with permute := perm') = (res,rcst)` by (
    rw[Abbr`p4`]>>
    match_mp_tac three_to_two_reg_correct>>
    gvs[]>>
    unabbrev_all_tac>>
    irule every_inst_distinct_tar_reg_copy_prop>>
    irule every_inst_distinct_tar_reg_word_common_subexp_elim >>
    fs [full_ssa_cc_trans_distinct_tar_reg])>>
  (* word_unreach *)
  `evaluate (p5,st with permute := perm') = (res,rcst)` by (
    rw[Abbr`p5`]>>
    simp[evaluate_remove_unreach])>>
  drule_at (Pos (el 3)) evaluate_remove_dead>>
  disch_then (drule_at Any)>>
  disch_then (qspec_then`st.locals` mp_tac)>>
  impl_tac>>fs[strong_locals_rel_def]>>
  strip_tac>>
  pairarg_tac>>gvs[word_state_eq_rel_def]>>
  every_case_tac>>gvs[]
QED

val tac =
    fs[evaluate_def,state_component_equality]>>
    qexists_tac`st.permute`>>
    fs[alloc_def,get_var_def,gc_def,push_env_def,set_store_def,env_to_list_def,pop_env_def,has_space_def,
    call_env_def,flush_state_def,set_var_def,get_var_def,dec_clock_def,jump_exc_def,set_vars_def,mem_store_def, stack_size_def,unset_var_def]>>
    every_case_tac>>fs[state_component_equality]

Triviality rm_perm:
  s with permute:= s.permute = s
Proof
  full_simp_tac(srw_ss())[state_component_equality]
QED

val size_tac= (full_simp_tac(srw_ss())[wordLangTheory.prog_size_def]>>DECIDE_TAC);

Triviality find_code_thm:
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

Triviality pop_env_termdep:
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

Triviality compile_single_eta:
  compile_single t k a c ((p,x),y) =
  (p,SND (compile_single t k a c ((p,x),y)))
Proof
  Cases_on`x`>>fs[compile_single_def]
QED


Triviality code_rel_union_fromAList:
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
    first_x_assum drule>>rw[]>>
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
  >- tac
  >- tac
  >- (Cases_on`i`>>
     fs[evaluate_def,inst_def,state_component_equality,assign_def,
       word_exp_perm,mem_load_def,get_var_perm,mem_store_def,get_var_def,get_vars_perm,LET_THM,get_fp_var_def]>>
     EVERY_CASE_TAC>>
     fs[set_var_def,set_fp_var_def]>>
     rw[])
  >- tac
  >- tac
  >- tac
  >- tac
  >- (
    (* Must_Terminate *)
    fs[evaluate_def,AND_IMP_INTRO]>>
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

  >- ( (*Call -- the hard case*)
    fs[evaluate_def]>>
    TOP_CASE_TAC>> fs [] >>
    TOP_CASE_TAC>> fs []>>
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
    rw[]>>
    rfs[]
    >- ( (*Tail calls*)
      ntac 2 (IF_CASES_TAC>>full_simp_tac(srw_ss())[])
      >- simp[call_env_def,flush_state_def,state_component_equality]>>
      qabbrev_tac`stt = call_env q r' (dec_clock st)`>>
      first_x_assum(qspecl_then[`stt`,`prog'`,`l`,`cc`] mp_tac)>>
      simp[AND_IMP_INTRO]>>
      impl_tac>-
        (full_simp_tac(srw_ss())[Abbr`stt`,dec_clock_def,call_env_def,flush_state_def]>>
        DECIDE_TAC)>>
      srw_tac[][]>>
      Q.ISPECL_THEN [`n`,`q'`,`LENGTH q`,`stt with permute:=perm'`]
       mp_tac (Q.GEN `name` compile_single_lem)>>
      impl_tac>-
        (full_simp_tac(srw_ss())[Abbr`stt`,call_env_def,flush_state_def]>>
        simp[domain_fromList2,word_allocTheory.even_list_def,dec_clock_def])>>
      qpat_abbrev_tac`A = compile_single t k a c B`>>
      PairCases_on`A`>>srw_tac[][]>>full_simp_tac(srw_ss())[LET_THM]>>
      pop_assum mp_tac>>
      pairarg_tac>>full_simp_tac(srw_ss())[Abbr`stt`] >>
      strip_tac
      >-
        (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def,call_env_def,flush_state_def])>>
      Cases_on`res`>>full_simp_tac(srw_ss())[]
      >-
        (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def,call_env_def,flush_state_def])>>
      Cases_on`x' = Error`>>full_simp_tac(srw_ss())[]
      >-
        (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def,call_env_def,flush_state_def])>>
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
    TOP_CASE_TAC>>full_simp_tac(srw_ss())[]>>
    TOP_CASE_TAC>>full_simp_tac(srw_ss())[]>>
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
    impl_tac>-
      fs[Abbr`stt`,call_env_def,flush_state_def,push_env_const,dec_clock_def]>>
    impl_tac>-
      fs[Abbr`stt`,call_env_def,flush_state_def,dec_clock_def,push_env_gc_fun]>>
    rw[]>>
    Q.ISPECL_THEN [`n`,`q'`,`LENGTH q`,`stt with permute:=perm'`] mp_tac
      (Q.GEN `name` compile_single_lem)>>
    impl_tac>-
      (full_simp_tac(srw_ss())[Abbr`stt`,call_env_def,flush_state_def]>>
      simp[domain_fromList2,word_allocTheory.even_list_def,push_env_gc_fun,dec_clock_def])>>
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
      (Cases_on`w ≠ Loc xl1 xl2`>>full_simp_tac(srw_ss())[]
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
      reverse (Cases_on`domain x''.locals = domain x'`)>>full_simp_tac(srw_ss())[]
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
      last_x_assum(qspecl_then[`(set_var xn w0 x'') with permute:=rcst.permute`,`xrh`,`rst1.code`,`cc`]mp_tac)>>
      impl_tac>-
        (simp[set_var_def]>>
        (*Monotonicity on 12, and dec_clock*)
        `rst.clock < st.clock` by
          (imp_res_tac evaluate_clock>>
          full_simp_tac(srw_ss())[call_env_def,flush_state_def,dec_clock_def]>>
          DECIDE_TAC)>>
        qpat_x_assum`A=SOME x''` mp_tac>>full_simp_tac(srw_ss())[pop_env_def]>>
        EVERY_CASE_TAC>>srw_tac[][state_component_equality]>>
        simp[])>>
      impl_tac>-
        (simp[set_var_def]>>
        imp_res_tac evaluate_clock>>full_simp_tac(srw_ss())[]>>
        imp_res_tac evaluate_clock>>
        Cases_on`o0`>>TRY(PairCases_on`x'''`)>>full_simp_tac(srw_ss())[call_env_def,flush_state_def,push_env_def,LET_THM,dec_clock_def,env_to_list_def]>>
        imp_res_tac pop_env_termdep>>
        full_simp_tac(srw_ss())[])>>
      impl_tac>-
        (simp[set_var_def]>>
        imp_res_tac pop_env_code_gc_fun_clock>>fs[]>>
        imp_res_tac evaluate_consts>>fs[dec_clock_def]>>
        fs[word_state_eq_rel_def]>>
        metis_tac[])>>
      rw[]>>
      Q.ISPECL_THEN[`q'`,`call_env q r' (push_env x' o0 (dec_clock st)) with permute:=perm''`,`perm'''`] assume_tac permute_swap_lemma>>
      rfs[]>>
      qexists_tac`λn. if n = 0:num then st.permute 0 else perm'''' (n-1)`>>
      Cases_on`o0`>>TRY(PairCases_on `x'''`)>>
      (fs[call_env_def,flush_state_def,push_env_def,dec_clock_def,env_to_list_def,ETA_AX,pop_env_perm,set_var_perm]>>
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
      Cases_on`domain rst.locals ≠ domain x'`
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
        (simp[set_var_def]>>
        imp_res_tac evaluate_clock>>
        full_simp_tac(srw_ss())[call_env_def,flush_state_def,dec_clock_def]>>
        DECIDE_TAC)>>
      impl_tac>-
        (imp_res_tac evaluate_clock>>
        full_simp_tac(srw_ss())[set_var_def,call_env_def,flush_state_def,push_env_def,dec_clock_def,LET_THM,env_to_list_def])>>
      impl_tac>-
        (simp[set_var_def]>>
        imp_res_tac pop_env_code_gc_fun_clock>>fs[]>>
        imp_res_tac evaluate_consts>>fs[dec_clock_def]>>
        fs[word_state_eq_rel_def]>>
        metis_tac[])>>
      rw[]>>
      Q.ISPECL_THEN[`q'`,`call_env q r' (push_env x' (SOME (p0,p1,p2,p3)) (dec_clock st)) with permute:=perm''`,`perm'''`] assume_tac permute_swap_lemma>>
      rfs[]>>
      qexists_tac`λn. if n = 0:num then st.permute 0 else perm'''' (n-1)`>>
      fs[call_env_def,flush_state_def,push_env_def,dec_clock_def,env_to_list_def,ETA_AX,pop_env_perm,set_var_perm]>>
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
      fs[push_env_def,env_to_list_def,dec_clock_def,call_env_def,flush_state_def,ETA_AX])
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
  >- (rename [‘StoreConsts’] \\ tac)
  >- (rename [‘Raise’] \\ tac)
  >- (rename [‘Return’] \\ tac)
  >- (rename [‘Tick’] \\ tac)
  >- (rename [‘OpCurrHeap’] \\ tac)
  >- (rename [‘LocValue’] \\ tac \\ fs[domain_lookup] \\ metis_tac[])
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
  >- (rename [‘CodeBufferWrite’] \\ tac)
  >- (rename [‘DataBufferWrite’] \\ tac)
  >- (rename [‘FFI’] \\ tac \\ Cases_on`call_FFI st.ffi s x'' x'` \\ simp[])
  >~ [`ShareInst`]
  >-
    (fs[evaluate_def,state_component_equality]>>
    qexists_tac`st.permute`>>
    rpt (TOP_CASE_TAC >> fs[state_component_equality]) >>
    fs[DefnBase.one_line_ify NONE share_inst_def,
      DefnBase.one_line_ify NONE sh_mem_set_var_def,
      sh_mem_load_def,sh_mem_load_byte_def,sh_mem_load32_def,
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

val rmt_thms = (remove_must_terminate_conventions|>SIMP_RULE std_ss [LET_THM,FORALL_AND_THM])|>CONJUNCTS;

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
     addr_offset_ok ac 0w ∧ byte_offset_ok ac 0w ⇒
      full_inst_ok_less ac prog) ∧
    (ac.two_reg_arith ⇒ every_inst two_reg_inst prog)) progs
Proof
  fs[compile_def]>>
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
    irule labels_rel_remove_unreach>>
    rw[GSYM three_to_two_reg_lab_pres]>>
    gvs[
      extract_labels_copy_prop,
      GSYM full_ssa_cc_trans_lab_pres,
         GSYM inst_select_lab_pres,GSYM (el 6 rmd_thms),
         extract_labels_word_common_subexp_elim]
    )>>
  fs[EVERY_MAP,EVERY_MEM,MEM_ZIP,FORALL_PROD]>>rw[]>>
  fs[full_compile_single_def,compile_single_def]>>
  CONJ_TAC>- (
    match_mp_tac (el 1 rmt_thms)>>
    match_mp_tac word_alloc_flat_exp_conventions>>
    match_mp_tac (el 1 rmd_thms)>>
    match_mp_tac flat_exp_conventions_remove_unreach>>
    IF_CASES_TAC>>
    TRY(match_mp_tac three_to_two_reg_flat_exp_conventions)>>
    irule flat_exp_conventions_copy_prop>>
    irule flat_exp_conventions_word_common_subexp_elim >>
    match_mp_tac full_ssa_cc_trans_flat_exp_conventions>>
    fs[inst_select_flat_exp_conventions])>>
  CONJ_TAC>- (
    match_mp_tac (el 3 rmt_thms)>>
    match_mp_tac pre_post_conventions_word_alloc>>
    match_mp_tac (el 3 rmd_thms)>>
    match_mp_tac pre_alloc_conventions_remove_unreach>>
    IF_CASES_TAC>>
    TRY(match_mp_tac three_to_two_reg_pre_alloc_conventions)>>
    (* pre_alloc_conventions *)
    irule pre_alloc_conventions_copy_prop>>
    irule pre_alloc_conventions_word_common_subexp_elim >>
    fs[full_ssa_cc_trans_pre_alloc_conventions])>>
  CONJ_TAC>- (
    strip_tac>>
    match_mp_tac (el 2 rmt_thms)>>
    match_mp_tac word_alloc_full_inst_ok_less>>
    match_mp_tac (el 2 rmd_thms)>>
    match_mp_tac full_inst_ok_less_remove_unreach>>
    rw[]>>
    TRY(match_mp_tac three_to_two_reg_full_inst_ok_less)>>
    irule full_inst_ok_less_copy_prop>>
    irule full_inst_ok_less_word_common_subexp_elim >>
    match_mp_tac full_ssa_cc_trans_full_inst_ok_less>>
    match_mp_tac inst_select_full_inst_ok_less>>
    fs[]>>
    metis_tac[compile_exp_no_inst,MEM_EL])>>
  rw[]>>
  match_mp_tac (el 4 rmt_thms)>>
  match_mp_tac word_alloc_two_reg_inst>>
  match_mp_tac two_reg_inst_remove_dead >>
  match_mp_tac two_reg_inst_remove_unreach >>
  fs[three_to_two_reg_two_reg_inst]
QED

(**** more on syntactic form restrictions ****)

Theorem inst_select_exp_not_created:
  not_created_subprogs P (inst_select_exp c c' n exp)
Proof
  MAP_EVERY qid_spec_tac [‘exp’, ‘n’, ‘c'’, ‘c’]>>
  ho_match_mp_tac word_instTheory.inst_select_exp_ind>>
  rw[word_instTheory.inst_select_exp_def, not_created_subprogs_def]>>
  every_case_tac>>
  gs[not_created_subprogs_def, word_instTheory.inst_select_exp_def]
QED

Theorem inst_select_not_created:
  not_created_subprogs P prog ⇒
  not_created_subprogs P (inst_select c n prog)
Proof
  MAP_EVERY qid_spec_tac [‘prog’, ‘n’, ‘c’]>>
  ho_match_mp_tac word_instTheory.inst_select_ind>>
  rw[not_created_subprogs_def]>>
  every_case_tac>>
  gs[inst_select_exp_not_created, word_instTheory.inst_select_def,
     not_created_subprogs_def]>>
  every_case_tac>>
  gs[inst_select_exp_not_created, word_instTheory.inst_select_def,
     not_created_subprogs_def]
QED

Theorem ssa_cc_trans_inst_not_created:
  ssa_cc_trans_inst i ssa na = (i',ssa',na') ⇒
  not_created_subprogs P i'
Proof
  MAP_EVERY qid_spec_tac [‘i'’, ‘ssa'’, ‘na'’, ‘na’, ‘ssa’, ‘i’]>>
  recInduct word_allocTheory.ssa_cc_trans_inst_ind>>
  rw[word_allocTheory.ssa_cc_trans_inst_def,
     not_created_subprogs_def]>>
  rpt (pairarg_tac>>gs[])>>
  rw[word_allocTheory.ssa_cc_trans_inst_def,
     not_created_subprogs_def]>>
  every_case_tac>>rw[]>>rveq>>
  gs[word_allocTheory.next_var_rename_def,
     not_created_subprogs_def]
QED

(*
Theorem fake_moves_no_install:
  fake_moves prio ls nL nR n = (prog1, prog2, n' ,ssa, ssa') ⇒
  no_install prog1 ∧ no_install prog2
*)
Theorem fake_moves_not_created:
  fake_moves prio ls nL nR n = (prog1, prog2, n' ,ssa, ssa') ⇒
  not_created_subprogs P prog1 ∧ not_created_subprogs P prog2
Proof
  MAP_EVERY qid_spec_tac [‘ssa'’, ‘ssa’, ‘n'’, ‘prog2’, ‘prog1’, ‘n’, ‘nR’, ‘NL’, ‘ls’]>>
  Induct_on ‘ls’>>
  gs[word_allocTheory.fake_moves_def,
     not_created_subprogs_def]>>rw[]>>
  pairarg_tac>>gs[]>>FULL_CASE_TAC>>gs[]>>
  every_case_tac>>
  rveq>>gs[not_created_subprogs_def]>>
  rveq>>gs[not_created_subprogs_def,
           word_allocTheory.fake_move_def]>>metis_tac[]
QED

Theorem ssa_cc_trans_not_created:
  not_created_subprogs P prog ∧
  ssa_cc_trans prog ssa n = (prog', ssa', na)⇒
  not_created_subprogs P prog'
Proof
  MAP_EVERY qid_spec_tac [‘prog'’, ‘ssa'’, ‘na’, ‘n’, ‘ssa’, ‘prog’]>>
  recInduct word_allocTheory.ssa_cc_trans_ind>>
  rw[word_allocTheory.ssa_cc_trans_def,
     word_allocTheory.fix_inconsistencies_def,
     word_allocTheory.list_next_var_rename_move_def,
     not_created_subprogs_def]>>gs[]>>
  rpt (pairarg_tac>>gs[])>>rveq>>
  gs[word_allocTheory.ssa_cc_trans_def,
     word_allocTheory.fix_inconsistencies_def,
     word_allocTheory.list_next_var_rename_move_def,
     not_created_subprogs_def]
  >- (drule ssa_cc_trans_inst_not_created>>rw[])
  >- (drule fake_moves_not_created>>rw[])
  >- (EVERY_CASE_TAC>>gs[]>>rveq>>gs[not_created_subprogs_def]>>
    rpt (pairarg_tac>>gs[])>>rveq>>gs[not_created_subprogs_def]>>
    drule fake_moves_not_created>>rw[])
QED

Theorem setup_ssa_not_created:
  not_created_subprogs P prog ∧
  setup_ssa n v prog = (mov, ssa, na)⇒
  not_created_subprogs P mov
Proof
  rw[word_allocTheory.setup_ssa_def]>>
  pairarg_tac>>gs[]>>
  rw[word_allocTheory.setup_ssa_def,
     word_allocTheory.list_next_var_rename_move_def,
     not_created_subprogs_def]
QED

Theorem full_ssa_cc_trans_not_created:
  not_created_subprogs P prog ⇒
  not_created_subprogs P (full_ssa_cc_trans n prog)
Proof
  rw[word_allocTheory.full_ssa_cc_trans_def]>>
  pairarg_tac>>gs[]>>
  pairarg_tac>>
  drule_all setup_ssa_not_created>>
  rw[not_created_subprogs_def]>>
  drule_all ssa_cc_trans_not_created>>
  rw[not_created_subprogs_def]
QED

Theorem remove_dead_not_created:
  not_created_subprogs P prog ⇒
  not_created_subprogs P (FST (remove_dead prog q))
Proof
  MAP_EVERY qid_spec_tac [‘q’, ‘prog’]>>
  recInduct word_allocTheory.remove_dead_ind>>
  rw[word_allocTheory.remove_dead_def,
     not_created_subprogs_def]>>gs[]>>
  rw[word_allocTheory.remove_dead_def,
     not_created_subprogs_def]>>gs[]>>
  rpt (pairarg_tac>>gs[])>>rveq>>
  rw[not_created_subprogs_def]>>gs[]>>
  every_case_tac>>rpt (pairarg_tac>>gs[])>>rveq>>
  rw[not_created_subprogs_def]>>gs[]
QED

Theorem three_to_two_reg_not_created:
  not_created_subprogs P prog ⇒
  not_created_subprogs P (three_to_two_reg prog)
Proof
  qid_spec_tac ‘prog’>>
  recInduct word_instTheory.three_to_two_reg_ind>>
  rw[word_instTheory.three_to_two_reg_def,
     not_created_subprogs_def]>>
  gs[]>>every_case_tac>>gs[]
QED

Theorem apply_colour_not_created:
  not_created_subprogs P prog ⇒
  not_created_subprogs P (apply_colour f prog)
Proof
  qid_spec_tac ‘prog’>>qid_spec_tac ‘f’>>
  recInduct word_allocTheory.apply_colour_ind>>
  rw[word_allocTheory.apply_colour_def,
     not_created_subprogs_def]>>gs[]>>
  every_case_tac>>gs[]
QED

Theorem word_alloc_not_created:
  not_created_subprogs P prog ⇒
  not_created_subprogs P (word_alloc n c a r prog cl)
Proof
  rw[word_allocTheory.word_alloc_def]>>
  every_case_tac>>gs[not_created_subprogs_def]
  >- (pairarg_tac>>gs[]>>
      every_case_tac>>gs[not_created_subprogs_def]>>
      irule apply_colour_not_created>>rw[])>>
  gs[word_allocTheory.oracle_colour_ok_def]>>
  every_case_tac>>gs[not_created_subprogs_def]>>
  rveq>>irule apply_colour_not_created>>rw[]
QED

Triviality word_cseInst_not_created:
  !env i. not_created_subprogs P (SND (word_cseInst env i))
Proof
  ho_match_mp_tac word_cseTheory.word_cseInst_ind
  \\ rw [word_cseTheory.word_cseInst_def]
  \\ fs [not_created_subprogs_def]
  \\ fs [word_cseTheory.add_to_data_def, word_cseTheory.add_to_data_aux_def]
  \\ every_case_tac
  \\ fs [not_created_subprogs_def]
QED

Triviality word_cse_not_created:
   !p env. not_created_subprogs P p ==>
   not_created_subprogs P (SND (word_cse env p))
Proof
  Induct \\ rw [word_cseTheory.word_cse_def]
  \\ fs [not_created_subprogs_def, word_cseInst_not_created]
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [not_created_subprogs_def]
  \\ gvs [PAIR_FST_SND_EQ]
  \\ fs [word_cseTheory.add_to_data_aux_def]
  \\ every_case_tac
  \\ fs [not_created_subprogs_def, word_cseInst_not_created]
QED

Theorem word_common_subexp_elim_not_created:
  not_created_subprogs P prog ⇒
  not_created_subprogs P (word_common_subexp_elim prog)
Proof
  fs [word_cseTheory.word_common_subexp_elim_def]
  \\ simp [ELIM_UNCURRY, word_cse_not_created]
QED

Theorem SimpSeq_no_install:
  no_install p1 ∧ no_install p2 ⇒
  no_install (SimpSeq p1 p2)
Proof
  rw [SimpSeq_def,no_install_def]
  \\ Cases_on ‘p1’
  \\ rw [no_install_def]
  \\ every_case_tac
  \\ rw [no_install_def]
  \\ Cases_on`p2` \\ gvs[dest_Seq_Move_def]
  \\ Cases_on`p` \\ gvs[dest_Seq_Move_def,no_install_def]
QED

Theorem Seq_assoc_right_lemma_no_install:
  ∀p1 p2.
  no_install p1 ∧ no_install p2 ⇒
  no_install (Seq_assoc_right p1 p2)
Proof
  HO_MATCH_MP_TAC Seq_assoc_right_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_right_def,no_install_def]
  >~ [`Call`]
  >- (
    every_case_tac \\ gvs[no_install_def]
    \\ match_mp_tac SimpSeq_no_install
    \\ gvs[no_install_def])
  \\ match_mp_tac SimpSeq_no_install
  \\ gvs[no_install_def]
QED

Theorem remove_unreach_no_install:
  no_install p ⇒
  no_install (remove_unreach p)
Proof
  rw[remove_unreach_def]
  \\ irule Seq_assoc_right_lemma_no_install
  \\ gvs[no_install_def]
QED

Theorem compile_single_not_created:
  not_created_subprogs P (SND (SND (FST prog_opt))) ==>
  not_created_subprogs P (SND (SND
    (compile_single two_reg_arith reg_count alg c prog_opt)))
Proof
  PairCases_on `prog_opt`>>
  strip_tac>>
  simp[word_to_wordTheory.compile_single_def]>>
  irule word_alloc_not_created>>
  irule remove_dead_not_created>>
  rw[]>>
  TRY (irule three_to_two_reg_not_created)>>
  irule word_common_subexp_elim_not_created>>
  irule full_ssa_cc_trans_not_created>>
  irule inst_select_not_created>>
  irule compile_exp_not_created_subprogs>>rw[]
QED

Theorem code_rel_not_created:
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
  irule compile_single_not_created>>
  simp []
QED

Triviality code_rel_P = Q.GEN `P` code_rel_not_created

Triviality code_rel_no_alloc = code_rel_P |> Q.SPEC `(<>) (Alloc 0 LN)`
    |> REWRITE_RULE [GSYM no_alloc_subprogs_def]

<<<<<<< HEAD
Theorem const_fp_no_alloc:
  r = const_fp prog ∧ no_alloc prog ⇒
  no_alloc r
Proof
  gs[word_simpTheory.const_fp_def, const_fp_loop_no_alloc]
QED

Theorem SmartSeq_no_alloc:
  no_alloc prog ∧
  no_alloc prog' ⇒
  no_alloc (SmartSeq prog prog')
Proof
  rw[word_simpTheory.SmartSeq_def, no_alloc_def]
QED

Theorem apply_if_opt_SOME_no_alloc:
  no_alloc prog ∧ no_alloc prog' ∧
  apply_if_opt prog prog' = SOME x ⇒
  no_alloc x
Proof
  strip_tac>>
  fs [word_simpTheory.apply_if_opt_def]>>
  pairarg_tac \\ fs []>>
  rpt FULL_CASE_TAC>>gs[]
  >- (every_case_tac \\ fs [])>>
  rpt (FULL_CASE_TAC>>gs[])>>
  fs [word_simpProofTheory.dest_If_Eq_Imm_thm]>>
  gs[word_simpProofTheory.dest_If_thm]>>
  fs [word_simpTheory.SmartSeq_def]>>rveq>>
  IF_CASES_TAC>>gs[no_alloc_def]>>
  Cases_on ‘prog’>>gs[word_simpTheory.dest_Seq_def,
                      no_alloc_def]
QED

Theorem simp_if_no_alloc:
  no_alloc prog ⇒ no_alloc (simp_if prog)
Proof
  qid_spec_tac ‘prog’>> ho_match_mp_tac word_simpTheory.simp_if_ind>>
  rw[word_simpTheory.simp_if_def, no_alloc_def]>>
  TRY (every_case_tac>> gs[no_alloc_def])>>
  TRY (pairarg_tac>>gs[no_alloc_def])>>
  imp_res_tac apply_if_opt_SOME_no_alloc
QED

Theorem Seq_assoc_no_alloc:
  no_alloc prog ∧
  no_alloc prog' ⇒
  no_alloc (Seq_assoc prog prog')
Proof
  gs[GSYM AND_IMP_INTRO]>>
  qid_spec_tac ‘prog'’>>
  qid_spec_tac ‘prog’>>
  ho_match_mp_tac word_simpTheory.Seq_assoc_ind>>
  rw[no_alloc_def]
  >~[‘_ (_ _ (Call _ _ _ _))’]
  >- (
  gs[word_simpTheory.Seq_assoc_def,
     word_simpTheory.SmartSeq_def,
     no_alloc_def]>>
  every_case_tac>>gs[no_alloc_def])>>
  Cases_on ‘prog’>>
  gs[word_simpTheory.Seq_assoc_def,
     word_simpTheory.SmartSeq_def,
     no_alloc_def]
QED

Theorem compile_exp_no_alloc:
  no_alloc prog ⇒
  no_alloc (compile_exp prog)
Proof
  rw[word_simpTheory.compile_exp_def]>>
  irule const_fp_no_alloc>>gs[]>>
  qexists_tac ‘simp_if (Seq_assoc Skip prog)’>>rw[]>>
  irule simp_if_no_alloc>>
  irule Seq_assoc_no_alloc>>
  rw[no_alloc_def]
QED

Theorem inst_select_exp_no_alloc:
  no_alloc (inst_select_exp c c' n exp)
Proof
  MAP_EVERY qid_spec_tac [‘exp’, ‘n’, ‘c'’, ‘c’]>>
  ho_match_mp_tac word_instTheory.inst_select_exp_ind>>
  rw[word_instTheory.inst_select_exp_def,
     no_alloc_def]>>
  every_case_tac>>gs[no_alloc_def,
                     word_instTheory.inst_select_exp_def]
QED

Theorem inst_select_no_alloc:
  no_alloc prog ⇒
  no_alloc (inst_select c n prog)
Proof
  MAP_EVERY qid_spec_tac [‘prog’, ‘n’, ‘c’]>>
  ho_match_mp_tac word_instTheory.inst_select_ind>>
  rw[
      no_alloc_def]>>
  every_case_tac>>
  gs[inst_select_exp_no_alloc, word_instTheory.inst_select_def,
     no_alloc_def]>>
  every_case_tac>>
  gs[inst_select_exp_no_alloc, word_instTheory.inst_select_def,
     no_alloc_def]
QED

Theorem ssa_cc_trans_inst_no_alloc:
  ssa_cc_trans_inst i ssa na = (i',ssa',na') ⇒
  no_alloc i'
Proof
  MAP_EVERY qid_spec_tac [‘i'’, ‘ssa'’, ‘na'’, ‘na’, ‘ssa’, ‘i’]>>
  recInduct word_allocTheory.ssa_cc_trans_inst_ind>>
  rw[word_allocTheory.ssa_cc_trans_inst_def,
     no_alloc_def]>>
  rpt (pairarg_tac>>gs[])>>
  rw[word_allocTheory.ssa_cc_trans_inst_def,
     no_alloc_def]>>
  every_case_tac>>rw[]>>rveq>>
  gs[word_allocTheory.next_var_rename_def,
     no_alloc_def]
QED

Theorem fake_moves_no_alloc:
  fake_moves prio ls nL nR n = (prog1, prog2, n' ,ssa, ssa') ⇒
  no_alloc prog1 ∧ no_alloc prog2
Proof
  MAP_EVERY qid_spec_tac [‘ssa'’, ‘ssa’, ‘n'’, ‘prog2’, ‘prog1’, ‘n’, ‘nR’, ‘NL’, ‘ls’]>>
  Induct_on ‘ls’>>
  gs[word_allocTheory.fake_moves_def,
     no_alloc_def]>>rw[]>>
  pairarg_tac>>gs[]>>FULL_CASE_TAC>>gs[]>>
  every_case_tac>>
  rveq>>gs[no_alloc_def]>>
  rveq>>gs[no_alloc_def,
           word_allocTheory.fake_move_def]>>metis_tac[]
QED

Theorem ssa_cc_trans_no_alloc:
  no_alloc prog ∧
  ssa_cc_trans prog ssa n = (prog', ssa', na)⇒
  no_alloc prog'
Proof
  MAP_EVERY qid_spec_tac [‘prog'’, ‘ssa'’, ‘na’, ‘n’, ‘ssa’, ‘prog’]>>
  recInduct word_allocTheory.ssa_cc_trans_ind>>
  rw[word_allocTheory.ssa_cc_trans_def,
     word_allocTheory.fix_inconsistencies_def,
     word_allocTheory.list_next_var_rename_move_def,
     no_alloc_def]>>gs[]>>
  rpt (pairarg_tac>>gs[])>>rveq>>
  gs[word_allocTheory.ssa_cc_trans_def,
     word_allocTheory.fix_inconsistencies_def,
     word_allocTheory.list_next_var_rename_move_def,
     no_alloc_def]
  >- (drule ssa_cc_trans_inst_no_alloc>>rw[])
  >- (drule fake_moves_no_alloc>>rw[])
  >- (EVERY_CASE_TAC>>gs[]>>rveq>>gs[no_alloc_def]>>
    rpt (pairarg_tac>>gs[])>>rveq>>gs[no_alloc_def]>>
    drule fake_moves_no_alloc>>rw[])
QED

Theorem setup_ssa_no_alloc:
  no_alloc prog ∧
  setup_ssa n v prog = (mov, ssa, na)⇒
  no_alloc mov
Proof
  rw[word_allocTheory.setup_ssa_def]>>
  pairarg_tac>>gs[]>>
  rw[word_allocTheory.setup_ssa_def,
     word_allocTheory.list_next_var_rename_move_def,
     no_alloc_def]
QED

Theorem full_ssa_cc_trans_no_alloc:
  no_alloc prog ⇒
  no_alloc (full_ssa_cc_trans n prog)
Proof
  rw[word_allocTheory.full_ssa_cc_trans_def]>>
  pairarg_tac>>gs[]>>
  pairarg_tac>>
  drule_all setup_ssa_no_alloc>>
  rw[no_alloc_def]>>
  drule_all ssa_cc_trans_no_alloc>>
  rw[no_alloc_def]
QED

Theorem remove_dead_no_alloc:
  no_alloc prog ⇒
  no_alloc (FST (remove_dead prog q))
Proof
  MAP_EVERY qid_spec_tac [‘q’, ‘prog’]>>
  recInduct word_allocTheory.remove_dead_ind>>
  rw[word_allocTheory.remove_dead_def,
     no_alloc_def]>>gs[]>>
  rw[word_allocTheory.remove_dead_def,
     no_alloc_def]>>gs[]>>
  rpt (pairarg_tac>>gs[])>>rveq>>
  rw[no_alloc_def]>>gs[]>>
  every_case_tac>>rpt (pairarg_tac>>gs[])>>rveq>>
  rw[no_alloc_def]>>gs[]
QED

Theorem three_to_two_reg_no_alloc:
  no_alloc prog ⇒
  no_alloc (three_to_two_reg prog)
Proof
  qid_spec_tac ‘prog’>>
  recInduct word_instTheory.three_to_two_reg_ind>>
  rw[word_instTheory.three_to_two_reg_def,
     no_alloc_def]>>gs[]>>
  every_case_tac>>gs[]
QED

Theorem apply_colour_no_alloc:
  no_alloc prog ⇒
  no_alloc (apply_colour f prog)
Proof
  qid_spec_tac ‘prog’>>qid_spec_tac ‘f’>>
  recInduct word_allocTheory.apply_colour_ind>>
  rw[word_allocTheory.apply_colour_def,
     no_alloc_def]>>gs[]>>
  every_case_tac>>gs[]
QED

Theorem word_alloc_no_alloc:
  no_alloc prog ⇒
  no_alloc (word_alloc n c a r prog cl)
Proof
  rw[word_allocTheory.word_alloc_def]>>
  every_case_tac>>gs[no_alloc_def]
  >- (pairarg_tac>>gs[]>>
      every_case_tac>>gs[no_alloc_def]>>
      irule apply_colour_no_alloc>>rw[])>>
  gs[word_allocTheory.oracle_colour_ok_def]>>
  every_case_tac>>gs[no_alloc_def]>>rveq>>
  irule apply_colour_no_alloc>>rw[]
QED

Theorem word_common_subexp_elim_no_alloc:
  no_alloc prog ⇒
  no_alloc (word_common_subexp_elim prog)
Proof
  fs [word_cseTheory.word_common_subexp_elim_def]
  \\ pairarg_tac \\ fs []
  \\ rename [‘_ e p = (a,np)’]
  \\ pop_assum mp_tac
  \\ MAP_EVERY qid_spec_tac [‘np’,‘e’,‘a’,‘p’]
  \\ ho_match_mp_tac word_simpTheory.simp_if_ind
  \\ rpt strip_tac \\ fs []
  \\ fs [word_cseTheory.word_cse_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ gvs [no_alloc_def,AllCaseEqs(),word_cseTheory.add_to_data_aux_def]
  \\ res_tac \\ fs []
  \\ gvs [word_cseTheory.word_cseInst_def |> DefnBase.one_line_ify NONE,AllCaseEqs()]
  \\ gvs [no_alloc_def,AllCaseEqs(),word_cseTheory.add_to_data_aux_def,
          word_cseTheory.add_to_data_def]
QED

Theorem SimpSeq_no_alloc:
  no_alloc p1 ∧ no_alloc p2 ⇒
  no_alloc (SimpSeq p1 p2)
Proof
  rw [SimpSeq_def,no_alloc_def]
  \\ Cases_on ‘p1’ \\ rw [no_alloc_def]
QED

Theorem Seq_assoc_right_lemma_no_alloc:
  ∀p1 p2.
  no_alloc p1 ∧ no_alloc p2 ⇒
  no_alloc (Seq_assoc_right p1 p2)
Proof
  HO_MATCH_MP_TAC Seq_assoc_right_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_right_def,no_alloc_def]
  >~ [`Call`]
  >- (
    every_case_tac \\ gvs[no_alloc_def]
    \\ match_mp_tac SimpSeq_no_alloc
    \\ gvs[no_alloc_def])
  \\ match_mp_tac SimpSeq_no_alloc
  \\ gvs[no_alloc_def]
QED

Theorem remove_unreach_no_alloc:
  no_alloc p ⇒
  no_alloc (remove_unreach p)
Proof
  rw[remove_unreach_def]
  \\ irule Seq_assoc_right_lemma_no_alloc
  \\ gvs[no_alloc_def]
QED

Theorem compile_single_no_alloc:
  no_alloc prog ∧
  (q, r) = (SND (compile_single two_reg_arith reg_count alg c
                 ((name_num,arg_count,prog),col_opt))) ⇒
  no_alloc r
Proof
  rw[word_to_wordTheory.compile_single_def]>>
  irule word_alloc_no_alloc>>
  TRY (irule three_to_two_reg_no_alloc)>>
  irule remove_dead_no_alloc>>
  irule remove_unreach_no_alloc>>
  irule word_common_subexp_elim_no_alloc>>
  irule full_ssa_cc_trans_no_alloc>>
  irule inst_select_no_alloc>>
  irule compile_exp_no_alloc>>rw[]
QED

Theorem code_rel_no_alloc:
  find_code op args c1 sz = SOME v ∧
  code_rel c1 c2 ∧
  no_alloc (FST (SND v)) ∧
  find_code op args c2 sz = SOME v' ⇒
  no_alloc (FST (SND v'))
Proof
  gs[code_rel_def]>>Cases_on ‘op’>>
  gs[find_code_def]>>every_case_tac>>rw[]>>gs[]>-
   (rename1 ‘lookup n c1 = SOME (q', r)’>>
    last_x_assum (qspecl_then [‘n’, ‘(q' ,r)’] assume_tac)>>gs[]>>
    drule_all compile_single_no_alloc>>gs[])>>
  res_tac>>gs[]>>rveq>>
  irule compile_single_no_alloc>>metis_tac[]
QED
||||||| 6eebd384c
Theorem const_fp_no_alloc:
  r = const_fp prog ∧ no_alloc prog ⇒
  no_alloc r
Proof
  gs[word_simpTheory.const_fp_def, const_fp_loop_no_alloc]
QED

Theorem SmartSeq_no_alloc:
  no_alloc prog ∧
  no_alloc prog' ⇒
  no_alloc (SmartSeq prog prog')
Proof
  rw[word_simpTheory.SmartSeq_def, no_alloc_def]
QED

Theorem apply_if_opt_SOME_no_alloc:
  no_alloc prog ∧ no_alloc prog' ∧
  apply_if_opt prog prog' = SOME x ⇒
  no_alloc x
Proof
  strip_tac>>
  fs [word_simpTheory.apply_if_opt_def]>>
  pairarg_tac \\ fs []>>
  rpt FULL_CASE_TAC>>gs[]
  >- (every_case_tac \\ fs [])>>
  rpt (FULL_CASE_TAC>>gs[])>>
  fs [word_simpProofTheory.dest_If_Eq_Imm_thm]>>
  gs[word_simpProofTheory.dest_If_thm]>>
  fs [word_simpTheory.SmartSeq_def]>>rveq>>
  IF_CASES_TAC>>gs[no_alloc_def]>>
  Cases_on ‘prog’>>gs[word_simpTheory.dest_Seq_def,
                      no_alloc_def]
QED

Theorem simp_if_no_alloc:
  no_alloc prog ⇒ no_alloc (simp_if prog)
Proof
  qid_spec_tac ‘prog’>> ho_match_mp_tac word_simpTheory.simp_if_ind>>
  rw[word_simpTheory.simp_if_def, no_alloc_def]>>
  TRY (every_case_tac>> gs[no_alloc_def])>>
  TRY (pairarg_tac>>gs[no_alloc_def])>>
  imp_res_tac apply_if_opt_SOME_no_alloc
QED

Theorem Seq_assoc_no_alloc:
  no_alloc prog ∧
  no_alloc prog' ⇒
  no_alloc (Seq_assoc prog prog')
Proof
  gs[GSYM AND_IMP_INTRO]>>
  qid_spec_tac ‘prog'’>>
  qid_spec_tac ‘prog’>>
  ho_match_mp_tac word_simpTheory.Seq_assoc_ind>>
  rw[no_alloc_def]
  >~[‘_ (_ _ (Call _ _ _ _))’]
  >- (
  gs[word_simpTheory.Seq_assoc_def,
     word_simpTheory.SmartSeq_def,
     no_alloc_def]>>
  every_case_tac>>gs[no_alloc_def])>>
  Cases_on ‘prog’>>
  gs[word_simpTheory.Seq_assoc_def,
     word_simpTheory.SmartSeq_def,
     no_alloc_def]
QED

Theorem compile_exp_no_alloc:
  no_alloc prog ⇒
  no_alloc (compile_exp prog)
Proof
  rw[word_simpTheory.compile_exp_def]>>
  irule const_fp_no_alloc>>gs[]>>
  qexists_tac ‘simp_if (Seq_assoc Skip prog)’>>rw[]>>
  irule simp_if_no_alloc>>
  irule Seq_assoc_no_alloc>>
  rw[no_alloc_def]
QED

Theorem inst_select_exp_no_alloc:
  no_alloc (inst_select_exp c c' n exp)
Proof
  MAP_EVERY qid_spec_tac [‘exp’, ‘n’, ‘c'’, ‘c’]>>
  ho_match_mp_tac word_instTheory.inst_select_exp_ind>>
  rw[word_instTheory.inst_select_exp_def,
     no_alloc_def]>>
  every_case_tac>>gs[no_alloc_def,
                     word_instTheory.inst_select_exp_def]
QED

Theorem inst_select_no_alloc:
  no_alloc prog ⇒
  no_alloc (inst_select c n prog)
Proof
  MAP_EVERY qid_spec_tac [‘prog’, ‘n’, ‘c’]>>
  ho_match_mp_tac word_instTheory.inst_select_ind>>
  rw[
      no_alloc_def]>>
  every_case_tac>>
  gs[inst_select_exp_no_alloc, word_instTheory.inst_select_def,
     no_alloc_def]>>
  every_case_tac>>
  gs[inst_select_exp_no_alloc, word_instTheory.inst_select_def,
     no_alloc_def]
QED

Theorem ssa_cc_trans_inst_no_alloc:
  ssa_cc_trans_inst i ssa na = (i',ssa',na') ⇒
  no_alloc i'
Proof
  MAP_EVERY qid_spec_tac [‘i'’, ‘ssa'’, ‘na'’, ‘na’, ‘ssa’, ‘i’]>>
  recInduct word_allocTheory.ssa_cc_trans_inst_ind>>
  rw[word_allocTheory.ssa_cc_trans_inst_def,
     no_alloc_def]>>
  rpt (pairarg_tac>>gs[])>>
  rw[word_allocTheory.ssa_cc_trans_inst_def,
     no_alloc_def]>>
  every_case_tac>>rw[]>>rveq>>
  gs[word_allocTheory.next_var_rename_def,
     no_alloc_def]
QED

Theorem fake_moves_no_alloc:
  fake_moves ls nL nR n = (prog1, prog2, n' ,ssa, ssa') ⇒
  no_alloc prog1 ∧ no_alloc prog2
Proof
  MAP_EVERY qid_spec_tac [‘ssa'’, ‘ssa’, ‘n'’, ‘prog2’, ‘prog1’, ‘n’, ‘nR’, ‘NL’, ‘ls’]>>
  Induct_on ‘ls’>>
  gs[word_allocTheory.fake_moves_def,
     no_alloc_def]>>rw[]>>
  pairarg_tac>>gs[]>>FULL_CASE_TAC>>gs[]>>
  every_case_tac>>
  rveq>>gs[no_alloc_def]>>
  rveq>>gs[no_alloc_def,
           word_allocTheory.fake_move_def]>>metis_tac[]
QED

Theorem ssa_cc_trans_no_alloc:
  no_alloc prog ∧
  ssa_cc_trans prog ssa n = (prog', ssa', na)⇒
  no_alloc prog'
Proof
  MAP_EVERY qid_spec_tac [‘prog'’, ‘ssa'’, ‘na’, ‘n’, ‘ssa’, ‘prog’]>>
  recInduct word_allocTheory.ssa_cc_trans_ind>>
  rw[word_allocTheory.ssa_cc_trans_def,
     word_allocTheory.fix_inconsistencies_def,
     word_allocTheory.list_next_var_rename_move_def,
     no_alloc_def]>>gs[]>>
  rpt (pairarg_tac>>gs[])>>rveq>>
  gs[word_allocTheory.ssa_cc_trans_def,
     word_allocTheory.fix_inconsistencies_def,
     word_allocTheory.list_next_var_rename_move_def,
     no_alloc_def]
  >- (drule ssa_cc_trans_inst_no_alloc>>rw[])
  >- (drule fake_moves_no_alloc>>rw[])
  >- (EVERY_CASE_TAC>>gs[]>>rveq>>gs[no_alloc_def]>>
    rpt (pairarg_tac>>gs[])>>rveq>>gs[no_alloc_def]>>
    drule fake_moves_no_alloc>>rw[])
QED

Theorem setup_ssa_no_alloc:
  no_alloc prog ∧
  setup_ssa n v prog = (mov, ssa, na)⇒
  no_alloc mov
Proof
  rw[word_allocTheory.setup_ssa_def]>>
  pairarg_tac>>gs[]>>
  rw[word_allocTheory.setup_ssa_def,
     word_allocTheory.list_next_var_rename_move_def,
     no_alloc_def]
QED

Theorem full_ssa_cc_trans_no_alloc:
  no_alloc prog ⇒
  no_alloc (full_ssa_cc_trans n prog)
Proof
  rw[word_allocTheory.full_ssa_cc_trans_def]>>
  pairarg_tac>>gs[]>>
  pairarg_tac>>
  drule_all setup_ssa_no_alloc>>
  rw[no_alloc_def]>>
  drule_all ssa_cc_trans_no_alloc>>
  rw[no_alloc_def]
QED

Theorem remove_dead_no_alloc:
  no_alloc prog ⇒
  no_alloc (FST (remove_dead prog q))
Proof
  MAP_EVERY qid_spec_tac [‘q’, ‘prog’]>>
  recInduct word_allocTheory.remove_dead_ind>>
  rw[word_allocTheory.remove_dead_def,
     no_alloc_def]>>gs[]>>
  rw[word_allocTheory.remove_dead_def,
     no_alloc_def]>>gs[]>>
  rpt (pairarg_tac>>gs[])>>rveq>>
  rw[no_alloc_def]>>gs[]>>
  every_case_tac>>rpt (pairarg_tac>>gs[])>>rveq>>
  rw[no_alloc_def]>>gs[]
QED

Theorem three_to_two_reg_no_alloc:
  no_alloc prog ⇒
  no_alloc (three_to_two_reg prog)
Proof
  qid_spec_tac ‘prog’>>
  recInduct word_instTheory.three_to_two_reg_ind>>
  rw[word_instTheory.three_to_two_reg_def,
     no_alloc_def]>>gs[]>>
  every_case_tac>>gs[]
QED

Theorem apply_colour_no_alloc:
  no_alloc prog ⇒
  no_alloc (apply_colour f prog)
Proof
  qid_spec_tac ‘prog’>>qid_spec_tac ‘f’>>
  recInduct word_allocTheory.apply_colour_ind>>
  rw[word_allocTheory.apply_colour_def,
     no_alloc_def]>>gs[]>>
  every_case_tac>>gs[]
QED

Theorem word_alloc_no_alloc:
  no_alloc prog ⇒
  no_alloc (word_alloc n c a r prog cl)
Proof
  rw[word_allocTheory.word_alloc_def]>>
  every_case_tac>>gs[no_alloc_def]
  >- (pairarg_tac>>gs[]>>
      every_case_tac>>gs[no_alloc_def]>>
      irule apply_colour_no_alloc>>rw[])>>
  gs[word_allocTheory.oracle_colour_ok_def]>>
  every_case_tac>>gs[no_alloc_def]>>rveq>>
  irule apply_colour_no_alloc>>rw[]
QED

Theorem word_common_subexp_elim_no_alloc:
  no_alloc prog ⇒
  no_alloc (word_common_subexp_elim prog)
Proof
  fs [word_cseTheory.word_common_subexp_elim_def]
  \\ pairarg_tac \\ fs []
  \\ rename [‘_ e p = (a,np)’]
  \\ pop_assum mp_tac
  \\ MAP_EVERY qid_spec_tac [‘np’,‘e’,‘a’,‘p’]
  \\ ho_match_mp_tac word_simpTheory.simp_if_ind
  \\ rpt strip_tac \\ fs []
  \\ fs [word_cseTheory.word_cse_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ gvs [no_alloc_def,AllCaseEqs(),word_cseTheory.add_to_data_aux_def]
  \\ res_tac \\ fs []
  \\ gvs [word_cseTheory.word_cseInst_def |> DefnBase.one_line_ify NONE,AllCaseEqs()]
  \\ gvs [no_alloc_def,AllCaseEqs(),word_cseTheory.add_to_data_aux_def,
          word_cseTheory.add_to_data_def]
QED

Theorem compile_single_no_alloc:
  no_alloc prog ∧
  (q, r) = (SND (compile_single two_reg_arith reg_count alg c
                 ((name_num,arg_count,prog),col_opt))) ⇒
  no_alloc r
Proof
  rw[word_to_wordTheory.compile_single_def]>>
  irule word_alloc_no_alloc>>
  TRY (irule three_to_two_reg_no_alloc)>>
  irule remove_dead_no_alloc>>
  irule word_common_subexp_elim_no_alloc>>
  irule full_ssa_cc_trans_no_alloc>>
  irule inst_select_no_alloc>>
  irule compile_exp_no_alloc>>rw[]
QED

Theorem code_rel_no_alloc:
  find_code op args c1 sz = SOME v ∧
  code_rel c1 c2 ∧
  no_alloc (FST (SND v)) ∧
  find_code op args c2 sz = SOME v' ⇒
  no_alloc (FST (SND v'))
Proof
  gs[code_rel_def]>>Cases_on ‘op’>>
  gs[find_code_def]>>every_case_tac>>rw[]>>gs[]>-
   (rename1 ‘lookup n c1 = SOME (q', r)’>>
    last_x_assum (qspecl_then [‘n’, ‘(q' ,r)’] assume_tac)>>gs[]>>
    drule_all compile_single_no_alloc>>gs[])>>
  res_tac>>gs[]>>rveq>>
  irule compile_single_no_alloc>>metis_tac[]
QED
=======
Triviality code_rel_no_install = code_rel_P |> Q.SPEC `(<>) (Install 0 0 0 0 LN)`
    |> REWRITE_RULE [GSYM no_install_subprogs_def]
>>>>>>> origin/master


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
                   simp[PULL_FORALL]>>
  completeInduct_on`prog_size (K 0) (prog:'a wordLang$prog)`>>
                   rpt strip_tac>>
  fs[PULL_FORALL,evaluate_def]>>
  Cases_on`prog`
  >- tac
  >- tac
  >- (Cases_on`i`>>
      fs[evaluate_def,inst_def,
         state_component_equality,assign_def,
         wordPropsTheory.word_exp_perm,mem_load_def,
         wordPropsTheory.get_var_perm,mem_store_def,
         get_var_def,wordPropsTheory.get_vars_perm,LET_THM,
         get_fp_var_def]>>
      EVERY_CASE_TAC>>
      fs[set_var_def,set_fp_var_def]>>
      rw[])
  >- tac
  >- tac
  >- tac
  >- tac
  >-
   (* Must_Terminate *)
   (fs[evaluate_def,AND_IMP_INTRO,
       no_alloc_def, no_install_def]>>
    IF_CASES_TAC>>
    fs[]>>
    last_x_assum(qspecl_then[`st with <|clock:=MustTerminate_limit(:'a);termdep:=st.termdep-1|>`,`p`,`l`] mp_tac)>>
    simp[]>>
    rw[]>>
    qexists_tac`perm'`>>fs[]>>
    pop_assum mp_tac >>
    rpt(pairarg_tac >> fs[])>>
    rw[]>> ntac 5 (pop_assum mp_tac) >>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    rw[] >> rw[]>>fs[state_component_equality])
  >- (*Call -- the hard case*)
   (
   fs[evaluate_def,
      no_alloc_def, no_install_def]>>
   TOP_CASE_TAC>> fs [] >>
   TOP_CASE_TAC>> fs []>>
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
   rw[]>>
   rfs[]
   >- (*Tail calls*)
    (
    ntac 2 (IF_CASES_TAC>>full_simp_tac(srw_ss())[])
    >-simp[flush_state_def,
           state_component_equality]>>
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
      drule (GEN_ALL code_rel_no_install)>>
      disch_then drule>>gs[]>>
      impl_tac
      >-(drule_all (INST_TYPE [beta|->alpha, gamma|->“:num”]
                    no_install_find_code)>>gs[])>>
      rw[]>>
      drule (GEN_ALL code_rel_no_alloc)>>
      disch_then drule>>gs[]>>
      impl_tac
      >-(drule_all (INST_TYPE [beta|->alpha, gamma|->“:num”]
                    no_alloc_find_code)>>gs[])>>
      rw[])>>
    srw_tac[][]>>
    Q.ISPECL_THEN [`n`,`q'`,`LENGTH q`,`stt with permute:=perm'`]
     mp_tac (Q.GEN `name` compile_single_lem)>>
    impl_tac>-
     (full_simp_tac(srw_ss())[Abbr`stt`,call_env_def,flush_state_def]>>
      simp[domain_fromList2,word_allocTheory.even_list_def,dec_clock_def])>>
    qpat_abbrev_tac`A = compile_single t k a c B`>>
                                       PairCases_on`A`>>srw_tac[][]>>full_simp_tac(srw_ss())[LET_THM]>>
    pop_assum mp_tac>>
    pairarg_tac>>full_simp_tac(srw_ss())[Abbr`stt`] >>
    strip_tac
    >-
     (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def,call_env_def,flush_state_def])>>
    Cases_on`res`>>full_simp_tac(srw_ss())[]
    >-
     (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def,call_env_def,flush_state_def])>>
    Cases_on`x' = Error`>>full_simp_tac(srw_ss())[]
    >-
     (qexists_tac`perm''`>>full_simp_tac(srw_ss())[dec_clock_def,call_env_def,flush_state_def])>>
    ntac 2 (pop_assum mp_tac) >>
    pairarg_tac>>full_simp_tac(srw_ss())[]>>
    rw[]>>
    qpat_x_assum`(λ(x,y). _) _`mp_tac >>
    pairarg_tac>>fs[]>>
    qpat_x_assum`Abbrev ((_,_,_) = _)` mp_tac>>
    simp[Once markerTheory.Abbrev_def]>>rw[]>>
    rw[]>>fs[dec_clock_def,call_env_def,flush_state_def]>>
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
   TOP_CASE_TAC>>full_simp_tac(srw_ss())[]>>
   TOP_CASE_TAC>>full_simp_tac(srw_ss())[]>>
   IF_CASES_TAC>-
    (Cases_on `o0` >> TRY (PairCases_on `x''`) >>
     fs[call_env_def,flush_state_def,state_component_equality,
        stack_size_def, stack_size_frame_def, push_env_def, env_to_list_def, LET_THM])>>
   fs[]>>
   qabbrev_tac`stt = call_env q r' (push_env x' o0 (dec_clock st))`>>
                              first_assum(qspecl_then[`stt`,`prog'`,`l`] mp_tac)>>
   impl_tac>-
    (fs[Abbr`stt`,dec_clock_def]>>
     DECIDE_TAC)>>
   impl_tac>-
    fs[Abbr`stt`,call_env_def,flush_state_def,wordPropsTheory.push_env_const,dec_clock_def]>>
   impl_tac>-
    (fs[Abbr`stt`,call_env_def,flush_state_def,dec_clock_def,word_simpProofTheory.push_env_gc_fun]>>
     qpat_x_assum ‘find_code _ _ st.code _ = _’ assume_tac>>
     drule (GEN_ALL code_rel_no_install)>>
     disch_then drule>>gs[]>>
     impl_tac
     >-(drule_all (INST_TYPE [beta|->alpha, gamma|->“:num”]
                   no_install_find_code)>>gs[])>>
     rw[]>>
     drule (GEN_ALL code_rel_no_alloc)>>
     disch_then drule>>gs[]>>
     impl_tac
     >-(drule_all (INST_TYPE [beta|->alpha, gamma|->“:num”]
                   no_alloc_find_code)>>gs[])>>
     rw[])>>
   rw[]>>
   Q.ISPECL_THEN [`n`,`q'`,`LENGTH q`,`stt with permute:=perm'`] mp_tac
    (Q.GEN `name` compile_single_lem)>>
   impl_tac>-
    (full_simp_tac(srw_ss())[Abbr`stt`,call_env_def,flush_state_def]>>
     simp[domain_fromList2,word_allocTheory.even_list_def,word_simpProofTheory.push_env_gc_fun,dec_clock_def])>>
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
   Cases_on`x''`>>full_simp_tac(srw_ss())[]
   >-
    (*Manual simulation for Result*)
    (Cases_on`w ≠ Loc xl1 xl2`>>full_simp_tac(srw_ss())[]
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
     reverse (Cases_on`domain x''.locals = domain x'`)>>full_simp_tac(srw_ss())[]
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
     last_x_assum(qspecl_then[`(set_var xn w0 x'') with permute:=rcst.permute`,`xrh`,`rst1.code`]mp_tac)>>
     impl_tac>-
      (simp[set_var_def]>>
       (*Monotonicity on 12, and dec_clock*)
       `rst.clock < st.clock` by
         (imp_res_tac evaluate_clock>>
          full_simp_tac(srw_ss())[call_env_def,flush_state_def,dec_clock_def]>>
          DECIDE_TAC)>>
       qpat_x_assum`A=SOME x''` mp_tac>>full_simp_tac(srw_ss())[pop_env_def]>>
       EVERY_CASE_TAC>>srw_tac[][state_component_equality]>>
       simp[])>>
     impl_tac>-
      (simp[set_var_def]>>
       imp_res_tac evaluate_clock>>full_simp_tac(srw_ss())[]>>
       imp_res_tac evaluate_clock>>
       Cases_on`o0`>>TRY(PairCases_on`x'''`)>>
       full_simp_tac(srw_ss())[call_env_def,flush_state_def,push_env_def,
                               LET_THM,dec_clock_def,env_to_list_def]>>
       imp_res_tac pop_env_termdep>>
       full_simp_tac(srw_ss())[])>>
     impl_tac>-
      (simp[set_var_def]>>
       imp_res_tac wordPropsTheory.pop_env_code_gc_fun_clock>>fs[]>>
       imp_res_tac wordPropsTheory.evaluate_consts>>
       fs[dec_clock_def]>>
       fs[word_allocProofTheory.word_state_eq_rel_def]>>
       gs[]>>
       gvs[] >>
       imp_res_tac no_install_evaluate_const_code >>
       imp_res_tac no_install_find_code >>
       gs []
      ) >>
     rw[]>>
     Q.ISPECL_THEN[`q'`,`call_env q r' (push_env x' o0 (dec_clock st)) with permute:=perm''`,`perm'''`] assume_tac wordPropsTheory.permute_swap_lemma>>
     rfs[]>>
     qexists_tac`λn. if n = 0:num then st.permute 0 else perm'''' (n-1)`>>
                                                                  Cases_on`o0`>>TRY(PairCases_on `x'''`)>>
     (fs[call_env_def,flush_state_def,
         push_env_def,dec_clock_def,
         env_to_list_def,ETA_AX,wordPropsTheory.pop_env_perm,
         wordPropsTheory.set_var_perm]>>
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
      pairarg_tac>>fs[set_var_def]))
   >-
    (*Manual simulation for Exceptions*)
    (Cases_on`o0`>>full_simp_tac(srw_ss())[]
     >-
      (pop_assum mp_tac >> pairarg_tac>>full_simp_tac(srw_ss())[]>>
       strip_tac >>
       qmatch_assum_abbrev_tac `evaluate(q',A) = _`>>
                                                  Q.ISPECL_THEN [`q'`,`A`,`rcst.permute`] mp_tac wordPropsTheory.permute_swap_lemma>>
       simp[Abbr`A`]>>
       impl_tac>-
        (qpat_x_assum`B=res'` sym_sub_tac>>full_simp_tac(srw_ss())[])>>
       rw[]>>
       qexists_tac`λn. if n = 0:num then st.permute 0 else perm''' (n-1)`>>
                                                                   fs[push_env_def,env_to_list_def,dec_clock_def,call_env_def,flush_state_def,ETA_AX]>>
       qpat_x_assum`(λ(x,y). _) _`mp_tac >>
       pairarg_tac>>rfs[]>>fs[]>>
       rw[]>>fs[word_allocProofTheory.word_state_eq_rel_def,state_component_equality]>>
       metis_tac[])
     >>
     qmatch_goalsub_rename_tac`push_env _ (SOME p)` >>
     PairCases_on`p`>>full_simp_tac(srw_ss())[]>>
     Cases_on`w ≠ Loc p2 p3`
     >-
      (qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
                                                                  full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def,call_env_def,flush_state_def,ETA_AX])>>
     Cases_on`domain rst.locals ≠ domain x'`
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
     last_x_assum(qspecl_then[`(set_var p0 w0 rst) with permute:=rcst.permute`,`p1`,`rst1.code`]mp_tac)>>
     impl_tac>-
      (simp[set_var_def]>>
       imp_res_tac evaluate_clock>>
       full_simp_tac(srw_ss())[call_env_def,flush_state_def,dec_clock_def]>>
       DECIDE_TAC)>>
     impl_tac>-
      (imp_res_tac evaluate_clock>>
       full_simp_tac(srw_ss())[set_var_def,call_env_def,flush_state_def,push_env_def,dec_clock_def,LET_THM,env_to_list_def])>>
     impl_tac>-
      (simp[set_var_def]>>
       imp_res_tac wordPropsTheory.pop_env_code_gc_fun_clock>>fs[]>>
       imp_res_tac wordPropsTheory.evaluate_consts>>fs[dec_clock_def]>>
       fs[word_allocProofTheory.word_state_eq_rel_def]>>
       gs[]>>
       qpat_assum ‘_ = (_, rst)’ assume_tac>>
       drule no_install_evaluate_const_code>>
       strip_tac>>gs[call_env_def,
                     push_env_def]>>
       qpat_x_assum ‘find_code _ _ st.code _ = _’ assume_tac>>
       drule_all (INST_TYPE [beta|->alpha, gamma|->“:num”]
                  no_alloc_find_code)>>gs[]>>
       drule_all (INST_TYPE [beta|->alpha, gamma|->“:num”]
                  no_install_find_code)>>gs[]>>
       ntac 2 strip_tac>>gs[])>>
     rw[]>>
     Q.ISPECL_THEN[`q'`,`call_env q r' (push_env x' (SOME (p0,p1,p2,p3)) (dec_clock st)) with permute:=perm''`,`perm'''`] assume_tac wordPropsTheory.permute_swap_lemma>>
     rfs[]>>
     qexists_tac`λn. if n = 0:num then st.permute 0 else perm'''' (n-1)` >>
     fs[call_env_def,flush_state_def,push_env_def,dec_clock_def,
        env_to_list_def,ETA_AX,wordPropsTheory.pop_env_perm,
        wordPropsTheory.set_var_perm]>>
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
       (unabbrev_all_tac>>fs[state_component_equality,word_allocProofTheory.word_state_eq_rel_def])>>
     rfs[]>>
     unabbrev_all_tac>>fs[])
   >>
   TRY(
     pop_assum mp_tac >> pairarg_tac>>
     fs[]>>
     Q.ISPECL_THEN [`q'`,`call_env q r' (push_env x' o0 (dec_clock st)) with permute:=perm''`,`rcst.permute`] mp_tac wordPropsTheory.permute_swap_lemma>>
     fs[]>>rw[]>>
     qexists_tac`λn. if n = 0:num then st.permute 0 else perm''' (n-1)`>>
                                                                 Cases_on`o0`>>TRY(PairCases_on`x''`)>>
     fs[push_env_def,env_to_list_def,dec_clock_def,call_env_def,flush_state_def,ETA_AX]>>
     qpat_x_assum`(λ(a,b). _) _`mp_tac >>
     pairarg_tac>>rfs[]>>
     fs[]>>rw[]>>
     fs[word_allocProofTheory.word_state_eq_rel_def,state_component_equality]>>
     metis_tac[])
   >>
   qexists_tac`λn. if n = 0:num then st.permute 0 else perm'' (n-1)`>>
                                                              Cases_on`o0`>>TRY(PairCases_on`x''`)>>
   fs[push_env_def,env_to_list_def,dec_clock_def,call_env_def,flush_state_def,ETA_AX])
  >- (*Seq, inductive*)
   (fs[evaluate_def,LET_THM,AND_IMP_INTRO]>>
    gs[no_install_def, no_alloc_def]>>
    first_assum(qspecl_then[`p`,`st`,`l`] mp_tac)>>
    impl_tac>- size_tac>>
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
     (gs[no_install_def, no_alloc_def]>>
      first_x_assum(qspecl_then[`p0`,`rst`,`rst1.code`] mp_tac)>>
      impl_tac>-(
       gs[no_install_def, no_alloc_def]>>
       ‘no_install_code rst.code ∧ no_alloc_code rst.code’
         by (qpat_assum ‘_ = (_, rst)’ assume_tac>>
             drule no_install_evaluate_const_code>>
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
     drule no_install_evaluate_const_code>>
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
      sh_mem_store_def,sh_mem_store_byte_def,sh_mem_store32_def] >>
    rpt (TOP_CASE_TAC >>
      fs[state_component_equality,set_var_def,flush_state_def]))
  >>gs[no_alloc_def, no_install_def]>>tac
QED

(******** more on no_mt **********)
<<<<<<< HEAD
(**
  no_mt simplifies full_compile_single, i.e.,
    full_compile_single = compile_single;
  also code_rel = code_rel_ext holds with no_mt
**)

Theorem const_fp_loop_no_mt:
  !prog p.
    no_mt prog ==>
    no_mt (FST (const_fp_loop prog p))
Proof
  recInduct word_simpTheory.const_fp_loop_ind>>
  rw[word_simpTheory.compile_exp_def, word_simpTheory.const_fp_loop_def]>>
  TRY (every_case_tac>> gs[no_mt_def])>>
  TRY (pairarg_tac>>gs[no_mt_def])>>
  gs[no_mt_def]>>
  pairarg_tac>>gs[no_mt_def]
QED

Theorem const_fp_no_mt:
  r = const_fp prog /\ no_mt prog ==>
  no_mt r
Proof
  gs[word_simpTheory.const_fp_def, const_fp_loop_no_mt]
QED

Theorem SmartSeq_no_mt:
  no_mt prog /\
  no_mt prog' ==>
  no_mt (SmartSeq prog prog')
Proof
  rw[word_simpTheory.SmartSeq_def, no_mt_def]
QED

Theorem apply_if_opt_SOME_no_mt:
  no_mt prog /\ no_mt prog' /\
  apply_if_opt prog prog' = SOME x ==>
  no_mt x
Proof
  strip_tac>>
  fs [word_simpTheory.apply_if_opt_def]>>
  pairarg_tac \\ fs []>>
  rpt FULL_CASE_TAC>>gs[]
  >- (every_case_tac \\ fs [])>>
  rpt (FULL_CASE_TAC>>gs[])>>
  fs [word_simpProofTheory.dest_If_Eq_Imm_thm]>>
  gs[word_simpProofTheory.dest_If_thm]>>
  fs [word_simpTheory.SmartSeq_def]>>rveq>>
  IF_CASES_TAC>>gs[no_mt_def]>>
  Cases_on ‘prog’>>gs[word_simpTheory.dest_Seq_def,
                      no_mt_def]
QED

Theorem simp_if_no_mt:
  no_mt prog ==> no_mt (simp_if prog)
Proof
  qid_spec_tac ‘prog’>> ho_match_mp_tac word_simpTheory.simp_if_ind>>
  rw[word_simpTheory.simp_if_def, no_mt_def]>>
  TRY (every_case_tac>> gs[no_mt_def])>>
  TRY (pairarg_tac>>gs[no_mt_def])>>
  imp_res_tac apply_if_opt_SOME_no_mt
QED

Theorem Seq_assoc_no_mt:
  no_mt prog /\
  no_mt prog' ==>
  no_mt (Seq_assoc prog prog')
Proof
  gs[GSYM AND_IMP_INTRO]>>
  qid_spec_tac ‘prog'’>>
  qid_spec_tac ‘prog’>>
  ho_match_mp_tac word_simpTheory.Seq_assoc_ind>>
  rw[no_mt_def]
  >~[‘_ (_ _ (Call _ _ _ _))’]
  >- (
  gs[word_simpTheory.Seq_assoc_def,
     word_simpTheory.SmartSeq_def,
     no_mt_def]>>
  every_case_tac>>gs[no_mt_def])>>
  Cases_on ‘prog’>>
  gs[word_simpTheory.Seq_assoc_def,
     word_simpTheory.SmartSeq_def,
     no_mt_def]
QED

Theorem compile_exp_no_mt:
  no_mt prog ==>
  no_mt (compile_exp prog)
Proof
  rw[word_simpTheory.compile_exp_def]>>
  irule const_fp_no_mt>>gs[]>>
  qexists_tac ‘simp_if (Seq_assoc Skip prog)’>>rw[]>>
  irule simp_if_no_mt>>
  irule Seq_assoc_no_mt>>
  rw[no_mt_def]
QED

Theorem inst_select_exp_no_mt:
  no_mt (inst_select_exp c c' n exp)
Proof
  MAP_EVERY qid_spec_tac [‘exp’, ‘n’, ‘c'’, ‘c’]>>
  ho_match_mp_tac word_instTheory.inst_select_exp_ind>>
  rw[word_instTheory.inst_select_exp_def,
     no_mt_def]>>
  every_case_tac>>gs[no_mt_def,
                     word_instTheory.inst_select_exp_def]
QED

Theorem inst_select_no_mt:
  no_mt prog ==>
  no_mt (inst_select c n prog)
Proof
  MAP_EVERY qid_spec_tac [‘prog’, ‘n’, ‘c’]>>
  ho_match_mp_tac word_instTheory.inst_select_ind>>
  rw[
      no_mt_def]>>
  every_case_tac>>
  gs[inst_select_exp_no_mt, word_instTheory.inst_select_def,
     no_mt_def]>>
  every_case_tac>>
  gs[inst_select_exp_no_mt, word_instTheory.inst_select_def,
     no_mt_def]
QED

Theorem ssa_cc_trans_inst_no_mt:
  ssa_cc_trans_inst i ssa na = (i',ssa',na') ==>
  no_mt i'
Proof
  MAP_EVERY qid_spec_tac [‘i'’, ‘ssa'’, ‘na'’, ‘na’, ‘ssa’, ‘i’]>>
  recInduct word_allocTheory.ssa_cc_trans_inst_ind>>
  rw[word_allocTheory.ssa_cc_trans_inst_def,
     no_mt_def]>>
  rpt (pairarg_tac>>gs[])>>
  rw[word_allocTheory.ssa_cc_trans_inst_def,
     no_mt_def]>>
  every_case_tac>>rw[]>>rveq>>
  gs[word_allocTheory.next_var_rename_def,
     no_mt_def]
QED

Theorem fake_moves_no_mt:
  fake_moves prio ls nL nR n = (prog1, prog2, n' ,ssa, ssa') ==>
  no_mt prog1 /\ no_mt prog2
Proof
  MAP_EVERY qid_spec_tac [‘ssa'’, ‘ssa’, ‘n'’, ‘prog2’, ‘prog1’, ‘n’, ‘nR’, ‘NL’, ‘ls’]>>
  Induct_on ‘ls’>>
  gs[word_allocTheory.fake_moves_def,
     no_mt_def]>>rw[]>>
  pairarg_tac>>gs[]>>FULL_CASE_TAC>>gs[]>>
  every_case_tac>>
  rveq>>gs[no_mt_def]>>
  rveq>>gs[no_mt_def,
           word_allocTheory.fake_move_def]>>metis_tac[]
QED

Theorem ssa_cc_trans_no_mt:
  no_mt prog /\
  ssa_cc_trans prog ssa n = (prog', ssa', na)==>
  no_mt prog'
Proof
  MAP_EVERY qid_spec_tac [‘prog'’, ‘ssa'’, ‘na’, ‘n’, ‘ssa’, ‘prog’]>>
  recInduct word_allocTheory.ssa_cc_trans_ind>>
  rw[word_allocTheory.ssa_cc_trans_def,
     word_allocTheory.fix_inconsistencies_def,
     word_allocTheory.list_next_var_rename_move_def,
     no_mt_def]>>gs[]>>
  rpt (pairarg_tac>>gs[])>>rveq>>
  gs[word_allocTheory.ssa_cc_trans_def,
     word_allocTheory.fix_inconsistencies_def,
     word_allocTheory.list_next_var_rename_move_def,
     no_mt_def]
  >- (drule ssa_cc_trans_inst_no_mt>>rw[])
  >- (drule fake_moves_no_mt>>rw[])
  >- (EVERY_CASE_TAC>>gs[]>>rveq>>gs[no_mt_def]>>
    rpt (pairarg_tac>>gs[])>>rveq>>gs[no_mt_def]>>
    drule fake_moves_no_mt>>rw[])
QED

Theorem setup_ssa_no_mt:
  no_mt prog /\
  setup_ssa n v prog = (mov, ssa, na)==>
  no_mt mov
Proof
  rw[word_allocTheory.setup_ssa_def]>>
  pairarg_tac>>gs[]>>
  rw[word_allocTheory.setup_ssa_def,
     word_allocTheory.list_next_var_rename_move_def,
     no_mt_def]
QED

Theorem full_ssa_cc_trans_no_mt:
  no_mt prog ==>
  no_mt (full_ssa_cc_trans n prog)
Proof
  rw[word_allocTheory.full_ssa_cc_trans_def]>>
  pairarg_tac>>gs[]>>
  pairarg_tac>>
  drule_all setup_ssa_no_mt>>
  rw[no_mt_def]>>
  drule_all ssa_cc_trans_no_mt>>
  rw[no_mt_def]
QED

Theorem remove_dead_no_mt:
  no_mt prog ==>
  no_mt (FST (remove_dead prog q))
Proof
  MAP_EVERY qid_spec_tac [‘q’, ‘prog’]>>
  recInduct word_allocTheory.remove_dead_ind>>
  rw[word_allocTheory.remove_dead_def,
     no_mt_def]>>gs[]>>
  rw[word_allocTheory.remove_dead_def,
     no_mt_def]>>gs[]>>
  rpt (pairarg_tac>>gs[])>>rveq>>
  rw[no_mt_def]>>gs[]>>
  every_case_tac>>rpt (pairarg_tac>>gs[])>>rveq>>
  rw[no_mt_def]>>gs[]
QED

Theorem three_to_two_reg_no_mt:
  no_mt prog ==>
  no_mt (three_to_two_reg prog)
Proof
  qid_spec_tac ‘prog’>>
  recInduct word_instTheory.three_to_two_reg_ind>>
  rw[word_instTheory.three_to_two_reg_def,
     no_mt_def]>>gs[]>>
  every_case_tac>>gs[]
QED

Theorem apply_colour_no_mt:
  no_mt prog ==>
  no_mt (apply_colour f prog)
Proof
  qid_spec_tac ‘prog’>>qid_spec_tac ‘f’>>
  recInduct word_allocTheory.apply_colour_ind>>
  rw[word_allocTheory.apply_colour_def,
     no_mt_def]>>gs[]>>
  every_case_tac>>gs[]
QED

Theorem word_alloc_no_mt:
  no_mt prog ==>
  no_mt (word_alloc n c a r prog cl)
Proof
  rw[word_allocTheory.word_alloc_def]>>
  every_case_tac>>gs[no_mt_def]
  >- (pairarg_tac>>gs[]>>
      every_case_tac>>gs[no_mt_def]>>
      irule apply_colour_no_mt>>rw[])>>
  gs[word_allocTheory.oracle_colour_ok_def]>>
  every_case_tac>>gs[no_mt_def]>>rveq>>
  irule apply_colour_no_mt>>rw[]
QED

Theorem word_common_subexp_elim_no_mt:
  no_mt prog ⇒
  no_mt (word_common_subexp_elim prog)
Proof
  fs [word_cseTheory.word_common_subexp_elim_def]
  \\ pairarg_tac \\ fs []
  \\ rename [‘_ e p = (a,np)’]
  \\ pop_assum mp_tac
  \\ MAP_EVERY qid_spec_tac [‘np’,‘e’,‘a’,‘p’]
  \\ ho_match_mp_tac word_simpTheory.simp_if_ind
  \\ rpt strip_tac \\ fs []
  \\ fs [word_cseTheory.word_cse_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ gvs [no_mt_def,AllCaseEqs(),word_cseTheory.add_to_data_aux_def]
  \\ res_tac \\ fs []
  \\ gvs [word_cseTheory.word_cseInst_def |> DefnBase.one_line_ify NONE,AllCaseEqs()]
  \\ gvs [no_mt_def,AllCaseEqs(),word_cseTheory.add_to_data_aux_def,
          word_cseTheory.add_to_data_def]
QED

Theorem SimpSeq_no_mt:
  no_mt p1 ∧ no_mt p2 ⇒
  no_mt (SimpSeq p1 p2)
Proof
  rw [SimpSeq_def,no_mt_def]
  \\ Cases_on ‘p1’ \\ rw [no_mt_def]
QED

Theorem Seq_assoc_right_lemma_no_mt:
  ∀p1 p2.
  no_mt p1 ∧ no_mt p2 ⇒
  no_mt (Seq_assoc_right p1 p2)
Proof
  HO_MATCH_MP_TAC Seq_assoc_right_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_right_def,no_mt_def]
  >~ [`Call`]
  >- (
    every_case_tac \\ gvs[no_mt_def]
    \\ match_mp_tac SimpSeq_no_mt
    \\ gvs[no_mt_def])
  \\ match_mp_tac SimpSeq_no_mt
  \\ gvs[no_mt_def]
QED

Theorem remove_unreach_no_mt:
  no_mt p ⇒
  no_mt (remove_unreach p)
Proof
  rw[remove_unreach_def]
  \\ irule Seq_assoc_right_lemma_no_mt
  \\ gvs[no_mt_def]
QED

Theorem compile_single_no_mt:
  no_mt prog /\
  (q, r) = (SND (compile_single two_reg_arith reg_count alg c
                 ((name_num,arg_count,prog),col_opt))) ==>
  no_mt r
Proof
  rw[word_to_wordTheory.compile_single_def]>>
  irule word_alloc_no_mt>>
  TRY (irule three_to_two_reg_no_mt)>>
  irule remove_dead_no_mt>>
  irule remove_unreach_no_mt>>
  irule word_common_subexp_elim_no_mt>>
  irule full_ssa_cc_trans_no_mt>>
  irule inst_select_no_mt>>
  irule compile_exp_no_mt>>rw[]
QED

Theorem code_rel_no_mt:
  wordSem$find_code op args c1 sz = SOME v /\
  code_rel c1 c2 /\
  no_mt (FST (SND v)) /\
  find_code op args c2 sz = SOME v' ==>
  no_mt (FST (SND v'))
Proof
  gs[code_rel_def]>>Cases_on ‘op’>>
  gs[wordSemTheory.find_code_def]>>every_case_tac>>rw[]>>gs[]>-
   (rename1 ‘lookup n c1 = SOME (q', r)’>>
    last_x_assum (qspecl_then [‘n’, ‘(q' ,r)’] assume_tac)>>gs[]>>
    drule_all compile_single_no_mt>>gs[])>>
  res_tac>>gs[]>>rveq>>
  irule compile_single_no_mt>>metis_tac[]
QED
||||||| 6eebd384c
(**
  no_mt simplifies full_compile_single, i.e.,
    full_compile_single = compile_single;
  also code_rel = code_rel_ext holds with no_mt
**)

Theorem const_fp_loop_no_mt:
  !prog p.
    no_mt prog ==>
    no_mt (FST (const_fp_loop prog p))
Proof
  recInduct word_simpTheory.const_fp_loop_ind>>
  rw[word_simpTheory.compile_exp_def, word_simpTheory.const_fp_loop_def]>>
  TRY (every_case_tac>> gs[no_mt_def])>>
  TRY (pairarg_tac>>gs[no_mt_def])>>
  gs[no_mt_def]>>
  pairarg_tac>>gs[no_mt_def]
QED

Theorem const_fp_no_mt:
  r = const_fp prog /\ no_mt prog ==>
  no_mt r
Proof
  gs[word_simpTheory.const_fp_def, const_fp_loop_no_mt]
QED

Theorem SmartSeq_no_mt:
  no_mt prog /\
  no_mt prog' ==>
  no_mt (SmartSeq prog prog')
Proof
  rw[word_simpTheory.SmartSeq_def, no_mt_def]
QED

Theorem apply_if_opt_SOME_no_mt:
  no_mt prog /\ no_mt prog' /\
  apply_if_opt prog prog' = SOME x ==>
  no_mt x
Proof
  strip_tac>>
  fs [word_simpTheory.apply_if_opt_def]>>
  pairarg_tac \\ fs []>>
  rpt FULL_CASE_TAC>>gs[]
  >- (every_case_tac \\ fs [])>>
  rpt (FULL_CASE_TAC>>gs[])>>
  fs [word_simpProofTheory.dest_If_Eq_Imm_thm]>>
  gs[word_simpProofTheory.dest_If_thm]>>
  fs [word_simpTheory.SmartSeq_def]>>rveq>>
  IF_CASES_TAC>>gs[no_mt_def]>>
  Cases_on ‘prog’>>gs[word_simpTheory.dest_Seq_def,
                      no_mt_def]
QED

Theorem simp_if_no_mt:
  no_mt prog ==> no_mt (simp_if prog)
Proof
  qid_spec_tac ‘prog’>> ho_match_mp_tac word_simpTheory.simp_if_ind>>
  rw[word_simpTheory.simp_if_def, no_mt_def]>>
  TRY (every_case_tac>> gs[no_mt_def])>>
  TRY (pairarg_tac>>gs[no_mt_def])>>
  imp_res_tac apply_if_opt_SOME_no_mt
QED

Theorem Seq_assoc_no_mt:
  no_mt prog /\
  no_mt prog' ==>
  no_mt (Seq_assoc prog prog')
Proof
  gs[GSYM AND_IMP_INTRO]>>
  qid_spec_tac ‘prog'’>>
  qid_spec_tac ‘prog’>>
  ho_match_mp_tac word_simpTheory.Seq_assoc_ind>>
  rw[no_mt_def]
  >~[‘_ (_ _ (Call _ _ _ _))’]
  >- (
  gs[word_simpTheory.Seq_assoc_def,
     word_simpTheory.SmartSeq_def,
     no_mt_def]>>
  every_case_tac>>gs[no_mt_def])>>
  Cases_on ‘prog’>>
  gs[word_simpTheory.Seq_assoc_def,
     word_simpTheory.SmartSeq_def,
     no_mt_def]
QED

Theorem compile_exp_no_mt:
  no_mt prog ==>
  no_mt (compile_exp prog)
Proof
  rw[word_simpTheory.compile_exp_def]>>
  irule const_fp_no_mt>>gs[]>>
  qexists_tac ‘simp_if (Seq_assoc Skip prog)’>>rw[]>>
  irule simp_if_no_mt>>
  irule Seq_assoc_no_mt>>
  rw[no_mt_def]
QED

Theorem inst_select_exp_no_mt:
  no_mt (inst_select_exp c c' n exp)
Proof
  MAP_EVERY qid_spec_tac [‘exp’, ‘n’, ‘c'’, ‘c’]>>
  ho_match_mp_tac word_instTheory.inst_select_exp_ind>>
  rw[word_instTheory.inst_select_exp_def,
     no_mt_def]>>
  every_case_tac>>gs[no_mt_def,
                     word_instTheory.inst_select_exp_def]
QED

Theorem inst_select_no_mt:
  no_mt prog ==>
  no_mt (inst_select c n prog)
Proof
  MAP_EVERY qid_spec_tac [‘prog’, ‘n’, ‘c’]>>
  ho_match_mp_tac word_instTheory.inst_select_ind>>
  rw[
      no_mt_def]>>
  every_case_tac>>
  gs[inst_select_exp_no_mt, word_instTheory.inst_select_def,
     no_mt_def]>>
  every_case_tac>>
  gs[inst_select_exp_no_mt, word_instTheory.inst_select_def,
     no_mt_def]
QED

Theorem ssa_cc_trans_inst_no_mt:
  ssa_cc_trans_inst i ssa na = (i',ssa',na') ==>
  no_mt i'
Proof
  MAP_EVERY qid_spec_tac [‘i'’, ‘ssa'’, ‘na'’, ‘na’, ‘ssa’, ‘i’]>>
  recInduct word_allocTheory.ssa_cc_trans_inst_ind>>
  rw[word_allocTheory.ssa_cc_trans_inst_def,
     no_mt_def]>>
  rpt (pairarg_tac>>gs[])>>
  rw[word_allocTheory.ssa_cc_trans_inst_def,
     no_mt_def]>>
  every_case_tac>>rw[]>>rveq>>
  gs[word_allocTheory.next_var_rename_def,
     no_mt_def]
QED

Theorem fake_moves_no_mt:
  fake_moves ls nL nR n = (prog1, prog2, n' ,ssa, ssa') ==>
  no_mt prog1 /\ no_mt prog2
Proof
  MAP_EVERY qid_spec_tac [‘ssa'’, ‘ssa’, ‘n'’, ‘prog2’, ‘prog1’, ‘n’, ‘nR’, ‘NL’, ‘ls’]>>
  Induct_on ‘ls’>>
  gs[word_allocTheory.fake_moves_def,
     no_mt_def]>>rw[]>>
  pairarg_tac>>gs[]>>FULL_CASE_TAC>>gs[]>>
  every_case_tac>>
  rveq>>gs[no_mt_def]>>
  rveq>>gs[no_mt_def,
           word_allocTheory.fake_move_def]>>metis_tac[]
QED

Theorem ssa_cc_trans_no_mt:
  no_mt prog /\
  ssa_cc_trans prog ssa n = (prog', ssa', na)==>
  no_mt prog'
Proof
  MAP_EVERY qid_spec_tac [‘prog'’, ‘ssa'’, ‘na’, ‘n’, ‘ssa’, ‘prog’]>>
  recInduct word_allocTheory.ssa_cc_trans_ind>>
  rw[word_allocTheory.ssa_cc_trans_def,
     word_allocTheory.fix_inconsistencies_def,
     word_allocTheory.list_next_var_rename_move_def,
     no_mt_def]>>gs[]>>
  rpt (pairarg_tac>>gs[])>>rveq>>
  gs[word_allocTheory.ssa_cc_trans_def,
     word_allocTheory.fix_inconsistencies_def,
     word_allocTheory.list_next_var_rename_move_def,
     no_mt_def]
  >- (drule ssa_cc_trans_inst_no_mt>>rw[])
  >- (drule fake_moves_no_mt>>rw[])
  >- (EVERY_CASE_TAC>>gs[]>>rveq>>gs[no_mt_def]>>
    rpt (pairarg_tac>>gs[])>>rveq>>gs[no_mt_def]>>
    drule fake_moves_no_mt>>rw[])
QED

Theorem setup_ssa_no_mt:
  no_mt prog /\
  setup_ssa n v prog = (mov, ssa, na)==>
  no_mt mov
Proof
  rw[word_allocTheory.setup_ssa_def]>>
  pairarg_tac>>gs[]>>
  rw[word_allocTheory.setup_ssa_def,
     word_allocTheory.list_next_var_rename_move_def,
     no_mt_def]
QED

Theorem full_ssa_cc_trans_no_mt:
  no_mt prog ==>
  no_mt (full_ssa_cc_trans n prog)
Proof
  rw[word_allocTheory.full_ssa_cc_trans_def]>>
  pairarg_tac>>gs[]>>
  pairarg_tac>>
  drule_all setup_ssa_no_mt>>
  rw[no_mt_def]>>
  drule_all ssa_cc_trans_no_mt>>
  rw[no_mt_def]
QED

Theorem remove_dead_no_mt:
  no_mt prog ==>
  no_mt (FST (remove_dead prog q))
Proof
  MAP_EVERY qid_spec_tac [‘q’, ‘prog’]>>
  recInduct word_allocTheory.remove_dead_ind>>
  rw[word_allocTheory.remove_dead_def,
     no_mt_def]>>gs[]>>
  rw[word_allocTheory.remove_dead_def,
     no_mt_def]>>gs[]>>
  rpt (pairarg_tac>>gs[])>>rveq>>
  rw[no_mt_def]>>gs[]>>
  every_case_tac>>rpt (pairarg_tac>>gs[])>>rveq>>
  rw[no_mt_def]>>gs[]
QED

Theorem three_to_two_reg_no_mt:
  no_mt prog ==>
  no_mt (three_to_two_reg prog)
Proof
  qid_spec_tac ‘prog’>>
  recInduct word_instTheory.three_to_two_reg_ind>>
  rw[word_instTheory.three_to_two_reg_def,
     no_mt_def]>>gs[]>>
  every_case_tac>>gs[]
QED

Theorem apply_colour_no_mt:
  no_mt prog ==>
  no_mt (apply_colour f prog)
Proof
  qid_spec_tac ‘prog’>>qid_spec_tac ‘f’>>
  recInduct word_allocTheory.apply_colour_ind>>
  rw[word_allocTheory.apply_colour_def,
     no_mt_def]>>gs[]>>
  every_case_tac>>gs[]
QED

Theorem word_alloc_no_mt:
  no_mt prog ==>
  no_mt (word_alloc n c a r prog cl)
Proof
  rw[word_allocTheory.word_alloc_def]>>
  every_case_tac>>gs[no_mt_def]
  >- (pairarg_tac>>gs[]>>
      every_case_tac>>gs[no_mt_def]>>
      irule apply_colour_no_mt>>rw[])>>
  gs[word_allocTheory.oracle_colour_ok_def]>>
  every_case_tac>>gs[no_mt_def]>>rveq>>
  irule apply_colour_no_mt>>rw[]
QED

Theorem word_common_subexp_elim_no_mt:
  no_mt prog ⇒
  no_mt (word_common_subexp_elim prog)
Proof
  fs [word_cseTheory.word_common_subexp_elim_def]
  \\ pairarg_tac \\ fs []
  \\ rename [‘_ e p = (a,np)’]
  \\ pop_assum mp_tac
  \\ MAP_EVERY qid_spec_tac [‘np’,‘e’,‘a’,‘p’]
  \\ ho_match_mp_tac word_simpTheory.simp_if_ind
  \\ rpt strip_tac \\ fs []
  \\ fs [word_cseTheory.word_cse_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ gvs [no_mt_def,AllCaseEqs(),word_cseTheory.add_to_data_aux_def]
  \\ res_tac \\ fs []
  \\ gvs [word_cseTheory.word_cseInst_def |> DefnBase.one_line_ify NONE,AllCaseEqs()]
  \\ gvs [no_mt_def,AllCaseEqs(),word_cseTheory.add_to_data_aux_def,
          word_cseTheory.add_to_data_def]
QED

Theorem compile_single_no_mt:
  no_mt prog /\
  (q, r) = (SND (compile_single two_reg_arith reg_count alg c
                 ((name_num,arg_count,prog),col_opt))) ==>
  no_mt r
Proof
  rw[word_to_wordTheory.compile_single_def]>>
  irule word_alloc_no_mt>>
  TRY (irule three_to_two_reg_no_mt)>>
  irule remove_dead_no_mt>>
  irule word_common_subexp_elim_no_mt>>
  irule full_ssa_cc_trans_no_mt>>
  irule inst_select_no_mt>>
  irule compile_exp_no_mt>>rw[]
QED

Theorem code_rel_no_mt:
  wordSem$find_code op args c1 sz = SOME v /\
  code_rel c1 c2 /\
  no_mt (FST (SND v)) /\
  find_code op args c2 sz = SOME v' ==>
  no_mt (FST (SND v'))
Proof
  gs[code_rel_def]>>Cases_on ‘op’>>
  gs[wordSemTheory.find_code_def]>>every_case_tac>>rw[]>>gs[]>-
   (rename1 ‘lookup n c1 = SOME (q', r)’>>
    last_x_assum (qspecl_then [‘n’, ‘(q' ,r)’] assume_tac)>>gs[]>>
    drule_all compile_single_no_mt>>gs[])>>
  res_tac>>gs[]>>rveq>>
  irule compile_single_no_mt>>metis_tac[]
QED
=======
>>>>>>> origin/master

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
  irule compile_single_not_created >>
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
  drule (GEN_ALL no_mt_full_compile_single)>>gs[]>>metis_tac[]
QED

(**** more on no_share_inst ****)

<<<<<<< HEAD
Theorem const_fp_loop_no_share_inst:
  ∀prog p.
    no_share_inst prog ⇒
    no_share_inst (FST (const_fp_loop prog p))
Proof
  recInduct word_simpTheory.const_fp_loop_ind>>
  rw[word_simpTheory.compile_exp_def, word_simpTheory.const_fp_loop_def]>>
  TRY (every_case_tac>> gs[no_share_inst_def])>>
  TRY (pairarg_tac>>gs[no_share_inst_def])>>
  gs[no_share_inst_def]>>
  pairarg_tac>>gs[no_share_inst_def]
QED

Theorem const_fp_no_share_inst:
  r = const_fp prog ∧ no_share_inst prog ⇒
  no_share_inst r
Proof
  gs[word_simpTheory.const_fp_def, const_fp_loop_no_share_inst]
QED

Theorem SmartSeq_no_share_inst:
  no_share_inst prog ∧
  no_share_inst prog' ⇒
  no_share_inst (SmartSeq prog prog')
Proof
  rw[word_simpTheory.SmartSeq_def, no_share_inst_def]
QED

Theorem apply_if_opt_SOME_no_share_inst:
  no_share_inst prog ∧ no_share_inst prog' ∧
  apply_if_opt prog prog' = SOME x ⇒
  no_share_inst x
Proof
  strip_tac>>
  fs [word_simpTheory.apply_if_opt_def]>>
  pairarg_tac \\ fs []>>
  rpt FULL_CASE_TAC>>gs[]
  >- (every_case_tac \\ fs [])>>
  rpt (FULL_CASE_TAC>>gs[])>>
  fs [word_simpProofTheory.dest_If_Eq_Imm_thm]>>
  gs[word_simpProofTheory.dest_If_thm]>>
  fs [word_simpTheory.SmartSeq_def]>>rveq>>
  IF_CASES_TAC>>gs[no_share_inst_def]>>
  Cases_on ‘prog’>>gs[word_simpTheory.dest_Seq_def,
                      no_share_inst_def]
QED

Theorem simp_if_no_share_inst:
  no_share_inst prog ⇒ no_share_inst (simp_if prog)
Proof
  qid_spec_tac ‘prog’>> ho_match_mp_tac word_simpTheory.simp_if_ind>>
  rw[word_simpTheory.simp_if_def, no_share_inst_def]>>
  TRY (every_case_tac>> gs[no_share_inst_def])>>
  TRY (pairarg_tac>>gs[no_share_inst_def])>>
  imp_res_tac apply_if_opt_SOME_no_share_inst
QED

Theorem Seq_assoc_no_share_inst:
  no_share_inst prog ∧
  no_share_inst prog' ⇒
  no_share_inst (Seq_assoc prog prog')
Proof
  gs[GSYM AND_IMP_INTRO]>>
  qid_spec_tac ‘prog'’>>
  qid_spec_tac ‘prog’>>
  ho_match_mp_tac word_simpTheory.Seq_assoc_ind>>
  rw[no_share_inst_def]
  >~[‘_ (_ _ (Call _ _ _ _))’]
  >- (
  gs[word_simpTheory.Seq_assoc_def,
     word_simpTheory.SmartSeq_def,
     no_share_inst_def]>>
  every_case_tac>>gs[no_share_inst_def])>>
  Cases_on ‘prog’>>
  gs[word_simpTheory.Seq_assoc_def,
     word_simpTheory.SmartSeq_def,
     no_share_inst_def]
QED

Theorem compile_exp_no_share_inst:
  no_share_inst prog ⇒
  no_share_inst (compile_exp prog)
Proof
  rw[word_simpTheory.compile_exp_def]>>
  irule const_fp_no_share_inst>>gs[]>>
  qexists_tac ‘simp_if (Seq_assoc Skip prog)’>>rw[]>>
  irule simp_if_no_share_inst>>
  irule Seq_assoc_no_share_inst>>
  rw[no_share_inst_def]
QED

Theorem inst_select_exp_no_share_inst:
  no_share_inst (inst_select_exp c c' n exp)
Proof
  MAP_EVERY qid_spec_tac [‘exp’, ‘n’, ‘c'’, ‘c’]>>
  ho_match_mp_tac word_instTheory.inst_select_exp_ind>>
  rw[word_instTheory.inst_select_exp_def,
     no_share_inst_def]>>
  every_case_tac>>gs[no_share_inst_def,
                     word_instTheory.inst_select_exp_def]
QED

Theorem inst_select_no_share_inst:
  no_share_inst prog ⇒
  no_share_inst (inst_select c n prog)
Proof
  MAP_EVERY qid_spec_tac [‘prog’, ‘n’, ‘c’]>>
  ho_match_mp_tac word_instTheory.inst_select_ind>>
  rw[
      no_share_inst_def]>>
  every_case_tac>>
  gs[inst_select_exp_no_share_inst, word_instTheory.inst_select_def,
     no_share_inst_def]>>
  every_case_tac>>
  gs[inst_select_exp_no_share_inst, word_instTheory.inst_select_def,
     no_share_inst_def]
QED

Theorem ssa_cc_trans_inst_no_share_inst:
  ssa_cc_trans_inst i ssa na = (i',ssa',na') ⇒
  no_share_inst i'
Proof
  MAP_EVERY qid_spec_tac [‘i'’, ‘ssa'’, ‘na'’, ‘na’, ‘ssa’, ‘i’]>>
  recInduct word_allocTheory.ssa_cc_trans_inst_ind>>
  rw[word_allocTheory.ssa_cc_trans_inst_def,
     no_share_inst_def]>>
  rpt (pairarg_tac>>gs[])>>
  rw[word_allocTheory.ssa_cc_trans_inst_def,
     no_share_inst_def]>>
  every_case_tac>>rw[]>>rveq>>
  gs[word_allocTheory.next_var_rename_def,
     no_share_inst_def]
QED

Theorem fake_moves_no_share_inst:
  fake_moves prio ls nL nR n = (prog1, prog2, n' ,ssa, ssa') ⇒
  no_share_inst prog1 ∧ no_share_inst prog2
Proof
  MAP_EVERY qid_spec_tac [‘ssa'’, ‘ssa’, ‘n'’, ‘prog2’, ‘prog1’, ‘n’, ‘nR’, ‘NL’, ‘ls’]>>
  Induct_on ‘ls’>>
  gs[word_allocTheory.fake_moves_def,
     no_share_inst_def]>>rw[]>>
  pairarg_tac>>gs[]>>FULL_CASE_TAC>>gs[]>>
  every_case_tac>>
  rveq>>gs[no_share_inst_def]>>
  rveq>>gs[no_share_inst_def,
           word_allocTheory.fake_move_def]>>metis_tac[]
QED

Theorem ssa_cc_trans_no_share_inst:
  no_share_inst prog ∧
  ssa_cc_trans prog ssa n = (prog', ssa', na)⇒
  no_share_inst prog'
Proof
  MAP_EVERY qid_spec_tac [‘prog'’, ‘ssa'’, ‘na’, ‘n’, ‘ssa’, ‘prog’]>>
  recInduct word_allocTheory.ssa_cc_trans_ind>>
  rw[word_allocTheory.ssa_cc_trans_def,
     word_allocTheory.fix_inconsistencies_def,
     word_allocTheory.list_next_var_rename_move_def,
     no_share_inst_def]>>gs[]>>
  rpt (pairarg_tac>>gs[])>>rveq>>
  gs[word_allocTheory.ssa_cc_trans_def,
     word_allocTheory.fix_inconsistencies_def,
     word_allocTheory.list_next_var_rename_move_def,
     no_share_inst_def]
  >- (drule ssa_cc_trans_inst_no_share_inst>>rw[])
  >- (drule fake_moves_no_share_inst>>rw[])
  >- (EVERY_CASE_TAC>>gs[]>>rveq>>gs[no_share_inst_def]>>
    rpt (pairarg_tac>>gs[])>>rveq>>gs[no_share_inst_def]>>
    drule fake_moves_no_share_inst>>rw[])
QED

Theorem setup_ssa_no_share_inst:
  no_share_inst prog ∧
  setup_ssa n v prog = (mov, ssa, na)⇒
  no_share_inst mov
Proof
  rw[word_allocTheory.setup_ssa_def]>>
  pairarg_tac>>gs[]>>
  rw[word_allocTheory.setup_ssa_def,
     word_allocTheory.list_next_var_rename_move_def,
     no_share_inst_def]
QED

Theorem full_ssa_cc_trans_no_share_inst:
  no_share_inst prog ⇒
  no_share_inst (full_ssa_cc_trans n prog)
Proof
  rw[word_allocTheory.full_ssa_cc_trans_def]>>
  pairarg_tac>>gs[]>>
  pairarg_tac>>
  drule_all setup_ssa_no_share_inst>>
  rw[no_share_inst_def]>>
  drule_all ssa_cc_trans_no_share_inst>>
  rw[no_share_inst_def]
QED

Theorem remove_dead_no_share_inst:
  no_share_inst prog ⇒
  no_share_inst (FST (remove_dead prog q))
Proof
  MAP_EVERY qid_spec_tac [‘q’, ‘prog’]>>
  recInduct word_allocTheory.remove_dead_ind>>
  rw[word_allocTheory.remove_dead_def,
     no_share_inst_def]>>gs[]>>
  rw[word_allocTheory.remove_dead_def,
     no_share_inst_def]>>gs[]>>
  rpt (pairarg_tac>>gs[])>>rveq>>
  rw[no_share_inst_def]>>gs[]>>
  every_case_tac>>rpt (pairarg_tac>>gs[])>>rveq>>
  rw[no_share_inst_def]>>gs[]
QED

Theorem three_to_two_reg_no_share_inst:
  no_share_inst prog ⇒
  no_share_inst (three_to_two_reg prog)
Proof
  qid_spec_tac ‘prog’>>
  recInduct word_instTheory.three_to_two_reg_ind>>
  rw[word_instTheory.three_to_two_reg_def,
     no_share_inst_def]>>
  gs[]>>every_case_tac>>gs[]
QED

Theorem apply_colour_no_share_inst:
  no_share_inst prog ⇒
  no_share_inst (apply_colour f prog)
Proof
  qid_spec_tac ‘prog’>>qid_spec_tac ‘f’>>
  recInduct word_allocTheory.apply_colour_ind>>
  rw[word_allocTheory.apply_colour_def,
     no_share_inst_def]>>gs[]>>
  every_case_tac>>gs[]
QED

Theorem word_alloc_no_share_inst:
  no_share_inst prog ⇒
  no_share_inst (word_alloc n c a r prog cl)
Proof
  rw[word_allocTheory.word_alloc_def]>>
  every_case_tac>>gs[no_share_inst_def]
  >- (pairarg_tac>>gs[]>>
      every_case_tac>>gs[no_share_inst_def]>>
      irule apply_colour_no_share_inst>>rw[])>>
  gs[word_allocTheory.oracle_colour_ok_def]>>
  every_case_tac>>gs[no_share_inst_def]>>
  rveq>>irule apply_colour_no_share_inst>>rw[]
QED

Theorem word_common_subexp_elim_no_share_inst:
  no_share_inst prog ⇒
  no_share_inst (word_common_subexp_elim prog)
Proof
  fs [word_cseTheory.word_common_subexp_elim_def]
  \\ pairarg_tac \\ fs []
  \\ rename [‘_ e p = (a,np)’]
  \\ pop_assum mp_tac
  \\ MAP_EVERY qid_spec_tac [‘np’,‘e’,‘a’,‘p’]
  \\ ho_match_mp_tac word_simpTheory.simp_if_ind
  \\ rpt strip_tac \\ fs []
  \\ fs [word_cseTheory.word_cse_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ gvs [no_share_inst_def,AllCaseEqs(),word_cseTheory.add_to_data_aux_def]
  \\ res_tac \\ fs []
  \\ gvs [word_cseTheory.word_cseInst_def |> DefnBase.one_line_ify NONE,AllCaseEqs()]
  \\ gvs [no_share_inst_def,AllCaseEqs(),word_cseTheory.add_to_data_aux_def,
          word_cseTheory.add_to_data_def]
QED

Theorem SimpSeq_no_share_inst:
  no_share_inst p1 ∧ no_share_inst p2 ⇒
  no_share_inst (SimpSeq p1 p2)
Proof
  rw [SimpSeq_def,no_share_inst_def]
  \\ Cases_on ‘p1’ \\ rw [no_share_inst_def]
QED

Theorem Seq_assoc_right_lemma_no_share_inst:
  ∀p1 p2.
  no_share_inst p1 ∧ no_share_inst p2 ⇒
  no_share_inst (Seq_assoc_right p1 p2)
Proof
  HO_MATCH_MP_TAC Seq_assoc_right_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_right_def,no_share_inst_def]
  >~ [`Call`]
  >- (
    every_case_tac \\ gvs[no_share_inst_def]
    \\ match_mp_tac SimpSeq_no_share_inst
    \\ gvs[no_share_inst_def])
  \\ match_mp_tac SimpSeq_no_share_inst
  \\ gvs[no_share_inst_def]
QED

Theorem remove_unreach_no_share_inst:
  no_share_inst p ⇒
  no_share_inst (remove_unreach p)
Proof
  rw[remove_unreach_def]
  \\ irule Seq_assoc_right_lemma_no_share_inst
  \\ gvs[no_share_inst_def]
QED

Theorem compile_single_no_share_inst:
  no_share_inst prog ∧
  (q, r) = (SND (compile_single two_reg_arith reg_count alg c
                 ((name_num,arg_count,prog),col_opt))) ⇒
  no_share_inst r
Proof
  rw[word_to_wordTheory.compile_single_def]>>
  irule word_alloc_no_share_inst>>
  TRY (irule three_to_two_reg_no_share_inst)>>
  irule remove_dead_no_share_inst>>
  irule remove_unreach_no_share_inst>>
  irule word_common_subexp_elim_no_share_inst>>
  irule full_ssa_cc_trans_no_share_inst>>
  irule inst_select_no_share_inst>>
  irule compile_exp_no_share_inst>>rw[]
QED

Theorem compile_single_no_share_inst':
  no_share_inst (SND $ SND $ FST x) ==>
  no_share_inst (SND $ SND (compile_single two_reg_arith reg_count alg c x))
Proof
  rpt strip_tac >>
  irule compile_single_no_share_inst >>
  PairCases_on `x` >>
  gvs[] >>
  metis_tac[SND_EQ_EQUIV]
QED

||||||| 6eebd384c
Theorem const_fp_loop_no_share_inst:
  ∀prog p.
    no_share_inst prog ⇒
    no_share_inst (FST (const_fp_loop prog p))
Proof
  recInduct word_simpTheory.const_fp_loop_ind>>
  rw[word_simpTheory.compile_exp_def, word_simpTheory.const_fp_loop_def]>>
  TRY (every_case_tac>> gs[no_share_inst_def])>>
  TRY (pairarg_tac>>gs[no_share_inst_def])>>
  gs[no_share_inst_def]>>
  pairarg_tac>>gs[no_share_inst_def]
QED

Theorem const_fp_no_share_inst:
  r = const_fp prog ∧ no_share_inst prog ⇒
  no_share_inst r
Proof
  gs[word_simpTheory.const_fp_def, const_fp_loop_no_share_inst]
QED

Theorem SmartSeq_no_share_inst:
  no_share_inst prog ∧
  no_share_inst prog' ⇒
  no_share_inst (SmartSeq prog prog')
Proof
  rw[word_simpTheory.SmartSeq_def, no_share_inst_def]
QED

Theorem apply_if_opt_SOME_no_share_inst:
  no_share_inst prog ∧ no_share_inst prog' ∧
  apply_if_opt prog prog' = SOME x ⇒
  no_share_inst x
Proof
  strip_tac>>
  fs [word_simpTheory.apply_if_opt_def]>>
  pairarg_tac \\ fs []>>
  rpt FULL_CASE_TAC>>gs[]
  >- (every_case_tac \\ fs [])>>
  rpt (FULL_CASE_TAC>>gs[])>>
  fs [word_simpProofTheory.dest_If_Eq_Imm_thm]>>
  gs[word_simpProofTheory.dest_If_thm]>>
  fs [word_simpTheory.SmartSeq_def]>>rveq>>
  IF_CASES_TAC>>gs[no_share_inst_def]>>
  Cases_on ‘prog’>>gs[word_simpTheory.dest_Seq_def,
                      no_share_inst_def]
QED

Theorem simp_if_no_share_inst:
  no_share_inst prog ⇒ no_share_inst (simp_if prog)
Proof
  qid_spec_tac ‘prog’>> ho_match_mp_tac word_simpTheory.simp_if_ind>>
  rw[word_simpTheory.simp_if_def, no_share_inst_def]>>
  TRY (every_case_tac>> gs[no_share_inst_def])>>
  TRY (pairarg_tac>>gs[no_share_inst_def])>>
  imp_res_tac apply_if_opt_SOME_no_share_inst
QED

Theorem Seq_assoc_no_share_inst:
  no_share_inst prog ∧
  no_share_inst prog' ⇒
  no_share_inst (Seq_assoc prog prog')
Proof
  gs[GSYM AND_IMP_INTRO]>>
  qid_spec_tac ‘prog'’>>
  qid_spec_tac ‘prog’>>
  ho_match_mp_tac word_simpTheory.Seq_assoc_ind>>
  rw[no_share_inst_def]
  >~[‘_ (_ _ (Call _ _ _ _))’]
  >- (
  gs[word_simpTheory.Seq_assoc_def,
     word_simpTheory.SmartSeq_def,
     no_share_inst_def]>>
  every_case_tac>>gs[no_share_inst_def])>>
  Cases_on ‘prog’>>
  gs[word_simpTheory.Seq_assoc_def,
     word_simpTheory.SmartSeq_def,
     no_share_inst_def]
QED

Theorem compile_exp_no_share_inst:
  no_share_inst prog ⇒
  no_share_inst (compile_exp prog)
Proof
  rw[word_simpTheory.compile_exp_def]>>
  irule const_fp_no_share_inst>>gs[]>>
  qexists_tac ‘simp_if (Seq_assoc Skip prog)’>>rw[]>>
  irule simp_if_no_share_inst>>
  irule Seq_assoc_no_share_inst>>
  rw[no_share_inst_def]
QED

Theorem inst_select_exp_no_share_inst:
  no_share_inst (inst_select_exp c c' n exp)
Proof
  MAP_EVERY qid_spec_tac [‘exp’, ‘n’, ‘c'’, ‘c’]>>
  ho_match_mp_tac word_instTheory.inst_select_exp_ind>>
  rw[word_instTheory.inst_select_exp_def,
     no_share_inst_def]>>
  every_case_tac>>gs[no_share_inst_def,
                     word_instTheory.inst_select_exp_def]
QED

Theorem inst_select_no_share_inst:
  no_share_inst prog ⇒
  no_share_inst (inst_select c n prog)
Proof
  MAP_EVERY qid_spec_tac [‘prog’, ‘n’, ‘c’]>>
  ho_match_mp_tac word_instTheory.inst_select_ind>>
  rw[
      no_share_inst_def]>>
  every_case_tac>>
  gs[inst_select_exp_no_share_inst, word_instTheory.inst_select_def,
     no_share_inst_def]>>
  every_case_tac>>
  gs[inst_select_exp_no_share_inst, word_instTheory.inst_select_def,
     no_share_inst_def]
QED

Theorem ssa_cc_trans_inst_no_share_inst:
  ssa_cc_trans_inst i ssa na = (i',ssa',na') ⇒
  no_share_inst i'
Proof
  MAP_EVERY qid_spec_tac [‘i'’, ‘ssa'’, ‘na'’, ‘na’, ‘ssa’, ‘i’]>>
  recInduct word_allocTheory.ssa_cc_trans_inst_ind>>
  rw[word_allocTheory.ssa_cc_trans_inst_def,
     no_share_inst_def]>>
  rpt (pairarg_tac>>gs[])>>
  rw[word_allocTheory.ssa_cc_trans_inst_def,
     no_share_inst_def]>>
  every_case_tac>>rw[]>>rveq>>
  gs[word_allocTheory.next_var_rename_def,
     no_share_inst_def]
QED

Theorem fake_moves_no_share_inst:
  fake_moves ls nL nR n = (prog1, prog2, n' ,ssa, ssa') ⇒
  no_share_inst prog1 ∧ no_share_inst prog2
Proof
  MAP_EVERY qid_spec_tac [‘ssa'’, ‘ssa’, ‘n'’, ‘prog2’, ‘prog1’, ‘n’, ‘nR’, ‘NL’, ‘ls’]>>
  Induct_on ‘ls’>>
  gs[word_allocTheory.fake_moves_def,
     no_share_inst_def]>>rw[]>>
  pairarg_tac>>gs[]>>FULL_CASE_TAC>>gs[]>>
  every_case_tac>>
  rveq>>gs[no_share_inst_def]>>
  rveq>>gs[no_share_inst_def,
           word_allocTheory.fake_move_def]>>metis_tac[]
QED

Theorem ssa_cc_trans_no_share_inst:
  no_share_inst prog ∧
  ssa_cc_trans prog ssa n = (prog', ssa', na)⇒
  no_share_inst prog'
Proof
  MAP_EVERY qid_spec_tac [‘prog'’, ‘ssa'’, ‘na’, ‘n’, ‘ssa’, ‘prog’]>>
  recInduct word_allocTheory.ssa_cc_trans_ind>>
  rw[word_allocTheory.ssa_cc_trans_def,
     word_allocTheory.fix_inconsistencies_def,
     word_allocTheory.list_next_var_rename_move_def,
     no_share_inst_def]>>gs[]>>
  rpt (pairarg_tac>>gs[])>>rveq>>
  gs[word_allocTheory.ssa_cc_trans_def,
     word_allocTheory.fix_inconsistencies_def,
     word_allocTheory.list_next_var_rename_move_def,
     no_share_inst_def]
  >- (drule ssa_cc_trans_inst_no_share_inst>>rw[])
  >- (drule fake_moves_no_share_inst>>rw[])
  >- (EVERY_CASE_TAC>>gs[]>>rveq>>gs[no_share_inst_def]>>
    rpt (pairarg_tac>>gs[])>>rveq>>gs[no_share_inst_def]>>
    drule fake_moves_no_share_inst>>rw[])
QED

Theorem setup_ssa_no_share_inst:
  no_share_inst prog ∧
  setup_ssa n v prog = (mov, ssa, na)⇒
  no_share_inst mov
Proof
  rw[word_allocTheory.setup_ssa_def]>>
  pairarg_tac>>gs[]>>
  rw[word_allocTheory.setup_ssa_def,
     word_allocTheory.list_next_var_rename_move_def,
     no_share_inst_def]
QED

Theorem full_ssa_cc_trans_no_share_inst:
  no_share_inst prog ⇒
  no_share_inst (full_ssa_cc_trans n prog)
Proof
  rw[word_allocTheory.full_ssa_cc_trans_def]>>
  pairarg_tac>>gs[]>>
  pairarg_tac>>
  drule_all setup_ssa_no_share_inst>>
  rw[no_share_inst_def]>>
  drule_all ssa_cc_trans_no_share_inst>>
  rw[no_share_inst_def]
QED

Theorem remove_dead_no_share_inst:
  no_share_inst prog ⇒
  no_share_inst (FST (remove_dead prog q))
Proof
  MAP_EVERY qid_spec_tac [‘q’, ‘prog’]>>
  recInduct word_allocTheory.remove_dead_ind>>
  rw[word_allocTheory.remove_dead_def,
     no_share_inst_def]>>gs[]>>
  rw[word_allocTheory.remove_dead_def,
     no_share_inst_def]>>gs[]>>
  rpt (pairarg_tac>>gs[])>>rveq>>
  rw[no_share_inst_def]>>gs[]>>
  every_case_tac>>rpt (pairarg_tac>>gs[])>>rveq>>
  rw[no_share_inst_def]>>gs[]
QED

Theorem three_to_two_reg_no_share_inst:
  no_share_inst prog ⇒
  no_share_inst (three_to_two_reg prog)
Proof
  qid_spec_tac ‘prog’>>
  recInduct word_instTheory.three_to_two_reg_ind>>
  rw[word_instTheory.three_to_two_reg_def,
     no_share_inst_def]>>
  gs[]>>every_case_tac>>gs[]
QED

Theorem apply_colour_no_share_inst:
  no_share_inst prog ⇒
  no_share_inst (apply_colour f prog)
Proof
  qid_spec_tac ‘prog’>>qid_spec_tac ‘f’>>
  recInduct word_allocTheory.apply_colour_ind>>
  rw[word_allocTheory.apply_colour_def,
     no_share_inst_def]>>gs[]>>
  every_case_tac>>gs[]
QED

Theorem word_alloc_no_share_inst:
  no_share_inst prog ⇒
  no_share_inst (word_alloc n c a r prog cl)
Proof
  rw[word_allocTheory.word_alloc_def]>>
  every_case_tac>>gs[no_share_inst_def]
  >- (pairarg_tac>>gs[]>>
      every_case_tac>>gs[no_share_inst_def]>>
      irule apply_colour_no_share_inst>>rw[])>>
  gs[word_allocTheory.oracle_colour_ok_def]>>
  every_case_tac>>gs[no_share_inst_def]>>
  rveq>>irule apply_colour_no_share_inst>>rw[]
QED

Theorem word_common_subexp_elim_no_share_inst:
  no_share_inst prog ⇒
  no_share_inst (word_common_subexp_elim prog)
Proof
  fs [word_cseTheory.word_common_subexp_elim_def]
  \\ pairarg_tac \\ fs []
  \\ rename [‘_ e p = (a,np)’]
  \\ pop_assum mp_tac
  \\ MAP_EVERY qid_spec_tac [‘np’,‘e’,‘a’,‘p’]
  \\ ho_match_mp_tac word_simpTheory.simp_if_ind
  \\ rpt strip_tac \\ fs []
  \\ fs [word_cseTheory.word_cse_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ gvs [no_share_inst_def,AllCaseEqs(),word_cseTheory.add_to_data_aux_def]
  \\ res_tac \\ fs []
  \\ gvs [word_cseTheory.word_cseInst_def |> DefnBase.one_line_ify NONE,AllCaseEqs()]
  \\ gvs [no_share_inst_def,AllCaseEqs(),word_cseTheory.add_to_data_aux_def,
          word_cseTheory.add_to_data_def]
QED

Theorem compile_single_no_share_inst:
  no_share_inst prog ∧
  (q, r) = (SND (compile_single two_reg_arith reg_count alg c
                 ((name_num,arg_count,prog),col_opt))) ⇒
  no_share_inst r
Proof
  rw[word_to_wordTheory.compile_single_def]>>
  irule word_alloc_no_share_inst>>
  TRY (irule three_to_two_reg_no_share_inst)>>
  irule remove_dead_no_share_inst>>
  irule word_common_subexp_elim_no_share_inst>>
  irule full_ssa_cc_trans_no_share_inst>>
  irule inst_select_no_share_inst>>
  irule compile_exp_no_share_inst>>rw[]
QED

Theorem compile_single_no_share_inst':
  no_share_inst (SND $ SND $ FST x) ==>
  no_share_inst (SND $ SND (compile_single two_reg_arith reg_count alg c x))
Proof
  rpt strip_tac >>
  irule compile_single_no_share_inst >>
  PairCases_on `x` >>
  gvs[] >>
  metis_tac[SND_EQ_EQUIV]
QED

=======
>>>>>>> origin/master
Theorem code_rel_no_share_inst:
  find_code op args c1 sz = SOME v ∧
  code_rel c1 c2 ∧
  no_share_inst (FST (SND v)) ∧
  find_code op args c2 sz = SOME v' ⇒
  no_share_inst (FST (SND v'))
Proof
  simp [no_share_inst_subprogs_def]
  \\ metis_tac [code_rel_not_created]
QED

Theorem remove_must_terminate_no_share_inst:
  !prog. no_share_inst (remove_must_terminate prog) = no_share_inst prog
Proof
  ho_match_mp_tac word_removeTheory.remove_must_terminate_ind >>
  rw[word_removeTheory.remove_must_terminate_def,
    no_share_inst_def] >>
  rpt (TOP_CASE_TAC >>
    gvs[word_removeTheory.remove_must_terminate_def,
      no_share_inst_def]) >>
  gvs[word_removeTheory.remove_must_terminate_def,
    no_share_inst_def,AllCaseEqs()]
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
  \\ simp[remove_must_terminate_no_share_inst]
  \\ fs [no_share_inst_subprogs_def]
  \\ simp [compile_single_not_created]
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
        irule compile_single_not_created >> res_tac >> gs [])>>
  drule no_install_no_alloc_compile_single_correct>>
  fs[]>>
  disch_then(qspec_then`prog`mp_tac)>>
  rpt (disch_then drule)>>
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
  drule code_rel_ext_word_to_word>>
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
    drule (GEN_ALL panLang_compile_word_to_word_thm)>>
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
    drule (GEN_ALL panLang_compile_word_to_word_thm)>>
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
    drule (GEN_ALL wordPropsTheory.evaluate_add_clock) >>
    simp[RIGHT_FORALL_IMP_THM] >>
    impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
    disch_then(qspec_then`k`mp_tac) >>
    strip_tac>>
    qpat_x_assum ‘_ = (r', t')’ assume_tac>>
    drule (GEN_ALL wordPropsTheory.evaluate_add_clock) >>
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
  drule (GEN_ALL panLang_compile_word_to_word_thm)>>
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
    drule (GEN_ALL panLang_compile_word_to_word_thm)>>
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
    drule (GEN_ALL panLang_compile_word_to_word_thm)>>
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

  drule (GEN_ALL panLang_compile_word_to_word_thm)>>
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

val _ = export_theory();
