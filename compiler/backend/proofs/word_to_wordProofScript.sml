open preamble BasicProvers word_to_wordTheory wordSemTheory
     wordPropsTheory word_allocProofTheory word_instProofTheory;

val good_dimindex_def = labPropsTheory.good_dimindex_def;

val _ = new_theory "word_to_wordProof";

val is_phy_var_tac =
    fs[reg_allocTheory.is_phy_var_def]>>
    `0<2:num` by DECIDE_TAC>>
    `∀k.(2:num)*k=k*2` by DECIDE_TAC>>
    metis_tac[arithmeticTheory.MOD_EQ_0];

(* TODO: I think all the correctness theorems in wordLang
  have to be strengthened to guarantee that on an exception
  with respect to the same stack, the final locals are equal
  -- In particular, this is a consequence of the fact
  that Alloc/the gc is called the same number of times
  (so that the values on the stack do not change differently)
  -- Note: evaluate_stack_swap unfortunately only gets half
  the way there by guaranteeing that the variable names
  present are equal but not their values
val lem = prove(``
  ∀alg prog k col_opt st.
  even_starting_locals st.locals
  ⇒
  ∃perm'.
  let (res,rst) = evaluate(prog,st with permute:=perm') in
  if (res = SOME Error) then T else
  let (res',rcst) = evaluate(word_alloc alg k prog col_opt,st) in
    res = res' ∧
    word_state_eq_rel rst rcst ∧
    case res of
      SOME (Exception x y) => rst.locals = rcst.locals
    | _ => T``,cheat)
*)

(*Chains up compile_single theorems*)
val compile_single_lem = prove(``
  ∀prog n k st.
  domain st.locals = set(even_list n)
  ⇒
  ∃perm'.
  let (res,rst) = evaluate(prog,st with permute:=perm') in
  let (_,_,cprog) = (compile_single t k a c ((name,n,prog),col)) in
  if (res = SOME Error) then T else
  let (res',rcst) = evaluate(cprog,st) in
    res = res' ∧
    word_state_eq_rel rst rcst``,
    (*∧
    case res of
      SOME (Exception x y) => rst.locals = rcst.locals
    | _ => T*)
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
    fs[word_state_eq_rel_def])
  >>
    split_pair_tac>>fs[]>>
    split_pair_tac>>fs[word_state_eq_rel_def]>>
    metis_tac[])

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
    fs[evaluate_def,LET_THM]>>
    qexists_tac`st.permute`>>fs[alloc_def,get_var_def,gc_def,LET_THM,push_env_def,set_store_def,env_to_list_def,pop_env_def,has_space_def,call_env_def,set_var_def,get_var_def,dec_clock_def,jump_exc_def,get_vars_perm,get_vars_code_frame,set_vars_def,word_exp_perm,word_exp_code_frame,mem_store_def]>>
    every_case_tac>>fs[state_component_equality]

val rm_perm = prove(``
  s with permute:= s.permute = s``,fs[state_component_equality])

val size_tac= (fs[wordLangTheory.prog_size_def]>>DECIDE_TAC);

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
          case res of
            SOME (Result x y) => ∃loc. rst1 = rst with <|code:=l;locals:=loc|>
          | _ => rst1 = rst with code:=l``,
  (*recInduct doesn't seem to give a nice induction thm*)
  completeInduct_on`(prog_size (K 0) (prog:'a wordLang$prog) + 1)
                    * ((st:('a,'b)state).clock +1)`>>
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
    (*TODO: Split into tail call and non-tail calls, tryout the complete
    induction, possibly assuming the stronger form of
    compile_single_lem*)
    cheat)
  >- (*Seq, inductive*)
    (fs[evaluate_def,LET_THM,AND_IMP_INTRO]>>
    last_assum(qspecl_then[`p`,`st`,`l`] mp_tac)>>
    discharge_hyps>-size_tac>> rw[]>>
    split_pair_tac>>fs[]
    >- (qexists_tac`perm'`>>rw[]) >>
    split_pair_tac>>fs[]>>
    reverse (Cases_on`res`)>>fs[]
    >- (qexists_tac`perm'`>>fs[])>>
    first_assum(qspecl_then[`p0`,`rst`,`l`] mp_tac)>>
    discharge_hyps>-
      (*Now need clock monotonicity*)
      (fs[]>>
      cheat)>>
    rw[]>>
    qspecl_then[`p`,`st with permute:=perm'`,`perm''`]
      assume_tac permute_swap_lemma>>
    rfs[LET_THM]>>
    qexists_tac`perm'''`>>rw[]>>fs[])
  >- cheat
  >- cheat
  >- tac
  >- tac
  >- tac
  >- (tac>>
     Cases_on`call_FFI st.ffi n x'`>>simp[]))

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
