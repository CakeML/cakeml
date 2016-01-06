open preamble BasicProvers word_to_wordTheory wordSemTheory
     wordPropsTheory word_allocProofTheory word_instProofTheory;

val good_dimindex_def = labPropsTheory.good_dimindex_def;

val _ = new_theory "word_to_wordProof";

(*TODO: Quantification over t k a c col -- should not affect correctness*)
(*Should be simple to write one for all non-recursive cases*)
val get_vars_code_frame = prove(``
  ∀ls.
  get_vars ls (st with code:=l) =
  get_vars ls st``,
  Induct>>fs[get_vars_def,get_var_def])

(*Move to wordProps so there's no scoping problems..*)
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
         lookup n l = SOME (SND (compile_single t k a c ((n,v),col)))) ==>
  ∃perm'.
    let (res,rst) = evaluate (prog,st with permute := perm') in
      if res = SOME Error then T
      else
        let (res1,rst1) = evaluate (prog,st with code := l) in
          res1 = res ∧
          rst.code = st.code ∧
          rst1 = rst with code := l``,
  (*recInduct doesn't seem to give a nice induction thm*)
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
    cheat
  >- (*Seq, inductive*)
    (fs[evaluate_def,LET_THM,AND_IMP_INTRO]>>
    last_assum(qspecl_then[`p`,`st`,`l`] mp_tac)>>
    discharge_hyps>- size_tac>> rw[]>>
    split_pair_tac>>fs[]
    >- (qexists_tac`perm'`>>rw[]) >>
    split_pair_tac>>fs[]>>
    reverse (Cases_on`res`)>>fs[]
    >- (qexists_tac`perm'`>>fs[])>>
    first_assum(qspecl_then[`p0`,`rst`,`l`] mp_tac)>>
    discharge_hyps>- size_tac>>
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
           lookup n l = SOME (SND (compile_single t k a c ((n,v),col)))) ==>
    ?perm'.
      let prog = Call NONE (SOME start) [0] NONE in
      let (res,rst) = evaluate (prog,st with permute := perm') in
        if res = SOME Error then T else
          let (res1,rst1) = evaluate (prog,st with code := l) in
            res1 = res /\ rst1.clock = rst.clock /\ rst1.ffi = rst.ffi``,
  cheat) (* can this be proved? *)
  |> SIMP_RULE std_ss [Once LET_THM]

val _ = export_theory();
