(*
  Correctness proof for data_to_word
*)
Theory data_to_wordProof
Ancestors
  backend[qualified] dataLang[qualified] dataSem
  data_to_word_gcProof word_to_wordProof wordProps data_to_word
  wordLang wordSem[qualified] dataProps copying_gc int_bitwise
  finite_map data_to_word_memoryProof data_to_word_bignumProof
  data_to_word_assignProof wordConvs wordConvsProof While set_sep
  semanticsProps alignment word_bignum word_bignumProof
  gen_gc_partial gc_shared gen_gc[qualified]
Libs
  preamble helperLib blastLib match_goal

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val _ = hide "next";

val clean_tac = rpt var_eq_tac \\ rpt (qpat_x_assum `T` kall_tac)
fun rpt_drule th = old_drule (th |> GEN_ALL) \\ rpt (disch_then old_drule \\ fs [])

val state_rel_def = data_to_word_gcProofTheory.state_rel_def
val code_rel_def = data_to_word_gcProofTheory.code_rel_def

val assign_def =
  data_to_wordTheory.assign_def
  |> REWRITE_RULE [data_to_wordTheory.arg1_def,
                   data_to_wordTheory.arg2_def,
                   data_to_wordTheory.arg3_def,
                   data_to_wordTheory.arg4_def,
                   data_to_wordTheory.all_assign_defs];

Theorem state_rel_with_locals_sfs[simp]:
  state_rel c l1 l2 (x with <| locals := l; safe_for_space := m |>) r t locs
  <=>
  state_rel c l1 l2 (x with <| locals := l |>) r t locs
Proof
  fs [state_rel_def]
QED

Theorem do_space_code_const:
  do_space op vs (s:('a,'b) dataSem$state) = SOME s1 ==>
  s1.code = s.code /\ s1.compile_oracle = s.compile_oracle
Proof
  strip_tac
  \\ gvs[do_space_def,AllCaseEqs(),consume_space_def]
QED

Triviality word_test_lemma1:
  good_dimindex (:α) ⇒
  (0b111100w && x = n2w ((8 + 6) * 4):'a word ⇔
   ~ word_bit 2 x ∧ word_bit 3 x ∧ word_bit 4 x ∧ word_bit 5 x)
Proof
  simp [word_eq,word_bit_and,word_bit_n2w,good_dimindex_def]
  \\ rw [] \\ gvs [] \\ rw []
  \\ simp [METIS_PROVE [] “(∀n. (P n = Q n)) ⇔ (∀n. P n ⇒ Q n) ∧ (∀n. Q n ⇒ P n)”]
  \\ gvs [SF DNF_ss,SF CONJ_ss]
QED

Triviality word_test_lemma2:
  good_dimindex (:α) ⇒
  (0b111100w && x = n2w ((0 + 6) * 4):'a word ⇔
   ~ word_bit 2 x ∧ word_bit 3 x ∧ word_bit 4 x ∧ ~ word_bit 5 x)
Proof
  simp [word_eq,word_bit_and,word_bit_n2w,good_dimindex_def]
  \\ rw [] \\ gvs [] \\ rw []
  \\ simp [METIS_PROVE [] “(∀n. (P n = Q n)) ⇔ (∀n. P n ⇒ Q n) ∧ (∀n. Q n ⇒ P n)”]
  \\ gvs [SF DNF_ss,SF CONJ_ss]
  \\ eq_tac \\ rw [] \\ gvs []
  \\ first_assum $ qspec_then ‘2’ assume_tac
  \\ first_assum $ qspec_then ‘3’ assume_tac
  \\ first_assum $ qspec_then ‘4’ assume_tac
  \\ first_assum $ qspec_then ‘5’ assume_tac
  \\ fs []
QED

Theorem memory_rel_Thunk_bits:
  memory_rel c be ts refs sp st m dm ((RefPtr bl p,Word (w:'a word))::vars) ∧
  lookup p refs = SOME (Thunk ev z) ∧ good_dimindex (:α) ∧
  get_real_addr c st w = SOME a ∧
  m a = Word x
  ⇒
  (case ev of
   | Evaluated => 0b111100w && x = n2w ((8 + 6) * 4)
   | NotEvaluated => 0b111100w && x = n2w ((0 + 6) * 4))
Proof
  strip_tac
  \\ drule_all memory_rel_Thunk_IMP \\ fs []
  \\ strip_tac
  \\ drule word_test_lemma1 \\ fs []
  \\ drule word_test_lemma2 \\ fs []
  \\ Cases_on ‘ev’ \\ gs []
QED

Theorem memory_rel_Force:
   memory_rel c be ts refs sp st m dm ((RefPtr bl nn,ptr)::vars) /\
    lookup nn refs = SOME (Thunk ev v) /\
    good_dimindex (:'a) ==>
    ?ptr_w x:'a word w w'.
      ptr = Word ptr_w /\
      get_real_addr c st ptr_w = SOME x /\
      x IN dm /\ m x = Word w /\
      (x + bytes_in_word) IN dm /\
      memory_rel c be ts refs sp st m dm
        ((v,m (x + bytes_in_word))::(RefPtr bl nn,ptr)::vars)
Proof
  rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ fs [memory_rel_def,PULL_EXISTS] \\ rw []
  \\ asm_exists_tac \\ fs []
  \\ fs [word_ml_inv_def,PULL_EXISTS] \\ clean_tac
  \\ rpt_drule (GEN_ALL deref_thm) \\ fs [domain_lookup] \\ strip_tac
  \\ asm_exists_tac \\ fs []
  \\ Cases_on `v'` \\ fs [heap_el_def]
  \\ every_case_tac \\ fs [] \\ clean_tac
  \\ fs [GSYM CONJ_ASSOC,word_addr_def]
  \\ fs [heap_in_memory_store_def]
  \\ rpt_drule get_real_addr_get_addr \\ fs []
  \\ disch_then kall_tac
  \\ drule LESS_LENGTH
  \\ strip_tac \\ fs [] \\ clean_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [EL_LENGTH_APPEND]
  \\ imp_res_tac heap_lookup_SPLIT
  \\ PairCases_on `b` \\ fs []
  \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def]
  \\ pairarg_tac \\ gvs []
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR] \\ gvs []
  \\ Cases_on `b0` \\ fs [word_payload_def]
  \\ gvs [word_list_def,word_list_APPEND,SEP_CLAUSES] \\ fs [SEP_F_def]
  \\ SEP_R_TAC \\ fs []
QED

Theorem MEM_join_env_cut_env:
  ∀(a:v # α word_loc) t r s.
    MEM a (join_env x (toAList (inter t (adjust_set x)))) ∧
    dataSem$cut_env r s = SOME x ⇒
    MEM a (join_env s (toAList (inter t (adjust_set s))))
Proof
  fs [join_env_def,MEM_MAP,EXISTS_PROD,MEM_FILTER]
  \\ rw [] \\ gvs [cut_env_def]
  \\ fs [MEM_toAList]
  \\ last_assum $ irule_at Any \\ simp []
  \\ fs [lookup_inter_alt,IN_domain_adjust_set_inter]
  \\ rw [] \\ fs []
  \\ imp_res_tac IN_adjust_set_IN
QED

Theorem jump_exc_locals:
  wordSem$jump_exc (t with locals := l) = jump_exc t
Proof
  fs [wordSemTheory.jump_exc_def]
QED

Theorem state_rel_cut_env_IMP_cut_env =
  state_rel_cut_state_opt_SOME |> Q.GEN ‘args’ |> Q.SPEC ‘[]’ |> GEN_ALL
  |> SRULE [get_vars_def,cut_state_opt_def,cut_state_def,
            CaseEq"option",PULL_EXISTS,wordSemTheory.get_vars_def];

Theorem data_compile_correct:
   !prog s c n l l1 l2 res s1 (t:('a,'c,'ffi)wordSem$state) locs.
      (dataSem$evaluate (prog,s) = (res,s1)) /\
      res <> SOME (Rerr (Rabort Rtype_error)) /\
      state_rel c l1 l2 s t [] locs /\
      t.termdep > 1
      ==>
      ?t1 res1.
        (wordSem$evaluate (FST (comp c n l prog),t) = (res1,t1)) /\
         option_le t1.stack_max s1.stack_max /\
        (res1 = SOME NotEnoughSpace ==>
           t1.ffi.io_events ≼ s1.ffi.io_events /\
           (c.gc_kind <> None ==> ~s1.safe_for_space)) /\
        (res1 <> SOME NotEnoughSpace ==>
         case res of
         | NONE => state_rel c l1 l2 s1 t1 [] locs /\ (res1 = NONE)
         | SOME (Rval v) =>
             ?w. state_rel c l1 l2 s1 t1 [(v,w)] locs /\
                 (res1 = SOME (Result (Loc l1 l2) [w]))
         | SOME (Rerr (Rraise v)) => (t1.ffi = s1.ffi) /\
             ?w l5 l6 ll.
               (res1 = SOME (Exception (mk_loc (jump_exc t)) w)) /\
               (jump_exc t <> NONE ==>
                LASTN (LENGTH s1.stack + 1) locs = (l5,l6)::ll /\
                !i. state_rel c l5 l6 (set_var i v s1)
                       (set_var (adjust_var i) w t1) [] ll)
         | SOME (Rerr (Rabort(Rffi_error f))) => (res1 = SOME(FinalFFI f) /\ t1.ffi = s1.ffi)
         | SOME (Rerr (Rabort e)) => (res1 = SOME TimeOut) /\ t1.ffi = s1.ffi)
Proof
  recInduct dataSemTheory.evaluate_ind \\ rpt strip_tac \\ fs []
  >~ [‘evaluate (Skip,s)’] >-
   (fs [comp_def,dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ srw_tac[][] \\ fs [state_rel_def])
  >~ [‘evaluate (Move dest src,s)’] >-
   (fs [comp_def,dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_var src s.locals` \\ fs [] \\ srw_tac[][]
    \\ fs [] \\ imp_res_tac state_rel_get_var_IMP \\ fs []
    \\ fs [wordSemTheory.get_vars_def,wordSemTheory.set_vars_def,alist_insert_def]
    \\ fs [state_rel_def,set_var_def,lookup_insert]
    \\ rpt strip_tac \\ fs []
    THEN1 (srw_tac[][] \\ Cases_on `n = dest` \\ fs [])
    \\ asm_exists_tac
    \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
    \\ imp_res_tac word_ml_inv_get_var_IMP
    \\ match_mp_tac word_ml_inv_insert \\ fs [])
  >~ [‘evaluate (Assign _ _ _ _,s)’] >-
   (full_simp_tac std_ss []
    \\ fs [comp_def,dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ imp_res_tac (METIS_PROVE [] ``(if b1 /\ b2 then x1 else x2) = y ==>
                                     b1 /\ b2 /\ x1 = y \/
                                     (b1 ==> ~b2) /\ x2 = y``)
    \\ fs [] \\ srw_tac[][]
    \\ Cases_on `cut_state_opt names_opt s` \\ fs []
    \\ Cases_on `get_vars args x.locals` \\ fs []
    \\ reverse (Cases_on `do_app op x' x`) \\ fs []
    THEN1 (imp_res_tac do_app_Rerr \\ rveq \\ fs []
           \\ drule_all_then assume_tac assign_FFI_final
           \\ first_x_assum(qspecl_then [`n`,`l`,`dest`] strip_assume_tac)
           \\ asm_exists_tac >> fs[] >> rpt strip_tac \\ fs[]
           \\ imp_res_tac cut_state_opt_const \\ fs[state_rel_def,flush_state_def]
           \\ fs [cut_state_opt_def,CaseEq"option",cut_state_def] \\ rveq \\ fs [])
    \\ Cases_on `a`
    \\ drule assign_thm \\ fs []
    \\ rpt (disch_then old_drule)
    \\ disch_then (qspecl_then [`n`,`l`,`dest`] strip_assume_tac)
    \\ `option_le r'.stack_max r.stack_max` by
        (Cases_on `q' = SOME NotEnoughSpace` \\ fs [state_rel_def,set_var_def])
    \\ fs [] \\ srw_tac[][] \\ fs []
    \\ imp_res_tac do_app_io_events_mono \\ rfs []
    \\ `s.ffi = t.ffi` by fs [state_rel_def] \\ fs []
    \\ sg `x.ffi = s.ffi`
    \\ imp_res_tac do_app_io_events_mono \\ rfs []
    \\ Cases_on `names_opt` \\ fs [cut_state_opt_def] \\ srw_tac[][] \\ fs []
    \\ fs [cut_state_def,cut_env_def] \\ every_case_tac
    \\ fs [] \\ rw [] \\ fs [set_var_def])
  >~ [‘evaluate (Force _ _ _,s)’] >-
   (simp [comp_def, force_thunk_def]
    \\ TOP_CASE_TAC \\ gvs []
    >- gvs [encode_header_def, encode_header_def, state_rel_def,
            good_dimindex_def, limits_inv_def, dimword_def, memory_rel_def,
            heap_in_memory_store_def, consume_space_def, arch_size_def,
            NOT_LESS]
    \\ simp [wordSemTheory.evaluate_def]
    \\ gvs [evaluate_def]
    \\ Cases_on `get_var src s.locals` \\ gvs []
    \\ Cases_on `dest_thunk x' s.refs` \\ gvs []
    \\ gvs [oneline dest_thunk_def]
    \\ Cases_on `x'` \\ gvs []
    \\ Cases_on `lookup n' s.refs` \\ gvs []
    \\ Cases_on `x'` \\ gvs []
    \\ `IsThunk t' v = IsThunk t'' a` by (Cases_on `t''` \\ gvs []) \\ gvs []
    \\ qpat_x_assum `_ = IsThunk t' a` kall_tac
    \\ drule_all state_rel_get_var_RefPtr \\ rw [] \\ gvs []
    \\ simp [wordSemTheory.get_var_imm_def, word_cmp_Test_1, word_bit_def,
             get_addr_0]
    \\ simp [Once list_Seq_def, wordSemTheory.evaluate_def]
    \\ qpat_assum `state_rel _ _ _ _ _ _ _` mp_tac
    \\ pure_rewrite_tac [Once state_rel_thm] \\ rw []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ drule_all memory_rel_get_var_IMP \\ rw [] \\ gvs []
    \\ drule_all memory_rel_Force \\ rw [] \\ gvs []
    \\ `word_exp t (real_addr c (adjust_var src)) = SOME (Word x')`
      by metis_tac [get_real_addr_lemma] \\ gvs []
    \\ simp [Once list_Seq_def, wordSemTheory.evaluate_def]
    \\ simp [wordSemTheory.set_var_def, wordSemTheory.word_exp_def,
             wordSemTheory.get_var_def, wordSemTheory.the_words_def,
             wordSemTheory.mem_load_def, word_op_def]
    \\ simp [list_Seq_def, wordSemTheory.evaluate_def]
    \\ simp [wordSemTheory.get_var_def, wordSemTheory.get_var_imm_def]
    \\ drule_all memory_rel_Thunk_bits \\ strip_tac
    \\ rename [‘_ = SOME (Thunk has_been_eval a)’]
    \\ Cases_on `has_been_eval` \\ gvs []
    >- (
      simp [asmTheory.word_cmp_def]
      \\ Cases_on `ret` \\ gvs []
      >- (
        simp [wordSemTheory.evaluate_def]
        \\ simp [wordSemTheory.word_exp_def, wordSemTheory.get_var_def,
                 lookup_insert, wordSemTheory.the_words_def,
                 word_op_def, wordSemTheory.mem_load_def,
                 wordSemTheory.set_var_def, wordSemTheory.get_vars_def]
        \\ simp [flush_state_def, wordSemTheory.flush_state_def]
        \\ fs [state_rel_thm] \\ simp [join_env_def]
        \\ conj_tac
        >-
         (irule backendPropsTheory.option_le_trans
          \\ first_x_assum $ irule_at Any
          \\ Cases_on ‘s.locals_size’ \\ fs []
          \\ Cases_on ‘stack_size t.stack’ \\ fs [])
        \\ qpat_x_assum ‘_ t.mdomain _’ mp_tac
        \\ match_mp_tac memory_rel_rearrange
        \\ simp [SF DNF_ss])
      \\ Cases_on `x''` \\ gvs []
      \\ simp [wordSemTheory.evaluate_def, wordSemTheory.word_exp_def,
               wordSemTheory.get_var_def, lookup_insert,
               wordSemTheory.the_words_def, word_op_def,
               wordSemTheory.mem_load_def]
      \\ Cases_on `cut_env r s.locals` \\ gvs []
      \\ conj_tac >- (simp [set_var_def])
      \\ simp [wordSemTheory.set_var_def, set_var_def]
      \\ fs [state_rel_thm,lookup_insert,adjust_var_11]
      \\ conj_tac >- (rw [] \\ gvs [cut_env_def,lookup_inter_alt]
                      \\ pop_assum mp_tac \\ rw [] \\ fs [])
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert
      \\ fs[inter_insert_ODD_adjust_set_alt]
      \\ qpat_x_assum ‘_ t.mdomain _’ mp_tac
      \\ match_mp_tac memory_rel_rearrange
      \\ simp [SF DNF_ss]
      \\ rpt strip_tac
      \\ drule_all MEM_join_env_cut_env \\ fs [])
    \\ IF_CASES_TAC \\ gvs []
    >- gvs [asmTheory.word_cmp_def, dimword_def, good_dimindex_def]
    \\ IF_CASES_TAC \\ gvs []
    >- gvs [asmTheory.word_cmp_def, dimword_def, good_dimindex_def]
    \\ simp [wordSemTheory.word_exp_def, wordSemTheory.get_var_def,
             lookup_insert, wordSemTheory.the_words_def, word_op_def,
             wordSemTheory.mem_load_def, wordSemTheory.set_var_def]
    \\ Cases_on `find_code (SOME loc) [RefPtr b n'; a] s.code
                           s.stack_frame_sizes` \\ gvs []
    \\ Cases_on `x''` \\ gvs []
    \\ Cases_on `r` \\ gvs []
    \\ Cases_on `ret` \\ gvs []
    >- (
      simp [wordSemTheory.evaluate_def, wordSemTheory.get_vars_def,
            wordSemTheory.get_var_def, lookup_insert]
      \\ once_rewrite_tac [GSYM wordSemTheory.get_var_def] \\ gvs []
      \\ simp [wordSemTheory.bad_dest_args_def]
      \\ gvs [find_code_def]
      \\ Cases_on `lookup loc s.code` \\ gvs []
      \\ Cases_on `x''` \\ gvs []
      \\ simp [wordSemTheory.find_code_def]
      \\ qpat_x_assum `code_rel _ _ _` assume_tac
      \\ gvs [code_rel_def]
      \\ first_x_assum drule \\ strip_tac \\ gvs []
      \\ simp [wordSemTheory.add_ret_loc_def]
      \\ IF_CASES_TAC \\ gvs []
      >- simp [wordSemTheory.flush_state_def]
      \\ gvs [CaseEq"prod",CaseEq"option",PULL_EXISTS]
      \\ qmatch_goalsub_abbrev_tac ‘(FST _, t8)’
      \\ last_x_assum $ qspecl_then [‘c’,‘loc’,‘2’,‘l1’,‘l2’,‘t8’,‘locs’] mp_tac
      \\ impl_tac >-
       (fs [state_rel_thm,dataSemTheory.call_env_def,
            dataSemTheory.dec_clock_def,wordSemTheory.dec_clock_def,
            wordSemTheory.call_env_def,dec_clock_def,Abbr‘t8’]
        \\ conj_tac >- EVAL_TAC
        \\ conj_tac >-
         (simp [fromList_def,fromList2_def]
          \\ simp [lookup_insert]
          \\ rw [] \\ gvs [])
        \\ conj_tac >-
         (Cases_on ‘t.stack_max’ \\ gvs []
          \\ Cases_on ‘stack_size t.stack’ \\ gvs []
          \\ Cases_on ‘lookup loc s.stack_frame_sizes’ \\ gvs [] )
        \\ conj_tac >-
         (imp_res_tac stack_rel_IMP_size_of_stack
          \\ Cases_on ‘size_of_stack s.stack’ \\ gvs []
          \\ Cases_on ‘lookup loc s.stack_frame_sizes’ \\ gvs []
          \\ Cases_on ‘s.stack_max’ \\ gvs []
          \\ Cases_on ‘t.stack_max’ \\ gvs [])
        \\ qpat_x_assum ‘_ t.mdomain _’ mp_tac
        \\ match_mp_tac memory_rel_rearrange
        \\ simp [SF DNF_ss]
        \\ EVAL_TAC
        \\ simp [SF DNF_ss])
      \\ strip_tac \\ fs []
      \\ Cases_on ‘res1’ \\ gvs []
      \\ strip_tac \\ gvs []
      \\ CASE_TAC \\ gvs []
      \\ CASE_TAC \\ gvs []
      \\ ‘(jump_exc t8 = NONE ⇔ jump_exc t = NONE) ∧
          mk_loc (jump_exc t8) = mk_loc (jump_exc t) : 'a word_loc’ by
       (gvs [wordSemTheory.jump_exc_def,Abbr‘t8’,wordSemTheory.call_env_def,
             wordSemTheory.dec_clock_def,mk_loc_def]
        \\ IF_CASES_TAC \\ simp []
        \\ rpt (CASE_TAC \\ gvs [mk_loc_def]))
      \\ gvs []
      \\ Cases_on ‘jump_exc t’ \\ gvs [wordSemTheory.set_var_def])
    \\ Cases_on `x''` \\ gvs []
    \\ simp [wordSemTheory.evaluate_def, wordSemTheory.get_vars_def,
             wordSemTheory.get_var_def, lookup_insert]
    \\ once_rewrite_tac [GSYM wordSemTheory.get_var_def] \\ gvs []
    \\ simp [wordSemTheory.bad_dest_args_def]
    \\ gvs [find_code_def]
    \\ Cases_on `lookup loc s.code` \\ gvs []
    \\ Cases_on `x''` \\ gvs []
    \\ simp [wordSemTheory.find_code_def]
    \\ qpat_x_assum `code_rel _ _ _` assume_tac
    \\ gvs [code_rel_def]
    \\ first_x_assum drule \\ strip_tac \\ gvs []
    \\ simp [wordSemTheory.add_ret_loc_def, domain_adjust_sets]
    \\ Cases_on `cut_env r s.locals` \\ gvs []
    \\ simp [cut_envs_adjust_sets_insert_ODD]
    \\ pop_assum mp_tac
    \\ simp [cut_env_def, SUBSET_DEF, domain_lookup] \\ strip_tac \\ gvs []
    \\ simp [adjust_sets_def, adjust_set_def, wordSemTheory.cut_envs_def,
             wordSemTheory.cut_names_def, domain_lookup, domain_fromAList]
    \\ simp [SUBSET_DEF, MEM_MAP, PULL_EXISTS]
    \\ reverse $ IF_CASES_TAC \\ gvs []
    >- (
      spose_not_then kall_tac
      \\ pairarg_tac \\ gvs [MEM_toAList, domain_lookup]
      \\ first_x_assum $ drule_then assume_tac \\ gvs []
      \\ first_x_assum $ qspec_then `n` assume_tac \\ gvs []
      \\ Cases_on `lookup (adjust_var n) t.locals` \\ gvs [])
    \\ IF_CASES_TAC \\ gvs []
    >-
     (fs [dataSemTheory.call_env_def,wordSemTheory.call_env_def]
      \\ imp_res_tac stack_rel_IMP_size_of_stack
      \\ fs [dataSemTheory.push_env_def,wordSemTheory.push_env_def,
             wordSemTheory.env_to_list_def,dataSemTheory.dec_clock_def,
             wordSemTheory.stack_size_def,
             wordSemTheory.stack_size_frame_def,
             dataSemTheory.size_of_stack_def,
             dataSemTheory.size_of_stack_frame_def]
      \\ fs [GSYM wordSemTheory.stack_size_def,
             GSYM wordSemTheory.stack_size_frame_def,
             GSYM dataSemTheory.size_of_stack_def,
             GSYM dataSemTheory.size_of_stack_frame_def]
      \\ Cases_on ‘s.stack_max’ \\ fs []
      \\ Cases_on ‘t.stack_max’ \\ fs []
      \\ Cases_on ‘s.locals_size’ \\ fs []
      \\ Cases_on ‘lookup loc s.stack_frame_sizes’ \\ fs []
      \\ Cases_on ‘size_of_stack s.stack’ \\ fs [])
    \\ gvs [CaseEq"prod",CaseEq"option",PULL_EXISTS]
    \\ qmatch_goalsub_abbrev_tac ‘(FST _, t8)’
    \\ last_x_assum $ qspecl_then [‘c’,‘loc’,‘2’,‘n’,‘l’,‘t8’,‘(l1,l2)::locs’] mp_tac
    \\ impl_tac >-
     (conj_tac >- (CCONTR_TAC \\ gvs [])
      \\ reverse conj_tac >- gvs [Abbr‘t8’]
      \\ simp [Abbr‘t8’]
      \\ irule state_rel_call_env_push \\ simp []
      \\ conj_tac >-
      (fs [cut_envs_adjust_sets_ODD]
       \\ qexists_tac ‘r’
       \\ ‘cut_env r s.locals = SOME (inter s.locals r)’ by
         simp [dataSemTheory.cut_env_def,SUBSET_DEF,domain_lookup]
       \\ drule_all state_rel_cut_env_IMP_cut_env
       \\ strip_tac \\ simp []
       \\ drule cut_env_IMP_cut_envs \\ strip_tac
       \\ gvs [wordSemTheory.cut_envs_def,CaseEq"option"]
       \\ gvs [wordSemTheory.cut_names_def,CaseEq"option"]
       \\ simp [adjust_sets_def,adjust_set_def])
      \\ fs [state_rel_thm,lookup_insert]
      \\ fs[inter_insert_ODD_adjust_set_alt]
      \\ qpat_x_assum ‘_ t.mdomain _’ mp_tac
      \\ match_mp_tac memory_rel_rearrange
      \\ simp [SF DNF_ss])
    \\ strip_tac \\ fs []
    \\ Cases_on ‘res1’
    >- (gvs [] \\ gvs [AllCaseEqs()])
    \\ gvs []
    \\ rename [‘word_res = NotEnoughSpace ⇒ _’]
    \\ Cases_on ‘word_res = NotEnoughSpace’ \\ gvs []
    >- (gvs [AllCaseEqs(),dataSemTheory.set_var_def,dataSemTheory.pop_env_def])
    \\ rename [‘dataSem$evaluate _ = (SOME data_res,s2)’]
    \\ reverse $ Cases_on ‘data_res’
    >- (
      reverse (Cases_on `e`) \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ full_simp_tac(srw_ss())[jump_exc_call_env,jump_exc_dec_clock,
                                 jump_exc_push_env_NONE,Abbr‘t8’,jump_exc_locals]
      THEN1 (every_case_tac \\ fs[])
      \\ Cases_on `jump_exc t = NONE` \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[jump_exc_push_env_NONE_simp,jump_exc_locals]
      \\ `LENGTH locs = LENGTH s.stack` by
         (fs[state_rel_def] \\ imp_res_tac LIST_REL_LENGTH \\ fs[]) \\ full_simp_tac(srw_ss())[]
      \\ `LENGTH s1.stack < LENGTH locs` by(imp_res_tac eval_exc_stack_shorter \\ fs[])
      \\ imp_res_tac LASTN_TL \\ full_simp_tac(srw_ss())[]
      \\ fs [jump_exc_push_env_NONE]
      \\ fs [wordSemTheory.set_var_def])
    \\ gvs []
    \\ Cases_on ‘pop_env s2’ \\ gvs []
    \\ qrefinel [‘_’,‘NONE’] \\ simp [AllCaseEqs(),PULL_EXISTS]
    \\ rename [‘set_var ret_var _ _’]
    \\ drule_all state_rel_pop_env_set_var_IMP
    \\ disch_then $ qspec_then ‘ret_var’ strip_assume_tac
    \\ gvs [wordSemTheory.set_vars_def,alist_insert_def,wordSemTheory.set_var_def,
            dataSemTheory.set_var_def]
    \\ reverse $ rpt strip_tac
    >- (imp_res_tac dataPropsTheory.pop_env_const
        \\ imp_res_tac wordPropsTheory.pop_env_const
        \\ gvs [])
    \\ simp [Abbr‘t8’]
    \\ drule evaluate_IMP_domain_EQ \\ fs [])
  >~ [‘evaluate (Tick,s)’] >-
   (fs [comp_def,dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ `t.clock = s.clock` by fs [state_rel_def] \\ fs [] \\ srw_tac[][]
    \\ fs [] \\ srw_tac[][] \\ rpt (pop_assum mp_tac)
    \\ fs [wordSemTheory.jump_exc_def,wordSemTheory.dec_clock_def] \\ srw_tac[][]
    \\ fs [state_rel_def,dataSemTheory.dec_clock_def,wordSemTheory.dec_clock_def]
    \\ fs [call_env_def,wordSemTheory.call_env_def,wordSemTheory.flush_state_def,flush_state_def]
    \\ asm_exists_tac \\ fs [])
  >~ [‘evaluate (MakeSpace k names,s)’] >-
   (fs [comp_def,dataSemTheory.evaluate_def,
        wordSemTheory.evaluate_def,
        GSYM alloc_size_def,LET_DEF,wordSemTheory.word_exp_def,
        wordLangTheory.word_op_def,wordSemTheory.get_var_imm_def]
    \\ `?end next hlen curr.
          FLOOKUP t.store CurrHeap = SOME (Word curr) /\
          FLOOKUP t.store HeapLength = SOME (Word hlen) /\
          FLOOKUP t.store TriggerGC = SOME (Word end) /\
          FLOOKUP t.store NextFree = SOME (Word next)` by
            fs [state_rel_def,heap_in_memory_store_def]
    \\ fs [wordSemTheory.the_words_def,wordSemTheory.get_store_def]
    \\ reverse CASE_TAC THEN1
     (every_case_tac \\ fs [] \\ srw_tac[][]
      \\ fs [wordSemTheory.set_var_def,state_rel_insert_1,add_space_def]
      THEN1 fs [state_rel_def]
      \\ match_mp_tac state_rel_cut_env \\ reverse (srw_tac[][])
      \\ fs [] \\ match_mp_tac has_space_state_rel
      \\ fs [wordSemTheory.has_space_def,WORD_LO,NOT_LESS,
             asmTheory.word_cmp_def,wordSemTheory.get_store_def])
    \\ reverse (Cases_on `c.call_empty_ffi`)
    THEN1
     (fs [SilentFFI_def,wordSemTheory.evaluate_def,list_Seq_def,CaseEq"option"]
      \\ srw_tac[][]
      \\ fs [add_space_def,wordSemTheory.word_exp_def,alloc_locals_insert_1,
           wordSemTheory.get_var_def,wordSemTheory.set_var_def]
      \\ pairarg_tac \\ gvs []
      \\ drule alloc_lemma
      \\ rpt (disch_then drule)
      \\ rw [] \\ fs [] \\ rfs [GSYM NOT_LESS,cut_locals_def]
      \\ qpat_x_assum `state_rel c l1 l2 _ _ _ _` mp_tac \\ simp [state_rel_def])
    \\ fs [SilentFFI_def,wordSemTheory.evaluate_def,list_Seq_def,eq_eval]
    \\ fs [wordSemTheory.evaluate_def,SilentFFI_def,wordSemTheory.word_exp_def,
           wordSemTheory.set_var_def,EVAL ``read_bytearray a 0 m``,
           wordSemTheory.get_store_def,
           ffiTheory.call_FFI_def,EVAL ``write_bytearray a [] m dm b``,
           wordSemTheory.get_var_def,lookup_insert,cut_names_adjust_set_insert_ODD]
    \\ Cases_on `dataSem$cut_env names s.locals` \\ gvs []
    \\ drule_all cut_env_IMP_cut_env \\ strip_tac \\ fs []
    \\ gvs [cut_env_adjust_sets_insert_ODD]
    \\ pairarg_tac \\ fs []
    \\ drule_all state_rel_cut_env_cut_env \\ strip_tac
    \\ rename [‘_ = (res1,s1)’]
    \\ ‘alloc (alloc_size k) (adjust_sets names) (t with locals := y) = (res1,s1)’ by
      (‘t with
           <|locals := insert 1 (Word (alloc_size k)) y; memory := t.memory;
             ffi := t.ffi|> =
        (t with locals := y) with locals := insert 1 (Word (alloc_size k)) (t with locals := y).locals’ by
          gvs [wordSemTheory.state_component_equality]
       \\ full_simp_tac std_ss [alloc_locals_insert_1])
    \\ `dataSem$cut_env names x = SOME x` by
      (fs [dataSemTheory.cut_env_def] \\ rveq \\ fs [lookup_inter_alt,domain_inter])
    \\ drule_then (drule_at $ Pos last) alloc_lemma
    \\ simp []
    \\ strip_tac \\ Cases_on `res1 = SOME NotEnoughSpace`
    >- (fs [] \\ rveq \\ rfs [add_space_def,cut_locals_def] \\ fs [GSYM NOT_LESS] \\ gvs [])
    \\ `?end next hlen curr.
          FLOOKUP s1.store CurrHeap = SOME (Word curr) /\
          FLOOKUP s1.store HeapLength = SOME (Word hlen) /\
          FLOOKUP s1.store TriggerGC = SOME (Word end) /\
          FLOOKUP s1.store NextFree = SOME (Word next)` by
            fs [state_rel_def,heap_in_memory_store_def]
    \\ rfs [lookup_insert,EVAL ``read_bytearray a 0 m``,
            cut_env_adjust_sets_insert_ODD]
    \\ rveq \\ rfs [add_space_def,cut_locals_def] \\ fs [GSYM NOT_LESS]
    \\ drule cut_env_IMP_cut_env \\ simp []
    \\ disch_then drule \\ strip_tac \\ gvs []
    \\ gvs [EVAL ``write_bytearray a [] m dm b``]
    \\ drule state_rel_cut_env_cut_env \\ simp []
    \\ disch_then drule \\ strip_tac \\ gvs []
    \\ gvs [state_rel_thm])
  >~ [‘evaluate (Raise _,s)’] >-
   (fs [comp_def,dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_var n s.locals` \\ fs [] \\ srw_tac[][]
    \\ fs [] \\ imp_res_tac state_rel_get_var_IMP \\ fs []
    \\ Cases_on `jump_exc s` \\ fs [] \\ srw_tac[][]
    \\ imp_res_tac state_rel_jump_exc \\ fs []
    \\ srw_tac[][] \\ fs [] \\ srw_tac[][mk_loc_def]
    \\ first_x_assum (qspec_then `0` mp_tac) \\ fs [state_rel_def]
    \\ fs [set_var_def])
  >~ [‘evaluate (Return _,s)’] >-
   (fs [comp_def,dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_var n s.locals` \\ fs [] \\ srw_tac[][]
    \\ `get_var 0 t = SOME (Loc l1 l2)` by
          fs [state_rel_def,wordSemTheory.get_var_def]
    \\ fs [] \\ imp_res_tac state_rel_get_var_IMP
    \\ fs [wordSemTheory.get_vars_def]
    \\ fs [state_rel_def,wordSemTheory.call_env_def,lookup_def,LET_THM,
           dataSemTheory.call_env_def,fromList_def,EVAL ``join_env LN []``,
           EVAL ``toAList (inter (fromList2 []) (insert 0 () LN))``,
           wordSemTheory.flush_state_def,flush_state_def]
    \\ conj_tac THEN1
     (qpat_x_assum `option_le _ t.stack_max` mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ Cases_on `stack_size t.stack`
      \\ Cases_on `t.locals_size`
      \\ Cases_on `t.stack_max`
      \\ fs [] \\ rveq \\ fs [])
    \\ asm_exists_tac \\ fs []
    \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
    \\ rpt_drule word_ml_inv_get_var_IMP
    \\ match_mp_tac word_ml_inv_rearrange
    \\ fs [] \\ srw_tac[][] \\ fs[EVAL ``join_env LN []``])
  >~ [‘evaluate (Seq _ _,s)’] >-
   (once_rewrite_tac [data_to_wordTheory.comp_def] \\ fs []
    \\ Cases_on `comp c n l c1` \\ fs [LET_DEF]
    \\ Cases_on `comp c n r c2` \\ fs [LET_DEF]
    \\ fs [dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `evaluate (c1,s)` \\ fs [LET_DEF]
    \\ `q'' <> SOME (Rerr (Rabort Rtype_error))` by
         (Cases_on `q'' = NONE` \\ fs []) \\ fs []
    \\ fs[GSYM AND_IMP_INTRO]
    \\ first_x_assum (drule_all_then assume_tac)
    \\ fs[]
    \\ pop_assum (mp_tac o Q.SPECL [`n`,`l`])
    \\ rpt strip_tac \\ rfs []
    \\ reverse (Cases_on `q'' = NONE`) \\ fs []
    THEN1 (fs [] \\ rpt strip_tac \\ fs []
           \\ srw_tac[][] \\ Cases_on `q''` \\ fs []
           \\ Cases_on `x` \\ fs [] \\ Cases_on `e`
           \\ fs [] \\ PURE_TOP_CASE_TAC >> fs[])
    \\ Cases_on `res1 = SOME NotEnoughSpace` \\ fs []
    THEN1 (fs []
      \\ imp_res_tac dataPropsTheory.evaluate_io_events_mono \\ fs []
      \\ imp_res_tac IS_PREFIX_TRANS \\ fs []
      \\ rw [] \\ fs []
      \\ rpt strip_tac \\ imp_res_tac evaluate_safe_for_space_mono
      \\ imp_res_tac evaluate_option_le_stack_max
      \\ match_mp_tac backendPropsTheory.option_le_trans
      \\ asm_exists_tac \\ fs [])
    \\ srw_tac[][]
    \\ qpat_x_assum `state_rel c l1 l2 _ _ [] locs` (fn th =>
             first_x_assum (fn th1 => mp_tac (MATCH_MP th1 th)))
    \\ imp_res_tac wordSemTheory.evaluate_clock \\ fs[]
    \\ strip_tac \\ pop_assum (mp_tac o Q.SPECL [`n`,`r`])
    \\ rpt strip_tac \\ rfs [] \\ rpt strip_tac \\ fs []
    \\ BasicProvers.EVERY_CASE_TAC \\ fs [mk_loc_def] \\ fs []
    \\ imp_res_tac evaluate_mk_loc_EQ \\ fs []
    \\ imp_res_tac eval_NONE_IMP_jump_exc_NONE_EQ
    \\ fs [jump_exc_inc_clock_EQ_NONE] \\ metis_tac [])
  >~ [‘evaluate (If _ _ _,s)’] >-
   (once_rewrite_tac [data_to_wordTheory.comp_def] \\ fs []
    \\ fs [LET_DEF]
    \\ pairarg_tac \\ fs [] \\ rename1 `comp c n4 l c1 = (q4,l4)`
    \\ pairarg_tac \\ fs [] \\ rename1 `comp c _ _ _ = (q5,l5)`
    \\ fs [dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_var n s.locals` \\ fs []
    \\ fs [] \\ imp_res_tac state_rel_get_var_IMP
    \\ fs [wordSemTheory.get_var_imm_def,
          asmTheory.word_cmp_def]
    \\ imp_res_tac get_var_isT_OR_isF
    \\ fs[GSYM AND_IMP_INTRO]
    \\ Cases_on `isBool T x` \\ fs [] THEN1
     (qpat_x_assum `state_rel c l1 l2 s t [] locs` (fn th =>
               first_x_assum (fn th1 => mp_tac (MATCH_MP th1 th)))
      \\ strip_tac \\ pop_assum (qspecl_then [`n4`,`l`] mp_tac)
      \\ rpt strip_tac \\ rfs [])
    \\ Cases_on `isBool F x` \\ fs [] THEN1
     (qpat_x_assum `state_rel c l1 l2 s t [] locs` (fn th =>
               first_x_assum (fn th1 => mp_tac (MATCH_MP th1 th)))
      \\ strip_tac \\ pop_assum (qspecl_then [`n4`,`l4`] mp_tac)
      \\ rpt strip_tac \\ rfs []))
  \\ rename [‘evaluate (Call ret dest args handler,s)’]
  \\ `t.clock = s.clock` by fs [state_rel_def]
  \\ once_rewrite_tac [data_to_wordTheory.comp_def] \\ fs []
  \\ Cases_on `ret`
  \\ fs [dataSemTheory.evaluate_def,wordSemTheory.evaluate_def,
         wordSemTheory.add_ret_loc_def,get_vars_inc_clock,flush_state_def,
         wordSemTheory.flush_state_def]
  THEN1 (* ret = NONE *)
   (fs [wordSemTheory.bad_dest_args_def]
    \\ Cases_on `get_vars args s.locals` \\ fs []
    \\ imp_res_tac state_rel_0_get_vars_IMP \\ fs []
    \\ Cases_on `find_code dest x s.code s.stack_frame_sizes` \\ fs []
    \\ rename1 `_ = SOME z` \\ PairCases_on `z` \\ fs []
    \\ Cases_on `handler` \\ fs []
    \\ `t.clock = s.clock /\
        t.stack_size = s.stack_frame_sizes` by fs [state_rel_def]
    \\ fs []
    \\ drule find_code_thm \\ rpt (disch_then drule)
    \\ srw_tac[][] \\ fs []
    \\ Cases_on `s.clock = 0` \\ fs[] \\ srw_tac[][] \\ fs[]
    THEN1 (fs[flush_state_def,wordSemTheory.flush_state_def,state_rel_def])
    THEN1 (fs[flush_state_def,wordSemTheory.flush_state_def,state_rel_def])
    \\ fs [CaseEq"option",pair_case_eq] \\ rveq
    \\ fs [] \\ res_tac
    \\ pop_assum kall_tac
    \\ pop_assum mp_tac \\ impl_tac
    >- fs[wordSemTheory.call_env_def,wordSemTheory.dec_clock_def]
    \\ disch_then (qspecl_then [`n1`,`n2`] strip_assume_tac) \\ fs[]
    \\ `t.clock <> 0` by fs [state_rel_def]
    \\ Cases_on `res1` \\ fs [] \\ srw_tac[][] \\ fs[]
    \\ every_case_tac \\ fs [mk_loc_def]
    \\ fs [wordSemTheory.jump_exc_def,wordSemTheory.call_env_def,
           wordSemTheory.dec_clock_def]
    \\ BasicProvers.EVERY_CASE_TAC \\ fs [mk_loc_def])
  \\ Cases_on `x` \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ `domain (FST (adjust_sets r)) <> {}` by fs[adjust_sets_def,domain_fromAList]
  \\ Cases_on `handler` \\ full_simp_tac(srw_ss())[wordSemTheory.evaluate_def]
  \\ Cases_on `get_vars args s.locals` \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac state_rel_get_vars_IMP \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[wordSemTheory.add_ret_loc_def]
  THEN1 (* no handler *)
   (Cases_on `find_code dest x s.code s.stack_frame_sizes` \\ fs[]
    \\ rename1 `_ = SOME x9` \\ PairCases_on `x9` \\ full_simp_tac(srw_ss())[]
    \\ rename1 `_ = SOME (actual_args,called_prog,ss)`
    \\ imp_res_tac data_find_code
    \\ `¬bad_dest_args dest (MAP adjust_var args)` by
      (full_simp_tac(srw_ss())[wordSemTheory.bad_dest_args_def]>>
      imp_res_tac get_vars_IMP_LENGTH>>
      metis_tac[LENGTH_NIL])
    \\ Q.MATCH_ASSUM_RENAME_TAC
         `find_code dest xs s.code s.stack_frame_sizes =SOME (ys,prog,ss)`
    \\ Cases_on `dataSem$cut_env r s.locals` \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac cut_env_IMP_cut_env \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ drule cut_env_IMP_cut_envs \\ strip_tac \\ gvs []
    \\ `t.clock = s.clock /\
        t.stack_size = s.stack_frame_sizes` by full_simp_tac(srw_ss())[state_rel_def]
    \\ full_simp_tac(srw_ss())[]
    \\ rpt_drule find_code_thm_ret
    \\ disch_then (qspecl_then [`n`,`l`] strip_assume_tac) \\ fs []
    \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    THEN1
     (fs [state_rel_def] \\ qpat_x_assum `option_le _ _` mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ fs [wordSemTheory.flush_state_def,wordSemTheory.call_env_def,
             wordPropsTheory.push_env_dec_clock_stack])
    THEN1 (fs[call_env_def,wordSemTheory.call_env_def,state_rel_def])
    \\ Cases_on `evaluate (prog,call_env ys ss (push_env x F (dec_clock s)))`
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `q'` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x' = Rerr (Rabort Rtype_error)` \\ full_simp_tac(srw_ss())[]
    \\ res_tac (* inst ind hyp *)
    \\ pop_assum kall_tac
    \\ pop_assum mp_tac \\ impl_tac >-
      fs[wordSemTheory.call_env_def,wordSemTheory.push_env_def,
         wordSemTheory.env_to_list_def,wordSemTheory.dec_clock_def]
    \\ disch_then (qspecl_then [`n1`,`n2`] strip_assume_tac)
    \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `res1 = SOME NotEnoughSpace` \\ full_simp_tac(srw_ss())[]
    THEN1
     (sg `s1.ffi = r'.ffi` \\ full_simp_tac(srw_ss())[]
      \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ full_simp_tac(srw_ss())[set_var_def]
      \\ imp_res_tac dataPropsTheory.pop_env_const \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac wordPropsTheory.pop_env_const \\ full_simp_tac(srw_ss())[]
      \\ strip_tac \\ imp_res_tac evaluate_safe_for_space_mono
      \\ fs [pop_env_def,CaseEq"list",CaseEq"stack"] \\ rveq \\ fs [])
    \\ reverse (Cases_on `x'` \\ full_simp_tac(srw_ss())[])
    THEN1 (reverse (Cases_on `e`) \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ full_simp_tac(srw_ss())[jump_exc_call_env,jump_exc_dec_clock,jump_exc_push_env_NONE]
      THEN1 (every_case_tac \\ fs[])
      \\ Cases_on `jump_exc t = NONE` \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[jump_exc_push_env_NONE_simp]
      \\ `LENGTH locs = LENGTH s.stack` by
         (fs[state_rel_def] \\ imp_res_tac LIST_REL_LENGTH \\ fs[]) \\ full_simp_tac(srw_ss())[]
      \\ `LENGTH r'.stack < LENGTH locs` by(imp_res_tac eval_exc_stack_shorter \\ fs[])
      \\ imp_res_tac LASTN_TL \\ full_simp_tac(srw_ss())[]
      \\ fs [jump_exc_push_env_NONE])
    \\ Cases_on `pop_env r'` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ gvs [set_vars_sing]
    \\ rpt_drule state_rel_pop_env_set_var_IMP \\ fs []
    \\ disch_then (qspec_then `q` strip_assume_tac) \\ fs []
    \\ imp_res_tac evaluate_IMP_domain_EQ \\ full_simp_tac(srw_ss()) []
    \\ gvs [wordSemTheory.set_vars_def,sptreeTheory.alist_insert_def]
    \\ fs [state_rel_def,wordSemTheory.set_var_def,set_var_def])
  (* with handler *)
  \\ PairCases_on `x` \\ full_simp_tac(srw_ss())[]
  \\ `?prog1 h1. comp c n (l + 2) x1 = (prog1,h1)` by METIS_TAC [PAIR]
  \\ fs[wordSemTheory.evaluate_def,wordSemTheory.add_ret_loc_def]
  \\ Cases_on `find_code dest x' s.code s.stack_frame_sizes` \\ fs[] \\ PairCases_on `x` \\ fs[]
  \\ imp_res_tac data_find_code
  \\ `¬bad_dest_args dest (MAP adjust_var args)` by
      (full_simp_tac(srw_ss())[wordSemTheory.bad_dest_args_def]>>
      imp_res_tac get_vars_IMP_LENGTH>>
      metis_tac[LENGTH_NIL])
  \\ Q.MATCH_ASSUM_RENAME_TAC
       `find_code dest xs s.code s.stack_frame_sizes = SOME (ys,prog,ss)`
  \\ Cases_on `dataSem$cut_env r s.locals` \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac cut_env_IMP_cut_env \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ drule cut_env_IMP_cut_envs \\ strip_tac \\ gvs []
  \\ rpt_drule find_code_thm_handler \\ fs []
  \\ disch_then (qspecl_then [`x0`,`n`,`prog1`,`n`,`l`] strip_assume_tac) \\ fs []
  \\ `t.stack_size = s.stack_frame_sizes` by fs [state_rel_def]
  \\ full_simp_tac std_ss []
  \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  THEN1
   (fs [state_rel_def] \\ qpat_x_assum `option_le _ _` mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ fs [wordSemTheory.flush_state_def,wordSemTheory.call_env_def,
           wordPropsTheory.push_env_dec_clock_stack])
  THEN1 (fs[call_env_def,wordSemTheory.call_env_def,state_rel_def])
  \\ Cases_on `evaluate (prog,call_env ys ss (push_env x T (dec_clock s)))`
  \\ full_simp_tac(srw_ss())[] \\ Cases_on `q'` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `x' = Rerr (Rabort Rtype_error)` \\ full_simp_tac(srw_ss())[]
  \\ `t.clock = s.clock /\
      t.stack_size = s.stack_frame_sizes` by full_simp_tac(srw_ss())[state_rel_def]
  \\ res_tac (* inst ind hyp *)
  \\ pop_assum kall_tac
  \\ pop_assum mp_tac \\ impl_tac >-
      fs[wordSemTheory.call_env_def,wordSemTheory.push_env_def,
         wordSemTheory.env_to_list_def,wordSemTheory.dec_clock_def]
  \\ disch_then (qspecl_then [`n1`,`n2`] strip_assume_tac) \\ fs[]
  \\ Cases_on `res1 = SOME NotEnoughSpace` \\ full_simp_tac(srw_ss())[]
  THEN1 (full_simp_tac(srw_ss())[]
    \\ qsuff_tac `r'.ffi.io_events ≼ s1.ffi.io_events /\ option_le r'.stack_max s1.stack_max`
    THEN1
     (strip_tac \\ imp_res_tac IS_PREFIX_TRANS
      \\ imp_res_tac backendPropsTheory.option_le_trans
      \\ full_simp_tac(srw_ss())[] \\ rpt strip_tac \\ fs []
      \\ fs [CaseEq"option",pair_case_eq,pop_env_def,
             CaseEq"semanticPrimitives$result",
             CaseEq"semanticPrimitives$error_result",
             CaseEq"list",CaseEq"stack"] \\ rveq \\ fs [set_var_def]
      \\ imp_res_tac evaluate_safe_for_space_mono \\ fs [])
    \\ every_case_tac \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac dataPropsTheory.evaluate_io_events_mono
    \\ full_simp_tac(srw_ss())[set_var_def]
    \\ imp_res_tac wordPropsTheory.pop_env_const \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac dataPropsTheory.pop_env_const
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
    \\ TRY strip_tac \\ imp_res_tac evaluate_safe_for_space_mono
    \\ imp_res_tac evaluate_option_le_stack_max
    \\ fs [pop_env_def,CaseEq"list",CaseEq"stack"] \\ rveq \\ fs []
    \\ rfs []
    \\ first_x_assum drule \\ fs []
    \\ disch_then (qspecl_then [`n1`,`n2`] mp_tac)
    \\ (impl_tac THEN1 fs [wordSemTheory.call_env_def,wordSemTheory.dec_clock_def])
    \\ strip_tac \\ rfs []
    \\ imp_res_tac IS_PREFIX_TRANS \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac backendPropsTheory.option_le_trans \\ full_simp_tac(srw_ss())[])
  \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[] THEN1
   (Cases_on `pop_env r'` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ rpt strip_tac \\ full_simp_tac(srw_ss())[set_vars_sing]
    \\ rpt_drule state_rel_pop_env_set_var_IMP \\ fs []
    \\ disch_then (qspec_then `q` strip_assume_tac) \\ fs []
    \\ imp_res_tac evaluate_IMP_domain_EQ \\ full_simp_tac(srw_ss())[]
    \\ fs [set_var_def,CaseEq"option",pair_case_eq,pop_env_def,
             CaseEq"semanticPrimitives$result",
             CaseEq"semanticPrimitives$error_result",
             CaseEq"list",CaseEq"stack"] \\ rveq \\ fs [set_var_def]
    \\ fs [state_rel_def])
  \\ reverse (Cases_on `e`) \\ full_simp_tac(srw_ss())[]
  THEN1 (full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ every_case_tac \\ fs[])
  \\ full_simp_tac(srw_ss())[mk_loc_jump_exc]
  \\ imp_res_tac evaluate_IMP_domain_EQ_Exc \\ full_simp_tac(srw_ss())[]
  \\ qpat_x_assum `!x y z.bbb` kall_tac
  \\ full_simp_tac(srw_ss())[jump_exc_push_env_NONE_simp,jump_exc_push_env_SOME]
  \\ imp_res_tac eval_push_env_T_Raise_IMP_stack_length
  \\ `LENGTH s.stack = LENGTH locs` by
       (full_simp_tac(srw_ss())[state_rel_def]
        \\ imp_res_tac LIST_REL_LENGTH \\ fs[]) \\ fs []
  \\ full_simp_tac(srw_ss())[LASTN_ADD1] \\ srw_tac[][]
  \\ qpat_x_assum `_ ==> _` mp_tac
  \\ impl_tac THEN1
   (simp [wordSemTheory.jump_exc_def,wordSemTheory.call_env_def,
          wordSemTheory.push_env_def,wordSemTheory.dec_clock_def]
    \\ pairarg_tac \\ fs [LASTN_ADD1])
  \\ strip_tac \\ rveq
  \\ first_x_assum (qspec_then `x0` assume_tac)
  \\ res_tac (* inst ind hyp *)
  \\ pop_assum kall_tac
  \\ pop_assum mp_tac \\ impl_tac >-
    (imp_res_tac wordSemTheory.evaluate_clock>>
    fs[wordSemTheory.set_var_def,wordSemTheory.call_env_def,wordSemTheory.push_env_def,
       wordSemTheory.env_to_list_def,wordSemTheory.dec_clock_def])
  \\ disch_then (qspecl_then [`n`,`l+2`] strip_assume_tac) \\ rfs []
  \\ `jump_exc (set_var (adjust_var x0) w t1) = jump_exc t1` by
        fs[wordSemTheory.set_var_def,wordSemTheory.jump_exc_def]
  \\ full_simp_tac(srw_ss())[] \\ rpt strip_tac \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac evaluate_IMP_domain_EQ_Exc \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `res` \\ full_simp_tac(srw_ss())[]
  \\ rpt (CASE_TAC \\ full_simp_tac(srw_ss())[])
  \\ imp_res_tac mk_loc_eq_push_env_exc_Exception \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac eval_push_env_SOME_exc_IMP_s_key_eq
  \\ imp_res_tac s_key_eq_handler_eq_IMP
  \\ full_simp_tac(srw_ss())[jump_exc_inc_clock_EQ_NONE] \\ metis_tac []
QED

Theorem compile_correct_lemma:
   !s c l1 l2 res s1 (t:('a,'c,'ffi) wordSem$state) start.
      (dataSem$evaluate (Call NONE (SOME start) [] NONE,s) = (res,s1)) /\
      res <> SOME (Rerr (Rabort Rtype_error)) /\
      t.termdep > 1 /\
      state_rel c l1 l2 s t [] [] ==>
      ?t1 res1.
        (wordSem$evaluate (Call NONE (SOME start) [0] NONE,t) = (res1,t1)) /\
        option_le t1.stack_max s1.stack_max /\
        (res1 = SOME NotEnoughSpace ==>
           t1.ffi.io_events ≼ s1.ffi.io_events /\
           (c.gc_kind <> None ==> ~s1.safe_for_space)) /\
        (res1 <> SOME NotEnoughSpace ==>
         case res of
        | NONE => (t1.ffi = s1.ffi) /\ (res1 = NONE)
        | SOME (Rval v) => (t1.ffi = s1.ffi) /\
                           ?w. (res1 = SOME (Result (Loc l1 l2) w))
        | SOME (Rerr (Rraise v)) => (t1.ffi = s1.ffi) /\
                                    (?v w. res1 = SOME (Exception v w))
        | SOME (Rerr (Rabort(Rffi_error f))) => (res1 = SOME(FinalFFI f) /\ t1.ffi = s1.ffi)
        | SOME (Rerr (Rabort e)) => (res1 = SOME TimeOut) /\ t1.ffi = s1.ffi)
Proof
  rpt strip_tac
  \\ old_drule data_compile_correct \\ fs []
  \\ ntac 2 (disch_then drule) \\ fs [comp_def]
  \\ strip_tac
  \\ qexists_tac `t1`
  \\ qexists_tac `res1`
  \\ fs [] \\ strip_tac \\ fs []
  \\ every_case_tac \\ fs []
  \\ fs [state_rel_def]
QED

Definition state_rel_ext_def:
  state_rel_ext c l1 l2 s u <=>
    ?t l.
      state_rel c l1 l2 s t [] [] /\
      domain t.code = domain l /\
      t.termdep > 1 /\
      (?tt kk aa co.
         u.compile_oracle =
           (I ## MAP (λp. full_compile_single tt kk aa co (p,NONE))) ∘
             t.compile_oracle /\
         t.compile = (λconf progs. u.compile conf
           (MAP (λp. full_compile_single tt kk aa co (p,NONE)) progs))) /\
      (!n v. lookup n t.code = SOME v ==>
             ∃t' k' a' c' col.
             lookup n l = SOME (SND (full_compile_single t' k' a' c' ((n,v),col)))) /\
      u = t with <| code := l; termdep:=0; compile:=u.compile; compile_oracle := u.compile_oracle|>
End

Theorem compile_correct:
   !x s l1 l2 res s1 (t:('a,'c,'ffi) wordSem$state) start.
      (dataSem$evaluate (Call NONE (SOME start) [] NONE,s) = (res,s1)) /\
      res <> SOME (Rerr (Rabort Rtype_error)) /\
      state_rel_ext x l1 l2 s t ==>
      ?ck t1 res1.
        (wordSem$evaluate (Call NONE (SOME start) [0] NONE,
           (wordProps$inc_clock ck t)) = (res1,t1)) /\
        option_le t1.stack_max s1.stack_max /\
        (res1 = SOME NotEnoughSpace ==>
           t1.ffi.io_events ≼ s1.ffi.io_events /\
           (x.gc_kind <> None ==> ~s1.safe_for_space)) /\
        (res1 <> SOME NotEnoughSpace ==>
         (t1.ffi = s1.ffi) /\
         case res of
         | NONE => (res1 = NONE)
         | SOME (Rval v) => ?w. (res1 = SOME (Result (Loc l1 l2) w))
         | SOME (Rerr (Rraise v)) => (?v w. res1 = SOME (Exception v w))
         | SOME (Rerr (Rabort(Rffi_error f))) => (res1 = SOME(FinalFFI f))
         | SOME (Rerr (Rabort e)) => (res1 = SOME TimeOut))
Proof
  gen_tac
  \\ fs [state_rel_ext_def,PULL_EXISTS] \\ srw_tac[][]
  \\ fs [wordSemTheory.state_component_equality]
  \\ rename1 `state_rel x0 l1 l2 s t2 [] []`
  \\ sg `?l2. code_rel t2.code l2 /\
              map (I ## remove_must_terminate) l2 = l`
  THEN1 (
    fs [boolTheory.SKOLEM_THM,METIS_PROVE [] ``(b ==> ?x. P x) <=> ?x. b ==> P x``]
    \\ fs [spt_eq,lookup_map,eq_shape_map]
    \\ simp [spt_eq,lookup_map,domain_lookup,EXTENSION,PULL_EXISTS,FORALL_PROD]
    \\ fs [word_to_wordProofTheory.code_rel_def,
         word_to_wordTheory.full_compile_single_def]
    \\ sg `?l3. eq_shape l3 l /\ ∀n v.
          lookup n t2.code = SOME v ⇒
          lookup n l3 = SOME (SND
            ((λ(name_num,arg_count,reg_prog).
                (name_num,arg_count,reg_prog))
               (compile_single (f n v) (f' n v) (f'' n v) (f''' n v)
                   ((n,v),f'''' n v))))`
    THEN1
     (qho_match_abbrev_tac `?l3. _ l3 /\ !n v. _ n v ==> _ n l3 = SOME (ff n v)`
      \\ qexists_tac `copy_shape (mapi ff t2.code) l`
      \\ conj_tac THEN1 (fs [] \\ match_mp_tac shape_eq_copy_shape \\ fs [])
      \\ fs [lookup_copy_shape]
      \\ rw [] \\ fs [lookup_mapi])
    \\ qexists_tac `l3`
    \\ rw [] \\ res_tac \\ fs []
    THEN1 (CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs [] \\ metis_tac [])
    \\ fs [spt_eq,lookup_map,domain_lookup,EXTENSION,PULL_EXISTS,FORALL_PROD]
    \\ fs [eq_shape_map] \\ rw []
    \\ imp_res_tac eq_shape_IMP_domain
    \\ fs [spt_eq,lookup_map,domain_lookup,EXTENSION,PULL_EXISTS,FORALL_PROD]
    \\ fs [EXISTS_PROD]
    \\ `?v11 v12. lookup k t.code = SOME (v11,v12)` by metis_tac []
    \\ `?v21 v22. lookup k t2.code = SOME (v21,v22)` by metis_tac []
    \\ res_tac
    \\ fs [] \\ rveq \\ pairarg_tac \\ fs [] \\ rveq \\ fs [])
  \\ drule (compile_word_to_word_thm |> GEN_ALL |> SIMP_RULE std_ss [])
  \\ `domain l2' = domain l` by (rveq \\ fs [domain_map])
  \\ `domain t2.code = domain l2'` by fs []
  \\ `gc_fun_const_ok t2.gc_fun` by
         fs [state_rel_def,gc_fun_const_ok_word_gc_fun]
  \\ rpt (disch_then drule)
  \\ disch_then (qspec_then `start` mp_tac)
  \\ strip_tac \\ fs [] \\ rveq
  \\ `state_rel x0 l1 l2 s (t2 with permute := perm') [] []` by
   (fs [state_rel_def] \\ rfs []
    \\ Cases_on `s.stack` \\ fs [] \\ metis_tac [])
  \\ old_drule compile_correct_lemma \\ fs []
  \\ disch_then (drule o ONCE_REWRITE_RULE [CONJ_COMM])
  \\ fs [] \\ strip_tac \\ fs []
  THEN1 (rveq \\ fs [] \\ every_case_tac \\ fs[])
  \\ pairarg_tac \\ fs [wordPropsTheory.inc_clock_def,data_to_word_gcProofTheory.inc_clock_def]
  \\ qexists_tac `clk`
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,t6)`
  \\ qpat_x_assum `evaulate _ = _` mp_tac
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,t7)`
  \\ `t6 = t7` by
    (unabbrev_all_tac \\ fs [] \\ fs [wordSemTheory.state_component_equality])
  \\ fs [] \\ every_case_tac \\ fs [] \\ rw[] \\ fs []
QED

Triviality state_rel_ext_with_clock:
  state_rel_ext a b c s1 s2 ==>
    state_rel_ext a b c (s1 with clock := k) (s2 with clock := k)
Proof
  fs [state_rel_ext_def] \\ srw_tac[][]
  \\ old_drule state_rel_with_clock
  \\ strip_tac \\ asm_exists_tac \\ fs []
  \\ qexists_tac `l` \\ fs []
  \\ fs [wordSemTheory.state_component_equality]
  \\ metis_tac []
QED

(* observational semantics preservation *)

Theorem compile_semantics_lemma:
   state_rel_ext conf 1 0 (initial_state (ffi:'ffi ffi_state) (fromAList prog) co cc T lims t.stack_size t.clock) (t:('a,'c,'ffi) wordSem$state) /\ fs = t.stack_size /\
   semantics ffi (fromAList prog) co cc lims fs start <> Fail ==>
   semantics t start IN
     extend_with_resource_limit { semantics ffi (fromAList prog) co cc lims fs start }
Proof
  simp[GSYM AND_IMP_INTRO] >> ntac 2 strip_tac >> rveq >>
  simp[dataSemTheory.semantics_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac
  >- (
    qx_gen_tac`r`>>simp[]>>strip_tac>>
    strip_tac >>
    simp[wordSemTheory.semantics_def] >>
    IF_CASES_TAC >- (
      full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
      qhdtm_x_assum`dataSem$evaluate`kall_tac >>
      last_x_assum(qspec_then`k'`mp_tac)>>simp[] >>
      (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
      strip_tac >>
      old_drule compile_correct >> simp[] >> full_simp_tac(srw_ss())[] >>
      simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
      impl_tac >- (
        strip_tac >> full_simp_tac(srw_ss())[] ) >>
      drule state_rel_ext_with_clock >>
      disch_then(qspec_then`k'`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
      disch_then drule >>
      simp[comp_def] >> strip_tac >>
      qmatch_assum_abbrev_tac`option_CASE (FST p) _ _` >>
      Cases_on`p`>>pop_assum(strip_assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
      drule wordPropsTheory.evaluate_add_clock >>
      simp[RIGHT_FORALL_IMP_THM] >>
      impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
      disch_then(qspec_then`ck`mp_tac) >>
      fsrw_tac[ARITH_ss][inc_clock_def] >> srw_tac[][] >>
      every_case_tac >> full_simp_tac(srw_ss())[] ) >>
    DEEP_INTRO_TAC some_intro >> simp[] >>
    conj_tac >- (
      srw_tac[][extend_with_resource_limit_def] >> full_simp_tac(srw_ss())[] >>
      `r' <> Rerr(Rabort Rtype_error)` by(CCONTR_TAC >> fs[]) >>
      `r' <> Rerr(Rabort Rtimeout_error)` by(CCONTR_TAC >> fs[]) >>
      old_drule(dataPropsTheory.evaluate_add_clock)>>simp[]>>
      disch_then(qspec_then`k'`mp_tac)>>simp[]>>strip_tac>>
      old_drule(compile_correct)>>simp[]>>
      drule state_rel_ext_with_clock >>simp[]>>
      disch_then(qspec_then `k+k'` assume_tac)>>disch_then drule>>
      simp[inc_clock_def]>>strip_tac>>
      qpat_x_assum `evaluate _ = (r,_)` assume_tac>>
      dxrule wordPropsTheory.evaluate_add_clock >>
      disch_then(qspec_then `ck+k` mp_tac)>>
      impl_tac>-(CCONTR_TAC>>fs[])>>
      simp[inc_clock_def]>>strip_tac>>
      rpt(PURE_FULL_CASE_TAC>>fs[]>>rveq>>fs[])) >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    old_drule compile_correct >> simp[] >>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    impl_tac >- (
      last_x_assum(qspec_then`k`mp_tac)>>simp[] >>
      srw_tac[][] >> strip_tac >> full_simp_tac(srw_ss())[] ) >>
    old_drule(state_rel_ext_with_clock) >> simp[] >> strip_tac >>
    disch_then drule >>
    simp[comp_def] >> strip_tac >>
    first_x_assum(qspec_then`k+ck`mp_tac) >>
    full_simp_tac(srw_ss())[inc_clock_def] >>
    first_x_assum(qspec_then`k+ck`mp_tac) >>
    simp[] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]) >>
  srw_tac[][] >>
  simp[wordSemTheory.semantics_def] >>
  IF_CASES_TAC >- (
    full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
    last_x_assum(qspec_then`k`mp_tac)>>simp[] >>
    (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
    strip_tac >>
    old_drule compile_correct >> simp[] >>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    old_drule(state_rel_ext_with_clock) >>
    simp[] >> strip_tac >>
    disch_then drule >>
    simp[comp_def] >> strip_tac >>
    qmatch_assum_abbrev_tac`option_CASE (FST p) _ _` >>
    Cases_on`p`>>pop_assum(strip_assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    drule wordPropsTheory.evaluate_add_clock >>
    simp[RIGHT_FORALL_IMP_THM] >>
    impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
    disch_then(qspec_then`ck`mp_tac) >>
    fsrw_tac[ARITH_ss][inc_clock_def] >> srw_tac[][] >>
    every_case_tac >> full_simp_tac(srw_ss())[] ) >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    srw_tac[][extend_with_resource_limit_def] >> full_simp_tac(srw_ss())[] >>
    qpat_x_assum`∀x y. _`(qspec_then`k`mp_tac)>>
    (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
    strip_tac >>
    old_drule(compile_correct)>>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    impl_tac >- (
      strip_tac >> full_simp_tac(srw_ss())[] >>
      last_x_assum(qspec_then`k`mp_tac) >>
      simp[] ) >>
    old_drule(state_rel_ext_with_clock) >>
    simp[] >> strip_tac >>
    disch_then drule >>
    simp[comp_def] >> strip_tac >>
    `t'.ffi.io_events ≼ t1.ffi.io_events` by (
      qmatch_assum_abbrev_tac`evaluate (exps,tt) = (_,t')` >>
      Q.ISPECL_THEN[`exps`,`tt`]mp_tac wordPropsTheory.evaluate_add_clock_io_events_mono >>
      full_simp_tac(srw_ss())[inc_clock_def,Abbr`tt`] >>
      disch_then(qspec_then`ck`mp_tac)>>simp[]) >>
    full_simp_tac(srw_ss())[] >>
    first_assum(qspec_then`k`mp_tac) >>
    first_x_assum(qspec_then`k+ck`mp_tac) >>
    fsrw_tac[ARITH_ss][inc_clock_def] >>
    qhdtm_x_assum`wordSem$evaluate`mp_tac >>
    drule wordPropsTheory.evaluate_add_clock >>
    simp[]>>
    disch_then(qspec_then`ck`mp_tac)>>
    last_x_assum(qspec_then`k`mp_tac) >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]>>srw_tac[][]>>full_simp_tac(srw_ss())[] >>
    qpat_abbrev_tac`ll = IMAGE _ _` >>
    `lprefix_chain ll` by (
      unabbrev_all_tac >>
      Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
      REWRITE_TAC[IMAGE_COMPOSE] >>
      match_mp_tac prefix_chain_lprefix_chain >>
      simp[prefix_chain_def,PULL_EXISTS] >>
      qx_genl_tac[`k1`,`k2`] >>
      qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
      simp[LESS_EQ_EXISTS] >>
      metis_tac[
        dataPropsTheory.evaluate_add_clock_io_events_mono,
        dataPropsTheory.initial_state_with_simp,
        dataPropsTheory.initial_state_simp]) >>
    old_drule build_lprefix_lub_thm >>
    simp[lprefix_lub_def] >> strip_tac >>
    match_mp_tac (GEN_ALL LPREFIX_TRANS) >>
    simp[LPREFIX_fromList] >>
    QUANT_TAC[("l2",`fromList x`,[`x`])] >>
    simp[from_toList] >>
    asm_exists_tac >> simp[] >>
    first_x_assum irule >>
    simp[Abbr`ll`] >>
    qexists_tac`k`>>simp[] ) >>
  srw_tac[][extend_with_resource_limit_def] >>
  qmatch_abbrev_tac`build_lprefix_lub l1 = build_lprefix_lub l2` >>
  `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
    suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_new_chain,unique_lprefix_lub] >>
  conj_asm1_tac >- (
    UNABBREV_ALL_TAC >>
    conj_tac >>
    Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
    REWRITE_TAC[IMAGE_COMPOSE] >>
    match_mp_tac prefix_chain_lprefix_chain >>
    simp[prefix_chain_def,PULL_EXISTS] >>
    qx_genl_tac[`k1`,`k2`] >>
    qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
    simp[LESS_EQ_EXISTS] >>
    metis_tac[
      wordPropsTheory.evaluate_add_clock_io_events_mono,
      EVAL``((t:('a,'c,'ffi) wordSem$state) with clock := k).clock``,
      EVAL``((t:('a,'c,'ffi) wordSem$state) with clock := k) with clock := k2``,
      dataPropsTheory.evaluate_add_clock_io_events_mono,
      dataPropsTheory.initial_state_with_simp,
      dataPropsTheory.initial_state_simp]) >>
  simp[equiv_lprefix_chain_thm] >>
  unabbrev_all_tac >> simp[PULL_EXISTS] >>
  pop_assum kall_tac >>
  simp[LNTH_fromList,PULL_EXISTS] >>
  simp[GSYM FORALL_AND_THM] >>
  rpt gen_tac >>
  reverse conj_tac >> strip_tac >- (
    qmatch_assum_abbrev_tac`n < LENGTH (_ (_ (SND p)))` >>
    Cases_on`p`>>pop_assum(assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    old_drule compile_correct >>
    simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM] >>
    impl_tac >- (
      last_x_assum(qspec_then`k`mp_tac)>>srw_tac[][]>>
      strip_tac >> full_simp_tac(srw_ss())[] ) >>
    old_drule(state_rel_ext_with_clock) >>
    simp[] >> strip_tac >>
    disch_then old_drule >>
    simp[comp_def] >> strip_tac >>
    qexists_tac`k+ck`>>full_simp_tac(srw_ss())[inc_clock_def]>>
    Cases_on`res1=SOME NotEnoughSpace`>>full_simp_tac(srw_ss())[]>-(
      first_x_assum(qspec_then`k+ck`mp_tac) >> simp[] >>
      CASE_TAC >> full_simp_tac(srw_ss())[] ) >>
    ntac 2 (pop_assum mp_tac) >>
    CASE_TAC >> full_simp_tac(srw_ss())[] >>
    TRY CASE_TAC >> full_simp_tac(srw_ss())[] >>
    TRY CASE_TAC >> full_simp_tac(srw_ss())[] >>
    strip_tac >> full_simp_tac(srw_ss())[] >>
    rveq >>
    rpt(first_x_assum(qspec_then`k+ck`mp_tac)>>simp[]) >>
    every_case_tac >> fs[]) >>
  (fn g => subterm (fn tm => Cases_on`^(Term.subst [{redex = #1(dest_exists(#2 g)), residue = “k:num”}] (assert(has_pair_type)tm))`) (#2 g) g) >>
  old_drule compile_correct >>
  simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM] >>
  impl_tac >- (
    last_x_assum(qspec_then`k`mp_tac)>>srw_tac[][]>>
    strip_tac >> full_simp_tac(srw_ss())[] ) >>
  old_drule(state_rel_ext_with_clock) >>
  simp[] >> strip_tac >>
  disch_then old_drule >>
  simp[comp_def] >> strip_tac >>
  full_simp_tac(srw_ss())[inc_clock_def] >>
  Cases_on`res1=SOME NotEnoughSpace`>>full_simp_tac(srw_ss())[]>-(
    first_x_assum(qspec_then`k+ck`mp_tac) >> simp[] >>
    CASE_TAC >> full_simp_tac(srw_ss())[] ) >>
  qmatch_assum_abbrev_tac`n < LENGTH (SND (evaluate (exps,s: (α, γ, 'ffi) wordSem$state))).ffi.io_events` >>
  Q.ISPECL_THEN[`exps`,`s`]mp_tac wordPropsTheory.evaluate_add_clock_io_events_mono >>
  disch_then(qspec_then`ck`mp_tac)>>simp[Abbr`s`]>>strip_tac>>
  qexists_tac`k`>>simp[]>>
  `r.ffi.io_events = t1.ffi.io_events` by (
    ntac 5 (pop_assum mp_tac) >>
    CASE_TAC >> full_simp_tac(srw_ss())[] >>
    every_case_tac >> full_simp_tac(srw_ss())[]>>srw_tac[][]>>
    rpt(first_x_assum(qspec_then`k+ck`mp_tac)>>simp[])) >>
  REV_FULL_SIMP_TAC(srw_ss()++ARITH_ss)[]>>
  fsrw_tac[ARITH_ss][IS_PREFIX_APPEND]>>
  simp[EL_APPEND1]
QED

Theorem compile_semantics_precise_lemma:
   state_rel_ext conf 1 0 (initial_state (ffi:'ffi ffi_state) (fromAList prog) co cc T lims t.stack_size t.clock) (t:('a,'c,'ffi) wordSem$state) /\ fs = t.stack_size /\
   data_lang_safe_for_space ffi (fromAList prog) lims fs start /\ conf.gc_kind <> None /\
   semantics ffi (fromAList prog) co cc lims fs start <> Fail ==>
   semantics t start IN
     extend_with_resource_limit' T { semantics ffi (fromAList prog) co cc lims fs start }
Proof
  simp[GSYM AND_IMP_INTRO] >> ntac 3 strip_tac >> rveq >>
  simp[dataSemTheory.semantics_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac
  >- (
    qx_gen_tac`r`>>simp[]>>strip_tac>>
    strip_tac >>
    simp[wordSemTheory.semantics_def] >>
    IF_CASES_TAC >- (
      full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
      qhdtm_x_assum`dataSem$evaluate`kall_tac >>
      last_x_assum(qspec_then`k'`mp_tac)>>simp[] >>
      (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
      strip_tac >>
      old_drule compile_correct >> simp[] >> full_simp_tac(srw_ss())[] >>
      simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
      impl_tac >- (
        strip_tac >> full_simp_tac(srw_ss())[] ) >>
      drule state_rel_ext_with_clock >>
      disch_then(qspec_then`k'`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
      disch_then drule >>
      simp[comp_def] >> strip_tac >>
      qmatch_assum_abbrev_tac`option_CASE (FST p) _ _` >>
      Cases_on`p`>>pop_assum(strip_assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
      drule wordPropsTheory.evaluate_add_clock >>
      simp[RIGHT_FORALL_IMP_THM] >>
      impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
      disch_then(qspec_then`ck`mp_tac) >>
      fsrw_tac[ARITH_ss][inc_clock_def] >> srw_tac[][] >>
      every_case_tac >> full_simp_tac(srw_ss())[] ) >>
    DEEP_INTRO_TAC some_intro >> simp[] >>
    conj_tac >- (
      srw_tac[][extend_with_resource_limit'_def] >> full_simp_tac(srw_ss())[] >>
      `r' <> Rerr(Rabort Rtype_error)` by(CCONTR_TAC >> fs[]) >>
      `r' <> Rerr(Rabort Rtimeout_error)` by(CCONTR_TAC >> fs[]) >>
      old_drule(dataPropsTheory.evaluate_add_clock)>>simp[]>>
      disch_then(qspec_then`k'`mp_tac)>>simp[]>>strip_tac>>
      old_drule(compile_correct)>>simp[]>>
      drule state_rel_ext_with_clock >>simp[]>>
      disch_then(qspec_then `k+k'` assume_tac)>>disch_then drule>>
      simp[inc_clock_def]>>strip_tac>>
      `s.safe_for_space` by
       (qpat_x_assum `data_lang_safe_for_space _ _ _ _ _` mp_tac
        \\ simp [data_lang_safe_for_space_def]
        \\ qpat_x_assum `_ = (_,s)` assume_tac
        \\ disch_then (qspec_then `k` mp_tac)
        \\ pairarg_tac \\ fs [] \\ strip_tac
        \\ `?s. dataSem$evaluate (Call NONE (SOME start) [] NONE,
               initial_state ffi (fromAList prog) co cc T lims t.stack_size k) =
                 (res,s) /\ cc_co_only_diff s' s` by
             (match_mp_tac evaluate_cc_co_only_diff
              \\ asm_exists_tac \\ fs []
              \\ fs [cc_co_only_diff_def,initial_state_def])
        \\ fs [] \\ rveq \\ fs [cc_co_only_diff_def]) >>
      fs [] >> rfs [] >>
      qpat_x_assum `evaluate _ = (r,_)` assume_tac>>
      dxrule wordPropsTheory.evaluate_add_clock >>
      disch_then(qspec_then `ck+k` mp_tac)>>
      impl_tac>-(CCONTR_TAC>>fs[])>>
      simp[inc_clock_def]>>strip_tac>>
      rpt(PURE_FULL_CASE_TAC>>fs[]>>rveq>>fs[])) >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    old_drule compile_correct >> simp[] >>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    impl_tac >- (
      last_x_assum(qspec_then`k`mp_tac)>>simp[] >>
      srw_tac[][] >> strip_tac >> full_simp_tac(srw_ss())[] ) >>
    old_drule(state_rel_ext_with_clock) >> simp[] >> strip_tac >>
    disch_then drule >>
    simp[comp_def] >> strip_tac >>
    first_x_assum(qspec_then`k+ck`mp_tac) >>
    full_simp_tac(srw_ss())[inc_clock_def] >>
    first_x_assum(qspec_then`k+ck`mp_tac) >>
    simp[] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]) >>
  rewrite_tac [GSYM IMP_DISJ_THM] >>
  srw_tac[][] >>
  simp[wordSemTheory.semantics_def] >>
  IF_CASES_TAC >- (
    full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
    last_x_assum(qspec_then`k`mp_tac)>>simp[] >>
    (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
    strip_tac >>
    old_drule compile_correct >> simp[] >>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    old_drule(state_rel_ext_with_clock) >>
    simp[] >> strip_tac >>
    disch_then drule >>
    simp[comp_def] >> strip_tac >>
    qmatch_assum_abbrev_tac`option_CASE (FST p) _ _` >>
    Cases_on`p`>>pop_assum(strip_assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    drule wordPropsTheory.evaluate_add_clock >>
    simp[RIGHT_FORALL_IMP_THM] >>
    impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
    disch_then(qspec_then`ck`mp_tac) >>
    fsrw_tac[ARITH_ss][inc_clock_def] >> srw_tac[][] >>
    every_case_tac >> full_simp_tac(srw_ss())[] ) >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >-
   (fs [] \\ rpt strip_tac
    \\ Cases_on `evaluate (Call NONE (SOME start) [] NONE,
                    initial_state ffi (fromAList prog) co cc T lims
                      t.stack_size k)`
    \\ `state_rel_ext conf 1 0
          (initial_state ffi (fromAList prog) co cc T lims t.stack_size
             k) (t with clock := k)` by
     (drule state_rel_ext_with_clock
      \\ disch_then (qspec_then `k` mp_tac) \\ fs [initial_state_def])
    \\ first_assum (mp_then (Pos last) mp_tac compile_correct)
    \\ disch_then drule
    \\ impl_tac THEN1
         (strip_tac >> full_simp_tac(srw_ss())[] >>
          last_x_assum(qspec_then`k`mp_tac) >>
          simp[] )
    \\ `r'.safe_for_space` by
       (qpat_x_assum `data_lang_safe_for_space _ _ _ _ _` mp_tac
        \\ simp [data_lang_safe_for_space_def]
        \\ qpat_x_assum `_ = (_,s)` assume_tac
        \\ disch_then (qspec_then `k` mp_tac)
        \\ pairarg_tac \\ fs [] \\ strip_tac
        \\ `?s'. dataSem$evaluate (Call NONE (SOME start) [] NONE,
               initial_state ffi (fromAList prog) co cc T lims t.stack_size k) =
                 (res,s') /\ cc_co_only_diff s s'` by
             (match_mp_tac evaluate_cc_co_only_diff
              \\ asm_exists_tac \\ fs []
              \\ fs [cc_co_only_diff_def,initial_state_def])
        \\ fs [] \\ rveq \\ fs [cc_co_only_diff_def])
    \\ fs [] \\ strip_tac \\ fs [] \\ rfs []
    \\ qpat_x_assum `evaluate _ = (r,_)` assume_tac
    \\ drule wordPropsTheory.evaluate_add_clock
    \\ disch_then (qspec_then `ck` mp_tac)
    \\ impl_tac THEN1 (strip_tac \\ fs [])
    \\ fs [] \\ strip_tac \\ fs [wordPropsTheory.inc_clock_def]
    \\ rveq \\ fs []
    \\ first_x_assum (qspec_then `k+ck` mp_tac) \\ fs []
    \\ strip_tac \\ fs []
    \\ last_x_assum (qspec_then `k` assume_tac) \\ rfs []
    \\ last_x_assum (qspec_then `k` assume_tac) \\ rfs []
    \\ Cases_on `q` \\ fs []
    \\ Cases_on `x` \\ fs [] \\ rveq \\ fs []) >>
  srw_tac[][extend_with_resource_limit'_def] >>
  qmatch_abbrev_tac`build_lprefix_lub l1 = build_lprefix_lub l2` >>
  `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
    suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_new_chain,unique_lprefix_lub] >>
  conj_asm1_tac >- (
    UNABBREV_ALL_TAC >>
    conj_tac >>
    Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
    REWRITE_TAC[IMAGE_COMPOSE] >>
    match_mp_tac prefix_chain_lprefix_chain >>
    simp[prefix_chain_def,PULL_EXISTS] >>
    qx_genl_tac[`k1`,`k2`] >>
    qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
    simp[LESS_EQ_EXISTS] >>
    metis_tac[
      wordPropsTheory.evaluate_add_clock_io_events_mono,
      EVAL``((t:('a,'c,'ffi) wordSem$state) with clock := k).clock``,
      EVAL``((t:('a,'c,'ffi) wordSem$state) with clock := k) with clock := k2``,
      dataPropsTheory.evaluate_add_clock_io_events_mono,
      dataPropsTheory.initial_state_with_simp,
      dataPropsTheory.initial_state_simp]) >>
  simp[equiv_lprefix_chain_thm] >>
  unabbrev_all_tac >> simp[PULL_EXISTS] >>
  pop_assum kall_tac >>
  simp[LNTH_fromList,PULL_EXISTS] >>
  simp[GSYM FORALL_AND_THM] >>
  rpt gen_tac >>
  reverse conj_tac >> strip_tac >- (
    qmatch_assum_abbrev_tac`n < LENGTH (_ (_ (SND p)))` >>
    Cases_on`p`>>pop_assum(assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    old_drule compile_correct >>
    simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM] >>
    impl_tac >- (
      last_x_assum(qspec_then`k`mp_tac)>>srw_tac[][]>>
      strip_tac >> full_simp_tac(srw_ss())[] ) >>
    old_drule(state_rel_ext_with_clock) >>
    simp[] >> strip_tac >>
    disch_then old_drule >>
    simp[comp_def] >> strip_tac >>
    qexists_tac`k+ck`>>full_simp_tac(srw_ss())[inc_clock_def]>>
    Cases_on`res1=SOME NotEnoughSpace`>>full_simp_tac(srw_ss())[]>-(
      first_x_assum(qspec_then`k+ck`mp_tac) >> simp[] >>
      CASE_TAC >> full_simp_tac(srw_ss())[] ) >>
    ntac 2 (pop_assum mp_tac) >>
    CASE_TAC >> full_simp_tac(srw_ss())[] >>
    TRY CASE_TAC >> full_simp_tac(srw_ss())[] >>
    TRY CASE_TAC >> full_simp_tac(srw_ss())[] >>
    strip_tac >> full_simp_tac(srw_ss())[] >>
    rveq >>
    rpt(first_x_assum(qspec_then`k+ck`mp_tac)>>simp[]) >>
    every_case_tac >> fs[]) >>
  (fn g => subterm (fn tm => Cases_on`^(Term.subst [{redex = #1(dest_exists(#2 g)), residue = “k:num”}] (assert(has_pair_type)tm))`) (#2 g) g) >>
  old_drule compile_correct >>
  simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM] >>
  impl_tac >- (
    last_x_assum(qspec_then`k`mp_tac)>>srw_tac[][]>>
    strip_tac >> full_simp_tac(srw_ss())[] ) >>
  old_drule(state_rel_ext_with_clock) >>
  simp[] >> strip_tac >>
  disch_then old_drule >>
  simp[comp_def] >> strip_tac >>
  full_simp_tac(srw_ss())[inc_clock_def] >>
  Cases_on`res1=SOME NotEnoughSpace`>>full_simp_tac(srw_ss())[]>-(
    first_x_assum(qspec_then`k+ck`mp_tac) >> simp[] >>
    CASE_TAC >> full_simp_tac(srw_ss())[] ) >>
  qmatch_assum_abbrev_tac`n < LENGTH (SND (evaluate (exps,s: (α, γ, 'ffi) wordSem$state))).ffi.io_events` >>
  Q.ISPECL_THEN[`exps`,`s`]mp_tac wordPropsTheory.evaluate_add_clock_io_events_mono >>
  disch_then(qspec_then`ck`mp_tac)>>simp[Abbr`s`]>>strip_tac>>
  qexists_tac`k`>>simp[]>>
  `r.ffi.io_events = t1.ffi.io_events` by (
    ntac 5 (pop_assum mp_tac) >>
    CASE_TAC >> full_simp_tac(srw_ss())[] >>
    every_case_tac >> full_simp_tac(srw_ss())[]>>srw_tac[][]>>
    rpt(first_x_assum(qspec_then`k+ck`mp_tac)>>simp[])) >>
  REV_FULL_SIMP_TAC(srw_ss()++ARITH_ss)[]>>
  fsrw_tac[ARITH_ss][IS_PREFIX_APPEND]>>
  simp[EL_APPEND1]
QED

Theorem compile_semantics_precise:
   state_rel_ext conf 1 0 (initial_state (ffi:'ffi ffi_state) (fromAList prog) co cc T lims t.stack_size t.clock) (t:('a,'c,'ffi) wordSem$state) /\
   fs = t.stack_size /\ conf.gc_kind <> None /\
   semantics ffi (fromAList prog) co cc lims fs start <> Fail /\
   data_lang_safe_for_space ffi (fromAList prog) lims fs start ==>
   semantics t start = semantics ffi (fromAList prog) co cc lims fs start
Proof
  rw [] \\ drule compile_semantics_precise_lemma \\ fs []
  \\ disch_then drule \\ fs [extend_with_resource_limit'_def]
QED

Definition get_limits_def:
  get_limits c (t :('a, 'c, 'ffi) wordSem$state) =
    <| stack_limit := t.stack_limit
     ; heap_limit := w2n (theWord (t.store ' HeapLength)) DIV (dimindex (:'a) DIV 8)
     ; length_limit := c.len_size
     ; arch_64_bit := (dimindex (:'a) = 64)
     ; has_fp_ops := c.has_fp_ops
     ; has_fp_tops := c.has_fp_tern
     |>
End

Theorem option_le_SOME:
  option_le x (SOME n) <=> ?m. x = SOME m /\ m <= n
Proof
  Cases_on `x` \\ fs []
QED

Theorem compile_semantics:
  (t :(α, γ, 'ffi) wordSem$state).handler = 0 ∧ t.gc_fun = word_gc_fun c ∧
  init_store_ok c t.store t.memory t.mdomain t.code_buffer t.data_buffer ∧
  good_dimindex (:α) ∧ lookup 0 t.locals = SOME (Loc 1 0) ∧ t.stack = [] ∧
  conf_ok (:α) c ∧ t.termdep = 0 ∧ code_rel c (fromAList prog) x1 ∧
  cc =
  (λcfg.
       OPTION_MAP (I ## MAP upper_w2w ## I) ∘ tcc cfg ∘
       MAP (compile_part c)) ∧
  Abbrev (tco = (I ## MAP (compile_part c)) ∘ co) ∧
  (∀n. EVERY (λ(n,_). data_num_stubs <= n) (SND (co n))) ∧
  code_rel_ext x1 t.code ∧ domain x1 = domain t.code ∧ t.be = c.be ∧
  t.stack_max = SOME 1 ∧ t.locals_size = SOME 0 ∧ t.stack_limit <> 0 ∧
  t.compile_oracle =
  (I ## MAP (λp. full_compile_single tt kk aa coo (p,NONE))) ∘ tco ∧
  Abbrev
    (tcc =
     (λconf progs.
          t.compile conf
            (MAP (λp. full_compile_single tt kk aa coo (p,NONE)) progs))) ∧
  fs = t.stack_size ∧
  Fail ≠ semantics t.ffi (fromAList prog) co cc zero_limits fs start ⇒
  (data_lang_safe_for_space t.ffi (fromAList prog) (get_limits c t) fs start /\
   c.gc_kind <> None ⇒ word_lang_safe_for_space t start) ∧
  semantics t start ∈
  extend_with_resource_limit'
    (data_lang_safe_for_space t.ffi (fromAList prog) (get_limits c t) fs
       start /\ c.gc_kind <> None)
    {semantics t.ffi (fromAList prog) co cc zero_limits fs start}
Proof
  strip_tac
  \\ `state_rel_ext c 1 0
        (initial_state t.ffi (fromAList prog) co
        (λcfg. OPTION_MAP (I ## MAP upper_w2w ## I) ∘ tcc cfg ∘
                 MAP (compile_part c)) T (get_limits c t) t.stack_size t.clock) t` by
   (fs[state_rel_ext_def]>>rw[]>>
    fs[code_rel_ext_def]>>
    qexists_tac`t with <|code := x1; termdep := 2; compile_oracle := tco; compile := tcc |>`>>
    simp[wordSemTheory.state_component_equality]>>
    CONJ_TAC >-
      (qmatch_goalsub_abbrev_tac`state_rel _ _ _ _ ttt`>>
      `t.clock = ttt.clock /\ t.stack_size = ttt.stack_size` by
        fs[Abbr`ttt`]>>
      simp[]>>
      match_mp_tac state_rel_init>>
      unabbrev_all_tac>>fs[code_oracle_rel_def] >>
      fs [init_store_ok_def,get_limits_def,bytes_in_word_def,word_mul_n2w] >>
      fs [FLOOKUP_DEF,wordSemTheory.theWord_def] >>
      fs [data_to_wordTheory.max_heap_limit_def] >>
      `0 < dimindex (:α) DIV 8 /\ (dimindex (:α) DIV 8) < dimword (:α)` by
           fs [good_dimindex_def,dimword_def] >> fs [] >>
      qsuff_tac `limit * (dimindex (:α) DIV 8) < dimword (:α)` THEN1 fs [MULT_DIV] >>
      fs [good_dimindex_def,dimword_def] \\ rfs [backend_commonTheory.word_shift_def] >>
      fs [good_dimindex_def,dimword_def] \\ rfs [backend_commonTheory.word_shift_def])>>
    CONJ_TAC>-
      (unabbrev_all_tac>>fs[]>>
      metis_tac[])>>
    fs[FORALL_PROD]>>
    metis_tac[])
  \\ qmatch_goalsub_abbrev_tac `extend_with_resource_limit' precise`
  \\ reverse (Cases_on `precise`)
  THEN1 (* non-precise case *)
   (fs [extend_with_resource_limit'_def]
    \\ rpt strip_tac
    \\ once_rewrite_tac [dataPropsTheory.semantics_zero_limits]
    \\ match_mp_tac (GEN_ALL compile_semantics_lemma
         |> ONCE_REWRITE_RULE [dataPropsTheory.semantics_zero_limits])
    \\ qexists_tac `get_limits c t` \\ fs []
    \\ qexists_tac `c` \\ fs []
    \\ qpat_x_assum `Fail <> _` mp_tac
    \\ once_rewrite_tac [dataPropsTheory.semantics_zero_limits] \\ fs [])
  \\ fs [markerTheory.Abbrev_def,extend_with_resource_limit'_def]
  \\ reverse conj_tac
  THEN1 (* precise case *)
   (rpt strip_tac
    \\ once_rewrite_tac [dataPropsTheory.semantics_zero_limits]
    \\ match_mp_tac (GEN_ALL compile_semantics_precise
         |> ONCE_REWRITE_RULE [dataPropsTheory.semantics_zero_limits])
    \\ qexists_tac `get_limits c t` \\ fs []
    \\ qexists_tac `c` \\ fs []
    \\ qpat_x_assum `Fail <> _` mp_tac
    \\ once_rewrite_tac [dataPropsTheory.semantics_zero_limits] \\ fs []
    \\ rfs [])
  (* data_lang_safe_for_space ==> word_lang_safe_for_space *)
  \\ rename [`word_lang_safe_for_space _ _`]
  \\ fs [wordSemTheory.word_lang_safe_for_space_def,
         data_lang_safe_for_space_def]
  \\ rpt strip_tac
  \\ first_x_assum (qspec_then `k` mp_tac)
  \\ pairarg_tac \\ fs [] \\ strip_tac
  \\ drule state_rel_ext_with_clock
  \\ disch_then (qspec_then `k` assume_tac) \\ fs []
  \\ `?t1. dataSem$evaluate (Call NONE (SOME start) [] NONE,
             initial_state t.ffi (fromAList prog) co cc T (get_limits c t) fs k) =
           (res',t1) /\ cc_co_only_diff s t1` by
   (match_mp_tac evaluate_cc_co_only_diff
    \\ asm_exists_tac \\ fs []
    \\ fs [cc_co_only_diff_def,initial_state_def])
  \\ drule compile_correct
  \\ simp [GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
  \\ impl_tac THEN1
   (CCONTR_TAC \\ fs [] \\ qpat_x_assum `Fail ≠ _` mp_tac \\ fs []
    \\ once_rewrite_tac [EQ_SYM_EQ] \\ rfs []
    \\ once_rewrite_tac [semantics_zero_limits]
    \\ qpat_x_assum `cc = _` (assume_tac o GSYM) \\ fs []
    \\ qsuff_tac `semantics t.ffi (fromAList prog) co cc (get_limits c t) fs start = Fail`
    THEN1 (once_rewrite_tac [semantics_zero_limits] \\ fs [])
    \\ simp [semantics_def,CaseEq"bool"] \\ rveq
    \\ disj1_tac \\ qexists_tac `k` \\ rfs [])
  \\ rfs []
  \\ disch_then drule
  \\ strip_tac
  \\ `t'.stack_limit = t.stack_limit /\
      s.limits.stack_limit = t.stack_limit` by
   (imp_res_tac dataPropsTheory.evaluate_stack_limit
    \\ imp_res_tac evaluate_consts
    \\ imp_res_tac wordPropsTheory.evaluate_stack_limit
    \\ fs [initial_state_def,get_limits_def,cc_co_only_diff_def]
   )
  \\ fs []
  \\ `option_le s.stack_max (SOME s.limits.stack_limit)` by
   (qpat_x_assum `_ = (_,s)` assume_tac
    \\ drule evaluate_stack_max_le_stack_limit \\ fs []
    \\ disch_then match_mp_tac
    \\ fs [initial_state_def,get_limits_def])
  \\ `option_le t1'.stack_max s.stack_max` by
        fs [cc_co_only_diff_def]
  \\ `option_le t'.stack_max t1'.stack_max` by
        (drule_then drule wordPropsTheory.evaluate_stack_max_only_grows \\ fs [])
  \\ ntac 5 (rfs [option_le_SOME])
QED

val _ = (max_print_depth := 15);

val extract_labels_def = wordConvsTheory.extract_labels_def;

Theorem extract_labels_MemEqList[simp]:
  ∀a x. extract_labels (MemEqList a x) = []
Proof
  Induct_on `x`
  \\ asm_rewrite_tac [MemEqList_def,extract_labels_def,APPEND]
QED

Theorem extract_labels_StoreEach:
  ∀xs a d. extract_labels (StoreEach a xs d) = []
Proof
  Induct \\ fs [StoreEach_def,extract_labels_def]
QED

Theorem extract_labels_StoreAnyConsts:
  ∀r1 r2 r3 ws w. extract_labels (StoreAnyConsts r1 r2 r3 ws w) = []
Proof
  ho_match_mp_tac StoreAnyConsts_ind \\ rw []
  \\ fs [StoreAnyConsts_def]
  THEN1 (every_case_tac \\ EVAL_TAC)
  \\ CASE_TAC
  \\ TRY pairarg_tac \\ fs []
  \\ fs [extract_labels_def,list_Seq_def]
QED

(* TODO: goes away on inlineenc branch *)
Triviality extract_labels_WordOp64_on_32:
  extract_labels (WordOp64_on_32 f) = []
Proof
  simp[WordOp64_on_32_def]>>Cases_on`f`>>simp[]>>
  EVAL_TAC
QED

Triviality extract_labels_WordShift64_on_32:
  extract_labels (WordShift64_on_32 f g) = []
Proof
  simp[WordShift64_on_32_def]>>
  Cases_on`f`>>simp[]>>
  IF_CASES_TAC>>EVAL_TAC
QED

Triviality extract_labels_assignWordOp:
  assign a b c d (WordOp (WordOpw e f)) g h = (i,j) ⇒
  extract_labels i = [] ∧ c ≤ j
Proof
  simp[assign_def]>>
  Cases_on`dimindex(:'a) = 64`>> simp[]
  >- (every_case_tac>>rw[]>> EVAL_TAC)
  >>
    every_case_tac>>rw[]>>
    simp[extract_labels_def,list_Seq_def,extract_labels_WordOp64_on_32]>>
    EVAL_TAC
QED

Triviality extract_labels_assignWordShift:
  assign a b c d (WordOp (WordShift e f k)) g h = (i,j) ⇒
  extract_labels i = [] ∧ c ≤ j
Proof
  simp[assign_def]>>
  Cases_on`dimindex(:'a) >= 64`>> simp[]
  >- (every_case_tac>>rw[]>> EVAL_TAC)
  >>
    every_case_tac>>rw[]>>
    simp[extract_labels_def,list_Seq_def,extract_labels_WordShift64_on_32]>>
    EVAL_TAC
QED

fun cases_on_op q = Cases_on q >|
  map (MAP_EVERY Cases_on)
      [[`n`], [`s`], [`i`], [`w`], [`b`], [`g`], [`m`], [], [`t`]];

Theorem data_to_word_lab_pres_lem:
  ∀c n l p.
    l ≠ 0 ⇒
    let (cp,l') = comp c n l p in
    l ≤ l' ∧
    EVERY (λ(l1,l2). l1 = n ∧ l ≤ l2 ∧ l2 < l') (extract_labels cp) ∧
    ALL_DISTINCT (extract_labels cp)
Proof
  HO_MATCH_MP_TAC comp_ind>>Cases_on`p`>>rw[]>>
  once_rewrite_tac[comp_def]>>fs[extract_labels_def]
  >-
    (BasicProvers.EVERY_CASE_TAC>>fs[]>>rveq>>fs[extract_labels_def]>>
    rpt(pairarg_tac>>fs[])>>rveq>>fs[extract_labels_def]>>
    fs[EVERY_MEM,FORALL_PROD]>>rw[]>>
    res_tac>>fs[]>>
    CCONTR_TAC>>fs[]>>res_tac>>fs[])
  >-
    (qmatch_goalsub_rename_tac `assign _ _ _ _ opname _ _` >>
    cases_on_op `opname`>>
    TRY(
      rename1`WordOp (WordOpw _ _)`>>
      pairarg_tac>>old_drule extract_labels_assignWordOp>>
      simp[])>>
    TRY(
      rename1`WordOp (WordShift _ _ _)`>>
      pairarg_tac>>old_drule extract_labels_assignWordShift>>
      simp[])>>
    fs[extract_labels_def,GiveUp_def,assign_def,assign_def_extras]>>
    BasicProvers.EVERY_CASE_TAC>>
    fs[extract_labels_def,list_Seq_def,extract_labels_StoreEach,
       extract_labels_StoreAnyConsts,Maxout_bits_code_def])
  >~ [‘force_thunk’] >- (
    pairarg_tac \\ gvs [force_thunk_def, AllCaseEqs()]
    >- gvs [GiveUp_def, extract_labels_def]
    \\ gvs [extract_labels_def]
    \\ CASE_TAC \\ gvs [list_Seq_def, extract_labels_def]
    \\ CASE_TAC \\ gvs [extract_labels_def])
  >>
    (rpt (pairarg_tac>>fs[])>>rveq>>
          fs[extract_labels_def,EVERY_MEM,FORALL_PROD,ALL_DISTINCT_APPEND,
             SilentFFI_def,list_Seq_def]>>
    rw[]>> res_tac>>fs[]>>
    CCONTR_TAC>>fs[]>>res_tac>>fs[] >>
    fs[extract_labels_def,EVERY_MEM,FORALL_PROD,ALL_DISTINCT_APPEND,
       SilentFFI_def,list_Seq_def]>>
    every_case_tac >> fs [] >>
    fs[extract_labels_def,EVERY_MEM,FORALL_PROD,ALL_DISTINCT_APPEND,
       SilentFFI_def,list_Seq_def])
QED

Triviality labels_rel_emp:
  labels_rel [] ls ⇒ ls = []
Proof
  fs[wordConvsTheory.labels_rel_def]
QED

Theorem stub_labels:
    EVERY (λ(n,m,p).
    EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) (extract_labels p)  ∧
                     ALL_DISTINCT (extract_labels p))
    (stubs (:'a) data_conf)
Proof
  simp[data_to_wordTheory.stubs_def,generated_bignum_stubs_eq]>>
  rpt conj_tac >>
  rpt (EVAL_TAC \\ rw [] \\ EVAL_TAC \\ NO_TAC) >>
  CONV_TAC (RAND_CONV EVAL) >>
  CONV_TAC ((RATOR_CONV o RAND_CONV) EVAL)
QED

Theorem stubs_with_has_fp_ops[simp]:
   stubs (:α) (data_conf with has_fp_ops := b) = stubs (:α) data_conf
Proof
  EVAL_TAC \\ fs []
QED

Theorem stubs_with_has_fp_tern[simp]:
  stubs (:'a) (data_conf with has_fp_tern := b) = stubs (:'a) data_conf
Proof
  EVAL_TAC \\ fs []
QED

(* no ShareInst in the compiled program *)

Theorem list_Seq_no_share_inst:
  !xs. no_share_inst (list_Seq xs) = EVERY no_share_inst xs
Proof
  ho_match_mp_tac list_Seq_ind >>
  rw[list_Seq_def,no_share_inst_def]
QED

Theorem StoreEach_no_share_inst:
  !v xs offset. no_share_inst (StoreEach v xs offset)
Proof
  Induct_on `xs` >>
  gvs[StoreEach_def,no_share_inst_def]
QED

Theorem MemEqList_no_share_inst:
  !a xs. no_share_inst (MemEqList a xs)
Proof
  Induct_on `xs` >>
  gvs[MemEqList_def,no_share_inst_def]
QED

Theorem StoreAnyConsts_no_share_inst:
  !r1 r2 r3 vs v.
    no_share_inst (StoreAnyConsts r1 r2 r3 vs v)
Proof
  ho_match_mp_tac StoreAnyConsts_ind >>
  rw[no_share_inst_def,StoreAnyConsts_def] >>
  TOP_CASE_TAC >>
  simp[no_share_inst_def,list_Seq_no_share_inst] >>
  pairarg_tac >>
  gvs[no_share_inst_def]
QED

Theorem stubs_no_share_inst:
  EVERY (\x. no_share_inst (SND $ SND x)) (data_to_word$stubs (:'a) data_conf)
Proof
  EVAL_TAC >>
  rw [] >>
  EVAL_TAC
QED

Theorem comp_no_share_inst:
  !c secn l prog prog' l'.
  data_to_word$comp c secn l prog = (prog',l') ==>
  no_share_inst prog'
Proof
  ho_match_mp_tac comp_ind >>
  Cases_on `prog` >>
  rw[]
  >- gvs[comp_def,no_share_inst_def] (* Skip *)
  >- gvs[comp_def,no_share_inst_def] (* Move *)
  >- ( (* Call *)
    first_x_assum mp_tac >>
    rw[Once comp_def,AllCaseEqs()] >>
    simp[no_share_inst_def] >>
    gvs[ELIM_UNCURRY,no_share_inst_def] >>
    metis_tac[FST_EQ_EQUIV]
  )
  >- ( (* Assign *)
    gvs[comp_def,AllCaseEqs(),assign_def,all_assign_defs,
      arg1_def,arg2_def,arg3_def,arg4_def] >>
    simp[no_share_inst_def,
      GiveUp_def,BignumHalt_def,AllocVar_def,SilentFFI_def,
      list_Seq_no_share_inst,StoreEach_no_share_inst,
      Make_ptr_bits_code_def,StoreAnyConsts_no_share_inst,
      Maxout_bits_code_def,MemEqList_no_share_inst,
      WriteWord64_def,WordOp64_on_32_def,WriteWord64_on_32_def,
      LoadWord64_def,WordShift64_on_32_def,LoadBignum_def,
      WriteWord32_on_32_def] >>
    rpt (
      TOP_CASE_TAC >>
      simp[no_share_inst_def,list_Seq_no_share_inst])
  )
  >- ( (* Seq *)
    first_x_assum mp_tac >>
    rw[Once comp_def] >>
    gvs[ELIM_UNCURRY,no_share_inst_def] >>
    metis_tac[FST_EQ_EQUIV,SND_EQ_EQUIV]
  )
  >- ( (* If *)
    first_x_assum mp_tac >>
    rw[Once comp_def] >>
    gvs[ELIM_UNCURRY,no_share_inst_def] >>
    metis_tac[FST_EQ_EQUIV,SND_EQ_EQUIV]
  )
  >- ( (* MakeSpace *)
    gvs[comp_def,no_share_inst_def,list_Seq_no_share_inst,SilentFFI_def] >>
    IF_CASES_TAC >>
    simp[comp_def,no_share_inst_def,list_Seq_no_share_inst]
  )
  >~ [‘Force’] >- (
    gvs [comp_def, force_thunk_def, AllCaseEqs()]
    >- gvs [GiveUp_def, no_share_inst_def]
    \\ gvs [no_share_inst_def]
    \\ CASE_TAC \\ gvs [no_share_inst_def, list_Seq_no_share_inst]
    \\ CASE_TAC \\ gvs [no_share_inst_def])
  >> gvs[comp_def,no_share_inst_def] (* Raise | Return | Tick *)
QED

Triviality MAP_FST_ZIP:
  !xs ys. MAP FST (ZIP (xs, ys)) = TAKE (LENGTH ys) xs
Proof
  Induct \\ simp [ZIP_def]
  \\ gen_tac
  \\ Cases \\ simp [ZIP_def]
QED

Theorem compile_no_share_inst:
  data_to_word$compile data_conf word_conf asm_conf prog = (xx,prog') ⇒
  EVERY (λ(n,m,pp). no_share_inst pp) prog'
Proof
  rw[data_to_wordTheory.compile_def] >>
  gvs[ELIM_UNCURRY,word_to_wordTheory.compile_def,
    EVERY_MAP,word_to_wordTheory.full_compile_single_def,
    remove_must_terminate_no_share_inst] >>
  irule MONO_EVERY >>
  simp[] >>
  qexists `no_share_inst o SND o SND o FST` >>
  conj_tac
  >- (rw[] >>
      irule remove_must_terminate_no_share_inst >>
      pop_assum mp_tac>>
      simp [FORALL_PROD, no_share_inst_subprogs_def]
      \\ simp [compile_single_not_created_subprogs |> GEN_ALL |> SIMP_RULE std_ss [PAIR_FST_SND_EQ]]
  )
  >>
  REWRITE_TAC [combinTheory.o_ASSOC] >>
  REWRITE_TAC [GSYM rich_listTheory.ALL_EL_MAP] >>
  simp [MAP_FST_ZIP] >>
  simp [EVERY_MAP] >>
  irule EVERY_TAKE >>
  simp[stubs_no_share_inst,EVERY_MAP] >>
  rw [EVERY_MEM, FORALL_PROD, compile_part_def] >>
  simp [comp_no_share_inst |> SIMP_RULE std_ss [PAIR_FST_SND_EQ]]
QED

(***)

Theorem data_to_word_compile_lab_pres:
    let (c,p) = compile data_conf word_conf asm_conf prog in
    MAP FST p = MAP FST (stubs(:α) data_conf) ++ MAP FST prog ∧
    EVERY (λn,m,(p:α wordLang$prog).
      let labs = extract_labels p in
      EVERY (λ(l1,l2).l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) labs ∧
      ALL_DISTINCT labs) p
Proof
  fs[data_to_wordTheory.compile_def]>>
  qpat_abbrev_tac`datap = _ ++ MAP (A B) prog`>>
  mp_tac (compile_to_word_conventions |>GEN_ALL |> Q.SPECL [`word_conf`,`datap`,`asm_conf`])>>
  impl_tac>-
   (fs[Abbr‘datap’]>>
    irule_at Any EVERY_MONOTONIC>>
    qexists ‘λx. no_share_inst (SND $ SND x)’>>simp[FORALL_PROD]>>
    irule_at Any stubs_no_share_inst>>
    fs[EVERY_MAP,LAMBDA_PROD]>>
    simp[compile_part_def]>>
    simp[EVERY_MEM]>>rw[]>>
    pairarg_tac>>fs[]>>irule OR_INTRO_THM1>>
    irule comp_no_share_inst>>metis_tac[PAIR])>>
  rw[]>>
  pairarg_tac>>fs[Abbr`datap`]>>
  fs[EVERY_MEM]>>rw[]
  >-
    (match_mp_tac LIST_EQ>>rw[EL_MAP]>>
    Cases_on`EL x prog`>>Cases_on`r`>>fs[compile_part_def]) >>
  qmatch_assum_abbrev_tac`MAP FST p = MAP FST p1 ++ MAP FST p2`>>
  full_simp_tac std_ss [GSYM MAP_APPEND]>>
  qabbrev_tac`pp = p1 ++ p2` >>
  fs[EL_MAP,MEM_EL,FORALL_PROD]>>
  `EVERY (λ(n,m,p).
    EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) (extract_labels p)  ∧ ALL_DISTINCT (extract_labels p)) pp` by
    (unabbrev_all_tac>>fs[EVERY_MEM]>>CONJ_TAC
    >-
      (assume_tac stub_labels>>
      fs[EVERY_MEM])
    >>
      fs[MEM_MAP,MEM_EL,EXISTS_PROD]>>rw[]>>fs[compile_part_def]>>
      qmatch_goalsub_abbrev_tac `comp data_conf2` >>
      Q.SPECL_THEN [`data_conf2`,`p_1`,`2n`,`p_2`]assume_tac
        data_to_word_lab_pres_lem>>
      fs[]>>pairarg_tac>>fs[EVERY_EL,PULL_EXISTS]>>
      rw[]>>res_tac>>
      pairarg_tac>>fs[])>>
  fs[LIST_REL_EL_EQN,EVERY_EL]>>
  rpt (first_x_assum(qspec_then`n` assume_tac))>>rfs[]>>
  rfs[EL_MAP]>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  rw[] >>fs[wordConvsTheory.labels_rel_def,SUBSET_DEF,MEM_EL,PULL_EXISTS]>>
  first_x_assum(qspec_then`n'''` assume_tac)>>rfs[]>>
  res_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  qpat_x_assum`A=MAP FST pp` mp_tac>>simp[Once LIST_EQ_REWRITE,EL_MAP]>>
  disch_then(qspec_then`n` assume_tac)>>rfs[]
QED

Triviality StoreEach_no_inst:
  ∀a ls off.
  every_inst (inst_ok_less ac) (StoreEach a ls off)
Proof
  Induct_on`ls`>>rw[StoreEach_def,every_inst_def]
QED

Triviality MemEqList_no_inst:
  ∀a x.
  every_inst (inst_ok_less ac) (MemEqList a x)
Proof
  Induct_on `x` \\ fs [MemEqList_def,every_inst_def]
QED

Theorem StoreAnyConsts_no_inst[local]:
  ∀r1 r2 r3 ws w. every_inst (inst_ok_less ac) (StoreAnyConsts r1 r2 r3 ws w)
Proof
  ho_match_mp_tac StoreAnyConsts_ind \\ rw []
  \\ fs [StoreAnyConsts_def] \\ every_case_tac
  \\ fs [list_Seq_def] \\ rpt (pairarg_tac \\ fs [])
  \\ fs [every_inst_def]
QED

fun cases_on_op q = Cases_on q >|
  map (MAP_EVERY Cases_on)
      [[`n`], [`s`], [`i`], [`w`], [`b`], [`g`], [`m`], [], [`t`]];

Theorem assign_no_inst[local]:
  ((a.has_longdiv ⇒ (ac.ISA = x86_64)) ∧
   (a.has_div ⇒ (ac.ISA ∈ {ARMv8; MIPS;RISC_V})) ∧
   (a.has_fp_ops ⇒ 1 < ac.fp_reg_count) ∧
   (a.has_fp_tern ==> 2 < ac.fp_reg_count /\ ac.ISA = ARMv7) /\
  addr_offset_ok ac 0w /\ byte_offset_ok ac 0w) ⇒
  every_inst (inst_ok_less ac) (FST(assign a b c d e f g))
Proof
  fs[assign_def]>>
  cases_on_op`e`>>fs[every_inst_def]>>
  rw[]>>fs[every_inst_def,GiveUp_def]>>
  every_case_tac>>
  TRY(Cases_on`f'`)>>
  fs[every_inst_def,list_Seq_def,StoreEach_no_inst,
    Maxout_bits_code_def,GiveUp_def,StoreAnyConsts_no_inst,
    inst_ok_less_def,assign_def_extras,MemEqList_no_inst,
    asmTheory.fp_reg_ok_def,fp_uop_inst_def,fp_cmp_inst_def,
    fp_bop_inst_def, fp_top_inst_def]>>
  IF_CASES_TAC>>fs[every_inst_def,list_Seq_def,StoreEach_no_inst,
    Maxout_bits_code_def,GiveUp_def,
    inst_ok_less_def,assign_def_extras,MemEqList_no_inst] \\ FAIL_TAC ""
QED

(*
inst_ok_less_def
*)

Theorem comp_no_inst:
    ∀c n m p.
  ((c.has_longdiv ⇒ (ac.ISA = x86_64)) ∧
   (c.has_div ⇒ (ac.ISA ∈ {ARMv8; MIPS;RISC_V})) ∧
   (c.has_fp_ops ⇒ 1 < ac.fp_reg_count) ∧
   (c.has_fp_tern ==> 2 < ac.fp_reg_count /\ ac.ISA = ARMv7)) /\
  addr_offset_ok ac 0w /\ byte_offset_ok ac 0w ⇒
  every_inst (inst_ok_less ac) (FST(comp c n m p))
Proof
  ho_match_mp_tac comp_ind>>Cases_on`p`>>rw[]>>
  simp[Once comp_def,every_inst_def,force_thunk_def]>>
  every_case_tac>>fs[]>>
  rpt(pairarg_tac>>fs[])>>
  fs[assign_no_inst]>>
  EVAL_TAC>>fs[] >>
  IF_CASES_TAC >> EVAL_TAC >> fs []
QED

Triviality bounds_lem:
  (dimindex(:'a) = 32 ∨ dimindex(:'a) = 64) ∧
  (w:'a word = -3w ∨
  w = -2w ∨
  w = -1w ∨
  w = 0w ∨
  w = 1w ∨
  w = 2w ∨
  w = 3w ∨
  w = 4w ∨
  w = 5w ∨
  w = 6w ∨
  w = 7w)
  ⇒
  -8w ≤ w ∧ w ≤ 8w
Proof
  rw[]>>
  EVAL_TAC>>
  simp[dimword_def]>>
  EVAL_TAC>>
  simp[dimword_def]>>
  EVAL_TAC>>
  simp[numeral_bitTheory.iSUC,numeralTheory.numeral_evenodd,ODD]
QED

Theorem data_to_word_compile_conventions:
    good_dimindex(:'a) ==>
  let (c,p) = compile data_conf wc ac prog in
  EVERY (λ(n,m,prog).
    flat_exp_conventions (prog:'a wordLang$prog) ∧
    post_alloc_conventions (ac.reg_count - (5+LENGTH ac.avoid_regs)) prog ∧
    ((data_conf.has_longdiv ⇒ (ac.ISA = x86_64)) ∧
    (data_conf.has_div ⇒ (ac.ISA ∈ {ARMv8; MIPS;RISC_V})) ∧
    addr_offset_ok ac 0w /\
    hw_offset_ok ac 0w /\
    (* NOTE: this condition is
       stricter than necessary, but we have much more byte_offset space
       anyway on all the targets *)
    (∀w. -8w <= w ∧ w <= 8w ==> byte_offset_ok ac w)
    ⇒ full_inst_ok_less ac prog) ∧
    (ac.two_reg_arith ⇒ every_inst two_reg_inst prog) ∧
    (no_share_inst prog ∨ ac.ISA ≠ Ag32)) p
Proof
 fs[data_to_wordTheory.compile_def]>>
 qpat_abbrev_tac`p= stubs(:'a) data_conf ++B`>>
 pairarg_tac>>fs[]>>
 Q.SPECL_THEN [`wc`,`p`,`ac`] mp_tac (GEN_ALL word_to_wordProofTheory.compile_to_word_conventions)>>
 impl_tac >-
  (fs[Abbr‘p’]>>
   irule_at Any EVERY_MONOTONIC>>
   qexists ‘λx. no_share_inst (SND $ SND x)’>>simp[FORALL_PROD]>>
   irule_at Any stubs_no_share_inst>>
   fs[EVERY_MAP,LAMBDA_PROD]>>
   simp[compile_part_def]>>
   simp[EVERY_MEM]>>rw[]>>
   pairarg_tac>>fs[]>>irule OR_INTRO_THM1>>
   irule comp_no_share_inst>>metis_tac[PAIR])>>
 rw[]>>fs[EVERY_MEM,LAMBDA_PROD,FORALL_PROD]>>rw[]>>
 res_tac>>fs[]>>
 first_assum irule>>
 simp[Abbr`p`]>>(rw[]
 >-
   (pop_assum mp_tac>>
   qpat_x_assum`data_conf.has_longdiv ⇒ P` mp_tac>>
   qpat_x_assum`data_conf.has_div⇒ P` mp_tac>>
   qpat_x_assum`∀w. _ ==> byte_offset_ok _ _ ` mp_tac>>
   qpat_x_assum`addr_offset_ok _ _` mp_tac>>
   qpat_x_assum`good_dimindex _` mp_tac>>
   rpt(pop_assum kall_tac)>>
   fs[stubs_def,generated_bignum_stubs_eq]>>rw[]>>
   TRY(rename1`ByteCopySub_code`>>
   fs[good_dimindex_def,ByteCopySub_code_def,every_inst_def,list_Seq_def,inst_ok_less_def]>>rw[]>>
   fs[]>>
   first_assum match_mp_tac>>
   metis_tac[bounds_lem])>>
   EVAL_TAC>>rw[]>>
   fs[good_dimindex_def] \\ fs[] \\ EVAL_TAC \\ fs[dimword_def] >>
   rw[] >> EVAL_TAC >> simp[]>>
   pairarg_tac \\ fs[]>>
   qmatch_goalsub_abbrev_tac `min ≤ ww ∧ ww ≤ max`>>
   first_x_assum(qspecl_then[`ww`] mp_tac)>>simp[Abbr`ww`]>>
   impl_tac>>simp[asmTheory.offset_ok_def]>>
   metis_tac[bounds_lem])
 >-
   (fs[MEM_MAP]>>PairCases_on`y`>>fs[compile_part_def]>>
   match_mp_tac comp_no_inst>>fs[]>>
   first_x_assum match_mp_tac>>
   fs[good_dimindex_def]>>
   metis_tac[bounds_lem])
 >>

   first_x_assum irule >>
   fs[WORD_LE,miscTheory.good_dimindex_def,word_2comp_n2w,
     dimword_def,word_msb_n2w])
QED

Theorem data_to_word_names:
   word_to_word$compile c1 c2 (stubs(:α)c.data_conf ++ MAP (compile_part c3) prog) = (col,p) ==>
    MAP FST p = (MAP FST (stubs(:α)c.data_conf))++MAP FST prog
Proof
  rw[]>>assume_tac(GEN_ALL word_to_wordProofTheory.compile_to_word_conventions)>>
  pop_assum (qspecl_then [`c1`,`stubs(:α)c.data_conf++(MAP (compile_part c3) prog)`,`c2`] mp_tac)>>impl_tac
  >- (irule_at Any EVERY_MONOTONIC>>
      qexists ‘λx. no_share_inst (SND $ SND x)’>>simp[FORALL_PROD]>>
      irule_at Any stubs_no_share_inst>>
      fs[EVERY_MAP,LAMBDA_PROD]>>
      simp[compile_part_def]>>
      simp[EVERY_MEM]>>rw[]>>
      pairarg_tac>>fs[]>>
      irule comp_no_share_inst>>metis_tac[PAIR])>>
  rfs[]>>
  fs[MAP_MAP_o,MAP_EQ_f,FORALL_PROD,data_to_wordTheory.compile_part_def]
QED

Theorem ALL_DISTINCT_MAP_FST_stubs:
   ALL_DISTINCT (MAP FST (data_to_word$stubs a c))
Proof
  Cases_on`a` \\ EVAL_TAC
QED

Theorem MAP_FST_stubs_bound:
   MEM n (MAP FST (data_to_word$stubs a c)) ⇒ n < data_num_stubs
Proof
  Cases_on`a` \\ EVAL_TAC
  \\ strip_tac \\ rveq \\ EVAL_TAC
QED

Theorem max_heap_limit_has_fp_ops[simp]:
   max_heap_limit (:α) (conf with has_fp_ops := b) =
    max_heap_limit (:α) conf
Proof
  EVAL_TAC
QED

Theorem FST_compile_part[simp]:
   FST (compile_part a b) = (FST b)
Proof
  PairCases_on`b` \\ EVAL_TAC
QED

Overload data_get_code_labels = ``dataProps$get_code_labels``
Overload data_good_code_labels = ``dataProps$good_code_labels``

Triviality word_get_code_labels_StoreEach:
  ∀ls off.
  word_get_code_labels (StoreEach v ls off) = {}
Proof
  Induct>>fs[StoreEach_def]
QED

Triviality word_get_code_labels_MemEqList:
  ∀x b.
  word_get_code_labels (MemEqList b x) = {}
Proof
  Induct>>fs[MemEqList_def]
QED

Triviality part_to_words_isWord:
  ∀h c m i w ws.
    part_to_words c m h i = SOME (w,ws) ∧
    (∀n v. sptree$lookup n m = SOME v ⇒ isWord (SND v)) ⇒
    EVERY isWord (MAP SND ws) ∧ isWord (SND w)
Proof
  Cases_on ‘h’ \\ fs [part_to_words_def] \\ rw []
  \\ fs [wordSemTheory.isWord_def]
  \\ EVERY_CASE_TAC \\ gvs [wordSemTheory.isWord_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ EVERY_CASE_TAC \\ gvs [wordSemTheory.isWord_def]
  \\ gvs [encode_header_def,make_ptr_def]
  \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS,wordSemTheory.isWord_def,lookup_mem_def]
  \\ rw [] \\ EVERY_CASE_TAC \\ gvs [wordSemTheory.isWord_def]
  \\ res_tac \\ fs []
QED

Triviality parts_to_words_isWord:
  ∀ps c w ws m n i.
    parts_to_words c m n ps i = SOME (w,ws) ∧
    (∀n v. sptree$lookup n m = SOME v ⇒ isWord (SND v)) ⇒
    EVERY isWord (MAP SND ws) ∧ isWord (SND w)
Proof
  Induct
  \\ fs [parts_to_words_def,lookup_mem_def]
  \\ rw [] \\ EVERY_CASE_TAC \\ gvs [wordSemTheory.isWord_def]
  \\ res_tac \\ fs []
  \\ drule_all part_to_words_isWord
  \\ fs [lookup_insert]
  \\ metis_tac [SOME_11]
QED

Theorem const_parts_to_words_isWord:
  ∀c ps w ws.
    const_parts_to_words c ps = SOME (w,ws) ⇒
    EVERY isWord (MAP SND ws) ∧ isWord (SND w)
Proof
  fs [const_parts_to_words_def]
  \\ rpt gen_tac \\ strip_tac
  \\ drule parts_to_words_isWord
  \\ fs [lookup_def]
QED

Theorem word_get_code_labels_StoreAnyConsts[local]:
  const_parts_to_words c ps = SOME (w,ws) ⇒
  word_get_code_labels (StoreAnyConsts r1 r2 r3 ws w) = EMPTY
Proof
  strip_tac
  \\ drule const_parts_to_words_isWord
  \\ EVERY (rev (map qid_spec_tac [‘r1’,‘r2’,‘r3’,‘ws’,‘w’]))
  \\ ho_match_mp_tac StoreAnyConsts_ind \\ rw []
  \\ fs [StoreAnyConsts_def]
  \\ every_case_tac \\ fs [wordSemTheory.isWord_def]
  \\ pairarg_tac \\ fs []
  \\ gvs []
  \\ imp_res_tac getWords_thm
  \\ ‘EVERY isWord (MAP SND (r1'::ws'))’ by fs [wordSemTheory.isWord_def]
  \\ pop_assum mp_tac
  \\ asm_rewrite_tac [EVERY_APPEND,MAP_APPEND]
  \\ rw [] \\ gvs []
QED

Triviality getWords_good_loc:
  ∀xs ys ws vs1 s.
    getWords xs ys = (ws,vs1) ∧
    EVERY (good_loc s ∘ SND) xs ⇒
    EVERY (good_loc s ∘ SND) vs1
Proof
  Induct \\ fs [getWords_def] \\ rw []
  \\ gvs [AllCaseEqs(),good_loc_def]
  \\ res_tac \\ fs []
QED

Theorem const_parts_to_words_labels:
  const_parts_to_words c bs = SOME (q,r) ⇒
  word_get_code_labels (StoreAnyConsts (adjust_var w) 1 3 r q) ⊆
  closLang$assign_get_code_label (BlockOp (Build bs))
Proof
  rw [] \\ drule word_get_code_labels_StoreAnyConsts \\ fs []
QED

(* slow... *)
Theorem word_get_code_labels_assign[local]:
  ∀x.
    word_get_code_labels (FST (assign c secn v w x y z)) SUBSET
    closLang$assign_get_code_label x ∪ (set(MAP FST (stubs (:α) c)))
Proof
  ho_match_mp_tac (closLangTheory.assign_get_code_label_ind)>>
  rw[assign_def,all_assign_defs,arg1_def,arg2_def,arg3_def,arg4_def,
     closLangTheory.assign_get_code_label_def]>>
  fs[list_Seq_def,word_get_code_labels_StoreEach,word_get_code_labels_MemEqList]>>
  ntac 3 (every_case_tac>>fs[] >>
  TRY (irule SUBSET_TRANS >>
       drule_then (irule_at Any) const_parts_to_words_labels) >>
  fs[list_Seq_def,word_get_code_labels_StoreEach,word_get_code_labels_MemEqList,
     closLangTheory.assign_get_code_label_def]>>
  EVAL_TAC)
QED

Theorem data_to_word_comp_code_labels[local]:
  ∀c secn l p.
  word_get_code_labels ((FST (comp c secn l p)):'a wordLang$prog) SUBSET
  data_get_code_labels p ∪ set(MAP FST (stubs (:α) c))
Proof
  ho_match_mp_tac comp_ind>>
  rw[]>>Cases_on`p`>>fs[]>>
  simp[Once comp_def]>>
  rpt(pairarg_tac>>fs[])
  >- (
    every_case_tac>>fs[]>>
    rpt(pairarg_tac>>fs[])>>
    fs[SUBSET_DEF]>>fs[]>>
    metis_tac[])
  >-
    fs[word_get_code_labels_assign]
  >-
    (fs[SUBSET_DEF]>>metis_tac[])
  >-
    (fs[SUBSET_DEF]>>metis_tac[])
  >~ [‘force_thunk’] >- (
    gvs [force_thunk_def]
    \\ every_case_tac \\ gvs [GiveUp_def, SUBSET_DEF]
    \\ EVAL_TAC \\ rpt strip_tac \\ disj1_tac \\ gvs []) >>
  EVAL_TAC>>rw[]>>fs[]
QED

Triviality word_good_handlers_StoreEach:
  ∀ls off.
  word_good_handlers secn (StoreEach v ls off)
Proof
  Induct>>fs[StoreEach_def]
QED

Triviality word_good_handlers_MemEqList:
  ∀x b.
  word_good_handlers secn (MemEqList b x)
Proof
  Induct>>fs[MemEqList_def]
QED

Theorem word_good_handlers_StoreAnyConsts[local]:
  ∀r1 r2 r3 ws w. word_good_handlers secn (StoreAnyConsts r1 r2 r3 ws w)
Proof
  ho_match_mp_tac StoreAnyConsts_ind \\ rw []
  \\ fs [StoreAnyConsts_def] \\ every_case_tac
  \\ fs [list_Seq_def] \\ rpt (pairarg_tac \\ fs [])
QED

(* slow... *)
Theorem word_good_handlers_assign[local]:
  ∀x.
    word_good_handlers secn (FST (assign c secn v w x y z))
Proof
  ho_match_mp_tac (closLangTheory.assign_get_code_label_ind)>>
  rw[assign_def,all_assign_defs,arg1_def,arg2_def,arg3_def,arg4_def]>>
  rpt(
  every_case_tac>>fs[list_Seq_def,word_good_handlers_StoreEach,
                     word_good_handlers_StoreAnyConsts,word_good_handlers_MemEqList]>>
  rw[]>>EVAL_TAC)
QED

Triviality data_to_word_comp_good_handlers:
  ∀c secn l p.
  word_good_handlers secn ((FST (comp c secn l p)):'a wordLang$prog)
Proof
  ho_match_mp_tac comp_ind>>
  rw[]>>Cases_on`p`>>fs[]>>
  simp[Once comp_def]>>
  rpt(pairarg_tac>>fs[])
  >- (
    every_case_tac>>fs[]>>
    rpt(pairarg_tac>>fs[])>>
    fs[SUBSET_DEF]>>fs[]>>
    metis_tac[])
  >-
    fs[word_good_handlers_assign]
  >~ [‘force_thunk’] >- (
    gvs [force_thunk_def]
    \\ every_case_tac \\ gvs [GiveUp_def]
    \\ EVAL_TAC)
  >>
    EVAL_TAC>>rw[]>>fs[]
QED

Triviality stubs_labels:
  BIGUNION (set (MAP (λ(n,m,pp). word_get_code_labels pp)  (stubs (:'a) dc)))
  ⊆ set (MAP FST (stubs (:'a) dc))
Proof
  rpt(EVAL_TAC>>
  IF_CASES_TAC>>
  simp[])
QED

Theorem data_to_word_good_code_labels:
  (data_to_word$compile data_conf word_conf asm_conf prog) = (xx,prog') ∧
  data_good_code_labels prog elabs ⇒
  word_good_code_labels prog' elabs
Proof
  fs[data_to_wordTheory.compile_def]>>rw[]>>
  qmatch_asmsub_abbrev_tac` stubs _ dc`>>
  pop_assum kall_tac>>
  qmatch_asmsub_abbrev_tac`LHS = _`>>
  `prog' = SND LHS` by (unabbrev_all_tac>>fs[])>>
  pop_assum SUBST_ALL_TAC>>
  fs[Abbr`LHS`]>>
  match_mp_tac word_good_code_labels_word_to_word>>
  fs[wordConvsTheory.good_code_labels_def,dataPropsTheory.good_code_labels_def]>>rw[]
  >-
    (EVAL_TAC>>rw[])
  >-
    (simp[EVERY_MAP,LAMBDA_PROD,compile_part_def,data_to_word_comp_good_handlers]>>
    fs[EVERY_MEM,FORALL_PROD])
  >-
    (assume_tac stubs_labels>>
    match_mp_tac SUBSET_TRANS>>
    asm_exists_tac>>fs[]>>
    metis_tac[SUBSET_TRANS,SUBSET_UNION])
  >>
    fs[MAP_MAP_o,o_DEF,LAMBDA_PROD,compile_part_def]>>
    fs[SUBSET_DEF,PULL_EXISTS,Once MEM_MAP,FORALL_PROD]>>
    rw[]>>
    old_drule (data_to_word_comp_code_labels |> SIMP_RULE std_ss [SUBSET_DEF])>>
    rw[]
    >-
      (first_x_assum old_drule>>
      disch_then old_drule>>fs[MEM_MAP,EXISTS_PROD]>>
      metis_tac[])
    >>
      fs[MEM_MAP]>>metis_tac[]
QED

val th = EVAL``MAP FST (stubs (:'a) c)``;

(* TODO: move somewhere better *)
Definition stubs_fst_def:
  stubs_fst = ^(rconc th)
End

Theorem stubs_fst_eq =
  th |> REWRITE_RULE [GSYM stubs_fst_def]

(* The incremental version ONLY does data_to_word
  TODO: MAP FST stubs is independent of the data conf,
  not sure if generality is needed
*)
Theorem data_to_word_good_code_labels_incr:
  set stubs_fst ⊆ elabs ∧
  data_good_code_labels progs elabs ⇒
  word_good_code_labels (MAP (compile_part dc) progs) elabs
Proof
  fs[wordConvsTheory.good_code_labels_def,dataPropsTheory.good_code_labels_def]>>rw[]
  >-
    (simp[EVERY_MAP,LAMBDA_PROD,compile_part_def,data_to_word_comp_good_handlers]>>
    fs[EVERY_MEM,FORALL_PROD])
  >>
  fs[SUBSET_DEF,PULL_EXISTS,FORALL_PROD,MEM_MAP]>>
  rw[]>>
  fs[EXISTS_PROD,compile_part_def]>>
  drule (data_to_word_comp_code_labels |> SIMP_RULE std_ss [SUBSET_DEF])>>
  rw[]
  >-
    metis_tac[]
  >>
    fs[stubs_fst_eq]
QED;

Theorem data_to_word_good_handlers:
  (data_to_word$compile data_conf word_conf asm_conf prog) = (xx,prog') ⇒
  EVERY (λ(n,m,pp). good_handlers n pp) prog'
Proof
  fs[data_to_wordTheory.compile_def]>>
  rw[]>>
  qmatch_asmsub_abbrev_tac` stubs _ dc`>>
  pop_assum kall_tac>>
  qmatch_asmsub_abbrev_tac`LHS = _`>>
  `prog' = SND LHS` by (unabbrev_all_tac>>fs[])>>
  pop_assum SUBST_ALL_TAC>>
  fs[Abbr`LHS`]>>
  match_mp_tac word_good_handlers_word_to_word>>
  fs[wordConvsTheory.good_code_labels_def,dataPropsTheory.good_code_labels_def]>>rw[]
  >-
    (EVAL_TAC>>rw[])
  >-
    (simp[EVERY_MAP,LAMBDA_PROD,compile_part_def,data_to_word_comp_good_handlers]>>
    fs[EVERY_MEM,FORALL_PROD])
QED

Theorem data_to_word_good_handlers_incr:
  EVERY (λ(n,m,pp). good_handlers n pp) (MAP (compile_part dc) progs)
Proof
  simp[EVERY_MAP,LAMBDA_PROD,compile_part_def,data_to_word_comp_good_handlers]>>
  fs[EVERY_MEM,FORALL_PROD]
QED
