(*
  Part of the correctness proof for data_to_word: assign for ThunkOp
*)
Theory data_to_word_assign_thunkProof
Libs
  preamble helperLib blastLib
Ancestors
  wordSem
  backend_common (* for word_add_carry *)
  data_to_word_memoryProof data_to_word_gcProof dataSem
  wordSem[qualified] data_to_word int_bitwise dataProps
  wordProps While set_sep
  semanticsProps alignment backendProps word_bignum wordLang
  word_bignumProof gc_shared word_gcFunctions word_simpProof wordConvs
  data_to_word_assign_commonProof

val assign_thm_goal = concl assign_goal;

val _ = augment_srw_ss [rewrites [CONJUNCT2 data_to_wordTheory.arch_size]];

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]
val _ = temp_delsimps ["DIV_NUMERAL_THM"]
val _ = temp_delsimps ["fromAList_def", "domain_union",
                       "domain_inter", "domain_difference",
                       "domain_map", "sptree.map_def", "sptree.lookup_rwts",
                       "sptree.insert_notEmpty", "sptree.isEmpty_union"]
val _ = diminish_srw_ss ["ABBREV"]

val _ = augment_srw_ss [rewrites [integer_wordTheory.i2w_pos,
                                  integer_wordTheory.i2w_w2i, i2w_neg, i2w_sub1,
    data_to_word_memoryProofTheory.compiler_all_ones_i2w,
  data_to_wordTheory.get_lowerbits_def,data_to_wordTheory.make_ptr_def,
  data_to_wordTheory.make_cons_ptr_def]]

val _ = numLib.prefer_num ();

fun drule0 th =
  first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))

val _ = hide "next";
val _ = hide "el";
val make_ptr_def = data_to_word_memoryProofTheory.make_ptr_def;
Overload lookup[local] = “sptree$lookup”;

val assign_def =
  data_to_wordTheory.assign_def
  |> REWRITE_RULE [arg1_def, arg2_def, arg3_def, arg4_def, all_assign_defs];

val clean_tac = rpt var_eq_tac \\ rpt (qpat_x_assum `T` kall_tac);
fun rpt_drule0 th = drule0 (th |> GEN_ALL) \\ rpt (disch_then drule0 \\ fs []);

val state_rel_def = data_to_word_gcProofTheory.state_rel_def;
val do_app = LIST_CONJ [do_app_def,do_app_aux_def,do_space_def,
  data_spaceTheory.op_space_req_def,
  dataLangTheory.op_space_reset_def,
  do_stack_def,stack_consumed_def];

val eval_tac = fs [wordSemTheory.evaluate_def,
  wordSemTheory.word_exp_def, wordSemTheory.set_var_def, set_var_def,
  wordSemTheory.get_store_def,
  wordSemTheory.get_var_def,
  wordSemTheory.the_words_def, wordSemTheory.mem_load_def,
  wordSemTheory.word_op_def, wordSemTheory.word_sh_def];

Theorem reorder_2_lemma:
  memory_rel c be ts x.refs x.space t.store t.memory t.mdomain (x1::x2::xs) ==>
  memory_rel c be ts x.refs x.space t.store t.memory t.mdomain (x2::x1::xs)
Proof
  match_mp_tac memory_rel_rearrange \\ fs [] \\ rw [] \\ fs []
QED

val _ = augment_srw_ss [rewrites [arch_bytes_word]];
val eval_tac = imp_res_tac state_rel_arch_width
  \\ imp_res_tac memory_rel_arch_width \\ eval_tac
  \\ fs [GSYM word_mul_n2w];

val _=augment_srw_ss[rewrites[i2w_int_or,i2w_mod_pow2,compiler_ptr_bits_i2w]];

val _ = augment_srw_ss [rewrites [arch_width_eq32, arch_bytes_scaled_word]];

Theorem do_app_AllocThunk:
   do_app (ThunkOp (AllocThunk m)) [v] x =
    case consume_space (1 + 1) x of
      NONE => Rerr (Rabort Rtype_error)
    | SOME s1 =>
      if bad_thunk_update m v s1.refs then Rerr (Rabort Rtype_error) else
      Rval
      (RefPtr F (LEAST ptr. ptr ∉ domain s1.refs),
         s1 with <|
           refs := insert (LEAST ptr. ptr ∉ domain s1.refs) (Thunk m v) s1.refs;
           safe_for_space := (
             do_stack
               (ThunkOp (AllocThunk m)) [v]
               (do_lim_safe s1 (ThunkOp (AllocThunk m)) [v])).safe_for_space;
           stack_max := (
             do_stack
               (ThunkOp (AllocThunk m)) [v]
               (do_lim_safe s1 (ThunkOp (AllocThunk m)) [v])).stack_max |>)
Proof
  gvs [do_app, consume_space_def]
QED

Theorem assign_AllocThunk:
  (∃ev. op = ThunkOp (AllocThunk ev)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ asm_rewrite_tac [] \\ pop_assum kall_tac
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t NONE locs` kall_tac \\ strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  \\ fs [assign_def] \\ fs [do_app_AllocThunk] \\ fs[do_app]
  \\ namedCases_on `consume_space (LENGTH vals + 1) s` ["", "s1"] \\ fs [] \\ rveq
  \\ Cases_on `vals` \\ gvs []
  \\ Cases_on `t'` \\ gvs []
  \\ Cases_on `bad_thunk_update ev h s1.refs` \\ gvs []
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ clean_tac
  \\ fs [consume_space_def] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ Cases_on `ws` \\ gvs []
  \\ Cases_on `args` \\ gvs []
  \\ simp [allowed_op_def]
  \\ TOP_CASE_TAC \\ fs []
  >- (
    conj_tac
    >- (
      fs [state_rel_def]
      \\ rw [option_le_max_right]
      \\ metis_tac[option_le_trans])
    \\ fs[encode_header_def]
    \\ fs[encode_header_def, state_rel_def, good_dimindex_def, limits_inv_def,
          dimword_def, memory_rel_def, heap_in_memory_store_def,
          consume_space_def, arch_size_def]
    \\ rfs[NOT_LESS]
    \\ Cases_on `ev` \\ gvs [])
  \\ simp [state_rel_thm] \\ eval_tac
  \\ fs [state_rel_thm] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs [NOT_LESS,DECIDE ``n + 1 <= m <=> n < m:num``]
  \\ strip_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ qabbrev_tac `new = LEAST ptr. ptr ∉ domain s.refs`
  \\ `new ∉ domain s.refs` by metis_tac [LEAST_NOTIN_spt_DOMAIN]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 memory_rel_AllocThunk
  \\ impl_tac >- gvs [bad_thunk_update_def]
  \\ strip_tac
  \\ `shift_length c - shift (dimindex (:'a)) < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword \\
        `shift_length c < dimindex (:'a)` suffices_by decide_tac \\
        fs [state_rel_thm,memory_rel_def,heap_in_memory_store_def])
  \\ fs [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.set_store_def,FLOOKUP_UPDATE]
  \\ qpat_abbrev_tac `t5 = t with <| locals := _ ; store := _ |>`
  \\ pairarg_tac \\ fs []
  \\ `t.memory = t5.memory /\ t.mdomain = t5.mdomain` by
       (unabbrev_all_tac \\ fs []) \\ fs []
  \\ ntac 2 (pop_assum kall_tac)
  \\ drule0 evaluate_StoreEach
  \\ disch_then (qspecl_then [`[3; adjust_var h'']`,`1`,`c`] mp_tac)
  \\ impl_tac
  >- (
    unabbrev_all_tac
    \\ gvs [wordSemTheory.get_vars_def, wordSemTheory.get_var_def,
            lookup_insert])
  \\ clean_tac \\ fs [] \\ UNABBREV_ALL_TAC
  \\ fs [lookup_insert,FAPPLY_FUPDATE_THM,adjust_var_11,FLOOKUP_UPDATE,
         code_oracle_rel_def,FLOOKUP_UPDATE]
  \\ rpt (qpat_x_assum `!x y z. _` kall_tac)
  \\ rw [] \\ fs [] \\ rw [] \\ fs []
  \\ fs [inter_insert_ODD_adjust_set]
  >- (rw[option_le_max_right] >> metis_tac[option_le_trans])
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ fs [make_ptr_def]
  \\ `TriggerGC <> EndOfHeap` by fs []
  \\ pop_assum (fn th => fs [MATCH_MP FUPDATE_COMMUTES th])
QED

Theorem assign_UpdateThunk:
  (∃ev. op = ThunkOp (UpdateThunk ev)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t NONE locs` kall_tac \\ strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  \\ gvs [do_app,allowed_op_def,AllCaseEqs()]
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [bvlSemTheory.Unit_def] \\ rveq
  \\ fs [GSYM bvlSemTheory.Unit_def] \\ rveq
  \\ fs [assign_def] \\ eval_tac \\ fs [state_rel_thm]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs []
  \\ Cases_on `args` \\ gvs []
  \\ Cases_on `t'` \\ gvs []
  \\ Cases_on `t''` \\ gvs []
  \\ Cases_on `ws` \\ gvs []
  \\ Cases_on `t'` \\ gvs []
  \\ imp_res_tac get_vars_2_IMP \\ fs []
  \\ strip_tac
  \\ drule0 reorder_2_lemma \\ strip_tac
  \\ reverse $ Cases_on `ev` \\ gvs []
  >- (
    drule0 (memory_rel_UpdateThunk_NotEvaluated |> GEN_ALL) \\ fs []
    \\ strip_tac \\ clean_tac
    \\ imp_res_tac get_real_addr_lemma
    \\ fs [] \\ eval_tac \\ fs [EVAL ``word_exp s1 Unit``]
    \\ fs [wordSemTheory.mem_store_def]
    \\ fs [lookup_insert,adjust_var_11]
    \\ rw [] \\ fs [option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ match_mp_tac memory_rel_Unit \\ fs []
    \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
    \\ rw [] \\ gvs [])
  \\ TOP_CASE_TAC \\ gvs []
  >- (
    fs[encode_header_def]
    \\ fs[encode_header_def, state_rel_def, good_dimindex_def, limits_inv_def,
          dimword_def, memory_rel_def, heap_in_memory_store_def,
          consume_space_def, arch_size_def]
    \\ rfs[NOT_LESS])
  \\ drule0 (memory_rel_UpdateThunk_Evaluated |> GEN_ALL) \\ fs []
  \\ impl_tac >- gvs [bad_thunk_update_def]
  \\ strip_tac \\ clean_tac
  \\ imp_res_tac get_real_addr_lemma
  \\ fs [list_Seq_def] \\ eval_tac \\ fs [EVAL ``word_exp s1 Unit``]
  \\ fs [wordSemTheory.mem_store_def]
  \\ fs [lookup_insert,adjust_var_11]
  \\ rw []
  >- simp [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ match_mp_tac memory_rel_Unit \\ fs [UPDATE_LIST_THM]
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
  \\ rw [] \\ gvs []
  \\ ntac 2 disj2_tac \\ ntac 2 disj1_tac \\ gvs []
  \\ gvs [join_env_def, MEM_MAP, MEM_FILTER]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ qexists `(n,v)` \\ gvs []
  \\ gvs [MEM_toAList,lookup_inter_alt,lookup_insert,AllCaseEqs()]
QED

Theorem join_lemma[local] =
  METIS_PROVE [] “(b1 ⇒ x) ∧ (b2 ⇒ x) ⇒ (b1 ∨ b2 ⇒ x)”;

Theorem imp_assign[local] =
  DB.match ["-"] “_ ==> ^assign_thm_goal” |> map (#1 o #2)
  |> end_itlist (fn x => fn y => MATCH_MP join_lemma (CONJ x y));

Theorem assign_ThunkOp:
  (∃th. op = ThunkOp th) ⇒ ^assign_thm_goal
Proof
  strip_tac \\ strip_tac
  \\ irule imp_assign
  \\ asm_rewrite_tac []
  \\ rpt $ first_assum $ irule_at Any
  \\ gvs [] \\ Cases_on ‘th’ \\ gvs []
  \\ qhdtm_x_assum`do_app`mp_tac \\ EVAL_TAC
QED

