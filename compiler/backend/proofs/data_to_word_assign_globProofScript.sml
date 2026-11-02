(*
  Part of the correctness proof for data_to_word: assign for GlobOp
*)
Theory data_to_word_assign_globProof
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
Overload lookup[local] = “sptree$lookup”;

val assign_def =
  data_to_wordTheory.assign_def
  |> REWRITE_RULE [arg1_def, arg2_def, arg3_def, arg4_def, all_assign_defs];

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

val _ = augment_srw_ss [rewrites [arch_bytes_word]];
val eval_tac = imp_res_tac state_rel_arch_width
  \\ imp_res_tac memory_rel_arch_width \\ eval_tac
  \\ fs [GSYM word_mul_n2w];

val _=augment_srw_ss[rewrites[i2w_int_or,i2w_mod_pow2,compiler_ptr_bits_i2w]];

val _ = augment_srw_ss [rewrites [arch_width_eq32, arch_bytes_scaled_word]];

val _ = augment_srw_ss [rewrites [compiler_tag_mask_i2w]];

val _ = augment_srw_ss [rewrites [compiler_Smallnum_i2w]];

Theorem arch_bytes_offset[local]:

 arch_width_bits c.arch_width = dimindex(:'a) ==>
 (a + n2w(arch_bytes c.arch_width * (n+1)) + p:'a word) =
 a + p + bytes_in_word + bytes_in_word * n2w n
Proof
 strip_tac >> rewrite_tac [GSYM word_mul_n2w] >> simp [] >>
 rewrite_tac [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB] >>
 CONV_TAC wordsLib.WORD_ARITH_CONV
QED

Theorem assign_GlobalsPtr:
  op = GlobOp GlobalsPtr ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ imp_res_tac state_rel_arch_width
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ gvs [do_app,AllCaseEqs(),allowed_op_def]
  \\ fs [assign_def,eq_eval,wordSemTheory.get_store_def]
  \\ fs [state_rel_thm,set_var_def]
  \\ fs [the_global_def,miscTheory.the_def,FLOOKUP_DEF]
  \\ fs [FLOOKUP_DEF,wordSemTheory.set_var_def,lookup_insert,
         adjust_var_11,miscTheory.the_def,set_var_def]
  \\ conj_tac >- rw []
  \\ conj_tac >- fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ qpat_x_assum ‘_ t.mdomain _’ mp_tac
  \\ match_mp_tac memory_rel_rearrange
  \\ fs [] \\ rw [] \\ fs [the_def]
QED

Theorem assign_Global:
  (∃n. op = GlobOp (Global n)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ imp_res_tac state_rel_arch_width
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ gvs [do_app,AllCaseEqs(),allowed_op_def]
  \\ fs [assign_def,eq_eval,wordSemTheory.get_store_def]
  \\ ‘∃curr.
        FLOOKUP t.store CurrHeap = SOME (Word curr) ∧
        glob_real_inv c curr (FLOOKUP t.store Globals) (FLOOKUP t.store GlobReal)’
          by fs [memory_rel_def,heap_in_memory_store_def,state_rel_def]
  \\ fs [glob_real_inv_def]
  \\ fs [state_rel_thm,option_le_max_right,set_var_def]
  \\ gvs [the_global_def,miscTheory.the_def]
  \\ qmatch_asmsub_abbrev_tac ‘(xs1 ++ [(RefPtr T ptr,t.store ' Globals)] ++ xs2)’
  \\ ‘memory_rel c t.be (THE s.tstamps) s.refs s.space t.store t.memory
          t.mdomain ((RefPtr T ptr,t.store ' Globals) :: (xs1 ++ xs2))’ by
      (first_x_assum (fn th => mp_tac th \\ match_mp_tac memory_rel_rearrange)
       \\ fs [] \\ rw [] \\ fs [])
  \\ drule0 (memory_rel_Deref' |> GEN_ALL) \\ fs []
  \\ disch_then drule \\ strip_tac \\ fs []
  \\ drule memory_rel_RefPtr_T_IMP \\ fs [] \\ strip_tac
  \\ gvs [get_real_simple_addr_def]
  \\ gvs[arch_bytes_offset,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ gvs [FLOOKUP_DEF]
  \\ fs [lookup_insert,adjust_var_11]
  \\ rw [] \\ fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ TRY (fs [lookup_insert,adjust_var_def] \\ NO_TAC)
  \\ TRY (rw [lookup_insert] \\ gvs [adjust_var_def] \\ first_x_assum irule \\ fs [] \\ NO_TAC)
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac memory_rel_rearrange)
  \\ fs [] \\ rw [] \\ fs []
QED

Theorem assign_SetGlobal:
  (∃n. op = GlobOp (SetGlobal n)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ imp_res_tac state_rel_arch_width
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ gvs [do_app,AllCaseEqs(),allowed_op_def]
  \\ fs [assign_def,eq_eval,wordSemTheory.get_store_def]
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ fs [state_rel_thm]
  \\ rfs [the_global_def,miscTheory.the_def]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs []
  \\ qmatch_goalsub_abbrev_tac ‘(x1,x2)::(xs1++[(RefPtr T ref_ptr,_)]++xs2)’
  \\ strip_tac
  \\ ‘memory_rel c t.be (THE s.tstamps) s.refs s.space t.store t.memory t.mdomain
        ((RefPtr T ref_ptr,t.store ' Globals)::(x1,x2)::(xs1 ++ xs2))’ by
      (first_x_assum (fn th => mp_tac th \\ match_mp_tac memory_rel_rearrange)
       \\ fs [] \\ rw [] \\ fs [])
  \\ ‘∃curr.
        FLOOKUP t.store CurrHeap = SOME (Word curr) ∧
        glob_real_inv c curr (FLOOKUP t.store Globals) (FLOOKUP t.store GlobReal)’
          by fs [memory_rel_def,heap_in_memory_store_def,state_rel_def]
  \\ drule memory_rel_RefPtr_T_IMP \\ fs [] \\ strip_tac
  \\ fs [glob_real_inv_def,set_var_def]
  \\ fs [wordSemTheory.get_vars_def,AllCaseEqs()]
  \\ ‘memory_rel c t.be (THE s.tstamps) s.refs s.space t.store t.memory t.mdomain
        ((x1,x2)::(RefPtr T ref_ptr,t.store ' Globals)::(xs1 ++ xs2))’ by
      (first_x_assum (fn th => mp_tac th \\ match_mp_tac memory_rel_rearrange)
       \\ fs [] \\ rw [] \\ fs [])
  \\ drule0 (memory_rel_Update' |> GEN_ALL) \\ fs []
  \\ disch_then drule \\ strip_tac
  \\ fs [] \\ gvs[get_real_simple_addr_def,eq_eval,wordSemTheory.get_store_def]
  \\ gvs[arch_bytes_offset,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,wordSemTheory.mem_store_def,
         wordSemTheory.get_var_def]
  \\ gvs [FLOOKUP_DEF,wordSemTheory.word_exp_def,data_to_wordTheory.Unit_def]
  \\ fs [lookup_insert,adjust_var_11]
  \\ rw [] \\ fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ TRY (fs [lookup_insert,adjust_var_def] \\ NO_TAC)
  \\ TRY (rw [lookup_insert] \\ gvs [adjust_var_def] \\ first_x_assum irule \\ fs [] \\ NO_TAC)
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ match_mp_tac memory_rel_Unit \\ fs [the_def]
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
  \\ rw [] \\ fs []
QED

Theorem assign_SetGlobalsPtr:
  op = GlobOp SetGlobalsPtr ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ imp_res_tac state_rel_arch_width
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ gvs [do_app,AllCaseEqs(),allowed_op_def]
  \\ fs [assign_def,eq_eval,wordSemTheory.get_store_def]
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ last_x_assum mp_tac
  \\ simp [Once state_rel_thm] \\ strip_tac
  \\ rfs [the_global_def,miscTheory.the_def]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule \\ simp []
  \\ rpt strip_tac
  \\ ‘∃v. h = Word v’ by (imp_res_tac memory_rel_RefPtr_T_IMP \\ simp [])
  \\ gvs [wordSemTheory.get_vars_def,AllCaseEqs()]
  \\ rename [‘_ = SOME (Word www)’]
  \\ eval_tac \\ fs [state_rel_thm,option_le_max_right]
  \\ rename [‘(real_addr c (adjust_var y))’]
  \\ drule_all memory_rel_RefPtr_T_IMP \\ strip_tac
  \\ ‘word_exp (set_store Globals (Word www) t) (real_addr c (adjust_var y)) =
      word_exp t (real_addr c (adjust_var y))’ by
      (rw[wordSemTheory.set_store_def,wordSemTheory.word_exp_def,real_addr_def,
          wordSemTheory.get_store_def,FLOOKUP_SIMP])
  \\ first_assum (mp_then (Pos last) mp_tac get_real_addr_lemma)
  \\ gvs []
  \\ disch_then (qspec_then ‘adjust_var y’ mp_tac)
  \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def]
  \\ fs [wordSemTheory.set_store_def]
  \\ fs [state_rel_def,wordSemTheory.set_var_def,lookup_insert,
         adjust_var_11,miscTheory.the_def,set_var_def,word_sh_def,
         wordSemTheory.set_store_def,code_oracle_rel_def,FLOOKUP_UPDATE]
  \\ simp [wordSemTheory.word_exp_def,data_to_wordTheory.Unit_def,
           FLOOKUP_SIMP,lookup_insert]
  \\ rw [adjust_var_11]
  \\ rw [] \\ fs [option_le_max_right,the_global_def,FAPPLY_FUPDATE_THM]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs [the_def]
  \\ match_mp_tac memory_rel_Unit \\ simp []
  \\ qpat_x_assum ‘_ t.mdomain _’ mp_tac
  \\ simp [memory_rel_def]
  \\ strip_tac
  \\ pop_assum $ irule_at $ Pos last
  \\ pop_assum $ irule_at $ Pos last
  \\ fs [heap_in_memory_store_def,FLOOKUP_SIMP]
  \\ first_assum $ irule_at $ Pos hd \\ simp []
  \\ irule_at (Pos hd) EQ_REFL \\ simp []
  \\ irule_at (Pos hd) EQ_REFL \\ simp []
  \\ first_assum $ irule_at $ Pos $ el 2 \\ simp []
  \\ conj_tac
  >- (gvs [glob_real_inv_def] \\ gvs [get_real_simple_addr_def])
  \\ pop_assum mp_tac
  \\ match_mp_tac word_ml_inv_rearrange \\ rw [] \\ fs []
QED

Theorem join_lemma[local] =
  METIS_PROVE [] “(b1 ⇒ x) ∧ (b2 ⇒ x) ⇒ (b1 ∨ b2 ⇒ x)”;

Theorem imp_assign[local] =
  DB.match ["-"] “_ ==> ^assign_thm_goal” |> map (#1 o #2)
  |> end_itlist (fn x => fn y => MATCH_MP join_lemma (CONJ x y));

Theorem assign_GlobOp:
  (∃g. op = GlobOp g) ⇒ ^assign_thm_goal
Proof
  strip_tac \\ strip_tac
  \\ Cases_on `op = GlobOp AllocGlobal`
  >- (fs [do_app] \\ every_case_tac \\ fs [])
  \\ irule imp_assign
  \\ asm_rewrite_tac []
  \\ rpt $ first_assum $ irule_at Any
  \\ gvs [] \\ Cases_on ‘g’ \\ gvs []
QED

