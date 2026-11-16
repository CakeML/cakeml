(*
  Part of the correctness proof for data_to_word: assign for Label,
  FFI and Install
*)
Theory data_to_word_assign_miscProof
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

val assign_thm_link_goal = concl assign_link_goal;

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
val shift_def = backend_commonTheory.word_shift_def
val upper_w2w_def = wordSemTheory.upper_w2w_def
val Smallnum_def = LIST_CONJ [data_to_word_memoryProofTheory.Smallnum_def,
                             data_to_wordTheory.Smallnum_def];
Overload lookup[local] = “sptree$lookup”;

val assign_def =
  data_to_wordTheory.assign_def
  |> REWRITE_RULE [arg1_def, arg2_def, arg3_def, arg4_def, all_assign_defs];

val clean_tac = rpt var_eq_tac \\ rpt (qpat_x_assum `T` kall_tac);
fun rpt_drule0 th = drule0 (th |> GEN_ALL) \\ rpt (disch_then drule0 \\ fs []);

val state_rel_def = data_to_word_gcProofTheory.state_rel_def;
val code_rel_def = data_to_word_gcProofTheory.code_rel_def;

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

Theorem memory_rel_lookup_var_IMP:
   memory_rel c be ts refs sp st m dm
     (join_env ll
        (toAList (inter t.locals (adjust_set ll))) ++ envs) ∧
    get_vars n ll = SOME x ∧
    get_vars (MAP adjust_var n) (t:('a,'c,'ffi) wordSem$state) = SOME w ⇒
    memory_rel c be ts refs sp st m dm
      (ZIP (x,w) ++
       join_env ll
         (toAList (inter t.locals (adjust_set ll))) ++ envs)
Proof
  fs [memory_rel_def] \\ rw [] \\ asm_exists_tac \\ fs []
  \\ drule0 word_ml_inv_get_vars_IMP_lemma \\ fs []
QED

val _ = augment_srw_ss [rewrites [arch_bytes_word]];
val eval_tac = imp_res_tac state_rel_arch_width
  \\ imp_res_tac memory_rel_arch_width \\ eval_tac
  \\ fs [GSYM word_mul_n2w];

Theorem IMP_read_bytearray_GENLIST:
   ∀ls len a. len = LENGTH ls ∧
   (∀i. i < len ⇒ g (a + n2w i) = SOME (EL i ls))
  ⇒ read_bytearray a len g = SOME ls
Proof
  Induct \\ rw[read_bytearray_def] \\ fs[]
  \\ last_x_assum(qspec_then`a + 1w`mp_tac)
  \\ impl_tac
  >- (
    rw[]
    \\ first_x_assum(qspec_then`SUC i`mp_tac)
    \\ simp[]
    \\ simp[ADD1,GSYM word_add_n2w] )
  \\ rw[]
  \\ first_x_assum(qspec_then`0`mp_tac)
  \\ simp[]
QED

Theorem bytes_to_mlstring_11:
  bytes_to_mlstring bs1 = bytes_to_mlstring bs2 <=> bs1 = bs2
Proof
  rw [EQ_IMP_THM]
  \\ qpat_x_assum `bytes_to_mlstring _ = _` mp_tac
  \\ rw [backend_commonTheory.bytes_to_mlstring_def]
  \\ `explode (implode (MAP (\w. CHR (w2n w)) bs1)) =
      explode (implode (MAP (\w. CHR (w2n w)) bs2))` by fs []
  \\ full_simp_tac std_ss [mlstringTheory.explode_implode]
  \\ `!w1 w2:word8. CHR (w2n w1) = CHR (w2n w2) ==> w1 = w2` by
       (rpt strip_tac
        \\ `w2n w1 < 256 /\ w2n w2 < 256` by
             (assume_tac (Q.ISPEC `w1:word8` w2n_lt)
              \\ assume_tac (Q.ISPEC `w2:word8` w2n_lt)
              \\ fs [dimword_def])
        \\ fs [CHR_11,w2n_11])
  \\ irule (Q.ISPEC `\(w:word8). CHR (w2n w)` listTheory.INJ_MAP_EQ)
  \\ fs [pred_setTheory.INJ_DEF]
QED

Theorem evaluate_BignumHalt:
   state_rel c l1 l2 s t NONE locs /\
    get_var reg t = SOME (Word w) ==>
    ∃r. (evaluate (BignumHalt reg,t) =
          if w ' 0 then (SOME NotEnoughSpace,r)
          else (NONE,t)) ∧ r.ffi = s.ffi ∧ t.ffi = s.ffi
Proof
  fs [BignumHalt_def,wordSemTheory.evaluate_def,word_exp_rw,
      asmTheory.word_cmp_def,word_and_one_eq_0_iff |> SIMP_RULE (srw_ss()) []]
  \\ IF_CASES_TAC \\ fs []
  THEN1 (rw [] \\ qexists_tac `t` \\ fs [state_rel_def])
  \\ rw []
  \\ match_mp_tac evaluate_GiveUp \\ fs []
QED

val get_var_get_real_addr_lemma =
    GEN_ALL(CONV_RULE(LAND_CONV(move_conj_left(
                                   same_const``wordSem$get_var`` o #1 o
                                   strip_comb o lhs)))
                     get_real_addr_lemma)

Theorem MAP_Word64_11[local]:
    !ns ns'.
      MAP (Word64) ns = MAP (Word64) ns' <=>
      ns = ns'
Proof
  Induct \\ Cases_on `ns'` \\ fs []
QED

Definition w2w_upper_def:
  w2w_upper (w:word64) =
    if dimindex (:'a) = 32 then ((63 >< 32) w):'a word else w2w w
End

Theorem InstallData_code_thm:
   !(t:('a,'c,'ffi) wordSem$state) c hv2 v1 q2 a1 a2 ret_val s1 vars sp refs ts.
      memory_rel c t.be ts refs sp t.store t.memory t.mdomain
         ((hv2,a2)::vars) /\
      (?md. lookup InstallData_location t.code = SOME (4,InstallData_code c,md)) /\
      (?md. lookup Install_location t.code = SOME (3,Install_code c,md)) /\
      v_to_words hv2 = SOME q2 /\
      LENGTH q2 ≤ t.data_buffer.space_left /\
      LENGTH q2 < t.clock /\
      get_var 0 t = SOME ret_val /\
      get_var 2 t = SOME (Word (t.data_buffer.position +
                                bytes_in_word *
                                  n2w (LENGTH t.data_buffer.buffer))) /\
      get_var 4 t = SOME a2 /\
      get_var 6 t = SOME a1 /\
      good_dimindex (:'a) ==>
      ?smx lsz.
      evaluate (InstallData_code c,t) =
      case
        evaluate (Install_code c,
           t with <|
             locals := fromList2 [ret_val;
               Word (t.data_buffer.position +
                     bytes_in_word * n2w (LENGTH t.data_buffer.buffer) +
                     bytes_in_word * n2w (LENGTH q2)); a1];
             clock := t.clock - LENGTH q2 - 1;
             data_buffer := t.data_buffer with
               <| buffer := t.data_buffer.buffer ++ MAP w2w_upper q2 ;
                  space_left := t.data_buffer.space_left - LENGTH q2 |>;
             locals_size := lsz;
             stack_max := smx|>) of
      | (res,s) => if bad_fun_return res then (SOME Error, s) else (res,s)
Proof
  Induct_on `q2` \\ fs [] THEN1
   (fs [v_to_words_def]
    \\ fs [some_def] \\ rw [] \\ rfs [MAP_Word64_11]
    \\ rveq \\ fs [v_to_list_EQ_SOME_NIL] \\ rveq
    \\ fs [InstallData_code_def,list_Seq_def]
    \\ eval_tac \\ fs [wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,
         wordSemTheory.get_vars_def,wordSemTheory.get_var_def,lookup_insert]
    \\ rpt_drule0 memory_rel_Block_IMP \\ strip_tac \\ rveq \\ fs []
    \\ simp [asmTheory.word_cmp_def]
    \\ fs [wordSemTheory.bad_dest_args_def,wordSemTheory.find_code_def,
           wordSemTheory.add_ret_loc_def,wordSemTheory.dec_clock_def,
           wordSemTheory.call_env_def]
    \\ rename1 `stack_max_fupd(K smx)`
    \\ qexists_tac `smx`
    \\ rename1 `locals_size_fupd(K lsz)`
    \\ qexists_tac `lsz`
    \\ qmatch_goalsub_abbrev_tac `wordSem$evaluate (_, t1)`
    \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ qmatch_goalsub_abbrev_tac `wordSem$evaluate (_, t2)`
    \\ qsuff_tac `t1 = t2` THEN1 (rw [] \\ fs [])
    \\ unabbrev_all_tac \\ fs [wordSemTheory.state_component_equality,
         wordSemTheory.buffer_component_equality])
  \\ fs [v_to_words_def]
  \\ fs [some_def] \\ rw [] \\ rfs [MAP_Word64_11]
  \\ rveq \\ fs []
  \\ Cases_on `hv2` \\ fs [v_to_list_def]
  \\ Cases_on `l` \\ fs [v_to_list_def]
  \\ Cases_on `t'` \\ fs [v_to_list_def]
  \\ Cases_on `t''` \\ fs [v_to_list_def] \\ rveq \\ fs []
  \\ Cases_on `v_to_list h''` \\ fs [] \\ rveq \\ fs []
  \\ rename1 `v_to_list htl = _`
  \\ rpt_drule0 memory_rel_El_any
  \\ disch_then (qspec_then `0` mp_tac) \\ fs [] \\ strip_tac
  \\ rveq \\ fs []
  \\ rpt_drule0 memory_rel_Word64_IMP \\ fs []
  \\ strip_tac \\ fs []
  \\ simp [InstallData_code_def]
  \\ simp [Once wordSemTheory.evaluate_def,
           wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def]
  \\ IF_CASES_TAC THEN1
   (rpt_drule0 memory_rel_Block_IMP \\ strip_tac
    \\ fs [word_bit_test_0] \\ fs [word_bit_def])
  \\ `t.memory (x' + bytes_in_word) = Word (w2w_upper h)` by
   (fs [w2w_upper_def,good_dimindex_def] \\ rfs []
    \\ Cases_on `h` \\ fs [word_extract_def,word_bits_n2w,bitTheory.BITS_THM])
  \\ qpat_x_assum `if _ then _ else _` kall_tac
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac \\ fs []
  \\ qpat_x_assum `get_real_addr c t.store ptr_w = SOME x` assume_tac
  \\ gvs [GSYM wordSemTheory.get_var_def]
  \\ rpt_drule0 (get_var_get_real_addr_lemma |> REWRITE_RULE [CONJ_ASSOC]
       |> ONCE_REWRITE_RULE [CONJ_COMM])
  \\ disch_then (qspec_then `4` mp_tac)
  \\ impl_tac THEN1 fs [memory_rel_def,heap_in_memory_store_def]
  \\ fs [] \\ disch_then kall_tac
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac \\ fs []
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac \\ fs []
  \\ qmatch_goalsub_abbrev_tac `word_exp t99`
  \\ `get_real_addr c t99.store (get_addr c ptr (Word 0w)) = SOME x'`
        by fs [Abbr `t99`]
  \\ rpt_drule0 (get_var_get_real_addr_lemma |> REWRITE_RULE [CONJ_ASSOC]
       |> ONCE_REWRITE_RULE [CONJ_COMM])
  \\ disch_then (qspec_then `4` mp_tac) \\ fs [Abbr `t99`]
  \\ impl_tac THEN1
   (fs [wordSemTheory.get_var_def,lookup_insert]
    \\ fs [memory_rel_def,heap_in_memory_store_def])
  \\ fs [] \\ disch_then kall_tac
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac \\ fs []
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac \\ fs []
  \\ fs [wordSemTheory.get_var_def,lookup_insert]
  \\ fs [wordSemTheory.buffer_write_def,bytes_in_word_def]
  \\ fs [GSYM bytes_in_word_def]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac \\ fs [lookup_insert]
  \\ rpt_drule0 memory_rel_El_any
  \\ disch_then (qspec_then `1` mp_tac) \\ fs [] \\ strip_tac
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac \\ fs [lookup_insert]
  \\ drule memory_rel_swap \\ pop_assum kall_tac \\ strip_tac
  \\ drule memory_rel_tl \\ pop_assum kall_tac \\ strip_tac
  \\ fs [list_Seq_def,wordSemTheory.evaluate_def,wordSemTheory.get_vars_def,
         wordSemTheory.get_var_def,lookup_insert,wordSemTheory.add_ret_loc_def,
         wordSemTheory.bad_dest_args_def,wordSemTheory.find_code_def,
         wordSemTheory.dec_clock_def,wordSemTheory.call_env_def]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ qmatch_goalsub_abbrev_tac `InstallData_code c, t88`
  \\ first_x_assum (qspec_then `t88` mp_tac)
  \\ fs [Abbr`t88`,fromList2_def,lookup_insert]
  \\ disch_then drule \\ fs [GSYM word_add_n2w,MAP_Word64_11]
  \\ fs [WORD_LEFT_ADD_DISTRIB]
  \\ strip_tac
  \\ MAP_EVERY qexists_tac [`smx`,`lsz`]
  \\ fs [ADD1,GSYM word_add_n2w]
  \\ CASE_TAC \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [WORD_LEFT_ADD_DISTRIB]
  \\ CASE_TAC \\ fs []
QED

Theorem w2w_upper_upper_w2w:
   !z1. good_dimindex (:'a) ==>
         MAP w2w_upper (MAP upper_w2w z1) = z1:'a word list
Proof
  Induct \\ fs []
  \\ fs [good_dimindex_def] \\ reverse (rw [])
  \\ fs [w2w_upper_def,upper_w2w_def]
  THEN1 (Cases_on `h` \\ rfs [w2w_def,dimword_def])
  \\ fs [fcpTheory.CART_EQ,word_extract_def,w2w,word_bits_def,
         fcpTheory.FCP_BETA,word_lsl_def]
QED

Theorem MAP_FST_MAP_compile_part[local]:
    !full_list. MAP FST (MAP (compile_part c) full_list) = MAP FST full_list
Proof
  Induct \\ fs [FORALL_PROD,compile_part_def]
QED

Theorem memory_rel_ignore_buffers[local]:
    memory_rel c be ts refs sp (st |+ (BitmapBuffer,x)) m dm vars =
    memory_rel c be ts refs sp st m dm vars /\
    memory_rel c be ts refs sp (st |+ (CodeBuffer,x)) m dm vars =
    memory_rel c be ts refs sp st m dm vars
Proof
  fs [memory_rel_def,heap_in_memory_store_def,FLOOKUP_UPDATE]
QED

Theorem compile_part_loc_IMP[local]:
    compile_part c (a1,a2) = (n,x) ==> n = a1
Proof
  PairCases_on `a2` \\ fs [compile_part_def]
QED

Theorem do_app_safe_for_space_allowed_op:
  do_app op xs s = Rval(r,s1) ∧
  s1.safe_for_space ⇒
  allowed_op op (LENGTH xs)
Proof
  rw[]>>drule do_app_locals>>
  disch_then(qspec_then`s.locals` assume_tac)>>rw[]>>
  `s with locals:=s.locals = s` by
    fs[dataSemTheory.state_component_equality]>>
  pop_assum SUBST_ALL_TAC>>fs[]>>
  fs[dataSemTheory.state_component_equality]
QED

Theorem assign_Install:
  (op = Install) ==> ^assign_thm_link_goal
Proof
  rpt strip_tac \\ drule (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ ‘names_opt ≠ NONE’ by (qpat_x_assum ‘op_requires_names _ ⇎ _’ mp_tac \\ EVAL_TAC \\ simp [])
  \\ gvs [GSYM IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS]
  \\ rename [‘cut_state_opt (SOME kept_names) s’]
  \\ drule_all state_rel_cut_state_opt_SOME
  \\ strip_tac
  \\ qpat_x_assum ‘_ (t with locals := y) NONE locs’ $ ASSUME_NAMED_TAC "with_locals"
  \\ `~s2.safe_for_space` by
    (drule do_app_safe_for_space_allowed_op \\ fs[allowed_op_def])
  \\ fs [assign_def] \\ rw []
  \\ gvs [do_app,REWRITE_RULE [METIS_PROVE [] ``~b\/c<=>(b==>c)``]
          do_install_def,UNCURRY,AllCaseEqs()]
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ rename1 `get_vars _ _ =
        SOME [hv1;hv2; Number (&LENGTH q2)]`
  \\ rename1 `get_vars [v1;v2;v4] _ =
        SOME [_;_; Number (&LENGTH q2)]`
  \\ fs [dataLangTheory.op_requires_names_def,
         dataLangTheory.op_space_reset_def,cut_state_opt_def]
  (* single-cut seam: args are NOT guaranteed in kept_names (dataSem reads get_vars
     from full s.locals pre-cut), so the arg memory_rel comes from the FULL state_rel s t
     hypothesis, NOT the cut state. s1 := x (the cut state) for the call setup + result. *)
  \\ `x = s with locals := x.locals` by
       (qpat_x_assum `cut_state kept_names s = SOME x` mp_tac
        \\ simp [dataSemTheory.cut_state_def, AllCaseEqs()] \\ rw [] \\ fs [])
  \\ qpat_x_assum `state_rel c l1 l2 s t NONE locs` (fn th => NTAC 2 (mp_tac th)) \\ strip_tac
  \\ simp_tac std_ss [Once state_rel_thm] \\ strip_tac \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 memory_rel_lookup_var_IMP \\ strip_tac
  \\ fs [code_oracle_rel_def]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ rename [‘get_vars [adjust_var v1; adjust_var v2; adjust_var v4] _
              = SOME [_;_;temp_w4]’]
  \\ `?w4. get_var (adjust_var v4) t = SOME (Word w4) ∧
           temp_w4 = Word w4` by
   (drule memory_rel_tl \\ strip_tac
    \\ drule memory_rel_tl \\ strip_tac
    \\ imp_res_tac memory_rel_any_Number_IMP \\ fs [get_vars_SOME_IFF]
    \\ gvs [wordSemTheory.get_vars_def])
  \\ rveq
  \\ rpt_drule0 evaluate_BignumHalt
  \\ strip_tac \\ fs [] \\ IF_CASES_TAC >- fs [] \\ fs []
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ ntac 2 (qpat_x_assum `_.ffi = _.ffi` kall_tac)
  \\ qpat_x_assum `eveluate _ = (NONE,_)` kall_tac
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [get_vars_SOME_IFF] \\ clean_tac
  \\ `w4 = n2w (2 * LENGTH q2) /\
      2 * LENGTH q2 < dimword (:'a) /\
      n2w (2 * LENGTH q2) >>> 1 = n2w (LENGTH q2):'a word` by
   (drule memory_rel_tl \\ strip_tac
    \\ drule memory_rel_tl \\ strip_tac
    \\ drule memory_rel_tl \\ strip_tac
    \\ imp_res_tac memory_rel_any_Number_IMP \\ fs [get_vars_SOME_IFF]
    \\ rfs [] \\ rveq
    \\ imp_res_tac memory_rel_any_Number_IMP \\ rfs [] \\ rveq
    \\ imp_res_tac memory_rel_Number_IMP
    \\ fs [Smallnum_def]
    \\ once_rewrite_tac [GSYM w2n_11] \\ rewrite_tac [w2n_lsr]
    \\ fs [w2n_n2w,small_int_def]
    \\ `(2 * LENGTH q2) < dimword (:α)`
         by (fs [good_dimindex_def,dimword_def] \\ rfs [])
    \\ fs [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV])
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.get_var_def]
  \\ simp [Once word_exp_set_var_ShiftVar_lemma,lookup_insert]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ simp [Once word_exp_set_var_ShiftVar_lemma,lookup_insert]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.get_var_def,lookup_insert,wordSemTheory.get_var_imm_def]
  \\ IF_CASES_TAC THEN1
   (qmatch_goalsub_abbrev_tac `GiveUp, t6`
    \\ qsuff_tac `state_rel c l1 l2 x t6 NONE locs`
    THEN1 (rw [] \\ imp_res_tac evaluate_GiveUp \\ fs [])
    \\ fs [Abbr `t6`]
    \\ full_simp_tac(srw_ss())[state_rel_def] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[lookup_insert,adjust_var_NEQ_1]
    \\ full_simp_tac(srw_ss())[inter_insert,domain_lookup,
         lookup_1_adjust_set,lookup_3_adjust_set,lookup_5_adjust_set]
    \\ metis_tac [])
  \\ `LENGTH q2 <= t.data_buffer.space_left` by
   (pop_assum mp_tac
    \\ fs [asmTheory.word_cmp_def,WORD_LO,NOT_LESS]
    \\ match_mp_tac (DECIDE ``m <= k ==> (n <= m ==> n <= k:num)``)
    \\ fs [w2n_lsr,bytes_in_word_def,word_mul_n2w]
    \\ `dimindex (:α) DIV 8 = 2 ** shift (dimindex (:α))` by
         fs [good_dimindex_def,shift_def]
    \\ `0 < dimword (:α) DIV 2 ** shift (dimindex (:α)) /\ 0 < 2 ** shift (dimindex (:α)) /\
        dimword (:α) = 2 ** shift (dimindex (:α)) * (dimword (:α) DIV 2 ** shift (dimindex (:α)))`
         by fs [good_dimindex_def,shift_def,dimword_def]
    \\ pop_assum (fn th => once_rewrite_tac [th])
    \\ simp [GSYM DIV_MOD_MOD_DIV,MULT_DIV]
    \\ match_mp_tac MOD_LESS_EQ \\ fs [])
  \\ qpat_x_assum `v_to_mlstring _ _ = SOME _` mp_tac
  \\ simp [dataSemTheory.v_to_mlstring_def, AllCaseEqs()]
  \\ strip_tac \\ gvs []
  \\ `x.refs = s.refs` by
   (qpat_x_assum `cut_state kept_names s = SOME x` mp_tac
    \\ simp [dataSemTheory.cut_state_def, AllCaseEqs()] \\ rw [] \\ fs [])
  \\ `lookup p s.refs = SOME (ByteArray T bs)` by fs []
  \\ rpt_drule0 memory_rel_ByteArray_IMP \\ strip_tac
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ `LENGTH bs + 2 ** shift (dimindex (:α)) < 2 ** (dimindex (:α) - 3) /\
      (n2w (make_byte_header c T (LENGTH bs)):α word) >>>
        (dimindex (:α) - (c.len_size + shift (dimindex (:α)))) =
      n2w (LENGTH bs + 2 ** shift (dimindex (:α)))` by
       (qpat_x_assum `if dimindex (:α) = 32 then _ else _` mp_tac
        \\ Cases_on `dimindex (:α) = 32`
        \\ fs [good_dimindex_def,shift_def,SUB_PLUS]
        \\ strip_tac \\ fs [])
  \\ `(dimindex (:α) - (c.len_size + shift (dimindex (:α)))) MOD dimword (:α) =
      dimindex (:α) - (c.len_size + shift (dimindex (:α)))` by
       (match_mp_tac LESS_MOD
        \\ assume_tac dimindex_lt_dimword \\ fs [])
  \\ `~(dimindex (:α) >= dimindex (:α) + (c.len_size + shift (dimindex (:α))))` by
       (Cases_on `dimindex (:α) = 32` \\ fs [good_dimindex_def,shift_def])
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.get_var_def,lookup_insert]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ qmatch_goalsub_abbrev_tac `word_exp t99 (real_addr c (adjust_var v1))`
  \\ `word_exp t99 (real_addr c (adjust_var v1)) = SOME (Word a)` by
       (match_mp_tac (GEN_ALL get_real_addr_lemma)
        \\ qexists_tac `w`
        \\ fs [Abbr `t99`,wordSemTheory.get_var_def,lookup_insert,
               good_dimindex_def])
  \\ fs []
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.get_var_def,lookup_insert]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.get_var_def,lookup_insert,wordSemTheory.get_var_imm_def]
  \\ `-1w * bytes_in_word + n2w (LENGTH bs + 2 ** shift (dimindex (:α))) =
      (n2w (LENGTH bs)):α word` by
       (Cases_on `dimindex (:α) = 32`
        \\ fs [bytes_in_word_def,good_dimindex_def,shift_def,GSYM word_add_n2w])
  \\ fs []
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.get_var_def,lookup_insert,wordSemTheory.get_var_imm_def]
  \\ IF_CASES_TAC THEN1
   (qmatch_goalsub_abbrev_tac `GiveUp, t6`
    \\ qsuff_tac `state_rel c l1 l2 x t6 NONE locs`
    THEN1 (rw [] \\ imp_res_tac evaluate_GiveUp \\ fs [])
    \\ fs [Abbr `t6`]
    \\ full_simp_tac(srw_ss())[state_rel_def] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[lookup_insert,adjust_var_NEQ_1]
    \\ full_simp_tac(srw_ss())[inter_insert,domain_lookup,
         lookup_1_adjust_set,lookup_3_adjust_set,lookup_5_adjust_set]
    \\ metis_tac [])
  \\ `LENGTH bs <= t.code_buffer.space_left` by
   (pop_assum mp_tac
    \\ fs [asmTheory.word_cmp_def,WORD_LO,NOT_LESS]
    \\ `LENGTH bs < dimword (:α)` by
         (qpat_x_assum `LENGTH bs + 2 ** shift (dimindex (:α)) < _` mp_tac
          \\ Cases_on `dimindex (:α) = 32`
          \\ fs [good_dimindex_def,dimword_def,shift_def])
    \\ fs [LESS_MOD]
    \\ match_mp_tac (DECIDE ``m <= k ==> (n <= m ==> n <= k:num)``)
    \\ match_mp_tac MOD_LESS_EQ \\ fs [])
  \\ pop_assum mp_tac \\ pop_assum kall_tac \\ strip_tac
  \\ clean_tac \\ fs []
  \\ fs [list_Seq_def]
  \\ `(?md. lookup InstallData_location t.code = SOME (4,InstallData_code c,md)) /\
      (?md. lookup Install_location t.code = SOME (3,Install_code c,md))` by
       (fs [state_rel_def,code_rel_def,stubs_md_def,stubs_def] \\ NO_TAC) \\ fs []
  \\ eval_tac
  \\ fs [wordSemTheory.evaluate_def,list_Seq_def,word_exp_rw,
         wordSemTheory.find_code_def,wordSemTheory.set_var_def,
         wordSemTheory.get_vars_def,wordSemTheory.get_var_def]
  \\ fs [wordSemTheory.add_ret_loc_def,wordSemTheory.find_code_def]
  \\ imp_res_tac cut_env_IMP_cut_envs
  \\ fs [wordSemTheory.bad_dest_args_def,wordSemTheory.get_vars_def,
         wordSemTheory.get_var_def,lookup_insert,data_to_wordTheory.get_names_def,
         cut_envs_adjust_sets_ODD,domain_adjust_sets]
  \\ fs [wordSemTheory.evaluate_def,wordSemTheory.call_env_def,
         wordSemTheory.push_env_def,wordSemTheory.dec_clock_def]
  \\ Cases_on `env_to_list y2 t.permute` \\ fs []
  \\ drule memory_rel_swap \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac `InstallData_code c, t88`
  \\ qspec_then `t88` mp_tac InstallData_code_thm
  \\ qunabbrev_tac `t88` \\ fs [wordSemTheory.get_var_def,
       lookup_insert,fromList2_def]
  \\ disch_then drule \\ fs []
  \\ strip_tac \\ fs[] \\ pop_assum kall_tac
  \\ simp [Install_code_def,Once list_Seq_def,wordSemTheory.evaluate_def]
  \\ eval_tac
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac \\ fs [lookup_insert]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac \\ fs [lookup_insert]
  \\ fs [wordSemTheory.set_store_def]
  \\ qmatch_goalsub_abbrev_tac `word_exp t98 (real_addr c 4)`
  \\ `word_exp t98 (real_addr c 4) = SOME (Word a)` by
       (match_mp_tac (GEN_ALL get_real_addr_lemma)
        \\ qexists_tac `w`
        \\ fs [Abbr `t98`,wordSemTheory.get_var_def,lookup_insert,
               good_dimindex_def])
  \\ fs []
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.get_var_def,lookup_insert]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.get_var_def,lookup_insert]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.set_store_def,wordSemTheory.get_var_def,lookup_insert]
  \\ `LENGTH bs < dimword (:α)` by
       (qpat_x_assum `LENGTH bs + 2 ** shift (dimindex (:α)) < _` mp_tac
        \\ Cases_on `dimindex (:α) = 32`
        \\ fs [good_dimindex_def,dimword_def,shift_def])
  \\ `read_bytearray (a + bytes_in_word) (LENGTH bs)
        (mem_load_byte_aux t.memory t.mdomain t.be) = SOME bs` by
       (match_mp_tac IMP_read_bytearray_GENLIST \\ fs [])
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [lookup_insert,wordSemTheory.code_buffer_install_def,w2n_n2w,LESS_MOD]
  \\ `x.compile = s.compile ∧ x.compile_oracle = s.compile_oracle` by
       (qpat_x_assum `cut_state kept_names s = SOME x` mp_tac
        \\ simp [dataSemTheory.cut_state_def, AllCaseEqs()] \\ rw [] \\ fs [])
  \\ Cases_on `s.compile_oracle 0`
  \\ fs [lookup_insert,wordSemTheory.get_var_def,wordSemTheory.cut_env_def,
         wordSemTheory.buffer_flush_def,bytes_in_word_def]
  \\ simp [wordSemTheory.cut_envs_def,wordSemTheory.cut_names_def]
  \\ qmatch_goalsub_rename_tac `compile_part c (ar1,ar2)`
  \\ qmatch_goalsub_rename_tac `compile_part c (ar1,ar2)`
  \\ Cases_on `compile_part c (ar1,ar2)` \\ fs [w2w_upper_upper_w2w]
  \\ rveq \\ fs []
  \\ reverse IF_CASES_TAC
  THEN1 (sg `F` \\ fs [] \\ fs [shift_seq_def,bytes_to_mlstring_11]
         \\ pop_assum mp_tac
         \\ DEP_REWRITE_TAC [w2w_upper_upper_w2w]
         \\ gvs [state_rel_def])
  \\ fs [inter_insert,wordSemTheory.get_vars_def,
         wordSemTheory.get_var_def,lookup_insert]
  \\ fs [list_Seq_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_def,
         wordSemTheory.get_vars_def,
         lookup_insert,wordSemTheory.call_env_def,wordSemTheory.pop_env_def,
         wordSemTheory.flush_state_def]
  \\ reverse IF_CASES_TAC
  THEN1
   (sg `F` \\ fs []
    \\ drule env_to_list_lookup_equiv
    \\ strip_tac
    \\ fs [domain_union,domain_fromAList_toAList]
    \\ fs [EXTENSION,domain_lookup,lookup_fromAList]
    \\ fs[GSYM IS_SOME_EXISTS]
    \\ CCONTR_TAC \\ fs []
    \\ metis_tac [IS_SOME_EXISTS])
  \\ fs [wordSemTheory.set_vars_def,alist_insert_def]
  \\ qabbrev_tac ‘t_locals = union y2 y1’
  \\ ‘union (fromAList q) (fromAList (toAList y1)) = t_locals’ by
   (gvs [Abbr‘t_locals’]
    \\ match_mp_tac (METIS_PROVE [] “f1 = f2 ∧ x1 = x2 ⇒ h f1 x1 = h f2 x2”)
    \\ imp_res_tac cut_envs_wf
    \\ DEP_REWRITE_TAC [spt_eq_thm]
    \\ drule env_to_list_lookup_equiv
    \\ simp [wf_fromAList,lookup_fromAList,ALOOKUP_toAList])
  \\ full_simp_tac std_ss [inter_insert_ODD_adjust_set]
  \\ qpat_x_assum ‘state_rel c l1 l2 _ _ NONE locs’ $ ASSUME_NAMED_TAC "state_rel_t"
  \\ LABEL_X_ASSUM "with_locals" mp_tac
  \\ simp [state_rel_thm]
  \\ strip_tac \\ gvs [FLOOKUP_SIMP,lookup_insert,adjust_var_11]
  \\ gvs []
  (* single-cut: result state_rel is in terms of the cut state x; bridge each
     non-locals field x.f = s.f (x = s with locals := x.locals) in both goal and
     assumptions, so the code_rel asm and the cut memory_rel asm line up. *)
  \\ `(x.code = s.code) /\ (x.refs = s.refs) /\ (x.space = s.space) /\
      (x.tstamps = s.tstamps) /\ (x.global = s.global) /\ (x.stack = s.stack)` by
       (qpat_x_assum `x = s with locals := x.locals` (fn th => once_rewrite_tac [th]) \\ simp [])
  \\ pop_assum (fn th => full_simp_tac std_ss (CONJUNCTS th))
  \\ reverse conj_tac
  THEN1 (* ptr_eq_link *)
   (`x.ptr_eq_oracle = s.ptr_eq_oracle` by
      (qpat_x_assum `x = s with locals := x.locals` (fn th => once_rewrite_tac [th])
       \\ simp [])
    \\ fs [ptr_eq_link_def])
  \\ conj_tac
  THEN1 (* code_rel *)
   (qpat_x_assum `_ = (_,_)` (fn th => fs [GSYM th])
    \\ rewrite_tac [GSYM MAP]
    \\ qmatch_goalsub_rename_tac `MAP _ full_list`
    \\ fs [code_rel_def,domain_union,domain_fromAList,lookup_union]
    \\ fs [lookup_fromAList,MAP_FST_MAP_compile_part]
    \\ fs [AC UNION_COMM UNION_ASSOC]
    \\ conj_tac THEN1
     (fs [EVERY_MEM,FORALL_PROD]
      \\ rw [] \\ first_x_assum drule \\ fs [])
    \\ rw []
    \\ qmatch_asmsub_rename_tac `ALOOKUP full_list nn`
    \\ qpat_x_assum `domain t.code = _` assume_tac
    \\ fs [EXTENSION,domain_lookup]
    \\ pop_assum (qspec_then `nn` mp_tac)
    \\ Cases_on `lookup nn s.code` \\ fs []
    THEN1
     (Cases_on `lookup nn t.code` \\ fs []
      THEN1
       (strip_tac \\ qpat_x_assum `ALOOKUP _ _ = _` mp_tac
        \\ qspec_tac (`full_list`,`xs`)
        \\ Induct \\ fs [FORALL_PROD,ALOOKUP_def,compile_part_def] \\ rw [])
      \\ qpat_x_assum `∀n. EVERY _ _` (qspec_then `0` mp_tac)
      \\ fs [EVERY_MEM]
      \\ imp_res_tac ALOOKUP_MEM
      \\ disch_then drule \\ fs []
      \\ rpt (pop_assum kall_tac)
      \\ rewrite_tac [stubs_md_def,stubs_def,generated_bignum_stubs_eq,
                      MAP_MAP_o,o_DEF,MAP,FST,APPEND]
      \\ rewrite_tac [MEM,EVAL ``data_num_stubs``]
      \\ rpt strip_tac \\ rveq \\ sg `F` \\ fs []
      \\ pop_assum mp_tac \\ EVAL_TAC)
    \\ rename1 `_ = SOME aa` \\ PairCases_on `aa`
    \\ first_x_assum drule \\ fs [])
  \\ conj_tac
  THEN1 (* code_oracle_rel *)
   (fs [code_oracle_rel_def,FLOOKUP_UPDATE,bytes_in_word_def,n2w_sub]
    \\ once_rewrite_tac [GSYM word_sub_def]
    \\ rewrite_tac [WORD_LEFT_SUB_DISTRIB]
    \\ fs [GSYM bytes_in_word_def]
    \\ simp [FUN_EQ_THM,o_DEF,shift_seq_def,FORALL_PROD]
    \\ rewrite_tac [GSYM WORD_ADD_ASSOC]
    \\ rewrite_tac [WORD_ADD_ASSOC]
    \\ once_rewrite_tac [WORD_ADD_COMM]
    \\ rewrite_tac [WORD_ADD_ASSOC,wordsTheory.WORD_ADD_LINV]
    \\ fs [])
  \\ conj_tac >- rw []
  \\ fs [FAPPLY_FUPDATE_THM,memory_rel_ignore_buffers]
  \\ imp_res_tac compile_part_loc_IMP \\ fs [] \\ rveq \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs [inter_insert_ODD_adjust_set_alt]
  \\ match_mp_tac memory_rel_CodePtr
  \\ asm_rewrite_tac []
QED

val _=augment_srw_ss[rewrites[i2w_int_or,i2w_mod_pow2,compiler_ptr_bits_i2w]];

val _ = augment_srw_ss [rewrites [arch_width_eq32, arch_bytes_scaled_word]];

val _ = augment_srw_ss [rewrites [compiler_tag_mask_i2w]];

val _ = augment_srw_ss [rewrites [compiler_Smallnum_i2w]];

Theorem assign_Label:
  (∃lab. op = Label lab) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ imp_res_tac state_rel_arch_width
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def,
          dataSemTheory.allowed_op_def]
  \\ gvs [do_app,AllCaseEqs()]
  \\ fs [assign_def,eq_eval]
  \\ fs [state_rel_thm]
  \\ fs [domain_lookup,lookup_map]
  \\ reverse IF_CASES_TAC THEN1
   (sg `F` \\ fs [code_rel_def]
    \\ rename1 `lookup _ s2.code = SOME zzz` \\ PairCases_on `zzz`
    \\ res_tac \\ fs []) \\ fs []
  \\ fs [wordSemTheory.set_var_def,set_var_def]
  \\ fs [lookup_insert,FAPPLY_FUPDATE_THM,adjust_var_11,FLOOKUP_UPDATE]
  \\ conj_tac >- rw []
  \\ fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ match_mp_tac memory_rel_CodePtr \\ fs []
QED

Theorem assign_FFI:
   (?n. op = FFI n) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ ‘names_opt ≠ NONE’ by (qpat_x_assum ‘op_requires_names _ ⇎ _’ mp_tac \\ EVAL_TAC \\ simp [])
  \\ gvs [GSYM IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS]
  \\ rename [‘cut_state_opt (SOME kept_names) s’]
  \\ drule_all state_rel_cut_state_opt_SOME \\ strip_tac
  \\ qpat_x_assum ‘_ (t with locals := y) NONE locs’ $ ASSUME_NAMED_TAC "with_locals"
  \\ qpat_x_assum `_  s t NONE locs`$ ASSUME_NAMED_TAC "old"
  \\ fs[do_app,dataSemTheory.allowed_op_def] \\ clean_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ rename [‘get_vars [e1;e2] s.locals’]
  \\ fs [bvlSemTheory.Unit_def] \\ rveq
  \\ fs [GSYM bvlSemTheory.Unit_def] \\ rveq
  \\ imp_res_tac get_vars_2_imp
  \\ LABEL_ASSUM "old" (assume_tac o REWRITE_RULE [state_rel_thm])
  \\ full_simp_tac std_ss [APPEND, GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP)
  \\ strip_tac
  \\ fs[get_vars_def]
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ rpt_drule0 memory_rel_ByteArray_IMP
  \\ drule0 memory_rel_tl \\ strip_tac
  \\ rpt_drule0 memory_rel_ByteArray_IMP
  \\ pop_assum kall_tac
  \\ ntac 2 strip_tac \\ clean_tac
  \\ qmatch_asmsub_rename_tac ‘call_FFI x.ffi (ExtCall n') cbs dbs = FFI_return nffi nbs’
  \\ qmatch_asmsub_rename_tac ‘lookup cp x.refs = SOME (ByteArray T cbs)’
  \\ qmatch_asmsub_rename_tac ‘lookup dp x.refs = SOME (ByteArray F dbs)’
  \\ qmatch_asmsub_rename_tac ‘get_vars [adjust_var e1; adjust_var e2] t = SOME [cw; dw]’
  (* args not in cut: refs/ffi unchanged by cut_state_opt *)
  \\ ‘x.refs = s.refs ∧ x.ffi = s.ffi’ by
       (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
        \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
        \\ rw [] \\ simp [])
  (* specialise the two byte-array facts against the full-state memory_rel *)
  \\ qpat_x_assum ‘∀vals fl. lookup cp s.refs = _ ∧ _ ⇒ _’ (qspecl_then [‘cbs’,‘T’] mp_tac)
  \\ impl_tac >- gvs []
  \\ strip_tac
  \\ qpat_x_assum ‘∀vals fl. lookup dp s.refs = _ ∧ _ ⇒ _’ (qspecl_then [‘dbs’,‘F’] mp_tac)
  \\ impl_tac >- gvs []
  \\ strip_tac
  \\ ‘dimindex (:'a) - shift (dimindex (:'a)) - c.len_size < dimword (:'a)’ by
       (MP_TAC dimindex_lt_dimword \\ decide_tac)
  \\ simp[assign_def,list_Seq_def] \\ eval_tac
  \\ Cases_on ‘¬c.call_empty_ffi ∧ n' = «»’
  >- (
  fs[wordSemTheory.evaluate_def]
  \\ simp[Unit_def,wordSemTheory.word_exp_def]
  \\ qpat_x_assum ‘state_rel c l1 l2 x t NONE locs’ (assume_tac o REWRITE_RULE [state_rel_thm])
  \\ ‘nffi = s.ffi ∧ nbs = dbs’ by
       (qpat_x_assum ‘call_FFI s.ffi (ExtCall «») _ _ = _’ mp_tac
        \\ simp [ffiTheory.call_FFI_def])
  \\ gvs [state_rel_thm, wordSemTheory.set_var_def, lookup_insert, option_le_max_right]
  \\ conj_tac >- (rw[] \\ metis_tac[])
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert
  \\ simp[option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ match_mp_tac memory_rel_Unit
  \\ DEP_REWRITE_TAC[insert_unchanged]
  \\ fs[FLOOKUP_DEF]
  \\ metis_tac[memory_rel_zero_space])
  \\ qpat_x_assum ‘¬(¬c.call_empty_ffi ∧ n' = «»)’ (SUBST_ALL_TAC o EQF_INTRO)
  \\ rewrite_tac[]
  \\ ‘get_var (adjust_var e1) t = SOME (Word w) ∧
      get_var (adjust_var e2) t = SOME (Word w')’ by fs [wordSemTheory.get_var_def]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (Word _)`
     (fn thm=> rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ eval_tac
  \\ simp[]
  \\ qpat_abbrev_tac`tt = t with locals := _`
  \\ ‘get_var (adjust_var e1) tt = get_var (adjust_var e1) t’
     by fs[Abbr`tt`,wordSemTheory.get_var_def,lookup_insert]
  \\ ‘get_var (adjust_var e2) tt = get_var (adjust_var e2) t’
     by fs[Abbr`tt`,wordSemTheory.get_var_def,lookup_insert]
  \\ rfs[]
  \\ ‘get_var (adjust_var e1) tt = SOME (Word w) ∧
      get_var (adjust_var e2) tt = SOME (Word w')’ by fs [wordSemTheory.get_var_def]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (Word _)`
     (fn thm=> rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ `tt.store = t.store` by simp[Abbr`tt`]
  \\ simp[]
  \\ qpat_abbrev_tac`ex1 = if n' = «» then _ else _`
  \\ qpat_abbrev_tac`ex2 = if n' = «» then _ else _`
  \\ IF_CASES_TAC >- ( fs[shift_def] )
  \\ simp[wordSemTheory.get_var_def,lookup_insert]
  \\ qpat_x_assum`¬_`kall_tac
  \\ qpat_abbrev_tac`ttt = t with locals := insert 3 _ (insert 1 _ t.locals)`
  \\ ‘get_var (adjust_var e1) ttt = get_var (adjust_var e1) t’
     by fs[Abbr`ttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ ‘get_var (adjust_var e2) ttt = get_var (adjust_var e2) t’
     by fs[Abbr`ttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ rfs[]
  \\ ‘get_var (adjust_var e1) ttt = SOME (Word w) ∧
      get_var (adjust_var e2) ttt = SOME (Word w')’ by fs [wordSemTheory.get_var_def]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (Word _)`
     (fn thm=> rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ `ttt.store = t.store` by simp[Abbr`ttt`]
  \\ simp[Abbr`ex1`,Abbr`ex2`]
  \\ Cases_on ‘n' = «»’ \\ fs[]
  >- (
  eval_tac
  \\ fs[lookup_insert,wordSemTheory.word_exp_def,ffiTheory.call_FFI_def]
  \\ fs[read_bytearray_def,wordSemTheory.write_bytearray_def]
  \\ fs[cut_env_adjust_sets_insert_ODD]
  \\ qmatch_goalsub_abbrev_tac`read_bytearray aa len g`
  \\ qispl_then[`cbs`,`LENGTH cbs`,`aa`]mp_tac IMP_read_bytearray_GENLIST
  \\ impl_tac >- simp[]
  \\ `len = LENGTH cbs`
  by (
    simp[Abbr`len`]
    \\ rfs[good_dimindex_def] \\ rfs[shift_def]
    \\ simp[bytes_in_word_def,GSYM word_add_n2w]
    \\ simp[dimword_def] )
  \\ fs[] \\ strip_tac
  \\ simp[Unit_def]
  \\ eval_tac
  \\ simp[lookup_insert,lookup_inter_alt]
  \\ rpt disch_tac
  \\ LABEL_ASSUM "with_locals" (assume_tac o REWRITE_RULE [state_rel_thm])
  \\ gvs [state_rel_thm, wordSemTheory.set_var_def, lookup_insert, option_le_max_right]
  \\ conj_tac >- (rw[] \\ metis_tac[])
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert
  \\ simp[option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ match_mp_tac memory_rel_Unit
  \\ DEP_REWRITE_TAC[insert_unchanged]
  \\ fs[FLOOKUP_DEF]
  \\ metis_tac[memory_rel_zero_space])
  \\ simp[]
  \\ eval_tac
  \\ qpat_abbrev_tac`tttt = t with locals := insert 5 _ (insert 3 _ (insert 1 _ t.locals))`
  \\ ‘get_var (adjust_var e1) tttt = get_var (adjust_var e1) t’
     by fs[Abbr`tttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ ‘get_var (adjust_var e2) tttt = get_var (adjust_var e2) t’
     by fs[Abbr`tttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ rfs[]
  \\ ‘get_var (adjust_var e1) tttt = SOME (Word w) ∧
      get_var (adjust_var e2) tttt = SOME (Word w')’ by fs [wordSemTheory.get_var_def]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (Word _)`
     (fn thm=> rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ `tttt.store = t.store` by simp[Abbr`tttt`]
  \\ simp[]
  \\ IF_CASES_TAC >- ( fs[shift_def] )
  \\ simp[]
  \\ qpat_abbrev_tac`ttttt = t with locals := insert 7 _ (insert 5 _ (insert 3 _ (insert 1 _ t.locals)))`
  \\ ‘get_var (adjust_var e1) ttttt = get_var (adjust_var e1) t’
     by fs[Abbr`ttttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ ‘get_var (adjust_var e2) ttttt = get_var (adjust_var e2) t’
     by fs[Abbr`ttttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ qpat_x_assum`¬_` kall_tac
  \\ rfs[]
  \\ ‘get_var (adjust_var e1) ttttt = SOME (Word w) ∧
      get_var (adjust_var e2) ttttt = SOME (Word w')’ by fs [wordSemTheory.get_var_def]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (Word _)`
     (fn thm => rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ `ttttt.store = t.store` by simp[Abbr`ttttt`]
  \\ simp[]
  \\ simp[wordSemTheory.get_var_def,lookup_insert]
  \\ qmatch_goalsub_abbrev_tac`read_bytearray aa len g`
  \\ qispl_then[`cbs`,`LENGTH cbs`,`aa`]mp_tac IMP_read_bytearray_GENLIST
  \\ impl_tac >- simp[]
  \\ `len = LENGTH cbs`
  by (
    simp[Abbr`len`]
    \\ rfs[good_dimindex_def] \\ rfs[shift_def]
    \\ simp[bytes_in_word_def,GSYM word_add_n2w]
    \\ simp[dimword_def] )
  \\ fs[] \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`read_bytearray aa2 len2 _`
  \\ qispl_then[`dbs`,`LENGTH dbs`,`aa2`]mp_tac IMP_read_bytearray_GENLIST
  \\ impl_tac >- simp[]
  \\ `len2 = LENGTH dbs`
  by (
    simp[Abbr`len2`]
    \\ rfs[good_dimindex_def] \\ rfs[shift_def]
    \\ simp[bytes_in_word_def,GSYM word_add_n2w]
    \\ simp[dimword_def] )
  \\ fs[]
  \\ rpt strip_tac
  \\ simp[Unit_def,cut_env_adjust_sets_insert_ODD]
  \\ eval_tac
  \\ simp[lookup_insert]
  \\ ‘x.tstamps = s.tstamps ∧ x.global = s.global ∧ x.stack = s.stack ∧
      x.space = s.space’ by
       (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
        \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
        \\ rw [] \\ simp [])
  \\ LABEL_ASSUM "with_locals" (assume_tac o REWRITE_RULE [state_rel_thm])
  \\ gvs [state_rel_thm, wordSemTheory.set_var_def, lookup_insert, option_le_max_right]
  \\ conj_tac >- (rw[] \\ metis_tac[])
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ match_mp_tac memory_rel_Unit
  \\ reverse conj_tac >- simp[]
  \\ qpat_x_assum ‘memory_rel c t.be (THE s.tstamps) s.refs s.space t.store t.memory t.mdomain ((RefPtr _ cp,_)::_)’ assume_tac
  \\ dxrule memory_rel_zero_space \\ strip_tac
  \\ dxrule memory_rel_tl \\ strip_tac
  \\ drule memory_rel_write_bytearray \\ simp []
  \\ disch_then $ qspec_then ‘nbs’ mp_tac
  \\ impl_tac >- gvs [ffiTheory.call_FFI_def,AllCaseEqs()]
  \\ strip_tac
  \\ dxrule memory_rel_tl \\ strip_tac
  \\ qpat_x_assum ‘memory_rel _ _ _ (insert dp _ _) _ _ _ _ (join_env s.locals _ ++ _)’ mp_tac
  \\ match_mp_tac memory_rel_rearrange
  \\ ‘x.locals = mk_wf (inter s.locals kept_names)’ by
       (imp_res_tac cut_state_opt_SOME_eq \\ gvs [])
  \\ gen_tac \\ simp [MEM_APPEND]
  \\ strip_tac \\ simp []
  \\ disj1_tac
  \\ gvs [join_env_def, MEM_MAP, MEM_FILTER, EXISTS_PROD, MEM_toAList,
          lookup_inter, AllCaseEqs()]
  \\ gvs [wordSemTheory.cut_env_def, wordSemTheory.cut_envs_def,
          wordSemTheory.cut_names_def, adjust_sets_def, AllCaseEqs(),
          lookup_union, lookup_inter_alt, lookup_mk_wf]
  \\ rw [] \\ gvs [domain_lookup]
  \\ qexists_tac ‘p_1’
  \\ gvs [lookup_inter, AllCaseEqs(), domain_lookup]
  \\ gvs [lookup_adjust_set, domain_inter, AllCaseEqs(), domain_lookup]
  \\ gvs [lookup_inter, AllCaseEqs()]
QED

Theorem assign_FFI_final:
   state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) NONE locs /\
   (op_requires_names (FFI i) ≠ (names_opt = NONE)) ∧
   cut_state_opt names_opt s = SOME x /\
   get_vars args s.locals = SOME vals /\
   t.termdep > 1 /\
   do_app (FFI i) vals x = Rerr(Rabort(Rffi_error f)) ==>
   ?q r.
     evaluate (FST (assign c n l dest (FFI i) args names_opt),t) = (q,r) /\
     option_le r.stack_max s.stack_max /\
     q <> SOME NotEnoughSpace /\ r.ffi = t.ffi /\ q = SOME(FinalFFI f)
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ ‘names_opt ≠ NONE’ by (qpat_x_assum ‘op_requires_names _ ⇎ _’ mp_tac \\ EVAL_TAC \\ simp [])
  \\ gvs [GSYM IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS]
  \\ rename [‘cut_state_opt (SOME kept_names) s’]
  \\ drule_all state_rel_cut_state_opt_SOME \\ strip_tac
  \\ qpat_x_assum ‘_ (t with locals := y) NONE locs’ $ ASSUME_NAMED_TAC "with_locals"
  \\ qpat_x_assum `_  s t NONE locs`$ ASSUME_NAMED_TAC "old"
  \\ fs[do_app,dataSemTheory.allowed_op_def] \\ clean_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ gvs[AllCaseEqs()]
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ rename [‘get_vars [e1;e2] s.locals’]
  \\ fs [bvlSemTheory.Unit_def] \\ rveq
  \\ fs [GSYM bvlSemTheory.Unit_def] \\ rveq
  \\ imp_res_tac get_vars_2_imp
  \\ LABEL_ASSUM "old" (assume_tac o REWRITE_RULE [state_rel_thm])
  \\ full_simp_tac std_ss [APPEND, GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP)
  \\ strip_tac
  \\ fs[get_vars_def]
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ rpt_drule0 memory_rel_ByteArray_IMP
  \\ drule0 memory_rel_tl \\ strip_tac
  \\ rpt_drule0 memory_rel_ByteArray_IMP
  \\ pop_assum kall_tac
  \\ ntac 2 strip_tac \\ clean_tac
  \\ qmatch_asmsub_rename_tac ‘call_FFI x.ffi (ExtCall i) cbs dbs = FFI_final f’
  \\ qmatch_asmsub_rename_tac ‘lookup cp x.refs = SOME (ByteArray T cbs)’
  \\ qmatch_asmsub_rename_tac ‘lookup dp x.refs = SOME (ByteArray F dbs)’
  \\ qmatch_asmsub_rename_tac ‘get_vars [adjust_var e1; adjust_var e2] t = SOME [cw; dw]’
  \\ ‘x.refs = s.refs ∧ x.ffi = s.ffi’ by
       (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
        \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
        \\ rw [] \\ simp [])
  \\ qpat_x_assum ‘∀vals fl. lookup cp s.refs = _ ∧ _ ⇒ _’ (qspecl_then [‘cbs’,‘T’] mp_tac)
  \\ impl_tac >- gvs []
  \\ strip_tac
  \\ qpat_x_assum ‘∀vals fl. lookup dp s.refs = _ ∧ _ ⇒ _’ (qspecl_then [‘dbs’,‘F’] mp_tac)
  \\ impl_tac >- gvs []
  \\ strip_tac
  \\ ‘dimindex (:'a) - shift (dimindex (:'a)) - c.len_size < dimword (:'a)’ by
       (MP_TAC dimindex_lt_dimword \\ decide_tac)
  \\ simp[assign_def,list_Seq_def] \\ eval_tac
  \\ Cases_on ‘i = «»’
  >- gvs[ffiTheory.call_FFI_def]
  \\ gvs[]
  \\ ‘get_var (adjust_var e1) t = SOME (Word w) ∧
      get_var (adjust_var e2) t = SOME (Word w')’ by fs [wordSemTheory.get_var_def]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (Word _)`
     (fn thm=> rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ eval_tac \\ simp[]
  \\ qpat_abbrev_tac`tt = t with locals := insert 1 _ t.locals`
  \\ ‘get_var (adjust_var e1) tt = get_var (adjust_var e1) t’
     by fs[Abbr`tt`,wordSemTheory.get_var_def,lookup_insert]
  \\ ‘get_var (adjust_var e2) tt = get_var (adjust_var e2) t’
     by fs[Abbr`tt`,wordSemTheory.get_var_def,lookup_insert]
  \\ rfs[]
  \\ ‘get_var (adjust_var e1) tt = SOME (Word w) ∧
      get_var (adjust_var e2) tt = SOME (Word w')’ by fs [wordSemTheory.get_var_def]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (Word _)`
     (fn thm=> rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ `tt.store = t.store` by simp[Abbr`tt`]
  \\ simp[]
  \\ IF_CASES_TAC >- ( fs[shift_def] )
  \\ simp[wordSemTheory.get_var_def,lookup_insert]
  \\ qpat_x_assum`¬_`kall_tac
  \\ qpat_abbrev_tac`ttt = t with locals := insert 3 _ (insert 1 _ t.locals)`
  \\ ‘get_var (adjust_var e1) ttt = get_var (adjust_var e1) t’
     by fs[Abbr`ttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ ‘get_var (adjust_var e2) ttt = get_var (adjust_var e2) t’
     by fs[Abbr`ttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ rfs[]
  \\ ‘get_var (adjust_var e1) ttt = SOME (Word w) ∧
      get_var (adjust_var e2) ttt = SOME (Word w')’ by fs [wordSemTheory.get_var_def]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (Word _)`
     (fn thm=> rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ `ttt.store = t.store` by simp[Abbr`ttt`]
  \\ simp[]
  \\ qpat_abbrev_tac`tttt = t with locals := insert 5 _ (insert 3 _ (insert 1 _ t.locals))`
  \\ ‘get_var (adjust_var e1) tttt = get_var (adjust_var e1) t’
     by fs[Abbr`tttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ ‘get_var (adjust_var e2) tttt = get_var (adjust_var e2) t’
     by fs[Abbr`tttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ rfs[]
  \\ ‘get_var (adjust_var e1) tttt = SOME (Word w) ∧
      get_var (adjust_var e2) tttt = SOME (Word w')’ by fs [wordSemTheory.get_var_def]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (Word _)`
     (fn thm=> rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ `tttt.store = t.store` by simp[Abbr`tttt`]
  \\ simp[]
  \\ simp[]
  \\ simp[wordSemTheory.get_var_def,lookup_insert]
  \\ qmatch_goalsub_abbrev_tac`read_bytearray aa len g`
  \\ qispl_then[`cbs`,`LENGTH cbs`,`aa`]mp_tac IMP_read_bytearray_GENLIST
  \\ impl_tac >- simp[]
  \\ `len = LENGTH cbs`
  by (
    simp[Abbr`len`]
    \\ rfs[good_dimindex_def] \\ rfs[shift_def]
    \\ simp[bytes_in_word_def,GSYM word_add_n2w]
    \\ simp[dimword_def] )
  \\ fs[] \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`read_bytearray aa2 len2 _`
  \\ qispl_then[`dbs`,`LENGTH dbs`,`aa2`]mp_tac IMP_read_bytearray_GENLIST
  \\ impl_tac >- simp[]
  \\ `len2 = LENGTH dbs`
  by (
    simp[Abbr`len2`]
    \\ rfs[good_dimindex_def] \\ rfs[shift_def]
    \\ simp[bytes_in_word_def,GSYM word_add_n2w]
    \\ simp[dimword_def] )
  \\ fs[]
  \\ rpt strip_tac
  \\ simp[Unit_def]
  \\ gvs [wordSemTheory.flush_state_def]
  \\ simp[cut_env_adjust_sets_insert_ODD]
  \\ gvs[wordSemTheory.flush_state_def]
QED

Theorem join_lemma[local] =
  METIS_PROVE [] “(b1 ⇒ x) ∧ (b2 ⇒ x) ⇒ (b1 ∨ b2 ⇒ x)”;

Theorem imp_assign[local] =
  DB.match ["-"] “_ ==> ^assign_thm_goal” |> map (#1 o #2)
  |> end_itlist (fn x => fn y => MATCH_MP join_lemma (CONJ x y));

Theorem assign_LabelFFI:
  ((∃lab. op = Label lab) ∨ (∃n. op = FFI n)) ⇒ ^assign_thm_goal
Proof
  strip_tac \\ strip_tac
  \\ irule imp_assign
  \\ asm_rewrite_tac []
  \\ rpt $ first_assum $ irule_at Any
  \\ gvs []
QED

