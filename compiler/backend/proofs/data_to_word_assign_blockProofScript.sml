(*
  Part of the correctness proof for data_to_word: assign for BlockOp
*)
Theory data_to_word_assign_blockProof
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
val all_ones_def = data_to_word_memoryProofTheory.all_ones_def;
val maxout_bits_def = data_to_word_memoryProofTheory.maxout_bits_def;
val ptr_bits_def = data_to_word_memoryProofTheory.ptr_bits_def;
val Smallnum_def = LIST_CONJ [data_to_word_memoryProofTheory.Smallnum_def,
                             data_to_wordTheory.Smallnum_def];
val get_lowerbits_def = data_to_word_memoryProofTheory.get_lowerbits_def;
val make_ptr_def = data_to_word_memoryProofTheory.make_ptr_def;
val make_cons_ptr_def = data_to_word_memoryProofTheory.make_cons_ptr_def;
val isWord_def = wordSemTheory.isWord_def
Overload lookup[local] = “sptree$lookup”;

val assign_def =
  data_to_wordTheory.assign_def
  |> REWRITE_RULE [arg1_def, arg2_def, arg3_def, arg4_def, all_assign_defs];

val clean_tac = rpt var_eq_tac \\ rpt (qpat_x_assum `T` kall_tac);
fun rpt_drule0 th = drule0 (th |> GEN_ALL) \\ rpt (disch_then drule0 \\ fs []);

val adjust_set_def = LIST_CONJ [data_to_wordTheory.adjust_set_def,
  data_to_word_gcProofTheory.adjust_set_def];

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

Theorem split_if[local]:
  (if b then f x else h y) = (if b then f else h) (if b then x else y)
Proof
  rw []
QED

Theorem LESS_DIV_4_IMP:
   n < k DIV 4 ==> 2 * n < k:num
Proof
  fs [X_LT_DIV]
QED

Theorem encode_header_IMP_BIT0:
   encode_header c tag l = SOME w /\
   c.len_size < arch_width_bits c.arch_width ==>
   (n2w w:'a word) ' 0
Proof
  fs [encode_header_def,make_header_def] \\ rw []
  \\ Cases_on `c.arch_width`
  \\ fs [word_index,bitTheory.BIT0_ODD,ODD_ADD,ODD_MULT,
         EVEN_EXP_IFF,ODD_EVEN,EVEN_ADD,EVEN_MULT,
         asmTheory.arch_width_bits_def]
QED

val _ = augment_srw_ss [rewrites [arch_bytes_word]];
val eval_tac = imp_res_tac state_rel_arch_width
  \\ imp_res_tac memory_rel_arch_width \\ eval_tac
  \\ fs [GSYM word_mul_n2w];

Theorem state_rel_IMP_test_zero:
   state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) vs locs /\
    get_var i s.locals = SOME (Number n) ==>
    ?w. get_var (adjust_var i) t = SOME (Word w) /\ (w = 0w <=> (n = 0))
Proof
  strip_tac
  \\ rpt_drule0 state_rel_get_var_IMP
  \\ strip_tac \\ fs []
  \\ fs [state_rel_thm,get_vars_SOME_IFF_data] \\ rw []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,get_var_def]
  \\ drule0 memory_rel_drop \\ strip_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,get_var_def]
  \\ rpt_drule0 memory_rel_lookup
  \\ fs [wordSemTheory.get_var_def] \\ strip_tac
  \\ `small_int (dimindex (:'a)) 0` by
     (fs [good_dimindex_def,dimword_def,small_int_def] \\ NO_TAC)
  \\ rpt_drule0 (IMP_memory_rel_Number
        |> REWRITE_RULE [CONJ_ASSOC]
        |> ONCE_REWRITE_RULE [CONJ_COMM])
  \\ fs [] \\ strip_tac
  \\ drule0 memory_rel_Number_EQ \\ fs []
  \\ strip_tac \\ fs [Smallnum_def]
  \\ eq_tac \\ rw [] \\ fs []
QED

val get_var_get_real_addr_lemma =
    GEN_ALL(CONV_RULE(LAND_CONV(move_conj_left(
                                   same_const``wordSem$get_var`` o #1 o
                                   strip_comb o lhs)))
                     get_real_addr_lemma)

val _=augment_srw_ss[rewrites[i2w_int_or,i2w_mod_pow2,compiler_ptr_bits_i2w]];

val _ = augment_srw_ss [rewrites [arch_width_eq32, arch_bytes_scaled_word]];

Theorem cut_envs_domain_IN:
  cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) ∧
  cut_env kept_names s_locals = SOME x ∧
  n ∈ domain x ⇒
  adjust_var n ∈ domain y2
Proof
  rw [] \\ gvs [wordSemTheory.cut_envs_def,AllCaseEqs(),wordSemTheory.cut_names_def]
  \\ gvs [adjust_sets_def,domain_inter,adjust_var_IN_adjust_set]
  \\ gvs [dataSemTheory.cut_env_def,domain_inter]
  \\ gvs [SUBSET_DEF]
  \\ last_x_assum irule
  \\ simp [adjust_var_IN_adjust_set]
QED

Theorem evaluate_AppendMainLoop_code[local]:
    !xs ww (t:('a,'c,'ffi)wordSem$state) vars ptr hdr l k frame r1 r2 next_free ts v.
      memory_rel c t.be ts (s:('c,'ffi) dataSem$state).refs sp t.store t.memory t.mdomain
         ((v,Word ww)::vars) /\ xs <> [] /\
      v_to_list v = SOME xs /\
      lookup 10 t.locals = SOME (Word ptr) /\
      lookup 8 t.locals = SOME (Word (bytes_in_word * n2w (sp - k))) /\
      lookup 6 t.locals = SOME (Word hdr) /\
      lookup 4 t.locals = SOME (Word ww) /\
      lookup 2 t.locals = SOME (Word next_free) /\
      lookup 0 t.locals = SOME (Loc r1 r2) /\
      k + 3 * LENGTH xs <= sp /\ good_dimindex (:'a) /\
      sp * (dimindex (:α) DIV 8) < dimword (:α) /\
      FLOOKUP t.store (Temp 0w) = SOME tmp0 /\
      FLOOKUP t.store (Temp 2w) = SOME tmp2 /\
      FLOOKUP t.store NextFree = SOME (Word f) /\
      Abbrev (next_free = f + bytes_in_word * n2w k) /\
      (?md. lookup AppendMainLoop_location t.code = SOME (6,AppendMainLoop_code c,md)) /\
      lookup AppendMainLoop_location t.stack_size = t.locals_size /\
      (word_list_exists next_free (3 * LENGTH xs) * frame)
         (fun2set (t.memory,t.mdomain)) /\ LENGTH xs <= t.clock ==>
      ?m1 ws smx.
        evaluate (AppendMainLoop_code c,t) =
          (SOME (Result (Loc r1 r2) [tmp2]),
           t with <| locals := LN ; locals_size := SOME 0;
                     store := t.store |+ (NextFree, Word (next_free +
                        bytes_in_word * n2w (3 * LENGTH xs))) ;
                     memory := m1 ;
                     stack_max := smx;
                     clock := t.clock - (LENGTH xs - 1) |>) /\
        LENGTH ws = LENGTH xs /\
        option_le smx (OPTION_MAP2 MAX
                         t.stack_max
                         (OPTION_MAP2 $+
                           (OPTION_MAP2 MAX
                             (lookup AppendMainLoop_location t.stack_size)
                             (lookup AppendLenLoop_location t.stack_size)
                           )
                           (stack_size t.stack))) /\
        (word_list next_free (append_writes c ptr hdr ws tmp0) * frame)
          (fun2set (m1,t.mdomain)) /\
        memory_rel c t.be ts s.refs sp t.store m1 t.mdomain
          (ZIP (xs,ws)++vars)
Proof
  strip_tac
  \\ completeInduct_on `LENGTH xs` \\ fs [PULL_FORALL]
  \\ rpt strip_tac \\ rveq \\ fs []
  \\ Cases_on `xs` \\ fs [] \\ clean_tac
  \\ imp_res_tac memory_rel_arch_width
  \\ once_rewrite_tac [AppendMainLoop_code_def]
  \\ fs [] \\ Cases_on `v'` \\ fs [v_to_list_def]
  \\ drule memory_rel_Block_IMP \\ fs []
  \\ strip_tac \\ fs []
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def]
  \\ `get_var 4 t = SOME (Word ww)` by fs [wordSemTheory.get_var_def]
  \\ `shift_length c < dimindex (:α)` by
        fs [memory_rel_def,heap_in_memory_store_def]
  \\ `l ≠ []` by (Cases_on `l` \\ fs [v_to_list_def])
  \\ rpt_drule0 get_var_get_real_addr_lemma \\ fs []
  \\ disch_then kall_tac
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [eq_eval,wordSemTheory.set_var_def]
  \\ rpt_drule0 memory_rel_Block_MEM
  \\ disch_then (qspec_then `0` mp_tac) \\ fs []
  \\ fs [get_real_offset_def,Smallnum_def]
  \\ impl_tac >- (Cases_on `l` \\ fs [])
  \\ strip_tac
  \\ drule memory_rel_swap \\ strip_tac
  \\ rpt_drule0 memory_rel_Block_MEM
  \\ disch_then (qspec_then `1` mp_tac) \\ fs []
  \\ drule v_to_list_SOME_CONS_IMP  \\ strip_tac \\ fs []
  \\ `get_real_offset (Smallnum 1) = SOME (2w * bytes_in_word )` by
     (EVAL_TAC \\ fs [good_dimindex_def,dimword_def]) \\ fs []
  \\ strip_tac
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [eq_eval,wordSemTheory.set_var_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [eq_eval,wordSemTheory.set_var_def]
  \\ IF_CASES_TAC THEN1
   (sg `F` \\ fs [WORD_LO,word_mul_n2w,bytes_in_word_def]
    \\ rfs [good_dimindex_def] \\ rfs [dimword_def])
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [eq_eval,wordSemTheory.set_var_def,wordSemTheory.mem_store_def]
  \\ fs [MULT_CLAUSES]
  \\ `?x1 x2 x3.
       (one (next_free,x1) *
        one (next_free + bytes_in_word,x2) *
        one (next_free + 2w * bytes_in_word,x3) *
        word_list_exists (next_free + 3w * bytes_in_word) (3 * LENGTH t') * frame)
             (fun2set (t.memory,t.mdomain))` by
       (fs [word_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM]
        \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
        \\ Cases_on `xs` \\ fs []
        \\ Cases_on `t''` \\ fs []
        \\ Cases_on `t'''` \\ fs [ADD1,word_list_def]
        \\ qexists_tac `h'`
        \\ qexists_tac `h''`
        \\ qexists_tac `h'''`
        \\ qexists_tac `t''`
        \\ fs [AC STAR_COMM STAR_ASSOC])
  \\ SEP_R_TAC \\ fs []
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [eq_eval,wordSemTheory.set_var_def,wordSemTheory.mem_store_def]
  \\ SEP_R_TAC \\ fs []
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [eq_eval,wordSemTheory.set_var_def,wordSemTheory.mem_store_def]
  \\ Cases_on `t'`
  THEN1
   (fs [v_to_list_EQ_SOME_NIL] \\ rveq \\ fs []
    \\ rpt_drule0 memory_rel_Block_IMP
    \\ simp [asmTheory.word_cmp_def]
    \\ fs [SIMP_RULE (srw_ss()) [] word_and_one_eq_0_iff]
    \\ disch_then kall_tac
    \\ rewrite_tac [list_Seq_def]
    \\ fs [eq_eval,wordSemTheory.set_var_def,
           wordSemTheory.mem_store_def,wordSemTheory.get_store_def]
    \\ SEP_R_TAC \\ fs [eq_eval,wordSemTheory.set_store_def,
                        wordSemTheory.flush_state_def]
    \\ fs [wordSemTheory.state_component_equality]
    \\ qexists_tac `[t.memory (a + bytes_in_word)]` \\ fs []
    \\ fs [append_writes_def,word_list_def]
    \\ conj_tac
    >- (rw[option_le_max_right])
    \\ conj_tac THEN1
     (fs [SEP_CLAUSES,word_list_exists_thm]
      \\ qabbrev_tac `mm = t.memory`
      \\ qabbrev_tac `dm = t.mdomain`
      \\ SEP_WRITE_TAC)
    \\ drule (IMP_TRANS (memory_rel_tl |> Q.INST [`x`|->`y`,`xs`|->`x::xs`])
                  memory_rel_tl) \\ strip_tac
    \\ drule (GEN_ALL memory_rel_write) \\ fs []
    \\ disch_then (qspecl_then [`Word hdr`,`k`] mp_tac)
    \\ impl_tac THEN1 fs [] \\ strip_tac \\ rfs []
    \\ drule (GEN_ALL memory_rel_write) \\ fs []
    \\ disch_then (qspecl_then [`t.memory (a + bytes_in_word)`,`k+1`] mp_tac)
    \\ impl_tac THEN1 fs [] \\ strip_tac
    \\ rfs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ drule (GEN_ALL memory_rel_write) \\ fs []
    \\ disch_then (qspecl_then [`tmp0`,`k+2`] mp_tac)
    \\ impl_tac THEN1 fs [] \\ strip_tac
    \\ rfs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,Abbr`next_free`])
  \\ drule v_to_list_SOME_CONS_IMP \\ strip_tac
  \\ fs [] \\ rveq \\ fs []
  \\ rpt_drule0 memory_rel_Block_IMP
  \\ strip_tac \\ fs []
  \\ simp [asmTheory.word_cmp_def]
  \\ fs [SIMP_RULE (srw_ss()) [] word_and_one_eq_0_iff]
  \\ qmatch_goalsub_abbrev_tac `list_Seq test`
  \\ pop_assum kall_tac
  \\ rewrite_tac [list_Seq_def]
  \\ fs [eq_eval,wordSemTheory.set_var_def,wordSemTheory.mem_store_def,
         wordSemTheory.get_store_def]
  \\ SEP_R_TAC \\ fs [eq_eval,wordSemTheory.set_store_def]
  \\ qmatch_goalsub_abbrev_tac `(AppendMainLoop_code c,tt)`
  \\ first_x_assum (qspecl_then [`h'::t''`,`w`,`tt`] mp_tac)
  \\ fs [Abbr `tt`,lookup_insert]
  \\ qmatch_goalsub_abbrev_tac `(_ =+ a1) ((_ =+ a2) ((_ =+ a3) _))`
  \\ qpat_abbrev_tac `m5 = (_ =+ a1) ((_ =+ a2) ((_ =+ a3) _))`
  \\ `(one (next_free,a3) * one (next_free + bytes_in_word,a2) *
       one (next_free + 2w * bytes_in_word,a1) *
       word_list_exists (next_free + 3w * bytes_in_word)
         (3 * SUC (LENGTH t'')) * frame) (fun2set (m5,t.mdomain))` by
    (qunabbrev_tac `m5`
     \\ qabbrev_tac `mm = t.memory`
     \\ qabbrev_tac `dm = t.mdomain`
     \\ SEP_WRITE_TAC)
  \\ disch_then (qspec_then `(h,t.memory (a + bytes_in_word))::vars` mp_tac)
  \\ disch_then (qspec_then `k+3` mp_tac) \\ fs []
  \\ disch_then (qspec_then `one (next_free,a3) *
        one (next_free + bytes_in_word,a2) *
        one (next_free + 2w * bytes_in_word,a1) * frame` mp_tac)
  \\ disch_then (qspecl_then [`ts`,`Block ts' cons_tag [h'; ys']`] mp_tac)
  \\ impl_tac THEN1
   (fs [AC STAR_COMM STAR_ASSOC]
    \\ unabbrev_all_tac \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ fs [markerTheory.Abbrev_def]
    \\ reverse conj_tac THEN1
     (qpat_x_assum `_ ≤ sp` assume_tac
      \\ fs [LESS_EQ_EXISTS]
      \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB] \\ rveq)
    \\ `memory_rel c t.be ts s.refs sp t.store t.memory t.mdomain
         ((Block ts' cons_tag [h'; ys'],Word w)::(h,t.memory (a + bytes_in_word))::vars)`
       by (first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
          \\ rw [] \\ fs [])
    \\ drule (GEN_ALL memory_rel_write) \\ fs []
    \\ qmatch_goalsub_abbrev_tac `(_ =+ a1) ((_ =+ a2) ((_ =+ a3) _))`
    \\ disch_then (qspecl_then [`a3`,`k`] mp_tac)
    \\ impl_tac THEN1 fs [] \\ strip_tac
    \\ drule (GEN_ALL memory_rel_write) \\ fs []
    \\ disch_then (qspecl_then [`a2`,`k+1`] mp_tac)
    \\ impl_tac THEN1 fs [] \\ strip_tac
    \\ drule (GEN_ALL memory_rel_write) \\ fs []
    \\ disch_then (qspecl_then [`a1`,`k+2`] mp_tac)
    \\ impl_tac THEN1 fs [] \\ strip_tac
    \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])
  \\ strip_tac \\ fs[] \\ rfs []
  \\ `-3w * bytes_in_word + bytes_in_word * n2w (sp − k) =
      bytes_in_word * n2w (sp − (k + 3))` by
     (fs [LESS_EQ_EXISTS]
      \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB] \\ rveq)
  \\ fs[] \\ rfs [wordSemTheory.state_component_equality]
  \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ qexists_tac `a2 :: ws`
  \\ fs [append_writes_def]
  \\ conj_tac
  >- (drule_then match_mp_tac option_le_trans >>
      rw[size_of_stack_eq,option_le_max_right,option_le_max,option_map2_max_add,AC option_add_comm option_add_assoc,option_le_eq_eqns,option_map2_max_add,stack_size_eq])
  \\ IF_CASES_TAC THEN1 fs []
  \\ fs [WORD_MUL_LSL,word_mul_n2w,word_list_def,SEP_CLAUSES,
         AC STAR_COMM STAR_ASSOC]
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
  \\ fs [] \\ rw [] \\ fs []
QED

Definition STOP_def:
  STOP x = x
End

Theorem evaluate_AppendMainLoop_code_alt[local]:
  !xs ww (t:('a,'c,'ffi)wordSem$state) vars ptr hdr l k frame r1 r2 next_free ts v.
    memory_rel c t.be ts (s:('c,'ffi) dataSem$state).refs sp t.store t.memory t.mdomain
       ((v,Word ww)::vars) /\ xs <> [] /\
    v_to_list v = SOME xs /\
    lookup 10 t.locals = SOME (Word ptr) /\
    lookup 8 t.locals = SOME (Word (bytes_in_word * n2w (sp - k))) /\
    lookup 6 t.locals = SOME (Word hdr) /\
    lookup 4 t.locals = SOME (Word ww) /\
    lookup 2 t.locals = SOME (Word next_free) /\
    lookup 0 t.locals = SOME (Loc r1 r2) /\
    sp < k + 3 * LENGTH xs /\ good_dimindex (:'a) /\ k <= sp /\
    sp * (dimindex (:α) DIV 8) < dimword (:α) /\
    FLOOKUP t.store (Temp 0w) = SOME tmp0 /\
    FLOOKUP t.store (Temp 2w) = SOME tmp2 /\
    FLOOKUP t.store NextFree = SOME (Word f) /\
    Abbrev (next_free = f + bytes_in_word * n2w k) /\
    (?md. lookup AppendMainLoop_location t.code = SOME (6,AppendMainLoop_code c,md)) /\
    (?md. lookup AppendLenLoop_location t.code = SOME (3,AppendLenLoop_code c,md)) /\
    (word_list_exists next_free (sp - k) * frame)
       (fun2set (t.memory,t.mdomain)) /\ LENGTH xs <= t.clock ==>
    ?m1 ww2 smx.
      evaluate (AppendMainLoop_code c,t) =
        (case STOP evaluate (AppendLenLoop_code c,
            t with <| locals := fromList2 [Loc r1 r2; Word ww2; Word 0w] ;
                      locals_size := lookup AppendLenLoop_location t.stack_size;
                      memory := m1 ;
                      stack_max := smx ;
                      clock := t.clock - ((sp - k) DIV 3 + 1) |>) of
         | (res,s) => if bad_fun_return res then (SOME Error, s) else (res,s)) /\
      option_le (OPTION_MAP2 $+ (stack_size t.stack) (lookup AppendLenLoop_location t.stack_size)) smx /\
      option_le smx
        (OPTION_MAP2 MAX t.stack_max
           (OPTION_MAP2 $+ (stack_size t.stack)
           (OPTION_MAP2 MAX
              (lookup AppendLenLoop_location t.stack_size)
              (lookup AppendMainLoop_location t.stack_size))))/\
      memory_rel c t.be ts s.refs sp t.store m1 t.mdomain
       ((THE (block_drop ((sp - k) DIV 3) v),Word ww2)::vars)
Proof
  strip_tac
  \\ completeInduct_on `LENGTH xs` \\ fs [PULL_FORALL]
  \\ rpt strip_tac \\ rveq \\ fs []
  \\ Cases_on `xs` \\ fs [] \\ clean_tac
  \\ imp_res_tac memory_rel_arch_width
  \\ once_rewrite_tac [AppendMainLoop_code_def]
  \\ drule v_to_list_SOME_CONS_IMP \\ strip_tac
  \\ fs [] \\ rveq \\ fs []
  \\ drule memory_rel_Block_IMP \\ fs []
  \\ strip_tac \\ fs []
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def]
  \\ `get_var 4 t = SOME (Word ww)` by fs [wordSemTheory.get_var_def]
  \\ `shift_length c < dimindex (:α)` by
        fs [memory_rel_def,heap_in_memory_store_def]
  \\ rpt_drule0 get_var_get_real_addr_lemma \\ fs []
  \\ disch_then kall_tac
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [eq_eval,wordSemTheory.set_var_def]
  \\ rpt_drule0 memory_rel_Block_MEM
  \\ disch_then (qspec_then `0` mp_tac) \\ fs []
  \\ fs [get_real_offset_def,Smallnum_def]
  \\ strip_tac
  \\ drule memory_rel_swap \\ strip_tac
  \\ rpt_drule0 memory_rel_Block_MEM
  \\ disch_then (qspec_then `1` mp_tac) \\ fs []
  \\ `get_real_offset (Smallnum 1) = SOME (2w * bytes_in_word )` by
     (EVAL_TAC \\ fs [good_dimindex_def,dimword_def]) \\ fs []
  \\ strip_tac
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [eq_eval,wordSemTheory.set_var_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [eq_eval,wordSemTheory.set_var_def]
  \\ IF_CASES_TAC THEN1
   (`sp - k < 3` by
     (fs [good_dimindex_def,bytes_in_word_def]
      \\ rfs [dimword_def,word_mul_n2w,WORD_LO]
      \\ rewrite_tac [GSYM word_sub_def,addressTheory.word_arith_lemma2]
      \\ fs [LEFT_SUB_DISTRIB,LEFT_ADD_DISTRIB])
    \\ fs [LESS_DIV_EQ_ZERO]
    \\ qexists_tac `t.memory`
    \\ qexists_tac `ww`
    \\ qexists_tac `OPTION_MAP2 MAX t.stack_max
          (OPTION_MAP2 $+ (stack_size t.stack)
             (lookup AppendLenLoop_location t.stack_size)) `
    \\ qmatch_goalsub_abbrev_tac `STOP _ (_,ttt)`
    \\ qmatch_goalsub_abbrev_tac `AppendLenLoop_code c, ttt2`
    \\ `ttt2 = ttt` by
      (unabbrev_all_tac \\ fs [wordSemTheory.state_component_equality])
    \\ fs [STOP_def]
    \\ Cases_on `evaluate (AppendLenLoop_code c,ttt)` \\ fs []
    \\ reverse (Cases_on `q`) \\ fs [wordSemTheory.bad_fun_return_def]
    >- (qmatch_asmsub_rename_tac `_ = (SOME xx,_)` \\ Cases_on `xx`
        \\ fs [wordSemTheory.bad_fun_return_def]
        \\ (conj_tac >- simp[option_le_max_right]
            \\ conj_tac >-
              (simp[option_le_max]>>simp[option_le_max_right]>>
               simp[backendPropsTheory.option_le_eq_eqns,option_le_max_right])
            \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
            \\ fs [] \\ rw [] \\ fs [block_drop_def]))
    \\ (conj_tac >- simp[option_le_max_right]
    \\ conj_tac >-
      (simp[option_le_max]>>simp[option_le_max_right]>>
      simp[backendPropsTheory.option_le_eq_eqns,option_le_max_right])
    \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
    \\ fs [] \\ rw [] \\ fs [block_drop_def]))
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [eq_eval,wordSemTheory.set_var_def,wordSemTheory.mem_store_def]
  \\ fs [MULT_CLAUSES]
  \\ `k + 3 <= sp` by
     (fs [good_dimindex_def,bytes_in_word_def]
      \\ rfs [dimword_def,word_mul_n2w,WORD_LO]
      \\ rewrite_tac [GSYM word_sub_def,addressTheory.word_arith_lemma2]
      \\ fs [LEFT_SUB_DISTRIB,LEFT_ADD_DISTRIB])
  \\ `?x1 x2 x3.
       (one (next_free,x1) *
        one (next_free + bytes_in_word,x2) *
        one (next_free + 2w * bytes_in_word,x3) *
        word_list_exists (next_free + 3w * bytes_in_word) (sp - (k + 3)) * frame)
             (fun2set (t.memory,t.mdomain))` by
       (fs [word_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM]
        \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
        \\ Cases_on `xs` \\ fs []
        \\ Cases_on `t''` \\ fs []
        \\ Cases_on `t'''` \\ fs [ADD1,word_list_def]
        \\ qexists_tac `h'`
        \\ qexists_tac `h''`
        \\ qexists_tac `h'''`
        \\ qexists_tac `t''`
        \\ fs [AC STAR_COMM STAR_ASSOC])
  \\ SEP_R_TAC \\ fs []
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [eq_eval,wordSemTheory.set_var_def,wordSemTheory.mem_store_def]
  \\ SEP_R_TAC \\ fs []
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [eq_eval,wordSemTheory.set_var_def,wordSemTheory.mem_store_def]
  \\ Cases_on `t'`
  THEN1 (fs [v_to_list_EQ_SOME_NIL])
  \\ drule v_to_list_SOME_CONS_IMP \\ strip_tac
  \\ fs [] \\ rveq \\ fs []
  \\ rpt_drule0 memory_rel_Block_IMP
  \\ strip_tac \\ fs []
  \\ simp [asmTheory.word_cmp_def]
  \\ fs [SIMP_RULE (srw_ss()) [] word_and_one_eq_0_iff]
  \\ qmatch_goalsub_abbrev_tac `list_Seq test`
  \\ pop_assum kall_tac
  \\ rewrite_tac [list_Seq_def]
  \\ fs [eq_eval,wordSemTheory.set_var_def,wordSemTheory.mem_store_def]
  \\ SEP_R_TAC \\ fs [eq_eval,wordSemTheory.set_store_def]
  \\ qmatch_goalsub_abbrev_tac `(AppendMainLoop_code c,tt)`
  \\ first_x_assum (qspecl_then [`h'::t''`,`w`,`tt`] mp_tac)
  \\ fs [Abbr `tt`,lookup_insert]
  \\ qmatch_goalsub_abbrev_tac `(_ =+ a1) ((_ =+ a2) ((_ =+ a3) _))`
  \\ qpat_abbrev_tac `m5 = (_ =+ a1) ((_ =+ a2) ((_ =+ a3) _))`
  \\ `(one (next_free,a3) * one (next_free + bytes_in_word,a2) *
       one (next_free + 2w * bytes_in_word,a1) *
       word_list_exists (next_free + 3w * bytes_in_word)
         (sp − (k + 3)) * frame) (fun2set (m5,t.mdomain))` by
    (qunabbrev_tac `m5`
     \\ qabbrev_tac `mm = t.memory`
     \\ qabbrev_tac `dm = t.mdomain`
     \\ SEP_WRITE_TAC)
  \\ disch_then (qspec_then `(h,t.memory (a + bytes_in_word))::vars` mp_tac)
  \\ disch_then (qspec_then `k+3` mp_tac) \\ fs []
  \\ disch_then (qspec_then `one (next_free,a3) *
        one (next_free + bytes_in_word,a2) *
        one (next_free + 2w * bytes_in_word,a1) * frame` mp_tac)
  \\ disch_then (qspecl_then [`ts`,`Block ts'' cons_tag [h'; ys']`] mp_tac)
  \\ impl_tac THEN1
   (fs [AC STAR_COMM STAR_ASSOC]
    \\ unabbrev_all_tac \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ fs [markerTheory.Abbrev_def]
    \\ reverse conj_asm2_tac THEN1
     (fs [good_dimindex_def,bytes_in_word_def]
      \\ rfs [dimword_def,word_mul_n2w,WORD_LO]
      \\ rewrite_tac [GSYM word_sub_def,addressTheory.word_arith_lemma2]
      \\ fs [LEFT_SUB_DISTRIB,LEFT_ADD_DISTRIB])
    \\ `memory_rel c t.be ts s.refs sp t.store t.memory t.mdomain
         ((Block ts'' cons_tag [h'; ys'],Word w)::(h,t.memory (a + bytes_in_word))::vars)`
       by (first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
          \\ rw [] \\ fs [])
    \\ drule (GEN_ALL memory_rel_write) \\ fs []
    \\ qmatch_goalsub_abbrev_tac `(_ =+ a1) ((_ =+ a2) ((_ =+ a3) _))`
    \\ disch_then (qspecl_then [`a3`,`k`] mp_tac)
    \\ impl_tac THEN1 fs [] \\ strip_tac
    \\ drule (GEN_ALL memory_rel_write) \\ fs []
    \\ disch_then (qspecl_then [`a2`,`k+1`] mp_tac)
    \\ impl_tac THEN1 fs [] \\ strip_tac
    \\ drule (GEN_ALL memory_rel_write) \\ fs []
    \\ disch_then (qspecl_then [`a1`,`k+2`] mp_tac)
    \\ impl_tac THEN1 fs [] \\ strip_tac
    \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])
  \\ strip_tac \\ fs[] \\ rfs []
  \\ `-3w * bytes_in_word + bytes_in_word * n2w (sp − k) =
      bytes_in_word * n2w (sp − (k + 3))` by
     (fs [good_dimindex_def,bytes_in_word_def]
      \\ rfs [dimword_def,word_mul_n2w,WORD_LO]
      \\ rewrite_tac [GSYM word_sub_def,addressTheory.word_arith_lemma2]
      \\ fs [LEFT_SUB_DISTRIB,LEFT_ADD_DISTRIB])
  \\ fs[] \\ rfs [wordSemTheory.state_component_equality]
  \\ fs [ADD1]
  \\ qexists_tac `m1`
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac `smx`
  \\ qmatch_goalsub_abbrev_tac `STOP _ ttt`
  \\ Cases_on `STOP evaluate ttt` \\ fs []
  \\ qpat_x_assum `k + 3 ≤ sp` assume_tac
  \\ `((sp − k) DIV 3) = SUC ((sp − (k + 3)) DIV 3)` by
   (pop_assum (strip_assume_tac o REWRITE_RULE [LESS_EQ_EXISTS])
    \\ fs [ADD_DIV_EQ,ADD1])
  \\ fs [DROP] \\ fs [ADD1] \\ unabbrev_all_tac \\ fs []
  \\ qexists_tac `ww2` \\ fs []
  \\ reverse (Cases_on `q`) \\ fs [block_drop_def,wordSemTheory.bad_fun_return_def]
  >- (qmatch_asmsub_rename_tac `_ = (SOME xx,_)` \\ Cases_on `xx`
      \\ fs [wordSemTheory.bad_fun_return_def]
      \\ (conj_tac >-
          (match_mp_tac option_le_trans>> asm_exists_tac>>
           simp[option_le_max,option_le_max_right,option_le_eq_eqns]))
      \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
      \\ fs [] \\ rw [] \\ fs [block_drop_def]
      \\ disj1_tac \\ AP_TERM_TAC
      \\ qmatch_goalsub_abbrev_tac `block_drop (k1 + 1)`
      \\ `k1 + 1 = SUC k1` by fs []
      \\ once_asm_rewrite_tac [] \\ fs [block_drop_def])
  \\ (conj_tac >-
    (match_mp_tac option_le_trans>> asm_exists_tac>>
    simp[option_le_max,option_le_max_right,option_le_eq_eqns]))
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
  \\ fs [] \\ rw [] \\ fs [block_drop_def]
  \\ disj1_tac \\ AP_TERM_TAC
  \\ qmatch_goalsub_abbrev_tac `block_drop (k1 + 1)`
  \\ `k1 + 1 = SUC k1` by fs []
  \\ once_asm_rewrite_tac [] \\ fs [block_drop_def]
QED
val evaluate_AppendMainLoop_code_alt = evaluate_AppendMainLoop_code_alt
  |> SPEC_ALL |> Q.INST [`k`|->`0`]
  |> SIMP_RULE std_ss []
  |> GEN_ALL;

Theorem evaluate_AppendLenLoop_code[local]:
  !k (t:('a,'c,'ffi)wordSem$state) c xs l1 l2 (w:'a word) vars ts v.
    memory_rel c t.be ts refs sp t.store t.memory t.mdomain
      ((v,Word w)::vars) /\
    v_to_list v =  SOME xs /\
    lookup 0 t.locals = SOME (Loc l1 l2) /\
    lookup 2 t.locals = SOME (Word w) /\
    lookup 4 t.locals = SOME (Word (n2w (6 * k))) /\
    (?md. lookup AppendLenLoop_location t.code = SOME (3,AppendLenLoop_code c,md)) /\
    t.locals_size = lookup AppendLenLoop_location t.stack_size /\
    good_dimindex (:'a) /\
    LENGTH xs <= t.clock ==>
    ?locals smx.
      (case evaluate (AppendLenLoop_code c, t) of
        (res,s) => if bad_fun_return res then (SOME Error,s) else (res,s)) =
      (case evaluate (AppendLenLoop_code c,
              t with <| locals := locals;
                        clock := t.clock - LENGTH xs;
                        stack_max := smx
                      |>) of
        (res,s) => if bad_fun_return res then (SOME Error,s) else (res,s)) /\
      lookup 0 locals = SOME (Loc l1 l2) /\
      lookup 2 locals = SOME (Word 0w) /\
      lookup 4 locals = SOME (Word (n2w (6 * (k + LENGTH xs)))) /\
      option_le t.stack_max smx /\
      option_le smx (OPTION_MAP2 MAX t.stack_max
                      (OPTION_MAP2 $+ (stack_size t.stack)
                      (lookup AppendLenLoop_location t.stack_size)))
Proof
  Induct_on `xs` THEN1
   (fs [] \\ rw [] \\ qexists_tac `t.locals` \\ fs []
    \\ qexists_tac `t.stack_max`
    \\ `t with <|locals := t.locals; stack_max := t.stack_max; clock := t.clock|> = t`
          by fs [wordSemTheory.state_component_equality] \\ fs []
    \\ fs [v_to_list_EQ_SOME_NIL] \\ rveq
    \\ rw[option_le_max_right]
    \\ rpt_drule0 memory_rel_Block_IMP)
  \\ rw []
  \\ imp_res_tac memory_rel_arch_width
  \\ simp [Once AppendLenLoop_code_def]
  \\ drule v_to_list_SOME_CONS_IMP \\ strip_tac
  \\ fs [] \\ rveq \\ fs []
  \\ rpt_drule0 memory_rel_Block_IMP
  \\ strip_tac \\ fs[eq_eval]
  \\ fs [SIMP_RULE (srw_ss()) [] word_and_one_eq_0_iff]
  \\ `get_var 2 t = SOME (Word w)` by fs [wordSemTheory.get_var_def]
  \\ `shift_length c < dimindex (:α)` by
        fs [memory_rel_def,heap_in_memory_store_def]
  \\ rpt_drule0 get_var_get_real_addr_lemma \\ fs []
  \\ fs [eq_eval,list_Seq_def]
  \\ rpt_drule0 memory_rel_Block_MEM
  \\ disch_then (qspec_then `1` mp_tac) \\ fs []
  \\ `get_real_offset (Smallnum 1) = SOME (2w * bytes_in_word )` by
     (EVAL_TAC \\ fs [good_dimindex_def,dimword_def]) \\ fs []
  \\ fs [eq_eval] \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac `(AppendLenLoop_code c,ttt)`
  \\ first_x_assum (qspecl_then [`k+1`,`ttt`,`c`] mp_tac)
  \\ fs [Abbr`ttt`,eq_eval]
  \\ `?xx. t.memory (a + 2w * bytes_in_word) = Word xx` by
     (Cases_on `xs` \\ fs [v_to_list_def,v_to_list_EQ_SOME_NIL] \\ rveq
      \\ TRY (drule v_to_list_SOME_CONS_IMP \\ strip_tac)
      \\ fs [] \\ rveq \\ fs []
      \\ rpt_drule0 memory_rel_Block_IMP \\ fs [] \\ rw [] \\ fs [])
  \\ disch_then (qspecl_then [`xx`,`vars`,`ts`,`ys`] mp_tac)
  \\ impl_tac THEN1
   (fs [LEFT_ADD_DISTRIB,word_add_n2w]
    \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
    \\ fs [] \\ rw [] \\ fs [])
  \\ strip_tac \\ fs []
  \\ fs [LEFT_ADD_DISTRIB,word_add_n2w]
  \\ rw []
  \\ qexists_tac `locals` \\ fs []
  \\ qexists_tac `smx` \\ fs[]
  \\ fs [LEFT_ADD_DISTRIB,word_add_n2w,ADD1]
  \\ qmatch_goalsub_abbrev_tac `(AppendLenLoop_code c,ttt)`
  \\ Cases_on `evaluate (AppendLenLoop_code c,ttt)`
  \\ Cases_on `q` \\ fs []
  >- ((* NONE branch *)
      rfs []
      \\ qmatch_goalsub_abbrev_tac `(AppendLenLoop_code c,tttt)`
      \\ `tttt = ttt` by(fs[Abbr`tttt`,Abbr`ttt`,wordSemTheory.state_component_equality])
      \\ fs [option_le_max,wordSemTheory.bad_fun_return_def])
  \\ Cases_on `x` \\ fs [wordSemTheory.bad_fun_return_def]
  \\ rfs[]
  \\ qmatch_goalsub_abbrev_tac `(AppendLenLoop_code c,tttt)`
  \\ `tttt = ttt` by(fs[Abbr`tttt`,Abbr`ttt`,wordSemTheory.state_component_equality])
  \\ fs[option_le_max]
QED
val evaluate_AppendLenLoop_code = evaluate_AppendLenLoop_code
  |> Q.SPEC `0` |> SIMP_RULE std_ss [] |> Q.GEN `refs`;

Theorem v_to_list_block_drop:
  ∀k v l.
   v_to_list v = SOME l ∧ k < LENGTH l
   ⇒ v_to_list (THE (block_drop k v)) = SOME (DROP k l)
Proof
  Induct \\ rw [block_drop_def]
  \\ Cases_on `l` \\ fs []
  \\ drule v_to_list_SOME_CONS_IMP \\ strip_tac
  \\ fs [] \\ rveq \\ fs [block_drop_def]
QED

(* TODO: move *)

Theorem option_le_flip_neg:
  ~option_le a b ==> option_le b a
Proof
  Cases_on `a` >> Cases_on `b` >> rw[]
QED

Theorem assign_ListAppend:
  op = BlockOp ListAppend ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ imp_res_tac state_rel_arch_width \\ imp_res_tac state_rel_small_shift_length \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ `option_le x.stack_max s2.stack_max` by metis_tac[do_app_stack_max]
  \\ rpt_drule0 state_rel_cut_IMP \\ strip_tac
  \\ fs [assign_def] \\ rveq
  \\ fs [dataLangTheory.op_requires_names_def,
         dataLangTheory.op_space_reset_def,cut_state_opt_def]
  \\ Cases_on `names_opt` \\ fs []
  \\ drule_all (state_rel_cut_state_opt_SOME |> SRULE [cut_state_opt_def])
  \\ strip_tac
  \\ qpat_x_assum `_ (t with locals := y) NONE locs` $ ASSUME_NAMED_TAC "with_locals"
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app,allowed_op_def]
  \\ `?r1 r2. vals = [r1;r2]` by
     (Cases_on `vals` \\ fs [] \\ Cases_on `t'` \\ fs [] \\ Cases_on `t''` \\ fs [])
  \\ rveq \\ fs []
  \\ Cases_on `v_to_list r1` \\ fs []
  \\ Cases_on `v_to_list r2` \\ fs []
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ `?v1 v2. args = [v1; v2]` by
       (Cases_on `args` \\ fs [] \\ Cases_on `t'` \\ fs []) \\ rveq \\ fs []
  \\ Cases_on `encode_header c 0 2` \\ fs []
  >- (
    conj_tac >-
      (drule_then match_mp_tac option_le_trans >>
       fs[with_fresh_ts_def,CaseEq"option",check_lim_def,opt_map_plus_zero_id] >>
       rveq >> simp[] >>
       FULL_SIMP_TAC std_ss [state_rel_def,option_le_max_right]) >>
    strip_tac >>
    `good_dimindex(:'a)` by metis_tac[state_rel_def] >>
    `c.len_size = x.limits.length_limit` by
      fs [state_rel_thm,limits_inv_def] >>
    `arch_width_bits c.arch_width = dimindex (:'a)` by
      fs [state_rel_def,heap_in_memory_store_def] >>
    fs[good_dimindex_def,encode_header_def,dimword_def] >> fs[] >>
    spose_not_then strip_assume_tac >>
    fs[with_fresh_ts_def,CaseEq"option"] >> rveq >> fs[check_lim_def] >>
    gvs [state_rel_thm]
    >> LABEL_ASSUM "with_locals" (assume_tac o REWRITE_RULE [state_rel_thm])
    >> gvs []
  )
  \\ rename1 `v_to_list r1 = SOME in1` \\ rename1 `v_to_list r2 = SOME in2`
  \\ `get_var (adjust_var v1) t = SOME a1 /\ get_var (adjust_var v2) t = SOME a2`
       by fs[wordSemTheory.get_vars_def,CaseEq"option"]
  \\ fs [wordSemTheory.evaluate_def,domain_adjust_sets]
  \\ fs [wordSemTheory.get_vars_def,wordSemTheory.bad_dest_args_def,
         wordSemTheory.add_ret_loc_def,wordSemTheory.find_code_def]
  \\ `(?md. lookup Append_location t.code = SOME (3, Append_code c,md))` by
       fs [state_rel_thm,code_rel_def,stubs_md_def,stubs_def,MAP_MAP_o,o_DEF]
  \\ fs []
  \\ fs [get_names_def]
  \\ drule cut_env_IMP_cut_envs \\ strip_tac \\ fs []
  \\ simp [Append_code_def] \\ simp [wordSemTheory.evaluate_def]
  \\ fs [wordSemTheory.get_var_imm_def]
  \\ simp [EVAL ``get_var 4 (call_env [Loc n l; a2; a1] (lookup Append_location t.stack_size) st)``]
  \\ simp [EVAL ``get_var 2 (call_env [Loc n l; a2; a1] (lookup Append_location t.stack_size) st)``]
  \\ simp [EVAL ``get_var 0 (call_env [Loc n l; a2; a1] (lookup Append_location t.stack_size) st)``]
  \\ Cases_on `in1` \\ fs [v_to_list_SOME_NIL_IFF]
  >- (
    rveq \\ fs []
    \\ qpat_x_assum `state_rel c l1 l2 s t NONE locs` mp_tac
    \\ simp [Once state_rel_thm,option_le_max_right] \\ strip_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ drule (GEN_ALL memory_rel_get_vars_IMP) \\ disch_then drule
    \\ fs [wordSemTheory.get_vars_def]
    \\ fs [SIMP_RULE (srw_ss()) [] word_and_one_eq_0_iff] \\ strip_tac
    \\ drule memory_rel_Block_IMP \\ fs [] \\ strip_tac \\ rveq \\ fs []
    \\ `(1w && (n2w (2 * nil_tag)):'a word) = 0w` by
         (simp [EVAL ``nil_tag``]) \\ fs []
    \\ simp [asmTheory.word_cmp_def]
    \\ simp [wordSemTheory.dec_clock_def, wordSemTheory.push_env_def]
    \\ Cases_on `env_to_list y2 t.permute` \\ fs []
    \\ simp [wordSemTheory.call_env_def, wordSemTheory.pop_env_def,lookup_insert,
             wordSemTheory.get_var_def,fromList2_def]
    \\ reverse IF_CASES_TAC
    >- (sg `F` \\ fs [] \\ pop_assum mp_tac \\ simp []
        \\ imp_res_tac env_to_list_domain
        \\ simp [domain_union,domain_fromAList_toAList,AC UNION_COMM UNION_ASSOC])
    >- (
      fs [wordSemTheory.set_var_def,set_var_def]
      \\ fs [state_rel_thm]
      \\ fs [lookup_insert,adjust_var_11, call_env_def,with_fresh_ts_def,
             wordSemTheory.set_vars_def,alist_insert_def,
             push_env_def,set_var_def,wordSemTheory.set_var_def,IS_SOME_EXISTS]
      \\ fs [] \\ rveq \\ fs [list_to_v_def]
      \\ simp[option_le_max_right, check_lim_def, wordSemTheory.flush_state_def, allowed_op_def]
      \\ qmatch_goalsub_rename_tac `memory_rel _ _ ts1 _ _ _ _ _ _`
      \\ conj_tac THEN1
         (simp [lookup_union,lookup_fromAList,ALOOKUP_toAList]
          \\ drule_all cut_envs_lookup_0 \\ simp [])
      \\ conj_tac THEN1
         (gen_tac \\ IF_CASES_TAC \\ simp [] \\ fs [lookup_fromAList]
          \\ `cut_env x' s.locals = SOME x.locals` by
               (qpat_x_assum `cut_state x' s = SOME x` mp_tac
                \\ simp [dataSemTheory.cut_state_def,AllCaseEqs()] \\ rw [] \\ fs [])
          \\ asm_rewrite_tac [GSYM IS_SOME_EXISTS, IS_SOME_lookup_domain]
          \\ simp [domain_union, domain_fromAList, sptreeTheory.MEM_toAList] \\ rw []
          \\ `n ∈ domain x.locals` by (simp [domain_lookup] \\ metis_tac [])
          \\ disj2_tac \\ drule_all cut_envs_domain_IN \\ simp [])
      \\ conj_tac THEN1
         (fs[size_of_stack_eq,option_le_max_right,option_le_max,option_map2_max_add,
             AC option_add_comm option_add_assoc,option_le_eq_eqns,stack_size_eq,
             opt_map_plus_zero_id] >>
          FULL_SIMP_TAC bool_ss [state_rel_def] >>
          imp_res_tac stack_rel_IMP_size_of_stack >> simp[option_le_add] >>
          metis_tac[option_le_flip_neg,option_le_trans])
      \\ conj_tac THEN1
         (fs[size_of_stack_eq,option_le_max_right,option_le_max,option_map2_max_add,
             AC option_add_comm option_add_assoc,option_le_eq_eqns,stack_size_eq,
             opt_map_plus_zero_id] >>
          FULL_SIMP_TAC bool_ss [state_rel_def] >>
          imp_res_tac stack_rel_IMP_size_of_stack >> simp[option_le_add] >>
          metis_tac[option_le_flip_neg,option_le_trans])
      >- (
        `x.refs = s.refs ∧ x.global = s.global ∧ x.stack = s.stack ∧ x.tstamps = s.tstamps` by
           (qpat_x_assum `cut_state x' s = SOME x` mp_tac
            \\ rpt (pop_assum kall_tac)
            \\ simp [cut_state_def,CaseEq"option"] \\ strip_tac \\ rveq \\ simp [])
        \\ `cut_env x' s.locals = SOME x.locals` by
           (qpat_x_assum `cut_state x' s = SOME x` mp_tac
            \\ rpt (pop_assum kall_tac)
            \\ simp [cut_state_def,CaseEq"option"] \\ strip_tac \\ rveq \\ fs [])
        \\ `ts1 = THE s.tstamps` by fs []
        \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
        \\ match_mp_tac memory_rel_insert \\ fs [flat_def]
        \\ qpat_x_assum `memory_rel _ _ _ _ _ _ _ _ ((Block_nil,_)::_)` assume_tac
        \\ drule memory_rel_tl \\ strip_tac
        \\ drule (GEN_ALL memory_rel_less_space)
        \\ disch_then (qspec_then `0` mp_tac) \\ fs [] \\ strip_tac
        \\ pop_assum mp_tac \\ match_mp_tac memory_rel_rearrange \\ rw [] \\ fs []
        \\ disj2_tac \\ disj1_tac \\ disj1_tac
        \\ `∀k v. lookup k x.locals = SOME v ⇒ lookup k s.locals = SOME v` by
             (`x.locals = mk_wf (inter s.locals x')` by
                (qpat_x_assum `cut_env x' s.locals = SOME x.locals` mp_tac
                 \\ rpt (pop_assum kall_tac)
                 \\ simp [dataSemTheory.cut_env_def, AllCaseEqs()] \\ metis_tac [])
              \\ asm_rewrite_tac []
              \\ simp [lookup_mk_wf, lookup_inter_alt, AllCaseEqs()])
        \\ `∀k v. lookup k (union (fromAList q) (fromAList (toAList y1))) = SOME v ⇒
                  lookup k t.locals = SOME v` by
             (rpt gen_tac
              \\ drule env_to_list_lookup_equiv \\ strip_tac
              \\ qpat_x_assum `cut_envs (adjust_sets x') t.locals = SOME (y1,y2)` mp_tac
              \\ simp [wordSemTheory.cut_envs_def, AllCaseEqs(), wordSemTheory.cut_names_def]
              \\ strip_tac \\ rveq
              \\ simp [lookup_union, lookup_fromAList, ALOOKUP_toAList]
              \\ rw [] \\ gvs [lookup_inter_alt, AllCaseEqs()])
        \\ drule_at (Pos last) join_env_submap_MEM \\ simp []
        \\ disch_then irule \\ rw [] \\ res_tac \\ simp []
      )
    )
  )
  \\ rename1 `v_to_list r1 = SOME (i1::in1)`
    \\ `?ww. a1 = Word ww /\ (1w && ww) <> 0w` by
       (imp_res_tac v_to_list_SOME_CONS_IMP \\ rveq \\ fs []
        \\ qpat_x_assum `state_rel c l1 l2 s t NONE locs` mp_tac
        \\ simp [Once state_rel_thm,option_le_max_right] \\ strip_tac
        \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
        \\ drule (GEN_ALL memory_rel_get_vars_IMP)
        \\ disch_then drule
        \\ fs [wordSemTheory.get_vars_def]
        \\ fs [SIMP_RULE (srw_ss()) [] word_and_one_eq_0_iff]
        \\ strip_tac \\ drule memory_rel_Block_IMP \\ fs []
        \\ strip_tac \\ rveq \\ fs [])
    \\ fs []
    \\ simp [wordSemTheory.push_env_def,wordSemTheory.dec_clock_def,
             wordSemTheory.flush_state_def]
    \\ Cases_on `env_to_list y2 t.permute` \\ fs []
    \\ simp [wordSemTheory.call_env_def,fromList2_def]
    \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def]
    \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def]
    \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def,
             wordSemTheory.get_store_def,FLOOKUP_UPDATE]
    \\ `?next_free trig_gc curr.
           FLOOKUP t.store NextFree = SOME (Word next_free) /\
           FLOOKUP t.store TriggerGC = SOME (Word trig_gc) /\
           FLOOKUP t.store CurrHeap = SOME (Word curr)` by
          fs [state_rel_thm,memory_rel_def,heap_in_memory_store_def]
    \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def,FLOOKUP_UPDATE,
             wordSemTheory.get_store_def]
    \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def,FLOOKUP_UPDATE,
             wordSemTheory.get_store_def]
    \\ `shift_length c - shift (dimindex (:'a)) < dimword (:'a)` by
         (assume_tac dimindex_lt_dimword \\
          `shift_length c < dimindex (:'a)` suffices_by decide_tac \\
          fs [state_rel_thm,memory_rel_def,heap_in_memory_store_def])
    \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def,FLOOKUP_UPDATE,
             wordSemTheory.word_sh_def,wordSemTheory.get_store_def]
    \\ IF_CASES_TAC THEN1
       (sg `F` \\ fs []
        \\ fs [state_rel_thm,memory_rel_def,heap_in_memory_store_def])
    \\ simp []
    \\ qpat_x_assum `~(_ /\ _)` kall_tac
    \\ qmatch_goalsub_abbrev_tac `insert 7 (Word init_ptr)`
    \\ simp [list_Seq_def,eq_eval,wordSemTheory.set_store_def]
    \\ `(?md. lookup AppendMainLoop_location t.code = SOME (6,AppendMainLoop_code c,md))` by
         fs [state_rel_thm,code_rel_def,stubs_md_def,stubs_def,MAP_MAP_o,o_DEF] \\ fs []
    \\ rename1 `encode_header c 0 2 = SOME hdr`
    \\ qpat_x_assum `state_rel c l1 l2 s t NONE locs` mp_tac
    \\ simp [Once state_rel_thm,option_le_max_right] \\ strip_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ drule (GEN_ALL memory_rel_get_vars_IMP)
    \\ disch_then drule
    \\ fs [wordSemTheory.get_vars_def] \\ strip_tac
    \\ drule memory_rel_space_max
    \\ simp [] \\ strip_tac \\ fs []
    \\ drule (GEN_ALL memory_rel_IMP_word_list_exists) \\ fs []
    \\ disch_then (qspec_then `sp` mp_tac) \\ fs [] \\ strip_tac
    \\ Cases_on `3 * LENGTH (i1::in1) <= sp`
    >- (
      `cut_env x' s.locals = SOME x.locals` by
         (qpat_x_assum `cut_state x' s = SOME x` mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ simp [cut_state_def,CaseEq"option"] \\ strip_tac \\ rveq \\ fs [])
      \\ assume_tac (GEN_ALL evaluate_AppendMainLoop_code)
      \\ SEP_I_TAC "evaluate"
      \\ fs [lookup_insert]
      \\ pop_assum drule \\ fs [FLOOKUP_UPDATE]
      \\ disch_then (qspec_then `0` mp_tac)
      \\ simp [markerTheory.Abbrev_def]
      \\ disch_then (qspec_then `SEP_T` mp_tac)
      \\ impl_tac THEN1
       (
        reverse conj_tac THEN1
         (match_mp_tac LESS_EQ_TRANS
          \\ qexists_tac `dimword (:'a) - 2` \\ fs []
          \\ fs [wordSemTheory.MustTerminate_limit_def]
          \\ fs [good_dimindex_def,dimword_def] \\ rfs [])
        \\ fs [LESS_EQ_EXISTS] \\ rveq
        \\ qpat_x_assum `(word_list_exists _ _ * SEP_T) _` mp_tac
        \\ once_rewrite_tac [ADD_COMM]
        \\ rewrite_tac [word_list_exists_ADD,GSYM STAR_ASSOC]
        \\ once_rewrite_tac [STAR_def] \\ fs [FUN_EQ_THM]
        \\ strip_tac \\ asm_exists_tac \\ fs [SEP_T_def])
      \\ strip_tac \\ fs []
      \\ fs [wordSemTheory.pop_env_def]
      \\ reverse IF_CASES_TAC THEN1
       (sg `F` \\ fs [] \\ pop_assum mp_tac \\ simp []
        \\ imp_res_tac env_to_list_domain
        \\ simp [domain_union,domain_fromAList_toAList,AC UNION_COMM UNION_ASSOC])
      \\ fs []
      \\ fs [wordSemTheory.set_var_def,set_var_def,
             wordSemTheory.set_vars_def,alist_insert_def]
      \\ fs [state_rel_thm]
      \\ fs [lookup_insert,adjust_var_11, IS_SOME_EXISTS,
             call_env_def,push_env_def, with_fresh_ts_def,
             dataSemTheory.set_var_def,wordSemTheory.set_var_def, check_lim_def]
      \\ fs [] \\ rveq \\ fs []
      >- (
        strip_tac THEN1
          fs [code_oracle_rel_def, FLOOKUP_UPDATE]
        \\ strip_tac THEN1
         (simp [lookup_union,lookup_fromAList,ALOOKUP_toAList]
          \\ drule_all cut_envs_lookup_0 \\ simp [])
        \\ conj_tac THEN1
         (qx_gen_tac `kk` \\ IF_CASES_TAC \\ simp [] \\ fs [lookup_fromAList]
          \\ asm_rewrite_tac [GSYM IS_SOME_EXISTS,IS_SOME_lookup_domain]
          \\ rw[] \\ `kk ∈ domain x.locals` by (simp [domain_lookup] \\ metis_tac [])
          \\ drule_all cut_envs_domain_IN \\ simp [])
        \\ conj_tac >-
          (drule evaluate_stack_max>>simp[]>>
          qmatch_goalsub_abbrev_tac`option_CASE sm1`>>
          strip_tac>>
          `option_le sm1 smx` by
            (Cases_on`sm1`>>Cases_on`smx`>>fs[miscTheory.the_def])>>
          `option_le t.stack_max sm1` by
            (fs[Abbr`sm1`]>>
            simp[option_le_max_right])>>
          metis_tac[option_le_trans])
        \\ conj_tac >-
          (
            drule_then match_mp_tac option_le_trans >>
            fsrw_tac [] [state_rel_def] >>
            imp_res_tac stack_rel_IMP_size_of_stack >>
            rw[size_of_stack_eq,option_le_max_right,option_le_max,option_map2_max_add,AC option_add_comm option_add_assoc,option_le_eq_eqns,option_map2_max_add,stack_size_eq,option_le_add]
          )
        \\ conj_tac >- (
          `x.limits = s.limits` by
            (qpat_x_assum `cut_state x' s = SOME x` mp_tac \\ rpt (pop_assum kall_tac)
             \\ simp [cut_state_def,CaseEq"option"] \\ strip_tac \\ rveq \\ simp [])
          \\ qhdtm_x_assum `limits_inv` mp_tac
          \\ simp[limits_inv_def,FLOOKUP_UPDATE])
        >- (
          fs [memory_rel_Temp,
               MATCH_MP FUPDATE_COMMUTES (prove(``Temp p <> NextFree``,EVAL_TAC))]
          \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
          \\ match_mp_tac memory_rel_insert \\ fs [flat_def]
          \\ simp [FAPPLY_FUPDATE_THM]
          \\ qmatch_asmsub_abbrev_tac `memory_rel _ _ _ _ _ _ _ _ (A ++ B::C)`
          \\ sg `memory_rel c t.be (THE s.tstamps) s.refs sp t.store m1 t.mdomain ((B::A) ++ C)`
          >- (irule memory_rel_rearrange \\ HINT_EXISTS_TAC \\ rw [] \\ fs [])
          \\ map_every qunabbrev_tac [`A`,`B`,`C`]
          \\ drule memory_rel_append
          \\ simp [make_cons_ptr_def]
          \\ impl_keep_tac
          >- (fs [Abbr`init_ptr`, get_lowerbits_def, make_header_def, encode_header_def] \\ gvs [])
          \\ strip_tac
          \\ drule (GEN_ALL memory_rel_less_space)
          \\ disch_then (qspec_then `0` mp_tac) \\ fs []
          \\ `x.refs = s.refs ∧ x.global = s.global ∧ x.stack = s.stack ∧ x.tstamps = s.tstamps` by
               (qpat_x_assum `cut_state x' s = SOME x` mp_tac \\ rpt (pop_assum kall_tac)
                \\ simp [cut_state_def,CaseEq"option"] \\ strip_tac \\ rveq \\ simp [])
          \\ `cut_env x' s.locals = SOME x.locals` by
               (qpat_x_assum `cut_state x' s = SOME x` mp_tac \\ rpt (pop_assum kall_tac)
                \\ simp [cut_state_def,CaseEq"option"] \\ strip_tac \\ rveq \\ fs [])
          \\ gvs []
          \\ strip_tac
          \\ qpat_x_assum `Abbrev (init_ptr = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])
          \\ pop_assum SUBST_ALL_TAC
          \\ pop_assum mp_tac \\ match_mp_tac memory_rel_rearrange \\ rw [] \\ fs []
          >- (disj1_tac \\ rewrite_tac [get_lowerbits_def]
              \\ metis_tac [WORD_OR_ASSOC, WORD_OR_COMM, WORD_OR_IDEM])
          \\ disj2_tac \\ disj1_tac \\ disj1_tac
          \\ `∀k v. lookup k x.locals = SOME v ⇒ lookup k s.locals = SOME v` by
               (`x.locals = mk_wf (inter s.locals x')` by
                  (qpat_x_assum `cut_env x' s.locals = SOME x.locals` mp_tac
                   \\ rpt (pop_assum kall_tac)
                   \\ simp [dataSemTheory.cut_env_def, AllCaseEqs()] \\ metis_tac [])
                \\ asm_rewrite_tac []
                \\ simp [lookup_mk_wf, lookup_inter_alt, AllCaseEqs()])
          \\ `∀k v. lookup k (union (fromAList q) (fromAList (toAList y1))) = SOME v ⇒
                    lookup k t.locals = SOME v` by
               (rpt gen_tac
                \\ drule env_to_list_lookup_equiv \\ strip_tac
                \\ qpat_x_assum `cut_envs (adjust_sets x') t.locals = SOME (y1,y2)` mp_tac
                \\ simp [wordSemTheory.cut_envs_def, AllCaseEqs(), wordSemTheory.cut_names_def]
                \\ strip_tac \\ rveq
                \\ simp [lookup_union, lookup_fromAList, ALOOKUP_toAList]
                \\ rw [] \\ gvs [lookup_inter_alt, AllCaseEqs()])
          \\ drule_at (Pos last) join_env_submap_MEM \\ simp []
          \\ disch_then irule \\ rw [] \\ res_tac \\ simp []
        )
      )
    )
    \\ assume_tac (GEN_ALL evaluate_AppendMainLoop_code_alt)
      \\ SEP_I_TAC "evaluate"
      \\ fs [lookup_insert,FLOOKUP_UPDATE]
      \\ pop_assum drule
      \\ rewrite_tac [markerTheory.Abbrev_def]
      \\ simp []
      \\ disch_then (qspec_then `SEP_T` mp_tac)
      \\ impl_tac THEN1
       (conj_tac THEN1 fs [stubs_md_def,stubs_def,MAP_MAP_o,o_DEF,code_rel_def]
        \\ conj_tac THEN1 fs []
        \\ match_mp_tac LESS_EQ_TRANS
        \\ qexists_tac `dimword (:'a) - 2` \\ fs []
        \\ fs [wordSemTheory.MustTerminate_limit_def]
        \\ drule (GEN_ALL memory_rel_list_limit)
        \\ fs [good_dimindex_def,dimword_def] \\ rfs [])
      \\ strip_tac \\ fs []
      \\ qpat_x_assum `evaluate (AppendMainLoop_code c,_) = _` kall_tac
      \\ simp [STOP_def]
      \\ qmatch_goalsub_abbrev_tac `(AppendLenLoop_code c,ttt)`
      \\ qspecl_then [`s.refs`,`ttt`,`c`,`(DROP (sp DIV 3) (i1::in1))`]
               mp_tac evaluate_AppendLenLoop_code
      \\ fs [Abbr`ttt`,eq_eval]
      \\ disch_then drule
      \\ impl_tac THEN1
       (conj_tac >- fs [v_to_list_block_drop,NOT_LESS_EQUAL,multiwordTheory.DIV_thm2]
        \\ fs [stubs_md_def,stubs_def,MAP_MAP_o,o_DEF,code_rel_def]
        \\ imp_res_tac memory_rel_list_limit
        \\ `2 * dimword (:'a) <= MustTerminate_limit (:α)` by
          fs [wordSemTheory.MustTerminate_limit_def]
        \\ rfs [good_dimindex_def,dimword_def] \\ rfs [] \\ fs [])
      \\ strip_tac \\ fs []
      \\ rpt (qpat_x_assum `lookup _ _ = _` mp_tac)
      \\ rpt strip_tac
      \\ sg `state_rel c l1 l2 ((s with <| locals := s.locals ; space := sp ; stack_max :=
              OPTION_MAP2 MAX s.stack_max
                     (OPTION_MAP2 $+
                        (OPTION_MAP2 MAX
                           (lookup Append_location s.stack_frame_sizes)
                           (OPTION_MAP2 MAX
                              (lookup AppendLenLoop_location s.stack_frame_sizes)
                              (lookup AppendMainLoop_location s.stack_frame_sizes)))
                        (OPTION_MAP2 $+ (size_of_stack s.stack) s.locals_size))|>)
              with clock := s.clock + 1)
           ((t with <| clock := t.clock + 1;
            store :=
            t.store |+ (Temp 0w,a2) |+ (Temp 1w,Word ww) |+
             (Temp 2w,Word init_ptr) |>) with memory := m1) NONE locs`
      >- (
        fs [state_rel_thm,FAPPLY_FUPDATE_THM]
          \\ conj_tac >- fs [code_oracle_rel_def, FLOOKUP_UPDATE]
          \\ conj_tac >- (qpat_x_assum `s.locals_size = x.locals_size` (fn th => fs [GSYM th]))
          \\ conj_tac >- metis_tac [option_le_trans, option_le_max_right]
          \\ conj_tac >- (qhdtm_x_assum `limits_inv` mp_tac \\ simp [FLOOKUP_UPDATE])
          \\ qpat_x_assum `memory_rel _ _ _ _ _ _ _ _ ((THE (block_drop _ _),_)::_)` assume_tac
          \\ drule memory_rel_tl \\ strip_tac \\ drule memory_rel_tl \\ strip_tac
          \\ pop_assum mp_tac \\ match_mp_tac memory_rel_rearrange \\ rw [] \\ fs []
      )
      \\ simp [AppendLenLoop_code_def,Once list_Seq_def]
        \\ fs [eq_eval,FLOOKUP_UPDATE]
        \\ simp [Once list_Seq_def,eq_eval]
        \\ simp [Once word_exp_ShiftVar_bits] \\ fs [eq_eval]
        \\ simp [Once list_Seq_def,eq_eval,FLOOKUP_UPDATE,wordSemTheory.get_store_def]
        \\ simp [Once list_Seq_def,eq_eval,FLOOKUP_UPDATE,wordSemTheory.get_store_def]
        \\ simp [Once list_Seq_def,eq_eval,FLOOKUP_UPDATE,wordSemTheory.get_store_def]
        \\ qmatch_goalsub_abbrev_tac `AllocVar _ ll ss,tt`
        \\ Cases_on `evaluate (AllocVar c ll ss,tt)`
        \\ rename1 `_ = (aa1,aa2)`
        \\ drule (AllocVar_thm
              |> ONCE_REWRITE_RULE [METIS_PROVE []
                   ``x1/\x2/\x3/\x4/\x5<=>x4/\x1/\x2/\x3/\x5``]
              |> GEN_ALL)
        \\ drule (state_rel_call_env_push_env |> Q.SPEC `NONE`
             |> SIMP_RULE std_ss [] |> Q.GENL
                 [`args`,`c`,`y`,`xs`,`x`,`ws`,`t`,`s`,`r`,`q`,`locs`,`l2`,`l1`,`l`])
        \\ `(dec_clock (s with clock := s.clock + 1)) = s` by
                fs [wordSemTheory.state_component_equality,wordSemTheory.dec_clock_def,
                    dataSemTheory.state_component_equality,dataSemTheory.dec_clock_def]
        \\ fs []
        \\ pop_assum kall_tac
        \\ disch_then drule
        \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def]
        \\ `dataSem$cut_env x' s.locals = SOME x.locals` by
             (qpat_x_assum `cut_state x' s = SOME x` mp_tac \\ rpt (pop_assum kall_tac)
              \\ simp [dataSemTheory.cut_state_def,CaseEq"option"] \\ strip_tac \\ rveq \\ fs [])
        \\ disch_then drule
        \\ disch_then drule
        \\ disch_then (qspecl_then [`lookup AppendLenLoop_location s.stack_frame_sizes`,
                                     `n`,`l`] assume_tac)
        \\ qmatch_assum_abbrev_tac `state_rel c n l s3 _ _ _`
        \\ `state_rel c n l (s3 with clock := tt.clock) tt NONE ((l1,l2)::locs)` by
         (qpat_x_assum ‘_ ((l1,l2)::locs)’ mp_tac
          \\ qunabbrev_tac `s3`
          \\ simp [call_env_def,wordSemTheory.call_env_def,push_env_def,
                   wordSemTheory.push_env_def,Abbr`tt`]
          \\ fs [eq_eval,FAPPLY_FUPDATE_THM,state_rel_thm,
                 wordSemTheory.dec_clock_def,dataSemTheory.dec_clock_def]
          \\ strip_tac
          \\ conj_tac THEN1
           (fs [fromList_def,lookup_insert] \\ rw []
            \\ fs [adjust_var_def,lookup_def])
          \\ conj_tac >-
            (match_mp_tac option_le_trans>>
            qexists_tac`smx`>>simp[]>>
            match_mp_tac option_le_trans>>
            simp[CONJ_COMM]>>
            asm_exists_tac>>simp[])
          \\ conj_tac >-
            (drule_then match_mp_tac option_le_trans >>
             imp_res_tac stack_rel_IMP_size_of_stack >>
             fs[dataSemTheory.dec_clock_def,size_of_stack_eq,stack_size_eq] >>
             qpat_x_assum `option_le smx (_ _ _)` mp_tac >>
             rw[size_of_stack_eq,option_le_max_right,option_le_max,option_map2_max_add,
                AC option_add_comm option_add_assoc,option_le_eq_eqns,
                option_map2_max_add,stack_size_eq] >>
             rw[] >> metis_tac[option_le_trans])
          \\ pop_assum mp_tac
          \\ match_mp_tac memory_rel_rearrange
          \\ fs [] \\ rw [] \\ fs []
          \\ rpt disj1_tac
          \\ pop_assum mp_tac
          \\ match_mp_tac (METIS_PROVE [] ``x = y ==> f x ==> f y``)
          \\ AP_TERM_TAC
          \\ fs [join_env_def]
          \\ rpt AP_TERM_TAC
          \\ simp [spt_eq_thm]
          \\ fs [lookup_inter_alt]
          \\ strip_tac \\ IF_CASES_TAC \\ fs []
          \\ fs [EVAL ``(adjust_set (fromList [x;y]))``]
          \\ fs [lookup_insert])
        \\ disch_then drule \\ fs []
        \\ `dataSem$cut_env ss s3.locals = SOME
                (fromList [r1; r2])` by
          (fs [Abbr`s3`,Abbr`ss`,dataSemTheory.cut_env_def] \\ EVAL_TAC)
        \\ fs []
        \\ qmatch_asmsub_abbrev_tac `insert 1 (Word ww11)`
        \\ disch_then (qspec_then `ww11` mp_tac)
        \\ impl_tac THEN1
         (fs [Abbr`tt`,lookup_insert,Abbr`ll`]
          \\ fs [good_dimindex_def,dimword_def])
        \\ strip_tac
        \\ Cases_on `aa1 = SOME NotEnoughSpace` \\ fs []
        >- (
          fs [with_fresh_ts_def]
          \\ `x.tstamps = s.tstamps` by
               (qpat_x_assum `cut_state x' s = SOME x` mp_tac \\ rpt (pop_assum kall_tac)
                \\ simp [cut_state_def,CaseEq"option"] \\ strip_tac \\ rveq \\ simp [])
          \\ Cases_on `s.tstamps` \\ gvs [check_lim_def]
          \\ conj_tac >- simp [Abbr `s3`, call_env_def, push_env_def, dataSemTheory.dec_clock_def]
          \\ `x.stack_frame_sizes = s.stack_frame_sizes ∧ x.stack = s.stack ∧
              x.locals_size = s.locals_size ∧ x.stack_max = s.stack_max` by
               (qpat_x_assum `cut_state x' s = SOME x` mp_tac \\ rpt (pop_assum kall_tac)
                \\ simp [cut_state_def,CaseEq"option"] \\ strip_tac \\ rveq \\ simp [])
          \\ conj_tac >-
              (drule_then match_mp_tac option_le_trans
               \\ fs []
               \\ simp [Abbr`s3`,call_env_def,push_env_def,dataSemTheory.dec_clock_def]
               \\ rw[size_of_stack_eq,option_le_max_right,option_le_max,option_map2_max_add,
                     AC option_add_comm option_add_assoc,option_le_eq_eqns,stack_size_eq,option_le_add])
          >- (
            strip_tac
            \\ spose_not_then strip_assume_tac
            \\ first_x_assum drule
            \\ impl_tac >- (
              ‘s3.refs = x.refs’ by
               (unabbrev_all_tac
                \\ imp_res_tac cut_state_refs_same
                \\ simp [call_env_def])
              \\ simp [Abbr `ww11`, Abbr `ll`]
              \\ `(bytes_in_word * n2w sp) ⋙ (shift (dimindex (:α)) − 1) = n2w (2 * sp):'a word` by
                 (rewrite_tac [GSYM w2n_11,w2n_lsr]
                  \\ fs [good_dimindex_def,bytes_in_word_def,shift_def,
                         dimword_def,word_mul_n2w] \\ rfs []
                  \\ fs [DIV_EQ_X])
              \\ pop_assum SUBST_ALL_TAC
              \\ fs [word_add_n2w]
              \\ fs [ADD_DIV_EQ] \\ fs [X_LE_DIV]
              \\ simp [LEFT_SUB_DISTRIB]
              \\ rw[SUB_LEFT_ADD] >-
                   (fs[NOT_LESS_EQUAL] >>
                    mp_tac (Q.INST [`m`|->`3`,`d`|->`sp`,`k`|->`sp+1`] IMP_MULT_DIV_LESS) >>
                    impl_tac >- simp[] >>
                    disch_then(assume_tac o SIMP_RULE std_ss [LESS_EQ,ADD1]) >>
                    `3* (SUC (LENGTH in1)) <= 3 * (sp DIV 3)` by simp[] >>
                    drule_then drule LESS_EQ_TRANS >> strip_tac >>
                    metis_tac[LESS_EQ_ANTISYM])
              \\ fs[NOT_LESS_EQUAL]
              \\ strip_assume_tac (MATCH_MP DIVISION (DECIDE ``0<3n``) |> Q.SPEC `sp`)
              \\ qpat_x_assum `_ = _` (fn th => once_rewrite_tac [th]
                    THEN rewrite_tac [LEFT_ADD_DISTRIB]
                    THEN rewrite_tac [GSYM th])
              \\ fs [LEFT_SUB_DISTRIB]
              \\ `(6 * SUC (LENGTH in1) + 2 * (sp MOD 3)) < dimword (:α)` by
                 (`sp MOD 3 < 3` by fs []
                  \\ qpat_x_assum `memory_rel c t.be _ s.refs s.space t.store t.memory t.mdomain
                     ((r1,Word ww)::_)` assume_tac
                  \\ drule (GEN_ALL memory_rel_list_limit)
                  \\ rfs [good_dimindex_def] \\ rfs [dimword_def]
                  \\ fs [LEFT_ADD_DISTRIB]
                  \\ `sp MOD 3 < 3` by fs [] \\ simp [])
              \\ fs [ADD_DIV_EQ] \\ fs [X_LE_DIV]
              \\ simp [ADD_DIV_ADD_DIV |> PURE_ONCE_REWRITE_RULE[ADD_SYM]
                                       |> PURE_ONCE_REWRITE_RULE[MULT_SYM]]
              \\ simp [intLib.COOPER_PROVE ``6 * a DIV 2 = 3 * a``]
              \\ simp[SUB_LEFT_LESS]
              \\ `dimword (:'a) = 2**arch_size s.limits` by(fs[state_rel_def,limits_inv_def,dimword_def,
                                                              arch_size_def,good_dimindex_def])
              \\ once_rewrite_tac [GSYM dimword_def]
              \\ pop_assum SUBST_ALL_TAC
              \\ match_mp_tac LESS_EQ_LESS_TRANS
              \\ `x.limits = s.limits` by
                   (qpat_x_assum `cut_state x' s = SOME x` mp_tac \\ rpt (pop_assum kall_tac)
                    \\ simp [cut_state_def,CaseEq"option"] \\ strip_tac \\ rveq \\ simp [])
              \\ qexists_tac `3 * SUC (SUC (LENGTH in1))`
              \\ `sp MOD 3 < 3` by simp []
              \\ fs []
              \\ intLib.COOPER_TAC
            )
            >- (
              strip_tac
              \\ `x.refs = s.refs ∧ x.limits = s.limits ∧ x.stack = s.stack` by
                   (qpat_x_assum `cut_state x' s = SOME x` mp_tac \\ rpt (pop_assum kall_tac)
                    \\ simp [cut_state_def,CaseEq"option"] \\ strip_tac \\ rveq \\ simp [])
              \\ qmatch_asmsub_abbrev_tac `size_of_heap (cut_locals _ a_state)`
              \\ `cut_locals ss a_state = a_state` by
                   (simp [Abbr`a_state`,Abbr`ss`,Abbr`s3`,data_to_word_gcProofTheory.cut_locals_def,
                          dataSemTheory.cut_env_def,call_env_def,push_env_def,dataSemTheory.dec_clock_def]
                    \\ EVAL_TAC)
              \\ `s3.limits = s.limits` by
                   simp [Abbr`s3`,call_env_def,push_env_def,dataSemTheory.dec_clock_def]
              \\ `size_of_heap a_state = size_of_heap_args [r1; r2] x` by
                   (simp [Abbr`a_state`,Abbr`s3`,dataSemTheory.size_of_heap_def,
                          dataSemTheory.size_of_heap_args_def,dataSemTheory.stack_to_vs_def,
                          call_env_def,push_env_def,dataSemTheory.dec_clock_def]
                    \\ `x.global = s.global` by
                         (qpat_x_assum `cut_state x' s = SOME x` mp_tac \\ rpt (pop_assum kall_tac)
                          \\ simp [cut_state_def,CaseEq"option"] \\ strip_tac \\ rveq \\ simp [])
                    \\ simp [dataSemTheory.extract_stack_def]
                    \\ EVAL_TAC)
              \\ sg `w2n ww11 DIV 2 + 1 ≤ space_consumed x (BlockOp ListAppend) [r1; r2]`
              >- (
                simp [dataSemTheory.space_consumed_def, Abbr `ww11`]
                \\ `(bytes_in_word * n2w sp) ⋙ (shift (dimindex (:α)) − 1) = n2w (2 * sp):'a word` by
                   (rewrite_tac [GSYM w2n_11,w2n_lsr]
                    \\ fs [good_dimindex_def,bytes_in_word_def,shift_def,
                           dimword_def,word_mul_n2w] \\ rfs []
                    \\ fs [DIV_EQ_X])
                \\ pop_assum SUBST_ALL_TAC
                \\ fs [word_add_n2w]
                \\ `sp MOD 3 < 3` by fs []
                \\ `sp DIV 3 ≤ LENGTH in1` by (simp [arithmeticTheory.DIV_LE_X] \\ fs [NOT_LESS_EQUAL])
                \\ `2 * sp + 6 * (SUC (LENGTH in1) − sp DIV 3) = 6 * SUC (LENGTH in1) + 2 * (sp MOD 3)` by
                     (qpat_x_assum `sp DIV 3 ≤ LENGTH in1` mp_tac
                      \\ rpt (pop_assum kall_tac) \\ intLib.COOPER_TAC)
                \\ qpat_x_assum `2 * sp + _ = _` (fn th => rewrite_tac [th])
                \\ `6 * SUC (LENGTH in1) + 2 * (sp MOD 3) < dimword (:α)` by
                   (qpat_x_assum `memory_rel c t.be _ s.refs sp t.store t.memory t.mdomain
                        ((r1,Word ww)::_)` assume_tac
                    \\ drule (GEN_ALL memory_rel_list_limit)
                    \\ rfs [good_dimindex_def] \\ rfs [dimword_def]
                    \\ fs [LEFT_ADD_DISTRIB]
                    \\ `sp MOD 3 < 3` by fs [] \\ simp [])
                \\ fs [LESS_MOD]
                \\ `sp MOD 3 < 3` by fs []
                \\ pop_assum mp_tac
                \\ rpt (pop_assum kall_tac)
                \\ intLib.COOPER_TAC
              )
              \\ qpat_x_assum `s3.limits.heap_limit < _` mp_tac
              \\ fs []
            )
          )
        )
        \\ rveq \\ fs []
          \\ qabbrev_tac `new_sp = w2n ww11 DIV 2 + 1`
          \\ `3 * LENGTH (i1::in1) <= new_sp` by
           (`(bytes_in_word * n2w sp) ⋙ (shift (dimindex (:α)) − 1) = n2w (2 * sp):'a word` by
               (rewrite_tac [GSYM w2n_11,w2n_lsr]
                \\ fs [good_dimindex_def,bytes_in_word_def,shift_def,
                       dimword_def,word_mul_n2w] \\ rfs []
                \\ fs [DIV_EQ_X])
            \\ fs [word_add_n2w] \\ qunabbrev_tac `ww11`
            \\ qunabbrev_tac `new_sp`
            \\ strip_assume_tac (MATCH_MP DIVISION (DECIDE ``0<3n``) |> Q.SPEC `sp`)
            \\ qpat_x_assum `_ = _` (fn th => once_rewrite_tac [th]
                  THEN rewrite_tac [LEFT_ADD_DISTRIB]
                  THEN rewrite_tac [GSYM th])
            \\ fs [LEFT_SUB_DISTRIB]
            \\ `6 * (sp DIV 3) < 6 * SUC (LENGTH in1)` by
                   (fs [LT_MULT_LCANCEL,DIV_LT_X]) \\ fs []
            \\ `(6 * SUC (LENGTH in1) + 2 * (sp MOD 3)) < dimword (:α)` by
             (`sp MOD 3 < 3` by fs []
              \\ qpat_x_assum `memory_rel c t.be _ s.refs s.space t.store t.memory t.mdomain
                 ((r1,Word ww)::vars)` assume_tac
              \\ drule (GEN_ALL memory_rel_list_limit)
              \\ rfs [good_dimindex_def] \\ rfs [dimword_def]
              \\ fs [LEFT_ADD_DISTRIB]
              \\ `sp MOD 3 < 3` by fs [] \\ simp [])
            \\ fs [ADD_DIV_EQ] \\ fs [X_LE_DIV])
          \\ pop_assum mp_tac
          \\ pop_assum kall_tac
          \\ strip_tac
          \\ fs [list_Seq_def,wordSemTheory.evaluate_def,eq_eval]
          \\ qmatch_assum_abbrev_tac `state_rel c n l s4 _ _ _`
          \\ `dataSem$get_vars [0;1] s4.locals = SOME [r1; r2]`
            by (qunabbrev_tac `s4` \\ fs [get_vars_SOME_IFF_data] \\ EVAL_TAC)
          \\ rpt_drule0 state_rel_get_vars_IMP
          \\ fs [LENGTH_EQ_2] \\ clean_tac
          \\ simp [PULL_EXISTS]
          \\ ntac 3 strip_tac
          \\ fs [get_vars_SOME_IFF,wordSemTheory.get_var_def,
                 EVAL ``adjust_var 0``,EVAL ``adjust_var 1``]
          \\ qpat_x_assum `state_rel c n l s4 aa2 NONE ((l1,l2)::locs)` mp_tac
          \\ simp [Once state_rel_thm]
          \\ strip_tac \\ fs []
          \\ `(?md. lookup Append_location aa2.code = SOME (3,Append_code c,md))` by
                fs [code_rel_def,stubs_md_def,stubs_def,MAP_MAP_o,o_DEF] \\ simp [] \\ rfs []
          \\ `dimword (:'a) < s4.clock` by
           (qunabbrev_tac `s4` \\ fs [Abbr `tt`]
            \\ `10 * dimword (:'a) <= MustTerminate_limit (:α)` by
              (simp [wordSemTheory.MustTerminate_limit_def]
               \\ match_mp_tac (DECIDE ``m <= n ==> m <= k+(n+i:num)``)
               \\ fs [good_dimindex_def,dimword_def])
            \\ `sp DIV 3 + 3 < dimword (:'a)` by
              (fs [ADD_DIV_EQ,DIV_LT_X]
               \\ fs [good_dimindex_def,dimword_def] \\ rfs [])
            \\ `SUC (LENGTH in1) < dimword (:'a)` by
             (qpat_x_assum `memory_rel c t.be (THE s.tstamps) s.refs s.space t.store t.memory t.mdomain
                 ((r1,Word ww)::vars)` assume_tac
              \\ drule (GEN_ALL memory_rel_list_limit)
              \\ rfs [good_dimindex_def] \\ rfs [dimword_def])
            \\ fs []) \\ simp []
          \\ simp [Append_code_def]
          \\ simp [wordSemTheory.evaluate_def,eq_eval,option_le_max_right]
          \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
          \\ drule (GEN_ALL memory_rel_get_vars_IMP)
          \\ disch_then drule
          \\ simp [wordSemTheory.get_vars_def,wordSemTheory.get_var_def,
                   EVAL ``MAP adjust_var [0; 1]``,list_to_v_def]
          \\ strip_tac
          \\ first_assum (mp_then Any assume_tac v_to_list_SOME_CONS_IMP)
          \\ fs [] \\ fs []
          \\ rpt_drule0 memory_rel_Block_IMP
          \\ strip_tac \\ fs []
          \\ simp [asmTheory.word_cmp_def]
          \\ fs [SIMP_RULE (srw_ss()) [] word_and_one_eq_0_iff]
          \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def]
          \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def]
          \\ `?next_free trig_gc curr.
                 FLOOKUP aa2.store NextFree = SOME (Word next_free) /\
                 FLOOKUP aa2.store TriggerGC = SOME (Word trig_gc) /\
                 FLOOKUP aa2.store CurrHeap = SOME (Word curr)` by
                fs [state_rel_thm,memory_rel_def,heap_in_memory_store_def]
          \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def,FLOOKUP_UPDATE,
                   wordSemTheory.get_store_def]
          \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def,
                   wordSemTheory.get_store_def]
          \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def,FLOOKUP_UPDATE]
          \\ `shift_length c - shift (dimindex (:'a)) < dimword (:'a)` by
               (assume_tac dimindex_lt_dimword \\
                `shift_length c < dimindex (:'a)` suffices_by decide_tac \\
                fs [state_rel_thm,memory_rel_def,heap_in_memory_store_def])
          \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def,FLOOKUP_UPDATE,
                   wordSemTheory.word_sh_def,
                   wordSemTheory.get_store_def]
          \\ qmatch_goalsub_abbrev_tac `insert 7 (Word init_ptr2)`
          \\ simp [list_Seq_def,eq_eval,wordSemTheory.set_store_def]
          \\ `(?md. lookup AppendMainLoop_location aa2.code = SOME (6,AppendMainLoop_code c,md))` by
               fs [state_rel_thm,code_rel_def,stubs_md_def,stubs_def,MAP_MAP_o,o_DEF] \\ fs [] \\ rfs []
          \\ drule memory_rel_space_max
          \\ simp [] \\ strip_tac \\ fs []
          \\ assume_tac (GEN_ALL evaluate_AppendMainLoop_code)
          \\ SEP_I_TAC "evaluate"
          \\ fs [lookup_insert,FLOOKUP_UPDATE]
          \\ pop_assum mp_tac
          \\ disch_then drule \\ fs []
          \\ disch_then (qspec_then `0` mp_tac)
          \\ simp [markerTheory.Abbrev_def]
          \\ disch_then (qspec_then `SEP_T` mp_tac)
          \\ impl_tac THEN1
           (conj_asm1_tac THEN1 fs [Abbr `s4`]
            \\ reverse conj_tac THEN1
             (qpat_x_assum `memory_rel c t.be _ s.refs s.space t.store t.memory t.mdomain
                 ((_,Word ww)::vars)` assume_tac
              \\ drule memory_rel_list_limit
              \\ rfs [good_dimindex_def] \\ rfs [dimword_def])
            \\ pop_assum mp_tac
            \\ rewrite_tac [LESS_EQ_EXISTS]
            \\ strip_tac \\ rveq \\ fs []
            \\ drule (GEN_ALL memory_rel_IMP_word_list_exists) \\ fs [])
          \\ strip_tac \\ fs []
          \\ fs [wordSemTheory.pop_env_def]
            \\ rename1 `stack_rel x56 x67`
            \\ Cases_on `x67` \\ fs []
            \\ fs [Abbr `s3`,Abbr `s4`]
            \\ fs [call_env_def,push_env_def,dec_clock_def]
            \\ rveq \\ fs [stack_rel_def] \\ rveq \\ fs []
            \\ Cases_on `o0` \\ fs [stack_rel_def]
            \\ reverse IF_CASES_TAC THEN1
             (sg `F` \\ fs [] \\ pop_assum mp_tac \\ simp []
              \\ qspecl_then [`AllocVar c ll ss`,`tt`] mp_tac
                   (wordPropsTheory.evaluate_stack_swap
                      |> INST_TYPE [``:'c``|->``:'ffi``,``:'b``|->``:'c``])
              \\ fs []
              \\ `tt.stack = StackFrame s.locals_size (toAList y1) q NONE::t.stack` by
                    fs [Abbr`tt`] \\ fs []
              \\ fs [wordPropsTheory.s_key_eq_def]
              \\ fs [wordPropsTheory.s_frame_key_eq_def]
              \\ strip_tac \\ pop_assum kall_tac
              \\ fs [dataSemTheory.dec_clock_def]
              \\ rw []
              \\ rewrite_tac [domain_union]
              \\ drule_all env_to_list_domain_eq
              \\ simp [domain_union,domain_fromAList_toAList,AC UNION_COMM UNION_ASSOC])
            \\ fs []
            \\ fs [wordSemTheory.set_var_def,set_var_def]
            \\ fs [state_rel_thm]
            \\ fs [lookup_insert,adjust_var_11,
                   dataSemTheory.call_env_def,
                   push_env_def,dataSemTheory.set_var_def,wordSemTheory.set_var_def]
            \\ fs [wordSemTheory.dec_clock_def,dataSemTheory.dec_clock_def,check_lim_def,
                   allowed_op_def]
            \\ simp [FAPPLY_FUPDATE_THM,memory_rel_Temp]
            \\ fs [memory_rel_Temp,
                   MATCH_MP FUPDATE_COMMUTES (prove(``Temp p <> NextFree``,EVAL_TAC))]
            \\ fs [contains_loc_def,lookup_fromAList,with_fresh_ts_def,IS_SOME_EXISTS,
                   wordSemTheory.set_vars_def,alist_insert_def]
            \\ fs [] \\ rveq \\ fs []
            \\ conj_tac >- (
                fs [Abbr `tt`]
              )
              \\ conj_tac >- (
                qpat_x_assum `code_oracle_rel c _ _ _ _ _ _ _` mp_tac
                \\ fs [code_oracle_rel_def,FLOOKUP_UPDATE, check_lim_def]
              )
              \\ conj_tac >- (
                simp [lookup_insert]
                \\ simp [lookup_union,lookup_fromAList,ALOOKUP_toAList]
                \\ drule_all cut_envs_lookup_0 \\ simp []
                \\ simp [AllCaseEqs()]
                \\ qpat_x_assum ‘EVERY _ l0’ mp_tac
                \\ rpt $ pop_assum kall_tac
                \\ gvs [ALOOKUP_NONE]
                \\ rw [] \\ disj1_tac
                \\ gvs [MEM_MAP,EXISTS_PROD]
                \\ CCONTR_TAC
                \\ gvs [EVERY_MEM] \\ res_tac
                \\ fs []
              )
              \\ conj_tac >- (
                gen_tac
                \\ simp [lookup_insert]
                \\ IF_CASES_TAC \\ simp [adjust_var_11]
                \\ simp [lookup_fromAList,lookup_union]
                \\ simp [CaseEq"option",SF DNF_ss]
              )
              \\ conj_tac >- (
                `x.stack = s.stack` by
                   (qpat_x_assum `cut_state x' s = SOME x` mp_tac \\ rpt (pop_assum kall_tac)
                    \\ simp [cut_state_def,CaseEq"option"] \\ strip_tac \\ rveq \\ simp [])
                \\ fs []
              )
              \\ conj_tac >- (
                simp[option_le_max_right]
                \\ drule evaluate_stack_max >> simp[]
                \\ qmatch_goalsub_abbrev_tac`option_CASE sm1`
                \\ strip_tac
                \\ `option_le sm1 smx''` by
                    (pop_assum mp_tac>>Cases_on`sm1`>>Cases_on`smx''`>>
                    simp[miscTheory.the_def])
                \\ qmatch_goalsub_abbrev_tac`option_le sm2 _`
                \\ `option_le sm2 sm1` by
                    (fs[Abbr`sm1`,Abbr`sm2`]>>
                    simp[wordPropsTheory.stack_size_eq]>>
                    simp[option_le_max_right]>>
                    metis_tac[option_add_comm,option_le_add])
                \\ metis_tac[option_le_trans]
              )
              \\ conj_tac >- (
                `x.stack_frame_sizes = s.stack_frame_sizes ∧ x.stack = s.stack ∧
                 x.stack_max = s.stack_max ∧ x.locals_size = s.locals_size` by
                   (qpat_x_assum `cut_state x' s = SOME x` mp_tac \\ rpt (pop_assum kall_tac)
                    \\ simp [cut_state_def,CaseEq"option"] \\ strip_tac \\ rveq \\ simp [])
                \\ fs []
                \\ drule_then match_mp_tac option_le_trans
                \\ rw[option_le_max]
                >- (drule_then match_mp_tac option_le_trans >>
                    rw[size_of_stack_eq,option_le_max_right,option_le_max,option_map2_max_add,AC option_add_comm option_add_assoc,option_le_eq_eqns,option_map2_max_add,stack_size_eq,option_le_add])
                \\ imp_res_tac stack_rel_IMP_size_of_stack
                \\ rw[size_of_stack_eq,option_le_max_right,option_le_max,option_map2_max_add,AC option_add_comm option_add_assoc,option_le_eq_eqns,option_map2_max_add,stack_size_eq,option_le_add]
              )
              \\ conj_tac >- (
                fs [limits_inv_def, FLOOKUP_UPDATE]
              )
              \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
                \\ match_mp_tac memory_rel_insert \\ fs [flat_def]
                \\ simp [FAPPLY_FUPDATE_THM]
                \\ qmatch_asmsub_abbrev_tac `memory_rel _ _ _ _ _ _ _ _ (A ++ B::C)`
                \\ sg `memory_rel c aa2.be (THE s.tstamps) s.refs sp' aa2.store m1' aa2.mdomain ((B::A) ++ C)`
                >-
                 (irule memory_rel_rearrange
                  \\ HINT_EXISTS_TAC
                  \\ rw [] \\ fs [])
                \\ map_every qunabbrev_tac [`A`,`B`,`C`]
                \\ drule (GEN_ALL memory_rel_append)
                \\ simp [make_cons_ptr_def]
                \\ impl_keep_tac
                >- (fs [Abbr`init_ptr2`, get_lowerbits_def, make_header_def, encode_header_def] \\ gvs [])
                \\ strip_tac
                \\ drule (GEN_ALL memory_rel_less_space)
                \\ disch_then (qspec_then `0` mp_tac) \\ fs []
                \\ strip_tac
                \\ `x.refs = s.refs ∧ x.global = s.global ∧ x.tstamps = s.tstamps ∧
                    x.stack = s.stack` by
                     (qpat_x_assum `cut_state x' s = SOME x` mp_tac \\ rpt (pop_assum kall_tac)
                      \\ simp [cut_state_def,CaseEq"option"] \\ strip_tac \\ rveq \\ simp [])
                \\ gvs []
                \\ fs [join_env_def]
                \\ irule memory_rel_rearrange
                \\ HINT_EXISTS_TAC \\ rw [] \\ fs []
                >- fs [Abbr`init_ptr2`, get_lowerbits_def]
                \\ ntac 3 disj2_tac
                \\ disj1_tac
                \\ pop_assum mp_tac
                \\ fs [inter_union_distrib]
                \\ ‘inter (fromAList l') (adjust_set x.locals) = LN’ by
                 (DEP_REWRITE_TAC [spt_eq_thm]
                  \\ simp [lookup_def,lookup_inter_alt,AllCaseEqs()]
                  \\ qx_gen_tac ‘nn’
                  \\ Cases_on ‘nn ∈ domain (adjust_set x.locals)’ \\ simp []
                  \\ simp [lookup_fromAList,ALOOKUP_NONE]
                  \\ qpat_x_assum ‘EVERY (λ(x1,x2). x1 = 0) l'’ mp_tac
                  \\ CCONTR_TAC \\ fs []
                  \\ qsuff_tac ‘nn = 0’
                  >-
                   (ntac 5 $ pop_assum mp_tac
                    \\ rpt $ pop_assum kall_tac
                    \\ rw [] \\ CCONTR_TAC \\ gvs [NOT_0_domain])
                  \\ ntac 5 $ pop_assum mp_tac
                  \\ rpt $ pop_assum kall_tac
                  \\ rw [] \\ gvs [MEM_MAP,EXISTS_PROD,EVERY_MEM]
                  \\ res_tac \\ fs [])
                \\ simp []
                \\ simp [MEM_MAP,MEM_FILTER,PULL_EXISTS,FORALL_PROD,EXISTS_PROD]
                \\ simp [MEM_toAList]
                \\ simp [lookup_inter_alt]
                \\ fs [domain_lookup,lookup_adjust_set]
                \\ rpt gen_tac
                \\ Cases_on `p_1 = 0` \\ simp []
                \\ strip_tac
                \\ qexists_tac `p_1` \\ simp []
                \\ fs [lookup_fromAList]
                \\ drule ALOOKUP_MEM \\ simp []
QED

Theorem FromList1_code_thm:
   !k a b r x m1 a1 a2 a3 a4 a5 a6.
      (?md. lookup FromList1_location r.code = SOME (6,FromList1_code c,md)) /\
      copy_list c r.store k (a,x,b,(r:('a,'c,'ffi) wordSem$state).memory,
        r.mdomain) = SOME (b1,m1) /\
      shift_length c < dimindex (:'a) /\ good_dimindex (:'a) /\
      arch_width_bits c.arch_width = dimindex (:'a) /\
      get_var a1 r = SOME (Loc l1 l2) /\
      get_var a2 r = SOME (Word (b:'a word)) /\
      get_var a3 r = SOME a /\
      get_var a4 r = SOME (Word (n2w (2 * k))) /\
      get_var a5 r = SOME ret_val /\
      get_var a6 r = SOME x /\
      2 * k < dimword (:'a) /\
      k < r.clock ==>
      evaluate (Call NONE (SOME FromList1_location) [a1;a2;a3;a4;a5;a6] NONE,r) =
        (SOME (Result (Loc l1 l2) [ret_val]),
         r with <| memory := m1 ; clock := r.clock - k - 1;
                   locals := LN ; locals_size := SOME 0;
                   store := r.store |+ (NextFree, Word b1) ;
                   stack_max := OPTION_MAP2 MAX r.stack_max (OPTION_MAP2 $+ (stack_size r.stack)
                                (lookup FromList1_location r.stack_size)) |>)
Proof
  Induct \\ rw [] \\ simp [wordSemTheory.evaluate_def]
  \\ simp [wordSemTheory.get_vars_def,wordSemTheory.bad_dest_args_def,
        wordSemTheory.find_code_def,wordSemTheory.add_ret_loc_def]
  \\ rw [] \\ simp [FromList1_code_def]
  \\ simp [Once list_Seq_def]
  \\ qpat_assum `_ = SOME (b1,m1)` mp_tac
  \\ once_rewrite_tac [copy_list_def] \\ fs []
  \\ strip_tac THEN1
   (rveq
    \\ simp [wordSemTheory.evaluate_def,wordSemTheory.call_env_def,
             wordSemTheory.get_var_def,word_exp_rw,fromList2_def,wordSemTheory.get_vars_def,
             asmTheory.word_cmp_def,wordSemTheory.dec_clock_def,lookup_insert,
             wordSemTheory.mem_store_def,list_Seq_def,wordSemTheory.set_var_def,
             wordSemTheory.set_store_def]
    \\ simp [wordSemTheory.flush_state_def])
  \\ Cases_on `a` \\ fs []
  \\ Cases_on `get_real_addr c r.store c'` \\ fs []
  \\ qabbrev_tac `m9 = (b =+ x) r.memory`
  \\ ntac 2 (simp [Once list_Seq_def])
  \\ simp [wordSemTheory.evaluate_def,word_exp_rw,wordSemTheory.call_env_def,
           wordSemTheory.get_var_def,word_exp_rw,fromList2_def,wordSemTheory.get_vars_def,
           wordSemTheory.mem_store_def,wordSemTheory.dec_clock_def,lookup_insert,
           wordSemTheory.set_var_def,asmTheory.word_cmp_def]
  \\ ntac 4 (simp [Once list_Seq_def])
  \\ simp [wordSemTheory.evaluate_def,word_exp_rw,wordSemTheory.call_env_def,
           wordSemTheory.get_var_def,word_exp_rw,fromList2_def,
           wordSemTheory.mem_store_def,wordSemTheory.dec_clock_def,lookup_insert,
           wordSemTheory.set_var_def,asmTheory.word_cmp_def]
  \\ qpat_abbrev_tac `r3 =
          (r with
           <|locals :=
               insert 2 (Word (b + bytes_in_word)) _;
             locals_size := _;
             stack_max := _;
             memory := m9; clock := r.clock − 1|>)`
  \\ rename1 `get_real_addr c r.store c1 = SOME x1`
  \\ `get_real_addr c r3.store c1 = SOME x1` by (fs [Abbr `r3`])
  \\ rpt_drule0 (get_real_addr_lemma
        |> REWRITE_RULE [CONJ_ASSOC]
        |> ONCE_REWRITE_RULE [CONJ_COMM]) \\ fs []
  \\ disch_then (qspec_then `4` mp_tac)
  \\ impl_tac
  THEN1 (unabbrev_all_tac \\ fs [wordSemTheory.get_var_def,lookup_insert])
  \\ fs [wordSemTheory.mem_load_def,lookup_insert]
  \\ fs [list_Seq_def]
  \\ qpat_abbrev_tac `r7 =
       r with <|locals := insert 6 _ _ ; locals_size := _ ; stack_max := _ ; memory := m9 ; clock := _ |> `
  \\ first_x_assum (qspecl_then [`(m9 (x1 + 2w * bytes_in_word))`,
         `b + bytes_in_word`,`r7`,`m9 (x1 + bytes_in_word)`,`m1`,
         `0`,`2`,`4`,`6`,`8`,`10`] mp_tac)
  \\ reverse impl_tac THEN1
    (strip_tac \\ fs [] \\ rw [wordSemTheory.state_component_equality,Abbr `r7`])
  \\ unabbrev_all_tac \\ fs []
  \\ fs [wordSemTheory.get_var_def,lookup_insert]
  \\ fs [MULT_CLAUSES,GSYM word_add_n2w]
QED

Theorem FromList_thm:
   state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) NONE locs /\
    encode_header c (4 * tag) 0 <> (NONE:num option) /\
    get_vars [0; 1; 2] s.locals = SOME [v1; v2; Number (&(8 * tag))] /\
    t.clock = MustTerminate_limit (:'a) - 1 /\
    pop_env s = SOME s1 /\ is_env(HD s.stack) /\
    s.locals_size = lookup FromList_location s.stack_frame_sizes /\
    do_app (BlockOp (FromList tag)) [v1; v2] s1 = Rval (v,s2) /\
    option_le s.stack_max s2.stack_max /\
    size_of_heap (cut_locals (fromList [(); (); ()]) s) <=
      size_of_heap_args [v1; v2] s1 ==>
    ?q r new_c.
      evaluate (FromList_code c,t) = (q,r) /\
      if q = SOME NotEnoughSpace then
        r.ffi = t.ffi /\
        option_le r.stack_max s2.stack_max /\
        (c.gc_kind <> None ∧ no_thunks_in_refs s.refs ==>
         (case (v1,v2) of
           (Number n,_) => ~small_num s.limits.arch_64_bit n \/
                           ~(Num n < dimword (:α) DIV 16) \/
                           ~(Num n < 2 ** c.len_size) \/
                           (s1.limits.heap_limit <
                             size_of_heap_args [v1; v2] s1 + Num n + 1)
         ))
      else
        ?rv. q = SOME (Result (Loc l1 l2) [rv]) /\
             state_rel c r1 r2 (s2 with <| locals := LN;
                                           locals_size := SOME 0;
                                           clock := new_c;
                                           stack := s.stack|>)
                r (SOME [(v,rv)]) locs
Proof
  fs [do_app_def,do_app_aux_def,do_space_def,
      dataLangTheory.op_space_reset_def]
  \\ Cases_on `v_to_list v2` \\ fs [with_fresh_ts_def]
  \\ reverse (Cases_on `v1 = Number (&LENGTH x)`)
  >- (Cases_on `x` \\ fs [])
  \\ fs [LENGTH_NIL] \\ strip_tac \\ rveq \\ fs [FromList_code_def]
  \\ once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ rpt_drule0 state_rel_get_vars_IMP
  \\ fs[wordSemTheory.get_var_imm_def]
  \\ rpt_drule0 state_rel_get_vars_IMP \\ strip_tac \\ fs [LENGTH_EQ_3]
  \\ rveq \\ fs [adjust_var_def,get_vars_SOME_IFF,get_vars_SOME_IFF_data]
  \\ qpat_assum `get_var 0 s.locals = SOME (Number _)` assume_tac
  \\ rpt_drule0 state_rel_IMP_test_zero
  \\ fs [adjust_var_def] \\ strip_tac \\ fs [] \\ rveq
  \\ simp [asmTheory.word_cmp_def]
  \\ `arch_width_bits c.arch_width = dimindex (:'a)` by
       fs [state_rel_def,heap_in_memory_store_def]
  \\ `small_int (dimindex (:α)) (&(8 * tag))` by (
    fs [encode_header_def,small_int_def,state_rel_thm,
        good_dimindex_def,dimword_def] \\ rfs [])
  \\ IF_CASES_TAC
  >- (* EmptyArm *)
     (qpat_assum ‘get_var 2 s.locals = SOME (Number (&(8 * tag)))’ assume_tac
  \\ rpt_drule0 state_rel_get_var_Number_IMP \\ fs []
  \\ fs [LENGTH_NIL] \\ rveq \\ rw []
  \\ ‘good_dimindex (:'a)’ by fs [data_to_word_gcProofTheory.state_rel_def]
  \\ ‘3 MOD dimword (:'a) = 3’ by fs [good_dimindex_def,dimword_def]
  \\ ‘~(3 >= dimindex (:'a))’ by fs [good_dimindex_def]
  \\ fs [data_to_wordTheory.list_Seq_def, wordSemTheory.evaluate_def,
         data_to_word_gcProofTheory.word_exp_rw,
         wordSemTheory.get_var_def, data_to_wordTheory.adjust_var_def,
         wordSemTheory.set_var_def, wordSemTheory.get_vars_def,
         wordSemTheory.flush_state_def]
  \\ rveq \\ fs [lookup_insert]
  \\ ‘lookup 0 t.locals = SOME (Loc l1 l2)’ by
       fs [data_to_word_gcProofTheory.state_rel_def]
  \\ fs []
  \\ fs [data_to_word_gcProofTheory.state_rel_thm,
         wordSemTheory.call_env_def, lookup_def,
         dataSemTheory.with_fresh_ts_def]
  \\ reverse (Cases_on ‘s.tstamps’) \\ fs []
  \\ fs [] \\ rveq
  \\ qpat_x_assum ‘pop_env s = SOME _’ mp_tac
  \\ fs [dataSemTheory.pop_env_def, is_env_def,
         CaseEq "list", CaseEq "stack"]
  \\ rveq \\ fs [] \\ rfs []
  \\ strip_tac
  \\ fs [dataSemTheory.state_component_equality]
  \\ rveq \\ fs [] \\ rfs []
  \\ conj_tac >- metis_tac [option_le_add_indv]
  \\ conj_tac >- metis_tac [backendPropsTheory.option_le_trans]
  \\ fs [data_to_word_memoryProofTheory.BlockNil_def,
         Smallnum_def, WORD_MUL_LSL, word_mul_n2w]
  \\ ‘16 * tag < dimword (:'a)’ by
       (fs [data_to_wordTheory.encode_header_def,dimword_def,X_LT_DIV]
        \\ DECIDE_TAC)
  \\ ‘(n2w (16 * tag) >>> 3) = BlockNil tag : 'a word’ by
       (fs [data_to_word_memoryProofTheory.BlockNil_def, WORD_MUL_LSL,
            word_mul_n2w]
        \\ rewrite_tac [GSYM w2n_11,w2n_lsr] \\ fs [] \\ fs [DIV_EQ_X])
  \\ fs []
  \\ match_mp_tac data_to_word_memoryProofTheory.memory_rel_Cons_empty
  \\ fs [data_to_wordTheory.encode_header_def] \\ fs [X_LT_DIV]
  \\ drule0 data_to_word_memoryProofTheory.memory_rel_zero_space
  \\ match_mp_tac data_to_word_memoryProofTheory.memory_rel_rearrange
  \\ fs [] \\ rw [] \\ fs [data_to_word_gcProofTheory.join_env_def])
  (* NonEmpty *)
  \\ once_rewrite_tac [data_to_wordTheory.list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def, data_to_word_gcProofTheory.word_exp_rw]
  \\ rpt_drule0 data_to_word_gcProofTheory.state_rel_get_vars_IMP
  \\ strip_tac \\ fs [data_to_word_memoryProofTheory.LENGTH_EQ_2]
  \\ rveq \\ fs [data_to_wordTheory.adjust_var_def,
                 data_to_word_gcProofTheory.get_vars_SOME_IFF]
  \\ fs [data_to_word_gcProofTheory.get_vars_SOME_IFF_data]
  \\ fs [GSYM wordSemTheory.get_var_def]
  \\ rpt_drule0 state_rel_get_var_Number_IMP_alt \\ fs []
  \\ strip_tac \\ rveq
  \\ fs [GSYM wordSemTheory.get_var_def]
  \\ rpt_drule0 evaluate_BignumHalt2
  (* NE_BignumSplit *)
  \\ reverse (Cases_on ‘small_int (dimindex (:α)) (&(LENGTH x))’)
  >- (* NE_BigErr *)
     (fs [] \\ strip_tac \\ fs []
      \\ conj_tac
      >- metis_tac [backendPropsTheory.option_le_trans,
                    data_to_word_gcProofTheory.state_rel_def]
      \\ qpat_x_assum ‘pop_env s = SOME _’ mp_tac
      \\ fs [dataSemTheory.pop_env_def, is_env_def,
             CaseEq "list", CaseEq "stack"]
      \\ rveq \\ fs []
      \\ strip_tac
      \\ fs [dataSemTheory.state_component_equality]
      \\ rveq \\ fs []
      \\ fs [data_to_wordTheory.small_int_def,
             dataSemTheory.small_num_def,
             data_to_word_gcProofTheory.state_rel_def,
             data_to_word_gcProofTheory.limits_inv_def,
             miscTheory.good_dimindex_def, dimword_def] \\ rfs [])
  \\ Cases_on ‘small_int (dimindex (:α)) (&(LENGTH x))’ \\ fs [] \\ strip_tac \\ fs []
  \\ ntac 3 (pop_assum kall_tac)
  \\ fs []
  (* NE_SmallOK *)
  \\ ntac 2 (once_rewrite_tac [data_to_wordTheory.list_Seq_def])
  \\ fs [wordSemTheory.evaluate_def, data_to_word_gcProofTheory.word_exp_rw,
         wordSemTheory.get_var_def]
  \\ pairarg_tac \\ fs []
  \\ ‘state_rel c l1 l2 s (set_var 1 (Word w) t) NONE locs’ by
       fs [wordSemTheory.set_var_def,
           data_to_word_gcProofTheory.state_rel_insert_1]
  \\ rpt_drule0 data_to_word_gcProofTheory.AllocVar_thm
  \\ ‘?cut_x. dataSem$cut_env (fromList [();();()]) s.locals = SOME cut_x’ by
       (fs [EVAL ``sptree$fromList [();();()]``, dataSemTheory.cut_env_def,
            sptreeTheory.domain_lookup,
            dataSemTheory.get_var_def,
            data_to_word_gcProofTheory.get_vars_SOME_IFF_data])
  \\ disch_then drule0
  \\ fs [data_to_word_gcProofTheory.get_var_set_var]
  \\ disch_then drule0
  \\ impl_tac
  >- (fs [data_to_word_gcProofTheory.state_rel_def,
          EVAL ``good_dimindex (:'a)``, dimword_def])
  \\ strip_tac \\ fs []
  \\ reverse (Cases_on ‘res’)
  >- (* NE_AllocNES *)
     (fs []
  \\ conj_tac
  >- (drule backendPropsTheory.option_le_trans
      \\ disch_then drule \\ simp [])
  \\ strip_tac
  \\ spose_not_then strip_assume_tac
  \\ ‘w2n w = 2 * LENGTH x’ by
       (qpat_assum ‘state_rel c l1 l2 s t NONE locs’ assume_tac
        \\ rpt_drule0 state_rel_get_var_Number_IMP
        \\ fs [data_to_wordTheory.adjust_var_def,
               wordSemTheory.get_var_def,
               dataSemTheory.small_num_def,
               Smallnum_def,
               data_to_word_gcProofTheory.state_rel_def,
               dimword_def,
               data_to_word_gcProofTheory.limits_inv_def,
               data_to_wordTheory.small_int_def,
               miscTheory.good_dimindex_def]
        \\ fs [])
  \\ ‘w2n w DIV 2 = LENGTH x’ by
       (qpat_assum ‘w2n w = 2 * LENGTH x’ (fn th => rewrite_tac [th])
        \\ simp [intLib.COOPER_PROVE “2 * k DIV 2 = k”])
  \\ ‘s1.limits = s.limits’ by
       (qpat_x_assum ‘pop_env s = SOME _’ mp_tac
        \\ fs [dataSemTheory.pop_env_def, is_env_def,
               CaseEq "list", CaseEq "stack"]
        \\ rveq \\ fs []
        \\ strip_tac
        \\ fs [dataSemTheory.state_component_equality])
  \\ qpat_x_assum ‘c.gc_kind ≠ None ∧ _ ⇒ _’ mp_tac
  \\ impl_tac >- fs [arithmeticTheory.EXP,dimword_def]
  \\ strip_tac
  \\ qpat_x_assum ‘s1.limits = s.limits’ (fn th => full_simp_tac std_ss [th])
  \\ qpat_x_assum ‘w2n w DIV 2 = LENGTH x’ (fn th => full_simp_tac std_ss [th])
  \\ qpat_x_assum ‘size_of_heap _ ≤ size_of_heap_args _ _’ mp_tac
  \\ decide_tac)
  (* NE_AllocOK *)
  \\ fs []
  \\ ‘?f cur. FLOOKUP s1'.store NextFree = SOME (Word f) /\
              FLOOKUP s1'.store CurrHeap = SOME (Word cur)’ by
        fs [data_to_word_gcProofTheory.state_rel_def,
            data_to_word_memoryProofTheory.heap_in_memory_store_def]
  \\ ‘4 < dimword (:'a) /\ 2 < dimword (:'a) /\ 1 < dimword (:'a) /\
      dimindex (:'a) - (c.len_size + 1) < dimword (:'a) /\
      dimindex (:'a) - (c.len_size + 2) < dimword (:'a)’ by
       (assume_tac wordsTheory.dimindex_lt_dimword
        \\ fs [data_to_word_gcProofTheory.state_rel_def,
               miscTheory.good_dimindex_def, dimword_def] \\ decide_tac)
  \\ ntac 5 (once_rewrite_tac [data_to_wordTheory.list_Seq_def])
  \\ fs [wordSemTheory.evaluate_def,
         data_to_word_gcProofTheory.word_exp_rw,
         lookup_insert,
         wordSemTheory.set_var_def]
  \\ qabbrev_tac ‘s0 = s with <|locals := cut_x; space := w2n w DIV 2 + 1|>’
  \\ ‘get_var 0 s0.locals = SOME (Number (&LENGTH x)) /\
      get_var 1 s0.locals = SOME v2 /\
      get_var 2 s0.locals = SOME (Number (&(8 * tag)))’ by
   (unabbrev_all_tac
    \\ fs [dataSemTheory.get_var_def, dataSemTheory.cut_env_def]
    \\ rveq \\ fs [sptreeTheory.lookup_inter_alt] \\ EVAL_TAC)
  \\ qpat_assum ‘get_var 1 s0.locals = SOME v2’ assume_tac
  \\ rpt_drule0 data_to_word_gcProofTheory.state_rel_get_var_IMP \\ strip_tac
  \\ qpat_assum ‘get_var 2 s0.locals = SOME (Number (&(8 * tag)))’ assume_tac
  \\ rpt_drule0 state_rel_get_var_Number_IMP \\ strip_tac \\ fs []
  \\ ‘small_int (dimindex (:'a)) (&LENGTH x)’ by fs []
  \\ qpat_assum ‘get_var 0 s0.locals = SOME (Number (&LENGTH x))’ assume_tac
  \\ rpt_drule0 state_rel_get_var_Number_IMP \\ strip_tac \\ fs []
  \\ fs [data_to_wordTheory.adjust_var_def]
  \\ fs [wordSemTheory.get_var_def]
  \\ qpat_assum ‘get_var 1 s0.locals = SOME v2’ assume_tac
  \\ fs [lookup_insert]
  \\ ‘~(1 ≥ dimindex (:α)) /\ ~(2 ≥ dimindex (:α)) /\ ~(4 ≥ dimindex (:α))’ by
       (fs [data_to_word_gcProofTheory.state_rel_def,
            miscTheory.good_dimindex_def])
  \\ fs [lookup_insert]
  \\ assume_tac (GEN_ALL Make_ptr_bits_thm)
  \\ SEP_I_TAC "evaluate"
  \\ fs [wordSemTheory.set_var_def, lookup_insert] \\ rfs []
  \\ pop_assum (qspecl_then [‘tag’, ‘LENGTH x’] mp_tac)
  \\ match_mp_tac (METIS_PROVE [] “a /\ (a /\ b ==> c) ==> ((a ==> b) ==> c)”)
  \\ ‘16 * tag < dimword (:'a) /\ 2 * LENGTH x < dimword (:'a)’ by
   (fs [data_to_wordTheory.encode_header_def, arithmeticTheory.X_LT_DIV,
        data_to_wordTheory.small_int_def,GSYM dimword_def])
  \\ conj_tac
  >- (fs [Smallnum_def,
          data_to_wordTheory.shift_length_def]
      \\ rewrite_tac [GSYM w2n_11, w2n_lsr]
      \\ fs [ONCE_REWRITE_RULE [arithmeticTheory.MULT_COMM]
               arithmeticTheory.MULT_DIV]
      \\ fs [data_to_word_gcProofTheory.state_rel_def,
             data_to_word_memoryProofTheory.heap_in_memory_store_def,
             data_to_wordTheory.shift_length_def])
  \\ strip_tac \\ fs []
  \\ ‘w2n w = 2 * LENGTH x’ by
   (qpat_assum ‘state_rel c l1 l2 s t NONE locs’ assume_tac
    \\ rpt_drule0 state_rel_get_var_Number_IMP
    \\ fs [data_to_wordTheory.adjust_var_def, wordSemTheory.get_var_def,
           Smallnum_def])
  \\ fs [data_to_word_gcProofTheory.state_rel_thm,
         dataSemTheory.get_var_def]
  \\ full_simp_tac std_ss [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]
  \\ fs [data_to_word_gcProofTheory.code_oracle_rel_def,
         finite_mapTheory.FLOOKUP_UPDATE]
  \\ rpt_drule0 memory_rel_lookup
  \\ fs [data_to_wordTheory.adjust_var_def]
  \\ qabbrev_tac ‘hd_word = (Smallnum (&(8 * tag)) || (3w:'a word) ||
                       (Smallnum (&LENGTH x) << (dimindex (:'a) - c.len_size - 1)))’
  \\ fs [data_to_wordTheory.list_Seq_def]
  \\ strip_tac \\ fs [listTheory.LENGTH_NIL]
  \\ assume_tac (GEN_ALL FromList1_code_thm)
  \\ SEP_I_TAC "evaluate"
  \\ pop_assum mp_tac
  \\ fs [wordSemTheory.set_var_def, wordSemTheory.get_var_def, lookup_insert]
  \\ ‘(?md. lookup FromList1_location s1'.code = SOME (6, FromList1_code c,md))’ by
       (fs [data_to_word_gcProofTheory.code_rel_def,
            data_to_wordTheory.stubs_md_def,data_to_wordTheory.stubs_def,
            MAP_MAP_o,o_DEF])
  \\ rfs []
  \\ disch_then (qspec_then ‘c’ mp_tac)
  \\ ‘encode_header c (4 * tag) (LENGTH x) =
      SOME (make_header c (4 * tag) (LENGTH x))’ by
       (fs [encode_header_def,dimword_def,EXP]
        \\ fs [good_dimindex_def] \\ fs [GSYM EXP_SUB])
  \\ ‘hd_word = (n2w (make_header c (4 * tag) (LENGTH x)):'a word)’ by
       (fs [Abbr ‘hd_word’,make_header_def,Smallnum_def,
            word_lsl_n2w,word_mul_n2w,WORD_MUL_LSL]
        \\ ‘dimindex (:α) - c.len_size =
            dimindex (:α) - (c.len_size + 1) + 1’ by
             (fs [memory_rel_def,heap_in_memory_store_def] \\ DECIDE_TAC)
        \\ ‘2 * (LENGTH x * 2 ** (dimindex (:α) - (c.len_size + 1))) =
            LENGTH x * 2 ** (dimindex (:α) - c.len_size)’ by
             (qpat_x_assum `dimindex (:α) - c.len_size = _`
                (fn th => once_rewrite_tac [th])
              \\ simp_tac std_ss [EXP_ADD]
              \\ simp_tac std_ss [AC MULT_ASSOC MULT_COMM])
        \\ asm_rewrite_tac []
        \\ ‘(n2w (16 * tag):'a word) || 3w = n2w (16 * tag + 3)’ by
             (rewrite_tac [GSYM word_add_n2w]
              \\ match_mp_tac (GSYM WORD_ADD_OR)
              \\ ‘n2w (16 * tag):'a word = n2w tag << 4’ by
                   simp [addressTheory.word_LSL_n2w]
              \\ asm_rewrite_tac []
              \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [wordsTheory.word_index]
              \\ DECIDE_TAC)
        \\ once_rewrite_tac [WORD_OR_ASSOC] \\ asm_rewrite_tac []
        \\ ‘16 * tag + (LENGTH x * 2 ** (dimindex (:α) -
              (c.len_size + 1) + 1) + 3) =
            LENGTH x * 2 ** (dimindex (:α) - (c.len_size + 1) + 1) +
              (16 * tag + 3)’ by DECIDE_TAC
        \\ asm_rewrite_tac []
        \\ irule multiplied_header_or
        \\ `c.len_size <> 0 /\ c.len_size + 9 < dimindex (:'a)` by
             (qpat_x_assum `memory_rel c _ _ _ _ _ _ _ _`
                (fn th => ACCEPT_TAC (MATCH_MP memory_rel_len_size th)))
        \\ ‘4 * tag < 2 ** (dimindex (:α) - c.len_size - 2)’ by
             (qpat_x_assum `encode_header c (4 * tag) (LENGTH x) = _` mp_tac
              \\ simp_tac std_ss [encode_header_def]
              \\ asm_rewrite_tac [] \\ simp_tac std_ss [])
        \\ ‘2 ** (dimindex (:α) - c.len_size) =
            4 * 2 ** (dimindex (:α) - c.len_size - 2)’ by
             (‘dimindex (:α) - c.len_size =
                 2 + (dimindex (:α) - c.len_size - 2)’ by DECIDE_TAC
              \\ qpat_x_assum `dimindex (:α) - c.len_size = 2 + _`
                   (fn th => once_rewrite_tac [th])
              \\ simp_tac std_ss [EXP_ADD])
        \\ fs [] \\ DECIDE_TAC)
  \\ ‘LENGTH x < s0.space’
       by (fs [Abbr ‘s0’,
               SIMP_RULE std_ss [Once arithmeticTheory.MULT_COMM]
                                arithmeticTheory.MULT_DIV])
  \\ rpt_drule0 data_to_word_memoryProofTheory.memory_rel_FromList
  \\ Cases_on ‘x’ \\ fs []
  \\ qabbrev_tac ‘x = h::t'’
  \\ ‘x ≠ []’ by rw [Abbr ‘x’]
  \\ qpat_x_assum ‘Abbrev _’ (K ALL_TAC)
  \\ Cases_on ‘s.tstamps’ \\ fs []
  \\ rename [‘s.tstamps = SOME next_ts’]
  \\ strip_tac \\ fs []
  \\ disch_then drule
  \\ impl_tac
  >- (fs [Abbr ‘s0’,
          ONCE_REWRITE_RULE [arithmeticTheory.MULT_COMM] arithmeticTheory.MULT_DIV,
          Smallnum_def])
  \\ strip_tac
  \\ fs [lookup_def, EVAL ``join_env LN []``]
  \\ fs [Abbr ‘s0’]
  \\ fs [finite_mapTheory.FAPPLY_FUPDATE_THM, finite_mapTheory.FLOOKUP_UPDATE]
  \\ rfs []
  \\ fs [dataSemTheory.pop_env_def, is_env_def,
         CaseEq "list", CaseEq "stack", CaseEq "option", CaseEq "bool",
         dataSemTheory.check_lim_def, dataSemTheory.do_stack_def]
  \\ rveq \\ rfs [] \\ rveq \\ rfs []
  \\ conj_tac >- (drule option_le_add_indv \\ rw [backendPropsTheory.option_le_max_right])
  \\ conj_tac
  >- (imp_res_tac data_to_word_gcProofTheory.stack_rel_simp
      \\ imp_res_tac data_to_word_gcProofTheory.stack_rel_IMP_size_of_stack
      \\ fs [wordPropsTheory.stack_size_eq, dataSemTheory.stack_consumed_def]
      \\ simp [dataPropsTheory.size_of_stack_eq,
               backendPropsTheory.option_le_max_right,
               backendPropsTheory.option_le_max,
               backendPropsTheory.option_map2_max_add,
               AC backendPropsTheory.option_add_comm backendPropsTheory.option_add_assoc,
               backendPropsTheory.option_le_eq_eqns,
               backendPropsTheory.option_map2_max_add,
               wordPropsTheory.stack_size_eq])
  \\ drule0 data_to_word_memoryProofTheory.memory_rel_zero_space
  \\ match_mp_tac data_to_word_memoryProofTheory.memory_rel_rearrange
  \\ fs [] \\ rw [] \\ fs []
QED

(* ---- helpers used by assign_FromList's NES/Success arms (also reused by
   assign_RefByte etc. below); hoisted above assign_FromList so they are in
   scope here. ---- *)

(* do_app for FromList sets the result stack_max uniformly (stack_consumed is
   the same for the empty and nonempty cases), regardless of tstamps. *)

Theorem do_app_FromList_stack_max[local]:
  do_app (BlockOp (FromList tag)) vals s = Rval (v, s') ==>
  s'.stack_max = OPTION_MAP2 MAX s.stack_max
    (OPTION_MAP2 $+
       (stack_consumed s.stack_frame_sizes s.limits (BlockOp (FromList tag)) vals)
       (OPTION_MAP2 $+ (size_of_stack s.stack) s.locals_size))
Proof
  simp [dataSemTheory.do_app_def, dataSemTheory.do_app_aux_def, dataSemTheory.do_space_def,
        dataSemTheory.do_stack_def, dataSemTheory.with_fresh_ts_def, dataSemTheory.check_lim_def,
        dataLangTheory.op_space_reset_def, dataSemTheory.allowed_op_def,
        dataSemTheory.consume_space_def, AllCaseEqs()]
  \\ rw [] \\ fs []
QED

(* do_app for FromList: the result safe_for_space field, uniform over the empty
   and nonempty cases (the empty case lacks the with_fresh_ts/check_lim wrapper,
   but its extra `LENGTH ys < 2 ** length_limit` conjunct is trivially true). The
   add_space_safe_args / the F terms are dataSem overloads; the statement spells
   them out so it parses without the abbreviation. *)

Theorem do_app_FromList_safe[local]:
  v_to_list v2 = SOME ys /\
  do_app (BlockOp (FromList tag)) [Number (&LENGTH ys); v2] (s:('c,'ffi) dataSem$state) = Rval (v,s') ==>
  (s'.safe_for_space <=>
   (((small_num s.limits.arch_64_bit (&LENGTH ys) /\
      LENGTH ys < 2 ** s.limits.length_limit /\
      LENGTH ys < arch_size s.limits DIV 16 /\
      4 * tag < 2 ** (arch_size s.limits − (s.limits.length_limit + 2)) /\
      4 * tag < 2 ** arch_size s.limits DIV 16) /\
     (s.safe_for_space /\
      no_thunks_in_refs s.refs /\
      size_of_heap_args [Number (&LENGTH ys); v2] s + (LENGTH ys + 1) <= s.limits.heap_limit)) /\
    the F (OPTION_MAP ($> s.limits.stack_limit)
      (OPTION_MAP2 $+ (OPTION_MAP2 MAX (lookup FromList_location s.stack_frame_sizes)
                                        (lookup FromList1_location s.stack_frame_sizes))
                      (OPTION_MAP2 $+ (size_of_stack s.stack) s.locals_size)))))
Proof
  strip_tac
  \\ Cases_on `ys`
  \\ gvs [dataSemTheory.do_app_def, dataSemTheory.do_app_aux_def, dataSemTheory.do_space_def,
          dataSemTheory.do_stack_def, dataSemTheory.with_fresh_ts_def, dataSemTheory.check_lim_def,
          dataSemTheory.space_consumed_def, dataSemTheory.arch_size_def, dataSemTheory.stack_consumed_def,
          dataLangTheory.op_space_reset_def, dataSemTheory.allowed_op_def,
          dataSemTheory.consume_space_def, AllCaseEqs()]
  \\ metis_tac []
QED

(* do_app for FromList: the result value is a Block of the source list, and the
   non-stack/safe/space fields are preserved from the input state (tstamps gains
   a fresh stamp for nonempty lists). Used by assign_FromList's success arm to
   relate s2 (do_app on x) and s2_inner (do_app on s_pop): both share these
   fields because x and s_pop agree on locals/refs/tstamps/.... *)

Theorem do_app_FromList_eq[local]:
  v_to_list v2 = SOME ys /\
  do_app (BlockOp (FromList tag)) [Number (&LENGTH ys); v2] (s:('c,'ffi) dataSem$state) = Rval (v,s') ==>
  (?ts'. v = Block ts' tag ys) /\ s'.space = 0 /\
  s'.refs = s.refs /\ s'.code = s.code /\ s'.ffi = s.ffi /\ s'.handler = s.handler /\
  s'.locals = s.locals /\ s'.stack = s.stack /\ s'.limits = s.limits /\
  s'.stack_frame_sizes = s.stack_frame_sizes /\ s'.locals_size = s.locals_size /\
  s'.global = s.global /\ s'.compile = s.compile /\ s'.compile_oracle = s.compile_oracle /\
  s'.clock = s.clock /\
  s'.tstamps = (if ys = [] then s.tstamps else OPTION_MAP SUC s.tstamps)
Proof
  strip_tac \\ Cases_on ‘ys’
  \\ gvs [dataSemTheory.do_app_def, dataSemTheory.do_app_aux_def, dataSemTheory.do_space_def,
          dataSemTheory.do_stack_def, dataSemTheory.with_fresh_ts_def, dataSemTheory.check_lim_def,
          dataSemTheory.space_consumed_def, dataSemTheory.arch_size_def, dataSemTheory.stack_consumed_def,
          dataLangTheory.op_space_reset_def, dataSemTheory.allowed_op_def,
          dataSemTheory.consume_space_def, AllCaseEqs()]
QED

Theorem assign_FromList:
  (?tag. op = BlockOp (FromList tag)) ==> ^assign_thm_goal
Proof
  rpt strip_tac
  >> drule0 (evaluate_GiveUp2 |> GEN_ALL) >> rw [] >> fs []
  >> ‘t.termdep <> 0’ by fs []
  >> ‘option_le x.stack_max s2.stack_max’ by metis_tac [do_app_stack_max]
  >> rpt_drule0 data_to_word_gcProofTheory.state_rel_cut_IMP >> strip_tac
  >> fs [data_to_wordTheory.assign_def] >> rveq
  >> fs [dataLangTheory.op_requires_names_def,
         dataLangTheory.op_space_reset_def,dataSemTheory.cut_state_opt_def]
  >> Cases_on ‘names_opt’ >> fs []
  >> drule_all (state_rel_cut_state_opt_SOME
                  |> SRULE [dataSemTheory.cut_state_opt_def])
  >> strip_tac
  >> qpat_x_assum ‘_ (t with locals := y) NONE locs’
       $ ASSUME_NAMED_TAC "with_locals"
  >> imp_res_tac data_to_word_gcProofTheory.get_vars_IMP_LENGTH
  >> fs [] >> rw []
  >> fs [do_app,dataSemTheory.allowed_op_def]
  >> ‘?v vs. vals = [Number (&LENGTH vs); v] /\ v_to_list v = SOME vs’
       by (every_case_tac >> fs [] >> rw [] >> NO_TAC)
  >> clean_tac
  >> imp_res_tac data_to_word_gcProofTheory.state_rel_get_vars_IMP
  >> fs [LENGTH_EQ_2] >> clean_tac
  >> fs [LENGTH_EQ_2] >> clean_tac
  >> fs [data_to_wordTheory.arg2_def, data_to_wordTheory.assign_FromList_def]
  >> IF_CASES_TAC >> fs []
  >- (* NES_encode arm (encode_header = NONE: GiveUp) *)
   (conj_tac
    >- (‘x.stack_max = s.stack_max ∧ option_le t.stack_max s.stack_max’ by
          (qpat_x_assum ‘cut_state x' s = SOME x’ mp_tac
           \\ fs [dataSemTheory.cut_state_def, AllCaseEqs(), data_to_word_gcProofTheory.state_rel_def]
           \\ rw [] \\ gvs [])
        >> metis_tac [backendPropsTheory.option_le_trans])
    >> strip_tac
    >> spose_not_then strip_assume_tac
    >> qpat_x_assum ‘_ = Rval (v,s2)’ mp_tac
    >> ‘x.limits.length_limit = c.len_size ∧ arch_size x.limits = dimindex (:'a)’
      by (fs [data_to_word_gcProofTheory.state_rel_def, data_to_word_gcProofTheory.limits_inv_def,
              dataSemTheory.arch_size_def, miscTheory.good_dimindex_def]
          >> rfs [])
    >> ‘arch_width_bits c.arch_width = dimindex (:'a)’ by
         fs [state_rel_def,heap_in_memory_store_def]
    >> ‘dimword (:'a) = 2 ** dimindex (:'a)’ by fs [dimword_def]
    >> Cases_on ‘vs’
    >- (simp [] >> rw [] >> gvs [dataSemTheory.with_fresh_ts_def, ELIM_UNCURRY,
                                 dataSemTheory.check_lim_def]
        >> qpat_x_assum ‘encode_header _ _ _ = NONE’ mp_tac
        >> simp [data_to_wordTheory.encode_header_def]
        >> rw [] >> disj2_tac >> strip_tac
        >> pop_assum (mp_tac o Q.AP_TERM ‘λs:('c,'ffi) dataSem$state. s.safe_for_space’)
        >> simp [])
    >> simp [] >> rw [] >> gvs [dataSemTheory.with_fresh_ts_def, ELIM_UNCURRY,
                                dataSemTheory.check_lim_def]
    >> qpat_x_assum ‘encode_header _ _ _ = NONE’ mp_tac
    >> simp [data_to_wordTheory.encode_header_def]
    >> rw [] >> Cases_on ‘x.tstamps’ >- fs [data_to_word_gcProofTheory.state_rel_def] >> rfs []
    >> simp [] >> disj2_tac >> strip_tac
    >> pop_assum (mp_tac o Q.AP_TERM ‘λs:('c,'ffi) dataSem$state. s.safe_for_space’)
    >> simp [])
  (* Main arm (encode OK: Call FromList_code) *)
  \\ clean_tac \\ fs []
  \\ drule0 lookup_RefByte_location \\ strip_tac \\ fs [get_names_def]
  \\ fs [wordSemTheory.evaluate_def, list_Seq_def, word_exp_rw,
         wordSemTheory.find_code_def, wordSemTheory.set_var_def]
  \\ fs [wordSemTheory.add_ret_loc_def, wordSemTheory.find_code_def]
  \\ fs [wordSemTheory.bad_dest_args_def, wordSemTheory.get_vars_def,
         wordSemTheory.get_var_def, lookup_insert]
  (* Body *)
  \\ `dataSem$cut_env x' s.locals = SOME x.locals` by
       (qpat_x_assum `cut_state x' s = SOME x` mp_tac
        \\ simp [dataSemTheory.cut_state_def, AllCaseEqs()] \\ rw [] \\ fs [])
  \\ `state_rel c l1 l2 (s with clock := MustTerminate_limit(:'a))
        (t with <|clock := MustTerminate_limit(:'a); termdep := t.termdep - 1|>) NONE locs` by
       (qpat_assum `state_rel c l1 l2 s t NONE locs`
          (mp_tac o MATCH_MP (data_to_word_gcProofTheory.state_rel_with_clock
                                |> Q.GEN `k` |> Q.SPEC `MustTerminate_limit(:'a)`))
        \\ fs [data_to_word_gcProofTheory.state_rel_def])
  \\ drule0 data_to_word_gcProofTheory.cut_env_IMP_cut_envs \\ strip_tac
  \\ `wordSem$get_vars [adjust_var a1''; adjust_var a2''] t = SOME [a1; a2]` by
       fs [wordSemTheory.get_vars_def, wordSemTheory.get_var_def]
  \\ rpt_drule0 data_to_word_gcProofTheory.state_rel_call_env_push_env \\ fs []
  \\ disch_then drule0 \\ fs []
  \\ disch_then drule0 \\ fs []
  \\ disch_then (qspecl_then [`lookup FromList_location t.stack_size`, `n`, `l`, `NONE`] mp_tac)
  \\ strip_tac
  \\ simp [wordSemTheory.evaluate_def, wordSemTheory.set_var_def,
           wordSemTheory.word_exp_def, wordSemTheory.get_var_def,
           wordSemTheory.get_vars_def, lookup_insert,
           wordSemTheory.bad_dest_args_def,
           wordSemTheory.add_ret_loc_def, wordSemTheory.find_code_def,
           data_to_wordTheory.get_names_def,
           data_to_word_gcProofTheory.cut_envs_adjust_sets_ODD,
           domain_adjust_sets]
  \\ `lookup (adjust_var a1'') t.locals = SOME a1 /\ lookup (adjust_var a2'') t.locals = SOME a2` by
       fs [wordSemTheory.get_vars_def, wordSemTheory.get_var_def, AllCaseEqs()]
  \\ simp [wordSemTheory.find_code_def]
  \\ `arch_width_bits c.arch_width = dimindex (:'a)` by
       fs [state_rel_def,heap_in_memory_store_def]
  \\ `4 * tag < dimword (:α) DIV 16` by
       fs [data_to_wordTheory.encode_header_def,dimword_def]
  \\ `8 * tag < dimword (:α) DIV 8` by
       (`good_dimindex (:'a)` by fs [data_to_word_gcProofTheory.state_rel_def]
        \\ qpat_x_assum `4 * tag < dimword (:α) DIV 16` mp_tac
        \\ pop_assum mp_tac \\ rpt (pop_assum kall_tac)
        \\ rw [miscTheory.good_dimindex_def] \\ gvs [dimword_def])
  \\ qpat_x_assum `state_rel c n l (call_env [Number (&LENGTH vs); v'] _ _) (call_env [Loc n l; a1; a2] _ _) NONE _` assume_tac
  \\ drule0 (Q.SPEC `8 * tag` (Q.GEN `n` data_to_word_gcProofTheory.state_rel_IMP_Number_arg))
  \\ impl_tac >- fs []
  \\ strip_tac \\ fs []
  \\ qmatch_assum_abbrev_tac `state_rel c n l (call_env _ _ st_inner_data) (call_env _ _ st_inner_word) NONE _`
  \\ qabbrev_tac `ts = call_env [Number (&LENGTH vs); v'; Number (&(8 * tag))]
                       (lookup FromList_location t.stack_size) st_inner_data`
  \\ qabbrev_tac `twAbv = call_env [Loc n l; a1; a2; Word (n2w (16 * tag):α word)]
                       (lookup FromList_location t.stack_size) st_inner_word`
  \\ `is_env (HD ts.stack)` by
       (unabbrev_all_tac \\ simp [dataSemTheory.call_env_def, dataSemTheory.push_env_def,
                 dataSemTheory.dec_clock_def, is_env_def] \\ metis_tac [])
  \\ `twAbv.clock = MustTerminate_limit (:'a) - 1` by
       (unabbrev_all_tac \\ simp [wordSemTheory.call_env_def, wordSemTheory.push_env_def,
                 wordSemTheory.dec_clock_def] \\ pairarg_tac \\ fs [])
  \\ qabbrev_tac `s_pop = s with <|locals := x.locals; clock := MustTerminate_limit (:'a) - 1;
                 stack_max := ts.stack_max; safe_for_space := ts.safe_for_space|>`
  \\ `pop_env ts = SOME s_pop` by
       (unabbrev_all_tac \\ simp [dataSemTheory.call_env_def, dataSemTheory.push_env_def,
                 dataSemTheory.pop_env_def, dataSemTheory.dec_clock_def,
                 dataSemTheory.state_component_equality])
  \\ `ts.locals_size = lookup FromList_location ts.stack_frame_sizes` by
       (unabbrev_all_tac \\ simp [dataSemTheory.call_env_def, dataSemTheory.push_env_def,
                 dataSemTheory.dec_clock_def] \\ fs [data_to_word_gcProofTheory.state_rel_def])
  \\ `get_vars [0;1;2] ts.locals = SOME [Number (&LENGTH vs); v'; Number (&(8 * tag))]` by
       (unabbrev_all_tac \\ simp [dataSemTheory.get_vars_def, dataSemTheory.call_env_def,
                 dataSemTheory.get_var_def, dataSemTheory.push_env_def,
                 dataSemTheory.dec_clock_def, sptreeTheory.lookup_fromList])
  (* do_app on s_pop reproduces the assign's result value v (same tstamps, same vs). *)
  \\ `?s2_inner. do_app (BlockOp (FromList tag)) [Number (&LENGTH vs); v'] s_pop = Rval (v, s2_inner)` by
       (`x = s with locals := mk_wf (inter s.locals x')` by
          (`cut_state_opt (SOME x') s = SOME x` by fs [dataSemTheory.cut_state_opt_def]
           \\ drule cut_state_opt_SOME_eq \\ simp [])
        \\ simp [Abbr `s_pop`]
        \\ qpat_x_assum `x = s with locals := _` (fn th => full_simp_tac std_ss [th])
        \\ Cases_on `vs`
        \\ fs [dataSemTheory.do_app_def, dataSemTheory.do_app_aux_def,
               dataSemTheory.do_space_def, dataSemTheory.do_stack_def,
               dataSemTheory.space_consumed_def, dataLangTheory.op_space_reset_def,
               dataSemTheory.allowed_op_def, dataSemTheory.check_lim_def,
               dataSemTheory.with_fresh_ts_def]
        \\ Cases_on `s.tstamps` \\ fs [])
  (* extra FromList_thm hyps: stack_max monotone + the heap-NES bridge. *)
  \\ `option_le ts.stack_max s2_inner.stack_max` by
       (`option_le s_pop.stack_max s2_inner.stack_max` by metis_tac [do_app_stack_max]
        \\ `s_pop.stack_max = ts.stack_max` by simp [Abbr `s_pop`]
        \\ fs [])
  \\ `small_num s.limits.arch_64_bit (&(8 * tag))` by
       (qpat_x_assum `encode_header c (4 * tag) 0 ≠ NONE` mp_tac
        \\ simp [data_to_wordTheory.encode_header_def] \\ strip_tac
        \\ `s.limits.arch_64_bit ⇔ dimindex (:α) = 64` by
             fs [data_to_word_gcProofTheory.state_rel_thm, data_to_word_gcProofTheory.limits_inv_def]
        \\ fs [dataSemTheory.small_num_def, dimword_def, miscTheory.good_dimindex_def]
        \\ `good_dimindex (:α)` by fs [data_to_word_gcProofTheory.state_rel_thm]
        \\ fs [miscTheory.good_dimindex_def] \\ rfs []
        \\ qpat_x_assum `4 * tag < 2 ** dimindex (:α) DIV 16` mp_tac
        \\ asm_rewrite_tac [] \\ EVAL_TAC \\ decide_tac)
  \\ `size_of_heap (cut_locals (fromList [();();()]) ts) <=
        size_of_heap_args [Number (&LENGTH vs); v'] s_pop` by
       (simp [Abbr `ts`, Abbr `s_pop`, Abbr `st_inner_data`]
        \\ simp [dataSemTheory.size_of_heap_def, dataSemTheory.size_of_heap_args_def,
                 data_to_word_gcProofTheory.cut_locals_def, dataSemTheory.cut_env_def,
                 dataSemTheory.stack_to_vs_def, dataSemTheory.call_env_def,
                 dataSemTheory.push_env_def, dataSemTheory.dec_clock_def,
                 dataSemTheory.extract_stack_def]
        \\ simp [sptreeTheory.domain_fromList]
        \\ simp [sptreeTheory.fromList_def]
        \\ simp [Once sptreeTheory.inter_def]
        \\ `toList (inter (insert 2 (Number (&(8 * tag))) (insert 1 v' (insert 0 (Number (&LENGTH vs)) LN)))
                          (insert 2 () (insert 1 () (insert 0 () LN)))) =
              [Number (&(8 * tag)); Number (&LENGTH vs); v']` by EVAL_TAC
        \\ simp [dataSemTheory.extract_stack_def]
        \\ qpat_x_assum `toList (inter _ _) = _` (fn th => rewrite_tac [th])
        \\ qpat_x_assum `small_num s.limits.arch_64_bit (&(8 * tag))`
             (fn th => simp [size_of_Number_head, th]))
  (* apply the args-aware FromList encapsulation lemma; reconcile the Call state. *)
  \\ rpt_drule0 FromList_thm
  \\ disch_then (qspecl_then [`l2`, `l1`] mp_tac)
  \\ strip_tac \\ pop_assum strip_assume_tac
  \\ qmatch_goalsub_abbrev_tac `evaluate (FromList_code c, twC)`
  \\ `twC = twAbv` by
       (unabbrev_all_tac
        \\ rw [wordSemTheory.call_env_def, wordSemTheory.push_env_def,
               wordSemTheory.dec_clock_def, wordSemTheory.state_component_equality]
        \\ pairarg_tac \\ fs [])
  \\ fs []
  \\ Cases_on `q = SOME NotEnoughSpace` \\ fs []
  >- (* FromListNES arm *)
   (conj_tac
    >- (qpat_x_assum `Abbrev (twAbv = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])
        \\ simp [wordSemTheory.call_env_def, wordSemTheory.push_env_def,
                 wordSemTheory.dec_clock_def, UNCURRY_DEF]
        \\ pairarg_tac \\ fs []
        \\ qpat_x_assum `state_rel c l1 l2 s t NONE locs` assume_tac
        \\ fs [data_to_word_gcProofTheory.state_rel_def])
    \\ conj_tac
    >- (qpat_x_assum `state_rel c l1 l2 s t NONE locs` assume_tac
        \\ `s.stack_frame_sizes = t.stack_size` by fs [data_to_word_gcProofTheory.state_rel_def]
        \\ `t.locals_size = s.locals_size` by fs [data_to_word_gcProofTheory.state_rel_def]
        \\ qpat_x_assum `option_le r'.stack_max s2_inner.stack_max` assume_tac
        \\ `!z. option_le s2_inner.stack_max z ==> option_le r'.stack_max z` by
          metis_tac [backendPropsTheory.option_le_trans]
        \\ first_x_assum match_mp_tac
        \\ `do_app (BlockOp (FromList tag)) [Number (&LENGTH vs); v'] x = Rval (v,s2)` by
          (qpat_x_assum `v_to_list v' = SOME vs` assume_tac
           \\ simp [do_app, dataSemTheory.allowed_op_def] \\ pop_assum (fn th => fs [th]))
        \\ imp_res_tac do_app_FromList_stack_max
        \\ ntac 2 (qpat_x_assum `_.stack_max = OPTION_MAP2 MAX _ _` (fn th => simp [th]))
        \\ simp [Abbr `s_pop`]
        \\ `x.stack_frame_sizes = s.stack_frame_sizes ∧
            x.limits = s.limits ∧ x.stack = s.stack ∧
            x.locals_size = s.locals_size ∧ x.stack_max = s.stack_max` by
          (`cut_state_opt (SOME x') s = SOME x` by fs [dataSemTheory.cut_state_opt_def]
           \\ drule cut_state_opt_SOME_eq \\ simp [])
        \\ simp []
        \\ simp [Abbr `ts`, Abbr `st_inner_data`, dataSemTheory.stack_consumed_def]
        \\ asm_simp_tac (srw_ss()) [call_env_push_env_dec_clock_stack_max]
        \\ irule option_le_stackmax_bridge)
    >- (* conj3: c.gc_kind <> None ==> ~s2.safe_for_space (heap-NES bound) *)
     (strip_tac
      \\ `cut_state_opt (SOME x') s = SOME x` by fs [dataSemTheory.cut_state_opt_def]
      \\ drule cut_state_opt_SOME_eq \\ strip_tac
      \\ `do_app (BlockOp (FromList tag)) [Number (&LENGTH vs); v'] x = Rval (v,s2)` by
           (qpat_x_assum `v_to_list v' = SOME vs` assume_tac \\ simp [do_app, allowed_op_def]
            \\ pop_assum (fn th => fs [th]))
      \\ drule_all do_app_FromList_safe \\ disch_then (fn th => rewrite_tac [th])
      \\ `ts.limits = x.limits ∧ s_pop.limits = x.limits` by
           (qpat_x_assum `Abbrev (ts = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])
            \\ qpat_x_assum `Abbrev (st_inner_data = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])
            \\ qpat_x_assum `Abbrev (s_pop = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])
            \\ qpat_x_assum `x = _` (fn th => asm_rewrite_tac [th])
            \\ simp [dataSemTheory.call_env_def, dataSemTheory.push_env_def, dataSemTheory.dec_clock_def])
      \\ `x.limits = s.limits` by (qpat_x_assum `x = _` (fn th => simp [th]))
      \\ `size_of_heap_args [Number (&LENGTH vs); v'] s_pop = size_of_heap_args [Number (&LENGTH vs); v'] x` by
           (qpat_x_assum `Abbrev (s_pop = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])
            \\ qpat_x_assum `x = _` (fn th => asm_rewrite_tac [th])
            \\ simp [dataSemTheory.size_of_heap_args_def, dataSemTheory.size_of_heap_def, dataSemTheory.stack_to_vs_def])
      \\ `c.len_size = x.limits.length_limit ∧ arch_size x.limits = dimindex (:α) ∧ dimword (:α) = 2 ** dimindex (:α)` by
           (qpat_x_assum `state_rel c l1 l2 s t NONE locs` assume_tac
            \\ qpat_x_assum `x.limits = s.limits` (fn th => simp [th])
            \\ fs [data_to_word_gcProofTheory.state_rel_def, data_to_word_gcProofTheory.limits_inv_def,
                   dataSemTheory.arch_size_def, miscTheory.good_dimindex_def, dimword_def])
      \\ `arch_size x.limits DIV 16 ≤ dimword (:α) DIV 16` by
           (qpat_x_assum `arch_size x.limits = _` (fn th => rewrite_tac [th])
            \\ qpat_x_assum `dimword (:α) = _` (fn th => rewrite_tac [th])
            \\ irule DIV_LE_MONOTONE \\ simp [arithmeticTheory.X_LT_EXP_X, arithmeticTheory.LESS_IMP_LESS_OR_EQ])
      \\ strip_tac
      \\ ‘no_thunks_in_refs ts.refs’ by
        (qsuff_tac ‘ts.refs = x.refs’ >- metis_tac []
         \\ unabbrev_all_tac \\ simp [call_env_def])
      \\ qpat_x_assum `c.gc_kind ≠ None ∧ _ ⇒ _` mp_tac
      \\ asm_rewrite_tac []
      \\ rfs [dataSemTheory.space_consumed_def]))
  (* FromListSucc arm *)
  \\ qpat_x_assum ‘state_rel c l1 l2 _ r' (SOME [(v,rv)]) _’ assume_tac
  \\ drule data_to_word_gcProofTheory.state_rel_pop_env_IMP
  \\ qpat_x_assum ‘Abbrev (ts = _)’ (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])
  \\ qpat_x_assum ‘Abbrev (st_inner_data = _)’ (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])
  \\ simp [dataSemTheory.push_env_def, dataSemTheory.call_env_def,
           dataSemTheory.pop_env_def, dataSemTheory.dec_clock_def]
  \\ strip_tac
  \\ qpat_x_assum ‘Abbrev (twAbv = _)’ (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])
  \\ qpat_x_assum ‘Abbrev (st_inner_word = _)’ (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])
  \\ fs []
  \\ qpat_x_assum ‘state_rel c n l (call_env _ _ (push_env _ F _)) (call_env _ _ (push_env (y1,y2) NONE _)) _ _’ assume_tac
  \\ drule state_rel_push_env_loc
  \\ disch_then assume_tac
  \\ fs [call_env_push_env_dec_clock_lift_locals]
  \\ drule_all evaluate_IMP_domain_union
  \\ disch_then assume_tac
  \\ fs []
  \\ fs [data_to_word_gcProofTheory.state_rel_def]
  \\ unabbrev_all_tac
  \\ fs []
  \\ simp [dataSemTheory.set_var_def, wordSemTheory.set_vars_def,
           wordSemTheory.set_var_def, sptreeTheory.alist_insert_def, lookup_insert]
  \\ imp_res_tac do_app_FromList_eq
  \\ ‘do_app (BlockOp (FromList tag)) [Number (&LENGTH vs); v'] x = Rval (v, s2)’ by
       (qpat_x_assum ‘_ = Rval (v, s2)’ mp_tac
        \\ simp [do_app, dataSemTheory.allowed_op_def])
  \\ qpat_assum ‘v_to_list v' = SOME vs’ (fn vth =>
       qpat_x_assum ‘do_app (BlockOp (FromList tag)) [Number (&LENGTH vs); v'] x = Rval (v,s2)’
         (fn dth => strip_assume_tac (MATCH_MP do_app_FromList_eq (CONJ vth dth))))
  \\ ‘x = s with locals := x.locals’ by
       (qpat_x_assum ‘cut_state x' s = SOME x’ mp_tac
        \\ simp [dataSemTheory.cut_state_def]
        \\ qpat_x_assum ‘cut_env x' s.locals = SOME x.locals’ (fn th => simp [th])
        \\ strip_tac \\ gvs [])
  \\ ‘x.code = s.code ∧ x.stack = s.stack ∧ x.locals_size = s.locals_size ∧
      x.stack_frame_sizes = s.stack_frame_sizes ∧ x.limits = s.limits ∧
      x.tstamps = s.tstamps ∧ x.global = s.global ∧ x.refs = s.refs ∧
      x.stack_max = s.stack_max ∧ x.ffi = s.ffi ∧ x.handler = s.handler ∧
      x.clock = s.clock ∧ x.compile = s.compile ∧ x.compile_oracle = s.compile_oracle’ by
       (qpat_x_assum ‘x = s with locals := x.locals’ (fn th => once_rewrite_tac [th]) \\ simp [])
  \\ fs []
  \\ conj_tac
  >- (rw [lookup_insert, data_to_word_gcProofTheory.adjust_var_11]
      \\ first_x_assum drule \\ simp [])
  \\ conj_tac
  >- (‘s2.stack_max = OPTION_MAP2 MAX s.stack_max
          (OPTION_MAP2 $+ (OPTION_MAP2 MAX (lookup FromList_location s.stack_frame_sizes)
                                           (lookup FromList1_location s.stack_frame_sizes))
                          (OPTION_MAP2 $+ (size_of_stack s.stack) s.locals_size))’ by
         (‘?vv. do_app (BlockOp (FromList tag)) [Number (&LENGTH vs); v'] x = Rval (vv, s2)’ by
            (qpat_x_assum ‘_ = Rval (_, s2)’ (fn th => simp [do_app, dataSemTheory.allowed_op_def, th]))
          \\ pop_assum strip_assume_tac
          \\ drule do_app_FromList_stack_max
          \\ simp [dataSemTheory.stack_consumed_def])
      \\ qpat_x_assum ‘do_app (BlockOp (FromList tag)) [Number (&LENGTH vs); v'] _ = Rval (_, s2_inner)’
           (assume_tac o MATCH_MP do_app_FromList_stack_max)
      \\ qpat_x_assum ‘s2.stack_max = _’ (fn th => rewrite_tac [th])
      \\ qpat_x_assum ‘option_le t2.stack_max s2_inner.stack_max’ mp_tac
      \\ qpat_x_assum ‘s2_inner.stack_max = _’ (fn th => rewrite_tac [th])
      \\ simp [call_env_push_env_dec_clock_stack_max, dataSemTheory.stack_consumed_def]
      \\ strip_tac
      \\ irule backendPropsTheory.option_le_trans
      \\ goal_assum (drule_at Any)
      \\ irule option_le_stackmax_bridge)
  \\ asm_exists_tac \\ fs []
  \\ full_simp_tac std_ss [GSYM listTheory.APPEND_ASSOC]
  \\ match_mp_tac word_ml_inv_insert \\ fs [data_to_word_gcProofTheory.flat_def]
QED

Theorem tag_mod_eq[local]:
  a < d DIV 4 /\ b < d DIV 4 /\
  (2 * a) MOD d = (2 * b) MOD d ==> a = b
Proof
  rw []
  \\ `2 * a < d /\ 2 * b < d` by (fs [X_LT_DIV] \\ DECIDE_TAC)
  \\ fs [LESS_MOD]
QED

val _ = augment_srw_ss [rewrites [compiler_tag_mask_i2w]];

Theorem assign_TagEq:
  (∃tag. op = BlockOp (TagEq tag)) ==> ^assign_thm_goal
Proof
  rpt strip_tac
  \\ imp_res_tac state_rel_arch_width
  \\ imp_res_tac state_rel_small_shift_length
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ gvs [do_app,AllCaseEqs(),allowed_op_def]
  \\ fs [assign_def,eq_eval,wordSemTheory.get_store_def,GSYM dimword_def]
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ last_x_assum mp_tac
  \\ simp [Once state_rel_thm] \\ strip_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs [set_var_def]
  \\ strip_tac
  \\ fs [assign_def,list_Seq_def]
  \\ reverse IF_CASES_TAC THEN1
   (eval_tac
    \\ fs [lookup_insert,adjust_var_11,state_rel_thm] \\ rw [] \\ fs []
    \\ rename1 `get_vars [a1] s.locals = SOME [Block t5 n5 l5]`
    \\ `n5 <> tag` by
     (strip_tac \\ clean_tac
      \\ imp_res_tac memory_rel_tag_limit \\ fs [] \\ NO_TAC)
    \\ fs [option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ simp []
    \\ match_mp_tac memory_rel_Boolv_F \\ simp []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC])
  \\ imp_res_tac get_vars_1_imp
  \\ eval_tac \\ fs [wordSemTheory.get_var_def, wordSemTheory.get_var_imm_def,
                     lookup_insert]
  \\ rpt_drule0 memory_rel_Block_IMP \\ strip_tac \\ fs []
  \\ simp [asmTheory.word_cmp_def]
  \\ fs [word_and_one_eq_0_iff |> SIMP_RULE (srw_ss()) []]
  \\ pop_assum mp_tac \\ IF_CASES_TAC \\ fs [state_rel_thm] THEN1
   (fs [word_mul_n2w,word_add_n2w] \\ strip_tac
    \\ simp [asmTheory.word_cmp_def]
    \\ fs [LESS_DIV_4_IMP,DECIDE ``2 * n = 2 * m <=> n = m:num``]
    \\ IF_CASES_TAC \\ fs [lookup_insert]
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs [inter_insert_ODD_adjust_set_alt]
    \\ match_mp_tac memory_rel_Boolv \\ fs [])
  \\ strip_tac \\ fs []
  \\ rename [‘(real_addr c (adjust_var hh))’]
  \\ `!w. word_exp (t with locals := insert 1 (Word w) t.locals)
        (real_addr c (adjust_var hh)) = SOME (Word a)` by
    (strip_tac \\ match_mp_tac (GEN_ALL get_real_addr_lemma)
     \\ fs [wordSemTheory.get_var_def,lookup_insert] \\ NO_TAC) \\ fs []
  \\ simp [asmTheory.word_cmp_def]
  \\ `3 MOD dimword (:'a) = 3` by fs [good_dimindex_def,dimword_def]
  \\ `~(3 >= dimindex (:'a))` by fs [good_dimindex_def]
  \\ imp_res_tac memory_rel_tag_limit
  \\ `arch_width_bits c.arch_width = dimindex (:'a)` by
       (qpat_x_assum `memory_rel c _ _ _ _ _ _ _ _`
          (fn th => ACCEPT_TAC (MATCH_MP memory_rel_arch_width th)))
  \\ `c.len_size <> 0 /\ c.len_size + 9 < dimindex (:'a)` by
       (qpat_x_assum `memory_rel c _ _ _ _ _ _ _ _`
          (fn th => ACCEPT_TAC (MATCH_MP memory_rel_len_size th)))
  \\ rpt_drule0 encode_header_tag_mask_lsr \\ fs []
  \\ fs [LESS_DIV_4_IMP,DECIDE ``2 * n = 2 * m <=> n = m:num``]
  \\ strip_tac \\ fs []
  \\ simp [asmTheory.word_cmp_def]
  \\ fs [LESS_DIV_4_IMP,DECIDE ``2 * n = 2 * m <=> n = m:num``]
  \\ IF_CASES_TAC \\ fs []
  \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs [inter_insert_ODD_adjust_set_alt]
  \\ match_mp_tac memory_rel_Boolv \\ fs [tag_mod_eq]
QED

Theorem all_ones_get_addr:
  all_ones (c.len_bits + (c.tag_bits + 1)) 0 &&
  get_addr c ptr (Word (ptr_bits c tag2 len2)) =
  ptr_bits c tag2 len2 || 1w
Proof
  fs [get_addr_def,get_lowerbits_def,small_shift_length_def]
  \\ fs [WORD_LEFT_AND_OVER_OR]
  \\ `1w && all_ones (c.len_bits + (c.tag_bits + 1)) 0 = 1w` by
   (fs [fcpTheory.CART_EQ,fcpTheory.FCP_BETA,word_and_def,word_slice_def]
    \\ once_rewrite_tac [n2w_def]
    \\ fs [fcpTheory.CART_EQ,fcpTheory.FCP_BETA,word_and_def,word_slice_def]
    \\ rw[] \\ eq_tac \\ rw []
    \\ asm_simp_tac std_ss [all_ones_def,word_slice_def,
          fcpTheory.FCP_BETA,word_1comp_def,n2w_def] \\ fs [])
  \\ fs [] \\ pop_assum kall_tac
  \\ `all_ones (c.len_bits + (c.tag_bits + 1)) 0 && n2w ptr ≪ shift_length c = 0w` by
   (fs [fcpTheory.CART_EQ,fcpTheory.FCP_BETA,word_and_def,n2w_def,word_lsl_def]
    \\ rw [] \\ CCONTR_TAC \\ fs []
    \\ imp_res_tac all_ones_bit \\ fs [shift_length_def])
  \\ fs [] \\ pop_assum kall_tac
  \\ `all_ones (c.len_bits + (c.tag_bits + 1)) 0 &&
        (c.len_bits + c.tag_bits -- 0) (ptr_bits c tag2 len2) =
      (c.len_bits + c.tag_bits -- 0) (ptr_bits c tag2 len2)` by
   (fs [fcpTheory.CART_EQ,fcpTheory.FCP_BETA,word_and_def,n2w_def,word_lsl_def,
        all_ones_bit,word_bits_def]
    \\ rw [] \\ eq_tac \\ rw [])
  \\ fs []
  \\ qsuff_tac `(c.len_bits + c.tag_bits -- 0) (ptr_bits c tag2 len2) =
                (ptr_bits c tag2 len2):'a word` \\ fs []
  \\ fs [ptr_bits_def]
  \\ fs [fcpTheory.CART_EQ,word_bits_def,fcpTheory.FCP_BETA,word_or_def]
  \\ rw [] \\ eq_tac \\ rw []
  \\ imp_res_tac maxout_bits_bit \\ fs []
QED

Theorem MULT_TWO_EXP_LESS_dimword:
  !b  l n.
    b + l <= dimindex (:α) /\ n < 2 ** b ==>
    n * 2 ** l < dimword (:α)
Proof
  rw []
  \\ match_mp_tac LESS_LESS_EQ_TRANS
  \\ qexists_tac `2 ** (b + l)`
  \\ reverse conj_tac
  THEN1 fs [dimword_def]
  \\ rewrite_tac [EXP_ADD] \\ fs []
QED

Theorem maxout_bits_eq:
  b + l <= dimindex (:'a) /\ n' < 2 ** b - 1 ==>
  (maxout_bits n b l = (maxout_bits n' b l:'a word) <=> n = n')
Proof
  Cases_on `n = n'` \\ fs [] \\ strip_tac
  \\ `(n' * 2 ** l) < dimword (:α)` by
   (match_mp_tac MULT_TWO_EXP_LESS_dimword
    \\ asm_exists_tac \\ fs [])
  \\ fs [maxout_bits_def] \\ rw []
  \\ fs [WORD_MUL_LSL,word_mul_n2w,all_ones_n2w]
  THEN1
   (qsuff_tac `(n * 2 ** l) < dimword (:α)` \\ fs []
    \\ match_mp_tac MULT_TWO_EXP_LESS_dimword
    \\ asm_exists_tac \\ fs [])
  \\ qsuff_tac `((2 ** b - 1) * 2 ** l) < dimword (:α)` \\ fs []
  \\ match_mp_tac MULT_TWO_EXP_LESS_dimword
  \\ asm_exists_tac \\ fs []
QED

Theorem word_or_eq_word_or_split:
  w1 && w2 = 0w /\ v1 && v2 = 0w /\
  w1 && v2 = 0w /\ v1 && w2 = 0w ==>
  ((w1 ‖ w2 = v1 ‖ v2) ⇔  (w1 = v1 ∧ w2 = v2))
Proof
  fs [fcpTheory.CART_EQ,word_or_def,word_and_def,word_0,fcpTheory.FCP_BETA]
  \\ metis_tac []
QED

Theorem ptr_bits_eq_ptr_bits:
  tag < 2 ** c.tag_bits - 1 /\
  len < 2 ** c.len_bits - 1 /\
  c.len_bits + c.tag_bits < dimindex (:'a) ==>
  ((ptr_bits c tag2 len2 ‖ 1w =
    ptr_bits c tag len ‖ (1w:'a word)) <=>
   (tag2 = tag /\ len2 = len))
Proof
  rewrite_tac [ptr_bits_or_1_add_1]
  \\ simp [ptr_bits_def] \\ rw []
  \\ qmatch_goalsub_abbrev_tac `w1 || w2 = v1 || v2`
  \\ match_mp_tac EQ_TRANS
  \\ qexists_tac `w1 = v1 /\ w2 = v2`
  \\ conj_tac
  THEN1
   (match_mp_tac word_or_eq_word_or_split
    \\ unabbrev_all_tac
    \\ simp_tac std_ss [fcpTheory.CART_EQ,word_0,word_and_def,fcpTheory.FCP_BETA]
    \\ rw [] \\ CCONTR_TAC \\ fs []
    \\ imp_res_tac maxout_bits_bit \\ fs [])
  \\ qsuff_tac `(w1 = v1 <=> len2 = len) /\ (w2 = v2 <=> tag2 = tag)`
  THEN1 fs []
  \\ unabbrev_all_tac
  \\ fs [maxout_bits_eq]
QED

Theorem maxout_bits_0:
  maxout_bits 0 b e = 0w
Proof
  fs [maxout_bits_def] \\ rw []
  \\ Cases_on `b` \\ fs []
  \\ fs [all_ones_def,EXP]
  \\ Cases_on `2 ** n` \\ fs []
QED

Theorem ptr_bits_eq_ptr_bits_len_only:
  len < 2 ** c.len_bits - 1 /\
  c.len_bits < dimindex (:'a) ==>
  ((ptr_bits c 0 len2 ‖ 1w =
    ptr_bits c 0 len ‖ (1w:'a word)) <=>
   (len2 = len))
Proof
  rewrite_tac [ptr_bits_or_1_add_1]
  \\ simp [ptr_bits_def] \\ rw [maxout_bits_0]
  \\ fs [maxout_bits_eq]
QED

Theorem encode_header_IMP_WORD_NEQ_0[local]:
  encode_header c tag len = SOME h /\
  c.len_size < arch_width_bits c.arch_width ==>
  (n2w h:'a word) <> 0w
Proof
  strip_tac
  \\ drule encode_header_IMP_BIT0
  \\ impl_tac >- fs []
  \\ strip_tac \\ strip_tac
  \\ pop_assum SUBST_ALL_TAC \\ fs [word_index]
QED

Theorem assign_TagLenEq:
  (∃tag len. op = BlockOp (TagLenEq tag len)) ==> ^assign_thm_goal
Proof
  rpt strip_tac
  \\ imp_res_tac state_rel_arch_width
  \\ imp_res_tac state_rel_small_shift_length
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ gvs [do_app,AllCaseEqs(),allowed_op_def]
  \\ fs [assign_def,eq_eval,small_shift_length_def,wordSemTheory.get_store_def,GSYM dimword_def]
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ last_x_assum mp_tac
  \\ simp [Once state_rel_thm] \\ strip_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs [set_var_def]
  \\ strip_tac
  \\ fs [assign_def,list_Seq_def] \\ IF_CASES_TAC \\ fs [] \\ clean_tac
  THEN1 (* len = 0 case *)
   (reverse IF_CASES_TAC
    \\ fs [LENGTH_NIL,state_rel_thm]
    \\ imp_res_tac get_vars_1_imp \\ eval_tac
    \\ fs [wordSemTheory.get_var_imm_def]
    THEN1
     (fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
      \\ imp_res_tac memory_rel_tag_limit
      \\ rpt_drule0 (DECIDE ``n < m /\ ~(k < m:num) ==> n <> k``) \\ fs [option_le_max_right]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ match_mp_tac memory_rel_Boolv_F \\ fs [])
    \\ rpt_drule0 memory_rel_test_nil_eq \\ strip_tac \\ fs []
    \\ simp [asmTheory.word_cmp_def]
    \\ IF_CASES_TAC \\ fs []
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ TRY (match_mp_tac memory_rel_Boolv_F) \\ fs []
    \\ TRY (match_mp_tac memory_rel_Boolv_T) \\ fs [])
  \\ IF_CASES_TAC
  THEN1 (* tag < 2 ** tag_bits - 1 /\ len < 2 ** len_bits - 1 *)
   (`c.len_bits + c.tag_bits < dimindex (:'a)` by
         fs [memory_rel_def,heap_in_memory_store_def,shift_length_def]
    \\ rpt_drule0 memory_rel_Block_IMP \\ strip_tac \\ fs []
    \\ imp_res_tac get_vars_1_imp \\ eval_tac
    \\ fs [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def,
           asmTheory.word_cmp_def,state_rel_thm]
    \\ rename [`Boolv (tag2 = tag ∧ LENGTH len2 = len)`]
    \\ qmatch_goalsub_abbrev_tac `COND ggg`
    \\ qsuff_tac `(tag2 = tag ∧ LENGTH len2 = len) = ggg` THEN1
     (strip_tac \\ asm_rewrite_tac [] \\ ntac 2 (pop_assum kall_tac)
      \\ Cases_on `ggg` \\ fs []
      \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
      \\ fs [inter_insert_ODD_adjust_set]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ TRY (match_mp_tac memory_rel_Boolv_F) \\ fs []
      \\ TRY (match_mp_tac memory_rel_Boolv_T) \\ fs [])
    \\ Cases_on `len2 = []` \\ fs [] THEN1
     (fs [Abbr`ggg`] \\ fs [fcpTheory.CART_EQ,word_and_def,fcpTheory.FCP_BETA]
      \\ qexists_tac `0` \\ fs [] \\ rveq \\ fs []
      \\ first_x_assum (qspec_then `0` assume_tac) \\ fs [fcpTheory.FCP_BETA]
      \\ fs [word_or_def,fcpTheory.FCP_BETA,n2w_def])
    \\ fs [memory_rel_def,word_ml_inv_def,abs_ml_inv_def,bc_stack_ref_inv_def]
    \\ rveq \\ fs [v_inv_def] \\ rveq \\ fs [word_addr_def]
    \\ rveq \\ fs []
    \\ `LENGTH xs' = LENGTH len2` by (imp_res_tac LIST_REL_LENGTH \\ fs []) \\ fs []
    \\ simp [Abbr`ggg`]
    \\ fs [all_ones_get_addr,ptr_bits_eq_ptr_bits])
  \\ pop_assum kall_tac
  \\ CASE_TAC \\ fs [state_rel_thm] THEN1
   (eval_tac \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ rpt_drule0 memory_rel_test_none_eq \\ strip_tac \\ fs []
    \\ match_mp_tac memory_rel_Boolv_F \\ fs [])
  \\ fs [list_Seq_def] \\ eval_tac \\ fs [wordSemTheory.get_var_imm_def]
  \\ imp_res_tac get_vars_1_imp \\ eval_tac
  \\ fs [wordSemTheory.get_var_def,lookup_insert]
  \\ rpt_drule0 memory_rel_Block_IMP \\ strip_tac \\ fs []
  \\ simp [asmTheory.word_cmp_def]
  \\ fs [word_and_one_eq_0_iff |> SIMP_RULE (srw_ss()) []]
  \\ IF_CASES_TAC \\ fs [] THEN1
   (simp [asmTheory.word_cmp_def]
    \\ IF_CASES_TAC \\ fs []
    \\ `c.len_size < arch_width_bits c.arch_width` by
         (`arch_width_bits c.arch_width = dimindex (:'a)` by
            (qpat_x_assum `memory_rel c _ _ _ _ _ _ _ _`
               (fn th => ACCEPT_TAC (MATCH_MP memory_rel_arch_width th)))
          \\ `c.len_size + 9 < dimindex (:'a)` by
            (qpat_x_assum `memory_rel c _ _ _ _ _ _ _ _`
               (fn th => ACCEPT_TAC (CONJUNCT2 (MATCH_MP memory_rel_len_size th))))
          \\ DECIDE_TAC)
    \\ `(n2w x:'a word) <> 0w` by
         (qspecl_then [`4 * tag`,`len`,`x`,`c`] mp_tac
            (GEN_ALL encode_header_IMP_WORD_NEQ_0)
          \\ fs [])
    \\ fs [n2w_mod]
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
    \\ fs [inter_insert_ODD_adjust_set]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ match_mp_tac memory_rel_Boolv_F \\ fs [])
  \\ rename1 `get_vars [a8] s2.locals = SOME [Block t8 n8 l8]`
  \\ `word_exp (t with locals := insert 1 (Word 0w) t.locals)
        (real_addr c (adjust_var a8)) = SOME (Word a)` by
    (match_mp_tac (GEN_ALL get_real_addr_lemma)
     \\ fs [wordSemTheory.get_var_def,lookup_insert]) \\ fs []
  \\ simp [asmTheory.word_cmp_def]
  \\ `arch_width_bits c.arch_width = dimindex (:'a)` by
       (qpat_x_assum `memory_rel c _ _ _ _ _ _ _ _`
          (fn th => ACCEPT_TAC (MATCH_MP memory_rel_arch_width th)))
  \\ `c.len_size + 2 < arch_width_bits c.arch_width` by
       (`c.len_size + 9 < dimindex (:'a)` by
          (qpat_x_assum `memory_rel c _ _ _ _ _ _ _ _`
             (fn th => ACCEPT_TAC (CONJUNCT2 (MATCH_MP memory_rel_len_size th))))
        \\ DECIDE_TAC)
  \\ drule0 (GEN_ALL encode_header_word_eq)
  \\ qpat_x_assum `encode_header _ _ _ = _` (assume_tac o GSYM)
  \\ disch_then drule0 \\ fs [n2w_11]
  \\ strip_tac \\ fs [DECIDE ``2 * k = 2 * l <=> k = l:num``]
  \\ rw [lookup_insert,adjust_var_11] \\ fs []
  \\ rw [lookup_insert,adjust_var_11] \\ fs []
  \\ fs [inter_insert_ODD_adjust_set,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ (match_mp_tac memory_rel_Boolv_T ORELSE
      match_mp_tac memory_rel_Boolv_F) \\ fs []
QED

Theorem all_ones_and_1:
  k <> 0 ==> all_ones k 0 && 1w = 1w
Proof
  fs [fcpTheory.CART_EQ,word_and_def,n2w_def,fcpTheory.FCP_BETA,all_ones_bit]
QED

Theorem all_ones_and_ptr_bits_tag_0:
  all_ones (c.len_bits + 1) 0 && ptr_bits c tag len = ptr_bits c 0 len
Proof
  fs [ptr_bits_def,maxout_bits_0]
  \\ fs [fcpTheory.CART_EQ,word_and_def,n2w_def,fcpTheory.FCP_BETA,all_ones_bit,
         word_or_def] \\ rw [] \\ eq_tac \\ rw []
  \\ imp_res_tac maxout_bits_bit \\ fs []
QED

Theorem assign_LenEq:
  (∃len. op = BlockOp (LenEq len)) ==> ^assign_thm_goal
Proof
  rpt strip_tac
  \\ imp_res_tac state_rel_arch_width
  \\ imp_res_tac state_rel_small_shift_length
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ gvs [do_app,AllCaseEqs(),allowed_op_def]
  \\ fs [assign_def,eq_eval,wordSemTheory.get_store_def,GSYM dimword_def]
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ last_x_assum mp_tac
  \\ simp [Once state_rel_thm] \\ strip_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs [set_var_def]
  \\ strip_tac
  \\ fs [assign_def] \\ IF_CASES_TAC \\ fs [] \\ clean_tac
  THEN1 (* len = 0 case *)
   (imp_res_tac get_vars_1_imp \\ eval_tac
    \\ fs [wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,state_rel_thm]
    \\ rpt_drule0 memory_rel_Block_IMP \\ strip_tac \\ fs []
    \\ simp [asmTheory.word_cmp_def]
    \\ fs [word_index_0] \\ IF_CASES_TAC \\ fs []
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ TRY (match_mp_tac memory_rel_Boolv_F) \\ fs []
    \\ TRY (match_mp_tac memory_rel_Boolv_T) \\ fs [])
  \\ IF_CASES_TAC
  THEN1 (* len < 2 ** len_bits - 1 *)
   (`c.len_bits < dimindex (:'a)` by
         fs [memory_rel_def,heap_in_memory_store_def,shift_length_def]
    \\ rpt_drule0 memory_rel_Block_IMP \\ strip_tac \\ fs []
    \\ imp_res_tac get_vars_1_imp \\ eval_tac
    \\ fs [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def,
           asmTheory.word_cmp_def,state_rel_thm]
    \\ rename [`Boolv (LENGTH len2 = len)`]
    \\ qmatch_goalsub_abbrev_tac `COND ggg`
    \\ qsuff_tac `(LENGTH len2 = len) = ggg` THEN1
     (strip_tac \\ asm_rewrite_tac [] \\ ntac 2 (pop_assum kall_tac)
      \\ Cases_on `ggg` \\ fs []
      \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
      \\ fs [inter_insert_ODD_adjust_set]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ TRY (match_mp_tac memory_rel_Boolv_F) \\ fs []
      \\ TRY (match_mp_tac memory_rel_Boolv_T) \\ fs [])
    \\ Cases_on `len2 = []` \\ fs [] THEN1
     (fs [Abbr`ggg`] \\ fs [fcpTheory.CART_EQ,word_and_def,fcpTheory.FCP_BETA]
      \\ qexists_tac `0` \\ fs [] \\ rveq \\ fs []
      \\ first_x_assum (qspec_then `0` assume_tac) \\ fs [fcpTheory.FCP_BETA]
      \\ fs [word_or_def,fcpTheory.FCP_BETA,n2w_def])
    \\ fs [memory_rel_def,word_ml_inv_def,abs_ml_inv_def,bc_stack_ref_inv_def]
    \\ rveq \\ fs [v_inv_def] \\ rveq \\ fs [word_addr_def]
    \\ rveq \\ fs []
    \\ `LENGTH xs' = LENGTH len2` by (imp_res_tac LIST_REL_LENGTH \\ fs []) \\ fs []
    \\ simp [Abbr`ggg`]
    \\ qmatch_goalsub_abbrev_tac `_ && ww`
    \\ `all_ones (c.len_bits + 1) 0 =
        all_ones (c.len_bits + 1) 0 && all_ones (c.len_bits + (c.tag_bits + 1)) 0` by
           fs [fcpTheory.CART_EQ,word_and_def,fcpTheory.FCP_BETA,all_ones_bit]
    \\ pop_assum (fn th => once_rewrite_tac [th])
    \\ rewrite_tac [WORD_AND_ASSOC]
    \\ qunabbrev_tac `ww`
    \\ rewrite_tac [all_ones_get_addr,WORD_LEFT_AND_OVER_OR]
    \\ simp [all_ones_and_1,all_ones_and_ptr_bits_tag_0]
    \\ fs [ptr_bits_eq_ptr_bits_len_only])
  \\ pop_assum kall_tac
  \\ imp_res_tac get_vars_1_imp \\ eval_tac
  \\ rpt_drule0 memory_rel_Block_IMP \\ strip_tac \\ fs [word_index_0]
  \\ rename [`COND (payload = [])`]
  \\ reverse IF_CASES_TAC THEN1
   (`LENGTH payload < dimword (:'a)` by
      (FULL_CASE_TAC \\ fs []
       \\ match_mp_tac LESS_LESS_EQ_TRANS
       \\ asm_exists_tac \\ fs [] \\ fs [dimword_def])
    \\ `LENGTH payload <> len` by (CCONTR_TAC \\ fs [])
    \\ eval_tac \\ fs [wordSemTheory.get_var_imm_def]
    \\ fs [inter_insert_ODD_adjust_set,state_rel_thm]
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ match_mp_tac memory_rel_Boolv_F \\ fs [])
  \\ Cases_on `payload = []` \\ fs [] \\ rveq \\ fs []
  THEN1
   (fs [list_Seq_def] \\ eval_tac \\ fs [wordSemTheory.get_var_imm_def]
    \\ fs [wordSemTheory.get_var_def,lookup_insert,asmTheory.word_cmp_def,
           state_rel_thm]
    \\ fs [inter_insert_ODD_adjust_set]
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ match_mp_tac memory_rel_Boolv_F \\ fs [])
  \\ `dimindex (:'a) - c.len_size < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword \\ decide_tac)
  \\ ntac 2 (once_rewrite_tac [list_Seq_def]) \\ eval_tac
  \\ fs [wordSemTheory.get_var_def,lookup_insert,wordSemTheory.get_var_imm_def,
         asmTheory.word_cmp_def]
  \\ drule word_exp_real_addr
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ fs [] \\ disch_then drule \\ fs [] \\ disch_then kall_tac
  \\ fs [GSYM NOT_LESS,GREATER_EQ]
  \\ `c.len_size <> 0` by
      (fs [memory_rel_def,heap_in_memory_store_def] \\ NO_TAC)
  \\ fs [NOT_LESS]
  \\ fs [decode_length_def]
  \\ fs [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.get_var_def,lookup_insert,wordSemTheory.get_var_imm_def,
         asmTheory.word_cmp_def]
  \\ `LENGTH payload < dimword (:'a)` by
   (match_mp_tac LESS_LESS_EQ_TRANS
    \\ asm_exists_tac \\ fs [] \\ fs [dimword_def])
  \\ fs [] \\ IF_CASES_TAC \\ fs []
  \\ fs [inter_insert_ODD_adjust_set,state_rel_thm]
  \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ TRY (match_mp_tac memory_rel_Boolv_T) \\ fs []
  \\ TRY (match_mp_tac memory_rel_Boolv_F) \\ fs []
QED

Theorem assign_LengthBlock:
  op = BlockOp LengthBlock ==> ^assign_thm_goal
Proof
  rpt strip_tac
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
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs [set_var_def]
  \\ strip_tac
  \\ drule0 memory_rel_Block_IMP \\ fs [] \\ rw []
  \\ fs [assign_def]
  \\ fs [wordSemTheory.get_vars_def]
  \\ gvs [AllCaseEqs()]
  \\ `2 < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword \\
        fs [good_dimindex_def] \\ decide_tac)
  \\ `dimindex (:'a) - c.len_size < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword \\ decide_tac)
  \\ eval_tac
  \\ fs [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def]
  \\ fs [asmTheory.word_cmp_def,word_and_one_eq_0_iff
           |> SIMP_RULE (srw_ss()) []]
  \\ reverse (Cases_on `w ' 0`) \\ fs [] THEN1
   (fs [state_rel_thm,lookup_insert,adjust_var_11] \\ rw [] \\ fs []
    >- fs [option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ match_mp_tac (IMP_memory_rel_Number |> Q.INST [`i`|->`0`]
          |> SIMP_RULE std_ss [EVAL ``Smallnum 0``])
    \\ fs [] \\ fs [good_dimindex_def,dimword_def]
    \\ EVAL_TAC \\ rw [good_dimindex_def,dimword_def])
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ rename [`real_addr c (adjust_var hh)`]
  \\ `word_exp t (real_addr c (adjust_var hh)) = SOME (Word a)` by
       (match_mp_tac (GEN_ALL get_real_addr_lemma)
        \\ gvs [wordSemTheory.get_var_def, AllCaseEqs()])
  \\ fs []
  \\ fs [GSYM NOT_LESS,GREATER_EQ]
  \\ `c.len_size <> 0` by
      (fs [memory_rel_def,heap_in_memory_store_def] \\ NO_TAC)
  \\ fs [NOT_LESS]
  \\ `~(dimindex (:α) <= 2)` by
         (fs [good_dimindex_def] \\ NO_TAC)
  \\ fs [state_rel_thm] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
  >- fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ fs [decode_length_def]
  \\ match_mp_tac IMP_memory_rel_Number_num \\ fs []
QED

Theorem assign_BoundsCheckBlock:
   assign c secn l dest (BlockOp BoundsCheckBlock) args names =
      case args of
      | [v1;v2] => (list_Seq [If Test (adjust_var v1) (Imm 1)
                               (Assign 1 (Const 0))
                               (Assign 1
                                 (let addr = real_addr c (adjust_var v1) in
                                  let header = Load addr in
                                  let k = arch_width_bits c.arch_width - c.len_size in
                                    ShiftN Lsr header k));
                              Assign 3 (ShiftVar (arch_width_bits c.arch_width) Ror (adjust_var v2) 1);
                              If Lower 3 (Reg 1)
                               (Assign (adjust_var dest) TRUE_CONST)
                               (Assign (adjust_var dest) FALSE_CONST)],l)
      | _ => (Skip:wordLang$prog,l)
Proof
  fs [assign_def] \\ every_case_tac \\ fs []
QED

Theorem assign_BoundsCheckBlock[allow_rebind]:
   op = BlockOp BoundsCheckBlock ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app,allowed_op_def] \\ rfs [] \\ every_case_tac \\ fs []
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [get_var_def]
  \\ `shift_length c - shift (dimindex (:'a)) < dimword (:'a) /\
      dimindex (:'a) - c.len_size < dimword (:'a) /\
      2 < dimword (:'a)` by
    (fs [dimindex_lt_dimword, state_rel_thm,memory_rel_def,heap_in_memory_store_def])
  \\ simp [state_rel_thm] \\ eval_tac
  \\ fs [state_rel_thm,option_le_max_right] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ drule0 memory_rel_Block_IMP \\ fs [] \\ rw []
  \\ fs [assign_BoundsCheckBlock]
  \\ fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF]
  \\ qmatch_asmsub_rename_tac `(Number i,w2)`
  \\ `?wi. w2 = Word wi` by
    (drule0 memory_rel_tl \\ strip_tac
     \\ imp_res_tac memory_rel_any_Number_IMP \\ simp [] \\ NO_TAC)
  \\ rveq
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [eq_eval]
  \\ reverse (Cases_on `w ' 0`) \\ fs [word_index_0] THEN1
   (fs [lookup_insert,adjust_var_11]
    \\ rw [] \\ fs []
    \\ fs [eq_eval,list_Seq_def]
    \\ simp [Once word_exp_ShiftVar_bits]
    \\ fs [eq_eval,WORD_LO_word_0,adjust_var_11]
    \\ rw []
    \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def,option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ fs [intLib.COOPER_PROVE ``~(0<=i /\ i<0:int)``]
    \\ match_mp_tac memory_rel_Boolv_F \\ fs [])
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ `word_exp t (real_addr c (adjust_var a1)) = SOME (Word a)` by
       (match_mp_tac (GEN_ALL get_real_addr_lemma)
        \\ fs [wordSemTheory.get_var_def] \\ NO_TAC) \\ fs []
  \\ fs [eq_eval,word_sh_def]
  \\ fs [list_Seq_def,eq_eval]
  \\ simp [Once word_exp_ShiftVar_bits]
  \\ `c.len_size < dimindex (:α) /\
      ~(dimindex (:α) ≥ c.len_size + dimindex (:α))` by
         (fs [memory_rel_def,heap_in_memory_store_def] \\ NO_TAC)
  \\ fs [eq_eval,WORD_LO_word_0,adjust_var_11]
  \\ fs [decode_length_def]
  \\ drule0 memory_rel_tl \\ strip_tac
  \\ drule0 (GEN_ALL memory_rel_bounds_check)
  \\ disch_then (qspec_then `LENGTH l'` mp_tac)
  \\ impl_tac THEN1
    (fs [small_int_def,dimword_def,good_dimindex_def] \\ rfs [])
  \\ strip_tac \\ fs []
  \\ qpat_abbrev_tac `bool_res <=> 0 ≤ i ∧ i < &LENGTH _`
  \\ Cases_on `bool_res`
  \\ fs [] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
  \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
  \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [])
QED

Theorem assign_BoolNot[allow_rebind]:
  op = BlockOp BoolNot ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app]
  \\ gvs[AllCaseEqs()]
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_1] \\ clean_tac
  \\ fs [get_var_def]
  \\ fs [state_rel_thm] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ gvs [oneline dest_Boolv_def,AllCaseEqs()]
  \\ drule memory_rel_Block_IMP \\ simp [backend_commonTheory.bool_to_tag_def]
  \\ drule memory_rel_tl \\ strip_tac
  \\ simp [allowed_op_def]
  \\ rpt strip_tac \\ gvs []
  \\ fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF]
  \\ simp [assign_def,wordSemTheory.evaluate_def,
           wordSemTheory.get_var_imm_def,
           asmTheory.word_cmp_def,
           wordSemTheory.word_exp_def, wordSemTheory.the_words_def,
           word_op_def, wordSemTheory.set_var_def, lookup_insert]
  \\ fs [] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
  \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ ‘tag = 0 ∨ tag = 1’ by decide_tac \\ gvs []
  \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
  \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [])
QED

Theorem assign_BoolTest[allow_rebind]:
  (∃test. op = BlockOp (BoolTest test)) ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app]
  \\ gvs[AllCaseEqs()]
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [get_var_def]
  \\ fs [state_rel_thm] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ gvs [oneline dest_Boolv_def,AllCaseEqs()]
  \\ drule memory_rel_Block_IMP \\ simp [backend_commonTheory.bool_to_tag_def]
  \\ drule memory_rel_tl \\ strip_tac
  \\ drule memory_rel_Block_IMP \\ simp [backend_commonTheory.bool_to_tag_def]
  \\ drule memory_rel_tl \\ strip_tac
  \\ simp [allowed_op_def]
  \\ rpt strip_tac \\ gvs []
  \\ fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF]
  \\ simp [assign_def,wordSemTheory.evaluate_def,
           wordSemTheory.get_var_imm_def,
           asmTheory.word_cmp_def]
  \\ ‘(n2w (2 * tag) = n2w (2 * tag') :α word) ⇔  (tag = 1 ⇔ tag' = 1)’ by
    (‘tag = 0 ∨ tag = 1’ by decide_tac
     \\ ‘tag' = 0 ∨ tag' = 1’ by decide_tac
     \\ gvs [dimword_def,good_dimindex_def])
  \\ simp []
  \\ IF_CASES_TAC \\ gvs [wordSemTheory.word_exp_def,wordSemTheory.set_var_def]
  \\ fs [] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
  \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
  \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [])
QED

Theorem assign_PtrEqual:
  op = BlockOp PtrEqual ==> ^assign_thm_link_goal
Proof
  rpt strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app]
  \\ gvs [AllCaseEqs()]
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [get_var_def]
  \\ fs [state_rel_thm] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL) \\ strip_tac
  \\ rpt_drule0 memory_rel_simple_eq \\ strip_tac \\ rveq
  \\ fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF]
  \\ simp [assign_def, arg2_def, assign_PtrEq_def]
  \\ fs [ptr_eq_link_def]
  \\ simp [wordSemTheory.evaluate_def]
  \\ drule_all word_ptr_eq_thm \\ strip_tac \\ simp []
  \\ IF_CASES_TAC
  \\ gvs [wordSemTheory.set_var_def, allowed_op_def]
  >- (
    fs [lookup_insert, adjust_var_11] \\ rw [] \\ fs []
    \\ simp [inter_insert_ODD_adjust_set, GSYM Boolv_def, option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ match_mp_tac memory_rel_Boolv_T \\ fs [])
  \\ fs [lookup_insert, adjust_var_11] \\ rw [] \\ fs []
  \\ simp [inter_insert_ODD_adjust_set, GSYM Boolv_def, option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ match_mp_tac memory_rel_Boolv_F \\ fs []
QED

val _ = augment_srw_ss [rewrites [compiler_Smallnum_i2w]];

Theorem MemEqList_thm[local]:
  !offset c t xs dm m b a.
      word_mem_eq (a + i2w offset) (MAP i2w xs) dm m = SOME b /\
      arch_width_bits c.arch_width = dimindex(:'a) /\
      get_var 3 (t:('a,'c,'ffi) wordSem$state) = SOME (Word a) /\ dm = t.mdomain /\ m = t.memory ==>
      ?x. evaluate (MemEqList c offset xs,t) =
            (NONE,t with locals := ((if b then insert 1 (Word 2w) else I) o
                                    (if xs <> [] then insert 5 x else I)) t.locals)
Proof
  Induct_on `xs`
  THEN1 (fs [MemEqList_def,eq_eval,word_mem_eq_def])
  \\ fs [word_mem_eq_def]
  \\ rpt strip_tac
  \\ Cases_on `t.memory (a + i2w offset)` \\ fs [isWord_def]
  \\ fs [MemEqList_def,eq_eval,word_mem_eq_def]
  \\ reverse IF_CASES_TAC
  THEN1 (fs [] \\ metis_tac [])
  \\ fs [] \\ rveq
  \\ full_simp_tac std_ss [GSYM WORD_ADD_ASSOC]
  \\ qmatch_goalsub_abbrev_tac `(MemEqList _ _ _, t6)`
  \\ first_x_assum (qspecl_then [`offset+ &(arch_bytes c.arch_width)`,`c`,`t6`,`b`,`a`] mp_tac)
  \\ fs [Abbr`t6`,eq_eval]
  \\ `i2w (offset + &arch_bytes c.arch_width) = (i2w offset + bytes_in_word:'a word)` by
    (asm_rewrite_tac [GSYM integer_wordTheory.word_i2w_add,integer_wordTheory.i2w_pos] \\ simp [])
  \\ gvs []
  \\ strip_tac \\ fs []
  \\ Cases_on `b`
  \\ fs [wordSemTheory.state_component_equality]
  \\ rw [] \\ fs [insert_shadow]
  \\ metis_tac []
QED

Theorem MemEqList_thm = MemEqList_thm
  |> Q.SPEC `0` |> SIMP_RULE std_ss [integer_wordTheory.i2w_0,WORD_ADD_0];

Theorem n2mw_same_width[local]:
!n. dimindex(:'a) = dimindex(:'b) ==>
 MAP (w2w:'b word -> 'a word) (n2mw n) = n2mw n
Proof
completeInduct_on `n` >> rw[] >>
 once_rewrite_tac[multiwordTheory.n2mw_def] >>
 rw[] >> gvs[dimword_def,w2w_n2w,bitTheory.BITS_ZERO3] >>
 first_x_assum irule >> simp[DIV_LESS,ONE_LT_dimword,GSYM dimword_def]
QED

Theorem w2i_w2w_same_width[local]:
dimindex(:'a) = dimindex(:'b) ==> w2i(w2w(w:'b word):'a word) = w2i w
Proof
 rw[] >> Cases_on `w` >>
 fs [integer_wordTheory.w2i_def,w2w_n2w,word_msb_n2w,dimword_def] >>
 FULL_SIMP_TAC std_ss [GSYM WORD_NEG_MUL,word_2comp_n2w,w2n_n2w,dimword_def]
QED

Theorem n2mw_w2i_same_width[local]:
dimindex(:'a)=dimindex(:'b) ==> MAP(w2i:'a word->int)(n2mw n) = MAP(w2i:'b word->int)(n2mw n)
Proof
 rw[] >> Q.ISPECL_THEN [`n`] mp_tac n2mw_same_width >> simp[] >>
 disch_then(mp_tac o AP_TERM ``MAP(w2i:'a word->int)``) >>
 simp[MAP_MAP_o,o_DEF,w2i_w2w_same_width,SF ETA_ss]
QED

Theorem compiler_i2mw_words[local]:

 arch_width_bits c.arch_width = dimindex(:'a) ==>
 (if c.arch_width = Arch32 then
   (let (sign,ws) = (i2mw i:bool # word32 list) in (sign,MAP w2i ws))
  else (let (sign,ws) = (i2mw i:bool # word64 list) in (sign,MAP w2i ws))) =
 (FST(i2mw i:bool # 'a word list), MAP w2i (SND(i2mw i:bool # 'a word list)))
Proof
 Cases_on `c.arch_width` >>
 fs [asmTheory.arch_width_bits_def,multiwordTheory.i2mw_def] >> rw[] >>
 fs [INST_TYPE [beta |-> ``:32``] n2mw_w2i_same_width,
     INST_TYPE [beta |-> ``:64``] n2mw_w2i_same_width]
QED

Theorem compiler_i2mw_words_thm[local]:

 (i2mw i:bool # 'a word list) = (sign,ws) /\
 arch_width_bits c.arch_width = dimindex(:'a) ==>
 (if c.arch_width = Arch32 then
   (let (sign,ws) = (i2mw i:bool # word32 list) in (sign,MAP w2i ws))
  else (let (sign,ws) = (i2mw i:bool # word64 list) in (sign,MAP w2i ws))) =
 (sign,MAP w2i ws)
Proof
 strip_tac >> mp_tac compiler_i2mw_words >> simp[]
QED

Theorem assign_EqualConst:
  (∃p. op = BlockOp (EqualConst p)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ imp_res_tac state_rel_arch_width \\ rveq \\ fs []
  \\ rpt_drule0 state_rel_cut_IMP \\ strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app,allowed_op_def] \\ rfs [] \\ every_case_tac \\ fs []
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_1] \\ clean_tac
  \\ fs [get_var_def]
  \\ fs [Boolv_def] \\ rveq \\ fs [GSYM Boolv_def,option_le_max_right]
  \\ qpat_assum `state_rel c l1 l2 x t NONE locs`
           (assume_tac o REWRITE_RULE [state_rel_thm])
  \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  THEN1
   (rename [‘Int i’]
    \\ qmatch_asmsub_rename_tac `(Number j,a7)`
    \\ `?w. a7 = Word w` by
      (imp_res_tac memory_rel_any_Number_IMP \\ fs [] \\ NO_TAC)
    \\ rveq
    \\ rpt_drule0 memory_rel_Number_const_test
    \\ disch_then (qspec_then `i` mp_tac)
    \\ fs [assign_def,part_to_words_def]
    \\ IF_CASES_TAC THEN1
     (fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF] \\ fs [eq_eval]
      \\ Cases_on `i = j` \\ fs [] \\ rveq \\ fs []
      \\ fs [lookup_insert,state_rel_thm] \\ rpt strip_tac
      \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [lookup_insert,option_le_max_right]
      \\ rfs[]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ TRY (fs [lookup_insert,adjust_var_def] \\ NO_TAC)
      \\ TRY (IF_CASES_TAC \\ fs [] \\ NO_TAC)
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
      \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs []))
    \\ fs [] \\ TOP_CASE_TAC \\ fs []
    \\ fs [bignum_words_def] \\ Cases_on `(i2mw i:bool # 'a word list)`
    \\ drule_all (GEN_ALL compiler_i2mw_words_thm) \\ strip_tac
    \\ gvs [eq_eval,CaseEq"option"]
    THEN1
     (fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF] \\ fs [eq_eval]
      \\ fs [lookup_insert,state_rel_thm] \\ rpt strip_tac
      \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [lookup_insert,option_le_max_right]
      \\ rfs[]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ TRY (fs [lookup_insert,adjust_var_def] \\ NO_TAC)
      \\ TRY (IF_CASES_TAC \\ fs [] \\ NO_TAC)
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
      \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs []))
    \\ fs [word_bit_test,make_ptr_def]
    \\ IF_CASES_TAC
    THEN1
     (fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF] \\ fs [eq_eval]
      \\ fs [lookup_insert,state_rel_thm] \\ rpt strip_tac
      \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [lookup_insert,option_le_max_right]
      \\ rfs[]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ TRY (fs [lookup_insert,adjust_var_def] \\ NO_TAC)
      \\ TRY (IF_CASES_TAC \\ fs [] \\ NO_TAC)
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
      \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs []))
    \\ strip_tac
    \\ simp [MAP_MAP_o,o_DEF]
    \\ fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF]
    \\ fs [list_Seq_def,eq_eval]
    \\ rename1 `get_real_addr c t.store w = SOME a`
    \\ qmatch_goalsub_abbrev_tac `word_exp t6`
    \\ `get_real_addr c t6.store w = SOME a` by fs [Abbr`t6`]
    \\ drule0 (get_real_addr_lemma |> REWRITE_RULE [CONJ_ASSOC]
                                   |> ONCE_REWRITE_RULE [CONJ_COMM] |> GEN_ALL)
    \\ disch_then (qspec_then `(adjust_var a1)` mp_tac)
    \\ impl_tac THEN1 fs [Abbr `t6`,eq_eval]
    \\ strip_tac \\ fs []
    \\ qmatch_goalsub_abbrev_tac `(MemEqList c 0 wss,t9)`
    \\ `word_mem_eq a (MAP i2w wss) t9.mdomain t9.memory = SOME (j = i)` by fs [Abbr`t9`,Abbr`wss`,MAP_MAP_o,o_DEF]
    \\ rpt_drule0 MemEqList_thm \\ TRY (disch_then (qspec_then `c` mp_tac))
    \\ impl_tac THEN1 fs [eq_eval,Abbr `t9`]
    \\ strip_tac \\ fs []
    \\ `wss <> []` by (gvs [Abbr‘wss’])
    \\ fs []
    \\ IF_CASES_TAC \\ fs [] \\ rveq
    \\ unabbrev_all_tac
    \\ fs [lookup_insert,state_rel_thm] \\ rpt strip_tac
    \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def]
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [lookup_insert,option_le_max_right]
    \\ rfs[]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ TRY (fs [lookup_insert,adjust_var_def] \\ NO_TAC)
      \\ TRY (IF_CASES_TAC \\ fs [] \\ NO_TAC)
      \\ match_mp_tac memory_rel_insert \\ fs []
    \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
    \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs []))
  THEN1
   (rename [‘Str ss’]
    \\ qmatch_asmsub_rename_tac `(RefPtr _ pp,a7)`
    \\ rpt_drule0 memory_rel_String_const_test
    \\ disch_then (qspec_then `ss` mp_tac) \\ strip_tac \\ clean_tac
    \\ ‘l' = MAP (n2w ∘ ORD) (explode ss) ⇔ ss = implode (MAP (CHR ∘ w2n) l')’
         by (eq_tac \\ rw [] \\ fs [MAP_MAP_o,o_DEF,ORD_BOUND,CHR_ORD])
    \\ asm_rewrite_tac [] \\ pop_assum kall_tac
    \\ fs [assign_def]
    \\ CASE_TAC
    THEN1
     (fs [eq_eval]
      \\ fs [lookup_insert,state_rel_thm] \\ rpt strip_tac
      \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [lookup_insert,option_le_max_right]
      \\ rfs[]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ TRY (fs [lookup_insert,adjust_var_def] \\ NO_TAC)
      \\ TRY (IF_CASES_TAC \\ fs [] \\ NO_TAC)
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
      \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs []))
    \\ CASE_TAC \\ gvs [] \\ PairCases_on ‘q’ \\ fs []
    \\ ‘q0’ by fs [part_to_words_def,AllCaseEqs()]
    \\ gvs []
    \\ fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF]
    \\ fs [list_Seq_def,eq_eval]
    \\ rename1 `get_real_addr c t.store w = SOME a`
    \\ qmatch_goalsub_abbrev_tac `word_exp t6`
    \\ `get_real_addr c t6.store w = SOME a` by fs [Abbr`t6`]
    \\ drule0 (get_real_addr_lemma |> REWRITE_RULE [CONJ_ASSOC]
                                   |> ONCE_REWRITE_RULE [CONJ_COMM] |> GEN_ALL)
    \\ disch_then (qspec_then `(adjust_var a1)` mp_tac)
    \\ impl_tac THEN1 fs [Abbr `t6`,eq_eval]
    \\ strip_tac \\ fs []
    \\ qmatch_goalsub_abbrev_tac `(MemEqList c 0 wss,t9)`
    \\ `word_mem_eq a (MAP i2w wss) t9.mdomain t9.memory =
       SOME (ss = implode (MAP (CHR ∘ w2n) l'))` by fs [Abbr`t9`,Abbr`wss`,MAP_MAP_o,o_DEF]
    \\ rpt_drule0 MemEqList_thm \\ TRY (disch_then (qspec_then `c` mp_tac))
    \\ impl_tac THEN1 fs [eq_eval,Abbr `t9`]
    \\ strip_tac \\ fs []
    \\ `wss <> []` by (gvs [Abbr‘wss’,part_to_words_def,AllCaseEqs()])
    \\ fs []
    \\ IF_CASES_TAC \\ fs [] \\ rveq
    \\ unabbrev_all_tac
    \\ fs [lookup_insert,state_rel_thm] \\ rpt strip_tac
    \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def]
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [lookup_insert,option_le_max_right]
    \\ rfs[]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ TRY (fs [lookup_insert,adjust_var_def] \\ NO_TAC)
      \\ TRY (IF_CASES_TAC \\ fs [] \\ NO_TAC)
      \\ match_mp_tac memory_rel_insert \\ fs []
    \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
    \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs []))
  THEN1
   (rename [‘W64 w64’]
    \\ qmatch_asmsub_rename_tac `(Word64 other64,a7)`
    \\ rpt_drule0 memory_rel_Word64_const_test
    \\ disch_then (qspec_then `w64` mp_tac) \\ strip_tac \\ clean_tac
    \\ fs [assign_def,part_to_words_def]
    \\ IF_CASES_TAC THEN
     (gvs [good_dimindex_def] \\ fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF]
      \\ fs [list_Seq_def,eq_eval]
      \\ rename1 `get_real_addr c t.store w = SOME a`
      \\ qmatch_goalsub_abbrev_tac `word_exp t6`
      \\ `get_real_addr c t6.store w = SOME a` by fs [Abbr`t6`]
      \\ drule0 (get_real_addr_lemma |> REWRITE_RULE [CONJ_ASSOC]
                                     |> ONCE_REWRITE_RULE [CONJ_COMM] |> GEN_ALL)
      \\ disch_then (qspec_then `(adjust_var a1)` mp_tac)
      \\ impl_tac THEN1 gvs [good_dimindex_def,Abbr `t6`,eq_eval]
      \\ strip_tac \\ fs []
      \\ qmatch_goalsub_abbrev_tac `(MemEqList c 0 wss,t9)`
      \\ `word_mem_eq (a+bytes_in_word) (MAP i2w wss) t9.mdomain t9.memory =
         SOME (other64 = w64)` by
           (Cases_on `w64`
            \\ fs [Abbr`t9`,Abbr`wss`,MAP_MAP_o,o_DEF,word_extract_n2w,
                   w2w_n2w,bitTheory.BITS_THM,dimword_def]
            \\ TRY (`n DIV 4294967296 < 4294967296` by fs[DIV_LT_X] \\ fs[]))
      \\ rpt_drule0 MemEqList_thm \\ TRY (disch_then (qspec_then `c` mp_tac))
      \\ impl_tac THEN1 fs [eq_eval,Abbr `t9`]
      \\ strip_tac \\ fs []
      \\ `wss <> []` by (gvs [Abbr‘wss’])
      \\ fs []
      \\ IF_CASES_TAC \\ fs [] \\ rveq
      \\ unabbrev_all_tac
      \\ fs [lookup_insert,state_rel_thm] \\ rpt strip_tac
      \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def]
      \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [lookup_insert,option_le_max_right]
      \\ rfs[]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ TRY (fs [lookup_insert,adjust_var_def] \\ NO_TAC)
      \\ TRY (IF_CASES_TAC \\ fs [] \\ NO_TAC)
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
      \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [])))
QED

(* TODO: move to backendProps *)

Theorem option_map_mult_suc:
  OPTION_MAP ($* (SUC n)) m =
  OPTION_MAP2 $+ m (OPTION_MAP ($* n) m)
Proof
  Cases_on `m` >> rw[MULT_SUC]
QED

Theorem eq_code_stack_max_sub1:
  l <> 0 ==>
  eq_code_stack_max l tsz =
  OPTION_MAP2 ($+)
    (OPTION_MAP2 MAX
      (lookup Equal_location tsz)
      (OPTION_MAP2 MAX
        (lookup Equal1_location tsz)
        (lookup Compare1_location tsz)))
    (eq_code_stack_max (l-1) tsz)
Proof
  Cases_on `l` >> rw[eq_code_stack_max_def,option_map_mult_suc]
QED

Theorem eq_code_stack_max_le_mono:
  a <= b ==>
  option_le (eq_code_stack_max a tsz) (eq_code_stack_max b tsz)
Proof
  rw[eq_code_stack_max_def] >> rw[OPTION_MAP2_DEF,IS_SOME_EXISTS]
QED

Definition sane_locals_size_def:
  sane_locals_size t = (t.locals_size = lookup Equal_location t.stack_size \/
                        t.locals_size = lookup Equal1_location t.stack_size)
End

Theorem Equal_code_lemma:
   (!c st dm m l wck v1 v2 t l1 l2 res l' wck'.
      word_eq c st dm m l wck v1 v2 = SOME (res,l',wck') /\
      dm = (t:('a,'c,'ffi) wordSem$state).mdomain /\
      m = t.memory /\
      st = t.store /\
      l <= t.clock /\
      c.len_size + 9 < dimindex (:'a) /\
      arch_width_bits c.arch_width = dimindex (:'a) /\
      shift_length c < dimindex (:'a) /\
      (?md. lookup Equal_location t.code = SOME (3,Equal_code c,md)) /\
      (?md. lookup Equal1_location t.code = SOME (4,Equal1_code c,md)) /\
      (?md. lookup Compare1_location t.code = SOME (4,Compare1_code c,md)) /\
      get_var 0 t = SOME (Loc l1 l2) /\
      get_var 2 t = SOME (Word (v1:'a word)) /\
      get_var 4 t = SOME (Word (v2:'a word)) /\
      c.len_size <> 0 /\
      c.len_size < dimindex (:α) /\
      sane_locals_size t /\
      good_dimindex (:'a) ==>
      ?ck new_p smx.
        evaluate (Equal_code c,t) =
         (SOME (Result (Loc l1 l2) [Word res]),
          t with <| clock := ck; locals := LN; locals_size := SOME 0; permute := new_p;
                    stack_max := smx |>) /\
        option_le smx (OPTION_MAP2 MAX t.stack_max
                                   (OPTION_MAP2 $+
                                     (stack_size t.stack)
                                     (eq_code_stack_max (wck+1) t.stack_size))) /\
        l' <= ck) /\
    (!c st dm m l wck w a1 a2 t l1 l2 res l' wck'.
      word_eq_list c st dm m l wck w a1 a2 = SOME (res,l',wck') /\
      dm = (t:('a,'c,'ffi) wordSem$state).mdomain /\
      m = t.memory /\
      st = t.store /\
      l <= t.clock /\
      c.len_size + 9 < dimindex (:'a) /\
      arch_width_bits c.arch_width = dimindex (:'a) /\
      shift_length c < dimindex (:'a) /\
      (?md. lookup Equal_location t.code = SOME (3,Equal_code c,md)) /\
      (?md. lookup Equal1_location t.code = SOME (4,Equal1_code c,md)) /\
      (?md. lookup Compare1_location t.code = SOME (4,Compare1_code c,md)) /\
      get_var 0 t = SOME (Loc l1 l2) /\
      get_var 2 t = SOME (Word (w:'a word)) /\
      get_var 4 t = SOME (Word (a1:'a word)) /\
      get_var 6 t = SOME (Word (a2:'a word)) /\
      sane_locals_size t /\
      c.len_size <> 0 /\
      c.len_size < dimindex (:α) /\
      good_dimindex (:'a) ==>
      ?ck new_p smx.
        evaluate (Equal1_code c,t) =
          (SOME (Result (Loc l1 l2) [Word res]),
           t with <| clock := ck; locals := LN; locals_size := SOME 0; permute := new_p;
                     stack_max := smx|>) /\
        option_le smx (OPTION_MAP2 MAX t.stack_max
                                   (OPTION_MAP2 $+
                                     (stack_size t.stack)
                                     (eq_code_stack_max (wck +1) t.stack_size))) /\
        l' <= ck)
Proof
  ho_match_mp_tac word_eq_ind \\ reverse (rpt strip_tac) \\ rveq
  \\ qpat_x_assum `_ = SOME (res,_)` mp_tac
  \\ once_rewrite_tac [word_eq_def]
  THEN1
   (IF_CASES_TAC THEN1
     (fs [Equal1_code_def] \\ strip_tac \\ rveq
      \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval,list_Seq_def]
      \\ fs [wordSemTheory.state_component_equality,wordSemTheory.flush_state_def]
      \\ fs[option_le_max_right])
    \\ IF_CASES_TAC \\ fs []
    \\ TOP_CASE_TAC \\ fs []
    \\ TOP_CASE_TAC \\ fs []
    \\ TOP_CASE_TAC \\ fs []
    \\ PairCases_on `x` \\ fs []
    \\ strip_tac
    \\ simp [Equal1_code_def]
    \\ ntac 4 (once_rewrite_tac [list_Seq_def])
    \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval]
    \\ TOP_CASE_TAC
    THEN1 (pop_assum mp_tac
           \\ simp [wordSemTheory.cut_env_def,domain_lookup,
               wordSemTheory.cut_envs_def,AllCaseEqs(),
               wordSemTheory.cut_names_def])
    \\ qmatch_goalsub_abbrev_tac `(Equal_code c, t1)`
    \\ first_x_assum (qspecl_then [`t1`,`Equal1_location`,`2`] mp_tac)
    \\ impl_tac THEN1
     (unabbrev_all_tac
      \\ fs [lookup_insert,wordSemTheory.push_env_def,wordSemTheory.flush_state_def]
      \\ pairarg_tac \\ fs [] \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval,sane_locals_size_def])
    \\ strip_tac \\ fs []
    \\ Cases_on `pop_env (t1 with <|locals := LN; locals_size := SOME 0;
                                    stack_max := smx; permute := new_p;
                                    clock := ck|>)` \\ fs []
    THEN1
     (pop_assum mp_tac \\ unabbrev_all_tac
      \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval,
             wordSemTheory.push_env_def,
             wordSemTheory.pop_env_def]
      \\ pairarg_tac \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval])
    \\ rename1 `pop_env _ = SOME t2`
    \\ `t2.locals =
          (insert 0 (Loc l1 l2) o
           insert 2 (Word w) o
           insert 4 (Word a1) o
           insert 6 (Word a2)) LN` by
     (rveq \\ fs []
      \\ unabbrev_all_tac
      \\ fs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def]
      \\ pairarg_tac \\ fs [] \\ rveq \\ fs []
      \\ imp_res_tac env_to_list_lookup_equiv
      \\ match_mp_tac IMP_spt_eq
      \\ fs [wf_fromAList,wf_insert,EVAL ``wf LN``]
      \\ fs [lookup_fromAList,lookup_insert,wordSemTheory.cut_env_def]
      \\ qpat_x_assum ‘cut_envs _ _ = _’ mp_tac
      \\ simp [wordSemTheory.cut_envs_def,
               wordSemTheory.cut_names_def,
               AllCaseEqs()] \\ strip_tac
      \\ rw []
      \\ fs [lookup_fromAList,lookup_insert,wordSemTheory.cut_env_def,
             ALOOKUP_toAList,lookup_inter_alt,lookup_insert,lookup_union]
      \\ rw []
      \\ rpt (irule wf_union \\ simp [wf_fromAList])
      \\ fs [lookup_fromAList,lookup_insert,wordSemTheory.cut_env_def,
             ALOOKUP_toAList,lookup_inter_alt,lookup_insert,lookup_union]
      \\ Cases_on ‘n = 0 ∨ n = 2 ∨ n = 4 ∨ n = 6’ \\ gvs [lookup_def])
    \\ `t.clock <> 0` by(CCONTR_TAC >> fs[] >> rfs[good_dimindex_def,dimword_def])
    \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval]
    \\ reverse IF_CASES_TAC THEN1
     (sg `F` \\ fs []
      \\ pop_assum mp_tac \\ fs [] \\ fs [EXTENSION] \\ rw []
      \\ qpat_x_assum ‘cut_envs _ _ = _’ mp_tac
      \\ simp [wordSemTheory.cut_envs_def,
               wordSemTheory.cut_names_def,
               AllCaseEqs()] \\ strip_tac
      \\ rw [] \\ simp [domain_inter,domain_insert]
      \\ EQ_TAC \\ rw [] \\ simp [])
    \\ pop_assum kall_tac \\ fs [wordSemTheory.set_vars_def]
    \\ once_rewrite_tac [list_Seq_def]
    \\ Cases_on `x0 ≠ 1w` \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval,alist_insert_def]
    THEN1
     (rveq \\ fs []
      \\ unabbrev_all_tac
      \\ fs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def,wordSemTheory.flush_state_def]
      \\ pairarg_tac \\ fs [] \\ rveq
      \\ fs [wordSemTheory.state_component_equality]
      \\ match_mp_tac option_le_trans \\ goal_assum drule
      \\ fs[sane_locals_size_def]
      \\ rw[stack_size_eq2,wordSemTheory.stack_size_frame_def,
            option_le_max,option_le_max_right,AC option_add_comm option_add_assoc,
            option_map2_max_add,option_le_add,option_le_eq_eqns]
      \\ fs[eq_code_stack_max_sub1]
      \\ rw[stack_size_eq2,wordSemTheory.stack_size_frame_def,
            option_le_max,option_le_max_right,AC option_add_comm option_add_assoc,
            option_map2_max_add,option_le_add,option_le_eq_eqns])
    \\ ntac 3 (once_rewrite_tac [list_Seq_def])
    \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval]
    \\ `t2.code = t.code /\ t2.clock = ck` by
     (unabbrev_all_tac
      \\ fs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def]
      \\ pairarg_tac \\ fs [] \\ rveq
      \\ fs [wordSemTheory.state_component_equality,word_exp_ShiftVar_bits,lookup_insert,eq_eval])
    \\ rewrite_tac [list_Seq_def] \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval]
    \\ qmatch_goalsub_abbrev_tac `(Equal1_code c, t5)`
    \\ first_x_assum (qspecl_then [`t5`,`l1`,`l2`] mp_tac)
    \\ impl_tac THEN1
     (unabbrev_all_tac
      \\ fs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def]
      \\ pairarg_tac \\ fs [] \\ rveq
      \\ fs [wordSemTheory.state_component_equality,word_exp_ShiftVar_bits,lookup_insert,eq_eval,sane_locals_size_def]
     )
    \\ strip_tac \\ fs []
    \\ rveq \\ fs []
    \\ unabbrev_all_tac
    \\ fs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def]
    \\ pairarg_tac \\ fs [] \\ rveq
    \\ fs [wordSemTheory.state_component_equality]
    \\ imp_res_tac word_eq_LESS_EQ
    \\ fs[eq_code_stack_max_sub1]
    \\ match_mp_tac option_le_trans \\ goal_assum drule
    \\ rw[option_le_max] \\ TRY(match_mp_tac option_le_trans \\ goal_assum drule)
    \\ fs[sane_locals_size_def]
    \\ fs[eq_code_stack_max_sub1]
    \\ rw[stack_size_eq2,wordSemTheory.stack_size_frame_def,
          option_le_max,option_le_max_right,AC option_add_comm option_add_assoc,
          option_map2_max_add,option_le_add,option_le_eq_eqns]
    \\ `option_le (eq_code_stack_max (x2) t2.stack_size)
                  (eq_code_stack_max (wck - 1) t2.stack_size)`
         by(match_mp_tac eq_code_stack_max_le_mono >> rw[])
    \\ metis_tac[option_le_eq_eqns,option_le_add,option_le_trans,option_add_assoc,
                 option_add_comm]
   )
  \\ rewrite_tac [Equal_code_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ Cases_on `v1 = v2` \\ fs []
  THEN1
   (strip_tac \\ rveq \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval]
    \\ fs [wordSemTheory.state_component_equality,wordSemTheory.flush_state_def,
           option_le_max_right])
  \\ ntac 2 (once_rewrite_tac [list_Seq_def])
  \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval]
  \\ fs [GSYM (SIMP_CONV (srw_ss()) [word_bit_test] ``~word_bit 0 (w && w1)``)]
  \\ fs [word_bit_and]
  \\ IF_CASES_TAC
  THEN1 (fs [] \\ rw [] \\ fs [] \\
         fs [wordSemTheory.state_component_equality,
             wordSemTheory.flush_state_def,option_le_max_right])
  \\ fs [] \\ fs [word_header_def]
  \\ Cases_on `get_real_addr c t.store v1`
  \\ Cases_on `get_real_addr c t.store v2`
  \\ fs [] THEN1 (every_case_tac \\ fs [])
  \\ rename1 `get_real_addr c t.store v1 = SOME x1`
  \\ rename1 `get_real_addr c t.store v2 = SOME x2`
  \\ Cases_on `x1 IN t.mdomain` \\ fs []
  \\ Cases_on `t.memory x1` \\ fs []
  \\ Cases_on `x2 IN t.mdomain` \\ fs []
  \\ Cases_on `t.memory x2` \\ fs []
  \\ rename1 `t.memory x1 = Word c1`
  \\ rename1 `t.memory x2 = Word c2`
  (* first real_addr *)
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval]
  \\ qmatch_goalsub_abbrev_tac `word_exp t6`
  \\ `get_real_addr c t6.store v1 = SOME x1` by fs [Abbr`t6`]
  \\ drule0 (get_real_addr_lemma |> REWRITE_RULE [CONJ_ASSOC]
              |> ONCE_REWRITE_RULE [CONJ_COMM] |> GEN_ALL)
  \\ disch_then (qspec_then `2` mp_tac)
  \\ impl_tac THEN1 fs [Abbr `t6`,word_exp_ShiftVar_bits,lookup_insert,eq_eval]
  \\ strip_tac \\ fs []
  (* second real_addr *)
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval]
  \\ qmatch_goalsub_abbrev_tac `word_exp t7`
  \\ `get_real_addr c t7.store v2 = SOME x2` by fs [Abbr`t7`]
  \\ drule0 (get_real_addr_lemma |> REWRITE_RULE [CONJ_ASSOC]
              |> ONCE_REWRITE_RULE [CONJ_COMM] |> GEN_ALL)
  \\ disch_then (qspec_then `4` mp_tac)
  \\ impl_tac THEN1 fs [Abbr `t7`,word_exp_ShiftVar_bits,lookup_insert,eq_eval]
  \\ strip_tac \\ fs []
  (* -- *)
  \\ ntac 2 (once_rewrite_tac [list_Seq_def])
  \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval]
  \\ reverse IF_CASES_TAC \\ rewrite_tac []
  THEN1
   (pop_assum kall_tac \\ fs []
    \\ fs [] \\ once_rewrite_tac [list_Seq_def] \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval]
    \\ IF_CASES_TAC THEN1
     (fs [] \\ strip_tac \\ rw [] \\ fs []
      \\ fs [wordSemTheory.state_component_equality,
             wordSemTheory.flush_state_def,option_le_max_right])
    \\ fs [] \\ rveq
    \\ once_rewrite_tac [list_Seq_def] \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval,word_bit_test]
    \\ IF_CASES_TAC THEN1
     (fs [] \\ strip_tac \\ rw [] \\ fs []
      \\ fs [wordSemTheory.state_component_equality,
             wordSemTheory.flush_state_def,option_le_max_right])
    \\ once_rewrite_tac [list_Seq_def]
    \\ once_rewrite_tac [list_Seq_def]
    \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval,word_bit_test]
    \\ qmatch_goalsub_abbrev_tac`COND test1`
    \\ `(24w && c1) = 16w ⇔ test1`
    by (
      simp[Abbr`test1`]
      \\ srw_tac[wordsLib.WORD_BIT_EQ_ss][]
      \\ rw[Once EQ_IMP_THM]
      >- (
        spose_not_then strip_assume_tac
        \\ first_x_assum(qspec_then`i`mp_tac)
        \\ simp[] \\ rfs[word_index] )
      >- (
        `4 < dimindex(:'a)` by fs[good_dimindex_def]
        \\ asm_exists_tac \\ fs[word_index]
        \\ metis_tac[] )
      >- (
        rfs[word_index]
        \\ `3 < dimindex(:'a)` by fs[good_dimindex_def]
        \\ metis_tac[] ))
    \\ pop_assum SUBST1_TAC \\ qunabbrev_tac`test1`
    \\ IF_CASES_TAC THEN1
     (fs [] \\ strip_tac \\ rw [] \\ fs []
      \\ fs [wordSemTheory.state_component_equality,
             wordSemTheory.flush_state_def,option_le_max_right])
    \\ pop_assum kall_tac
    \\ fs [] \\ TOP_CASE_TAC \\ fs []
    \\ strip_tac \\ rveq \\ fs []
    \\ ntac 3 (once_rewrite_tac [list_Seq_def]) \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval]
    \\ simp [word_exp_ShiftVar_bits] \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval]
    \\ fs [GSYM decode_length_def,shift_lsl]
    \\ ntac 3 (once_rewrite_tac [list_Seq_def]) \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval]
    \\ fs [GSYM NOT_LESS]
    \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
    \\ fs [eq_eval,lookup_insert,GSYM decode_length_def,shift_lsl]
    \\ qmatch_goalsub_abbrev_tac `(Compare1_code c, t9)`
    \\ drule0 Compare1_code_thm
    \\ disch_then (qspecl_then [`c`,`t9`] mp_tac)
    \\ impl_tac THEN1 (fs [Abbr`t9`,word_exp_ShiftVar_bits,lookup_insert,eq_eval])
    \\ strip_tac \\ fs []
    \\ fs[]
    \\ fs [wordSemTheory.state_component_equality,Abbr`t9`]
    \\ fs[eq_code_stack_max_sub1]
    \\ match_mp_tac option_le_trans \\ goal_assum drule
    \\ fs[sane_locals_size_def]
    \\ rw[stack_size_eq2,wordSemTheory.stack_size_frame_def,
          option_le_max,option_le_max_right,AC option_add_comm option_add_assoc,
          option_map2_max_add,option_le_add,option_le_eq_eqns]
    \\ metis_tac[option_le_add,option_add_comm]
   )
  \\ fs []
  \\ qpat_abbrev_tac `other_case = list_Seq _`
  \\ pop_assum kall_tac
  \\ fs [word_is_clos_def]
  \\ strip_tac
  \\ ntac 2 (once_rewrite_tac [list_Seq_def]) \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval]
  \\ IF_CASES_TAC
  THEN1 (fs [] \\ rveq \\ fs [wordSemTheory.state_component_equality,
                              wordSemTheory.flush_state_def,option_le_max_right])
  \\ ntac 1 (once_rewrite_tac [list_Seq_def]) \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval]
  \\ IF_CASES_TAC
  THEN1 (fs [] \\ rveq \\ fs [wordSemTheory.state_component_equality,
                              wordSemTheory.flush_state_def,option_le_max_right])
  \\ fs []
  \\ ntac 1 (once_rewrite_tac [list_Seq_def]) \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval]
  \\ reverse IF_CASES_TAC
  THEN1 (fs [] \\ rveq \\ fs [wordSemTheory.state_component_equality,
                              wordSemTheory.flush_state_def,option_le_max_right])
  \\ fs []
  \\ ntac 4 (once_rewrite_tac [list_Seq_def]) \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval]
  \\ simp [word_exp_ShiftVar_bits] \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval]
  \\ fs [GSYM decode_length_def,shift_lsl]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
  \\ fs [eq_eval,lookup_insert,GSYM decode_length_def,shift_lsl]
  \\ qmatch_goalsub_abbrev_tac `(Equal1_code c,t8)`
  \\ first_x_assum (qspecl_then [`t8`,`l1`,`l2`] mp_tac)
  \\ impl_tac THEN1 (unabbrev_all_tac \\ fs [word_exp_ShiftVar_bits,lookup_insert,eq_eval,sane_locals_size_def])
  \\ strip_tac \\ fs []
  \\ fs [Abbr`t8`,wordSemTheory.state_component_equality]
  \\ qhdtm_x_assum `option_le` (strip_assume_tac o REWRITE_RULE [option_le_max_right])
  >- metis_tac[option_le_max_right,option_le_trans]
  >- (simp[option_le_max_right] \\ disj2_tac \\
      drule_then match_mp_tac option_le_trans \\
      rw[stack_size_eq2,wordSemTheory.stack_size_frame_def,
        option_le_max,option_le_max_right,AC option_add_comm option_add_assoc,
        option_map2_max_add,option_le_add,option_le_eq_eqns,eq_code_stack_max_sub1] >>
      metis_tac[option_add_comm, option_le_add]
     )
  >- (simp[option_le_max_right] \\ disj2_tac \\
      drule_then match_mp_tac option_le_trans \\
      simp[option_le_eq_eqns] \\ disj2_tac \\
      match_mp_tac eq_code_stack_max_le_mono \\ simp[])
QED

Theorem Equal_code_thm:
    word_eq c st dm m l wck v1 v2 = SOME (res,l',wck') /\
    dm = (t:('a,'c,'ffi) wordSem$state).mdomain /\
    m = t.memory /\
    st = t.store /\
    l <= t.clock /\
    c.len_size + 9 < dimindex (:'a) /\
      arch_width_bits c.arch_width = dimindex (:'a) /\
    shift_length c < dimindex (:'a) /\
    t.locals_size = lookup Equal_location t.stack_size /\
    (?md. lookup Equal_location t.code = SOME (3,Equal_code c,md)) /\
    (?md. lookup Equal1_location t.code = SOME (4,Equal1_code c,md)) /\
    (?md. lookup Compare1_location t.code = SOME (4,Compare1_code c,md)) /\
    get_var 0 t = SOME (Loc l1 l2) /\
    get_var 2 t = SOME (Word (v1:'a word)) /\
    get_var 4 t = SOME (Word (v2:'a word)) /\
    c.len_size <> 0 /\
    c.len_size < dimindex (:α) /\
    good_dimindex (:'a) ==>
    ?ck new_p smx.
      evaluate (Equal_code c,t) =
        (SOME (Result (Loc l1 l2) [Word res]),
         t with <| clock := ck; locals := LN; locals_size := SOME 0; permute := new_p;
                   stack_max := smx|>) /\
      option_le smx (OPTION_MAP2 MAX t.stack_max
                                    (OPTION_MAP2 $+
                                                 (stack_size t.stack)
                                                 (eq_code_stack_max (wck+1) t.stack_size))) /\
      l' <= ck
Proof
  strip_tac
  \\ match_mp_tac (Equal_code_lemma |> CONJUNCT1)
  \\ fs [] \\ asm_exists_tac \\ fs [sane_locals_size_def]
QED

Theorem MIN_SUB[local]:
  MIN a b - c = MIN (a - c) (b - c)
Proof
  rw[MIN_DEF]
QED

Theorem assign_Equal:
  op = BlockOp Equal ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ ‘names_opt ≠ NONE’ by (qpat_x_assum ‘op_requires_names _ ⇎ _’ mp_tac \\ EVAL_TAC \\ simp [])
  \\ gvs [GSYM IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS]
  \\ rename [‘cut_state_opt (SOME kept_names) s’]
  \\ drule_all state_rel_cut_state_opt_SOME \\ strip_tac
  \\ qpat_x_assum ‘_ (t with locals := y) NONE locs’ $ ASSUME_NAMED_TAC "with_locals"
  \\ qpat_x_assum `_  s t NONE locs`$ ASSUME_NAMED_TAC "old"
  \\ fs [do_app,oneline do_int_app_def]
  \\ gvs[AllCaseEqs()]
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [get_var_def]
  \\ qabbrev_tac ‘t0 = t with locals := y’
  \\ fs [Boolv_def] \\ rveq \\ fs [GSYM Boolv_def]
  \\ LABEL_ASSUM "old" (assume_tac o REWRITE_RULE [state_rel_thm])
  \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule memory_rel_get_vars_IMP
  \\ disch_then drule
  \\ simp [] \\ strip_tac
  \\ ‘x.refs = s.refs’ by (imp_res_tac cut_state_opt_SOME_eq \\ asm_rewrite_tac [] \\ simp [])
  \\ qpat_x_assum ‘x.refs = s.refs’ (fn th => full_simp_tac std_ss [th])
  \\ rename1 `memory_rel _ _ _ _ _ _ _ _ ((h_1,a_1)::(h_2,a_2)::_)`
  \\ rpt_drule0 memory_rel_simple_eq
  \\ strip_tac \\ fs [] \\ rveq
  \\ fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF]
  \\ fs [wordSemTheory.get_var_def]
  \\ fs [assign_def,arg2_def,assign_Equal_def]
  \\ simp [Ntimes list_Seq_def 5] \\ eval_tac
  \\ fs [lookup_insert,wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def,
         word_cmp_Test_1,word_bit_or]
  \\ IF_CASES_TAC THEN1
   (fs [lookup_insert,state_rel_thm]
    \\ fs [wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def]
    \\ qpat_x_assum ‘_ ⇒ _’ mp_tac
    \\ impl_tac >- gvs [word_bit_and]
    \\ strip_tac \\ asm_rewrite_tac []
    \\ rewrite_tac [push_if]
    \\ rewrite_tac [split_if]
    \\ rewrite_tac [push_if]
    \\ simp []
    \\ fs [lookup_insert,inter_insert_ODD_adjust_set]
    \\ conj_tac >- (fs [lookup_insert,adjust_var_11] \\ rw [])
    \\ conj_tac >- rfs[option_le_max_right]
    \\ conj_tac >- rfs[option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ IF_CASES_TAC \\ gvs []
    \\ rpt (match_mp_tac memory_rel_Boolv_T \\ fs [])
    \\ rpt (match_mp_tac memory_rel_Boolv_F \\ fs [])
    \\ match_mp_tac (GEN_ALL memory_rel_zero_space)
    \\ first_x_assum $ irule_at Any)
  \\ pop_assum kall_tac
  \\ pop_assum kall_tac
  \\ drule_all word_eq_thm
  \\ IF_CASES_TAC
  >-
   (pop_assum mp_tac
    \\ simp [lookup_insert,asmTheory.word_cmp_def]
    \\ strip_tac \\ gvs []
    \\ simp [Once word_eq_def]
    \\ strip_tac \\ gvs []
    \\ simp [state_rel_thm,lookup_insert,adjust_var_11]
    \\ fs [lookup_insert,inter_insert_ODD_adjust_set]
    \\ fs [state_rel_thm]
    \\ conj_tac >- (fs [lookup_insert,adjust_var_11] \\ rw [])
    \\ conj_tac >- rfs[option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ match_mp_tac memory_rel_Boolv_T \\ fs []
    \\ match_mp_tac (GEN_ALL memory_rel_zero_space)
    \\ first_x_assum $ irule_at Any)
  \\ strip_tac
  \\ rpt_drule0 (Equal_code_thm |> INST_TYPE [``:'b``|->``:'ffi``])
  \\ strip_tac
  \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def,lookup_insert,
         wordSemTheory.bad_dest_args_def,wordSemTheory.find_code_def]
  \\ `(?md. lookup Equal_location t.code = SOME (3,Equal_code c,md))` by
       (fs [state_rel_def,code_rel_def,stubs_md_def,stubs_def,MAP_MAP_o,o_DEF] \\ NO_TAC)
  \\ fs [wordSemTheory.add_ret_loc_def,get_names_def]
  \\ fs [cut_envs_adjust_sets_ODD,domain_adjust_sets]
  \\ drule cut_env_IMP_cut_envs \\ strip_tac \\ gvs []
  \\ qpat_abbrev_tac `t1 = wordSem$call_env _ _ _`
  \\ first_x_assum (qspecl_then [`t1`,`l`,`n`] mp_tac)
  \\ impl_tac THEN1
     (unabbrev_all_tac
      \\ fs [wordSemTheory.call_env_def,wordSemTheory.push_env_def,
             wordSemTheory.dec_clock_def]
      \\ fs [fromList2_def,lookup_insert]
      \\ fs [state_rel_def,code_rel_def,stubs_md_def,stubs_def,MAP_MAP_o,o_DEF]
      \\ fs [memory_rel_def,word_ml_inv_def,heap_in_memory_store_def])
  \\ strip_tac \\ fs []
  \\ pop_assum kall_tac
  \\ rfs[]
  \\ imp_res_tac evaluate_stack_max_le
  \\ `?t2. pop_env (t1 with
                        <|stack_max := smx; permute := new_p; clock := ck|>) = SOME t2 /\
           domain t2.locals = domain y1 ∪ domain y2` by
     (unabbrev_all_tac
      \\ fs [wordSemTheory.call_env_def,wordSemTheory.push_env_def,
             wordSemTheory.pop_env_def] \\ pairarg_tac
      \\ fs [domain_union,domain_fromAList_toAList]
      \\ imp_res_tac env_to_list_lookup_equiv
      \\ fs [domain_lookup,EXTENSION,lookup_fromAList, AC DISJ_COMM DISJ_ASSOC])
  \\ fs []
  \\ fs [lookup_insert,word_cmp_Less_word_cmp_res,wordSemTheory.set_vars_def,
         alist_insert_def,asmTheory.word_cmp_def]
  \\ rewrite_tac [push_if] \\ simp []
  \\ rewrite_tac [split_if] \\ simp []
  \\ fs [wordSemTheory.pop_env_def,wordSemTheory.call_env_def,
         wordSemTheory.push_env_def,wordSemTheory.dec_clock_def]
  \\ pairarg_tac \\ fs [] \\ rveq \\ fs []
  \\ fs[CaseEq "bool",CaseEq"prod",CaseEq"option",CaseEq"list",CaseEq"stack_frame",
        FST_EQ_EQUIV,ELIM_UNCURRY] >> rveq >> fs[lookup_insert]
  \\ rfs[wordSemTheory.set_vars_def,alist_insert_def]
  \\ simp [state_rel_thm]
  \\ gvs [Abbr‘t1’]
  \\ fs [lookup_insert,adjust_var_11]
  \\ qabbrev_tac ‘t_locals = union y2 y1’
  \\ ‘union (fromAList e) (fromAList (toAList y1)) = t_locals’ by
     (gvs [Abbr‘t_locals’]
      \\ match_mp_tac (METIS_PROVE [] “f1 = f2 ∧ x1 = x2 ⇒ h f1 x1 = h f2 x2”)
      \\ imp_res_tac cut_envs_wf
      \\ DEP_REWRITE_TAC [spt_eq_thm]
      \\ drule env_to_list_lookup_equiv
      \\ simp [wf_fromAList,lookup_fromAList,ALOOKUP_toAList])
  \\ full_simp_tac std_ss [inter_insert_ODD_adjust_set]
  \\ qpat_x_assum ‘state_rel c l1 l2 x t NONE locs’ $ ASSUME_NAMED_TAC "state_rel_t"
  \\ LABEL_X_ASSUM "with_locals" assume_tac
  \\ gvs [Abbr‘t0’]
  \\ gvs [state_rel_thm]
  \\ conj_tac >- rw []
  \\ conj_tac >-
      (rfs[option_le_max_right,option_le_max,stack_size_eq2,wordSemTheory.stack_size_frame_def,
           AC option_add_comm option_add_assoc])
  \\ conj_tac >-
      (drule_then match_mp_tac option_le_trans >>
       imp_res_tac stack_rel_IMP_size_of_stack >>
       fs[eq_code_stack_max_sub1,stack_consumed_def] >>
       rw[option_le_max_right,option_le_max,stack_size_eq2,wordSemTheory.stack_size_frame_def,
          AC option_add_comm option_add_assoc,state_rel_def,option_map2_max_add,
          option_le_eq_eqns,option_le_add,option_le_refl,MIN_SUB])
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs [inter_insert_ODD_adjust_set_alt]
  \\ match_mp_tac (GEN_ALL memory_rel_zero_space)
  \\ qexists_tac `x.space`
  \\ IF_CASES_TAC \\ simp []
  \\ rpt (match_mp_tac memory_rel_Boolv_T)
  \\ rpt (match_mp_tac memory_rel_Boolv_F) \\ fs []
QED

Theorem assign_ElemAt:
   (∃n. op = BlockOp (ElemAt n)) ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac \\ imp_res_tac state_rel_arch_width
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  \\ fs [do_app,CaseEq"list",CaseEq"dataSem$v",CaseEq"bool"]
  \\ rveq \\ fs []
  THEN1
   (fs [INT_EQ_NUM_LEMMA] \\ clean_tac
    \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_1] \\ clean_tac
    \\ imp_res_tac state_rel_get_vars_IMP
    \\ fs [assign_def] \\ eval_tac \\ fs [state_rel_thm]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ disch_then drule0 \\ fs []
    \\ imp_res_tac get_vars_1_IMP \\ fs []
    \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_1] \\ clean_tac
    \\ imp_res_tac get_vars_1_IMP \\ fs [] \\ strip_tac
    \\ drule0 (memory_rel_El' |> GEN_ALL) \\ fs []
    \\ disch_then drule
    \\ strip_tac \\ clean_tac
    \\ rename [`get_real_addr c t.store ptr_w = SOME x1`]
    \\ `word_exp t (real_addr c (adjust_var a1)) = SOME (Word x1)` by
          (match_mp_tac (GEN_ALL get_real_addr_lemma)
           \\ fs [wordSemTheory.get_var_def] \\ NO_TAC)
    \\ `x1 + bytes_in_word * n2w (n' + 1) = x1 + bytes_in_word + bytes_in_word * n2w n'` by
      (simp [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB] \\ CONV_TAC wordsLib.WORD_ARITH_CONV)
    \\ fs [] \\ eval_tac
    \\ fs [lookup_insert,adjust_var_11]
    \\ rw [] \\ fs []
    \\ TRY (fs [lookup_insert,adjust_var_def] \\ NO_TAC)
    \\ TRY (match_mp_tac option_le_trans \\ qexists_tac `t.stack_max` \\ fs [option_le_max_right] \\ NO_TAC)
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ TRY (rw [lookup_insert] \\ gvs [adjust_var_def] \\ first_x_assum irule \\ fs [] \\ NO_TAC)
    \\ irule (GEN_ALL memory_rel_insert) \\ fs []
    \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
    \\ fs [] \\ rw [] \\ fs [])
  \\ fs [INT_EQ_NUM_LEMMA] \\ clean_tac
  \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_1] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [assign_def] \\ eval_tac \\ fs [state_rel_thm,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs []
  \\ imp_res_tac get_vars_1_IMP \\ fs []
  \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_1] \\ clean_tac
  \\ imp_res_tac get_vars_1_IMP \\ fs [] \\ strip_tac
  \\ fs [CaseEq"option",CaseEq"ref",CaseEq"bool"] \\ rveq \\ fs []
  \\ drule0 (memory_rel_Deref' |> GEN_ALL) \\ fs []
  \\ strip_tac \\ clean_tac
  \\ pop_assum drule \\ strip_tac
  \\ `word_exp t (real_addr c (adjust_var a1)) = SOME (Word x)` by
        (match_mp_tac (GEN_ALL get_real_addr_lemma)
         \\ fs [wordSemTheory.get_var_def] \\ NO_TAC)
  \\ `x + bytes_in_word * n2w (n' + 1) = x + bytes_in_word + bytes_in_word * n2w n'` by
    (simp [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB] \\ CONV_TAC wordsLib.WORD_ARITH_CONV)
  \\ fs [] \\ eval_tac
  \\ fs [lookup_insert,adjust_var_11]
  \\ rw [] \\ fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ TRY (rw [lookup_insert] \\ gvs [adjust_var_def] \\ first_x_assum irule \\ fs [] \\ NO_TAC)
    \\ irule (GEN_ALL memory_rel_insert) \\ fs []
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
  \\ fs [] \\ rw [] \\ fs []
QED

Theorem IMP:
   b1 \/ b2 <=> ~b1 ==> b2
Proof
  Cases_on `b1` \\ Cases_on `b2` \\ fs []
QED

Theorem MemCopy_thm:
   !ret_val l1 l2 k c a1 a2 (s:('a,'c,'ffi) wordSem$state) m dm m1.
      memcopy k a1 a2 m dm  = SOME m1 /\
      arch_width_bits c.arch_width = dimindex(:'a) /\
      s.memory = m /\ s.mdomain = dm /\
      (?md. lookup MemCopy_location s.code = SOME (5,MemCopy_code c,md)) /\
      k <= s.clock /\ 2 * k < dimword (:'a) /\
      get_var 0 s = SOME (Loc l1 l2) /\
      get_var 2 s = SOME (Word (n2w (2 * k))) /\
      get_var 4 s = SOME (Word (a1:'a word)) /\
      get_var 6 s = SOME (Word a2) /\
      get_var 8 s = SOME ret_val ==>
      ?smx.
      evaluate (MemCopy_code c,s) =
        (SOME (Result (Loc l1 l2) [ret_val]),
         s with <| clock := s.clock - k ;
                   memory := m1 ; locals := LN; locals_size := SOME 0;
                   stack_max := smx |>) /\
      option_le smx
        (OPTION_MAP2 MAX s.stack_max
          (OPTION_MAP2 $+ (stack_size s.stack)
                          (lookup MemCopy_location s.stack_size)))
Proof
  ntac 3 gen_tac
  \\ Induct \\ simp [Once memcopy_def]
  \\ rw [] \\ simp [MemCopy_code_def] \\ fs [eq_eval,wordSemTheory.flush_state_def]
  THEN1 (fs [wordSemTheory.state_component_equality,option_le_max_right])
  \\ ntac 5 (once_rewrite_tac [list_Seq_def])
  \\ fs [eq_eval,wordSemTheory.mem_store_def]
  \\ fs [list_Seq_def,eq_eval]
  \\ fs [MULT_CLAUSES,GSYM word_add_n2w]
  \\ qmatch_goalsub_abbrev_tac `(MemCopy_code c,s5)`
  \\ first_x_assum (qspecl_then [`c`,`a1 + bytes_in_word`,
      `a2 + bytes_in_word`,`s5`] mp_tac)
  \\ qunabbrev_tac `s5` \\ fs [lookup_insert,ADD1]
  \\ strip_tac \\ qexists_tac `smx`
  \\ fs[]
QED

Theorem assign_ConsExtend_expand =
  ``assign c n l dest (BlockOp (ConsExtend tag)) args names_opt``
  |> SIMP_CONV (srw_ss()) [assign_def]

Theorem get_vars_IMP_domain:
   !xs s y.
      get_vars xs s = SOME y ==>
      EVERY (\x. x IN domain s) xs
Proof
  Induct \\ fs [get_vars_SOME_IFF_data_eq] \\ rw []
  \\ fs [get_var_def,domain_lookup]
QED

Theorem memory_rel_IMP_free_space:
   memory_rel c be ts refs sp st m dm vars ==>
    ?nfree curr other.
      FLOOKUP st NextFree = SOME (Word nfree) /\
      FLOOKUP st CurrHeap = SOME (Word curr) /\
      (word_list_exists nfree sp * other) (fun2set (m,dm))
Proof
  fs [memory_rel_def,heap_in_memory_store_def] \\ strip_tac
  \\ fs [word_ml_inv_def,abs_ml_inv_def,unused_space_inv_def]
  \\ Cases_on `sp = 0` THEN1
   (fs [word_list_exists_def,SEP_CLAUSES,LENGTH_NIL,SEP_EXISTS_THM]
    \\ simp_tac (std_ss++sep_cond_ss) [cond_STAR,word_list_def,SEP_CLAUSES]
    \\ asm_exists_tac \\ fs [])
  \\ fs [] \\ drule0 heap_lookup_SPLIT \\ strip_tac
  \\ rveq \\ fs []
  \\ fs [word_heap_APPEND,word_heap_def,word_el_def]
  \\ `sp <= sp' + sp1` by fs []
  \\ pop_assum mp_tac
  \\ rewrite_tac [LESS_EQ_EXISTS]
  \\ strip_tac \\ full_simp_tac std_ss []
  \\ full_simp_tac std_ss [word_list_exists_ADD]
  \\ qpat_abbrev_tac `aa = word_list_exists _ _`
  \\ fs [AC STAR_ASSOC STAR_COMM]
  \\ asm_exists_tac \\ fs []
QED

Theorem IMP_store_list_SOME:
   !ws a n m dm other.
      (word_list_exists a n * other) (fun2set (m,dm)) /\ LENGTH ws <= n ==>
      ∃m1. store_list a ws m dm = SOME m1 /\
           (word_list a ws *
            word_list_exists (a + bytes_in_word * n2w (LENGTH ws)) (n - LENGTH ws) *
            other) (fun2set (m1,dm))
Proof
  Induct \\ fs [store_list_def,word_list_def,SEP_CLAUSES] \\ rw []
  \\ Cases_on `n` \\ fs [word_list_exists_thm,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ SEP_R_TAC \\ fs []
  \\ SEP_W_TAC
  \\ SEP_F_TAC \\ fs []
  \\ strip_tac \\ fs []
  \\ fs [AC STAR_COMM STAR_ASSOC,ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
QED

Theorem get_vars_cut_env:
   !vs bs.
      dataSem$cut_env nms x1 = SOME x2 /\
      dataSem$get_vars vs x1 = SOME bs /\
      EVERY (\v. v IN domain nms) vs ==>
      dataSem$get_vars vs x2 = SOME bs
Proof
  Induct \\ fs [get_vars_def] \\ rw [] \\ fs []
  \\ every_case_tac \\ fs []
  \\ rveq \\ fs []
  \\ fs [cut_env_def] \\ rveq
  \\ fs [get_var_def,lookup_inter_alt]
QED

Theorem word_exp_real_addr_some_value:
   FLOOKUP s3.store CurrHeap = SOME (Word curr) /\
    get_var a s3 = SOME (Word ww) /\
    good_dimindex (:'a) /\ shift_length c < dimindex (:'a) ==>
    ∃wx. word_exp (s3:('a,'c,'ffi) wordSem$state) (real_addr c a) = SOME (Word wx)
Proof
  rw [real_addr_def] \\ fs [eq_eval] \\ eval_tac
  \\ IF_CASES_TAC \\ fs [NOT_LESS] \\ fs [GSYM NOT_LESS]
  \\ fs [good_dimindex_def, dimword_def] \\ rfs [shift_def]
QED

Theorem store_list_APPEND:
   !xs ys a m.
      store_list a (xs ++ ys) m dm =
      case store_list a xs m dm of
      | NONE => NONE
      | SOME m1 => store_list (a + bytes_in_word * n2w (LENGTH xs)) ys m1 dm
Proof
  Induct \\ fs [store_list_def]
  \\ rw [] \\ fs [] \\ every_case_tac \\ fs []
  \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,ADD1]
QED

Theorem memory_rel_store_list_to_unused:
   !ws2 m dm m1.
      memory_rel c be ts refs n st m dm vars /\
      store_list nfree ws2 m dm = SOME m1 /\
      FLOOKUP st NextFree = SOME (Word nfree) /\ LENGTH ws2 <= n ==>
      memory_rel c be ts refs n st m1 dm vars
Proof
  ho_match_mp_tac SNOC_INDUCT \\ rw [] \\ fs [store_list_def]
  \\ fs [SNOC_APPEND] \\ fs [store_list_APPEND]
  \\ every_case_tac \\ fs [] \\ res_tac \\ rfs []
  \\ fs [store_list_def] \\ rveq \\ fs []
  \\ rpt_drule0 memory_rel_write \\ fs []
QED

Theorem get_vars_delete_lemma:
   !t7. get_vars (MAP adjust_var t7)
            (s1 with
             locals :=
               insert 9 x9
                 (insert 7 x7
                    (insert 5 x5
                       (insert 1 x1 s1.locals)))) =
      get_vars (MAP adjust_var t7) s1
Proof
  Induct \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def,eq_eval]
QED

Theorem STAR_fun2set_IMP_SEP_T:
   (p * q) (fun2set (m, dm)) ==> (p * SEP_T) (fun2set (m, dm))
Proof
  qspec_tac (`fun2set (m, dm)`,`s`)
  \\ fs [GSYM SEP_IMP_def] \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ match_mp_tac SEP_IMP_STAR \\ fs [SEP_IMP_REFL]
  \\ EVAL_TAC \\ fs []
QED

Theorem IMP_memcopy_lemma:
   memory_rel c s1.be ts x.refs sp s1.store m1 s1.mdomain
      ((Block ts' n' l',Word w_ptr)::(ZIP (ys7,ws1) ++ vars)) /\
    startptr < LENGTH l' /\ LENGTH ys7 = LENGTH ws1 /\ good_dimindex (:α) /\
    lookup (adjust_var a1) s1.locals = SOME (Word (w_ptr:'a word)) /\
    word_exp s1 (real_addr c (adjust_var a1)) = SOME (Word wx) ==>
    memory_rel c s1.be ts x.refs sp s1.store m1 s1.mdomain
      ((Block ts' n' l',Word w_ptr)::
       (ZIP (ys7 ++ [EL startptr l'],
        ws1 ++ [m1 (wx + bytes_in_word + bytes_in_word * n2w startptr)]) ++ vars)) /\
    (wx + bytes_in_word + bytes_in_word * n2w startptr) IN s1.mdomain
Proof
  strip_tac \\ fs [GSYM SNOC_APPEND,ZIP_SNOC] \\ fs [SNOC_APPEND]
  \\ rpt_drule0 memory_rel_Block_IMP
  \\ full_simp_tac (std_ss++ARITH_ss) [GSYM LENGTH_NIL] \\ strip_tac
  \\ `word_exp s1 (real_addr c (adjust_var a1)) = SOME (Word a)` by
   (match_mp_tac (GEN_ALL get_real_addr_lemma)
    \\ fs [wordSemTheory.get_var_def]
    \\ fs [heap_in_memory_store_def,memory_rel_def])
  \\ fs [] \\ rveq \\ fs []
  \\ `small_int (dimindex (:'a)) (& startptr)` by
    (fs [small_int_def,good_dimindex_def,dimword_def] \\ rfs [])
  \\ rpt_drule0 (RW1 [CONJ_COMM] (RW [CONJ_ASSOC] IMP_memory_rel_Number))
  \\ strip_tac
  \\ imp_res_tac memory_rel_swap
  \\ drule0 memory_rel_El
  \\ `get_real_offset (Smallnum (&startptr)) =
      SOME (bytes_in_word + n2w startptr * bytes_in_word)` by
    fs [Smallnum_def,get_real_offset_def,good_dimindex_def,
        bytes_in_word_def,word_mul_n2w,WORD_MUL_LSL]
  \\ fs [] \\ rpt strip_tac \\ pop_assum mp_tac
  \\ match_mp_tac memory_rel_rearrange
  \\ fs [] \\ rw[] \\ fs[]
QED

Theorem IMP_memcopy = Q.prove(`
  !len startptr m1 m2 ws1 ys7 k ts.
      memory_rel c s1.be ts x.refs sp s1.store m1 s1.mdomain
        ((Block ts' n' l',Word w_ptr)::(ZIP (ys7,ws1) ++ vars)) /\
      (word_list nfree (Word full_header::ws1) *
       word_list_exists
         (nfree + bytes_in_word * n2w (SUC (LENGTH ws1))) k * other)
           (fun2set (m1,s1.mdomain)) /\ len <= k /\ good_dimindex (:α) /\
      lookup (adjust_var a1) s1.locals = SOME (Word (w_ptr:'a word)) /\
      word_exp s1 (real_addr c (adjust_var a1)) = SOME (Word wx) /\
      FLOOKUP s1.store NextFree = SOME (Word nfree) /\
      startptr + len <= LENGTH l' /\
      LENGTH ws1 + len < sp /\
      LENGTH ys7 = LENGTH ws1 ==>
      ∃m2 ws2.
        memcopy len (wx + bytes_in_word + bytes_in_word * n2w startptr)
          (nfree + bytes_in_word * n2w (LENGTH ws1 + 1)) m1 s1.mdomain =
          SOME m2 ∧
        (word_list nfree (Word full_header::(ws1 ++ ws2)) * SEP_T)
          (fun2set (m2,s1.mdomain)) ∧
        LENGTH ws2 = len ∧
        memory_rel c s1.be ts x.refs sp s1.store m2 s1.mdomain
          (ZIP (ys7 ++ TAKE len (DROP startptr l'),ws1 ++ ws2) ++ vars)`,
  Induct \\ simp [Once memcopy_def,LENGTH_NIL] THEN1
   (rpt strip_tac \\ full_simp_tac std_ss [GSYM STAR_ASSOC]
    THEN1 imp_res_tac STAR_fun2set_IMP_SEP_T
    \\ imp_res_tac memory_rel_tl \\ fs [])
  \\ rpt gen_tac
  \\ Cases_on `k` \\ fs []
  \\ fs [word_list_exists_thm,SEP_CLAUSES,SEP_EXISTS_THM,PULL_EXISTS]
  \\ rpt strip_tac \\ fs [ADD1]
  \\ SEP_W_TAC \\ SEP_R_TAC
  \\ qmatch_goalsub_abbrev_tac `memcopy _ _ _ m4`
  \\ qabbrev_tac `xx = m1 (wx + bytes_in_word + bytes_in_word * n2w startptr)`
  \\ `startptr < LENGTH l'` by fs []
  \\ rpt_drule0 IMP_memcopy_lemma
  \\ strip_tac
  \\ `memory_rel c s1.be ts x.refs sp s1.store m4 s1.mdomain
         ((Block ts' n' l',Word w_ptr)::
              (ZIP (ys7 ++ [EL startptr l'],ws1 ++ [xx]) ++ vars))` by
   (rpt_drule0 memory_rel_write \\ fs []
    \\ disch_then (qspecl_then [`xx`,`LENGTH ws1 + 1`] mp_tac) \\ fs [])
  \\ first_x_assum drule0 \\ fs []
  \\ disch_then (qspecl_then [`startptr + 1`,`n`] mp_tac)
  \\ impl_tac THEN1
   (fs [word_list_def,word_list_APPEND,SEP_CLAUSES]
    \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB, AC STAR_COMM STAR_ASSOC])
  \\ simp [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ strip_tac \\ simp []
  \\ qexists_tac `[xx] ++ ws2` \\ fs []
  \\ drule0 LESS_LENGTH
  \\ strip_tac \\ fs [] \\ rveq \\ fs []
  \\ `LENGTH ys1 + 1 = LENGTH (ys1 ++ [y])` by fs []
  \\ full_simp_tac std_ss [DROP_LENGTH_APPEND]
  \\ full_simp_tac std_ss [DROP_LENGTH_APPEND,GSYM APPEND_ASSOC]
  \\ `EL (LENGTH ys1) (ys1 ++ [y] ++ ys2) = y` by
     full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC,EL_LENGTH_APPEND,NULL,HD]
  \\ full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC] \\ fs [])
  |> SPEC_ALL |> GEN_ALL;

Theorem cut_envs_adjust_sets_insert_ODD:
  ODD n ⇒
  cut_envs (adjust_sets names) (insert n w t) =
  cut_envs (adjust_sets names) t
Proof
  rw [adjust_sets_def,wordSemTheory.cut_envs_def]
  \\ gvs [adjust_set_def,cut_names_adjust_set_insert_ODD]
  \\ qsuff_tac ‘cut_names (LS ()) (insert n w t) = cut_names (LS ()) t’
  >- gvs []
  \\ gvs [wordSemTheory.cut_names_def]
  \\ Cases_on ‘n = 0’ \\ gvs []
  \\ rw [] \\ gvs []
  \\ gvs [lookup_inter_alt]
  \\ rw [] \\ gvs [lookup_insert]
QED

Theorem IN_domain_adjust_set_IMP:
  x ∈ domain (adjust_set the_names) ⇒
  ∃xa. x = adjust_var xa ∧ xa ∈ domain the_names
Proof
  gvs [domain_lookup,adjust_set_def,lookup_fromAList]
  \\ rw [] \\ imp_res_tac ALOOKUP_MEM
  \\ gvs [MEM_MAP,EXISTS_PROD,adjust_var_11]
  \\ imp_res_tac MEM_toAList \\ fs []
QED

Theorem assign_ConsExtend:
  (?tag. op = BlockOp (ConsExtend tag)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ imp_res_tac state_rel_arch_width \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ `option_le x.stack_max s2.stack_max` by metis_tac[do_app_stack_max]
  \\ rpt_drule0 state_rel_cut_IMP \\ strip_tac
  \\ fs [dataLangTheory.op_requires_names_def,
         dataLangTheory.op_space_reset_def,cut_state_opt_def]
  \\ Cases_on `names_opt` \\ fs []
  \\ drule_all (state_rel_cut_state_opt_SOME |> SRULE [cut_state_opt_def])
  \\ strip_tac
  \\ qpat_x_assum ‘_ (t with locals := y) NONE locs’ $ ASSUME_NAMED_TAC "with_locals"
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [do_app,allowed_op_def] \\ every_case_tac \\ fs [] \\ rveq
  \\ `?startptr len. i = &startptr /\ i' = & len` by
       (Cases_on `i` \\ Cases_on `i'` \\ fs [] \\ NO_TAC) \\ rveq \\ fs []
  \\ imp_res_tac state_rel_IMP_tstamps \\ fs [with_fresh_ts_def]
  \\ rveq \\ fs []
  \\ qpat_x_assum `& _ + _ <> _` mp_tac
  \\ fs [integerTheory.int_gt,integerTheory.INT_ADD,NOT_LESS]
  \\ fs [IMP] \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ clean_tac
  \\ `?a1 a2 a3 a4 arest. args = a1::a2::a3::a4::arest` by
   (Cases_on `args` \\ fs []
    \\ rpt (rename1 `LENGTH args = _` \\ Cases_on `args` \\ fs []) \\ NO_TAC)
  \\ rveq \\ fs []
  \\ rewrite_tac [assign_ConsExtend_expand] \\ fs []
  \\ CASE_TAC >- suspend "no_header"
  \\ suspend "header"
QED

Resume assign_ConsExtend[header]:
  fs []
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [get_vars_SOME_IFF_eq] \\ rveq \\ fs []
  \\ full_simp_tac std_ss [GSYM wordSemTheory.get_var_def]
  \\ rpt_drule0 evaluate_BignumHalt2
  \\ rename1 `LENGTH t7 = LENGTH ys7`
  \\ `?w4. get_var (adjust_var a4) t = SOME (Word w4) /\
           (~(w4 ' 0) ==> small_int (dimindex (:α)) (&(len + LENGTH t7)) /\
                          w4 = Smallnum (&(len + LENGTH t7)))` by
   (qpat_x_assum `state_rel c l1 l2 x t NONE locs` kall_tac
    \\ fs [state_rel_thm] \\ eval_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def]
    \\ ntac 3 (strip_tac \\ drule0 memory_rel_tl)
    \\ strip_tac
    \\ drule0 (memory_rel_any_Number_IMP |> ONCE_REWRITE_RULE [CONJ_COMM])
    \\ fs [] \\ strip_tac \\ rveq \\ fs [] \\ strip_tac
    \\ imp_res_tac memory_rel_Number_IMP \\ rfs [] \\ NO_TAC)
  \\ disch_then drule0 \\ strip_tac \\ fs []
  \\ Cases_on `w4 ' 0` THEN1
       (fs [check_lim_def] >>
        conj_tac >- metis_tac[option_le_max_right,option_le_trans,state_rel_def] >>
        fs [get_vars_def,CaseEq"option"] >>
        qpat_assum `state_rel c l1 l2 s t NONE locs`
          (mp_then (Pos hd) mp_tac state_rel_get_var_Number_IMP_alt) >>
        disch_then drule >>
        fs[adjust_var_def] >>
        rveq >> simp[] >>
        rpt strip_tac >>
        fs[small_int_def,state_rel_def,integerTheory.INT_NOT_LE,
           limits_inv_def,arch_size_def,good_dimindex_def,dimword_def] >> rfs[])
  \\ fs []
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.get_var_def]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ qmatch_goalsub_abbrev_tac `wordSem$evaluate (_, t5)`
  \\ pairarg_tac \\ pop_assum mp_tac
  \\ fs[]
  \\ `state_rel c l1 l2 s t5 NONE locs` by
       (unabbrev_all_tac \\ fs [state_rel_insert_1])
  \\ fs [get_names_def]
  \\ qmatch_goalsub_abbrev_tac `AllocVar c lim _` \\ fs [] \\ strip_tac
  \\ `?xa. dataSem$cut_env (list_insert (a1::a2::a3::a4::t7) x') s.locals =
           SOME xa` by
   (qpat_x_assum `get_vars (a1::a2::a3::a4::t7) s.locals = SOME _` mp_tac
    \\ qpat_x_assum `cut_state x' s = SOME x` mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ simp [cut_state_def,CaseEq"option",dataSemTheory.cut_env_def]
    \\ rpt strip_tac \\ rveq
    \\ imp_res_tac get_vars_IMP_domain
    \\ gvs [domain_list_insert,SUBSET_DEF,EVERY_MEM]
    \\ rw [] \\ fs [])
  \\ `get_var 1 t5 = SOME (Word (n2w (2 * (len + LENGTH t7))))` by
   (fs [wordSemTheory.get_var_def,Abbr`t5`,lookup_insert] \\ rveq
    \\ fs [Smallnum_def] \\ NO_TAC)
  \\ `2 * (len + LENGTH t7) < dimword (:'a)` by
   (fs [small_int_def] \\ rfs []
    \\ fs [dimword_def,good_dimindex_def,state_rel_def]
    \\ rfs [] \\ fs [] \\ NO_TAC)
  \\ rpt_drule0 AllocVar_thm_nary
  \\ `lim < dimword (:α) DIV 8` by
       (unabbrev_all_tac \\ fs []
        \\ fs [state_rel_def,EVAL ``good_dimindex (:'a)``,dimword_def])
  \\ disch_then (qspecl_then [`len + LENGTH t7`,`lim`,`res`,`s1`] mp_tac)
  \\ impl_tac >- fs []
  \\ strip_tac
  \\ reverse (Cases_on `res`)
  >-
   (fs []
    \\ `x.stack_max = s.stack_max /\ x.limits = s.limits /\ x.refs = s.refs /\
        cut_locals x' s = x` by
      (qpat_x_assum `cut_state x' s = SOME x` mp_tac
       \\ rpt (pop_assum kall_tac)
       \\ simp [cut_locals_def,cut_state_def,CaseEq"option"]
       \\ rpt strip_tac \\ rveq \\ simp [])
    \\ conj_tac
    >- (simp [check_lim_def]
        \\ qpat_x_assum `option_le s1.stack_max s.stack_max` mp_tac
        \\ qpat_x_assum `x.stack_max = s.stack_max` mp_tac
        \\ rpt (pop_assum kall_tac)
        \\ rpt strip_tac \\ fs []
        \\ metis_tac [option_le_trans,option_le_max_right])
    \\ strip_tac \\ simp [check_lim_def]
    \\ spose_not_then strip_assume_tac
    \\ qpat_x_assum `_ /\ _ ==> s.limits.heap_limit < _` mp_tac
    \\ impl_tac
    >- (fs [Abbr `lim`]
        \\ fs [state_rel_def,limits_inv_def,arch_size_def,good_dimindex_def,
               dimword_def]
        \\ rfs [])
    \\ fs [space_consumed_def]
    \\ `LENGTH (TAKE len (DROP startptr l')) = len` by fs []
    \\ fs [])
  \\ suspend "after_alloc"
QED

Resume assign_ConsExtend[after_alloc]:
  fs []
  \\ qpat_x_assum `LENGTH ys7 = LENGTH _`
       (fn th => full_simp_tac std_ss [GSYM th])
  \\ qpat_x_assum
       `state_rel c l1 l2 (s with <|locals := xa; space := _|>) s1 NONE locs`
       (strip_assume_tac o REWRITE_RULE [state_rel_thm])
  \\ drule0 memory_rel_IMP_free_space \\ strip_tac \\ fs []
  \\ `dimindex (:'a) - c.len_size - 1 < dimword (:'a) /\
      dimindex (:'a) - c.len_size - 2 < dimword (:'a) /\
      1 < dimword (:'a) /\
      2 < dimword (:'a) /\ shift (dimindex (:'a)) < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword
        \\ fs [shift_def,good_dimindex_def] \\ decide_tac)
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [lookup_insert] \\ rveq
  \\ qabbrev_tac `tot_len = len + LENGTH ys7`
  \\ `x.refs = s.refs /\ x.global = s.global /\ x.stack = s.stack /\
      x.tstamps = s.tstamps` by
       (qpat_x_assum `cut_state x' s = SOME x` mp_tac
        \\ rpt (pop_assum kall_tac)
        \\ simp [cut_state_def,CaseEq"option"] \\ strip_tac \\ rveq \\ simp [])
  \\ fs [] \\ rveq
  \\ sg `lookup (adjust_var a2) s1.locals = SOME (Word (n2w (2 * startptr))) /\
      lookup (adjust_var a3) s1.locals = SOME (Word (n2w (2 * len))) /\
      lookup (adjust_var a4) s1.locals = SOME (Word (n2w (2 * tot_len))) /\
      ?ws1 w_ptr a_ptr.
        get_vars (MAP adjust_var t7) s1 = SOME ws1 /\
        lookup (adjust_var a1) s1.locals = SOME (Word w_ptr) /\
        (l' <> [] ==> get_real_addr c s1.store w_ptr = SOME a_ptr) /\
        memory_rel c s1.be (THE s.tstamps) s.refs (len + (LENGTH t7 + 1))
         s1.store s1.memory s1.mdomain
            ((Block n0 n' l',Word w_ptr)::(ZIP (ys7,ws1) ++
               join_env xa
                 (toAList (inter s1.locals (adjust_set xa))) ++
               [(the_global s.global,s1.store ' Globals)] ++
               flat s.stack s1.stack))`
  >-
   (full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ `get_vars (a1::a2::a3::a4::t7) xa =
          SOME (Block n0 n' l'::Number (&startptr)::Number (&len)::
              Number (&tot_len)::ys7)` by
      (rpt_drule0 get_vars_cut_env \\ disch_then match_mp_tac
       \\ fs [Abbr`tot_len`,domain_list_insert,EVERY_MEM])
    \\ `?w1 w2 w3 w4 ws1. get_vars
          (adjust_var a1::adjust_var a2::adjust_var a3::adjust_var a4::
           MAP adjust_var t7) s1 = SOME (w1::w2::w3::w4::ws1) /\
          LENGTH ws1 = LENGTH t7` by
      (qsuff_tac `!xs bs. get_vars xs xa = SOME bs ==>
                          ?bs1. get_vars (MAP adjust_var xs) s1 = SOME bs1`
       THEN1
        (disch_then drule0 \\ strip_tac \\ fs []
         \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
         \\ imp_res_tac get_vars_IMP_LENGTH_word \\ fs []
         \\ namedCases_on `bs1` ["", "w1 bs2"] \\ fs []
         \\ namedCases_on `bs2` ["", "w2 bs3"] \\ fs []
         \\ namedCases_on `bs3` ["", "w3 bs4"] \\ fs []
         \\ namedCases_on `bs4` ["", "w4h ws1"] \\ fs [])
       \\ pop_assum kall_tac
       \\ Induct \\ fs [get_vars_def,wordSemTheory.get_vars_def]
       \\ rpt gen_tac \\ rpt (TOP_CASE_TAC \\ fs [])
       \\ fs [get_var_def,wordSemTheory.get_var_def]
       \\ first_x_assum (qspec_then `h` mp_tac) \\ fs [] \\ NO_TAC)
    \\ rpt_drule0 memory_rel_get_vars_IMP_lemma
    \\ fs [get_vars_SOME_IFF]
    \\ strip_tac
    \\ ntac 3 (drule0 memory_rel_tl \\ strip_tac)
    \\ fs [wordSemTheory.get_var_def]
    \\ rpt_drule0 (memory_rel_Number_IMP |> REWRITE_RULE [CONJ_ASSOC]
                                         |> ONCE_REWRITE_RULE [CONJ_COMM])
  \\ impl_tac
  THEN1 (fs [small_int_def,good_dimindex_def,dimword_def] \\ rfs [] \\ fs [])
  \\ fs [Smallnum_def]
  \\ pop_assum kall_tac
  \\ rpt_drule0 (memory_rel_Number_IMP |> REWRITE_RULE [CONJ_ASSOC]
      |> ONCE_REWRITE_RULE [CONJ_COMM])
  \\ impl_tac
  THEN1 (fs [small_int_def,good_dimindex_def,dimword_def]
         \\ rfs [] \\ fs [Abbr `tot_len`])
  \\ fs [Smallnum_def]
  \\ pop_assum kall_tac
  \\ rpt_drule0 (memory_rel_Number_IMP |> REWRITE_RULE [CONJ_ASSOC]
      |> ONCE_REWRITE_RULE [CONJ_COMM])
  \\ impl_tac
  THEN1 (rpt_drule0 memory_rel_Block_IMP
         \\ fs [small_int_def,good_dimindex_def,dimword_def]
         \\ rfs [] \\ fs [Abbr `tot_len`]
         \\ strip_tac \\ pop_assum mp_tac \\ IF_CASES_TAC \\ fs []
         \\ strip_tac \\ fs [])
  \\ fs [Smallnum_def]
  \\ rpt_drule0 memory_rel_Block_IMP \\ fs []
  \\ strip_tac \\ fs [] \\ Cases_on `l' = []` \\ fs []
  \\ qpat_x_assum `memory_rel _ _ _ _ _ _ _ _ _` kall_tac
  \\ rpt strip_tac
  \\ qpat_x_assum `memory_rel _ _ _ _ _ _ _ _ _` mp_tac \\ rfs []
  \\ match_mp_tac memory_rel_rearrange
  \\ rw [] \\ fs [])
  \\ pop_assum strip_assume_tac
  \\ `dataSem$cut_env x' s.locals = SOME x.locals` by
       (qpat_x_assum `cut_state x' s = SOME x` mp_tac
        \\ rpt (pop_assum kall_tac)
        \\ simp [cut_state_def,CaseEq"option"] \\ strip_tac \\ rveq \\ simp [])
  \\ `dataSem$cut_env x' xa = SOME x.locals` by
       (drule_all cut_env_cut_env_list_insert \\ simp [])
  \\ sg `memory_rel c s1.be (THE s.tstamps) s.refs (len + (LENGTH t7 + 1))
          s1.store s1.memory s1.mdomain
          ((Block n0 n' l',Word w_ptr)::(ZIP (ys7,ws1) ++
             join_env x.locals
               (toAList (inter s1.locals (adjust_set x.locals))) ++
             [(the_global s.global,s1.store ' Globals)] ++
             flat s.stack s1.stack))`
  >-
   (qpat_x_assum `memory_rel _ _ _ _ _ _ _ _ ((Block _ _ _,_)::_)` mp_tac
    \\ match_mp_tac memory_rel_rearrange
    \\ `!k v. lookup k x.locals = SOME v ==> lookup k xa = SOME v` by
       (qpat_x_assum `dataSem$cut_env x' xa = SOME x.locals` mp_tac
        \\ rpt (pop_assum kall_tac)
        \\ simp [dataSemTheory.cut_env_def, AllCaseEqs()]
        \\ strip_tac \\ rpt strip_tac
        \\ qpat_x_assum `lookup _ x.locals = SOME _` mp_tac
        \\ qpat_x_assum `inter xa x' = x.locals`
           (fn th => rewrite_tac [GSYM th])
        \\ simp [lookup_inter_alt])
    \\ rw [] \\ fs []
    \\ disj2_tac \\ disj1_tac
    \\ drule_at (Pos last) join_env_submap_MEM \\ simp []
    \\ disch_then irule \\ rw [] \\ res_tac \\ simp [])
  \\ pop_assum mp_tac
  \\ qpat_x_assum `memory_rel _ _ _ _ _ _ _ _ (_ :: _)` kall_tac
  \\ qpat_x_assum `memory_rel _ _ _ _ _ _ _ _ (_ ++ _)` kall_tac
  \\ strip_tac
  \\ qpat_assum `LENGTH t7 = LENGTH ys7` (fn th => full_simp_tac std_ss [th])
  \\ fs []
  \\ `10 < dimindex (:'a)` by (fs [good_dimindex_def] \\ NO_TAC)
  \\ once_rewrite_tac [list_Seq_def]
  \\ `n2w (2 * tot_len) ⋙ 1 = n2w tot_len:'a word` by
      (rewrite_tac [GSYM w2n_11,w2n_lsr,w2n_n2w]
       \\ fs [Abbr`tot_len`]
       \\ simp [MULT_DIV |> ONCE_REWRITE_RULE [MULT_COMM]] \\ NO_TAC)
  \\ fs [eq_eval,wordSemTheory.word_sh_def]
  \\ qpat_abbrev_tac `full_header = word_or _ _`
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,s2)`
  \\ `?ws2. get_vars (5::MAP adjust_var t7) s2 = SOME ws2` by
   (qsuff_tac `get_vars (MAP adjust_var t7) s2 = SOME ws1`
    THEN1 fs [wordSemTheory.get_vars_def,Abbr`s2`,eq_eval]
    \\ qunabbrev_tac `s2`
    \\ qpat_x_assum `_ = SOME ws1` (fn th => fs [GSYM th])
    \\ qspec_tac (`ws1`,`ws1`)
    \\ qspec_tac (`t7`,`t7`) \\ Induct
    \\ fs [wordSemTheory.get_vars_def,eq_eval] \\ NO_TAC)
  \\ drule0 get_vars_IMP_LENGTH_word \\ strip_tac
  \\ sg `?m1. store_list nfree ws2 s2.memory s2.mdomain = SOME m1 /\
           (word_list nfree ws2 *
            word_list_exists (nfree + bytes_in_word * n2w (LENGTH ws2))
             (len + (LENGTH ys7 + 1) - LENGTH ws2) * other)
                (fun2set (m1,s1.mdomain))`
  >-
   (qunabbrev_tac `s2` \\ fs []
    \\ drule0 IMP_store_list_SOME
    \\ disch_then (qspec_then `ws2` mp_tac)
    \\ impl_tac
    >- (imp_res_tac get_vars_IMP_LENGTH_word
        \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [])
    \\ strip_tac \\ asm_exists_tac \\ fs [])
  \\ pop_assum strip_assume_tac
  \\ `get_var 1 s2 = SOME (Word nfree)` by (fs [eq_eval,Abbr `s2`] \\ NO_TAC)
  \\ rpt_drule0 evaluate_StoreEach
  \\ strip_tac
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ qunabbrev_tac `s2`
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,s2)`
  \\ mp_tac (Make_ptr_bits_thm |> Q.INST
              [`tag_reg`|->`9`,
               `len_reg`|->`7`,
               `dest`|->`3`,
               `t`|->`s2`,
               `tag1`|->`tag`,
               `len1`|->`tot_len`] |> Q.GENL [`d`,`f`])
  \\ simp [Abbr`s2`,FLOOKUP_UPDATE]
  \\ impl_tac THEN1
   (fs [eq_eval]
    \\ fs [encode_header_def,good_dimindex_def] \\ rfs [] \\ fs [dimword_def]
    \\ fs [memory_rel_def,heap_in_memory_store_def,shift_length_def]
    \\ rfs [] \\ fs [dimword_def] \\ decide_tac)
  \\ suspend "after_ptr"
QED

Resume assign_ConsExtend[after_ptr]:
  strip_tac
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ pop_assum kall_tac
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ `shift (dimindex (:'a)) < dimindex (:'a)` by
       (fs [good_dimindex_def,shift_def] \\ NO_TAC)
  \\ fs [eq_eval,wordSemTheory.set_store_def]
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval]
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,s3)`
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval]
  \\ `?wx. word_exp s3 (real_addr c (adjust_var a1)) = SOME (Word wx)` by
   (match_mp_tac (GEN_ALL word_exp_real_addr_some_value)
    \\ fs [wordSemTheory.get_var_def,Abbr `s3`,eq_eval,FLOOKUP_UPDATE]
    \\ rw [] \\ fs [] \\ NO_TAC)
  \\ fs [] \\ simp [Once word_exp_ShiftVar_bits]
  \\ fs [Abbr `s3`,eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval]
  \\ `(2 * len) < dimword (:α)` by
       (fs [dimword_def,good_dimindex_def,Abbr `tot_len`] \\ rfs [] \\ fs [])
  \\ simp []
  \\ rpt_drule0 memory_rel_store_list_to_unused \\ strip_tac
  \\ pop_assum mp_tac
  \\ impl_tac
  >- (imp_res_tac get_vars_IMP_LENGTH_word
      \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [])
  \\ strip_tac
  \\ `encode_header c (4 * tag) tot_len =
      SOME (make_header c (4 * tag) tot_len)` by
   (fs [encode_header_def,Abbr `lim`,memory_rel_def,
        heap_in_memory_store_def,good_dimindex_def,dimword_def]
    \\ rfs []
    \\ ((`32 - (c.len_size + 2) = 30 - c.len_size` by decide_tac
         \\ fs [EVAL ``2 ** 32 DIV 16``] \\ NO_TAC) ORELSE
        (`64 - (c.len_size + 2) = 62 - c.len_size` by decide_tac
         \\ fs [EVAL ``2 ** 64 DIV 16``] \\ NO_TAC)))
  \\ `full_header = (n2w (make_header c (4 * tag) tot_len):'a word)` by
   (fs [Abbr `full_header`,encode_header_def,make_header_def,
        WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
    \\ imp_res_tac memory_rel_arch_width
    \\ imp_res_tac memory_rel_len_size
    \\ `dimindex (:'a) - c.len_size =
        dimindex (:'a) - (c.len_size + 1) + 1` by decide_tac
    \\ `2 * (tot_len * 2 ** (dimindex (:'a) - (c.len_size + 1))) =
        tot_len * 2 ** (dimindex (:'a) - c.len_size)` by
         (qpat_x_assum `dimindex (:'a) - c.len_size = _`
            (fn th => once_rewrite_tac [th])
          \\ simp_tac std_ss [EXP_ADD]
          \\ simp_tac std_ss [AC MULT_ASSOC MULT_COMM])
    \\ qpat_x_assum `2 * (tot_len * 2 ** (dimindex (:'a) - (c.len_size + 1))) = _`
         (fn th => once_rewrite_tac [th])
    \\ qpat_x_assum `arch_width_bits c.arch_width = dimindex (:'a)`
         (fn th => once_rewrite_tac [th])
    \\ `16 * tag + (tot_len * 2 ** (dimindex (:'a) - c.len_size) + 3) =
        tot_len * 2 ** (dimindex (:'a) - c.len_size) + (16 * tag + 3)` by
         decide_tac
    \\ qpat_x_assum `16 * tag + (tot_len * 2 ** (dimindex (:'a) - c.len_size) + 3) = _`
         (fn th => once_rewrite_tac [th])
    \\ imp_res_tac memory_rel_arch_width
    \\ `dimindex (:'a) - c.len_size =
        2 + (dimindex (:'a) - (c.len_size + 2))` by decide_tac
    \\ `2 ** (dimindex (:'a) - c.len_size) =
        4 * 2 ** (dimindex (:'a) - (c.len_size + 2))` by
         (qpat_x_assum `dimindex (:'a) - c.len_size = 2 + _`
            (fn th => once_rewrite_tac [th])
          \\ simp_tac std_ss [EXP_ADD])
    \\ qpat_x_assum `arch_width_bits c.arch_width = dimindex (:'a)`
         (fn th => qpat_x_assum
            `4 * tag < 2 ** (arch_width_bits c.arch_width - (c.len_size + 2))`
            (fn th2 => assume_tac (REWRITE_RULE [th] th2)))
    \\ `x'' < 2 ** (dimindex (:'a) - c.len_size)` by
         (qpat_x_assum `2 ** (dimindex (:'a) - c.len_size) = _`
            (fn th => once_rewrite_tac [th])
          \\ qpat_x_assum `16 * tag + 3 = x''`
            (fn th => once_rewrite_tac [GSYM th])
          \\ decide_tac)
    \\ qpat_x_assum `16 * tag + 3 = x''`
         (fn th => once_rewrite_tac [th])
    \\ once_rewrite_tac [WORD_OR_COMM]
    \\ irule multiplied_header_or
    \\ conj_tac >-
         (qpat_x_assum `x'' < 2 ** (dimindex (:'a) - c.len_size)` ACCEPT_TAC)
    \\ decide_tac)
  \\ suspend "after_header"
QED

Resume assign_ConsExtend[after_header]:
  rfs [get_vars_delete_lemma] \\ rveq \\ fs []
  \\ `x.stack_max = s.stack_max /\ x.limits = s.limits /\
      x.locals_size = s.locals_size /\
      x.stack_frame_sizes = s.stack_frame_sizes /\ x.clock = s.clock /\
      x.code = s.code /\ x.compile = s.compile /\
      x.compile_oracle = s.compile_oracle /\ x.handler = s.handler` by
       (qpat_x_assum `cut_state x' s = SOME x` mp_tac
        \\ rpt (pop_assum kall_tac)
        \\ simp [cut_state_def,CaseEq"option"] \\ strip_tac \\ rveq \\ simp [])
  \\ fs []
  \\ Cases_on `len = 0` \\ fs []
  >- suspend "empty_len"
  \\ fs [list_Seq_def]
  \\ `(?md. lookup MemCopy_location s1.code = SOME (5,MemCopy_code c,md))` by
     (qpat_x_assum `code_rel c s.code t5.code` mp_tac
      \\ fs [code_rel_def,stubs_md_def,stubs_def,MAP_MAP_o,o_DEF])
  \\ `s1.termdep <> 0` by
     (imp_res_tac wordSemTheory.evaluate_clock \\ fs [Abbr `t5`])
  \\ fs [eq_eval] \\ pop_assum kall_tac
  \\ fs [cut_envs_adjust_sets_insert_ODD,domain_adjust_sets]
  \\ sg `?the_env. cut_env (adjust_sets x') s1.locals = SOME the_env`
  >-
   (simp [wordSemTheory.cut_env_def,domain_lookup,SUBSET_DEF,
          lookup_adjust_set,adjust_sets_def,AllCaseEqs(),PULL_EXISTS]
    \\ simp [wordSemTheory.cut_envs_def,AllCaseEqs()]
    \\ simp [GSYM PULL_EXISTS]
    \\ conj_tac
    >- gvs [wordSemTheory.cut_names_def,domain_lookup]
    \\ simp [wordSemTheory.cut_names_def]
    \\ fs [IS_SOME_lookup]
    \\ rewrite_tac [SUBSET_DEF] \\ rpt strip_tac
    \\ drule IN_domain_adjust_set_IMP
    \\ strip_tac \\ fs []
    \\ fs [domain_lookup,GSYM IS_SOME_EXISTS]
    \\ first_x_assum match_mp_tac
    \\ qpat_x_assum `dataSem$cut_env
           (list_insert t7 (insert a4 () (insert a3 ()
              (insert a2 () (insert a1 () x'))))) s.locals = SOME xa`
           (strip_assume_tac o
            REWRITE_RULE [dataSemTheory.cut_env_def,AllCaseEqs()])
    \\ qpat_x_assum `cut_state x' s = SOME x`
          (strip_assume_tac o
           REWRITE_RULE [cut_state_def,dataSemTheory.cut_env_def,AllCaseEqs()])
    \\ gvs [lookup_inter_alt,domain_list_insert,IS_SOME_EXISTS,
            domain_lookup,SUBSET_DEF]
    \\ gvs [lookup_insert] \\ res_tac \\ fs [])
  \\ pop_assum strip_assume_tac
  \\ drule cut_env_IMP_cut_envs \\ strip_tac
  \\ fs [] \\ simp [wordSemTheory.push_env_def]
  \\ Cases_on `env_to_list y2 s1.permute` \\ fs []
  \\ `n2w (2 * startptr) ≪ (shift (dimindex (:α)) − 1) =
      n2w startptr * bytes_in_word :'a word` by
    fs [good_dimindex_def,shift_def,bytes_in_word_def,word_mul_n2w,
        WORD_MUL_LSL]
  \\ rfs [] \\ fs []
  \\ qmatch_goalsub_abbrev_tac
    `insert 8 ar8 (insert 6 (Word ar6)
                   (insert 4 (Word ar4) (insert 2 _ (insert 0 ar0 _))))`
  \\ qmatch_goalsub_abbrev_tac `(MemCopy_code c,s88)`
  \\ sg `?m2 ws2'.
          memcopy len ar4 ar6 m1 s1.mdomain = SOME m2 /\
          (word_list nfree
             (Word (n2w (make_header c (4 * tag) tot_len))::(ws1 ++ ws2')) *
           SEP_T)
            (fun2set (m2,s1.mdomain)) /\ LENGTH ws2' = len /\
          memory_rel c s1.be next_stamp s.refs (len + (LENGTH ys7 + 1))
           s1.store m2 s1.mdomain
           ((ZIP (ys7 ++ TAKE len (DROP startptr l'),ws1 ++ ws2') ++
               join_env x.locals
                 (toAList (inter s1.locals (adjust_set x.locals))) ++
               [(the_global s.global,s1.store ' Globals)] ++
               flat s.stack s1.stack))`
  >- suspend "memcopy_setup"
  \\ suspend "after_memcopy"
QED

Resume assign_ConsExtend[after_memcopy]:
  pop_assum strip_assume_tac
  \\ rpt_drule0 MemCopy_thm
  \\ disch_then (qspecl_then [`ar8`,`n`,`l`,`s88`] mp_tac)
  \\ impl_tac THEN1
   (map_every qunabbrev_tac [`s88`,`ar0`]
    \\ fs [wordSemTheory.get_var_def,lookup_insert,word_mul_n2w]
    \\ match_mp_tac LESS_EQ_TRANS
    \\ qexists_tac `dimword (:α)`
    \\ conj_tac THEN1 (fs [dimword_def,good_dimindex_def] \\ rfs [])
    \\ fs [wordSemTheory.MustTerminate_limit_def])
  \\ strip_tac \\ fs [word_mul_n2w]
  \\ suspend "after_memcopy_eval"
QED

Resume assign_ConsExtend[after_memcopy_eval]:
  qunabbrev_tac `s88` \\ fs [wordSemTheory.pop_env_def]
  \\ reverse IF_CASES_TAC
  >- (sg `F` \\ fs [] \\ pop_assum mp_tac \\ simp []
      \\ imp_res_tac env_to_list_domain
      \\ simp [domain_union,domain_fromAList_toAList,
               AC UNION_COMM UNION_ASSOC])
  \\ fs [state_rel_thm,check_lim_def,code_oracle_rel_def,FLOOKUP_UPDATE,
         wordSemTheory.set_vars_def,alist_insert_def]
  \\ conj_tac THEN1
   (simp [lookup_union,lookup_fromAList,ALOOKUP_toAList,lookup_insert]
    \\ drule_all cut_envs_lookup_0 \\ simp [])
  \\ conj_tac THEN1
   (gen_tac \\ simp [lookup_insert,adjust_var_11] \\ IF_CASES_TAC \\ simp []
    \\ fs [lookup_fromAList,lookup_insert,adjust_var_11]
    \\ asm_rewrite_tac [GSYM IS_SOME_EXISTS,IS_SOME_lookup_domain]
    \\ rename [`kk ∈ _ ⇒ _`]
    \\ simp_tac std_ss [IN_UNION]
    \\ strip_tac
    \\ disj2_tac
    \\ qpat_x_assum `cut_envs (adjust_sets x') s1.locals = SOME (y1,y2)`
         mp_tac
    \\ simp [wordSemTheory.cut_envs_def,adjust_sets_def,
             wordSemTheory.cut_names_def,CaseEq"option"]
    \\ strip_tac \\ rpt var_eq_tac
    \\ simp [domain_inter,adjust_var_IN_adjust_set]
    \\ `kk ∈ domain x'` by
         (qpat_x_assum `cut_state x' s = SOME x` mp_tac
          \\ qpat_x_assum `kk ∈ domain x.locals` mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ simp [cut_state_def,dataSemTheory.cut_env_def,AllCaseEqs()]
          \\ rpt strip_tac \\ rveq \\ gvs [domain_inter])
    \\ fs [SUBSET_DEF]
    \\ first_x_assum match_mp_tac
    \\ simp [adjust_var_IN_adjust_set])
  \\ conj_tac THEN1
   (drule evaluate_stack_max_le
    \\ simp [option_le_max,stack_size_eq,AC option_add_comm option_add_assoc])
  \\ conj_tac THEN1
   (drule_then match_mp_tac option_le_trans
    \\ imp_res_tac stack_rel_IMP_size_of_stack
    \\ rw [option_le_max,option_le_max_right,
           AC option_add_comm option_add_assoc,stack_size_eq,
           option_le_eq_eqns,option_le_add])
  \\ simp [FAPPLY_FUPDATE_THM]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ rewrite_tac [inter_union_distrib]
  \\ `inter (fromAList (toAList y1)) (adjust_set x.locals) = LN` by
    (irule cut_envs_inter
     \\ first_assum $ irule_at $ Pos hd
     \\ gvs [cut_state_def,CaseEq"option"]
     \\ last_x_assum $ irule_at Any)
  \\ simp []
  \\ sg `join_env x.locals (toAList (inter s1.locals (adjust_set x.locals))) =
         join_env x.locals
           (toAList (inter (fromAList q) (adjust_set x.locals)))`
  >-
   (AP_TERM_TAC \\ AP_TERM_TAC
    \\ fs [spt_eq_thm,lookup_inter_alt]
    \\ rw [] \\ drule0 env_to_list_lookup_equiv
    \\ fs [lookup_fromAList]
    \\ rpt strip_tac \\ fs []
    \\ gvs [wordSemTheory.cut_envs_def,CaseEq"option",
            wordSemTheory.cut_names_def,adjust_sets_def]
    \\ fs [lookup_inter_alt] \\ rw []
    \\ drule IN_domain_adjust_set_IMP \\ strip_tac \\ rveq
    \\ fs [adjust_var_IN_adjust_set]
    \\ qpat_x_assum `cut_state x' s = SOME x` mp_tac
    \\ simp [cut_state_def,dataSemTheory.cut_env_def,AllCaseEqs()]
    \\ rpt strip_tac \\ rveq \\ gvs [domain_inter,adjust_var_IN_adjust_set]
    \\ qpat_x_assum `dataSem$cut_env x' s.locals = SOME x.locals` mp_tac
    \\ simp [dataSemTheory.cut_env_def,AllCaseEqs()]
    \\ strip_tac \\ gvs [domain_inter]
    \\ qpat_x_assum `inter s.locals x' = x.locals` (fn th => fs [GSYM th])
    \\ gvs [domain_inter])
  \\ fs [] \\ pop_assum kall_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ suspend "after_memcopy_state"
QED

Resume assign_ConsExtend[after_memcopy_state]:
  rpt_drule0 memory_rel_Cons_alt
  \\ disch_then (qspecl_then [`tag`,`make_header c (4 * tag) tot_len`] mp_tac)
  \\ suspend "cons_rel"
QED

Resume assign_ConsExtend[cons_rel]:
  reverse impl_tac
  >- suspend "cons_consequence"
  \\ suspend "cons_premise"
QED

Resume assign_ConsExtend[cons_consequence]:
  fs [shift_lsl,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ `LENGTH ys7 = LENGTH ws1` by
    (imp_res_tac get_vars_IMP_LENGTH \\ fs [])
  \\ fs [shift_lsl,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ qpat_x_assum `Abbrev (tot_len = len + LENGTH ws1)`
       (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])
  \\ fs [shift_lsl,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
QED

Resume assign_ConsExtend[cons_premise]:
  fs [] \\ CCONTR_TAC \\ fs [DROP_NIL]
  \\ gvs []
  \\ fs [markerTheory.Abbrev_def]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ gvs []
QED

Resume assign_ConsExtend[memcopy_setup]:
   `LENGTH ys7 = LENGTH ws1` by (imp_res_tac get_vars_IMP_LENGTH \\ fs [])
    \\ fs []
    \\ simp [Abbr`ar4`,Abbr`ar6`]
    \\ `(2w * n2w startptr) ≪ (shift (dimindex (:α)) − 1) =
         bytes_in_word * n2w startptr : 'a word` by
         fs [good_dimindex_def,shift_def,bytes_in_word_def,word_mul_n2w,WORD_MUL_LSL]
    \\ fs [GSYM word_mul_n2w,arch_bytes_word]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac IMP_memcopy \\ fs []
    \\ qexists_tac `w_ptr`
    \\ qexists_tac `n0`
    \\ qexists_tac `other`
    \\ qexists_tac `n'`
    \\ qexists_tac `(len + (LENGTH ws1 + 1) - SUC (LENGTH ws1))`
    \\ qexists_tac `a1`
    \\ fs [] \\ rfs []
    \\ qpat_x_assum `_ = SOME (Word wx)` (fn th => fs [GSYM th])
    \\ rpt (pop_assum kall_tac)
    \\ fs [real_addr_def] \\ rw []
    \\ fs [eq_eval,FLOOKUP_UPDATE,wordSemTheory.get_store_def]
QED

Resume assign_ConsExtend[empty_len]:
   fs [state_rel_thm,check_lim_def,FAPPLY_FUPDATE_THM,lookup_insert,
        adjust_var_11]
    \\ fs [inter_insert_ODD_adjust_set,code_oracle_rel_def,FLOOKUP_UPDATE]
    \\ conj_tac THEN1
     (rw [] \\ fs []
      \\ first_x_assum match_mp_tac
      \\ qpat_x_assum `dataSem$cut_env x' xa = SOME x.locals` mp_tac
      \\ qpat_x_assum `IS_SOME (lookup n x.locals)` mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ simp [dataSemTheory.cut_env_def,AllCaseEqs()]
      \\ rpt strip_tac
      \\ gvs [lookup_inter_alt,IS_SOME_EXISTS,AllCaseEqs()]
      \\ qpat_x_assum `inter xa x' = x.locals` (fn th => fs [GSYM th])
      \\ gvs [lookup_inter_alt,AllCaseEqs()])
    \\ conj_tac THEN1 (fs [option_le_max_right])
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ drule0 memory_rel_tl
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ strip_tac \\ rpt_drule0 memory_rel_Cons_alt
    \\ fs [Abbr`tot_len`] \\ imp_res_tac get_vars_IMP_LENGTH_word \\ fs []
    \\ full_simp_tac (std_ss++ARITH_ss)
                     [GSYM LENGTH_NIL,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ fs [GSYM bytes_in_word_mul_eq_shift,AND_IMP_INTRO]
    \\ `LENGTH ys7 = LENGTH ws1` by (imp_res_tac get_vars_IMP_LENGTH \\ fs [])
    \\ fs []
    \\ disch_then match_mp_tac
    \\ rfs []
    \\ drule0 IMP_store_list_SOME
    \\ disch_then (qspec_then
         `(Word (n2w (make_header c (4 * tag) (LENGTH ws1)))::ws1)` mp_tac)
    \\ simp_tac std_ss []
    \\ impl_tac THEN1 fs []
    \\ asm_rewrite_tac [] \\ simp_tac std_ss []
    \\ qspec_tac (`fun2set (m1,s1.mdomain)`,`ss`)
    \\ rewrite_tac [GSYM SEP_IMP_def,GSYM STAR_ASSOC]
    \\ match_mp_tac SEP_IMP_STAR
    \\ fs [SEP_IMP_REFL] \\ fs [SEP_IMP_def,SEP_T_def]
QED

Resume assign_ConsExtend[no_header]:
  simp [check_lim_def,space_consumed_def]
  \\ fs [check_lim_def,option_le_max_right,state_rel_def,
         space_consumed_def,encode_header_def,CaseEq"bool",arch_size_def,
         limits_inv_def,good_dimindex_def,dimword_def]
  \\ rfs []
  \\ `arch_width_bits c.arch_width = dimindex (:'a)` by
       fs [heap_in_memory_store_def]
  \\ `c.len_size + 9 < dimindex (:'a)` by
       fs [heap_in_memory_store_def]
  \\ TRY (disj1_tac \\ metis_tac [backendPropsTheory.option_le_trans] \\ NO_TAC)
  \\ (conj_tac THEN1
       (disj1_tac
        \\ qspecl_then [`r.stack_max`,`t.stack_max`,`x.stack_max`]
             mp_tac backendPropsTheory.option_le_trans
        \\ fs []))
  \\ ((`dimindex (:'a) - (c.len_size + 2) = 30 - c.len_size` by fs []
       \\ fs [] \\ NO_TAC) ORELSE
      (`2 ** dimindex (:'a) DIV 16 = 268435456` by
         (fs [] \\ EVAL_TAC)
       \\ fs [] \\ NO_TAC) ORELSE
      (`dimindex (:'a) - (c.len_size + 2) = 62 - c.len_size` by fs []
       \\ fs [] \\ NO_TAC) ORELSE
      (`2 ** dimindex (:'a) DIV 16 = 1152921504606846976` by
         (fs [] \\ EVAL_TAC)
       \\ fs [] \\ NO_TAC))
QED

Finalise assign_ConsExtend;

Theorem assign_Cons:
   (?tag. op = BlockOp (Cons tag)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ imp_res_tac state_rel_arch_width \\ imp_res_tac state_rel_small_shift_length \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t NONE locs` kall_tac \\ strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ Cases_on `LENGTH args = 0` THEN1
   (fs [assign_def] \\ reverse IF_CASES_TAC \\ fs []
    >-
      (fs[state_rel_def] >>
       conj_tac >- metis_tac[backendPropsTheory.option_le_trans,
                             do_app_stack_max,option_le_max_right] >>
       strip_tac >>
       fs[do_app,CaseEq"bool",CaseEq"option"] >>
       imp_res_tac get_vars_IMP_LENGTH >>
       rveq >> fs[arch_size_def,limits_inv_def,good_dimindex_def] >>
       rfs[dimword_def,with_fresh_ts_def,consume_space_def,
           IS_SOME_EXISTS])
    \\ fs [LENGTH_NIL] \\ rpt var_eq_tac
    \\ fs [do_app,allowed_op_def] \\ every_case_tac \\ fs []
    \\ imp_res_tac state_rel_IMP_tstamps \\ fs [with_fresh_ts_def]
    \\ rveq \\ fs []
    \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
    \\ TRY (Cases_on `vals`) \\ fs [] \\ clean_tac
    \\ eval_tac \\ clean_tac
    \\ fs [state_rel_def,lookup_insert,adjust_var_11,option_le_max_right]
    \\ rw [] \\ fs []
    \\ asm_exists_tac \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac word_ml_inv_insert \\ fs []
    \\ fs [word_ml_inv_def,PULL_EXISTS] \\ rw []
    \\ qexists_tac `Data (Word (n2w (2 * tag)))`
    \\ qexists_tac `hs` \\ fs [word_addr_def]
    \\ reverse conj_tac
    THEN1 (fs [GSYM word_mul_n2w,BlockNil_and_lemma])
    \\ `n2w (2 * tag) = BlockNil tag : 'a word` by
         fs [BlockNil_def,WORD_MUL_LSL,word_mul_n2w]
    \\ fs [cons_thm_EMPTY,GSYM dimword_def])
  \\ fs [assign_def] \\ CASE_TAC \\ fs []
  >- suspend "bad_header"
  \\ suspend "good_header"
QED

Resume assign_Cons[bad_header]:
  fs[state_rel_def] >>
  conj_tac >- metis_tac[backendPropsTheory.option_le_trans,do_app_stack_max,option_le_max_right] >>
     strip_tac >>
     fs[do_app,CaseEq"bool",CaseEq"option"] >>
     imp_res_tac get_vars_IMP_LENGTH >>
     rveq >> fs[arch_size_def,limits_inv_def,good_dimindex_def,encode_header_def] >>
     rfs[dimword_def,with_fresh_ts_def,consume_space_def,
         IS_SOME_EXISTS] >>
     rveq >> fs[check_lim_def] >> rveq >> fs[heap_in_memory_store_def] >>
     qpat_x_assum `arch_width_bits c.arch_width = dimindex (:'a)`
       (fn th => fs [th]) >>
     ((`dimindex (:'a) - (c.len_size + 2) = 30 - c.len_size` by
         decide_tac >> fs [] >> NO_TAC) ORELSE
      (qpat_x_assum `dimindex (:'a) = 32` (fn th => fs [th]) >> NO_TAC) ORELSE
      (`dimindex (:'a) - (c.len_size + 2) = 62 - c.len_size` by
         decide_tac >> fs [] >> NO_TAC) ORELSE
      (qpat_x_assum `dimindex (:'a) = 64` (fn th => fs [th]) >> NO_TAC))
QED

Resume assign_Cons[good_header]:
  fs [do_app,allowed_op_def] \\ every_case_tac \\ fs []
  \\ imp_res_tac state_rel_IMP_tstamps \\ fs [with_fresh_ts_def]
  \\ rveq \\ fs []
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ clean_tac
  \\ fs [consume_space_def] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ `shift_length c - shift (dimindex (:'a)) < dimword (:'a)` by
       (fs [state_rel_thm] \\ assume_tac dimindex_lt_dimword \\ decide_tac)
  \\ simp [state_rel_thm] \\ eval_tac
  \\ fs [state_rel_thm,option_le_max_right] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs [NOT_LESS,DECIDE ``n + 1 <= m <=> n < m:num``]
  \\ strip_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ `vals <> [] /\ (LENGTH vals = LENGTH ws)` by fs []
  \\ rpt_drule0 memory_rel_Cons1
  \\ strip_tac
  \\ fs [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.set_store_def]
  \\ qpat_abbrev_tac `t5 = t with <| locals := _ |>`
  \\ pairarg_tac \\ fs []
  \\ `t.memory = t5.memory /\ t.mdomain = t5.mdomain` by
       (unabbrev_all_tac \\ fs []) \\ fs []
  \\ ntac 2 (pop_assum kall_tac)
  \\ drule0 evaluate_StoreEach
  \\ disch_then (qspecl_then [`3::MAP adjust_var args`,`1`,`c`] mp_tac)
  \\ impl_tac THEN1
   (fs [wordSemTheory.get_vars_def,Abbr`t5`,wordSemTheory.get_var_def,
        lookup_insert,get_vars_with_store,get_vars_adjust_var]
    \\ `(t with locals := t.locals) = t` by
          fs [wordSemTheory.state_component_equality] \\ fs [] \\ NO_TAC)
  \\ clean_tac \\ fs [] \\ UNABBREV_ALL_TAC
  \\ fs [lookup_insert,FAPPLY_FUPDATE_THM,adjust_var_11,FLOOKUP_UPDATE,
         code_oracle_rel_def,FLOOKUP_UPDATE,check_lim_def]
  \\ rw [] \\ fs [] \\ rw [] \\ fs []
  \\ fs [inter_insert_ODD_adjust_set,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ fs [make_cons_ptr_def,get_lowerbits_def]
QED

Finalise assign_Cons;

Theorem store_list_word_cond_add_IMP:

 ∀ws m a m1 free.
 store_list free (MAP (const_word c (a:'a word)) ws) m dm = SOME m1 ==>
 const_addresses free ws dm ∧
 const_writes free (a << (shift_length c - shift(dimindex(:'a))))
    (MAP (λ(b,i). (b,i2w i)) ws) m = m1
Proof

 Induct >> simp[wordSemTheory.const_addresses_def,wordSemTheory.const_writes_def,store_list_def] >>
 Cases_on `h` >> Cases_on `q` >>
 simp[const_word_def,word_cond_add_def,wordSemTheory.const_addresses_def,wordSemTheory.const_writes_def,store_list_def] >>
 rw[] >> first_x_assum drule >> simp[]
QED

Theorem evaluate_StoreAnyConsts:

 ∀r1 r2 r3 vs w (s:('a,'c,'ffi) wordSem$state) free m dm m1.
 store_list free (MAP (const_word c (a:'a word)) vs) m dm = SOME m1 ∧
 m = s.memory ∧ dm = s.mdomain ∧ ALL_DISTINCT [r1;r2;r3] ∧
 lookup r2 s.locals = SOME (Word free) ∧
 lookup r3 s.locals = SOME (Word (a << (shift_length c - shift(dimindex(:'a))))) ==>
 ∃ll.
 evaluate (StoreAnyConsts r1 r2 r3 vs w,s) =
 (NONE,s with <|memory:=m1;locals:=ll;
    store:=s.store |+ (NextFree,Word(free+bytes_in_word*n2w(LENGTH vs)))|>) ∧
 lookup r1 ll = SOME (const_word c a w) ∧
 ∀n. ~MEM n [r1;r2;r3] ==> lookup n ll = lookup n s.locals
Proof

 rpt gen_tac >> PairCases_on `w` >> strip_tac >>
 drule store_list_word_cond_add_IMP >> strip_tac >>
 Cases_on `vs` >> Cases_on `w0` >>
 gvs[StoreAnyConsts_def,wordSemTheory.evaluate_def,wordSemTheory.word_exp_def,
   wordSemTheory.set_store_def,wordSemTheory.get_var_def,const_word_def,word_cond_add_def,
   wordSemTheory.the_words_def,wordSemTheory.word_op_def,wordSemTheory.set_var_def,
   wordSemTheory.unset_var_def,wordSemTheory.state_component_equality,
   lookup_insert,lookup_delete,store_list_def,integer_wordTheory.i2w_pos] >>
 rw[] >> ntac 10 (simp[Once insert_swap,insert_shadow])
QED

Theorem do_build_const_IMP_SOME:
  do_build_const parts x (SOME ts) = (v,vs,ts1) ⇒
  ∃ts2. ts1 = SOME ts2
Proof
  fs [do_build_const_def]
  \\ qmatch_goalsub_rename_tac ‘do_build m k _ _ _ = (x1,x2,x3)’
  \\ EVERY (map qid_spec_tac [‘x3’,‘x2’,‘x1’,‘ts’,‘x’,‘parts’,‘k’,‘m’])
  \\ Induct_on ‘parts’ \\ fs [do_build_def]
  \\ rw [] \\ pairarg_tac \\ fs []
  \\ qsuff_tac ‘∃ttt. ts1 = SOME ttt’
  THEN1 (rw [] \\ gvs [] \\ res_tac \\ fs [])
  \\ Cases_on ‘h’ \\ gvs [do_part_def,AllCaseEqs()]
QED

Theorem TWO_POW_LEMMA[local]:
  (2 ** n ≤ 3 ⇒ n < 2) ∧
  (2 ** n ≤ 2 ⇒ n < 2) ∧
  (2 ** n ≤ 1 ⇒ n < 1)
Proof
  Cases_on ‘n’ \\ fs [EXP]
  \\ rename [‘SUC n'’]
  \\ Cases_on ‘n'’ \\ fs [EXP]
  \\ ‘0 < 2 ** n’ by fs [bitTheory.ZERO_LT_TWOEXP]
  \\ decide_tac
QED

Theorem bignum_size:
  good_dimindex (:'a) ⇒
  bignum_size (dimindex (:α) = 64) i = LENGTH (n2mw (Num (ABS i)) :'a word list) + 1
Proof
  fs [bignum_size_def]
  \\ rename [‘n2mw n’]
  \\ qid_spec_tac ‘n’
  \\ ho_match_mp_tac multiwordTheory.n2mw_ind \\ rw [] \\ fs []
  \\ once_rewrite_tac [multiwordTheory.n2mw_def,bignum_digits_def]
  \\ IF_CASES_TAC \\ fs []
  \\ gvs [good_dimindex_def,dimword_def]
QED

val _ = Parse.hide "free";

Theorem parts_to_words_NONE[local]:
  ∀parts (off:int) m aa (t:('a,'c,'ffi) wordSem$state) (s:('c,'ffi) dataSem$state).
    parts_to_words c m aa parts off = NONE ∧ good_dimindex (:'a) ∧
    heap_in_memory_store heap a sp sp1 gens c t.store t.memory t.mdomain limit ⇒
    limits_inv s.limits (FLOOKUP t.store HeapLength) t.stack_limit
               c.len_size c.has_fp_ops c.has_fp_tern ⇒
    EXISTS ($¬ ∘ lim_safe_part s.limits) parts
Proof[exclude_simps = EXP_LE_LOG_SIMP EXP_LT_LOG_SIMP LE_EXP_LOG_SIMP LT_EXP_LOG_SIMP LOG_NUMERAL EXP_LT_1 ONE_LE_EXP TWO_LE_EXP]
  suspend "initial"
QED

Resume parts_to_words_NONE[initial]:
  Induct
  >- fs [parts_to_words_def,AllCaseEqs(),PULL_EXISTS]
  \\ suspend "step"
QED

Resume parts_to_words_NONE[step]:
  fs [parts_to_words_def,AllCaseEqs(),PULL_EXISTS]
  \\ rpt gen_tac
  \\ reverse (Cases_on ‘part_to_words c m h off’)
  THEN1 (gvs [] \\ rw [] \\ res_tac \\ fs [])
  \\ fs [] \\ disch_tac
  \\ simp [limits_inv_def] \\ strip_tac
  \\ `arch_width_bits c.arch_width = dimindex (:α)` by fs [heap_in_memory_store_def]
  \\ disj1_tac \\ strip_tac
  \\ Cases_on ‘∃n l. h = Con n l’
  THEN1 (suspend "con")
  \\ Cases_on ‘∃i. h = Int i’
  THEN1 (suspend "int")
  \\ suspend "other"
QED

Resume parts_to_words_NONE[con]:
  gvs [part_to_words_def,arch_size_def,CaseEq "bool"]
  \\ Cases_on ‘l’
  \\ gvs [good_dimindex_def,dimword_def,encode_header_def]
  \\ fs [heap_in_memory_store_def]
QED

Resume parts_to_words_NONE[int]:
  gvs []
  \\ full_simp_tac std_ss [part_to_words_def,GEN_ALL compiler_i2mw_words,arch_size_def]
  \\ gvs [AllCaseEqs(),multiwordTheory.i2mw_def,encode_header_def]
  THEN1
   (fs [heap_in_memory_store_def,good_dimindex_def]
    \\ Cases_on `i < 0` \\ fs []
    \\ `7 < 2 ** (dimindex (:'a) - (c.len_size + 2))` by
         (match_mp_tac LESS_TRANS \\ qexists_tac `2 ** 4`
          \\ simp [EXP_BASE_LT_MONO] \\ decide_tac)
    \\ `3 < 2 ** (dimindex (:'a) - (c.len_size + 2))` by decide_tac
    \\ gvs [] \\ decide_tac)
  THEN1
   (qpat_x_assum ‘~(n < m:num)’ mp_tac
    \\ Cases_on ‘i < 0’ \\ gvs [good_dimindex_def,dimword_def]
    \\ fs [heap_in_memory_store_def]
    \\ ntac 10 (fs [dimword_def] \\ EVAL_TAC))
  \\ fs [heap_in_memory_store_def]
  \\ gvs [bignum_size]
  \\ qsuff_tac ‘2 ** c.len_size ≤ 2 ** (dimindex (:α) − 4)’
  THEN1 decide_tac
  \\ fs [heap_in_memory_store_def]
QED

Resume parts_to_words_NONE[other]:
  Cases_on ‘h’ \\ gvs [part_to_words_def,arch_size_def]
  \\ gvs [good_dimindex_def,dimword_def,byte_len_def,encode_header_def,
          AllCaseEqs(),NOT_LESS]
  \\ imp_res_tac TWO_POW_LEMMA
  \\ fs [heap_in_memory_store_def,encode_header_def,AllCaseEqs()]
QED

Finalise parts_to_words_NONE[local];

Theorem assign_Build:
   (∃parts. op = BlockOp (Build parts)) ==> ^assign_thm_goal
Proof[exclude_simps = EXP_LE_LOG_SIMP EXP_LT_LOG_SIMP LE_EXP_LOG_SIMP LT_EXP_LOG_SIMP LOG_NUMERAL EXP_LT_1 ONE_LE_EXP TWO_LE_EXP]
  rpt strip_tac \\ imp_res_tac state_rel_arch_width \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t NONE locs` kall_tac \\ strip_tac
  \\ Cases_on `FST (assign c n l dest (BlockOp (Build parts)) args names_opt) = GiveUp`
  THEN1
   (asm_rewrite_tac [] >> fs [] >>
    fs[state_rel_def] >>
    conj_tac >- metis_tac[backendPropsTheory.option_le_trans,
                          do_app_stack_max,option_le_max_right] >>
    pop_assum mp_tac >>
    `x.limits = s.limits` by
      (Cases_on `names_opt` \\ gvs [cut_state_opt_def,cut_state_def,AllCaseEqs()]) >>
    simp [assign_def]
    \\ reverse (Cases_on `const_parts_to_words c parts`)
    THEN1 (fs [] \\ PairCases_on `x'` \\ fs [] \\ EVAL_TAC) \\ fs []
    \\ qsuff_tac `EXISTS ($¬ ∘ lim_safe_part s.limits) parts`
    THEN1 (strip_tac \\ gvs[do_app,CaseEq"bool",CaseEq"option",AllCaseEqs()] >>
           imp_res_tac get_vars_IMP_LENGTH >>
           rveq >> fs[arch_size_def,limits_inv_def,good_dimindex_def] >>
           gvs [consume_space_def,AllCaseEqs()])
    \\ fs [const_parts_to_words_def]
    \\ drule_all parts_to_words_NONE \\ rewrite_tac [])
  \\ gvs [assign_def]
  \\ fs [] \\ Cases_on `const_parts_to_words c parts` THEN1 fs []
  \\ rename [`_ = SOME y`]
  \\ PairCases_on `y` \\ fs []
  \\ qpat_x_assum `_ ≠ _` kall_tac
  \\ qexists_tac `NONE` \\ fs []
  \\ `∃free curr.
        FLOOKUP t.store NextFree = SOME (Word free) ∧
        FLOOKUP t.store CurrHeap = SOME (Word curr) ∧
        good_dimindex (:'a) ∧ shift_length c < dimindex (:α)` by
          fs [state_rel_thm,memory_rel_def,heap_in_memory_store_def]
  \\ `(shift_length c − shift (dimindex (:α))) MOD dimword (:α)
      = shift_length c − shift (dimindex (:α))` by fs [good_dimindex_def, dimword_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,wordSemTheory.word_exp_def,wordSemTheory.set_var_def,
         wordSemTheory.get_store_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,wordSemTheory.word_exp_def,wordSemTheory.set_var_def,
         wordSemTheory.the_words_def,wordSemTheory.word_op_def,wordSemTheory.word_sh_def,
         wordSemTheory.get_var_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ qpat_x_assum `state_rel c l1 l2 x t NONE locs` mp_tac
  \\ simp [Once state_rel_thm] \\ strip_tac
  \\ Cases_on `x.tstamps` \\ gvs [get_var_def,wordSemTheory.get_store_def]
  \\ rename [`x.tstamps = SOME ts`]
  \\ fs [do_app]
  \\ qabbrev_tac `x3 = if SUM (MAP part_space_req parts) = 0 then SOME x
                       else consume_space (SUM (MAP part_space_req parts)) x`
  \\ `x3 = consume_space (SUM (MAP part_space_req parts)) x` by
   (unabbrev_all_tac \\ rw []
    \\ fs [consume_space_def,dataSemTheory.state_component_equality])
  \\ fs []
  \\ pop_assum kall_tac
  \\ pop_assum kall_tac
  \\ gvs [AllCaseEqs(),consume_space_def]
  \\ imp_res_tac do_build_const_IMP_SOME \\ gvs []
  \\ imp_res_tac const_parts_to_words_LENGTH
  \\ drule_at_then (Pos (el 2)) (drule_at (Pos (el 2))) memory_rel_do_build_const
  \\ fs [] \\ strip_tac
  \\ fs [allowed_op_def]
  \\ qmatch_goalsub_abbrev_tac `wordSem$evaluate (_,s1)`
  \\ `t.memory = s1.memory ∧ t.mdomain = s1.mdomain` by fs [Abbr`s1`]
  \\ fs []
  \\ drule evaluate_StoreAnyConsts
  \\ disch_then (qspecl_then [`adjust_var dest`,`1`,`3`,`(y0,y1)`,`s1`] mp_tac)
  \\ impl_tac THEN1 rgs [Abbr`s1`,lookup_insert]
  \\ strip_tac \\ fs []
  \\ fs [state_rel_thm,dataSemTheory.set_var_def,lookup_insert,lookup_delete,Abbr`s1`,
         FLOOKUP_UPDATE,FAPPLY_FUPDATE_THM,adjust_var_11,option_le_max_right]
  \\ conj_tac THEN1
   (rw [] \\ res_tac
    \\ first_x_assum (qspec_then `adjust_var n` mp_tac)
    \\ fs [adjust_var_11])
  \\ `(inter ll (adjust_set (insert dest v x.locals))) =
      (inter (insert (adjust_var dest) (const_word c (-1w * curr + free) (y0,y1)) t.locals)
            (adjust_set (insert dest v x.locals)))` by
   (fs [lookup_inter_alt] \\ rw [] \\ rw [lookup_insert]
    \\ first_x_assum irule
    \\ CCONTR_TAC \\ gvs []
    \\ imp_res_tac domain_adjust_set_EVEN \\ fs [])
  \\ simp []
  \\ gvs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert
  \\ fs[inter_insert_ODD_adjust_set_alt,inter_delete_ODD_adjust_set_alt]
  \\ irule memory_rel_less_space
  \\ qexists_tac `x.space − LENGTH y2` \\ fs []
QED

Theorem join_lemma[local] =
  METIS_PROVE [] “(b1 ⇒ x) ∧ (b2 ⇒ x) ⇒ (b1 ∨ b2 ⇒ x)”;

Theorem imp_assign[local] =
  DB.match ["-"] “_ ==> ^assign_thm_goal” |> map (#1 o #2)
  |> end_itlist (fn x => fn y => MATCH_MP join_lemma (CONJ x y));

Theorem assign_BlockOp:
  (∃b. op = BlockOp b) ∧ op ≠ BlockOp PtrEqual ⇒ ^assign_thm_goal
Proof
  strip_tac \\ strip_tac
  \\ irule imp_assign
  \\ asm_rewrite_tac []
  \\ rpt $ first_assum $ irule_at Any
  \\ gvs [] \\ Cases_on ‘b’ \\ gvs []
  \\ qhdtm_x_assum`do_app`mp_tac \\ EVAL_TAC
QED

