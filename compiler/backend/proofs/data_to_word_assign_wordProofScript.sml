(*
  Part of the correctness proof for data_to_word: assign for WordOp
*)
Theory data_to_word_assign_wordProof
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
val shift_def = backend_commonTheory.word_shift_def
val Smallnum_def = LIST_CONJ [data_to_word_memoryProofTheory.Smallnum_def,
                             data_to_wordTheory.Smallnum_def];
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

val _ = augment_srw_ss [rewrites [arch_bytes_word]];
val eval_tac = imp_res_tac state_rel_arch_width
  \\ imp_res_tac memory_rel_arch_width \\ eval_tac
  \\ fs [GSYM word_mul_n2w];

val get_var_get_real_addr_lemma =
    GEN_ALL(CONV_RULE(LAND_CONV(move_conj_left(
                                   same_const``wordSem$get_var`` o #1 o
                                   strip_comb o lhs)))
                     get_real_addr_lemma)

Theorem evaluate_LoadWord64:
   memory_rel c be ts refs sp t.store t.memory t.mdomain ((Word64 w,v)::vars) ∧
   shift_length c < dimindex(:α) ∧ dimindex(:α) = 64 ∧
   get_var src (t:('a,'c,'ffi) state) = SOME v
   ==>
   evaluate (LoadWord64 c dest src,t) = (NONE, set_var dest (Word (w2w w)) t)
Proof
  rw[LoadWord64_def] \\ eval_tac
  \\ rpt_drule0 memory_rel_Word64_IMP
  \\ impl_keep_tac >- fs[good_dimindex_def]
  \\ strip_tac \\ rfs[] \\ clean_tac
  \\ gvs [GSYM wordSemTheory.get_var_def]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ simp[] \\ disch_then drule0
  \\ simp[] \\ rw[]
  \\ rpt(AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ simp[FUN_EQ_THM]
  \\ rw[WORD_w2w_EXTRACT]
QED

Theorem evaluate_WriteWord64:
   memory_rel c be ts refs sp t.store t.memory t.mdomain
     (join_env_locals sl t.locals ++ vars) ∧
   get_var src (t:('a,'c,'ffi) state) = SOME (Word w) ∧
   shift_length c < dimindex(:α) ∧
   src ≠ 1 ∧ 1 < sp ∧
   dimindex(:α) = 64 ∧
   encode_header c 3 1 = SOME header ∧
   (∀n. IS_SOME (lookup n sl) ⇒ IS_SOME (lookup (adjust_var n) t.locals))
   ==>
   ∃nf m' locals' v.
     evaluate (WriteWord64 c header dest src,t) =
       (NONE, t with <| store := t.store |+ (NextFree, nf);
                        memory := m'; locals := locals'|>) ∧
     memory_rel c be ts refs (sp-2) (t.store |+ (NextFree, nf)) m' t.mdomain
       (join_env_locals (insert dest (Word64 (w2w w)) sl) locals' ++ vars) ∧
     (∀n. IS_SOME (lookup n sl) ⇒ IS_SOME (lookup (adjust_var n) locals')) ∧
     IS_SOME (lookup (adjust_var dest) locals') ∧
     lookup 0 locals' = lookup 0 t.locals
Proof
  rw[WriteWord64_def,list_Seq_def,join_env_locals_def]
  \\ drule0(GEN_ALL(memory_rel_Word64_alt |> Q.GEN`vs` |> Q.SPEC`[]` |> SIMP_RULE (srw_ss())[]))
  \\ disch_then(qspecl_then[`[Word w]`,`w2w w`]mp_tac)
  \\ simp[]
  \\ impl_tac >- (
    simp[good_dimindex_def] \\ EVAL_TAC \\ simp[WORD_w2w_EXTRACT]
    \\ srw_tac[wordsLib.WORD_BIT_EQ_ss][] )
  \\ strip_tac
  \\ `shift_length c − shift (dimindex (:'a)) < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword \\ decide_tac)
  \\ fs [shift_def]
  \\ eval_tac
  \\ fs[wordSemTheory.get_var_def,
        wordSemTheory.mem_store_def,
        lookup_insert,
        wordSemTheory.set_store_def,
        FLOOKUP_UPDATE,
        store_list_def]
  \\ simp[wordSemTheory.state_component_equality,lookup_insert]
  \\ qmatch_goalsub_abbrev_tac`(NextFree,next_free)`
  \\ qexists_tac`next_free` \\ simp[]
  \\ reverse conj_tac
  >- ( rw[] \\ fs[FLOOKUP_DEF,EXTENSION] \\ metis_tac[] )
  \\ full_simp_tac std_ss [APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert
  \\ fs[inter_insert_ODD_adjust_set_alt]
  \\ rw[] \\ fs[make_ptr_def,shift_def] \\ rfs[]
  \\ qmatch_abbrev_tac`memory_rel c be ts refs sp' st' m' md vars'`
  \\ qmatch_assum_abbrev_tac`memory_rel c be ts refs sp' st' m'' md vars'`
  \\ `m' = m''` suffices_by simp[]
  \\ simp[Abbr`m'`,Abbr`m''`,FUN_EQ_THM,APPLY_UPDATE_THM]
  \\ rw[] \\ fs[]
  \\ fs [addressTheory.WORD_EQ_ADD_CANCEL]
  \\ pop_assum mp_tac \\ EVAL_TAC
  \\ fs [dimword_def]
QED

Theorem evaluate_WriteWord64_on_32:
   memory_rel c be ts refs sp t.store t.memory t.mdomain
     (join_env_locals sl t.locals ++ vars) ∧
   get_var src1 (t:('a,'c,'ffi) state) = SOME (Word ((31 >< 0) w)) ∧
   get_var src2 (t:('a,'c,'ffi) state) = SOME (Word ((63 >< 32) w)) ∧
   shift_length c < dimindex(:α) ∧
   src1 ≠ 1 ∧ src2 ≠ 1 ∧ 2 < sp ∧
   dimindex(:α) = 32 ∧
   encode_header c 3 2 = SOME header ∧
   (∀n. IS_SOME (lookup n sl) ⇒ IS_SOME (lookup (adjust_var n) t.locals))
   ==>
   ∃nf m' locals' v.
     evaluate (WriteWord64_on_32 c header dest src1 src2,t) =
       (NONE, t with <| store := t.store |+ (NextFree, nf);
                        memory := m'; locals := locals'|>) ∧
     memory_rel c be ts refs (sp-3) (t.store |+ (NextFree, nf)) m' t.mdomain
       (join_env_locals (insert dest (Word64 w) sl) locals' ++ vars) ∧
     (∀n. IS_SOME (lookup n sl) ⇒ IS_SOME (lookup (adjust_var n) locals')) ∧
     IS_SOME (lookup (adjust_var dest) locals') ∧
     lookup 0 locals' = lookup 0 t.locals
Proof
  qpat_abbrev_tac `w1 = ((31 >< 0) w):'a word`
  \\ qpat_abbrev_tac `w2 = ((63 >< 32) w):'a word`
  \\ rw[WriteWord64_on_32_def,list_Seq_def,join_env_locals_def]
  \\ drule0(GEN_ALL(memory_rel_Word64_alt |> Q.GEN`vs` |> Q.SPEC`[]` |> SIMP_RULE (srw_ss())[]))
  \\ disch_then(qspecl_then[`[Word w2;Word w1]`,`w`]mp_tac)
  \\ asm_rewrite_tac[Word64Rep_def]
  \\ simp_tac (srw_ss()) []
  \\ disch_then (qspec_then `header` mp_tac)
  \\ impl_tac >- (
    unabbrev_all_tac \\ fs []
    \\ simp[good_dimindex_def] \\ EVAL_TAC \\ simp[WORD_w2w_EXTRACT]
    \\ srw_tac[wordsLib.WORD_BIT_EQ_ss][])
  \\ strip_tac
  \\ `shift_length c − shift (dimindex (:'a)) < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword \\ decide_tac)
  \\ fs [shift_def]
  \\ eval_tac
  \\ fs[wordSemTheory.get_var_def,
        wordSemTheory.mem_store_def,
        lookup_insert,
        wordSemTheory.set_store_def,
        FLOOKUP_UPDATE,
        store_list_def]
  \\ simp[wordSemTheory.state_component_equality,lookup_insert]
  \\ qmatch_goalsub_abbrev_tac`(NextFree,next_free)`
  \\ qexists_tac`next_free` \\ simp[]
  \\ reverse conj_tac
  >- ( rw[] \\ fs[FLOOKUP_DEF,EXTENSION] \\ metis_tac[] )
  \\ rveq \\ fs []
  \\ full_simp_tac std_ss [APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert
  \\ fs[inter_insert_ODD_adjust_set_alt]
  \\ rw[] \\ fs[make_ptr_def,shift_def] \\ rfs[]
  \\ qmatch_abbrev_tac`memory_rel c be ts refs sp' st' m' md vars'`
  \\ qmatch_assum_abbrev_tac`memory_rel c be ts refs sp' st' m'' md vars'`
  \\ `m' = m''` suffices_by simp[]
  \\ simp[Abbr`m'`,Abbr`m''`,FUN_EQ_THM,APPLY_UPDATE_THM]
  \\ rw[] \\ fs[]
  \\ fs [addressTheory.WORD_EQ_ADD_CANCEL]
  \\ pop_assum mp_tac \\ EVAL_TAC \\ fs [dimword_def]
  \\ pop_assum mp_tac \\ EVAL_TAC \\ fs [dimword_def]
QED

Theorem Num_ABS_AND[local]:
    Num (ABS (& n)) = n /\ Num (ABS (- & n)) = n
Proof
  intLib.COOPER_TAC
QED

Theorem evaluate_WriteWord64_on_32_num:
   memory_rel c be ts refs sp t.store t.memory t.mdomain
     (join_env_locals sl t.locals ++ vars) ∧
   get_var src1 (t:('a,'c,'ffi) state) = SOME (Word w1) ∧
   get_var src2 (t:('a,'c,'ffi) state) = SOME (Word w2) ∧
   shift_length c < dimindex(:α) ∧ w2 <> 0w /\
   src1 ≠ 1 ∧ src2 ≠ 1 ∧ 2 < sp ∧
   dimindex(:α) = 32 ∧
   encode_header c 3 2 = SOME header ∧
   (∀n. IS_SOME (lookup n sl) ⇒ IS_SOME (lookup (adjust_var n) t.locals))
   ==>
   ∃nf m' locals' v.
     evaluate (WriteWord64_on_32 c header dest src2 src1,t) =
       (NONE, t with <| store := t.store |+ (NextFree, nf);
                        memory := m'; locals := locals'|>) ∧
     memory_rel c be ts refs (sp-3) (t.store |+ (NextFree, nf)) m' t.mdomain
       (join_env_locals (insert dest (Number (&(w2n w2 * dimword (:'a) + w2n w1))) sl) locals' ++ vars) ∧
     (∀n. IS_SOME (lookup n sl) ⇒ IS_SOME (lookup (adjust_var n) locals')) ∧
     IS_SOME (lookup (adjust_var dest) locals') ∧
     lookup 0 locals' = lookup 0 t.locals
Proof
  rw[WriteWord64_on_32_def,list_Seq_def,join_env_locals_def]
  \\ drule0(GEN_ALL(IMP_memory_rel_bignum_alt))
  \\ disch_then(qspecl_then[`[w1;w2]`,`F`,
        `&(w2n w2 * dimword (:'a) + w2n w1)`,`header`]mp_tac)
  \\ simp[]
  \\ impl_tac >- (
    simp[good_dimindex_def]
    \\ conj_tac
    THEN1 (Cases_on `w2` \\ fs [small_int_def,dimword_def])
    \\ conj_tac
    >- (
      rw[Bignum_def]
      \\ fs[multiwordTheory.i2mw_def,Num_ABS_AND]
      \\ once_rewrite_tac [multiwordTheory.n2mw_def]
      \\ Cases_on `w2` \\ fs []
      \\ once_rewrite_tac [multiwordTheory.n2mw_def]
      \\ `(w2n w1 + n * dimword (:α)) DIV dimword (:α) = n` by
       (once_rewrite_tac [ADD_COMM]
        \\ match_mp_tac DIV_MULT \\ fs [w2n_lt])
      \\ fs []
      \\ `n DIV dimword (:α) = 0` by rfs [DIV_EQ_0,dimword_def]
      \\ once_rewrite_tac [multiwordTheory.n2mw_def] \\ fs []
      \\ fs [w2n_lt])
    \\ CONV_TAC(PATH_CONV"lrlr"EVAL)
    \\ simp[dimword_def])
  \\ strip_tac
  \\ `shift_length c − shift (dimindex (:'a)) < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword \\ decide_tac)
  \\ fs [shift_def]
  \\ eval_tac
  \\ fs[wordSemTheory.get_var_def,
        wordSemTheory.mem_store_def,
        lookup_insert,
        wordSemTheory.set_store_def,
        FLOOKUP_UPDATE,
        store_list_def]
  \\ simp[wordSemTheory.state_component_equality,lookup_insert]
  \\ qmatch_goalsub_abbrev_tac`(NextFree,next_free)`
  \\ qexists_tac`next_free` \\ simp[]
  \\ reverse conj_tac
  >- ( rw[] \\ fs[FLOOKUP_DEF,EXTENSION] \\ metis_tac[] )
  \\ full_simp_tac std_ss [APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert
  \\ fs[inter_insert_ODD_adjust_set_alt]
  \\ rw[] \\ fs[make_ptr_def,shift_def] \\ rfs[]
  \\ qmatch_abbrev_tac`memory_rel c be ts refs sp' st' m' md vars'`
  \\ qmatch_assum_abbrev_tac`memory_rel c be ts refs sp' st' m'' md vars'`
  \\ `m' = m''` suffices_by simp[]
  \\ simp[Abbr`m'`,Abbr`m''`,FUN_EQ_THM,APPLY_UPDATE_THM]
  \\ rw[] \\ fs[]
  \\ fs [addressTheory.WORD_EQ_ADD_CANCEL]
  \\ pop_assum mp_tac \\ EVAL_TAC
  \\ fs [dimword_def]
  \\ rfs [bytes_in_word_def,dimword_def]
QED

Theorem evaluate_WriteWord32_bignum:
   memory_rel c be ts refs sp t.store t.memory t.mdomain
     (join_env_locals sl t.locals ++ vars) ∧
   get_var src (t:('a,'c,'ffi) state) = SOME (Word w) ∧
   shift_length c < dimindex(:α) ∧
   src ≠ 1 ∧ 1 < sp ∧
   dimindex(:α) = 32 ∧
   encode_header c 3 1 = SOME header ∧
   ¬small_int (dimindex (:α)) (&w2n w) ∧
   (∀n. IS_SOME (lookup n sl) ⇒ IS_SOME (lookup (adjust_var n) t.locals))
   ==>
   ∃nf m' locals' v.
     evaluate (WriteWord32_on_32 c header dest src,t) = (NONE, t with
       <| store := t.store |+ (NextFree, nf); memory := m'; locals := locals'|>) ∧
     memory_rel c be ts refs (sp-2) (t.store |+ (NextFree, nf)) m' t.mdomain
       (join_env_locals (insert dest (Number (&w2n w)) sl) locals' ++ vars) ∧
     (∀n. IS_SOME (lookup n sl) ⇒ IS_SOME (lookup (adjust_var n) locals')) ∧
     IS_SOME (lookup (adjust_var dest) locals') ∧
     lookup 0 locals' = lookup 0 t.locals
Proof
  rw[WriteWord32_on_32_def,list_Seq_def,join_env_locals_def]
  \\ drule0(GEN_ALL(IMP_memory_rel_bignum_alt))
  \\ disch_then(qspecl_then[`[w]`,`F`,`&w2n w`,`header`]mp_tac)
  \\ simp[]
  \\ impl_tac >- (
    simp[good_dimindex_def]
    \\ conj_tac
    >- (
      rw[Bignum_def]
      \\ fs[multiwordTheory.i2mw_def]
      \\ simp[n2mw_w2n]
      \\ IF_CASES_TAC \\ fs[]
      \\ fs[small_int_def]
      \\ rfs[dimword_def] )
    \\ CONV_TAC(PATH_CONV"lrlr"EVAL)
    \\ simp[dimword_def])
  \\ strip_tac
  \\ `shift_length c − shift (dimindex (:'a)) < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword \\ decide_tac)
  \\ fs [shift_def]
  \\ eval_tac
  \\ fs[wordSemTheory.get_var_def,
        wordSemTheory.mem_store_def,
        lookup_insert,
        wordSemTheory.set_store_def,
        FLOOKUP_UPDATE,
        store_list_def]
  \\ simp[wordSemTheory.state_component_equality,lookup_insert]
  \\ qmatch_goalsub_abbrev_tac`(NextFree,next_free)`
  \\ qexists_tac`next_free` \\ simp[]
  \\ reverse conj_tac
  >- ( rw[] \\ fs[FLOOKUP_DEF,EXTENSION] \\ metis_tac[] )
  \\ full_simp_tac std_ss [APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert
  \\ fs[inter_insert_ODD_adjust_set_alt]
  \\ rw[] \\ fs[make_ptr_def,shift_def] \\ rfs[]
  \\ qmatch_abbrev_tac`memory_rel c be ts refs sp' st' m' md vars'`
  \\ qmatch_assum_abbrev_tac`memory_rel c be ts refs sp' st' m'' md vars'`
  \\ `m' = m''` suffices_by simp[]
  \\ simp[Abbr`m'`,Abbr`m''`,FUN_EQ_THM,APPLY_UPDATE_THM]
  \\ rw[] \\ fs[]
  \\ fs [addressTheory.WORD_EQ_ADD_CANCEL]
  \\ pop_assum mp_tac \\ EVAL_TAC
  \\ fs [dimword_def]
QED

Theorem evaluate_WriteWord64_bignum:
   memory_rel c be ts refs sp t.store t.memory t.mdomain
     (join_env_locals sl t.locals ++ vars) ∧
   get_var src (t:('a,'c,'ffi) state) = SOME (Word w) ∧
   shift_length c < dimindex(:α) ∧
   src ≠ 1 ∧ 1 < sp ∧
   dimindex(:α) = 64 ∧
   encode_header c 3 1 = SOME header ∧
   ¬small_int (dimindex (:α)) (&w2n w) ∧
   (∀n. IS_SOME (lookup n sl) ⇒ IS_SOME (lookup (adjust_var n) t.locals))
   ==>
   ∃nf m' locals' v.
     evaluate (WriteWord64 c header dest src,t) = (NONE, t with
       <| store := t.store |+ (NextFree, nf); memory := m'; locals := locals'|>) ∧
     memory_rel c be ts refs (sp-2) (t.store |+ (NextFree, nf)) m' t.mdomain
       (join_env_locals (insert dest (Number (&w2n w)) sl) locals' ++ vars) ∧
     (∀n. IS_SOME (lookup n sl) ⇒ IS_SOME (lookup (adjust_var n) locals')) ∧
     IS_SOME (lookup (adjust_var dest) locals') ∧
     lookup 0 locals' = lookup 0 t.locals
Proof
  rw[WriteWord64_def,list_Seq_def,join_env_locals_def]
  \\ drule0(GEN_ALL(IMP_memory_rel_bignum_alt))
  \\ disch_then(qspecl_then[`[w]`,`F`,`&w2n w`,`header`]mp_tac)
  \\ simp[]
  \\ impl_tac >- (
    simp[good_dimindex_def]
    \\ conj_tac
    >- (
      rw[Bignum_def]
      \\ fs[multiwordTheory.i2mw_def]
      \\ simp[n2mw_w2n]
      \\ IF_CASES_TAC \\ fs[]
      \\ fs[small_int_def]
      \\ rfs[dimword_def] )
    \\ CONV_TAC(PATH_CONV"lrlr"EVAL)
    \\ simp[dimword_def])
  \\ strip_tac
  \\ `shift_length c − shift (dimindex (:'a)) < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword \\ decide_tac)
  \\ fs [shift_def]
  \\ eval_tac
  \\ fs[wordSemTheory.get_var_def,
        wordSemTheory.mem_store_def,
        lookup_insert,
        wordSemTheory.set_store_def,
        FLOOKUP_UPDATE,
        store_list_def]
  \\ simp[wordSemTheory.state_component_equality,lookup_insert]
  \\ qmatch_goalsub_abbrev_tac`(NextFree,next_free)`
  \\ qexists_tac`next_free` \\ simp[]
  \\ reverse conj_tac
  >- ( rw[] \\ fs[FLOOKUP_DEF,EXTENSION] \\ metis_tac[] )
  \\ full_simp_tac std_ss [APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert
  \\ fs[inter_insert_ODD_adjust_set_alt]
  \\ rw[] \\ fs[make_ptr_def,shift_def] \\ rfs[]
  \\ qmatch_abbrev_tac`memory_rel c be ts refs sp' st' m' md vars'`
  \\ qmatch_assum_abbrev_tac`memory_rel c be ts refs sp' st' m'' md vars'`
  \\ `m' = m''` suffices_by simp[]
  \\ simp[Abbr`m'`,Abbr`m''`,FUN_EQ_THM,APPLY_UPDATE_THM]
  \\ rw[] \\ fs[]
  \\ fs [addressTheory.WORD_EQ_ADD_CANCEL]
  \\ pop_assum mp_tac \\ EVAL_TAC
  \\ fs [dimword_def]
QED

Theorem evaluate_LoadBignum:
   memory_rel c be ts refs sp t.store t.memory t.mdomain ((Number i,v)::vars) ∧
   ¬small_int (dimindex (:α)) i ∧ good_dimindex (:α) ∧ shift_length c < dimindex (:α) ∧
   get_var src (t:(α,'c,'ffi) state) = SOME v ∧ header ≠ w1
   ⇒
   ∃h junk.
   evaluate (LoadBignum c header w1 src,t) =
     (NONE, set_vars [w1;header;w1]
                     [Word (n2w (Num (ABS i)));(Word h);junk] t) ∧
   ((16w && h) = 0w ⇔ 0 ≤ i)
Proof
  rw[LoadBignum_def,list_Seq_def] \\ eval_tac
  \\ rpt_drule0 memory_rel_Number_bignum_IMP
  \\ strip_tac \\ rfs[] \\ clean_tac
  \\ gvs [GSYM wordSemTheory.get_var_def]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ simp[lookup_insert,wordSemTheory.get_var_def]
  \\ simp[wordSemTheory.set_vars_def,wordSemTheory.state_component_equality,alist_insert_def]
  \\ rw[] \\ metis_tac[]
QED

val evaluate_Assign =
  SIMP_CONV(srw_ss())[wordSemTheory.evaluate_def]``evaluate (Assign _ _, _)``

Theorem consume_space_stack_max:
  consume_space a x = SOME s ⇒ x.stack_max = s.stack_max
Proof
  rw[consume_space_def]>>
  simp[]
QED

val _=augment_srw_ss[rewrites[i2w_int_or,i2w_mod_pow2,compiler_ptr_bits_i2w]];

val _ = augment_srw_ss [rewrites [arch_width_eq32, arch_bytes_scaled_word]];

Theorem assign_WordFromWord:
   (?b. op = WordOp (WordFromWord b)) ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac
  \\ imp_res_tac state_rel_arch_width
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ Cases_on `b`
  THEN1
   (fs[do_app,oneline do_word_app_def,case_eq_thms,allowed_op_def]
    \\ every_case_tac \\ fs[]
    \\ clean_tac
    \\ drule state_rel_get_vars_IMP
    \\ disch_then drule
    \\ imp_res_tac state_rel_get_vars_IMP
    \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
    \\ fs[state_rel_thm] \\ eval_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ strip_tac
    \\ fs[wordSemTheory.get_vars_def,case_eq_thms]
    \\ every_case_tac \\ fs[] \\ clean_tac
    \\ fs[assign_def,good_dimindex_def]
    \\ rpt_drule0 memory_rel_Word64_IMP \\ fs [good_dimindex_def]
    \\ strip_tac
    \\ fs [list_Seq_def,eq_eval]
    \\ rpt_drule0 (get_var_get_real_addr_lemma
          |> SIMP_RULE std_ss [wordSemTheory.get_var_def,good_dimindex_def])
    \\ disch_then kall_tac
    \\ rfs [good_dimindex_def] \\ rfs [WORD_MUL_LSL]
    \\ simp [Once word_exp_ShiftVar_bits] \\ fs [eq_eval]
    \\ fs [adjust_var_11]
    \\ TRY (conj_tac THEN1 rw [])
    \\ simp[inter_insert_ODD_adjust_set]
    \\ simp[option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert
    \\ fs []
    \\ qmatch_goalsub_abbrev_tac`Number i,Word sn`
    \\ (qsuff_tac `sn = Smallnum i /\ small_int (dimindex (:'a)) i`
       >-(rw [] \\ fs []
            \\ match_mp_tac IMP_memory_rel_Number  \\ fs [good_dimindex_def]))
    \\ unabbrev_all_tac
    \\ irule_at (Pos (el 2))small_int_w2n
    \\ fs [good_dimindex_def,dimword_def,w2w_def,Smallnum_def]
    \\ Cases_on `c'` \\ fs [word_extract_n2w]
    \\ rewrite_tac [LSL_BITWISE]
    \\ rewrite_tac [WORD_AND_EXP_SUB1 |> Q.SPEC `8` |> SIMP_RULE (srw_ss()) []]
    \\ fs [WORD_MUL_LSL,word_mul_n2w,dimword_def]
    \\ fs [bitTheory.BITS_THM]
    \\ rw [] \\ rewrite_tac [GSYM (EVAL ``256n * 16777216``)]
    \\ rewrite_tac [MATCH_MP MOD_MULT_MOD (DECIDE ``0 < 256n /\ 0 < 16777216n``)])
  \\ fs[do_app,oneline do_word_app_def, allowed_op_def,case_eq_thms]
  \\ every_case_tac \\ fs[]
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ fs[state_rel_thm] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ fs[wordSemTheory.get_vars_def,case_eq_thms]
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ fs[assign_def,some_def] \\ rveq
  \\ rpt_drule0 (memory_rel_Number_IMP
        |> REWRITE_RULE [CONJ_ASSOC]
        |> ONCE_REWRITE_RULE [CONJ_COMM])
  \\ strip_tac \\ rveq
  \\ `2 < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword \\
        fs [good_dimindex_def] \\ decide_tac)
  \\ TOP_CASE_TAC \\ fs [] \\ fs [good_dimindex_def,list_Seq_def] \\ rfs []
  \\ fs [eq_eval,word_sh_def,Smallnum_def]
  \\ TRY(qpat_abbrev_tac `ww = _ >>> 1`
    \\ `ww = n2w (w2n w)` by
     (unabbrev_all_tac
      \\ once_rewrite_tac [GSYM w2n_11]
      \\ rewrite_tac [w2n_lsr]
      \\ Cases_on `w` \\ fs [dimword_def]
      \\ once_rewrite_tac [MULT_COMM] \\ fs [MULT_DIV]))
  \\ rveq \\ fs []
  >- (conj_tac >-
        (imp_res_tac consume_space_stack_max >> simp[option_le_max_right] >>
         metis_tac[option_le_trans]) >>
      strip_tac >> spose_not_then strip_assume_tac >>
      fs[encode_header_def,state_rel_def,good_dimindex_def,limits_inv_def,dimword_def,
          memory_rel_def,heap_in_memory_store_def,consume_space_def] >> rfs[NOT_LESS] >>
      rveq >> rfs[] >>
      `2 <= 30 - c.len_size` by simp[] >>
      dxrule_then (strip_assume_tac o GSYM) LESS_EQ_ADD_EXISTS >>
      fs[EXP_ADD] >> assume_tac bitTheory.TWOEXP_NOT_ZERO >>
      pop_assum(qspec_then `p` assume_tac) >>
      Cases_on `2 ** p` >> fs[])
  >- (conj_tac >-
        (imp_res_tac consume_space_stack_max >> simp[option_le_max_right] >>
         metis_tac[option_le_trans]) >>
      strip_tac >> spose_not_then strip_assume_tac >>
      fs[encode_header_def,state_rel_def,good_dimindex_def,limits_inv_def,dimword_def,
         memory_rel_def,heap_in_memory_store_def,consume_space_def] >> rfs[NOT_LESS] >>
      rveq >> rfs[])
  THEN1
   (assume_tac (GEN_ALL evaluate_WriteWord64_on_32)
    \\ SEP_I_TAC "evaluate"
    \\ pop_assum mp_tac \\ fs [join_env_locals_def]
    \\ fs [wordSemTheory.get_var_def,lookup_insert]
    \\ fs [inter_insert_ODD_adjust_set_alt]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ disch_then drule0
    \\ disch_then (qspec_then `w2w w` mp_tac)
    \\ impl_keep_tac THEN1
     (fs [consume_space_def]
      \\ Cases_on `w` \\ fs [w2w_def,word_extract_n2w,dimword_def]
      \\ fs [bitTheory.BITS_THM2,LESS_DIV_EQ_ZERO])
    \\ strip_tac \\ fs [w2w_def]
    \\ fs [consume_space_def] \\ rveq \\ fs[]
    \\ conj_tac THEN1 rw []
    \\ fs [FAPPLY_FUPDATE_THM]
    \\ qhdtm_x_assum `limits_inv` mp_tac
    \\ simp[limits_inv_def,FLOOKUP_UPDATE]
    \\ simp[option_le_max_right]
   )
  THEN1
   (assume_tac (GEN_ALL evaluate_WriteWord64)
    \\ SEP_I_TAC "evaluate"
    \\ pop_assum mp_tac \\ fs [join_env_locals_def]
    \\ fs [wordSemTheory.get_var_def,lookup_insert]
    \\ fs [inter_insert_ODD_adjust_set_alt]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ disch_then drule0
    \\ impl_keep_tac THEN1 (fs [consume_space_def])
    \\ strip_tac \\ fs [w2w_def]
    \\ fs [consume_space_def] \\ rveq \\ fs[]
    \\ conj_tac THEN1 rw []
    \\ conj_tac THEN1 simp [option_le_max_right]
    \\ conj_tac THEN1
      (qhdtm_x_assum `limits_inv` mp_tac
      \\ simp[limits_inv_def,FLOOKUP_UPDATE])
    \\ fs [FAPPLY_FUPDATE_THM,w2w_def]
    \\ Cases_on `w` \\ fs [] \\ rfs [dimword_def] \\ fs []
    \\ match_mp_tac (GEN_ALL memory_rel_less_space)
    \\ qexists_tac`s.space - 2` \\ fs[]
   )
QED

Theorem assign_WordToInt:
   op = WordOp WordToInt ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app,oneline do_word_app_def,allowed_op_def]
  \\ gvs [AllCaseEqs()]
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ `good_dimindex (:'a)` by fs [state_rel_thm]
  \\ `shift_length c < dimindex (:'a)` by
       fs [state_rel_thm,memory_rel_def,heap_in_memory_store_def]
  \\ `shift_length c - shift (dimindex (:'a)) < dimword (:'a) /\
      shift_length c < dimword (:'a) /\
      shift (dimindex (:'a)) < dimword (:'a) /\
      62 < dimword (:'a) /\ 30 < dimword (:'a) /\ 1 < dimword (:'a) /\
      2 < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword
        \\ fs [shift_def,good_dimindex_def,dimword_def] \\ decide_tac)
  \\ fs[state_rel_thm] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ fs[wordSemTheory.get_vars_def]
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ simp[assign_def]
  \\ Cases_on `dimindex (:α) = 32` \\ simp []
  THEN1
   (BasicProvers.TOP_CASE_TAC >-
      (simp[] >>
       conj_tac >- metis_tac[consume_space_stack_max,backendPropsTheory.option_le_trans,option_le_max_right] >>
       strip_tac >> spose_not_then strip_assume_tac >>
       fs[encode_header_def,state_rel_def,good_dimindex_def,limits_inv_def,dimword_def,
          memory_rel_def,heap_in_memory_store_def,consume_space_def] >> rfs[NOT_LESS] >>
       rveq >> rfs[] >>
       `2 <= 30 - c.len_size` by simp[] >>
       dxrule_then (strip_assume_tac o GSYM) LESS_EQ_ADD_EXISTS >>
       fs[EXP_ADD] >> assume_tac bitTheory.TWOEXP_NOT_ZERO >>
       pop_assum(qspec_then `p` assume_tac) >>
       Cases_on `2 ** p` >> fs[])
    \\ BasicProvers.TOP_CASE_TAC >-
      (simp[]>>
       conj_tac >- metis_tac[consume_space_stack_max,backendPropsTheory.option_le_trans,option_le_max_right] >>
       strip_tac >> spose_not_then strip_assume_tac >>
       fs[encode_header_def,state_rel_def,good_dimindex_def,limits_inv_def,dimword_def,
          memory_rel_def,heap_in_memory_store_def,consume_space_def] >> rfs[NOT_LESS] >>
       rveq >> rfs[] >>
       Cases_on `c.len_size` >> fs[EXP] >>
       Cases_on `2 ** n` >> fs[])
    \\ eval_tac
    \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
    \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
    \\ drule0 memory_rel_Word64_IMP \\ fs [] \\ strip_tac
    \\ fs [get_vars_def,GSYM wordSemTheory.get_var_def]
    \\ rpt_drule0 get_var_get_real_addr_lemma
    \\ disch_then kall_tac
    \\ fs [WORD_MUL_LSL]
    \\ ntac 3 (once_rewrite_tac [list_Seq_def] \\ eval_tac \\ fs [lookup_insert])
    \\ fs [wordSemTheory.get_var_imm_def,wordSemTheory.get_var_def] \\ eval_tac
    \\ fs [asmTheory.word_cmp_def,lookup_insert]
    \\ IF_CASES_TAC
    THEN1
     (assume_tac (GEN_ALL evaluate_WriteWord64_on_32_num)
      \\ SEP_I_TAC "evaluate"
      \\ rfs [wordSemTheory.get_var_def,lookup_insert]
      \\ fs [GSYM join_env_locals_def]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ pop_assum drule0
      \\ impl_tac THEN1 fs [consume_space_def]
      \\ strip_tac \\ fs [consume_space_def] \\ rveq \\ fs []
      \\ conj_tac THEN1 rw []
      \\ fs [GSYM join_env_locals_def,option_le_max_right]
      \\ CONJ_TAC >-
        fs[limits_inv_def,FLOOKUP_UPDATE]
      \\ first_x_assum (fn th => mp_tac th THEN
           match_mp_tac (METIS_PROVE [] ``x=y ==> x ==> y``) THEN
           AP_TERM_TAC)
      \\ fs [FAPPLY_FUPDATE_THM]
      \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
      \\ rename [‘_ = w2n ccc’]
      \\ Cases_on `ccc` \\ rfs [word_extract_n2w,dimword_def,bitTheory.BITS_THM]
      \\ fs [DIV_MOD_MOD_DIV]
      \\ `0 < 4294967296n` by fs []
      \\ drule0 DIVISION
      \\ simp [Once MULT_COMM])
    \\ simp[list_Seq_def]
    \\ simp[wordSemTheory.evaluate_def]
    \\ simp[word_exp_rw,wordSemTheory.set_var_def]
    \\ simp[wordSemTheory.get_var_def,lookup_insert,wordSemTheory.get_var_imm_def]
    \\ simp[asmTheory.word_cmp_def] \\ fs []
    \\ IF_CASES_TAC
    >- (
      simp[Once wordSemTheory.evaluate_def,lookup_insert]
      \\ fs[consume_space_def]
      \\ clean_tac \\ fs[]
      \\ conj_tac >- rw[]
      \\ simp[inter_insert_ODD_adjust_set,option_le_max_right]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert
      \\ qmatch_goalsub_abbrev_tac`Number i,Word sn`
      \\ `sn = Smallnum i ∧ small_int (dimindex (:α)) i` suffices_by (
        rw[]
        \\ match_mp_tac IMP_memory_rel_Number
        \\ simp[]
        \\ match_mp_tac (GEN_ALL memory_rel_less_space)
        \\ qexists_tac`s.space` \\ fs[] )
      \\ simp[Abbr`sn`,Abbr`i`]
      \\ fs [Smallnum_def]
      \\ rename [‘(31 >< 0) ccc ≪ 1 = _’]
      \\ Cases_on `ccc` \\ fs []
      \\ fs [word_extract_n2w,WORD_MUL_LSL,word_mul_n2w,
             bitTheory.BITS_THM2,dimword_def] \\ rfs []
      \\ fs [DIV_MOD_MOD_DIV]
      \\ fs [DIV_EQ_X] \\ rfs []
      \\ `w2n (n2w n ⋙ 30) = w2n 0w` by fs []
      \\ full_simp_tac std_ss [w2n_lsr]
      \\ rfs [dimword_def]
      \\ fs [DIV_EQ_X] \\ rfs [small_int_def,dimword_def])
    THEN1
     (assume_tac (GEN_ALL evaluate_WriteWord32_bignum)
      \\ SEP_I_TAC "evaluate"
      \\ rfs [wordSemTheory.get_var_def,lookup_insert]
      \\ fs [GSYM join_env_locals_def]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ pop_assum drule0
      \\ impl_tac THEN1 (
        fs [consume_space_def]
        \\ rename [‘(&w2n ((31 >< 0) ccc))’]
        \\ Cases_on `ccc` \\ fs []
        \\ fs [word_extract_n2w,WORD_MUL_LSL,word_mul_n2w,
               bitTheory.BITS_THM2,dimword_def] \\ rfs []
        \\ fs [DIV_MOD_MOD_DIV]
        \\ fs [DIV_EQ_X] \\ rfs [small_int_def,dimword_def]
        \\ `w2n (n2w n ⋙ 30) <> w2n 0w` by fs []
        \\ full_simp_tac std_ss [w2n_lsr]
        \\ rfs [dimword_def]
        \\ fs [DIV_EQ_X])
      \\ strip_tac \\ fs [consume_space_def] \\ rveq \\ fs []
      \\ conj_tac THEN1 rw []
      \\ conj_tac THEN1 simp[option_le_max_right]
      \\ conj_tac >-
        fs[limits_inv_def,FLOOKUP_UPDATE]
      \\ fs [GSYM join_env_locals_def]
      \\ fs [FAPPLY_FUPDATE_THM]
      \\ match_mp_tac (GEN_ALL memory_rel_less_space)
      \\ qexists_tac `s.space − 2` \\ fs []
      \\ first_x_assum (fn th => mp_tac th THEN
           match_mp_tac (METIS_PROVE [] ``x=y ==> x ==> y``) THEN
           AP_TERM_TAC)
      \\ fs [FAPPLY_FUPDATE_THM]
      \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
      \\ rename [‘w2n ((31 >< 0) ccc) = w2n ccc’]
      \\ Cases_on `ccc` \\ fs []
      \\ fs [word_extract_n2w,WORD_MUL_LSL,word_mul_n2w,
             bitTheory.BITS_THM2,dimword_def] \\ rfs []
      \\ fs [DIV_MOD_MOD_DIV]
      \\ fs [DIV_EQ_X] \\ rfs []))
  \\ BasicProvers.TOP_CASE_TAC >-
      (simp[]>>
       conj_tac >- metis_tac[consume_space_stack_max,
                             backendPropsTheory.option_le_trans,option_le_max_right] >>
       qsuff_tac ‘F’ >- simp [] >>
       pop_assum mp_tac >>
       gvs [encode_header_def,good_dimindex_def,dimword_def] >>
       gvs [limits_inv_def] >>
       gvs[encode_header_def,state_rel_def,good_dimindex_def,limits_inv_def,dimword_def,
          memory_rel_def,heap_in_memory_store_def,consume_space_def] >> rfs[NOT_LESS] >>
       irule LESS_LESS_EQ_TRANS >>
       qexists_tac ‘2 ** 2’ >>
       gvs [])
  \\ `dimindex (:'a) = 64` by fs [good_dimindex_def] \\ simp []
  \\ simp[list_Seq_def]
  \\ simp[Once wordSemTheory.evaluate_def]
  \\ rpt_drule0 evaluate_LoadWord64 \\ fs[]
  \\ disch_then kall_tac
  \\ simp[Once wordSemTheory.evaluate_def]
  \\ simp[evaluate_Assign,word_exp_rw,wordSemTheory.set_var_def]
  \\ simp[Once wordSemTheory.evaluate_def]
  \\ simp[evaluate_Assign,word_exp_rw,wordSemTheory.set_var_def]
  \\ simp[Once wordSemTheory.evaluate_def]
  \\ simp[wordSemTheory.get_var_def,lookup_insert,wordSemTheory.get_var_imm_def]
  \\ simp[asmTheory.word_cmp_def]
  \\ IF_CASES_TAC
  >- (
    simp[Once wordSemTheory.evaluate_def,lookup_insert]
    \\ fs[consume_space_def]
    \\ clean_tac \\ fs[]
    \\ conj_tac >- rw[]
    \\ simp[inter_insert_ODD_adjust_set,option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert
    \\ qmatch_goalsub_abbrev_tac`Number i,Word sn`
    \\ `sn = Smallnum i ∧ small_int (dimindex (:α)) i` suffices_by (
      rw[]
      \\ match_mp_tac IMP_memory_rel_Number
      \\ simp[]
      \\ match_mp_tac (GEN_ALL memory_rel_less_space)
      \\ qexists_tac`s.space` \\ fs[] )
    \\ simp[Abbr`sn`,Abbr`i`]
    \\ rename [‘w2w ccc ⋙ 62 = 0w’]
    \\ reverse conj_tac
    >- (`ccc >>> 62 = 0w`
        by (qpat_x_assum `w2w c' >>> 62 = 0w` mp_tac
            \\ srw_tac[wordsLib.WORD_BIT_EQ_ss][])
        \\ simp[small_int_def,wordsTheory.dimword_def]
        \\ wordsLib.n2w_INTRO_TAC 64
        \\ qpat_x_assum `ccc >>> 62 = 0w` mp_tac
        \\ blastLib.BBLAST_TAC)
    \\ simp_tac(std_ss++wordsLib.WORD_MUL_LSL_ss)
         [Smallnum_i2w,GSYM integerTheory.INT_MUL,
          integer_wordTheory.i2w_w2n_w2w,GSYM integer_wordTheory.word_i2w_mul,
          EVAL ``i2w 2 : 'a word``])
  \\ assume_tac (GEN_ALL evaluate_WriteWord64_bignum)
  \\ SEP_I_TAC "evaluate" \\ fs[]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,GSYM join_env_locals_def]
  \\ first_x_assum drule0
  \\ simp[wordSemTheory.get_var_def,lookup_insert]
  \\ fs[consume_space_def]
  \\ impl_tac
  >- (
    pop_assum mp_tac
    \\ fs[small_int_def]
    \\ simp[dimword_def]
    \\ simp[w2n_w2w]
    \\ qmatch_goalsub_rename_tac`w2n w`
    \\ srw_tac[wordsLib.WORD_BIT_EQ_ss][]
    \\ Cases_on`w` \\ fs[]
    \\ rfs[word_index]
    \\ imp_res_tac bitTheory.BIT_IMP_GE_TWOEXP
    \\ fs[])
  \\ strip_tac \\ fs[]
  \\ clean_tac \\ fs[code_oracle_rel_def,FLOOKUP_UPDATE]
  \\ conj_tac >- rw[]
  \\ fs[FAPPLY_FUPDATE_THM,option_le_max_right]
  \\ match_mp_tac (GEN_ALL memory_rel_less_space)
  \\ qexists_tac`s.space - 2` \\ fs[]
  \\ qmatch_goalsub_abbrev_tac`Number w1`
  \\ qmatch_asmsub_abbrev_tac`Number w2`
  \\ `w1 = w2` suffices_by simp[]
  \\ simp[Abbr`w1`,Abbr`w2`]
  \\ simp[w2n_w2w]
QED

Theorem LENGTH_n2mw_1[local]:
    LENGTH ((n2mw n) :'a word list) = 1 <=> n <> 0 /\ n < dimword (:'a)
Proof
  once_rewrite_tac [multiwordTheory.n2mw_def] \\ rw []
  \\ once_rewrite_tac [multiwordTheory.n2mw_def] \\ rw []
  \\ fs [dimword_def,DIV_EQ_0]
QED

Theorem WordFromInt_DIV_LEMMA[local]:
    kk < B * B /\ 0 < B ==> B * (kk DIV B) <= B * B − B
Proof
  rw []
  \\ `kk DIV B < B` by fs [DIV_LT_X]
  \\ `B² − B = B * (B - 1)` by fs [LEFT_SUB_DISTRIB]
  \\ fs []
QED

Theorem explode_less_32[local]:
    (!n. n < 32n ==> P (n:num)) <=>
    P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5 /\ P 6 /\ P 7 /\ P 8 /\ P 9 /\
    P 10 /\ P 11 /\ P 12 /\ P 13 /\ P 14 /\ P 15 /\ P 16 /\ P 17 /\ P 18 /\ P 19 /\
    P 20 /\ P 21 /\ P 22 /\ P 23 /\ P 24 /\ P 25 /\ P 26 /\ P 27 /\ P 28 /\ P 29 /\
    P 30 /\ P 31
Proof
  rw [] \\ eq_tac \\ fs [] \\ rw []
  \\ rpt (Cases_on `n` \\ fs [] \\ Cases_on `n'` \\ fs [])
QED

Theorem LESS_IMP_NOT_BIT[local]:
    !k n. n < 2 ** k ==> ~BIT k n
Proof
  fs [bitTheory.BIT_def,bitTheory.BITS_THM,LESS_DIV_EQ_ZERO]
QED

Theorem Smallnum_alt:
   Smallnum i =
    if i < 0 then (0w - n2w (Num (-i))) << 1 else n2w (Num i) << 1
Proof
  Cases_on `i` \\ fs [WORD_MUL_LSL,Smallnum_def,GSYM word_mul_n2w]
  \\ once_rewrite_tac [SIMP_CONV (srw_ss()) [] ``-w:'a word``]
  \\ simp_tac std_ss [AC WORD_MULT_COMM WORD_MULT_ASSOC]
QED

Theorem BIT_lemma[local]:
    BIT n (2 ** k - i) <=> if n < k /\ i < 2n ** k /\ i <> 0
                           then BIT n (2 ** (MAX n i + 1) - i)
                           else BIT n (2 ** k - i)
Proof
  IF_CASES_TAC \\ fs []
  \\ `i = i MOD 2 ** k` by fs []
  \\ pop_assum (fn th => CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [th])))
  \\ rewrite_tac [bitTheory.BIT_COMPLEMENT] \\ fs []
  \\ `i < 2 ** (MAX n i + 1)` by
   (match_mp_tac LESS_LESS_EQ_TRANS
    \\ `i < 2 ** i` by fs [multiwordTheory.LESS_2_EXP]
    \\ asm_exists_tac \\ fs []
    \\ rw [MAX_DEF])
  \\ `i MOD 2 ** (MAX n i + 1) = i` by fs []
  \\ `2 ** (MAX n i + 1) − i =
      2 ** (MAX n i + 1) − (i MOD 2 ** (MAX n i + 1))` by metis_tac []
  \\ pop_assum (fn th => rewrite_tac [th])
  \\ rewrite_tac [bitTheory.BIT_COMPLEMENT] \\ fs []
  \\ eq_tac \\ rw []
  \\ rw [MAX_DEF] \\ fs []
QED

Theorem BIT_Lemma2[local]:
    BIT m (2 ** k - n) = if n <> 0 /\ n <= 2 ** m /\ m < k then T
                         else BIT m (2n ** k - n)
Proof
  IF_CASES_TAC \\ fs []
  \\ imp_res_tac bitTheory.TWOEXP_MONO
  \\ drule0 LESS_EQ_LESS_TRANS
  \\ disch_then drule0
  \\ strip_tac
  \\ `n = n MOD 2 ** k` by fs []
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ rewrite_tac [bitTheory.BIT_COMPLEMENT]
  \\ fs [] \\ fs [bitTheory.BIT_def,bitTheory.BITS_THM]
  \\ `n - 1 < 2 ** m` by fs [] \\ fs []
  \\ fs [LESS_DIV_EQ_ZERO]
QED

Theorem assign_WordFromInt:
  op = WordOp WordFromInt ==> ^assign_thm_goal
Proof[exclude_simps = INT_OF_NUM NUM_EQ0]
  strip_tac
  \\ rpt strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app,oneline do_word_app_def,allowed_op_def]
  \\ every_case_tac \\ fs[]
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ fs[state_rel_thm] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ fs[wordSemTheory.get_vars_def]
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ simp[assign_def]
  \\ BasicProvers.TOP_CASE_TAC >-
    (simp[]>>
     conj_tac >- metis_tac[backendPropsTheory.option_le_trans,consume_space_stack_max,option_le_max_right] >>
     strip_tac >> spose_not_then strip_assume_tac >>
     fs[encode_header_def,state_rel_def,good_dimindex_def,limits_inv_def,dimword_def,
        memory_rel_def,heap_in_memory_store_def,consume_space_def] >> rfs[NOT_LESS] >>
     rveq >> rfs[])
  \\ reverse BasicProvers.TOP_CASE_TAC >- suspend "word32"
  \\ simp[Once wordSemTheory.evaluate_def]
  \\ simp[Once wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def]
  \\ rpt_drule0 memory_rel_any_Number_IMP \\ strip_tac
  \\ simp[asmTheory.word_cmp_def]
  \\ ONCE_REWRITE_TAC[WORD_AND_COMM]
  \\ simp[word_and_one_eq_0_iff]
  \\ IF_CASES_TAC
  >- (
    simp[Once wordSemTheory.evaluate_def]
    \\ simp[Once wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def]
    \\ simp[Once wordSemTheory.evaluate_def]
    \\ simp[evaluate_Assign]
    \\ simp[word_exp_rw |> CONJUNCTS |> first(can(find_term(same_const``wordLang$Shift``)) o concl)]
    \\ simp[word_exp_rw |> CONJUNCTS |> first(can(find_term(same_const``wordLang$Var``)) o concl)]
    \\ fs[wordSemTheory.get_var_def]
    \\ simp[wordSemTheory.word_sh_def]
    \\ simp[wordSemTheory.set_var_def]
    \\ simp[wordSemTheory.word_exp_def]
    \\ ‘2 MOD dimword (:α) < dimindex (:α)’ by simp[dimword_def]
    \\ simp []
    \\ rpt_drule0 memory_rel_Number_IMP
    \\ strip_tac \\ clean_tac
    \\ assume_tac (GEN_ALL evaluate_WriteWord64)
    \\ SEP_I_TAC "evaluate" \\ fs[]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,GSYM join_env_locals_def]
    \\ first_x_assum drule0
    \\ simp[wordSemTheory.get_var_def]
    \\ fs[consume_space_def]
    \\ rfs[good_dimindex_def] \\ rfs[lookup_insert]
    \\ strip_tac \\ fs[]
    \\ clean_tac \\ fs[code_oracle_rel_def,FLOOKUP_UPDATE,option_le_max_right]
    \\ conj_tac >- rw[]
    \\ match_mp_tac (GEN_ALL memory_rel_less_space)
    \\ qexists_tac`s.space - 2` \\ simp[]
    \\ fs[FAPPLY_FUPDATE_THM]
    \\ qmatch_asmsub_abbrev_tac`Word64 w1`
    \\ qmatch_goalsub_abbrev_tac`Word64 w2`
    \\ `w1 = w2` suffices_by (rw[] \\ fs[])
    \\ simp[Abbr`w1`,Abbr`w2`]
    \\ ‘2 MOD dimword (:α) = 2’ by simp [dimword_def]
    \\ `INT_MIN (:'a) <= 2 * i /\ 2 * i <= INT_MAX (:'a)`
    by (rfs [small_int_def,wordsTheory.dimword_def,
             integer_wordTheory.INT_MIN_def,wordsTheory.INT_MAX_def,
             wordsTheory.INT_MIN_def]
        \\ intLib.ARITH_TAC)
    \\ simp[Smallnum_i2w,GSYM integer_wordTheory.i2w_DIV,
            integerTheory.INT_DIV_LMUL,integer_wordTheory.w2w_i2w] )
  \\ simp[Once wordSemTheory.evaluate_def]
  \\ drule0 (GEN_ALL evaluate_LoadBignum)
  \\ simp[] \\ clean_tac
  \\ disch_then drule0
  \\ disch_then(qspecl_then[`3`,`1`]mp_tac)
  \\ simp[] \\ strip_tac
  \\ simp[]
  \\ simp[Once wordSemTheory.evaluate_def,wordSemTheory.set_vars_def,wordSemTheory.get_var_imm_def]
  \\ simp[wordSemTheory.get_var_def,alist_insert_def,lookup_insert,asmTheory.word_cmp_def]
  \\ IF_CASES_TAC
  >- (
    simp[Once wordSemTheory.evaluate_def]
    \\ assume_tac(GEN_ALL evaluate_WriteWord64)
    \\ SEP_I_TAC "evaluate" \\ fs[]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,GSYM join_env_locals_def]
    \\ first_x_assum drule0
    \\ simp[wordSemTheory.get_var_def]
    \\ fs[lookup_insert,good_dimindex_def,consume_space_def]
    \\ strip_tac
    \\ clean_tac \\ fs[code_oracle_rel_def,FLOOKUP_UPDATE,option_le_max_right]
    \\ conj_tac >- rw[]
    \\ match_mp_tac (GEN_ALL memory_rel_less_space)
    \\ qexists_tac`s.space - 2`
    \\ simp[]
    \\ `(i2w i : word64) = n2w (Num i)` by (
      rw[integer_wordTheory.i2w_def]
      \\ `F` suffices_by rw[]
      \\ intLib.COOPER_TAC )
    \\ rfs[w2w_n2w]
    \\ simp[FAPPLY_FUPDATE_THM]
    \\ metis_tac [integerTheory.INT_ABS_EQ_ID])
  \\ simp[Once wordSemTheory.evaluate_def]
  \\ simp[word_exp_rw,wordSemTheory.set_var_def]
  \\ assume_tac(GEN_ALL evaluate_WriteWord64)
  \\ SEP_I_TAC "evaluate" \\ fs[]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,GSYM join_env_locals_def]
  \\ first_x_assum drule0
  \\ simp[wordSemTheory.get_var_def]
  \\ fs[lookup_insert,good_dimindex_def,consume_space_def]
  \\ strip_tac
  \\ clean_tac \\ fs[code_oracle_rel_def,FLOOKUP_UPDATE,option_le_max_right]
  \\ conj_tac >- rw[]
  \\ match_mp_tac (GEN_ALL memory_rel_less_space)
  \\ qexists_tac`s.space - 2`
  \\ simp[]
  \\ `(i2w i : word64) = -n2w (Num (-i))` by (
    simp_tac std_ss [integer_wordTheory.i2w_def]
    \\ IF_CASES_TAC  \\ simp[]
    \\ `F` suffices_by rw[]
    \\ intLib.COOPER_TAC )
  \\ pop_assum SUBST_ALL_TAC
  \\ `ABS i = -i`
  by (
    simp[integerTheory.INT_ABS]
    \\ rw[]
    \\ intLib.COOPER_TAC )
  \\ pop_assum SUBST_ALL_TAC
  \\ ONCE_REWRITE_TAC[WORD_NEG_MUL]
  \\ rfs[WORD_w2w_OVER_MUL,w2w_n2w]
  \\ qmatch_goalsub_abbrev_tac`insert dest w1`
  \\ qmatch_asmsub_abbrev_tac`insert dest w2`
  \\ `w1 = w2` suffices_by simp[FAPPLY_FUPDATE_THM]
  \\ simp[Abbr`w1`,Abbr`w2`]
  \\ simp[WORD_BITS_EXTRACT]
  \\ match_mp_tac EQ_SYM
  \\ `w2w (-1w:'a word) = (-1w:word64)`
  by ( EVAL_TAC \\ simp[w2w_n2w,dimword_def] )
  \\ pop_assum SUBST_ALL_TAC
  \\ simp[Once WORD_MULT_COMM,SimpLHS]
  \\ match_mp_tac WORD_EXTRACT_ID
  \\ qmatch_goalsub_abbrev_tac`w2n ww`
  \\ Q.ISPEC_THEN`ww`mp_tac w2n_lt
  \\ simp[dimword_def]
QED

Resume assign_WordFromInt[word32]:
simp[Once wordSemTheory.evaluate_def]
    \\ simp[Once wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def]
    \\ rpt_drule0 memory_rel_any_Number_IMP \\ strip_tac
    \\ simp[asmTheory.word_cmp_def]
    \\ ONCE_REWRITE_TAC[WORD_AND_COMM]
    \\ simp[word_and_one_eq_0_iff]
    \\ IF_CASES_TAC
    >- (
      simp[list_Seq_def,Once wordSemTheory.evaluate_def]
      \\ simp[Once wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def]
      \\ simp[Once wordSemTheory.evaluate_def]
      \\ simp[evaluate_Assign]
      \\ simp[word_exp_rw |> CONJUNCTS |> first(can(find_term(same_const``wordLang$Shift``)) o concl)]
      \\ simp[word_exp_rw |> CONJUNCTS |> first(can(find_term(same_const``wordLang$Var``)) o concl)]
      \\ fs[wordSemTheory.get_var_def]
      \\ `31 < dimindex(:'a)` by fs[good_dimindex_def]
      \\ simp[wordSemTheory.word_sh_def]
      \\ simp[wordSemTheory.set_var_def]
      \\ simp[wordSemTheory.word_exp_def]
      \\ ‘2 MOD dimword (:α) < dimindex (:α)
          ∧ 31 MOD dimword (:α) < dimindex (:α)’
        by simp[dimword_def]
      \\ fs[adjust_var_def,lookup_insert]
      \\ ‘∀x:num. 2 * x + 2 ≠ 3’ by intLib.COOPER_TAC \\ simp []
      \\ rpt_drule0 memory_rel_Number_IMP
      \\ strip_tac \\ clean_tac
      \\ assume_tac (GEN_ALL evaluate_WriteWord64_on_32)
      \\ SEP_I_TAC "evaluate" \\ fs[]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,GSYM join_env_locals_def]
      \\ first_x_assum drule0
      \\ simp[wordSemTheory.get_var_def]
      \\ fs[consume_space_def]
      \\ rfs[good_dimindex_def] \\ rfs[lookup_insert]
      \\ simp[]
      \\ disch_then (qspec_then `(Smallnum i >> 1)` mp_tac)
      \\ `INT_MIN (:'a) <= 2 * i /\ 2 * i <= INT_MAX (:'a) ∧
          INT_MIN (:64) <= 2 * i /\ 2 * i <= INT_MAX (:64) ∧
          INT_MIN (:'a) <= i /\ i <= INT_MAX (:'a) `
        by (rfs [small_int_def,wordsTheory.dimword_def,
               integer_wordTheory.INT_MIN_def,wordsTheory.INT_MAX_def,
               wordsTheory.INT_MIN_def]
        \\ intLib.ARITH_TAC)
      \\ impl_keep_tac >-
       (rewrite_tac [CONJ_ASSOC]
        \\ reverse conj_tac THEN1 rw [adjust_var_def]
        \\ rewrite_tac [Smallnum_alt,WORD_SUB_LZERO]
        \\ fs [] \\ Cases_on `i` \\ fs []
        \\ rfs [small_int_def,dimword_def]
        \\ fs [fcpTheory.CART_EQ,word_asr_def,fcpTheory.FCP_BETA,
               word_extract_def,w2w,word_bits_def,word_msb_def,word_lsl_def]
        THEN1
         (fs [word_lsl_def,fcpTheory.FCP_BETA]
          \\ fs [explode_less_32,fcpTheory.FCP_BETA,word_index]
          \\ `~BIT 30 n` by (match_mp_tac LESS_IMP_NOT_BIT \\ fs []) \\ fs []
          \\ rw [] \\ TRY (match_mp_tac LESS_IMP_NOT_BIT) \\ fs [])
        \\ fs [word_lsl_def,fcpTheory.FCP_BETA]
        \\ fs [explode_less_32,fcpTheory.FCP_BETA,word_index]
        \\ fs [word_2comp_n2w,dimword_def,word_index]
        \\ reverse (rw [])
        \\ rewrite_tac [GSYM (EVAL ``2n ** 32``)]
        \\ rewrite_tac [GSYM (EVAL ``2n ** 64``)]
        \\ TRY (once_rewrite_tac [BIT_Lemma2] \\ fs [] \\ NO_TAC)
        \\ once_rewrite_tac [BIT_lemma] \\ fs [])
      \\ strip_tac \\ fs[]
      \\ clean_tac \\ fs[]
      \\ conj_tac >-
        (fs[adjust_var_def]>>
        metis_tac[])
      \\ conj_tac >- simp[option_le_max_right]
      \\ conj_tac >-
        (qhdtm_x_assum `limits_inv` mp_tac
        \\ simp[limits_inv_def,FLOOKUP_UPDATE])
      \\ match_mp_tac (GEN_ALL memory_rel_less_space)
      \\ qexists_tac`s.space - 3` \\ simp[]
      \\ fs[FAPPLY_FUPDATE_THM]
      \\ qmatch_asmsub_abbrev_tac`Word64 w1`
      \\ qmatch_goalsub_abbrev_tac`Word64 w2`
      \\ `w1 = w2` suffices_by (rw[] \\ fs[])
      \\ simp[Abbr`w1`,Abbr`w2`]
      \\ simp[Smallnum_i2w,GSYM integer_wordTheory.i2w_DIV,
            integerTheory.INT_DIV_LMUL,integer_wordTheory.w2w_i2w])
    (* bignum cases *)
    \\ rpt_drule0 memory_rel_Number_bignum_IMP_ALT
    \\ strip_tac \\ rfs[] \\ clean_tac
    \\ ntac 3 (once_rewrite_tac [list_Seq_def])
    \\ rpt_drule0 get_var_get_real_addr_lemma
    \\ simp[lookup_insert]
    \\ simp[wordSemTheory.set_vars_def,
          wordSemTheory.state_component_equality,alist_insert_def]
    \\ eval_tac \\ fs [lookup_insert]
    \\ once_rewrite_tac [list_Seq_def]
    \\ eval_tac \\ fs [lookup_insert]
    \\ simp [Once word_exp_ShiftVar_bits] \\ fs [eq_eval]
    \\ fs [decode_length_def]
    \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
    \\ `dimindex (:α) = 32` by fs [good_dimindex_def]
    \\ IF_CASES_TAC (* first case is LENGTH = 1 *)
    THEN1
     (IF_CASES_TAC THEN1
       (assume_tac (GEN_ALL evaluate_WriteWord64_on_32)
        \\ SEP_I_TAC "evaluate" \\ fs [eq_eval]
        \\ fs [GSYM join_env_locals_def]
        \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
        \\ pop_assum drule0
        \\ disch_then (qspec_then `n2w (Num (ABS i))` mp_tac)
        \\ fs [] \\ impl_keep_tac
        THEN1
         (fs [consume_space_def,LENGTH_n2mw_1]
          \\ rfs [word_extract_n2w,bitTheory.BITS_THM,dimword_def]
          \\ fs [DIV_MOD_MOD_DIV]
          \\ once_rewrite_tac [EQ_SYM_EQ] \\ fs [DIV_EQ_X])
        \\ strip_tac \\ fs []
        \\ fs [consume_space_def,LENGTH_n2mw_1]
        \\ rveq \\ fs [option_le_max_right]
        \\ strip_tac \\ conj_tac THEN1 rw []
        \\ conj_tac >-
          (qhdtm_x_assum `limits_inv` mp_tac
          \\ simp[limits_inv_def,FLOOKUP_UPDATE])
        \\ `Word64 (n2w (Num (ABS i))) = Word64 (i2w i)` by
              (Cases_on `i` \\ fs [integer_wordTheory.i2w_def,Num_ABS_AND])
        \\ fs [FAPPLY_FUPDATE_THM])
      THEN1
       (assume_tac (GEN_ALL evaluate_WriteWord64_on_32)
        \\ SEP_I_TAC "evaluate" \\ fs [eq_eval]
        \\ fs [GSYM join_env_locals_def,option_le_max_right]
        \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
        \\ pop_assum drule0
        \\ disch_then (qspec_then `-n2w (Num (ABS i))` mp_tac)
        \\ fs [] \\ impl_keep_tac
        THEN1
         (fs [consume_space_def,LENGTH_n2mw_1]
          \\ rfs [word_extract_n2w,bitTheory.BITS_THM,dimword_def]
          \\ rewrite_tac [GSYM (SIMP_CONV (srw_ss()) [] ``- w:'a word``)]
          \\ rewrite_tac [word_2comp_n2w]
          \\ fs [dimword_def]
          \\ rewrite_tac [GSYM (EVAL ``4294967296 * 4294967296n``)]
          \\ `(4294967296 * 4294967296 − Num (ABS i)) MOD 4294967296 =
              (4294967296 − Num (ABS i)) MOD 4294967296` by
                 (match_mp_tac MOD_TIMES_SUB \\ fs []) \\ fs []
          \\ `18446744073709551616 − Num (ABS i) =
              4294967295 * 4294967296 + (4294967296 - Num (ABS i))` by fs[]
          \\ asm_rewrite_tac []
          \\ `4294967296 − Num (ABS i) < 4294967296` by (
            qpat_x_assum `¬(0 ≤ i)` mp_tac
            \\ rpt (pop_assum kall_tac)
            \\ strip_tac
            \\ `i ≠ 0` by intLib.ARITH_TAC
            \\ `Num (ABS i) ≠ 0` by
                 fs [integerTheory.NUM_EQ0,integerTheory.INT_ABS_EQ0]
            \\ decide_tac)
          \\ drule0 DIV_MULT
          \\ simp_tac std_ss []
          \\ qpat_x_assum `4294967296 − Num (ABS i) < 4294967296` mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ rpt strip_tac
          \\ `18446744069414584320 + (4294967296 − Num (ABS i)) <
              18446744073709551616` by decide_tac
          \\ fs []
          \\ qpat_x_assum `∀q. _` (qspec_then `4294967295` mp_tac)
          \\ simp [])
        \\ strip_tac \\ fs []
        \\ fs [consume_space_def,LENGTH_n2mw_1]
        \\ rveq \\ fs []
        \\ strip_tac \\ conj_tac THEN1 rw []
        \\ `Word64 (-n2w (Num (ABS i))) = Word64 (i2w i)` by
              (Cases_on `i` \\ fs [integer_wordTheory.i2w_def,Num_ABS_AND])
        \\ fs [FAPPLY_FUPDATE_THM]
        \\ qhdtm_x_assum `limits_inv` mp_tac
        \\ simp[limits_inv_def,FLOOKUP_UPDATE]))
    \\ `LENGTH (n2mw (Num (ABS i))) <> 0` by
     (once_rewrite_tac [multiwordTheory.n2mw_def]
      \\ rw [] \\ fs [small_int_def]
      \\ fs [dimword_def] \\ intLib.COOPER_TAC)
    \\ IF_CASES_TAC THEN1
     (Cases_on `n2mw (Num (ABS i))` \\ fs []
      \\ Cases_on `t'` \\ fs []
      \\ fs [word_list_def] \\ SEP_R_TAC \\ fs []
      \\ assume_tac (GEN_ALL evaluate_WriteWord64_on_32)
      \\ SEP_I_TAC "evaluate" \\ fs [eq_eval]
      \\ fs [GSYM join_env_locals_def,option_le_max_right]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ pop_assum drule0
      \\ disch_then (qspec_then `n2w (Num (ABS i))` mp_tac)
      \\ fs [] \\ impl_keep_tac
      THEN1
       (fs [consume_space_def,LENGTH_n2mw_1]
        \\ rfs [word_extract_n2w,bitTheory.BITS_THM,dimword_def]
        \\ pop_assum mp_tac
        \\ once_rewrite_tac [multiwordTheory.n2mw_def] \\ rw []
        \\ pop_assum mp_tac
        \\ once_rewrite_tac [multiwordTheory.n2mw_def] \\ rw []
        \\ fs [dimword_def])
      \\ strip_tac \\ fs []
      \\ fs [consume_space_def,LENGTH_n2mw_1]
      \\ rveq \\ fs []
      \\ strip_tac \\ conj_tac THEN1 rw []
      \\ `Word64 (n2w (Num (ABS i))) = Word64 (i2w i)` by
            (Cases_on `i` \\ fs [integer_wordTheory.i2w_def,Num_ABS_AND])
      \\ fs [FAPPLY_FUPDATE_THM]
      \\ qhdtm_x_assum `limits_inv` mp_tac
      \\ simp[limits_inv_def,FLOOKUP_UPDATE] )
    THEN1
     (Cases_on `n2mw (Num (ABS i))` \\ fs []
      \\ Cases_on `t'` \\ fs []
      \\ fs [word_list_def] \\ SEP_R_TAC \\ fs []
      \\ fs [list_Seq_def,eq_eval] \\ SEP_R_TAC
      \\ fs [eq_eval,wordSemTheory.inst_def,word_add_carry_def]
      \\ assume_tac (GEN_ALL evaluate_WriteWord64_on_32)
      \\ SEP_I_TAC "evaluate" \\ fs [eq_eval,option_le_max_right]
      \\ fs [GSYM join_env_locals_def]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ pop_assum drule0
      \\ disch_then (qspec_then `-n2w (Num (ABS i))` mp_tac)
      \\ fs [] \\ impl_keep_tac
      THEN1
       (fs [consume_space_def,LENGTH_n2mw_1]
        \\ fs [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
        \\ rewrite_tac [GSYM (SIMP_CONV (srw_ss()) [] ``- w:'a word``)]
        \\ rewrite_tac [word_2comp_n2w]
        \\ conj_tac
        \\ rfs [word_extract_n2w,bitTheory.BITS_THM,dimword_def]
        THEN1
          (qmatch_goalsub_abbrev_tac`_ MOD A MOD B`>>
          `A = B * B ∧ 0 < B` by fs[Abbr`A`,Abbr`B`]>>
          drule0 MOD_MULT_MOD>>
          disch_then drule0 >>
          simp[]>> strip_tac>>
          drule0 MOD_COMPLEMENT>>
          disch_then drule0>>
          simp[])
        \\ pop_assum mp_tac
        \\ once_rewrite_tac [multiwordTheory.n2mw_def]
        \\ once_rewrite_tac [multiwordTheory.n2mw_def]
        \\ IF_CASES_TAC \\ fs []
        \\ IF_CASES_TAC \\ fs []
        \\ strip_tac \\ rveq \\ fs []
        \\ fs [ADD1,GSYM word_add_n2w,dimword_def]
        \\ fs [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
        \\ fs [DIV_MOD_MOD_DIV]
        \\ fs [word_add_n2w,dimword_def]
        \\ qmatch_goalsub_abbrev_tac `if (if bb then _ else _) = _ then _ else _`
        \\ `bb <=> Num (ABS i) MOD 4294967296 = 0` by
          (unabbrev_all_tac
           \\ Cases_on `Num (ABS i) MOD 4294967296 = 0` \\ fs []
           \\ fs [GSYM NOT_LESS]
           \\ DEP_REWRITE_TAC [GSYM bitTheory.MOD_ADD_1]
           \\ simp[ADD_COMM,ADD_ASSOC]
           \\ simp[NOT_LESS_EQUAL])
        \\ Cases_on `bb` \\ fs []
        >-
          (simp[Once (GSYM WORD_NEG_MUL),word_2comp_n2w,dimword_def]
          \\ Cases_on `Num (ABS i) MOD 18446744073709551616 = 0` \\ fs []
          \\ qabbrev_tac `kk = Num (ABS i) MOD 18446744073709551616`
          \\ `kk < 18446744073709551616` by fs [Abbr `kk`]
          \\ `kk MOD 4294967296 = 0` by
           (unabbrev_all_tac
            \\ qmatch_goalsub_abbrev_tac`_ MOD A MOD B`
            \\ `A = B * B ∧ 0 < B` by fs[Abbr`A`,Abbr`B`]
            \\ asm_rewrite_tac []
            \\ asm_simp_tac std_ss [MOD_MULT_MOD])
          \\ fs [DIV_MOD_MOD_DIV]
          \\ once_rewrite_tac [EQ_SYM_EQ]
          \\ `0n < 4294967296` by EVAL_TAC
          \\ drule0 DIVISION
          \\ disch_then (qspec_then `kk` strip_assume_tac)
          \\ rfs [] \\ clean_tac
          \\ `18446744073709551616 − kk =
              (4294967296 - kk DIV 4294967296) * 4294967296`
                  by fs [RIGHT_SUB_DISTRIB]
          \\ asm_simp_tac std_ss [MULT_DIV]
          \\ qpat_x_assum `kk = _` (fn th => simp [Once th])
          \\ rewrite_tac [SUB_PLUS]
          \\ qmatch_goalsub_abbrev_tac`A - B * _`
          \\ `A = B * B ∧ 0 < B` by fs[Abbr`A`,Abbr`B`]
          \\ asm_rewrite_tac [GSYM LEFT_SUB_DISTRIB])
        \\ simp[Once (GSYM WORD_NEG_MUL),word_2comp_n2w,dimword_def,word_add_n2w]
        \\ qabbrev_tac `kk = Num (ABS i) MOD 18446744073709551616`
        \\ `kk < 18446744073709551616` by fs [Abbr `kk`]
        \\ `kk MOD 4294967296 <> 0` by
         (unabbrev_all_tac
          \\ qmatch_goalsub_abbrev_tac`_ MOD A MOD B`
          \\ `A = B * B ∧ 0 < B` by fs[Abbr`A`,Abbr`B`]
          \\ asm_rewrite_tac []
          \\ asm_simp_tac std_ss [MOD_MULT_MOD])
        \\ Cases_on `kk = 0` \\ fs []
        \\ once_rewrite_tac [EQ_SYM_EQ]
        \\ `0n < 4294967296` by EVAL_TAC
        \\ drule0 DIVISION
        \\ disch_then (qspec_then `kk` strip_assume_tac)
        \\ rfs [] \\ clean_tac
        \\ qpat_x_assum `kk = _` (fn th => once_rewrite_tac [th])
        \\ once_rewrite_tac [MULT_COMM] \\ fs [DIV_MULT]
        \\ qmatch_goalsub_abbrev_tac`A - _`
        \\ qmatch_goalsub_abbrev_tac`B * _`
        \\ `A − (B * (kk DIV B) + kk MOD B) =
            B * (B - 1) + B − (B * (kk DIV B) + kk MOD B)` by
                 fs [Abbr `B`,Abbr `A`] \\ asm_rewrite_tac []
        \\ `B * (B - 1) + B − (B * (kk DIV B) + kk MOD B) =
            (B - 1 − (kk DIV B)) * B + (B - kk MOD B)` by
            (fs [LEFT_SUB_DISTRIB,RIGHT_SUB_DISTRIB]
             \\ rewrite_tac [SUB_PLUS]
             \\ `B ** 2 − B + B − B * (kk DIV B) − kk MOD B =
                 B ** 2 − B − B * (kk DIV B) + B − kk MOD B` by
              (`B * (kk DIV B) <= B * B − B` by
                 (match_mp_tac WordFromInt_DIV_LEMMA
                  \\ fs [Abbr `B`,Abbr `A`])
               \\ fs [Abbr `B`,Abbr `A`]) \\ asm_rewrite_tac []
             \\ `kk MOD B < B` by simp [Abbr `B`]
             \\ pop_assum mp_tac
             \\ rpt (pop_assum kall_tac) \\ decide_tac)
        \\ asm_rewrite_tac []
        \\ `0 < B` by fs [Abbr `B`]
        \\ simp [DIV_MULT]
        \\ `8589934591 = B + (B-1)` by fs [Abbr `B`]
        \\ asm_rewrite_tac []
        \\ `B + (B − 1) − kk DIV B = B + ((B − 1) − kk DIV B)` by
           (`kk DIV B < B /\ kk MOD B < B`
                  by fs [Abbr `B`,Abbr `A`,DIV_LT_X]
            \\ fs [Abbr `B`,Abbr `A`])
        \\ asm_rewrite_tac []
        \\ asm_simp_tac std_ss [ADD_MODULUS]
        \\ rewrite_tac [GSYM SUB_PLUS]
        \\ once_rewrite_tac [EQ_SYM_EQ]
        \\ simp [])
      \\ strip_tac \\ fs []
      \\ fs [consume_space_def,LENGTH_n2mw_1]
      \\ rveq \\ fs []
      \\ strip_tac \\ conj_tac THEN1 rw []
      \\ `Word64 (- n2w (Num (ABS i))) = Word64 (i2w i)` by
            (Cases_on `i` \\ fs [integer_wordTheory.i2w_def,Num_ABS_AND])
      \\ fs [FAPPLY_FUPDATE_THM]
      \\ qhdtm_x_assum `limits_inv` mp_tac
      \\ simp[limits_inv_def,FLOOKUP_UPDATE]
      )
QED

Finalise assign_WordFromInt;

val _ = augment_srw_ss [rewrites [compiler_tag_mask_i2w]];

Theorem assign_WordTest[allow_rebind]:
  (∃ws test. op = WordOp (WordTest ws test)) ==> ^assign_thm_goal
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
  \\ gvs [oneline do_word_app_def,AllCaseEqs(),allowed_op_def]
  \\ fs [LENGTH_EQ_2] \\ clean_tac \\ fs [ZIP]
  \\ fs [LENGTH_EQ_2] \\ clean_tac \\ fs [ZIP]
  \\ drule_at (Pos last) memory_rel_Number_IMP \\ simp []
  \\ (impl_tac >- (gvs [small_int_def,good_dimindex_def,dimword_def] \\ intLib.COOPER_TAC))
  \\ drule memory_rel_tl \\ strip_tac
  \\ drule_at (Pos last) memory_rel_Number_IMP \\ simp []
  \\ (impl_tac >- (gvs [small_int_def,good_dimindex_def,dimword_def] \\ intLib.COOPER_TAC))
  \\ rpt strip_tac \\ gvs []
  \\ fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF]
  \\ simp [assign_def,wordSemTheory.evaluate_def,
           wordSemTheory.get_var_imm_def,
           asmTheory.word_cmp_def]
  \\ ‘(Smallnum n1' = Smallnum n2' :α word) ⇔  (n1' = n2')’ by
    gvs [Smallnum_def,INT_EQ_NUM_LEMMA,dimword_def,good_dimindex_def]
  \\ ‘(Smallnum n1' <+ Smallnum n2' :α word) ⇔  (n1' < n2')’ by
    gvs [Smallnum_def,INT_EQ_NUM_LEMMA,dimword_def,good_dimindex_def,WORD_LO]
  \\ ‘(Smallnum n1' <=+ Smallnum n2' :α word) ⇔  (n1' <= n2')’ by
    gvs [Smallnum_def,INT_EQ_NUM_LEMMA,dimword_def,good_dimindex_def,WORD_LS]
  \\ simp [] \\ fs [GSYM WORD_NOT_LOWER]
  \\ IF_CASES_TAC \\ gvs [wordSemTheory.word_exp_def,wordSemTheory.set_var_def]
  \\ fs [] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
  \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
  \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [])
QED

Theorem word_exp_set_var_ShiftVar:
   word_exp (set_var v (Word (w:'a word)) t) (ShiftVar (dimindex(:'a)) sow v n) =
    OPTION_MAP Word (case sow of Lsl => SOME (w << n)
                         | Lsr => SOME (w >>> n)
                         | Asr => SOME (w >> n)
                         | Ror => SOME (word_ror w n))
Proof
  simp [Once word_exp_ShiftVar_bits]
  \\ eval_tac \\ fs [lookup_insert] \\ fs []
QED

val _ = augment_srw_ss [rewrites [compiler_Smallnum_i2w]];

Theorem assign_WordOpW8:
  (∃opw. op = WordOp (WordOpw W8 opw)) ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app,oneline do_word_app_def,allowed_op_def]
  \\ every_case_tac \\ fs[]
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ clean_tac
  \\ fs[state_rel_thm] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ qhdtm_x_assum`$some`mp_tac
  \\ DEEP_INTRO_TAC some_intro \\ fs[]
  \\ strip_tac \\ clean_tac
  \\ qmatch_asmsub_rename_tac`[Number (&w2n w1); Number (&w2n w2)]`
  \\ `small_int (dimindex (:'a)) (&w2n w1) ∧ small_int (dimindex (:'a)) (&w2n w2)`
  by ( simp[small_int_w2n] )
  \\ imp_res_tac memory_rel_Number_IMP
  \\ imp_res_tac memory_rel_tl
  \\ imp_res_tac memory_rel_Number_IMP
  \\ qhdtm_x_assum`memory_rel`kall_tac
  \\ ntac 2 (first_x_assum(qspec_then`ARB`kall_tac))
  \\ fs[wordSemTheory.get_vars_def]
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ simp[assign_def] \\ eval_tac
  \\ fs[wordSemTheory.get_var_def]
  \\ Cases_on`opw` \\ simp[] \\ eval_tac \\ fs[lookup_insert,option_le_max_right]
  >- (
    conj_tac >- rw[]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs[]
    \\ match_mp_tac memory_rel_And \\ fs[])
  >- (
    conj_tac >- rw[]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs[]
    \\ match_mp_tac memory_rel_Or \\ fs[] )
  >- (
    conj_tac >- rw[]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs[]
    \\ match_mp_tac memory_rel_Xor \\ fs[] )
  >- (
    ‘(dimindex (:α) - 9) MOD dimword (:α) = dimindex (:α) - 9’ by
       fs [good_dimindex_def, dimword_def]
    \\ simp []
    \\ conj_tac >- simp [lookup_insert]
    \\ conj_tac >- rw [lookup_insert]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs[]
    \\ qmatch_goalsub_abbrev_tac`Word w`
    \\ qmatch_goalsub_abbrev_tac`Number i`
    \\ `w = Smallnum i`
    by (
      unabbrev_all_tac
      \\ qmatch_goalsub_rename_tac`w2n (w1 + w2)`
      \\ simp[Smallnum_i2w,integer_wordTheory.i2w_def]
      \\ simp[WORD_MUL_LSL]
      \\ ONCE_REWRITE_TAC[GSYM n2w_w2n]
      \\ REWRITE_TAC[w2n_lsr]
      \\ simp[word_mul_n2w,word_add_n2w]
      \\ Cases_on`w1` \\ Cases_on`w2` \\ fs[word_add_n2w]
      \\ fs[good_dimindex_def,dimword_def,GSYM LEFT_ADD_DISTRIB]
      \\ qmatch_goalsub_abbrev_tac`(a * b) MOD f DIV d`
      \\ qspecl_then[`a * b`,`d`,`f DIV d`]mp_tac (GSYM DIV_MOD_MOD_DIV)
      \\ simp[Abbr`a`,Abbr`d`,Abbr`f`] \\ disch_then kall_tac
      \\ qmatch_goalsub_abbrev_tac`d * b DIV f`
      \\ `d * b = (b * (d DIV f)) * f`
      by simp[Abbr`d`,Abbr`f`]
      \\ pop_assum SUBST_ALL_TAC
      \\ qspecl_then[`f`,`b * (d DIV f)`]mp_tac MULT_DIV
      \\ (impl_tac >- simp[Abbr`f`])
      \\ disch_then SUBST_ALL_TAC
      \\ simp[Abbr`d`,Abbr`f`]
      \\ qmatch_goalsub_abbrev_tac`a * (b MOD q)`
      \\ qspecl_then[`a`,`b`,`q`]mp_tac MOD_COMMON_FACTOR
      \\ (impl_tac >- simp[Abbr`a`,Abbr`q`])
      \\ disch_then SUBST_ALL_TAC
      \\ simp[Abbr`a`,Abbr`q`])
    \\ pop_assum SUBST_ALL_TAC
    \\ match_mp_tac IMP_memory_rel_Number
    \\ fs[]
    \\ fs[Abbr`i`,small_int_def]
    \\ qmatch_goalsub_rename_tac`w2n w`
    \\ Q.ISPEC_THEN`w`mp_tac w2n_lt
    \\ fs[good_dimindex_def,dimword_def] )
  \\ ‘(dimindex (:α) - 9) MOD dimword (:α) = dimindex (:α) - 9’ by
     fs [good_dimindex_def, dimword_def]
  \\ simp []
  \\ conj_tac >- simp [lookup_insert]
  \\ conj_tac >- rw [lookup_insert]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs[]
  \\ qmatch_goalsub_abbrev_tac`Word w`
  \\ qmatch_goalsub_abbrev_tac`Number i`
  \\ `w = Smallnum i`
  by (
    unabbrev_all_tac
    \\ qmatch_goalsub_rename_tac`w2n (w1 + -1w * w2)`
    \\ simp[Smallnum_i2w,integer_wordTheory.i2w_def]
    \\ simp[WORD_MUL_LSL]
    \\ ONCE_REWRITE_TAC[GSYM n2w_w2n]
    \\ REWRITE_TAC[w2n_lsr]
    \\ simp[word_mul_n2w,word_add_n2w]
    \\ REWRITE_TAC[WORD_SUB_INTRO,WORD_MULT_CLAUSES]
    \\ Cases_on`w1` \\ Cases_on`w2`
    \\ REWRITE_TAC[addressTheory.word_arith_lemma2]
    \\ reverse(rw[]) \\ fs[NOT_LESS,GSYM LEFT_SUB_DISTRIB,GSYM RIGHT_SUB_DISTRIB]
    >- (
      `2 * ((n - n') * 2 ** (dimindex (:'a) - 9)) =
       (2 * (n - n')) * 2 ** (dimindex (:'a) - 9)` by simp []
      \\ pop_assum SUBST_ALL_TAC
      \\ `2 ** 9 * 2 ** (dimindex (:'a) - 9) = dimword (:'a)` by
           fs [dimword_def, good_dimindex_def, GSYM EXP_ADD]
      \\ `2 * (n - n') < 2 ** 9` by simp []
      \\ `(2 * (n - n')) * 2 ** (dimindex (:'a) - 9) < dimword (:'a)` by
           (qpat_x_assum `2 ** 9 * _ = dimword (:'a)` (fn th => rewrite_tac [GSYM th])
            \\ fs [LT_MULT_RCANCEL])
      \\ simp []
      \\ `2 * ((n - n') * 2 ** (dimindex (:'a) - 9)) =
           (2 * (n - n')) * 2 ** (dimindex (:'a) - 9)` by simp []
      \\ pop_assum SUBST1_TAC
      \\ `0 < 2 ** (dimindex (:'a) - 9)` by simp []
      \\ simp [MULT_DIV] )
    \\ simp[word_2comp_n2w]
    \\ qmatch_goalsub_abbrev_tac`(2 * (b * d)) MOD f`
    \\ qmatch_goalsub_abbrev_tac`f - y MOD f`
    \\ `f = d * 2**9`
    by (
      unabbrev_all_tac
      \\ fs[dimword_def,good_dimindex_def] )
    \\ qunabbrev_tac`f`
    \\ pop_assum SUBST_ALL_TAC
    \\ fs[]
    \\ qmatch_goalsub_abbrev_tac`m MOD (512 * d) DIV d`
    \\ qspecl_then[`m`,`d`,`512`]mp_tac DIV_MOD_MOD_DIV
    \\ impl_tac >- simp[Abbr`d`] \\ simp[]
    \\ disch_then(CHANGED_TAC o SUBST_ALL_TAC o SYM)
    \\ qspecl_then[`512 * d`,`(m DIV d) MOD 512`]mp_tac LESS_MOD
    \\ impl_tac
    >- (
      qspecl_then[`m DIV d`,`512`]mp_tac MOD_LESS
      \\ impl_tac >- simp[]
      \\ `512 < 512 * d`
      by (
        simp[Abbr`d`,ONE_LT_EXP]
        \\ fs[good_dimindex_def] )
      \\ decide_tac )
    \\ disch_then (CHANGED_TAC o SUBST_ALL_TAC)
    \\ fs[Abbr`m`,Abbr`y`]
    \\ qspecl_then[`d`,`2 * b`,`512`]mp_tac MOD_COMMON_FACTOR
    \\ impl_tac >- simp[Abbr`d`] \\ simp[]
    \\ disch_then(CHANGED_TAC o SUBST_ALL_TAC o SYM)
    \\ qmatch_assum_rename_tac`n2 < 256n`
    \\ `n2 <= 256` by simp[]
    \\ drule0 LESS_EQ_ADD_SUB
    \\ qmatch_assum_rename_tac`n1 < n2`
    \\ disch_then(qspec_then`n1`(CHANGED_TAC o SUBST_ALL_TAC))
    \\ REWRITE_TAC[LEFT_ADD_DISTRIB]
    \\ simp[LEFT_SUB_DISTRIB,Abbr`b`]
    \\ `2 * (d * n2) - 2 * (d * n1) = (2 * d) * (n2 - n1)` by simp[]
    \\ pop_assum (CHANGED_TAC o SUBST_ALL_TAC)
    \\ `512 * d - 2 * d * (n2 - n1) = (512 - 2 * (n2 - n1)) * d` by simp[]
    \\ pop_assum (CHANGED_TAC o SUBST_ALL_TAC)
    \\ `0 < d` by simp[Abbr`d`]
    \\ drule0 MULT_DIV
    \\ disch_then(CHANGED_TAC o (fn th => REWRITE_TAC[th]))
    \\ simp[])
  \\ pop_assum SUBST_ALL_TAC
  \\ match_mp_tac IMP_memory_rel_Number
  \\ fs[]
  \\ fs[Abbr`i`,small_int_def]
  \\ qmatch_goalsub_rename_tac`w2n w`
  \\ Q.ISPEC_THEN`w`mp_tac w2n_lt
  \\ fs[good_dimindex_def,dimword_def]
QED

val assign_WordOp64 =
  ``assign c n l dest (WordOp (WordOpw W64 opw)) [e1; e2] names_opt``
  |> SIMP_CONV (srw_ss()) [assign_def]

Theorem mw2n_2_IMP:
   mw2n [w1;w2:'a word] = n ==>
    w2 = n2w (n DIV dimword (:'a)) /\
    w1 = n2w n
Proof
  fs [multiwordTheory.mw2n_def] \\ rw []
  \\ Cases_on `w1` \\ Cases_on `w2` \\ fs []
  \\ once_rewrite_tac [ADD_COMM]
  \\ asm_simp_tac std_ss [DIV_MULT]
QED

Theorem IMP_mw2n_2:
   Abbrev (x2 = (63 >< 32) (n2w n:word64)) /\
    Abbrev (x1 = (31 >< 0) (n2w n:word64)) /\
    n < dimword (:64) /\ dimindex (:'a) = 32 ==>
    mw2n [x1;x2:'a word] = n
Proof
  fs [markerTheory.Abbrev_def]
  \\ rw [multiwordTheory.mw2n_def]
  \\ fs [word_extract_n2w]
  \\ fs [bitTheory.BITS_THM2,dimword_def]
  \\ fs [DIV_MOD_MOD_DIV]
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ simp [Once (MATCH_MP DIVISION (DECIDE ``0 < 4294967296n``))]
QED

Theorem evaluate_WordOp64_on_32:
   !l.
    dimindex (:'a) = 32 ==>
    ?w27 w29.
      evaluate
       (WordOp64_on_32 opw,
        (t:('a,'c,'ffi) wordSem$state) with
        locals :=
          insert 23 (Word ((31 >< 0) c''))
            (insert 21 (Word ((63 >< 32) c''))
               (insert 13 (Word ((31 >< 0) c'))
                  (insert 11 (Word ((63 >< 32) c')) l)))) =
     (NONE,t with locals :=
       insert 31 (Word ((63 >< 32) (opw_lookup opw c' c'')))
        (insert 33 (Word ((31 >< 0) (opw_lookup opw (c':word64) (c'':word64))))
          (insert 27 w27
            (insert 29 w29
              (insert 23 (Word ((31 >< 0) c''))
                (insert 21 (Word ((63 >< 32) c''))
                  (insert 13 (Word ((31 >< 0) c'))
                    (insert 11 (Word ((63 >< 32) c')) l))))))))
Proof
  Cases_on `opw`
  \\ fs [WordOp64_on_32_def,closSemTheory.opw_lookup_def,list_Seq_def]
  \\ eval_tac \\ fs [lookup_insert]
  \\ fs [wordSemTheory.state_component_equality]
  \\ fs [GSYM WORD_EXTRACT_OVER_BITWISE]
  THEN1 metis_tac []
  THEN1 metis_tac []
  THEN1 metis_tac []
  \\ fs [wordSemTheory.inst_def,wordSemTheory.get_vars_def,lookup_insert,
         wordSemTheory.set_var_def,wordSemTheory.get_var_def,word_add_carry_def]
  THEN1
   (qpat_abbrev_tac `c1 <=> dimword (:α) ≤
                    w2n ((31 >< 0) c') + w2n ((31 >< 0) c'')`
    \\ qpat_abbrev_tac `c2 <=> dimword (:α) ≤ _`
    \\ rpt strip_tac
    \\ qexists_tac `(Word 0w)`
    \\ qexists_tac `(Word (if c2 then 1w else 0w))`
    \\ simp [Once (Q.SPECL [`29`,`31`] insert_insert)]
    \\ simp [Once (Q.SPECL [`29`,`29`] insert_insert)]
    \\ simp [Once (Q.SPECL [`29`,`33`] insert_insert)]
    \\ simp [Once (Q.SPECL [`29`,`29`] insert_insert)]
    \\ simp [Once (Q.SPECL [`29`,`27`] insert_insert)]
    \\ simp [Once (Q.SPECL [`29`,`29`] insert_insert)]
    \\ qmatch_goalsub_abbrev_tac `insert 31 (Word w1)`
    \\ qmatch_goalsub_abbrev_tac `insert 33 (Word w2)`
    \\ qsuff_tac `w1 = (63 >< 32) (c' + c'') /\ w2 = (31 >< 0) (c' + c'')`
    THEN1 fs []
    \\ Cases_on `c'`
    \\ Cases_on `c''`
    \\ fs [word_add_n2w]
    \\ fs [word_extract_n2w]
    \\ fs [bitTheory.BITS_THM2,dimword_def] \\ rfs []
    \\ unabbrev_all_tac
    \\ reverse conj_tac
    THEN1 (once_rewrite_tac [GSYM n2w_mod] \\ fs [dimword_def])
    \\ strip_assume_tac (Q.SPEC `n` (MATCH_MP DIVISION (DECIDE ``0 < 4294967296n``))
                         |> ONCE_REWRITE_RULE [CONJ_COMM])
    \\ pop_assum (fn th => ONCE_REWRITE_TAC [th])
    \\ simp_tac std_ss [DIV_MULT,DIV_MOD_MOD_DIV
          |> Q.SPECL [`m`,`4294967296`,`4294967296`]
          |> SIMP_RULE std_ss [] |> GSYM,MOD_MULT]
    \\ strip_assume_tac (Q.SPEC `n'` (MATCH_MP DIVISION (DECIDE ``0 < 4294967296n``))
                         |> ONCE_REWRITE_RULE [CONJ_COMM])
    \\ pop_assum (fn th => ONCE_REWRITE_TAC [th])
    \\ simp_tac std_ss [DIV_MULT,DIV_MOD_MOD_DIV
          |> Q.SPECL [`m`,`4294967296`,`4294967296`]
          |> SIMP_RULE std_ss [] |> GSYM,MOD_MULT]
    \\ once_rewrite_tac [DECIDE ``(m1+n1)+(m2+n2)=m1+(m2+(n1+n2:num))``]
    \\ simp_tac std_ss [ADD_DIV_ADD_DIV]
    \\ simp [dimword_def]
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ AP_TERM_TAC \\ AP_TERM_TAC
    \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ fs [DIV_EQ_X]
    \\ CASE_TAC \\ fs []
    \\ `n MOD 4294967296 < 4294967296` by fs []
    \\ `n' MOD 4294967296 < 4294967296` by fs []
    \\ decide_tac)
  \\ qpat_abbrev_tac `c1 <=> dimword (:α) ≤ _ + (_ + 1)`
  \\ qpat_abbrev_tac `c2 <=> dimword (:α) ≤ _`
  \\ rpt strip_tac
  \\ qexists_tac `(Word (¬(63 >< 32) c''))`
  \\ qexists_tac `(Word (if c2 then 1w else 0w))`
  \\ simp [Once (Q.SPECL [`29`,`31`] insert_insert)]
  \\ simp [Once (Q.SPECL [`29`,`31`] insert_insert),insert_shadow]
  \\ simp [(Q.SPECL [`29`,`33`] insert_insert)]
  \\ simp [(Q.SPECL [`27`,`33`] insert_insert)]
  \\ simp [(Q.SPECL [`29`,`33`] insert_insert)]
  \\ simp [(Q.SPECL [`29`,`27`] insert_insert),insert_shadow]
  \\ qmatch_goalsub_abbrev_tac `insert 31 (Word w1)`
  \\ qmatch_goalsub_abbrev_tac `insert 33 (Word w2)`
  \\ qsuff_tac `w1 = (63 >< 32) (c' - c'') /\ w2 = (31 >< 0) (c' - c'')`
  THEN1 fs [insert_shadow]
  \\ qabbrev_tac `x2 = (63 >< 32) c'`
  \\ qabbrev_tac `x1 = (31 >< 0) c'`
  \\ qabbrev_tac `y2 = (63 >< 32) c''`
  \\ qabbrev_tac `y1 = (31 >< 0) c''`
  \\ `?c. mw_sub [x1;x2] [y1;y2] T = ([w2;w1],c)` by
    (fs [multiwordTheory.mw_sub_def,multiwordTheory.single_sub_def,
         multiwordTheory.single_add_def,EVAL ``multiword$b2w T``]
     \\ fs [GSYM word_add_n2w,multiwordTheory.b2n_def]
     \\ Cases_on `c1` \\ fs [multiwordTheory.b2w_def,multiwordTheory.b2n_def])
  \\ drule0 multiwordTheory.mw_sub_lemma
  \\ fs [multiwordTheory.b2n_def,multiwordTheory.dimwords_def]
  \\ strip_tac
  \\ drule0 (DECIDE ``m+(w+r)=k ==> w = k-m-r:num``)
  \\ strip_tac
  \\ drule0 mw2n_2_IMP
  \\ simp []
  \\ disch_then kall_tac
  \\ pop_assum kall_tac
  \\ Cases_on `c'`
  \\ Cases_on `c''`
  \\ `mw2n [x1;x2] = n /\ mw2n [y1;y2] = n'` by
    (rw [] \\ match_mp_tac IMP_mw2n_2 \\ fs [] \\ fs [markerTheory.Abbrev_def])
  \\ fs [] \\ ntac 2 (pop_assum kall_tac)
  \\ rewrite_tac [GSYM (SIMP_CONV (srw_ss()) [] ``w:'a word-x``)]
  \\ rewrite_tac [word_sub_def,word_2comp_n2w,word_add_n2w]
  \\ fs [word_extract_n2w]
  \\ fs [bitTheory.BITS_THM2,dimword_def] \\ rfs []
  \\ fs [DIV_MOD_MOD_DIV]
  \\ once_rewrite_tac [
      Q.SPECL [`4294967296`,`4294967296`] MOD_MULT_MOD
      |> SIMP_RULE std_ss [] |> GSYM]
  \\ qsuff_tac `(n + 18446744073709551616 − (n' + 18446744073709551616 * b2n c))
        MOD 18446744073709551616 =
      (n + 18446744073709551616 − n') MOD 18446744073709551616`
  THEN1 fs []
  \\ Cases_on `c` \\ fs [multiwordTheory.b2n_def]
  \\ `n' <= n` by decide_tac
  \\ fs [LESS_EQ_EXISTS]
QED

Theorem IMP_encode_header_NOT_NONE:
  arch_width_bits c.arch_width = dimindex (:'a) ∧
  dimindex (:'a) = 32 ∧ 1 < c.len_size ∧ 1 < 30 − c.len_size ⇒
  encode_header c 3 2 ≠ (NONE:num option)
Proof
  gvs [encode_header_def,dimword_def]
QED

Theorem assign_WordOpW64:
  (∃opw. op = WordOp (WordOpw W64 opw)) ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app,oneline do_word_app_def,allowed_op_def]
  \\ gvs [AllCaseEqs()]
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ clean_tac
  \\ rename [‘get_vars [e1;e2] s.locals’]
  \\ simp[state_rel_thm] \\ eval_tac
  \\ fs[state_rel_thm,option_le_max_right] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ fs[wordSemTheory.get_vars_def]
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ drule0 memory_rel_Word64_IMP
  \\ imp_res_tac memory_rel_tl
  \\ drule0 memory_rel_Word64_IMP
  \\ qhdtm_x_assum`memory_rel`kall_tac
  \\ simp[] \\ ntac 2 strip_tac
  \\ clean_tac
  \\ simp [assign_WordOp64(*assign_def*)]
  \\ Cases_on `dimindex (:'a) = 64` \\ simp [] >-
   (TOP_CASE_TAC \\ fs []
    >- (conj_tac >- metis_tac[backendPropsTheory.option_le_trans,consume_space_stack_max] >>
        strip_tac >> spose_not_then strip_assume_tac >>
        fs[encode_header_def,state_rel_def,good_dimindex_def,limits_inv_def,dimword_def,
           memory_rel_def,heap_in_memory_store_def,consume_space_def] >> rfs[NOT_LESS] >>
        rveq >> rfs[] >>
        `2 <= 62 - c.len_size` by simp[] >>
        dxrule_then (strip_assume_tac o GSYM) LESS_EQ_ADD_EXISTS >>
        fs[EXP_ADD] >> assume_tac bitTheory.TWOEXP_NOT_ZERO >>
        pop_assum(qspec_then `p` assume_tac) >>
        Cases_on `2 ** p` >> fs[])
    \\ clean_tac
    \\ eval_tac
    \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
    \\ full_simp_tac std_ss [GSYM wordSemTheory.get_var_def]
    \\ rpt_drule0 get_var_get_real_addr_lemma
    \\ qpat_x_assum `get_var (adjust_var e2) t =
         SOME (Word (get_addr c ptr (Word 0w)))` assume_tac
    \\ rpt_drule0 get_var_get_real_addr_lemma
    \\ qpat_abbrev_tac`sow = opw_CASE opw _ _ _ _ _`
    \\ qpat_abbrev_tac`sw = _ sow _ _ _ _ _`
    \\ qpat_abbrev_tac `w64 = opw_lookup opw _ _`
    \\ `sw = SOME (w2w w64)`
    by (
      simp[Abbr`sow`,Abbr`sw`,Abbr`w64`]
      \\ Cases_on`opw` \\ simp[]
      \\ simp[WORD_w2w_EXTRACT,WORD_EXTRACT_OVER_BITWISE]
      \\ fs[good_dimindex_def,WORD_EXTRACT_OVER_ADD,WORD_EXTRACT_OVER_MUL]
      \\ qpat_abbrev_tac`neg1 = (_ >< _) (-1w)`
      \\ `neg1 = -1w`
      by ( srw_tac[wordsLib.WORD_BIT_EQ_ss][Abbr`neg1`] )
      \\ pop_assum SUBST_ALL_TAC
      \\ simp[] )
    \\ qunabbrev_tac`sw` \\ pop_assum SUBST_ALL_TAC
    \\ simp[wordSemTheory.get_var_def,lookup_insert]
    \\ rpt strip_tac
    \\ assume_tac (GEN_ALL evaluate_WriteWord64)
    \\ SEP_I_TAC "evaluate"
    \\ pop_assum mp_tac \\ fs [join_env_locals_def]
    \\ fs [wordSemTheory.get_var_def,lookup_insert]
    \\ fs [inter_insert_ODD_adjust_set_alt]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ disch_then drule0
    \\ impl_tac THEN1 fs [consume_space_def]
    \\ strip_tac \\ fs []
    \\ fs[FAPPLY_FUPDATE_THM]
    \\ fs [consume_space_def]
    \\ rveq \\ fs [code_oracle_rel_def,FLOOKUP_UPDATE]
    \\ conj_tac THEN1 (rw [] \\ fs [])
    \\ `w2w ((w2w w64):'a word) = w64` by
      (Cases_on `w64` \\ fs [w2w_def,dimword_def])
    \\ fs []
    \\ match_mp_tac (GEN_ALL memory_rel_less_space) \\ fs []
    \\ asm_exists_tac \\ fs [])
  \\ TOP_CASE_TAC \\ fs []
  >- (conj_tac >- metis_tac[backendPropsTheory.option_le_trans,consume_space_stack_max]
      \\ qsuff_tac ‘F’ \\ simp []
      \\ pop_assum mp_tac \\ rewrite_tac []
      \\ irule IMP_encode_header_NOT_NONE
      \\ gvs [good_dimindex_def,limits_inv_def,state_rel_def,
              memory_rel_def,heap_in_memory_store_def,consume_space_def]
      \\ CCONTR_TAC
      \\ ‘c.len_size = 1’ by decide_tac
      \\ qpat_x_assum ‘decode_length _ _ = 2w’ mp_tac
      \\ simp [decode_length_def,make_header_def]
      \\ EVAL_TAC \\ simp [dimword_def]
      \\ EVAL_TAC \\ simp [dimword_def])
  \\ `dimindex (:'a) = 32` by rfs [good_dimindex_def] \\ fs [] \\ rveq
  \\ eval_tac
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
    \\ full_simp_tac std_ss [GSYM wordSemTheory.get_var_def]
  \\ full_simp_tac std_ss [GSYM wordSemTheory.get_var_def]
  \\ qpat_x_assum `get_var (adjust_var e1) t =
       SOME (Word (get_addr c _ (Word 0w)))` assume_tac
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var (adjust_var e2) t =
       SOME (Word (get_addr c _ (Word 0w)))` assume_tac
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_abbrev_tac `t1 = t with locals := insert 15 _ t.locals`
  \\ `get_var (adjust_var e2) t1 =
       SOME (Word (get_addr c ptr (Word 0w)))` by
   (fs [wordSemTheory.get_var_def,Abbr`t1`,lookup_insert]
    \\ rw [] \\ `EVEN 15` by metis_tac [EVEN_adjust_var] \\ fs [])
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ fs [Abbr`t1`]
  \\ fs [WORD_MUL_LSL]
  \\ ntac 8 (once_rewrite_tac [list_Seq_def] \\ eval_tac \\ fs [lookup_insert])
  \\ assume_tac (GEN_ALL evaluate_WordOp64_on_32) \\ rfs []
  \\ SEP_I_TAC "evaluate"
  \\ fs [] \\ pop_assum kall_tac
  \\ rpt strip_tac
  \\ assume_tac (GEN_ALL evaluate_WriteWord64_on_32)
  \\ SEP_I_TAC "evaluate"
  \\ pop_assum mp_tac \\ fs [join_env_locals_def]
  \\ fs [wordSemTheory.get_var_def,lookup_insert]
  \\ fs [inter_insert_ODD_adjust_set_alt]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ disch_then drule0
  \\ disch_then (qspec_then `opw_lookup opw w1 w2` mp_tac)
  \\ simp []
  \\ impl_tac
  THEN1 (fs [consume_space_def,good_dimindex_def] \\ rw [] \\ fs [])
  \\ strip_tac \\ fs []
  \\ fs[FAPPLY_FUPDATE_THM]
  \\ fs [consume_space_def]
  \\ rveq \\ fs [] \\ rw [] \\ fs [code_oracle_rel_def,FLOOKUP_UPDATE]
QED

Theorem assign_WordShiftW8:
  (∃sh n. op = WordOp (WordShift W8 sh n)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ imp_res_tac state_rel_arch_width \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ asm_rewrite_tac [] \\ pop_assum kall_tac
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t NONE locs` kall_tac \\ strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app,oneline do_word_app_def,allowed_op_def]
  \\ every_case_tac \\ fs[]
  \\ clean_tac
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ qhdtm_x_assum`$some`mp_tac
  \\ DEEP_INTRO_TAC some_intro \\ fs[]
  \\ strip_tac \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ simp[state_rel_thm] \\ eval_tac
  \\ fs[state_rel_thm] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs[] \\ strip_tac
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ clean_tac \\ fs[]
  \\ qmatch_asmsub_rename_tac`Number (&w2n ww)`
  \\ `small_int (dimindex (:α)) (&w2n ww)` by simp[small_int_w2n]
  \\ rpt_drule0 memory_rel_Number_IMP
  \\ strip_tac \\ clean_tac
  \\ imp_res_tac get_vars_1_imp
  \\ fs[wordSemTheory.get_var_def]
  \\ simp[assign_def]
  \\ BasicProvers.CASE_TAC \\ eval_tac
  (* Helper theorems used to simplify goals *)
  \\ ‘(dimindex (:α) - 9) MOD dimword (:α) = dimindex (:α) - 9’ by
    fs [good_dimindex_def, dimword_def]
  \\ ‘∀n. (dimindex (:α) − 9 + MIN n 8) MOD dimword (:α)
          = (dimindex (:α) − 9 + MIN n 8)’ by
    fs [MIN_DEF, good_dimindex_def, dimword_def]
  \\ ‘∀n. (MIN n 8 + 1) MOD dimword (:α) = (MIN n 8 + 1)’ by
    fs [MIN_DEF, good_dimindex_def, dimword_def]
  \\ ‘(dimindex (:α) − 8) MOD dimword (:α) = dimindex (:α) − 8’ by
    fs [good_dimindex_def, dimword_def]
  \\ ‘1 MOD dimword (:α) = 1 ∧ 1 < dimindex (:α)’ by
    fs [good_dimindex_def, dimword_def]
  \\ ‘2 MOD dimword (:α) = 2 ∧ 2 < dimindex (:α)’ by
    fs [good_dimindex_def, dimword_def]
  \\ fs []
  >- (
    IF_CASES_TAC
    >- (fs[good_dimindex_def,dimword_def,MIN_DEF] \\ rfs[])
    \\ simp[lookup_insert,option_le_max_right]
    \\ conj_tac >- rw[]
    \\ pop_assum kall_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert
    \\ qmatch_goalsub_abbrev_tac`Number i`
    \\ qmatch_goalsub_abbrev_tac`Word w`
    \\ `small_int (dimindex (:'a)) i`
    by (
      simp[Abbr`i`,small_int_def,WORD_MUL_LSL]
      \\ qmatch_goalsub_rename_tac`z * n2w _`
      \\ Cases_on`z` \\ fs[word_mul_n2w]
      \\ fs[good_dimindex_def,dimword_def]
      \\ qmatch_abbrev_tac`a MOD b < d`
      \\ `b < d` by simp[Abbr`b`,Abbr`d`]
      \\ qspecl_then[`a`,`b`]mp_tac MOD_LESS
      \\ (impl_tac >- simp[Abbr`b`])
      \\ decide_tac )
    \\ `w = Smallnum i`
    by (
      simp[Abbr`w`,Abbr`i`]
      \\ simp[Smallnum_i2w,integer_wordTheory.i2w_def]
      \\ qmatch_goalsub_rename_tac`w2n w`
      \\ qmatch_goalsub_rename_tac`w << n`
      \\ Cases_on`n=0`
      >- (
        simp[]
        \\ match_mp_tac lsl_lsr
        \\ simp[GSYM word_mul_n2w,dimword_def]
        \\ Q.ISPEC_THEN`w`mp_tac w2n_lt
        \\ fs[good_dimindex_def] )
      \\ simp[GSYM word_mul_n2w]
      \\ qspecl_then[`n2w(w2n w)`,`1`]mp_tac WORD_MUL_LSL
      \\ simp[] \\ disch_then (SUBST_ALL_TAC o SYM)
      \\ simp[]
      \\ `9 < dimindex(:'a)` by fs[good_dimindex_def]
      \\ simp[]
      \\ qspecl_then[`n2w(w2n (w<<n))`,`1`]mp_tac WORD_MUL_LSL
      \\ simp[] \\ disch_then (SUBST_ALL_TAC o SYM)
      \\ simp[GSYM w2w_def]
      \\ simp[w2w_LSL]
      \\ IF_CASES_TAC
      \\ simp[MIN_DEF]
      \\ simp[word_lsr_n2w]
      \\ simp[WORD_w2w_EXTRACT]
      \\ simp[WORD_EXTRACT_BITS_COMP]
      \\ `MIN (7 - n) 7 = 7 - n` by simp[MIN_DEF]
      \\ pop_assum SUBST_ALL_TAC
      \\ qmatch_abbrev_tac`_ ((7 >< 0) w << m) = _`
      \\ qispl_then[`7n`,`0n`,`m`,`w`](mp_tac o INST_TYPE[beta|->alpha]) WORD_EXTRACT_LSL2
      \\ impl_tac >- ( simp[Abbr`m`] )
      \\ disch_then SUBST_ALL_TAC
      \\ simp[Abbr`m`]
      \\ simp[WORD_BITS_LSL]
      \\ simp[SUB_LEFT_SUB,SUB_RIGHT_SUB]
      \\ qmatch_goalsub_abbrev_tac`_ -- z`
      \\ `z = 0` by simp[Abbr`z`]
      \\ simp[Abbr`z`]
      \\ simp[WORD_BITS_EXTRACT]
      \\ simp[WORD_EXTRACT_COMP_THM,MIN_DEF] )
    \\ simp[Abbr`w`]
    \\ match_mp_tac IMP_memory_rel_Number
    \\ simp[]
    \\ drule0 memory_rel_tl
    \\ simp_tac std_ss [GSYM APPEND_ASSOC])
  >- (
    IF_CASES_TAC
    >- (fs[good_dimindex_def,MIN_DEF] \\ rfs[])
    \\ simp[lookup_insert,option_le_max_right]
    \\ conj_tac >- rw[]
    \\ pop_assum kall_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert
    \\ qmatch_goalsub_abbrev_tac`Number i`
    \\ qmatch_goalsub_abbrev_tac`Word w`
    \\ `small_int (dimindex (:'a)) i`
    by (
      simp[Abbr`i`,small_int_def]
      \\ qmatch_goalsub_rename_tac`z >>> _`
      \\ Cases_on`z` \\ fs[w2n_lsr]
      \\ fs[good_dimindex_def,dimword_def]
      \\ qmatch_abbrev_tac`a DIV b < d`
      \\ `a < d` by simp[Abbr`a`,Abbr`d`]
      \\ qspecl_then[`b`,`a`]mp_tac (SIMP_RULE std_ss [PULL_FORALL]DIV_LESS_EQ)
      \\ (impl_tac >- simp[Abbr`b`])
      \\ decide_tac )
    \\ `w = Smallnum i`
    by (
      simp[Abbr`w`,Abbr`i`]
      \\ simp[Smallnum_i2w,integer_wordTheory.i2w_def]
      \\ simp[GSYM word_mul_n2w]
      \\ REWRITE_TAC[Once ADD_COMM]
      \\ REWRITE_TAC[GSYM LSR_ADD]
      \\ qmatch_goalsub_rename_tac`w2n w`
      \\ qmatch_goalsub_abbrev_tac`2w * ww`
      \\ `2w * ww = ww << 1` by simp[WORD_MUL_LSL]
      \\ pop_assum SUBST_ALL_TAC
      \\ qspecl_then[`ww`,`1`]mp_tac lsl_lsr
      \\ Q.ISPEC_THEN`w`assume_tac w2n_lt
      \\ impl_tac
      >- ( simp[Abbr`ww`] \\ fs[good_dimindex_def,dimword_def] )
      \\ disch_then SUBST_ALL_TAC
      \\ simp[WORD_MUL_LSL]
      \\ AP_TERM_TAC
      \\ simp[Abbr`ww`]
      \\ simp[w2n_lsr]
      \\ `w2n w < dimword(:'a)`
      by ( fs[good_dimindex_def,dimword_def] )
      \\ simp[GSYM n2w_DIV]
      \\ AP_THM_TAC \\ AP_TERM_TAC
      \\ rw[MIN_DEF] \\ fs[]
      \\ simp[LESS_DIV_EQ_ZERO]
      \\ qmatch_goalsub_rename_tac`2n ** k`
      \\ `2n ** 8 <= 2 ** k`
      by ( simp[logrootTheory.LE_EXP_ISO] )
      \\ `256n ≤ 2 ** k` by metis_tac[EVAL``2n ** 8``]
      \\ `w2n w < 2 ** k` by decide_tac
      \\ simp[LESS_DIV_EQ_ZERO] )
    \\ simp[Abbr`w`]
    \\ match_mp_tac IMP_memory_rel_Number
    \\ simp[]
    \\ drule0 memory_rel_tl
    \\ simp_tac std_ss [GSYM APPEND_ASSOC])
  >- (
    IF_CASES_TAC
    >- (gvs[good_dimindex_def,MIN_DEF])
    \\ simp[lookup_insert,option_le_max_right]
    \\ conj_tac >- rw[]
    \\ ntac 2 (pop_assum kall_tac)
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert
    \\ qmatch_goalsub_abbrev_tac`Number i`
    \\ qmatch_goalsub_abbrev_tac`Word w`
    \\ `small_int (dimindex (:'a)) i` by simp[Abbr`i`]
    \\ `w = Smallnum i`
    by (
      simp[Abbr`w`,Abbr`i`]
      \\ simp[Smallnum_i2w,integer_wordTheory.i2w_def]
      \\ simp[GSYM word_mul_n2w]
      \\ full_simp_tac(srw_ss()++wordsLib.WORD_MUL_LSL_ss)
           [good_dimindex_def,GSYM wordsTheory.w2w_def]
      \\ Cases_on `n' < 8`
      \\ asm_simp_tac(std_ss++wordsLib.WORD_BIT_EQ_ss)
           [MIN_DEF,
            DECIDE ``(32n <= n + 31) = (8 <= n + 7) /\
                     (32n <= n + 30) = (8 <= n + 6) /\
                     (32n <= n + 29) = (8 <= n + 5) /\
                     (32n <= n + 28) = (8 <= n + 4) /\
                     (32n <= n + 27) = (8 <= n + 3) /\
                     (32n <= n + 26) = (8 <= n + 2) /\
                     (32n <= n + 25) = (8 <= n + 1)``,
            DECIDE ``(64n <= n + 63) = (8 <= n + 7) /\
                     (64n <= n + 62) = (8 <= n + 6) /\
                     (64n <= n + 61) = (8 <= n + 5) /\
                     (64n <= n + 60) = (8 <= n + 4) /\
                     (64n <= n + 59) = (8 <= n + 3) /\
                     (64n <= n + 58) = (8 <= n + 2) /\
                     (64n <= n + 57) = (8 <= n + 1)``])
    \\ simp[Abbr`w`]
    \\ match_mp_tac IMP_memory_rel_Number
    \\ simp[]
    \\ drule0 memory_rel_tl
    \\ simp_tac std_ss [GSYM APPEND_ASSOC])
  \\ qmatch_goalsub_rename_tac `ww #>> kk`
  \\ `~(2 ≥ dimindex (:α))` by (fs [good_dimindex_def] \\ fs [])
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [eq_eval,lookup_insert]
  \\ fs [lookup_insert,adjust_var_11,option_le_max_right] \\ rw []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert
  \\ qmatch_goalsub_abbrev_tac`Number i8`
  \\ qmatch_goalsub_abbrev_tac`Word w8`
  \\ `small_int (dimindex (:'a)) i8` by simp[Abbr`i8`]
  \\ qsuff_tac `w8 = Smallnum i8` THEN1
   (rw [] \\ fs []
    \\ match_mp_tac IMP_memory_rel_Number
    \\ simp[] \\ drule0 memory_rel_tl
    \\ simp_tac std_ss [GSYM APPEND_ASSOC])
  \\ simp[Abbr`w8`,Abbr`i8`]
  \\ simp[Smallnum_i2w,integer_wordTheory.i2w_def]
  \\ simp[GSYM word_mul_n2w]
  \\ full_simp_tac(srw_ss()++wordsLib.WORD_MUL_LSL_ss)
       [good_dimindex_def,GSYM wordsTheory.w2w_def]
  THEN
   (simp [fcpTheory.CART_EQ,word_or_def,fcpTheory.FCP_BETA,
         word_lsr_def,word_lsl_def,w2w,word_ror_def]
    \\ once_rewrite_tac
         [METIS_PROVE [] ``b1 /\ 1n <= i /\ c <=>
            b1 /\ 1n <= i /\ (b1 /\ 1n <= i ==> c)``]
    \\ simp [fcpTheory.CART_EQ,word_or_def,fcpTheory.FCP_BETA,
           word_lsr_def,word_lsl_def,w2w,word_ror_def]
    \\ rpt strip_tac
    \\ reverse (Cases_on `1 <= i`) \\ fs []
    THEN1
     (fs [fcpTheory.FCP_BETA] \\ CCONTR_TAC \\ fs []
      \\ `kk MOD 8 < 8` by fs [] \\ decide_tac)
    \\ `kk MOD 8 < 8` by fs []
    \\ simp []
    \\ reverse (Cases_on `i < 9`)
    THEN1
     (simp [fcpTheory.FCP_BETA]
      \\ CCONTR_TAC \\ fs []
      \\ rfs [fcpTheory.FCP_BETA])
    \\ fs []
    \\ `kk MOD 8 < 8` by fs []
    \\ simp [fcpTheory.FCP_BETA]
    \\ qpat_x_assum `1 ≤ i` mp_tac
    \\ simp [Once LESS_EQ_EXISTS] \\ strip_tac
    \\ rfs [] \\ rveq
    \\ `p < 8 /\ kk MOD 8 < 8` by fs []
    \\ once_rewrite_tac [GSYM MOD_PLUS]
    \\ drule0 (DECIDE ``n < 8n ==> n=0 \/ n=1 \/ n=2 \/ n=3 \/
                                  n=4 \/ n=5 \/ n=6 \/ n=7``)
    \\ strip_tac \\ fs []
    \\ drule0 (DECIDE ``n < 8n ==> n=0 \/ n=1 \/ n=2 \/ n=3 \/
                                  n=4 \/ n=5 \/ n=6 \/ n=7``)
    \\ strip_tac \\ fs [w2w])
QED

Theorem evaluate_WordShift64_on_32:
   !l.
    dimindex (:'a) = 32 ==>
      evaluate
       (WordShift64_on_32 sh n,
        (t:('a,'c,'ffi) wordSem$state) with
        locals :=
          (insert 13 (Word ((31 >< 0) c'))
          (insert 11 (Word ((63 >< 32) c')) l))) =
     (NONE,t with locals :=
       insert 31 (Word ((63 >< 32) (shift_lookup sh c' n)))
        (insert 33 (Word ((31 >< 0) (shift_lookup sh (c':word64) n)))
          (insert 13 (Word ((31 >< 0) c'))
            (insert 11 (Word ((63 >< 32) c')) l))))
Proof
  ntac 2 strip_tac \\ Cases_on `sh = Ror`
  THEN1
   (simp [WordShift64_on_32_def] \\ TOP_CASE_TAC
    \\ fs [list_Seq_def] \\ eval_tac
    \\ qpat_assum `dimindex(:'a) = 32`
      (fn th => once_rewrite_tac [GSYM th])
    \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
    \\ fs [eq_eval,lookup_insert]
    \\ fs [lookup_insert]
    \\ qmatch_goalsub_abbrev_tac `insert 31 (Word w31)`
    \\ qmatch_goalsub_abbrev_tac `insert 33 (Word w33)`
    \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ qmatch_goalsub_abbrev_tac `insert 31 (Word w31p)`
    \\ qmatch_goalsub_abbrev_tac `insert 33 (Word w33p)`
    \\ qsuff_tac `w31p = w31 /\ w33p = w33` \\ fs []
    \\ unabbrev_all_tac \\ rveq
    \\ fs [fcpTheory.CART_EQ,word_extract_def,word_bits_def,w2w,word_or_def,w2w,
           fcpTheory.FCP_BETA,word_lsl_def,word_0,word_lsr_def,word_ror_def]
    \\ rpt strip_tac
    THEN1
     (Cases_on `i + n MOD 64 < 32` \\ fs [w2w,fcpTheory.FCP_BETA]
      \\ once_rewrite_tac [DECIDE ``i+(n+32)=(i+32)+n:num``]
      \\ once_rewrite_tac [GSYM MOD_PLUS]
      \\ qabbrev_tac `nn = n MOD 64` \\ fs []
      \\ simp [GSYM SUB_MOD])
    THEN1
     (Cases_on `i + n MOD 64 < 32` \\ fs [w2w,fcpTheory.FCP_BETA]
      \\ once_rewrite_tac [GSYM MOD_PLUS]
      \\ qabbrev_tac `nn = n MOD 64` \\ fs [])
    THEN1
     (Cases_on `i + n MOD 64 < 64` \\ fs [w2w,fcpTheory.FCP_BETA]
      \\ once_rewrite_tac [DECIDE ``i+(n+32)=(i+32)+n:num``]
      \\ once_rewrite_tac [GSYM MOD_PLUS]
      \\ `n MOD 64 < 64` by fs []
      \\ qabbrev_tac `nn = n MOD 64` \\ fs []
      \\ simp [GSYM SUB_MOD])
    THEN1
     (Cases_on `i + n MOD 64 < 64` \\ fs [w2w,fcpTheory.FCP_BETA]
      \\ once_rewrite_tac [GSYM MOD_PLUS]
      \\ `n MOD 64 < 64` by fs []
      \\ qabbrev_tac `nn = n MOD 64` \\ fs []
      \\ simp [GSYM SUB_MOD]))
  \\ fs [WordShift64_on_32_def]
  \\ reverse TOP_CASE_TAC \\ fs [NOT_LESS]
  THEN1
   (Cases_on `sh` \\ fs [list_Seq_def] \\ eval_tac
    \\ qpat_assum `dimindex(:'a) = 32`
      (fn th => once_rewrite_tac [GSYM th])
    \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
    \\ fs [eq_eval,lookup_insert] \\ fs [lookup_insert]
    \\ rpt strip_tac
    \\ qmatch_goalsub_abbrev_tac `insert 31 (Word w31)`
    \\ qmatch_goalsub_abbrev_tac `insert 33 (Word w33)`
    \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ qmatch_goalsub_abbrev_tac `insert 31 (Word w31p)`
    \\ qmatch_goalsub_abbrev_tac `insert 33 (Word w33p)`
    \\ qsuff_tac `w31p = w31 /\ w33p = w33` \\ fs []
    \\ unabbrev_all_tac
    \\ fs [fcpTheory.CART_EQ,word_extract_def,word_bits_def,w2w,word_msb_def,
           fcpTheory.FCP_BETA,word_lsl_def,word_0,word_lsr_def,word_asr_def]
    THEN1
     (rw []
      \\ Cases_on `i + n < 64` \\ fs []
      \\ fs [fcpTheory.CART_EQ,word_extract_def,word_bits_def,w2w,
           fcpTheory.FCP_BETA,word_lsl_def,word_0,word_lsr_def])
    \\ rw [WORD_NEG_1_T,word_0] \\ fs [])
  \\ Cases_on `sh` \\ fs [list_Seq_def] \\ eval_tac
  \\ qpat_assum `dimindex(:'a) = 32`
      (fn th => once_rewrite_tac [GSYM th])
    \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
    \\ fs [eq_eval,lookup_insert] \\ fs [lookup_insert]
  \\ rpt strip_tac
  \\ qmatch_goalsub_abbrev_tac `insert 31 (Word w31)`
  \\ qmatch_goalsub_abbrev_tac `insert 33 (Word w33)`
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ qmatch_goalsub_abbrev_tac `insert 31 (Word w31p)`
  \\ qmatch_goalsub_abbrev_tac `insert 33 (Word w33p)`
  \\ qsuff_tac `w31p = w31 /\ w33p = w33` \\ fs []
  \\ unabbrev_all_tac
  \\ fs [fcpTheory.CART_EQ,word_extract_def,word_bits_def,w2w,word_msb_def,
         fcpTheory.FCP_BETA,word_lsl_def,word_0,word_lsr_def,word_asr_def,
         word_or_def] \\ rw [] \\ fs []
  THEN1 (Cases_on `n <= i` \\ fs [] \\ fs [fcpTheory.FCP_BETA,w2w])
  THEN1 (Cases_on `i + n < 32` \\ fs [fcpTheory.FCP_BETA,w2w])
  THEN1 (Cases_on `i + n < 32` \\ fs [fcpTheory.FCP_BETA,w2w])
  THEN1 (Cases_on `i + n < 32` \\ fs [fcpTheory.FCP_BETA,w2w])
QED

Theorem assign_WordShiftW64:
  (∃sh n. op = WordOp (WordShift W64 sh n)) ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac \\ imp_res_tac state_rel_arch_width
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app,oneline do_word_app_def,allowed_op_def]
  \\ every_case_tac \\ fs[]
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ clean_tac
  \\ simp[assign_def]
  \\ TOP_CASE_TAC \\ fs[]
  >-
    (conj_tac >-
      (fs[state_rel_def]>>metis_tac[backendPropsTheory.option_le_trans,
                                    consume_space_stack_max,option_le_max_right])
     \\ ‘good_dimindex (:'a)’ by gvs [state_rel_thm]
     \\ qsuff_tac ‘F’ >- rewrite_tac []
     \\ fs [state_rel_thm]
     \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
     \\ rpt_drule0 (memory_rel_get_vars_IMP |> Q.GEN ‘n’ |> Q.SPEC ‘[xx]’ |> SRULE [])
     \\ CCONTR_TAC \\ gvs []
     \\ dxrule memory_rel_Word64_IMP
     \\ strip_tac \\ rfs []
     \\ gvs [good_dimindex_def,limits_inv_def,
             memory_rel_def,heap_in_memory_store_def,consume_space_def]
     \\ qpat_x_assum ‘encode_header _ _ _ = NONE’ mp_tac
     \\ rewrite_tac []
     >-
      (irule IMP_encode_header_NOT_NONE
       \\ gvs [good_dimindex_def,limits_inv_def,state_rel_def,
               memory_rel_def,heap_in_memory_store_def,consume_space_def]
       \\ CCONTR_TAC
       \\ ‘c.len_size = 1’ by decide_tac
       \\ qpat_x_assum ‘decode_length _ _ = 2w’ mp_tac
       \\ simp [decode_length_def,make_header_def]
       \\ EVAL_TAC \\ simp [dimword_def]
       \\ EVAL_TAC \\ simp [dimword_def])
     \\ gvs [encode_header_def,dimword_def]
     \\ irule_at Any LESS_LESS_EQ_TRANS
     \\ qexists_tac ‘2 ** 2’ \\ gvs [])
  \\ TOP_CASE_TAC \\ fs[]
  THEN1 (* dimindex (:'a) = 64 *)
   (
    `dimindex (:'a) = 64` by fs [state_rel_def,good_dimindex_def]
    \\ fs [] \\ clean_tac
    \\ fs[state_rel_thm] \\ eval_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ strip_tac
    \\ fs[wordSemTheory.get_vars_def]
    \\ gvs[AllCaseEqs()]
    \\ rpt_drule0 evaluate_LoadWord64
    \\ rfs[good_dimindex_def] \\ rfs[]
    \\ disch_then drule0
    \\ simp[list_Seq_def]
    \\ simp[Once wordSemTheory.evaluate_def]
    \\ disch_then kall_tac
    \\ simp[Once wordSemTheory.evaluate_def]
    \\ qpat_assum `dimindex(:'a) = 64`
      (fn th => once_rewrite_tac [GSYM th])
    \\ simp[Once wordSemTheory.evaluate_def,word_exp_set_var_ShiftVar]
    \\ eval_tac
    \\ qmatch_goalsub_abbrev_tac`option_CASE opt _ _`
    \\ `∃w. opt = SOME w`
      by ( simp[Abbr`opt`] \\ CASE_TAC \\ simp[] )
    \\ qunabbrev_tac`opt` \\ simp[]
    \\ qhdtm_x_assum`memory_rel`kall_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,GSYM join_env_locals_def]
    \\ assume_tac(GEN_ALL evaluate_WriteWord64)
    \\ SEP_I_TAC "evaluate" \\ fs[option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ first_x_assum drule0
    \\ simp[wordSemTheory.get_var_def]
    \\ fs[consume_space_def]
    \\ simp[lookup_insert]
    \\ disch_then(qspec_then`w`strip_assume_tac)
    \\ simp[]
    \\ clean_tac \\ fs[]
    \\ fs[lookup_insert,code_oracle_rel_def,FLOOKUP_UPDATE]
    \\ conj_tac >- rw[]
    \\ match_mp_tac (GEN_ALL memory_rel_less_space)
    \\ qexists_tac`s.space-2` \\ simp[]
    \\ qmatch_abbrev_tac`memory_rel c be ts refs sp' st' m' md vars'`
    \\ qmatch_assum_abbrev_tac`memory_rel c be ts refs sp' st' m' md vars''`
    \\ `vars' = vars''` suffices_by simp[]
    \\ simp[Abbr`vars'`,Abbr`vars''`]
    \\ simp[Abbr`st'`,FAPPLY_FUPDATE_THM]
    \\ rpt(AP_TERM_TAC ORELSE AP_THM_TAC)
    \\ Cases_on`sh` \\ fs[] \\ clean_tac
    \\ simp[WORD_w2w_EXTRACT]
    >- srw_tac[wordsLib.WORD_BIT_EQ_ss][]
    >- (
      simp[fcpTheory.CART_EQ]
      \\ simp[word_extract_def,word_bits_def,w2w,word_lsr_index,fcpTheory.FCP_BETA]
      \\ rpt strip_tac
      \\ EQ_TAC \\ strip_tac \\ simp[]
      \\ rfs[w2w,fcpTheory.FCP_BETA] )
    >- (
      simp[fcpTheory.CART_EQ]
      \\ simp[word_extract_def,word_bits_def,w2w,word_asr_def,fcpTheory.FCP_BETA]
      \\ rpt strip_tac
      \\ IF_CASES_TAC \\ simp[]
      \\ simp[word_msb_def]
      \\ rfs[w2w,fcpTheory.FCP_BETA])
    >- (
      simp[fcpTheory.CART_EQ]
      \\ simp[word_extract_def,word_bits_def,w2w,word_ror_def,fcpTheory.FCP_BETA]
      \\ rpt strip_tac
      \\ eq_tac \\ fs []
      \\ `(i + n') MOD 64 < 64` by fs [] \\ simp []))
  \\ `dimindex (:'a) = 32` by fs [state_rel_def,good_dimindex_def]
  \\ fs [] \\ clean_tac
  \\ fs[state_rel_thm] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ fs[wordSemTheory.get_vars_def]
  \\ qpat_x_assum`_ = SOME [_]`mp_tac
  \\ TOP_CASE_TAC \\ fs[] \\ strip_tac \\ clean_tac
  \\ drule0 memory_rel_Word64_IMP
  \\ fs [good_dimindex_def]
  \\ strip_tac \\ fs []
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM wordSemTheory.get_var_def]
  \\ qpat_x_assum `get_var (adjust_var e1) t =
       SOME (Word (get_addr c _ (Word 0w)))` assume_tac
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ fs [WORD_MUL_LSL,good_dimindex_def]
  \\ ntac 8 (once_rewrite_tac [list_Seq_def] \\ eval_tac \\ fs [lookup_insert])
  \\ assume_tac (GEN_ALL evaluate_WordShift64_on_32) \\ rfs []
  \\ SEP_I_TAC "evaluate"
  \\ fs [] \\ pop_assum kall_tac
  \\ rpt strip_tac
  \\ assume_tac (GEN_ALL evaluate_WriteWord64_on_32)
  \\ SEP_I_TAC "evaluate"
  \\ pop_assum mp_tac \\ fs [join_env_locals_def]
  \\ fs [wordSemTheory.get_var_def,lookup_insert]
  \\ fs [inter_insert_ODD_adjust_set_alt,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ disch_then drule0
  \\ disch_then (qspec_then `shift_lookup sh c' n'` mp_tac)
  \\ simp []
  \\ impl_tac
  THEN1 (fs [consume_space_def,good_dimindex_def] \\ rw [] \\ fs [])
  \\ strip_tac \\ fs []
  \\ fs[FAPPLY_FUPDATE_THM]
  \\ fs [consume_space_def]
  \\ rveq \\ fs [] \\ rw [] \\ fs []
  \\ fs[limits_inv_def, FLOOKUP_UPDATE]
QED

Theorem Smallnum_w2n_word8:
  good_dimindex (:'a) ⇒ Smallnum (&w2n (w:word8)) = (w2w w << 1) :'a word
Proof
  rw [Smallnum_def, WORD_MUL_LSL, w2w_def, word_mul_n2w]
QED

Theorem word8_shift_MIN:
  (w:word8) << MIN n 8 = w << n ∧ w >>> MIN n 8 = w >>> n ∧
  w >> MIN n 8 = w >> n ∧ word_ror w (n MOD 8) = word_ror w n
Proof
  rw [MIN_DEF] \\ gvs [NOT_LESS, LSL_LIMIT, LSR_LIMIT, ASR_LIMIT]
  \\ qspecl_then [‘w’,‘n’] mp_tac ROR_MOD \\ simp []
QED

Theorem word64_shift_sat:
  (c:word64) >> MIN n 63 = c >> n ∧ word_ror c (n MOD 64) = word_ror c n
Proof
  rw [MIN_DEF]
  \\ TRY (qspecl_then [‘c’,‘n’] mp_tac ROR_MOD \\ simp [] \\ NO_TAC)
  \\ rw [fcpTheory.CART_EQ, word_asr_def, fcpTheory.FCP_BETA, word_msb_def]
  \\ Cases_on ‘i’ \\ gvs [] \\ rw [] \\ ‘n = 63’ by gvs [] \\ gvs []
QED

Theorem word64_halves_w2n:
  dimindex (:'a) = 32 ⇒
  w2n ((31 >< 0) (n:word64) :'a word) = w2n n MOD 2 ** 32 ∧
  (((63 >< 32) n :'a word) = 0w ⇔ w2n n < 2 ** 32)
Proof
  Cases_on ‘n’ \\ rw [word_extract_n2w, dimword_def, bitTheory.BITS_THM2, w2w_def]
  \\ gvs [DIV_MOD_MOD_DIV, DIV_EQ_0]
QED

Theorem word_exp_ShiftW8:
  good_dimindex (:'a) ∧
  lookup v t.locals = SOME (Word (w2w (w:word8) << 1)) ∧
  lookup r t.locals = SOME (Word (n2w k)) ∧
  (if sh = Ror then k < 8 else k ≤ 8) ⇒
  word_exp (t:('a,'c,'ffi) wordSem$state) (ShiftW8 (dimindex(:'a)) sh (Var v) (Var r)) =
  SOME (Word (w2w (shift_lookup sh w k) << 1))
Proof
  Cases_on ‘sh’ \\ rw [good_dimindex_def]
  \\ ‘k ≤ 8 ⇒ -1w * n2w k + 8w = n2w (8 - k) :'a word’ by
    (rw [n2w_sub] \\ simp [GSYM WORD_NEG_MUL])
  \\ gvs [ShiftW8_def, wordSemTheory.word_exp_def, wordSemTheory.get_var_def,
          wordSemTheory.word_sh_def, wordSemTheory.the_words_def,
          wordSemTheory.word_op_def, dimword_def]
  \\ rw [fcpTheory.CART_EQ, word_lsl_def, word_lsr_def, word_asr_def,
         word_or_def, word_ror_def, word_msb_def, w2w, fcpTheory.FCP_BETA]
  \\ Cases_on ‘1 ≤ i ∧ i < 9’ \\ gvs [fcpTheory.FCP_BETA, w2w]
  \\ rpt IF_CASES_TAC \\ gvs [fcpTheory.FCP_BETA, w2w]
  \\ rw [DISJ_EQ_IMP] \\ gvs [fcpTheory.FCP_BETA, w2w]
  \\ Cases_on ‘i + k < 9’ \\ gvs [EQ_IMP_THM]
  \\ ‘(i + k − 1) MOD 8 = i + k − 9’ by
    (irule MOD_UNIQUE \\ qexists_tac ‘1’ \\ gvs [])
  \\ gvs []
QED

Theorem shift64_on_32:
  dimindex (:'a) = 32 ∧ k < 32 ⇒
  let hi = ((63 >< 32) c):'a word; lo = ((31 >< 0) c):'a word in
    (31 >< 0) (c << k) = lo << k ∧
    (63 >< 32) (c << k) = (hi << k || lo >>> 1 >>> (31 - k)) ∧
    (31 >< 0) (c >>> k) = (lo >>> k || hi << 1 << (31 - k)) ∧
    (63 >< 32) (c >>> k) = hi >>> k ∧
    (31 >< 0) (c >> k) = (lo >>> k || hi << 1 << (31 - k)) ∧
    (63 >< 32) (c >> k) = hi >> k ∧
    (31 >< 0) (word_ror (c:word64) k) = (lo >>> k || hi << 1 << (31 - k)) ∧
    (63 >< 32) (word_ror c k) = (hi >>> k || lo << 1 << (31 - k))
Proof
  rw [fcpTheory.CART_EQ, word_lsl_def, word_lsr_def, word_asr_def, word_or_def,
      word_ror_def, word_msb_def, word_extract_def, word_bits_def, w2w,
      fcpTheory.FCP_BETA]
  \\ Cases_on ‘i < k’ \\ Cases_on ‘i + k < 32’
  \\ rw [EQ_IMP_THM] \\ gvs [fcpTheory.FCP_BETA, w2w]
  \\ ‘(i + (k + 32)) MOD 64 = i + k − 32’ by
    (irule MOD_UNIQUE \\ qexists_tac ‘1’ \\ gvs [])
  \\ gvs []
QED

Theorem w2w_shift_lookup:
  dimindex (:'a) = 64 ⇒
  w2w (shift_lookup sh (c:word64) k) = shift_lookup sh (w2w c :'a word) k
Proof
  Cases_on ‘sh’
  \\ rw [fcpTheory.CART_EQ, word_lsl_def, word_lsr_def, word_asr_def,
         word_ror_def, word_msb_def, w2w, fcpTheory.FCP_BETA]
  \\ rw [EQ_IMP_THM] \\ gvs [w2w]
QED

Theorem insert_Word_eq[local]:
  sptree$insert k (Word x) l = insert k (Word y) l ⇔ x = y
Proof
  rw [EQ_IMP_THM]
  \\ ‘lookup k (sptree$insert k (Word x) l) = lookup k (insert k (Word y) l)’
    by asm_rewrite_tac []
  \\ gvs [lookup_insert]
QED

Theorem evaluate_WordShiftVar64:
  dimindex (:'a) = 64 ∧
  lookup 3 t.locals = SOME (Word c) ∧
  lookup 5 t.locals = SOME (Word n) ⇒
  evaluate (WordShiftVar64 sh, t:('a,'c,'ffi) wordSem$state) =
    (NONE, set_var 3 (Word (shift_lookup sh c (w2n n))) t)
Proof
  Cases_on ‘sh’ \\ rw [WordShiftVar64_def] \\ eval_tac
  \\ ‘w2n (63w && n) = w2n n MOD 64’
    by (Cases_on ‘n’ \\ simp [Once WORD_AND_COMM,
          WORD_AND_EXP_SUB1 |> Q.SPEC ‘6’ |> SRULE [], dimword_def]
        \\ irule LESS_TRANS \\ qexists_tac ‘64’ \\ simp [])
  \\ gvs [wordSemTheory.get_var_imm_def, asmTheory.word_cmp_def, WORD_LO,
          dimword_def]
  \\ ‘∀k. word_ror c (k MOD 64) = word_ror c k’
    by (rw [] \\ qspecl_then [‘c’,‘k’] mp_tac ROR_MOD \\ simp [])
  \\ rw [] \\ gvs [LSL_LIMIT, LSR_LIMIT, insert_Word_eq]
  \\ rw [fcpTheory.CART_EQ, word_asr_def, fcpTheory.FCP_BETA, word_msb_def,
         WORD_NEG_1_T, word_0]
  \\ TRY (‘w2n n MOD 64 < 64’ by simp [] \\ decide_tac)
  \\ Cases_on ‘i = 0’ \\ gvs []
QED

Theorem lo_and_63[local]:
  dimindex (:'a) = 32 ⇒ (63w && (31 >< 0) (n:word64) :'a word) = n2w (w2n n MOD 64)
Proof
  strip_tac \\ Cases_on ‘(31 >< 0) n :'a word’
  \\ simp [WORD_AND_EXP_SUB1 |> Q.SPEC ‘6’ |> SRULE []]
  \\ drule word64_halves_w2n \\ disch_then (qspec_then ‘n’ mp_tac)
  \\ gvs [dimword_def] \\ strip_tac
  \\ gvs [MOD_MULT_MOD |> Q.SPECL [‘67108864’,‘64’] |> SRULE []]
QED

Theorem evaluate_WordShiftVar64_on_32_count[local]:
  dimindex (:'a) = 32 ∧
  lookup 11 t.locals = SOME (Word ((63 >< 32) c)) ∧
  lookup 13 t.locals = SOME (Word ((31 >< 0) c)) ∧
  lookup 21 t.locals = SOME (Word ((63 >< 32) n)) ∧
  lookup 23 t.locals = SOME (Word ((31 >< 0) n)) ⇒
  ∃c1 k l.
    evaluate
      (if sh = Ror then Assign 23 (Op And [Var 23; Const 63]) else
         Seq (If Equal 21 (Imm 0) Skip (Assign 23 (Const 64)))
             (If Lower 23 (Imm 64) Skip
                (list_Seq ((if sh = Asr then [] else
                              [Assign 11 (Const 0); Assign 13 (Const 0)]) ++
                           [Assign 23 (Const 63)]))),
       t:('a,'c,'ffi) wordSem$state) = (NONE, t with locals := l) ∧
    k < 64 ∧
    shift_lookup sh c1 k = shift_lookup sh (c:word64) (w2n (n:word64)) ∧
    lookup 11 l = SOME (Word ((63 >< 32) c1)) ∧
    lookup 13 l = SOME (Word ((31 >< 0) c1)) ∧
    lookup 23 l = SOME (Word (n2w k)) ∧
    ∀v. EVEN v ⇒ lookup v l = lookup v t.locals
Proof
  strip_tac
  \\ drule word64_halves_w2n \\ strip_tac
  \\ Cases_on ‘sh = Ror’ \\ gvs []
  >- (qexistsl [‘c’, ‘w2n n MOD 64’] \\ eval_tac
      \\ simp [lookup_insert, word64_shift_sat, lo_and_63]
      \\ rw [lookup_insert] \\ gvs [])
  \\ Cases_on ‘w2n n < 64’
  >- (qexistsl [‘c’,‘w2n n’]
      \\ ‘(63 >< 32) n = 0w :'a word ∧ (31 >< 0) n = n2w (w2n n) :'a word’
        by (first_x_assum (qspec_then ‘n’ strip_assume_tac)
            \\ gvs [] \\ metis_tac [n2w_w2n])
      \\ eval_tac
      \\ gvs [wordSemTheory.get_var_imm_def, asmTheory.word_cmp_def,
              word_lo_n2w, dimword_def]
      \\ qexists_tac ‘t.locals’ \\ simp [wordSemTheory.state_component_equality])
  \\ qexistsl [‘if sh = Asr then c else 0w’, ‘63’]
  \\ ‘(63 >< 32) n = 0w :'a word ⇒ ¬((31 >< 0) n <+ 64w :'a word)’
    by (first_x_assum (qspec_then ‘n’ strip_assume_tac) \\ rw [WORD_LO]
        \\ gvs [dimword_def])
  \\ ‘c >> 63 = c >> w2n n’
    by metis_tac [word64_shift_sat, MIN_DEF, DECIDE “¬(x < 64n) ⇒ ¬(x < 63)”]
  \\ eval_tac
  \\ gvs [wordSemTheory.get_var_imm_def, asmTheory.word_cmp_def]
  \\ Cases_on ‘w2n n < 4294967296’ \\ Cases_on ‘sh’ \\ gvs [list_Seq_def]
  \\ eval_tac
  \\ gvs [asmTheory.word_cmp_def, LSL_LIMIT, LSR_LIMIT, lookup_insert,
          wordSemTheory.state_component_equality]
  \\ rw [lookup_insert]
QED

Theorem evaluate_WordShiftVar64_on_32_step[local]:
  dimindex (:'a) = 32 ∧ k < 64 ∧
  lookup 11 t.locals = SOME (Word ((63 >< 32) c)) ∧
  lookup 13 t.locals = SOME (Word ((31 >< 0) c)) ∧
  lookup 23 t.locals = SOME (Word (n2w k)) ⇒
  ∃c1 k1 l.
    evaluate
      (If Lower 23 (Imm 32) Skip
         (list_Seq [WordShift64_on_32 sh 32; Move 0 [(11,31);(13,33)];
                    Assign 23 (Op Sub [Var 23; Const 32])]),
       t:('a,'c,'ffi) wordSem$state) = (NONE, t with locals := l) ∧
    k1 < 32 ∧ shift_lookup sh c1 k1 = shift_lookup sh (c:word64) k ∧
    lookup 11 l = SOME (Word ((63 >< 32) c1)) ∧
    lookup 13 l = SOME (Word ((31 >< 0) c1)) ∧
    lookup 23 l = SOME (Word (n2w k1)) ∧
    ∀v. EVEN v ⇒ lookup v l = lookup v t.locals
Proof
  strip_tac \\ Cases_on ‘k < 32’
  >- (qexistsl [‘c’, ‘k’, ‘t.locals’] \\ eval_tac
      \\ gvs [wordSemTheory.get_var_imm_def, asmTheory.word_cmp_def,
              word_lo_n2w, dimword_def])
  \\ qexistsl [‘shift_lookup sh c 32’, ‘k - 32’]
  \\ ‘evaluate (WordShift64_on_32 sh 32, t) =
      (NONE, t with locals :=
         insert 31 (Word ((63 >< 32) (shift_lookup sh c 32)))
           (insert 33 (Word ((31 >< 0) (shift_lookup sh c 32))) t.locals))’
    by (qspec_then ‘t.locals’ mp_tac
          (Q.INST [‘c'’ |-> ‘c’, ‘n’ |-> ‘32’] evaluate_WordShift64_on_32)
        \\ simp [insert_unchanged])
  \\ ‘shift_lookup sh (shift_lookup sh c 32) (k − 32) = shift_lookup sh c k’
    by (Cases_on ‘sh’ \\ simp [LSL_ADD, LSR_ADD, ASR_ADD, ROR_ADD])
  \\ simp [list_Seq_def] \\ eval_tac
  \\ gvs [wordSemTheory.get_var_imm_def, asmTheory.word_cmp_def, word_lo_n2w,
          dimword_def, wordSemTheory.get_vars_def, wordSemTheory.set_vars_def,
          alist_insert_def, lookup_insert, n2w_sub]
  \\ eval_tac
  \\ gvs [wordSemTheory.get_vars_def, wordSemTheory.set_vars_def,
          alist_insert_def, lookup_insert]
  \\ rw [lookup_insert]
QED

Theorem evaluate_WordShiftVar64_on_32:
  dimindex (:'a) = 32 ∧
  lookup 11 t.locals = SOME (Word ((63 >< 32) (c:word64))) ∧
  lookup 13 t.locals = SOME (Word ((31 >< 0) c)) ∧
  lookup 21 t.locals = SOME (Word ((63 >< 32) n)) ∧
  lookup 23 t.locals = SOME (Word ((31 >< 0) n)) ⇒
  ∃l. evaluate (WordShiftVar64_on_32 sh, t:('a,'c,'ffi) wordSem$state) =
        (NONE, t with locals := l) ∧
      lookup 31 l = SOME (Word ((63 >< 32) (shift_lookup sh c (w2n (n:word64))))) ∧
      lookup 33 l = SOME (Word ((31 >< 0) (shift_lookup sh c (w2n n)))) ∧
      ∀v. EVEN v ⇒ lookup v l = lookup v t.locals
Proof
  strip_tac
  \\ drule_all evaluate_WordShiftVar64_on_32_count
  \\ disch_then (qspec_then ‘sh’ strip_assume_tac)
  \\ simp [WordShiftVar64_on_32_def, list_Seq_def, Once wordSemTheory.evaluate_def]
  \\ mp_tac (Q.INST [‘t’ |-> ‘t with locals := l’, ‘c’ |-> ‘c1’]
                 evaluate_WordShiftVar64_on_32_step)
  \\ simp [] \\ strip_tac
  \\ fs [list_Seq_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ simp [wordSemTheory.evaluate_def, wordSemTheory.word_exp_def,
          wordSemTheory.get_var_def, wordSemTheory.the_words_def,
          wordSemTheory.word_op_def, wordSemTheory.word_sh_def,
          wordSemTheory.set_var_def, lookup_insert]
  \\ ntac 2 (qpat_x_assum ‘evaluate _ = _’ kall_tac)
  \\ qpat_x_assum ‘shift_lookup sh c1' _ = _’ (SUBST1_TAC o GSYM)
  \\ mp_tac (Q.INST [‘k’ |-> ‘k1’, ‘c’ |-> ‘c1'’] shift64_on_32)
  \\ simp [] \\ strip_tac
  \\ ‘-1w * n2w k1 + 31w = n2w (31 - k1) :'a word’
    by (rw [n2w_sub] \\ simp [GSYM WORD_NEG_MUL])
  \\ Cases_on ‘sh’
  \\ gvs [wordSemTheory.word_exp_def, wordSemTheory.the_words_def,
          wordSemTheory.word_op_def, wordSemTheory.word_sh_def,
          wordSemTheory.get_var_def, lookup_insert, dimword_def]
  \\ rw [] \\ gvs []
QED

Theorem evaluate_clamp_W8:
  good_dimindex (:'a) ∧ k < 256 ⇒
  evaluate (if sh = Ror then Assign 1 (Op And [Var 1; Const 7])
            else If Lower 1 (Imm 8) Skip (Assign 1 (Const 8)),
            t with locals := insert 1 (Word (n2w k)) l) =
  (NONE, t with locals := insert 1 (Word (n2w (if sh = Ror then k MOD 8
                                                else MIN k 8))) l)
   : 'a result option # ('a,'c,'ffi) wordSem$state
Proof
  rw [] \\ eval_tac
  \\ gvs [WORD_AND_EXP_SUB1 |> Q.SPEC ‘3’ |> SRULE [], word_lo_n2w,
          good_dimindex_def, dimword_def, MIN_DEF, lookup_insert,
          wordSemTheory.get_var_imm_def, asmTheory.word_cmp_def, insert_shadow]
  \\ rw []
QED

Theorem assign_WordShiftVarW8:
  (∃sh. op = WordOp (WordShiftVar W8 sh)) ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac \\ imp_res_tac state_rel_arch_width
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app,oneline do_word_app_def,allowed_op_def]
  \\ every_case_tac \\ fs[]
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ clean_tac
  \\ fs[state_rel_thm] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ qhdtm_x_assum`$some`mp_tac
  \\ DEEP_INTRO_TAC some_intro \\ fs[FORALL_PROD]
  \\ strip_tac \\ clean_tac
  \\ qmatch_asmsub_rename_tac`[Number (&w2n w); Number (&w2n k)]`
  \\ `small_int (dimindex (:'a)) (&w2n w) ∧ small_int (dimindex (:'a)) (&w2n k)`
    by simp[small_int_w2n]
  \\ imp_res_tac memory_rel_Number_IMP
  \\ imp_res_tac memory_rel_tl
  \\ imp_res_tac memory_rel_Number_IMP
  \\ qhdtm_x_assum`memory_rel`kall_tac
  \\ ntac 2 (first_x_assum(qspec_then`ARB`kall_tac))
  \\ fs[wordSemTheory.get_vars_def]
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ simp[assign_def,list_Seq_def] \\ eval_tac
  \\ `~(1 ≥ dimindex (:'a))` by fs [good_dimindex_def]
  \\ `(w2w k << 1) >>> 1 = n2w (w2n k) :'a word`
    by (simp [GSYM w2w_def] \\ irule lsl_lsr
        \\ gvs [good_dimindex_def, dimword_def, w2n_w2w]
        \\ assume_tac (Q.ISPEC ‘k:word8’ w2n_lt) \\ gvs [])
  \\ gvs [Smallnum_w2n_word8]
  \\ qabbrev_tac ‘k8 = if sh = Ror then w2n k MOD 8 else MIN (w2n k) 8’
  \\ qmatch_goalsub_abbrev_tac ‘evaluate (_,t1)’
  \\ ‘evaluate (if sh = Ror then Assign 1 (Op And [Var 1; Const 7])
                 else If Lower 1 (Imm 8) Skip (Assign 1 (Const 8)), t1) =
      (NONE, t with locals := insert 1 (Word (n2w k8)) t.locals)’
    by (unabbrev_all_tac \\ irule evaluate_clamp_W8 \\ gvs [w2n_lt_256])
  \\ simp []
  \\ ‘shift_lookup sh w (w2n k) = shift_lookup sh w k8’
    by (Cases_on ‘sh’ \\ simp [Abbr ‘k8’, word8_shift_MIN])
  \\ qmatch_goalsub_abbrev_tac ‘word_exp t2’
  \\ ‘word_exp t2 (ShiftW8 (arch_width_bits c.arch_width) sh (Var (adjust_var h)) (Var 1)) =
      SOME (Word (w2w (shift_lookup sh w k8) << 1))’
    by (gvs [] \\ irule word_exp_ShiftW8
        \\ gvs [Abbr ‘t2’, Abbr ‘k8’, lookup_insert] \\ rw [MIN_DEF])
  \\ gvs [Abbr ‘t2’, lookup_insert, option_le_max_right]
  \\ conj_tac >- rw []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert
  \\ fs [inter_insert_ODD_adjust_set_alt, GSYM Smallnum_w2n_word8]
  \\ match_mp_tac IMP_memory_rel_Number
  \\ simp [small_int_w2n]
QED

Theorem inter_adjust_set_EVEN[local]:
  (∀v. EVEN v ⇒ lookup v l = lookup v l') ⇒
  inter l (adjust_set x) = inter l' (adjust_set x)
Proof
  rw [spt_eq_thm, wf_inter, lookup_inter_alt]
  \\ rw [] \\ imp_res_tac domain_adjust_set_EVEN \\ fs []
QED

Theorem assign_WordShiftVarW64:
  (∃sh. op = WordOp (WordShiftVar W64 sh)) ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac \\ imp_res_tac state_rel_arch_width
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app,oneline do_word_app_def,allowed_op_def]
  \\ every_case_tac \\ fs[]
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ clean_tac
  \\ simp[assign_def]
  \\ TOP_CASE_TAC \\ fs[]
  >- (conj_tac >-
       (fs[state_rel_def]>>metis_tac[backendPropsTheory.option_le_trans,
                                     consume_space_stack_max,option_le_max_right])
      \\ ‘good_dimindex (:'a)’ by gvs [state_rel_thm]
      \\ qsuff_tac ‘F’ >- rewrite_tac []
      \\ fs [state_rel_thm]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ rpt_drule0 (memory_rel_get_vars_IMP |> Q.GEN ‘n’ |> Q.SPEC ‘[xx;yy]’ |> SRULE [])
      \\ CCONTR_TAC \\ gvs []
      \\ dxrule memory_rel_Word64_IMP
      \\ strip_tac \\ rfs []
      \\ gvs [good_dimindex_def,limits_inv_def,
              memory_rel_def,heap_in_memory_store_def,consume_space_def]
      \\ qpat_x_assum ‘encode_header _ _ _ = NONE’ mp_tac
      \\ rewrite_tac []
      >-
       (irule IMP_encode_header_NOT_NONE
        \\ gvs [good_dimindex_def,limits_inv_def,state_rel_def,
                memory_rel_def,heap_in_memory_store_def,consume_space_def]
        \\ CCONTR_TAC
        \\ ‘c.len_size = 1’ by decide_tac
        \\ qpat_x_assum ‘decode_length _ _ = 2w’ mp_tac
        \\ simp [decode_length_def,make_header_def]
        \\ EVAL_TAC \\ simp [dimword_def]
        \\ EVAL_TAC \\ simp [dimword_def])
      \\ gvs [encode_header_def,dimword_def]
      \\ irule_at Any LESS_LESS_EQ_TRANS
      \\ qexists_tac ‘2 ** 2’ \\ gvs [])
  \\ IF_CASES_TAC
  >- (`dimindex (:'a) = 32` by fs [state_rel_def,good_dimindex_def]
      \\ fs [] \\ clean_tac
      \\ fs[state_rel_thm] \\ eval_tac
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
      \\ strip_tac
      \\ fs[wordSemTheory.get_vars_def]
      \\ gvs [AllCaseEqs()]
      \\ drule0 memory_rel_Word64_IMP \\ fs [good_dimindex_def] \\ strip_tac
      \\ drule0 memory_rel_tl \\ strip_tac
      \\ drule0 memory_rel_Word64_IMP \\ fs [good_dimindex_def] \\ strip_tac
      \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
      \\ ‘∀v p x. get_var v t = SOME (Word p) ∧ get_real_addr c t.store p = SOME x ⇒
            ∀t1:('a,'c,'ffi) wordSem$state.
              t1.store = t.store ∧ lookup v t1.locals = lookup v t.locals ⇒
              word_exp t1 (real_addr c v) = SOME (Word x)’
        by (rw [] \\ irule get_real_addr_lemma
            \\ gvs [wordSemTheory.get_var_def, good_dimindex_def])
      \\ pop_assum (fn th => imp_res_tac th)
      \\ simp [list_Seq_def]
      \\ ntac 2 (eval_tac \\ fs [lookup_insert, WORD_MUL_LSL])
      \\ qmatch_goalsub_abbrev_tac ‘evaluate (WordShiftVar64_on_32 sh, t2)’
      \\ mp_tac (Q.INST [‘t’ |-> ‘t2’, ‘c’ |-> ‘c''’, ‘n’ |-> ‘c'’]
                     evaluate_WordShiftVar64_on_32)
      \\ simp [Abbr ‘t2’, lookup_insert] \\ strip_tac \\ simp []
      \\ ‘∀v. EVEN v ⇒ lookup v l = lookup v t.locals’
        by (rw [] \\ first_x_assum drule \\ rw [lookup_insert] \\ gvs [])
      \\ assume_tac (GEN_ALL evaluate_WriteWord64_on_32)
      \\ SEP_I_TAC "evaluate"
      \\ pop_assum mp_tac \\ fs [join_env_locals_def, wordSemTheory.get_var_def]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
      \\ disch_then (qspecl_then [‘shift_lookup sh c'' (w2n c')’,
           ‘(the_global s.global, t.store ' Globals)::flat s.stack t.stack’,
           ‘THE s.tstamps’, ‘s.space’, ‘s.locals’, ‘s.refs’, ‘t.be’] mp_tac)
      \\ drule_then (fn th => rewrite_tac [th]) inter_adjust_set_EVEN
      \\ impl_tac >- (fs [consume_space_def, EVEN_adjust_var] \\ rw [] \\ fs [])
      \\ strip_tac \\ fs []
      \\ fs [FAPPLY_FUPDATE_THM, consume_space_def]
      \\ rveq \\ fs [] \\ rw [] \\ fs []
      \\ fs [limits_inv_def, FLOOKUP_UPDATE, option_le_max_right])
  \\ `dimindex (:'a) = 64` by fs [state_rel_def,good_dimindex_def]
  \\ fs [] \\ clean_tac
  \\ fs[state_rel_thm] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ fs[wordSemTheory.get_vars_def]
  \\ gvs[AllCaseEqs()]
  \\ ‘evaluate (LoadWord64 c 3 (adjust_var h), t) =
      (NONE, set_var 3 (Word (w2w c'')) t)’
    by (irule evaluate_LoadWord64 \\ simp [wordSemTheory.get_var_def]
        \\ metis_tac [])
  \\ ‘evaluate (LoadWord64 c 5 (adjust_var h'), set_var 3 (Word (w2w c'')) t) =
      (NONE, set_var 5 (Word (w2w c')) (set_var 3 (Word (w2w c'')) t))’
    by (irule evaluate_LoadWord64
        \\ simp [wordSemTheory.get_var_def, wordSemTheory.set_var_def, lookup_insert]
        \\ drule memory_rel_tl \\ fs [wordSemTheory.get_var_def]
        \\ strip_tac \\ metis_tac [])
  \\ mp_tac (Q.INST [‘t’ |-> ‘set_var 5 (Word (w2w (c':word64)))
                                 (set_var 3 (Word (w2w (c'':word64))) t)’,
                     ‘c’ |-> ‘w2w (c'':word64)’, ‘n’ |-> ‘w2w (c':word64)’]
                 evaluate_WordShiftVar64)
  \\ simp [wordSemTheory.set_var_def, lookup_insert] \\ strip_tac
  \\ simp [list_Seq_def, Once wordSemTheory.evaluate_def]
  \\ simp [Once wordSemTheory.evaluate_def, wordSemTheory.set_var_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ ‘shift_lookup sh (w2w c'' :'a word) (w2n (w2w c' :'a word)) =
      w2w (shift_lookup sh c'' (w2n c'))’ by simp [w2w_shift_lookup, w2n_w2w]
  \\ pop_assum SUBST1_TAC
  \\ qhdtm_x_assum`memory_rel`kall_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,GSYM join_env_locals_def]
  \\ assume_tac(GEN_ALL evaluate_WriteWord64)
  \\ SEP_I_TAC "evaluate" \\ fs[option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ first_x_assum drule0
  \\ simp[wordSemTheory.get_var_def]
  \\ fs[consume_space_def]
  \\ simp[lookup_insert]
  \\ ‘w2w (w2w (shift_lookup sh c'' (w2n c')) :'a word) =
      shift_lookup sh c'' (w2n c')’ by simp [Once w2w_def, w2n_w2w]
  \\ strip_tac \\ fs []
  \\ fs [lookup_insert, code_oracle_rel_def, FLOOKUP_UPDATE]
  \\ gvs [consume_space_def, option_le_max_right, FLOOKUP_UPDATE, limits_inv_def]
  \\ conj_tac >- rw []
  \\ irule memory_rel_less_space
  \\ qexists_tac ‘s.space - 2’ \\ simp [FAPPLY_FUPDATE_THM]
QED

val assign_FP_cmp = SIMP_CONV (srw_ss()) [assign_def]
  ``((assign (c:data_to_word$config) (secn:num) (l:num) (dest:num) (WordOp (FP_cmp fpc))
       (args:num list) (names:num_set option)):wordLang$prog # num)``;

val assign_FP_top = SIMP_CONV (srw_ss()) [assign_def]
  ``((assign (c:data_to_word$config) (secn:num) (l:num) (dest:num) (WordOp (FP_top fpt))
       (args:num list) (names:num_set option)):wordLang$prog # num)``;

val assign_FP_bop = SIMP_CONV (srw_ss()) [assign_def]
  ``((assign (c:data_to_word$config) (secn:num) (l:num) (dest:num) (WordOp (FP_bop fpb))
       (args:num list) (names:num_set option)):wordLang$prog # num)``;

val assign_FP_uop = SIMP_CONV (srw_ss()) [assign_def]
  ``((assign (c:data_to_word$config) (secn:num) (l:num) (dest:num) (WordOp (FP_uop fpu))
       (args:num list) (names:num_set option)):wordLang$prog # num)``;

Theorem w2w_select_id:
   dimindex (:'a) = 64 ==>
    ((w2w:'a word -> word64) ((63 >< 0) w)) = w
Proof
  Cases_on `w`
  \\ fs [wordsTheory.word_extract_n2w,bitTheory.BITS_THM,w2w_def,dimword_def]
QED

Theorem extract_append_id:
   dimindex (:'a) = 32 ==>
    ((((63 >< 32) w):'a word) @@ (((31 >< 0) w):'a word)) = w:word64
Proof
  fs [fcpTheory.CART_EQ,word_concat_def,word_join_def,w2w,word_or_def,
      fcpTheory.FCP_BETA,w2w] \\ rw []
  \\ `FINITE 𝕌(:α)` by (CCONTR_TAC \\ fs [fcpTheory.dimindex_def])
  \\ `dimindex (:'a + 'a) = 64` by fs [fcpTheory.index_sum]
  \\ fs [fcpTheory.FCP_BETA,w2w,word_lsl_def,word_extract_def,word_bits_def]
  \\ Cases_on `i < 32` \\ fs []
  \\ fs [fcpTheory.FCP_BETA,w2w,word_lsl_def,word_extract_def,word_bits_def]
QED

Theorem word1_cases:
   !w:word1. w = 0w \/ w = 1w
Proof
  Cases \\ fs [dimword_def]
QED

Theorem w2w_w2w_64:
   !w. dimindex (:'a) = 64 ==> w2w ((w2w w):'a word) = w:word64
Proof
  Cases \\ fs [w2w_def,dimword_def]
QED

Theorem fp_greater[local]:
  fp64_greaterThan a b = fp64_lessThan b a /\
  fp64_greaterEqual a b = fp64_lessEqual b a
Proof
  fs [machine_ieeeTheory.fp64_greaterEqual_def,
      machine_ieeeTheory.fp64_lessEqual_def,
      binary_ieeeTheory.float_greater_equal_def,
      binary_ieeeTheory.float_less_equal_def,
      machine_ieeeTheory.fp64_greaterThan_def,
      machine_ieeeTheory.fp64_lessThan_def,
      binary_ieeeTheory.float_greater_than_def,
      binary_ieeeTheory.float_less_than_def,
      binary_ieeeTheory.float_compare_def]
  \\ every_case_tac \\ fs [] \\ rveq \\ fs []
  \\ metis_tac [realTheory.REAL_LT_ANTISYM,
                realTheory.REAL_LT_TOTAL,word1_cases]
QED

Theorem assign_FP_cmp:
  (∃fpc. op = WordOp (FP_cmp fpc)) ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app,oneline do_word_app_def,allowed_op_def]
  \\ gvs [AllCaseEqs()]
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ clean_tac
  \\ rename[‘get_vars [e1;e2] s.locals’]
  \\ fs[state_rel_thm,option_le_max_right] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ fs[wordSemTheory.get_vars_def]
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ drule0 memory_rel_Word64_IMP
  \\ imp_res_tac memory_rel_tl
  \\ drule0 memory_rel_Word64_IMP
  \\ qhdtm_x_assum`memory_rel`kall_tac
  \\ simp[] \\ ntac 2 strip_tac
  \\ clean_tac
  \\ simp [assign_FP_cmp]
  \\ TOP_CASE_TAC >-
    (fs [state_rel_def,limits_inv_def]>>
    metis_tac[backendPropsTheory.option_le_trans,option_le_max_right])
  \\ Cases_on `dimindex (:'a) = 64` \\ simp [] THEN1
   (fs [] \\ clean_tac
    \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
    \\ rpt_drule0 get_var_get_real_addr_lemma
    \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
    \\ qmatch_goalsub_abbrev_tac `evaluate (_,t1)`
    \\ `get_var (adjust_var e2) t1 =
         SOME (Word (get_addr c ptr (Word 0w)))` by
         (unabbrev_all_tac \\ fs [wordSemTheory.get_var_def,lookup_insert])
    \\ rpt_drule0 get_var_get_real_addr_lemma
    \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
    \\ simp [Abbr `t1`]
    \\ rpt (disch_then kall_tac)
    \\ Cases_on `fpc` \\ fs [fp_cmp_inst_def]
    \\ rewrite_tac [list_Seq_def] \\ eval_tac
    \\ fs [wordSemTheory.inst_def,wordSemTheory.get_var_def,lookup_insert,
           wordSemTheory.set_fp_var_def,wordSemTheory.get_fp_var_def,
           FLOOKUP_UPDATE,wordSemTheory.set_var_def,w2w_select_id,
           fpSemTheory.fp_cmp_comp_def]
    \\ simp [Once word_exp_ShiftVar_bits]
    \\ fs [lookup_insert,adjust_var_11]
    \\ conj_tac \\ TRY (rw [] \\ NO_TAC)
    \\ fs [option_le_max_right] \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert
    \\ fs [inter_insert_ODD_adjust_set_alt,fp_greater]
    \\ rw [] \\ fs [WORD_MUL_LSL]
    \\ TRY (match_mp_tac memory_rel_Boolv_T)
    \\ TRY (match_mp_tac memory_rel_Boolv_F)
    \\ fs [])
  \\ fs []
  \\ `dimindex (:'a) = 32` by rfs [good_dimindex_def] \\ fs [] \\ rveq
  \\ eval_tac
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM wordSemTheory.get_var_def]
  \\ qpat_x_assum `get_var (adjust_var e1) t =
       SOME (Word (get_addr c _ (Word 0w)))` assume_tac
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var (adjust_var e2) t =
       SOME (Word (get_addr c _ (Word 0w)))` assume_tac
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_abbrev_tac `t1 = t with locals := insert 15 _ t.locals`
  \\ `get_var (adjust_var e2) t1 =
       SOME (Word (get_addr c ptr (Word 0w)))` by
   (fs [wordSemTheory.get_var_def,Abbr`t1`,lookup_insert]
    \\ rw [] \\ `EVEN 15` by metis_tac [EVEN_adjust_var] \\ fs [])
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ fs [Abbr`t1`]
  \\ fs [WORD_MUL_LSL]
  \\ ntac 7 (once_rewrite_tac [list_Seq_def] \\ eval_tac \\ fs [lookup_insert])
  \\ Cases_on `fpc` \\ fs [fp_cmp_inst_def]
  \\ rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.inst_def,wordSemTheory.get_var_def,lookup_insert,
         wordSemTheory.set_fp_var_def,wordSemTheory.get_fp_var_def,
         FLOOKUP_UPDATE,wordSemTheory.set_var_def,w2w_select_id,
         fpSemTheory.fp_cmp_comp_def,extract_append_id]
  \\ simp [Once word_exp_ShiftVar_bits]
  \\ fs [lookup_insert,adjust_var_11]
  \\ rpt (disch_then kall_tac)
  \\ conj_tac \\ TRY (rw [] \\ NO_TAC)
  \\ fs [option_le_max_right] \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert
  \\ fs [inter_insert_ODD_adjust_set_alt,fp_greater]
  \\ rw [] \\ fs [WORD_MUL_LSL]
  \\ TRY (match_mp_tac memory_rel_Boolv_T)
  \\ TRY (match_mp_tac memory_rel_Boolv_F)
  \\ fs []
QED

Theorem assign_FP_top:
  (∃fpt. op = WordOp (FP_top fpt)) ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app,oneline do_word_app_def,allowed_op_def,space_consumed_def]
  \\ gvs [AllCaseEqs()]
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ clean_tac
  \\ rename[‘get_vars [e1;e2;e3] s.locals’]
  \\ fs[state_rel_thm,option_le_max_right] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ fs[wordSemTheory.get_vars_def]
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ drule0 memory_rel_Word64_IMP
  \\ imp_res_tac memory_rel_tl
  \\ drule0 memory_rel_Word64_IMP
  \\ imp_res_tac memory_rel_tl
  \\ drule0 memory_rel_Word64_IMP
  \\ qhdtm_x_assum`memory_rel`kall_tac
  \\ simp[] \\ ntac 3 strip_tac
  \\ clean_tac
  \\ simp [assign_FP_top]
  \\ TOP_CASE_TAC
  >-
    (fs[state_rel_def,limits_inv_def] >>
     conj_tac >- metis_tac[backendPropsTheory.option_le_trans,
                           consume_space_stack_max,option_le_max_right] >>
     fs[consume_space_def,CaseEq"option"] >> rveq >> simp[] >>
     metis_tac[option_le_trans]
    )
  \\ Cases_on `dimindex (:'a) = 64` \\ simp [] THEN1
   (TOP_CASE_TAC \\ fs []
    >- (fs[state_rel_def,limits_inv_def]>>
        conj_tac >- metis_tac[backendPropsTheory.option_le_trans,
                              consume_space_stack_max,option_le_max_right]
        \\ qsuff_tac ‘F’ >- rewrite_tac []
        \\ pop_assum mp_tac
        \\ simp [encode_header_def,dimword_def]
        \\ irule_at Any LESS_LESS_EQ_TRANS
        \\ qexists_tac ‘2 ** 2’ \\ simp []
        \\ gvs [state_rel_thm,limits_inv_def,memory_rel_def,heap_in_memory_store_def])
    \\ clean_tac
    \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
    \\ rpt_drule0 get_var_get_real_addr_lemma
    \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
    \\ qmatch_goalsub_abbrev_tac `evaluate (_,t1)`
    \\ `get_var (adjust_var e2) t1 =
         SOME (Word (get_addr c ptr' (Word 0w)))` by
         (unabbrev_all_tac \\ fs [wordSemTheory.get_var_def,lookup_insert])
    \\ rpt_drule0 get_var_get_real_addr_lemma
    \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
    \\ simp [Abbr `t1`]
    \\ qmatch_goalsub_abbrev_tac `evaluate (_,t2)`
    \\ `get_var (adjust_var e3) t2 =
         SOME (Word (get_addr c ptr (Word 0w)))` by
         (unabbrev_all_tac \\ fs [wordSemTheory.get_var_def,lookup_insert])
    \\ rpt_drule0 get_var_get_real_addr_lemma
    \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
    \\ simp [Abbr `t2`]
    \\ rpt (disch_then kall_tac)
    \\ Cases_on `fpt` \\ fs [fp_top_inst_def]
    \\ rewrite_tac [list_Seq_def] \\ eval_tac
    \\ fs [wordSemTheory.inst_def,wordSemTheory.get_var_def,lookup_insert,
           wordSemTheory.set_fp_var_def,wordSemTheory.get_fp_var_def,
           FLOOKUP_UPDATE,wordSemTheory.set_var_def,w2w_select_id,
           fpSemTheory.fp_top_comp_def]
    \\ assume_tac(GEN_ALL evaluate_WriteWord64)
    \\ SEP_I_TAC "evaluate" \\ fs[]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,GSYM join_env_locals_def]
    \\ first_x_assum drule0
    \\ simp[wordSemTheory.get_var_def]
    \\ fs[lookup_insert,good_dimindex_def,consume_space_def]
    \\ strip_tac
    \\ clean_tac \\ fs[option_le_max_right]
    \\ conj_tac \\ TRY (rw [] \\ NO_TAC)
    \\ conj_tac >-
      (qhdtm_x_assum `limits_inv` mp_tac>>
      simp[limits_inv_def,FLOOKUP_UPDATE])
    \\ fs [FAPPLY_FUPDATE_THM] \\ rfs [w2w_w2w_64, fpSemTheory.fpfma_def]
    \\ rpt_drule0 memory_rel_less_space
    \\ disch_then match_mp_tac \\ fs [])
  \\ TOP_CASE_TAC \\ fs []
  >-
    (fs[state_rel_def,limits_inv_def]>>
     conj_tac >- metis_tac[backendPropsTheory.option_le_trans,
                           consume_space_stack_max,option_le_max_right]
     \\ qsuff_tac ‘F’ >- rewrite_tac []
     \\ qpat_x_assum ‘encode_header _ _ _ = NONE’ mp_tac
     \\ gvs [encode_header_def,dimword_def]
     \\ `dimindex (:'a) = 32` by rfs [good_dimindex_def] \\ fs [] \\ rveq
     \\ irule_at Any LESS_LESS_EQ_TRANS
     \\ qexists_tac ‘2 ** 2’ \\ gvs []
     \\ gvs [state_rel_thm,limits_inv_def,memory_rel_def,heap_in_memory_store_def]
     \\ CCONTR_TAC
     \\ ‘c.len_size = 1’ by decide_tac
     \\ qpat_x_assum ‘decode_length _ _ = 2w’ mp_tac
     \\ simp [decode_length_def,make_header_def]
     \\ EVAL_TAC \\ simp [dimword_def]
     \\ EVAL_TAC \\ simp [dimword_def])
  \\ `dimindex (:'a) = 32` by rfs [good_dimindex_def] \\ fs [] \\ rveq
  \\ eval_tac
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM wordSemTheory.get_var_def]
  \\ qpat_x_assum `get_var (adjust_var e1) t =
       SOME (Word (get_addr c _ (Word 0w)))` assume_tac
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var (adjust_var e2) t =
       SOME (Word (get_addr c _ (Word 0w)))` assume_tac
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var (adjust_var e3) t =
       SOME (Word (get_addr c _ (Word 0w)))` assume_tac
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_abbrev_tac `t1 = t with locals := insert 15 _ t.locals`
  \\ `get_var (adjust_var e2) t1 =
       SOME (Word (get_addr c ptr' (Word 0w)))` by
   (fs [wordSemTheory.get_var_def,Abbr`t1`,lookup_insert]
    \\ rw [] \\ `EVEN 15` by metis_tac [EVEN_adjust_var] \\ fs [])
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ fs [Abbr`t1`]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ qpat_abbrev_tac `t2 = t with locals := insert 17 _ _`
  \\ `get_var (adjust_var e3) t2 =
       SOME (Word (get_addr c ptr (Word 0w)))` by
   (fs [wordSemTheory.get_var_def,Abbr`t2`,lookup_insert]
    \\ rw [] \\ `EVEN 17` by metis_tac [EVEN_adjust_var] \\ fs [])
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ fs [Abbr`t2`]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ Cases_on `fpt` \\ fs [fp_top_inst_def]
  \\ rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.inst_def,wordSemTheory.get_var_def,lookup_insert,
         wordSemTheory.set_fp_var_def,wordSemTheory.get_fp_var_def,
         FLOOKUP_UPDATE,wordSemTheory.set_var_def,w2w_select_id,
         fpSemTheory.fp_top_comp_def,WORD_MUL_LSL]
  \\ rpt (disch_then kall_tac)
  \\ assume_tac(GEN_ALL evaluate_WriteWord64_on_32)
  \\ SEP_I_TAC "evaluate" \\ fs[option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,GSYM join_env_locals_def]
  \\ first_x_assum drule0
  \\ simp[wordSemTheory.get_var_def]
  \\ fs[lookup_insert,good_dimindex_def,consume_space_def]
  \\ rfs [extract_append_id]
  \\ (qpat_abbrev_tac `ww = fpSem$fpfma _ _ _`)
  \\ disch_then (qspec_then `ww` mp_tac) \\ fs []
  \\ TRY impl_tac \\ TRY (rw [] \\ NO_TAC)
  \\ strip_tac \\ fs [FAPPLY_FUPDATE_THM]
  \\ rveq \\ fs [] \\ rw []
  \\ qhdtm_x_assum `limits_inv` mp_tac
  \\ simp[limits_inv_def,FLOOKUP_UPDATE]
QED

Theorem assign_FP_bop:
  (∃fpb. op = WordOp (FP_bop fpb)) ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app,oneline do_word_app_def,allowed_op_def]
  \\ every_case_tac \\ fs[]
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ clean_tac
  \\ rename[‘get_vars [e1;e2] s.locals’]
  \\ fs[state_rel_thm,option_le_max_right] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ fs[wordSemTheory.get_vars_def]
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ drule0 memory_rel_Word64_IMP
  \\ imp_res_tac memory_rel_tl
  \\ drule0 memory_rel_Word64_IMP
  \\ qhdtm_x_assum`memory_rel`kall_tac
  \\ simp[] \\ ntac 2 strip_tac
  \\ clean_tac
  \\ simp [assign_FP_bop]
  \\ TOP_CASE_TAC
  >-
    (fs[state_rel_def,limits_inv_def] >>
     conj_tac >- metis_tac[backendPropsTheory.option_le_trans,
                           consume_space_stack_max,option_le_max_right] >>
     fs[consume_space_def,CaseEq"option"] >> rveq >> simp[] >>
     metis_tac[option_le_trans]
    )
  \\ Cases_on `dimindex (:'a) = 64` \\ simp [] THEN1
   (TOP_CASE_TAC \\ fs []
    >- (fs[state_rel_def,limits_inv_def]>>
        conj_tac >- metis_tac[backendPropsTheory.option_le_trans,
                              consume_space_stack_max,option_le_max_right]
        \\ qsuff_tac ‘F’ >- rewrite_tac []
        \\ pop_assum mp_tac
        \\ simp [encode_header_def,dimword_def]
        \\ irule_at Any LESS_LESS_EQ_TRANS
        \\ qexists_tac ‘2 ** 2’ \\ simp []
        \\ gvs [state_rel_thm,limits_inv_def,memory_rel_def,heap_in_memory_store_def])
    \\ clean_tac
    \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
    \\ rpt_drule0 get_var_get_real_addr_lemma
    \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
    \\ qmatch_goalsub_abbrev_tac `evaluate (_,t1)`
    \\ `get_var (adjust_var e2) t1 =
         SOME (Word (get_addr c ptr (Word 0w)))` by
         (unabbrev_all_tac \\ fs [wordSemTheory.get_var_def,lookup_insert])
    \\ rpt_drule0 get_var_get_real_addr_lemma
    \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
    \\ simp [Abbr `t1`]
    \\ rpt (disch_then kall_tac)
    \\ Cases_on `fpb` \\ fs [fp_bop_inst_def]
    \\ rewrite_tac [list_Seq_def] \\ eval_tac
    \\ fs [wordSemTheory.inst_def,wordSemTheory.get_var_def,lookup_insert,
           wordSemTheory.set_fp_var_def,wordSemTheory.get_fp_var_def,
           FLOOKUP_UPDATE,wordSemTheory.set_var_def,w2w_select_id,
           fpSemTheory.fp_bop_comp_def]
    \\ assume_tac(GEN_ALL evaluate_WriteWord64)
    \\ SEP_I_TAC "evaluate" \\ fs[option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,GSYM join_env_locals_def]
    \\ first_x_assum drule0
    \\ simp[wordSemTheory.get_var_def]
    \\ fs[lookup_insert,good_dimindex_def,consume_space_def]
    \\ strip_tac
    \\ clean_tac \\ fs[]
    \\ conj_tac \\ TRY (rw [] \\ NO_TAC)
    \\ (conj_tac
    >-
      (qhdtm_x_assum `limits_inv` mp_tac
      \\ simp[limits_inv_def,FLOOKUP_UPDATE])
    \\ fs [FAPPLY_FUPDATE_THM] \\ rfs [w2w_w2w_64]
    \\ rpt_drule0 memory_rel_less_space
    \\ disch_then match_mp_tac \\ fs []))
  \\ TOP_CASE_TAC \\ fs []
  >-
    (fs[state_rel_def,limits_inv_def]>>
     conj_tac >- metis_tac[backendPropsTheory.option_le_trans,
                           consume_space_stack_max,option_le_max_right]
     \\ qsuff_tac ‘F’ >- rewrite_tac []
     \\ qpat_x_assum ‘encode_header _ _ _ = NONE’ mp_tac
     \\ gvs [encode_header_def,dimword_def]
     \\ `dimindex (:'a) = 32` by rfs [good_dimindex_def] \\ fs [] \\ rveq
     \\ irule_at Any LESS_LESS_EQ_TRANS
     \\ qexists_tac ‘2 ** 2’ \\ gvs []
     \\ gvs [state_rel_thm,limits_inv_def,memory_rel_def,heap_in_memory_store_def]
     \\ CCONTR_TAC
     \\ ‘c.len_size = 1’ by decide_tac
     \\ qpat_x_assum ‘decode_length _ _ = 2w’ mp_tac
     \\ simp [decode_length_def,make_header_def]
     \\ EVAL_TAC \\ simp [dimword_def]
     \\ EVAL_TAC \\ simp [dimword_def])
  \\ `dimindex (:'a) = 32` by rfs [good_dimindex_def] \\ fs [] \\ rveq
  \\ eval_tac
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM wordSemTheory.get_var_def]
  \\ qpat_x_assum `get_var (adjust_var e1) t =
       SOME (Word (get_addr c _ (Word 0w)))` assume_tac
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var (adjust_var e2) t =
       SOME (Word (get_addr c _ (Word 0w)))` assume_tac
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_abbrev_tac `t1 = t with locals := insert 15 _ t.locals`
  \\ `get_var (adjust_var e2) t1 =
       SOME (Word (get_addr c ptr (Word 0w)))` by
   (fs [wordSemTheory.get_var_def,Abbr`t1`,lookup_insert]
    \\ rw [] \\ `EVEN 15` by metis_tac [EVEN_adjust_var] \\ fs [])
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ fs [Abbr`t1`]
  \\ Cases_on `fpb` \\ fs [fp_bop_inst_def]
  \\ rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.inst_def,wordSemTheory.get_var_def,lookup_insert,
         wordSemTheory.set_fp_var_def,wordSemTheory.get_fp_var_def,
         FLOOKUP_UPDATE,wordSemTheory.set_var_def,w2w_select_id,
         fpSemTheory.fp_bop_comp_def,WORD_MUL_LSL]
  \\ rpt (disch_then kall_tac)
  \\ assume_tac(GEN_ALL evaluate_WriteWord64_on_32)
  \\ SEP_I_TAC "evaluate" \\ fs[option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,GSYM join_env_locals_def]
  \\ first_x_assum drule0
  \\ simp[wordSemTheory.get_var_def]
  \\ fs[lookup_insert,good_dimindex_def,consume_space_def]
  \\ rfs [extract_append_id]
  \\ qpat_abbrev_tac `ww = fpSem$fix_NaN _`
  \\ disch_then (qspec_then `ww` mp_tac) \\ fs []
  \\ TRY impl_tac \\ TRY (rw [] \\ NO_TAC)
  \\ strip_tac \\ fs [FAPPLY_FUPDATE_THM]
  \\ rveq \\ fs [] \\ rw []
  \\ qhdtm_x_assum `limits_inv` mp_tac
  \\ simp[limits_inv_def,FLOOKUP_UPDATE]
QED

Theorem assign_FP_uop:
  (∃fpu. op = WordOp (FP_uop fpu)) ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app,oneline do_word_app_def,allowed_op_def]
  \\ every_case_tac \\ fs[]
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ clean_tac
  \\ rename[‘get_vars [e1] s.locals’]
  \\ fs[state_rel_thm,option_le_max_right] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ fs[wordSemTheory.get_vars_def]
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ drule0 memory_rel_Word64_IMP \\ fs []
  \\ strip_tac
  \\ clean_tac \\ rfs []
  \\ simp [assign_FP_uop]
  \\ TOP_CASE_TAC
  >-
    (fs[state_rel_def,limits_inv_def] >>
     conj_tac >- metis_tac[backendPropsTheory.option_le_trans,
                           consume_space_stack_max,option_le_max_right] >>
     fs[consume_space_def,CaseEq"option"] >> rveq >> simp[] >>
     metis_tac[option_le_trans]
    )
  \\ Cases_on `dimindex (:'a) = 64` \\ simp [] THEN1
   (TOP_CASE_TAC \\ fs []
    >- (fs[state_rel_def,limits_inv_def]>>
        conj_tac >- metis_tac[backendPropsTheory.option_le_trans,
                              consume_space_stack_max,option_le_max_right]
        \\ qsuff_tac ‘F’ >- rewrite_tac []
        \\ pop_assum mp_tac
        \\ simp [encode_header_def,dimword_def]
        \\ irule_at Any LESS_LESS_EQ_TRANS
        \\ qexists_tac ‘2 ** 2’ \\ simp []
        \\ gvs [state_rel_thm,limits_inv_def,memory_rel_def,heap_in_memory_store_def])
    \\ clean_tac
    \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
    \\ rpt_drule0 get_var_get_real_addr_lemma
    \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
    \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
    \\ rpt (disch_then kall_tac)
    \\ Cases_on `fpu` \\ fs [fp_bop_inst_def]
    \\ rewrite_tac [list_Seq_def] \\ eval_tac
    \\ fs [wordSemTheory.inst_def,wordSemTheory.get_var_def,lookup_insert,
           wordSemTheory.set_fp_var_def,wordSemTheory.get_fp_var_def,
           FLOOKUP_UPDATE,wordSemTheory.set_var_def,w2w_select_id,
           fpSemTheory.fp_uop_comp_def,fp_uop_inst_def]
    \\ assume_tac(GEN_ALL evaluate_WriteWord64)
    \\ SEP_I_TAC "evaluate" \\ fs[option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,GSYM join_env_locals_def]
    \\ first_x_assum drule0
    \\ simp[wordSemTheory.get_var_def]
    \\ fs[lookup_insert,good_dimindex_def,consume_space_def]
    \\ strip_tac
    \\ clean_tac \\ fs[]
    \\ conj_tac \\ TRY (rw [] \\ NO_TAC)
    \\ (conj_tac >-
      (qhdtm_x_assum `limits_inv` mp_tac
      \\ simp[limits_inv_def,FLOOKUP_UPDATE]))
    \\ fs [FAPPLY_FUPDATE_THM] \\ rfs [w2w_w2w_64]
    \\ rpt_drule0 memory_rel_less_space
    \\ disch_then match_mp_tac \\ fs [])
  \\ TOP_CASE_TAC \\ fs []
  >-
    (fs[state_rel_def,limits_inv_def]>>
     conj_tac >- metis_tac[backendPropsTheory.option_le_trans,
                           consume_space_stack_max,option_le_max_right]
     \\ qsuff_tac ‘F’ >- rewrite_tac []
     \\ qpat_x_assum ‘encode_header _ _ _ = NONE’ mp_tac
     \\ gvs [encode_header_def,dimword_def]
     \\ `dimindex (:'a) = 32` by rfs [good_dimindex_def] \\ fs [] \\ rveq
     \\ irule_at Any LESS_LESS_EQ_TRANS
     \\ qexists_tac ‘2 ** 2’ \\ gvs []
     \\ gvs [state_rel_thm,limits_inv_def,memory_rel_def,heap_in_memory_store_def]
     \\ CCONTR_TAC
     \\ ‘c.len_size = 1’ by decide_tac
     \\ qpat_x_assum ‘decode_length _ _ = 2w’ mp_tac
     \\ simp [decode_length_def,make_header_def]
     \\ EVAL_TAC \\ simp [dimword_def]
     \\ EVAL_TAC \\ simp [dimword_def])
  \\ `dimindex (:'a) = 32` by rfs [good_dimindex_def] \\ fs [] \\ rveq
  \\ eval_tac
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM wordSemTheory.get_var_def]
  \\ qpat_x_assum `get_var (adjust_var e1) t =
       SOME (Word (get_addr c _ (Word 0w)))` assume_tac
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ Cases_on `fpu` \\ fs [fp_bop_inst_def]
  \\ rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.inst_def,wordSemTheory.get_var_def,lookup_insert,
         wordSemTheory.set_fp_var_def,wordSemTheory.get_fp_var_def,
         FLOOKUP_UPDATE,wordSemTheory.set_var_def,w2w_select_id,
         fpSemTheory.fp_bop_comp_def,WORD_MUL_LSL,
         fpSemTheory.fp_uop_comp_def,fp_uop_inst_def]
  \\ rpt (disch_then kall_tac)
  \\ assume_tac(GEN_ALL evaluate_WriteWord64_on_32)
  \\ SEP_I_TAC "evaluate" \\ fs[option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,GSYM join_env_locals_def]
  \\ first_x_assum drule0
  \\ simp[wordSemTheory.get_var_def]
  \\ fs[lookup_insert,good_dimindex_def,consume_space_def]
  \\ rfs [extract_append_id]
  \\ qmatch_goalsub_abbrev_tac `insert dest (Word64 ww) _`
  \\ disch_then (qspec_then `ww` mp_tac) \\ fs []
  \\ strip_tac \\ fs [FAPPLY_FUPDATE_THM]
  \\ rveq \\ fs [] \\ rw []
  \\ qhdtm_x_assum `limits_inv` mp_tac
  \\ simp[limits_inv_def,FLOOKUP_UPDATE]
QED

Theorem join_lemma[local] =
  METIS_PROVE [] “(b1 ⇒ x) ∧ (b2 ⇒ x) ⇒ (b1 ∨ b2 ⇒ x)”;

Theorem imp_assign[local] =
  DB.match ["-"] “_ ==> ^assign_thm_goal” |> map (#1 o #2)
  |> end_itlist (fn x => fn y => MATCH_MP join_lemma (CONJ x y));

Theorem assign_WordOp:
  (∃w. op = WordOp w) ⇒ ^assign_thm_goal
Proof
  strip_tac \\ strip_tac
  \\ irule imp_assign
  \\ asm_rewrite_tac []
  \\ rpt $ first_assum $ irule_at Any
  \\ gvs [] \\ Cases_on ‘w’ \\ gvs []
  \\ rename1 ‘ws:word_size’ \\ Cases_on ‘ws’ \\ gvs []
QED

