(*
  Part of the correctness proof for data_to_word
*)
Theory data_to_word_assignProof
Libs
  preamble helperLib blastLib
Ancestors
  data_to_word_memoryProof data_to_word_gcProof dataSem
  wordSem[qualified] data_to_word int_bitwise dataProps
  copying_gc data_to_word_bignumProof wordProps While set_sep
  semanticsProps alignment backendProps word_bignum wordLang
  word_bignumProof gen_gc_partial gc_shared word_gcFunctions
  gen_gc[qualified] bvi_to_data[qualified]

val _ = (max_print_depth := 1);

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]
val _ = temp_delsimps ["DIV_NUMERAL_THM"]
val _ = temp_delsimps ["fromAList_def", "domain_union",
                       "domain_inter", "domain_difference",
                       "domain_map", "sptree.map_def", "sptree.lookup_rwts",
                       "sptree.insert_notEmpty", "sptree.isEmpty_union"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val _ = numLib.prefer_num ();

fun drule0 th =
  first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))

val _ = hide "next";
val _ = hide "el";
val shift_def = backend_commonTheory.word_shift_def
val isWord_def = wordSemTheory.isWord_def
val theWord_def = wordSemTheory.theWord_def

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
  wordLangTheory.word_op_def, wordLangTheory.word_sh_def];

(* This list must list all auxiliary definitions used in assign_def *)
Theorem assign_def_extras =
  LIST_CONJ
  [LoadWord64_def,WriteWord64_def,BignumHalt_def,LoadBignum_def,
   AnyArith_code_def,Add_code_def,Sub_code_def,Mul_code_def,
   Div_code_def,Mod_code_def, Compare1_code_def, Compare_code_def,
   Equal1_code_def, Equal_code_def, LongDiv1_code_def, LongDiv_code_def,
   ShiftVar_def, generated_bignum_stubs_eq, DivCode_def,
   AddNumSize_def, AnyHeader_def, WriteWord64_on_32_def,
   WriteWord32_on_32_def, AllocVar_def, SilentFFI_def,
   WordOp64_on_32_def, WordShift64_on_32_def, Make_ptr_bits_code_def];

Theorem get_vars_SING:
   dataSem$get_vars args s = SOME [w] ==> ?y. args = [y]
Proof
  Cases_on `args` \\ fs [get_vars_def]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ Cases_on `t` \\ fs [get_vars_def]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
QED

Theorem state_rel_IMP_tstamps:
  state_rel c l1 l2 x t p locs ==>
  ?next_stamp. x.tstamps = SOME next_stamp
Proof
  Cases_on `x.tstamps` \\ fs [state_rel_def]
QED

Theorem INT_EQ_NUM_LEMMA:
   0 <= (i:int) <=> ?index. i = & index
Proof
  Cases_on `i` \\ fs []
QED

Theorem push_if[local]:
  (∀f x y b. (if b then f x else f y) = f (if b then x else y)) ∧
  (∀f h x b. (if b then f x else h x) = (if b then f else h) x)
Proof
  rw []
QED

Theorem split_if[local]:
  (if b then f x else h y) = (if b then f else h) (if b then x else y)
Proof
  rw []
QED

Theorem cut_env_IMP_domain:
   wordSem$cut_names x y = SOME t ==> domain t = domain x
Proof
  fs [wordSemTheory.cut_names_def] \\ rw []
  \\ fs [SUBSET_DEF,EXTENSION,domain_inter] \\ metis_tac []
QED

Theorem cut_envs_wf:
  cut_envs kept_names t = SOME (y1,y2) ⇒ wf y1 ∧ wf y2
Proof
  gvs [wordSemTheory.cut_envs_def,AllCaseEqs()] \\ rw []
  \\ gvs [wordSemTheory.cut_names_def]
QED

Theorem domain_list_insert_thm:
  !l names.
    domain (list_insert l names) = set l ∪ domain names
Proof
 Induct_on `l` >> rw[list_insert_def] >> rw[UNION_DEF,EQ_IMP_THM,FUN_EQ_THM] >> rw[]
QED

Theorem cut_env_lookup:
  wordSem$cut_env names t = SOME y ∧
  lookup n y = SOME a ⇒
  lookup n t = SOME a
Proof
  PairCases_on ‘names’
  \\ gvs [wordSemTheory.cut_env_def,wordSemTheory.cut_envs_def]
  \\ gvs [wordSemTheory.cut_names_def,AllCaseEqs()] \\ rw []
  \\ gvs [lookup_union,AllCaseEqs(),lookup_inter_alt]
QED

Theorem cut_env_get_vars_get_vars:
  ∀vs ws ws'.
    cut_env kept_names t.locals = SOME y ∧
    get_vars vs (t with locals := y) = SOME ws ∧
    get_vars vs t = SOME ws' ⇒
    ws = ws'
Proof
  Induct \\ gvs [wordSemTheory.get_vars_def,AllCaseEqs()]
  \\ rw [wordSemTheory.get_var_def]
  \\ drule_all cut_env_lookup \\ gvs []
QED

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

Theorem get_real_offset_lemma:
   get_var v t = SOME (Word i_w) /\
    good_dimindex (:'a) /\
    get_real_offset i_w = SOME y ==>
    word_exp t (real_offset c v) = SOME (Word (y:'a word))
Proof
  fs [get_real_offset_def] \\ every_case_tac \\ fs []
  \\ fs [wordSemTheory.get_var_def,real_offset_def] \\ eval_tac \\ fs []
  \\ fs [good_dimindex_def,dimword_def] \\ rw []
    \\ fs [wordSemTheory.get_var_def,real_offset_def]
QED

Theorem state_rel_push_env_loc:
  state_rel c n l s (call_env args b (push_env (y1,y2) NONE t)) ys ((l1,l2)::locs) ⇒
  lookup 0 y1 = SOME (Loc l1 l2)
Proof
  rw [state_rel_thm]
  \\ gvs [wordSemTheory.push_env_def]
  \\ pairarg_tac \\ gvs [wordSemTheory.call_env_def,contains_loc_def]
  \\ gvs [ALOOKUP_toAList]
QED

Theorem evaluate_IMP_domain_union:
  evaluate (p,call_env args b (push_env (y1,y2) NONE (t:('a,'c,'ffi) wordSem$state)) with
              <|clock := ck; termdep := tp |>) = (SOME (Result ret1 ret2),t1) ∧
  pop_env t1 = SOME t2 ∧
  lookup 0 y1 = SOME (Loc l1 l2) ∧
  cut_envs (adjust_sets kept_names) t.locals = SOME (y1,y2) ⇒
  domain t2.locals = domain y1 ∪ domain y2 ∧
  lookup 0 t2.locals = SOME (Loc l1 l2)
Proof
  strip_tac
  \\ fs [wordSemTheory.call_env_def, wordSemTheory.push_env_def,
         wordSemTheory.dec_clock_def, dataSemTheory.dec_clock_def]
  \\ pairarg_tac \\ fs []
  \\ qmatch_asmsub_abbrev_tac `stack_max_fupd(K smnew)`
  \\ qmatch_asmsub_abbrev_tac `locals_fupd(K lcnew)`
  \\ qspecl_then [`p`,`t with
                   <|locals := lcnew;
                     locals_size := b;
                     stack := StackFrame t.locals_size (toAList y1) l NONE::t.stack;
                     stack_max := smnew; permute := permute;
                     clock := ck; termdep := tp|>`] mp_tac
                 (wordPropsTheory.evaluate_stack_swap
                    |> INST_TYPE [``:'b``|->``:'c``,``:'c``|->``:'ffi``])
  \\ fs [] \\ fs [wordSemTheory.pop_env_def]
  \\ Cases_on `t1.stack` \\ fs []
  \\ qmatch_assum_rename_tac `t1.stack = hr::tr`
  \\ Cases_on `hr` \\ fs []
  \\ rpt strip_tac
  \\ gvs [s_key_eq_def,oneline s_frame_key_eq_def]
  \\ gvs [AllCaseEqs()]
  \\ gvs [domain_union,domain_fromAList_toAList]
  \\ rw [] \\ drule0 env_to_list_lookup_equiv
  \\ fs [EXTENSION,domain_lookup,lookup_fromAList,lookup_union,
         lookup_fromAList,ALOOKUP_toAList]
  \\ ‘ALOOKUP l0 0 = NONE’ by
    (simp [ALOOKUP_NONE]
     \\ qpat_x_assum ‘MAP _ _ = MAP FST l0’ $ assume_tac o GSYM
     \\ simp []
     \\ CCONTR_TAC \\ gvs [MEM_MAP,EXISTS_PROD]
     \\ rw [] \\ drule0 env_to_list_lookup_equiv
     \\ strip_tac
     \\ pop_assum drule
     \\ gvs [wordSemTheory.cut_envs_def,adjust_sets_def,AllCaseEqs(),
             wordSemTheory.cut_names_def]
     \\ strip_tac \\ gvs [lookup_inter_alt,data_to_word_gcProofTheory.NOT_0_domain])
  \\ fs[GSYM IS_SOME_EXISTS]
  \\ imp_res_tac MAP_FST_EQ_IMP_IS_SOME_ALOOKUP
  \\ rpt(qpat_x_assum `!n. _ (IS_SOME _) (IS_SOME _)` mp_tac)
  \\ rpt(pop_assum kall_tac) \\ metis_tac[]
QED

Theorem get_real_byte_offset_lemma:
   get_var v t = SOME (Word (w:α word)) ∧ good_dimindex (:α) ⇒
   word_exp t (real_byte_offset v) = SOME (Word (bytes_in_word + (w >>> 2)))
Proof
  rw[real_byte_offset_def,wordSemTheory.get_var_def]
  \\ eval_tac \\ fs[good_dimindex_def]
QED

Theorem reorder_lemma:
  memory_rel c be ts x.refs x.space t.store t.memory t.mdomain (x1::x2::x3::xs) ==>
  memory_rel c be ts x.refs x.space t.store t.memory t.mdomain (x3::x1::x2::xs)
Proof
  match_mp_tac memory_rel_rearrange \\ fs [] \\ rw [] \\ fs []
QED

Theorem reorder_2_lemma:
  memory_rel c be ts x.refs x.space t.store t.memory t.mdomain (x1::x2::xs) ==>
  memory_rel c be ts x.refs x.space t.store t.memory t.mdomain (x2::x1::xs)
Proof
  match_mp_tac memory_rel_rearrange \\ fs [] \\ rw [] \\ fs []
QED

Theorem evaluate_StoreEach = Q.prove(`
  !xs ys t offset m1.
      store_list (a + offset) ys t.memory t.mdomain = SOME m1 /\
      get_vars xs t = SOME ys /\
      get_var i t = SOME (Word a) ==>
      evaluate (StoreEach i xs offset, t) = (NONE,t with memory := m1)`,
  Induct
  \\ fs [store_list_def,StoreEach_def] \\ eval_tac
  \\ fs [wordSemTheory.state_component_equality,
           wordSemTheory.get_vars_def,store_list_def,
           wordSemTheory.get_var_def]
  \\ rw [] \\ fs [] \\ CASE_TAC \\ fs []
  \\ Cases_on `get_vars xs t` \\ fs [] \\ clean_tac
  \\ fs [store_list_def,wordSemTheory.mem_store_def]
  \\ `(t with memory := m1) =
      (t with memory := (a + offset =+ x) t.memory) with memory := m1` by
       (fs [wordSemTheory.state_component_equality] \\ NO_TAC)
  \\ pop_assum (fn th => rewrite_tac [th])
  \\ first_x_assum match_mp_tac \\ fs []
  \\ asm_exists_tac \\ fs []
  \\ rename1 `get_vars qs t = SOME ts`
  \\ pop_assum mp_tac
  \\ qspec_tac (`ts`,`ts`)
  \\ qspec_tac (`qs`,`qs`)
  \\ Induct \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def]
  \\ rw [] \\ every_case_tac \\ fs [])
  |> Q.SPECL [`xs`,`ys`,`t`,`0w`] |> SIMP_RULE (srw_ss()) [] |> GEN_ALL;

Theorem get_vars_adjust_var:
   ODD k ==>
    get_vars (MAP adjust_var args) (t with locals := insert k w s) =
    get_vars (MAP adjust_var args) (t with locals := s)
Proof
  Induct_on `args`
  \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def,lookup_insert]
  \\ rw [] \\ fs [ODD_EVEN,EVEN_adjust_var]
QED

Theorem get_vars_with_store:
   !args. get_vars args (t with <| locals := t.locals ; store := s |>) =
           get_vars args t
Proof
  Induct \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def]
QED

Theorem word_less_lemma1:
   v2 < (v1:'a word) <=> ~(v1 <= v2)
Proof
  metis_tac [WORD_NOT_LESS]
QED

Theorem get_vars_2_imp:
   wordSem$get_vars [x1;x2] s = SOME [y1;y2] ==>
    wordSem$get_var x1 s = SOME y1 /\
    wordSem$get_var x2 s = SOME y2
Proof
  fs [wordSemTheory.get_vars_def] \\ every_case_tac \\ fs []
QED

Theorem get_vars_1_imp:
   wordSem$get_vars [x1] s = SOME [y1] ==>
    wordSem$get_var x1 s = SOME y1
Proof
  fs [wordSemTheory.get_vars_def] \\ every_case_tac \\ fs []
QED

Theorem LESS_DIV_16_IMP:
   n < k DIV 16 ==> 16 * n + 2 < k:num
Proof
  fs [X_LT_DIV]
QED

Theorem lookup_loc_lemma:
   env_to_list y2 permute = (l',permute') ∧
   cut_envs (adjust_sets keep_names) locals = SOME (y1,y2) ∧
   lookup 0 (union y2 y1) = SOME (Loc l1 l2) ⇒
   ALOOKUP l' 0 = NONE ∧ lookup 0 y1 = SOME (Loc l1 l2)
Proof
  strip_tac
  \\ imp_res_tac wordPropsTheory.env_to_list_lookup_equiv
  \\ gvs []
  \\ reverse conj_asm1_tac
  >- gvs [lookup_union]
  \\ gvs [adjust_sets_def,wordSemTheory.cut_envs_def]
  \\ gvs [AllCaseEqs(),wordSemTheory.cut_names_def]
  \\ gvs [lookup_inter_alt,data_to_word_gcProofTheory.NOT_0_domain]
QED

Theorem word_exp_real_addr:
   get_real_addr c t.store ptr_w = SOME a /\
    shift_length c < dimindex (:α) ∧ good_dimindex (:α) /\
    lookup (adjust_var a1) (t:('a,'c,'ffi) wordSem$state).locals = SOME (Word ptr_w) ==>
    !w. word_exp (t with locals := insert 1 (Word (w:'a word)) t.locals)
          (real_addr c (adjust_var a1)) = SOME (Word a)
Proof
  rpt strip_tac \\ match_mp_tac (GEN_ALL get_real_addr_lemma)
  \\ fs [wordSemTheory.get_var_def,lookup_insert]
QED

Theorem word_exp_real_addr_2:
   get_real_addr c (t:('a,'c,'ffi) wordSem$state).store ptr_w = SOME a /\
    shift_length c < dimindex (:α) ∧ good_dimindex (:α) /\
    lookup (adjust_var a1) t.locals = SOME (Word ptr_w) ==>
    !w1 w2.
      word_exp
        (t with locals := insert 3 (Word (w1:'a word)) (insert 1 (Word w2) t.locals))
        (real_addr c (adjust_var a1)) = SOME (Word a)
Proof
  rpt strip_tac \\ match_mp_tac (GEN_ALL get_real_addr_lemma)
  \\ fs [wordSemTheory.get_var_def,lookup_insert]
QED

Theorem encode_header_IMP_BIT0:
   encode_header c tag l = SOME w ==> w ' 0
Proof
  fs [encode_header_def,make_header_def] \\ rw []
  \\ fs [word_or_def,fcpTheory.FCP_BETA,word_index]
QED

Theorem get_addr_inj:
   p1 * 2 ** shift_length c < dimword (:'a) ∧
   p2 * 2 ** shift_length c < dimword (:'a) ∧
   get_addr c p1 (Word (0w:'a word)) = get_addr c p2 (Word 0w)
   ⇒ p1 = p2
Proof
  rw[get_addr_def,get_lowerbits_def]
  \\ `1 < 2 ** shift_length c` by (
    fs[ONE_LT_EXP,shift_length_NOT_ZERO,GSYM NOT_ZERO_LT_ZERO] )
  \\ `dimword (:'a) < dimword(:'a) * 2 ** shift_length c` by fs[]
  \\ `p1 < dimword (:'a) ∧ p2 < dimword (:'a)`
  by (
    imp_res_tac LESS_TRANS
    \\ fs[LT_MULT_LCANCEL])
  \\ `n2w p1 << shift_length c >>> shift_length c = n2w p1`
  by ( match_mp_tac lsl_lsr \\ fs[] )
  \\ `n2w p2 << shift_length c >>> shift_length c = n2w p2`
  by ( match_mp_tac lsl_lsr \\ fs[] )
  \\ qmatch_assum_abbrev_tac`(x || 1w) = (y || 1w)`
  \\ `x = y`
  by (
    unabbrev_all_tac
    \\ fsrw_tac[wordsLib.WORD_BIT_EQ_ss][]
    \\ rw[]
    \\ rfs[word_index]
    \\ Cases_on`i` \\ fs[]
    \\ last_x_assum(qspec_then`SUC n`mp_tac)
    \\ simp[] )
  \\ `n2w p1 = n2w p2` by metis_tac[]
  \\ imp_res_tac n2w_11
  \\ rfs[]
QED

Theorem Word64Rep_inj:
   good_dimindex(:'a) ⇒
   (Word64Rep (:'a) w1 = Word64Rep (:'a) w2 ⇔ w1 = w2)
Proof
  rw[good_dimindex_def,Word64Rep_def]
  \\ srw_tac[wordsLib.WORD_BIT_EQ_ss][Word64Rep_def,EQ_IMP_THM]
QED

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

Theorem lookup_IMP_insert_EQ:
   !t x y. lookup x t = SOME y ==> insert x y t = t
Proof
  Induct \\ fs [lookup_def,Once insert_def] \\ rw []
QED

Theorem set_vars_sing:
   set_vars [n] [w] t = set_var n w t
Proof
  EVAL_TAC
QED

Theorem NONNEG_INT:
   0 <= (i:int) ==> ?j. i = & j
Proof
  Cases_on `i` \\ fs []
QED

Theorem BIT_X_1:
   BIT i 1 = (i = 0)
Proof
  EQ_TAC \\ rw []
QED

Theorem minus_2_word_and_id:
   ~(w ' 0) ==> (-2w && w) = w
Proof
  fs [fcpTheory.CART_EQ,word_and_def,fcpTheory.FCP_BETA]
  \\ rewrite_tac [GSYM (SIMP_CONV (srw_ss()) [] ``~1w``)]
  \\ Cases_on `w`
  \\ simp_tac std_ss [word_1comp_def,fcpTheory.FCP_BETA,word_index,
        DIMINDEX_GT_0,BIT_X_1] \\ metis_tac []
QED

Theorem FOUR_MUL_LSL:
   n2w (4 * i) << k = n2w i << (k + 2)
Proof
  fs [WORD_MUL_LSL,EXP_ADD,word_mul_n2w]
QED

Theorem evaluate_BignumHalt:
   state_rel c l1 l2 s t [] locs /\
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

(* TODO: should probably replace evaluate_GiveUp directly *)
Theorem evaluate_GiveUp2:
  state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) [] locs ==>
  ?r. evaluate (GiveUp,t) = (SOME NotEnoughSpace,r) /\
    r.ffi = s.ffi /\ t.ffi = s.ffi ∧
    option_le r.stack_max t.stack_max
Proof
  strip_tac>>drule evaluate_GiveUp>>rw[]>>qexists_tac`r`>>
  fs [GiveUp_def,wordSemTheory.evaluate_def,wordSemTheory.word_exp_def]>>
  rw[]>>
  fs [wordSemTheory.alloc_def]>>every_case_tac>>fs[wordSemTheory.flush_state_def]>>
  rw[]>>fs[]>>
  drule gc_const>>
  rw[]>>
  `x''.stack_max = x'.stack_max` by fs[pop_env_const]>>
  fs[wordSemTheory.push_env_def]>>
  pairarg_tac>>fs[]>>
  qmatch_goalsub_abbrev_tac`stack_size tt`>>
  `stack_size tt = OPTION_MAP2 $+ (stack_size t.stack) t.locals_size` by
    (simp[Abbr`tt`]>>EVAL_TAC>>
    simp[OPTION_MAP2_DEF]>>rw[]>>fs[]>>
    qpat_x_assum`_ = NONE` SUBST_ALL_TAC>>fs[])>>
  fs[state_rel_def,option_le_OPTION_MAP2_MAX]>>
  metis_tac[]
QED

Theorem evaluate_BignumHalt2:
   state_rel c l1 l2 s t [] locs /\
    get_var reg t = SOME (Word w) ==>
    ∃r. (evaluate (BignumHalt reg,t) =
          if w ' 0 then (SOME NotEnoughSpace,r)
          else (NONE,t)) ∧ r.ffi = s.ffi ∧ t.ffi = s.ffi /\
                           option_le r.stack_max t.stack_max
Proof
  fs [BignumHalt_def,wordSemTheory.evaluate_def,word_exp_rw,
      asmTheory.word_cmp_def,word_and_one_eq_0_iff |> SIMP_RULE (srw_ss()) []]
  \\ IF_CASES_TAC \\ fs []
  THEN1 (rw [] \\ qexists_tac `t` \\ fs [state_rel_def])
  \\ rw [] \\ match_mp_tac evaluate_GiveUp2 \\ fs []
QED

Theorem state_rel_get_var_Number_IMP_alt:
   !k i. state_rel c l1 l2 s t [] locs /\
          get_var k s.locals = SOME (Number i) /\
          get_var (2 * k + 2) t = SOME a1 ==>
          ?w:'a word. a1 = Word w /\ w ' 0 = ~small_int (:'a) i
Proof
  fs [state_rel_thm] \\ rw []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 memory_rel_get_var_IMP
  \\ fs [adjust_var_def] \\ rw []
  \\ imp_res_tac memory_rel_any_Number_IMP \\ fs []
QED

(* TODO: move to sptreeTheory *)
Theorem EXISTS_NOT_IN_spt_DOMAIN[local]:
  ∃x. x ∉ domain (refs : 'a spt)
Proof
  assume_tac (Q.INST [`t` |-> `refs`] FINITE_domain
                      |> CONJ INFINITE_NUM_UNIV
                      |> MATCH_MP IN_INFINITE_NOT_FINITE
                      |> SIMP_RULE std_ss [IN_UNIV])
  \\ rw []
QED

(* TODO: move to sptreeTheory *)
Theorem LEAST_NOTIN_spt_DOMAIN:
  ∀refs. (LEAST x. x ∉ domain (refs : 'a num_map)) ∉ domain refs
Proof
  rw []
  \\ assume_tac EXISTS_NOT_IN_spt_DOMAIN
  \\ fs [LEAST_EXISTS]
QED

(*TODO: move to backendProps *)
Theorem option_le_add_indv:
  option_le (OPTION_MAP2 $+ n m) r ==> option_le n r /\ option_le m r
Proof
  rw [] \\ Cases_on `n` \\ Cases_on `m` \\ Cases_on `r`
  \\ fs [OPTION_MAP2_DEF, option_le_def, IS_SOME_DEF]
QED

Theorem option_le_add_drop_right:
  option_le x y ⇒
  option_le x (OPTION_MAP2 $+ z y)
Proof
  rw[]>>match_mp_tac option_le_trans>>asm_exists_tac>>
  simp[]>>
  metis_tac[option_add_comm,option_le_add]
QED

Theorem word_exp_SmallLsr:
   word_exp s (SmallLsr e n) =
      if dimindex (:'a) <= n then NONE else
      case word_exp s e of
        | SOME (Word w) => SOME (Word ((w:'a word) >>> n))
        | res => (if n = 0 then res else NONE)
Proof
  rw [SmallLsr_def] \\ assume_tac DIMINDEX_GT_0
  \\ TRY (`F` by decide_tac \\ NO_TAC)
  THEN1
   (full_simp_tac std_ss [GSYM NOT_LESS]
    \\ Cases_on `word_exp s e` \\ fs []
    \\ Cases_on `x` \\ fs [])
  \\ fs [word_exp_rw] \\ every_case_tac \\ fs []
QED

Theorem evaluate_MakeBytes:
   good_dimindex (:'a) ==>
    evaluate (MakeBytes n,s) =
      case get_var n s of
      | SOME (Word w) => (NONE,set_var n (Word (word_of_byte ((w:'a word) >>> 2))) s)
      | _ => (SOME Error,s)
Proof
  fs [MakeBytes_def,list_Seq_def,wordSemTheory.evaluate_def,word_exp_rw,
      wordSemTheory.get_var_def] \\ strip_tac
  \\ Cases_on `lookup n s.locals` \\ fs []
  \\ Cases_on `x` \\ fs [] \\ IF_CASES_TAC
  \\ fs [EVAL ``good_dimindex (:'a)``]
  \\ fs [wordSemTheory.set_var_def,
         wordSemTheory.get_var_def,lookup_insert,word_of_byte_def,
         insert_shadow,wordSemTheory.evaluate_def,word_exp_rw]
QED

Theorem w2w_shift_shift:
   good_dimindex (:'a) ==> ((w2w (w:word8) ≪ 2 ⋙ 2) : 'a word) = w2w w
Proof
  fs [good_dimindex_def,fcpTheory.CART_EQ,
      word_lsl_def,word_lsr_def,fcpTheory.FCP_BETA,w2w]
  \\ rw [] \\ fs [] \\ EQ_TAC \\ rw [] \\ rfs [fcpTheory.FCP_BETA,w2w]
QED

fun sort_tac n =
  CONV_TAC(PATH_CONV(String.concat(List.tabulate(n,(K "lr"))))(REWR_CONV set_byte_sort)) \\
  simp[good_dimindex_def]

Theorem evaluate_WriteLastBytes:
   good_dimindex(:'a) ∧ w2n n < dimindex(:'a) DIV 8 ∧
   get_vars [av;bv;nv] (s:('a,'c,'ffi)wordSem$state) = SOME [Word (a:'a word); Word b; Word n] ∧
   byte_aligned a ∧ a ∈ s.mdomain ∧ s.memory a = Word w
  ⇒
   evaluate (WriteLastBytes av bv nv,s) =
     (NONE, s with memory := (a =+ Word (last_bytes (w2n n) (w2w b) 0w w s.be)) s.memory)
Proof
  rw[good_dimindex_def]
  \\ fs[get_vars_SOME_IFF]
  \\ simp[WriteLastBytes_def]
  \\ simp[WriteLastByte_aux_def]
  \\ map_every (let
      val th = CONV_RULE(RESORT_FORALL_CONV(sort_vars["p","b"])) align_add_aligned
      val th = Q.SPEC`LOG2 (dimindex(:'a) DIV 8)`th
      val th2 = set_byte_change_a |> Q.GEN`b` |> Q.SPEC`w2w b` |> Q.GENL[`be`,`a`,`a'`,`w`]
      in (fn n =>
       let val nw = Int.toString n ^ "w" in
         qspecl_then([[QUOTE nw],`a`])mp_tac th \\
         qspecl_then([`s.be`,[QUOTE (nw^"+ byte_align a")], [QUOTE nw]])mp_tac th2
       end) end)
       (List.tabulate(8,I))
  \\ simp_tac std_ss [GSYM byte_align_def,GSYM byte_aligned_def]
  \\ fs[w2n_add_byte_align_lemma,good_dimindex_def]
  \\ fs[dimword_def]
  \\ rpt strip_tac
  \\ fs[wordSemTheory.evaluate_def,wordSemTheory.inst_def,
        wordSemTheory.get_var_imm_def,
        word_exp_rw, wordSemTheory.get_var_def,
        asmTheory.word_cmp_def,last_bytes_simp,
        wordSemTheory.mem_store_byte_aux_def,
        APPLY_UPDATE_THM]
  \\ rw[wordSemTheory.state_component_equality,
        FUN_EQ_THM,APPLY_UPDATE_THM,
        dimword_def, last_bytes_simp]
  \\ rw[] \\ rw[] \\ rfs[dimword_def]
  >- ( simp[Once set_byte_sort,good_dimindex_def] )
  >- ( map_every sort_tac [1,2,1])
  >- ( Cases_on`n` \\ fs[dimword_def] \\ rfs[] )
  >- ( simp[Once set_byte_sort,good_dimindex_def] )
  >- ( map_every sort_tac [1,2,1] )
  >- ( map_every sort_tac [1,2,3,2,1,2] )
  >- ( map_every sort_tac [1,2,3,4,3,2,1,2,3,2] )
  >- ( map_every sort_tac [1,2,3,4,5,4,3,2,1,2,3,4,3,2,3] )
  >- ( map_every sort_tac [1,2,3,4,5,6,5,4,3,2,1,2,3,4,5,4,3,2,3,4,5,4,3,4,3,4,5] )
  >- ( Cases_on`n` \\ fs[dimword_def] \\ rfs[] )
QED

Theorem byte_aligned_bytes_in_word:
   good_dimindex (:'a) ==>
    byte_aligned (w * bytes_in_word) /\
    byte_aligned (bytes_in_word * w:'a word)
Proof
  fs [byte_aligned_def,good_dimindex_def] \\ rw []
  \\ fs [bytes_in_word_def]
  \\ `aligned 2 (0w + w * n2w (2 ** 2)) /\
      aligned 3 (0w + w * n2w (2 ** 3))` by
    (Cases_on `w` \\ rewrite_tac [word_mul_n2w,aligned_add_pow,aligned_0])
  \\ fs []
QED

Definition is_env_def:
 is_env st = (?n vs. st = Env n vs)
End

(* TODO: copypasta from costPropsScript *)
Theorem size_of_Number_head:
  ∀vs lims refs seen n b.
  small_num lims.arch_64_bit n ⇒
  (size_of lims (Number n::vs) refs seen = size_of lims vs refs seen)
Proof
  Cases \\ rw [size_of_def] \\ pairarg_tac \\ fs []
QED

Theorem ADD4DIV4[local] =
  ADD_DIV_ADD_DIV |> Q.SPEC `4` |> SIMP_RULE std_ss []
  |> Q.SPEC `1` |> SIMP_RULE std_ss[]
  |> Q.SPEC `i` |> PURE_ONCE_REWRITE_RULE [ADD_SYM];

Theorem ADD8DIV8[local] =
  ADD_DIV_ADD_DIV |> Q.SPEC `8` |> SIMP_RULE std_ss []
  |> Q.SPEC `1` |> SIMP_RULE std_ss[]
  |> Q.SPEC `i` |> PURE_ONCE_REWRITE_RULE [ADD_SYM];

Theorem RefByte_thm:
   state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) [] locs /\
    get_vars [0;1;2] s.locals = SOME (vals ++ [Number &(if fl then 0 else 4)]) /\
    t.clock = MustTerminate_limit (:'a) - 1 /\
    pop_env s = SOME s1 /\ is_env(HD s.stack) /\
    s.locals_size = lookup RefByte_location s.stack_frame_sizes /\
    do_app (MemOp (RefByte fl)) vals s1 = Rval (v,s2) ==>
    ?q r new_c.
      evaluate (RefByte_code c,t) = (q,r) /\
      if q = SOME NotEnoughSpace then
        r.ffi = t.ffi ∧
        option_le r.stack_max s2.stack_max /\
        (c.gc_kind <> None ==>
         case vals of
              (Number i::_) =>
              (i < 0 \/
              ~small_num s.limits.arch_64_bit i \/
              ~(Num i DIV (arch_size s.limits DIV 8) < dimword (:α) DIV arch_size s.limits) \/
              ~(Num i DIV (arch_size s.limits DIV 8) + 1 < (2 ** c.len_size)) \/
              s1.limits.heap_limit <
              size_of_heap s1 + Num i DIV (arch_size s.limits DIV 8) + 2)
         )
      else
        ?rv. q = SOME (Result (Loc l1 l2) [rv]) /\
             state_rel c r1 r2 (s2 with <| locals := LN;
                                           locals_size := SOME 0;
                                           clock := new_c;
                                           stack := s.stack |>)
                r [(v,rv)] locs
Proof
  qpat_abbrev_tac`tag = if fl then _ else _`
  \\ fs [RefByte_code_def]
  \\ fs [do_app_def,do_space_def,EVAL ``op_space_reset (MemOp (RefByte fl))``,do_app_aux_def]
  \\ Cases_on `vals` \\ fs []
  \\ Cases_on `t'` \\ fs []
  \\ Cases_on `h` \\ fs []
  \\ Cases_on `t''` \\ fs []
  \\ Cases_on `h'` \\ fs []
  \\ IF_CASES_TAC \\ fs [] \\ rw []
  \\ `good_dimindex (:'a)` by fs [state_rel_def]
  \\ drule0 NONNEG_INT \\ strip_tac \\ rveq \\ fs []
  \\ rename1 `get_vars [0; 1; 2] s.locals = SOME [Number (&i); Number (&w2n w); Number &tag]`
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw]
  \\ rpt_drule0 state_rel_get_vars_IMP \\ strip_tac \\ fs [LENGTH_EQ_NUM_compute]
  \\ rveq \\ fs [adjust_var_def,get_vars_SOME_IFF]
  \\ fs [get_vars_SOME_IFF_data]
  \\ drule0 (Q.GEN`a1`(Q.SPEC `0` state_rel_get_var_Number_IMP_alt)) \\ fs []
  \\ strip_tac \\ rveq
  \\ rpt_drule0 evaluate_BignumHalt2
  \\ reverse (Cases_on `small_int (:α) (&i)` \\ fs [] \\ strip_tac \\ fs [])
  >-
    (conj_tac >-
       (fs[do_stack_def,stack_consumed_def,state_rel_def,pop_env_def,CaseEq"option",
           CaseEq"list",CaseEq"stack"]>>rveq>>
        match_mp_tac option_le_trans>>asm_exists_tac>>fs[]>>
        match_mp_tac option_le_trans>>asm_exists_tac>>fs[]>>
        simp[option_le_max_right]) >>
     strip_tac >> spose_not_then strip_assume_tac >>
     fs[small_int_def,state_rel_def,good_dimindex_def,limits_inv_def,arch_size_def,dimword_def,
        pop_env_def,CaseEq"option",CaseEq"list",CaseEq"stack"] >>
     rveq >> rfs[] >> fs[DIV_LT_X]
    )
  \\ ntac 3 (pop_assum kall_tac)
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw]
  \\ rpt_drule0 state_rel_get_vars_IMP \\ strip_tac \\ fs [LENGTH_EQ_2]
  \\ rveq \\ fs [adjust_var_def,get_vars_SOME_IFF]
  \\ fs [wordSemTheory.get_var_def]
  \\ `w' = n2w (4 * i) /\ 4 * i < dimword (:'a)` by
   (fs [state_rel_thm]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ qpat_x_assum `get_var 0 s.locals = SOME (Number (&i))` assume_tac
    \\ rpt_drule0 memory_rel_get_var_IMP \\ fs [adjust_var_def]
    \\ fs [wordSemTheory.get_var_def]
    \\ strip_tac \\ imp_res_tac memory_rel_Number_IMP
    \\ fs [Smallnum_def] \\ fs [small_int_def] \\ fs [X_LT_DIV] \\ NO_TAC)
  \\ rveq \\ fs [word_exp_SmallLsr]
  \\ IF_CASES_TAC
  THEN1 (fs [shift_def,state_rel_def,
             EVAL ``good_dimindex (:'a)``] \\ rfs []) \\ fs []
  \\ pop_assum kall_tac
  \\ fs [word_exp_rw]
  \\ IF_CASES_TAC
  THEN1 (fs [shift_def,state_rel_def,
             EVAL ``good_dimindex (:'a)``] \\ rfs []) \\ fs []
  \\ pop_assum kall_tac
  \\ `n2w (4 * i) ⋙ 2 = (n2w i):'a word` by
   (rewrite_tac [GSYM w2n_11,w2n_lsr]
    \\ fs [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV] \\ NO_TAC) \\ fs []
  \\ qabbrev_tac `wA = ((bytes_in_word + n2w i)
        ⋙ (dimindex (:α) − 63)):'a word`
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw]
  \\ `state_rel c l1 l2 s (set_var 1 (Word wA) t) [] locs` by
        fs [wordSemTheory.set_var_def,state_rel_insert_1]
  \\ rpt_drule0 AllocVar_thm
  \\ `?x. dataSem$cut_env (fromList [();();()]) s.locals = SOME x` by
    (fs [EVAL ``sptree$fromList [(); (); ()]``,cut_env_def,domain_lookup,
         get_var_def,get_vars_SOME_IFF_data] \\ NO_TAC)
  \\ disch_then drule0
  \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def]
  \\ qabbrev_tac `limit = MIN (2 ** c.len_size) (dimword (:α) DIV 16)`
  \\ fs [get_var_set_var_thm]
  \\ Cases_on `evaluate
       (AllocVar c limit (fromList [(); (); ()]),set_var 1 (Word wA) t)` \\ fs []
  \\ disch_then drule0
  \\ impl_tac THEN1 (unabbrev_all_tac \\ fs []
                     \\ fs [state_rel_def,EVAL ``good_dimindex (:'a)``,dimword_def])
  \\ strip_tac \\ fs [set_vars_sing]
  \\ reverse IF_CASES_TAC \\ fs []
  >- (fs[do_stack_def,option_le_max_right,pop_env_def,CaseEq"list",CaseEq"stack"] >>
      rveq >> fs[] >> rfs[is_env_def] >>
      strip_tac >>
      spose_not_then strip_assume_tac >>
      `w2n wA DIV (arch_size s.limits DIV 8) < limit`
        by(fs[Abbr`wA`,Abbr`limit`,state_rel_def,limits_inv_def,good_dimindex_def] >>
           rfs[dimword_def] >>
           fs[] >>
           `~word_msb(bytes_in_word:'a word)`
             by(fs[word_msb_def,bytes_in_word_def] >>
                wordsLib.WORD_EVAL_TAC >> rw[]) >>
           `~word_msb(n2w i)`
             by(fs[word_msb_def,bytes_in_word_def] >>
                wordsLib.WORD_EVAL_TAC >> rw[] >>
                match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP >>
                fs[]) >>
           simp[w2n_add,dimword_def,w2n_lsr] >>
           simp[bytes_in_word_def,dimword_def,DIV_DIV_DIV_MULT] >>
           simp[ADD4DIV4,ADD8DIV8] >>
           rfs[arch_size_def,limits_inv_def] >>
           (conj_tac >-
              (match_mp_tac LESS_EQ_LESS_TRANS >>
               HINT_EXISTS_TAC >>
               rw[] >>
               fs[DIV_LE_X] >> rpt(pop_assum kall_tac) >> intLib.COOPER_TAC)) >>
           fs[DIV_LT_X]) >>
      fs[space_consumed_def] >>
      `size_of_heap (cut_locals (fromList [(); (); ()]) s) =
       size_of_heap
             (s with <|locals := e; locals_size := ss; stack := xs|>)`
        by(fs[cut_locals_def,cut_env_def,size_of_heap_def,
              stack_to_vs_def,extract_stack_def
             ] >> rveq >>
           fs[fromList_def] >>
           rfs[] >>
           `inter s.locals (fromList [();();()]) =
            inter (insert 2 (THE(lookup 2 s.locals))
                   (insert 1 (THE(lookup 1 s.locals))
                    (insert 0 (THE(lookup 0 s.locals)) LN)))
                   (fromList [();();()])`
            by(fs[dataSemTheory.get_var_def] >>
               rw[inter_eq,lookup_inter,lookup_insert,lookup_fromList] >>
               fs[] >>
               fs[lookup_def] >> TOP_CASE_TAC >> rw[]) >>
           pop_assum(SUBST_ALL_TAC o SIMP_RULE list_ss [fromList_def]) >>
           rpt(CHANGED_TAC(simp[Once insert_def])) >>
           simp[inter_def,mk_BS_def,toList_def] >>
           fs[toList_def,toListA_def,dataSemTheory.get_var_def] >>
           `small_num s.limits.arch_64_bit (&tag)` by rw[small_num_def,Abbr `tag`] >>
           `small_num s.limits.arch_64_bit (&w2n w)`
             by(fs[small_num_def,small_int_def] >> rw[] >>
                match_mp_tac LESS_TRANS >>
                qexists_tac `dimword(:8)` >>
                (conj_tac >- MATCH_ACCEPT_TAC w2n_lt) >>
                rw[]) >>
           simp[size_of_Number_head]) >>
      fs[] >>
      fs[Abbr`wA`,Abbr`limit`,state_rel_def,good_dimindex_def] >>
      rfs[dimword_def] >>
      fs[] >>
      `~word_msb(bytes_in_word:'a word)`
        by(fs[word_msb_def,bytes_in_word_def] >>
           wordsLib.WORD_EVAL_TAC >> rw[]) >>
      `~word_msb(n2w i)`
        by(fs[word_msb_def,bytes_in_word_def] >>
           wordsLib.WORD_EVAL_TAC >> rw[] >>
           match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP >>
           fs[]) >>
      fs[w2n_add,dimword_def,w2n_lsr,arch_size_def,limits_inv_def] >>
      rfs[bytes_in_word_def,dimword_def,DIV_DIV_DIV_MULT] >>
      fs[ADD4DIV4,ADD8DIV8] >>
      fs[NOT_LESS] >>
      drule_then drule LESS_EQ_LESS_TRANS >>
      rpt(pop_assum kall_tac) >> rw[] >>
      rw[DIV_LT_X] >> intLib.COOPER_TAC
     )
  \\ rveq \\ fs []
  \\ fs [dataSemTheory.call_env_def,push_env_def,
         dataSemTheory.set_var_def,wordSemTheory.set_var_def]
  \\ qabbrev_tac `new = LEAST ptr. ptr ∉ domain s.refs`
  \\ `new ∉ domain s.refs` by metis_tac [LEAST_NOTIN_spt_DOMAIN]
  \\ fs [] \\ once_rewrite_tac [list_Seq_def]
  \\ fs [] \\ once_rewrite_tac [list_Seq_def]
  \\ fs [] \\ once_rewrite_tac [list_Seq_def]
  \\ once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ fs [word_exp_rw]
  \\ `lookup 2 r.locals = SOME (Word (n2w (4 * i)))` by
   (qabbrev_tac `s9 = s with <|locals := x; space := w2n wA DIV 4 + 1|>`
    \\ fs [state_rel_def,get_vars_SOME_IFF_data]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,get_var_def]
    \\ rpt_drule0 word_ml_inv_get_var_IMP
    \\ fs [get_var_def,wordSemTheory.get_var_def,adjust_var_def]
    \\ `lookup 0 s9.locals = SOME (Number (&i))` by
     (unabbrev_all_tac \\ fs [cut_env_def] \\ rveq
      \\ fs [lookup_inter_alt] \\ EVAL_TAC)
    \\ rpt (disch_then drule0) \\ fs []
    \\ `IS_SOME (lookup 0 s9.locals)` by fs []
    \\ res_tac \\ Cases_on `lookup 2 r.locals` \\ fs []
    \\ fs [word_ml_inv_def] \\ rw []
    \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def] \\ rfs []
    \\ rw [] \\ fs [word_addr_def,Smallnum_def]
    \\ fs [small_int_def,X_LT_DIV]
    \\ match_mp_tac minus_2_word_and_id
    \\ fs [word_index,word_mul_n2w,bitTheory.BIT0_ODD,ODD_MULT] \\ NO_TAC)
  \\ `~(2 ≥ dimindex (:α))` by (fs [good_dimindex_def] \\ NO_TAC)
  \\ `shift (:α) ≠ 0 /\ ~(shift (:α) ≥ dimindex (:α))` by
        (rw [shift_def] \\ fs [good_dimindex_def] \\ NO_TAC)
  \\ simp []
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ fs [word_exp_rw]
  \\ `(?free. FLOOKUP r.store NextFree = SOME (Word free)) /\
      (?eoh1. FLOOKUP r.store EndOfHeap = SOME (Word eoh1)) /\
      (?cur1. FLOOKUP r.store CurrHeap = SOME (Word cur1))` by
        (fs [state_rel_thm,memory_rel_def,heap_in_memory_store_def] \\ NO_TAC)
  \\ fs []
  \\ `lookup 4 r.locals = SOME (Word (w2w w << 2))` by
   (qabbrev_tac `s9 = s with <|locals := x; space := w2n wA DIV 4 + 1|>`
    \\ fs [state_rel_def,get_vars_SOME_IFF_data]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,get_var_def]
    \\ rpt_drule0 word_ml_inv_get_var_IMP
    \\ fs [get_var_def,wordSemTheory.get_var_def,adjust_var_def]
    \\ `lookup 1 s9.locals = SOME (Number (&w2n w))` by
     (unabbrev_all_tac \\ fs [cut_env_def] \\ rveq
      \\ fs [lookup_inter_alt] \\ EVAL_TAC)
    \\ rpt (disch_then drule0) \\ fs []
    \\ `IS_SOME (lookup 1 s9.locals)` by fs []
    \\ res_tac \\ Cases_on `lookup 4 r.locals` \\ fs []
    \\ fs [word_ml_inv_def] \\ rw []
    \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def] \\ rfs []
    \\ rw [] \\ fs [word_addr_def,Smallnum_def]
    \\ fs [word_mul_n2w,w2w_def,WORD_MUL_LSL]
    \\ fs [small_int_def,X_LT_DIV]
    \\ match_mp_tac minus_2_word_and_id
    \\ fs [word_index,word_mul_n2w,bitTheory.BIT0_ODD,ODD_MULT] \\ NO_TAC)
  \\ `lookup 6 r.locals = SOME (Word (n2w (4 * tag)))` by
   (qabbrev_tac `s9 = s with <|locals := x; space := w2n wA DIV 4 + 1|>`
    \\ fs [state_rel_def,get_vars_SOME_IFF_data]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,get_var_def]
    \\ rpt_drule0 word_ml_inv_get_var_IMP
    \\ fs [get_var_def,wordSemTheory.get_var_def,adjust_var_def]
    \\ `lookup 2 s9.locals = SOME (Number &tag)` by
     (unabbrev_all_tac \\ fs [cut_env_def] \\ rveq
      \\ fs [lookup_inter_alt] \\ EVAL_TAC)
    \\ rpt (disch_then drule0) \\ fs []
    \\ `IS_SOME (lookup 2 s9.locals)` by fs []
    \\ res_tac \\ Cases_on `lookup 6 r.locals` \\ fs []
    \\ fs [word_ml_inv_def] \\ rw []
    \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def] \\ rfs []
    \\ `small_int (:'a) (&tag)`
    by (
      rw[small_int_def,Abbr`tag`]
      \\ fs[good_dimindex_def,dimword_def] )
    \\ fs[word_addr_def,Smallnum_def]
    \\ match_mp_tac minus_2_word_and_id
    \\ simp[word_index,bitTheory.BIT0_ODD,ODD_MULT]
    \\ NO_TAC)
  \\ fs [wordSemTheory.set_var_def,lookup_insert]
  \\ fs [] \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,wordSemTheory.set_var_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,wordSemTheory.set_var_def,
         wordSemTheory.set_store_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,wordSemTheory.set_var_def,
         wordSemTheory.set_store_def,FLOOKUP_UPDATE]
  \\ IF_CASES_TAC
  THEN1 (fs [shift_def,shift_length_def,state_rel_def,
                 EVAL ``good_dimindex (:'a)``] \\ fs [])
  \\ pop_assum kall_tac \\ fs []
  \\ qabbrev_tac `var5 = (bytes_in_word + n2w i:'a word) ⋙ shift (:α)`
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,wordSemTheory.set_var_def,
         wordSemTheory.set_store_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,wordSemTheory.set_var_def,
         wordSemTheory.set_store_def]
  \\ fs [evaluate_MakeBytes,word_exp_rw,wordSemTheory.set_var_def,
         lookup_insert,wordSemTheory.get_var_def,w2w_shift_shift]
  \\ qpat_assum `state_rel c l1 l2 _ _ _ _` mp_tac
  \\ simp_tac std_ss [Once state_rel_thm] \\ strip_tac \\ fs []
  \\ `w2n wA DIV 4 = byte_len (:'a) i` by
   (unabbrev_all_tac \\ fs [byte_len_def,bytes_in_word_def,w2n_lsr,
      good_dimindex_def,word_add_n2w,dimword_def] \\ rfs []
    \\ fs [GSYM word_add_n2w] \\ fs [word_add_n2w,dimword_def]
    \\ fs [ADD_DIV_EQ,DIV_DIV_DIV_MULT] \\ NO_TAC)
  \\ fs [wordSemTheory.set_var_def,lookup_insert]
  \\ rpt_drule0 memory_rel_RefByte_alt
  \\ disch_then (qspecl_then [`w`,`i`,`fl`] mp_tac) \\ fs []
  \\ impl_tac THEN1
   (unabbrev_all_tac \\ fs []
    \\ fs [good_dimindex_def,dimword_def] \\ rfs [])
  \\ strip_tac \\ fs [FLOOKUP_DEF] \\ rveq \\ clean_tac
  \\ `var5 = n2w (byte_len (:α) i)` by
   (unabbrev_all_tac
    \\ rewrite_tac [GSYM w2n_11,w2n_lsr,byte_len_def]
    \\ fs [bytes_in_word_def,shift_def,good_dimindex_def]
    \\ fs [word_add_n2w,ADD_DIV_EQ]
    THEN1
     (sg `i + 4 < dimword (:'a)`
      \\ sg `i + 4 DIV 4 < dimword (:'a)` \\ fs []
      \\ rfs [dimword_def] \\ fs [DIV_LT_X])
    THEN1
     (sg `i + 8 < dimword (:'a)`
      \\ sg `i + 8 DIV 8 < dimword (:'a)` \\ fs []
      \\ rfs [dimword_def] \\ fs [DIV_LT_X]))
  \\ fs [] \\ rveq
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,wordSemTheory.set_var_def,
         wordSemTheory.set_store_def,wordSemTheory.get_var_def,lookup_insert,
         wordSemTheory.mem_store_def,store_list_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ simp[Once wordSemTheory.evaluate_def,
          wordSemTheory.get_var_def,lookup_insert,
          wordSemTheory.get_var_imm_def,
          asmTheory.word_cmp_def]
  \\ rfs [shift_lsl,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ qpat_abbrev_tac `ppp = Word (_ || _:'a word)`
  \\ `ppp = Word (make_byte_header c fl i)` by
   (unabbrev_all_tac \\ fs [make_byte_header_def,bytes_in_word_def]
    \\ Cases_on`fl`
    \\ fs [good_dimindex_def,GSYM word_add_n2w,WORD_MUL_LSL]
    \\ fs [word_mul_n2w,word_add_n2w,shift_def,RIGHT_ADD_DISTRIB]
    \\ NO_TAC)
  \\ rveq \\ pop_assum kall_tac
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,
         wordSemTheory.get_var_def,lookup_insert,
         wordSemTheory.mem_store_def,store_list_def]
  \\ once_rewrite_tac[list_Seq_def]
  \\ simp[wordSemTheory.evaluate_def,word_exp_rw]
  \\ simp[wordSemTheory.set_var_def]
  \\ once_rewrite_tac[list_Seq_def]
  \\ simp[wordSemTheory.evaluate_def,word_exp_rw,
          asmTheory.word_cmp_def,wordSemTheory.get_var_def]
  \\ `(bytes_in_word:'a word) + -1w = n2w (2 ** shift(:'a) - 1)`
  by ( fs[bytes_in_word_def,good_dimindex_def,shift_def] )
  \\ simp[WORD_AND_EXP_SUB1]
  \\ `i MOD 2 ** (shift(:'a)) < dimword(:'a)`
  by (
    match_mp_tac LESS_LESS_EQ_TRANS
    \\ qexists_tac`2 ** shift(:'a)`
    \\ simp[]
    \\ fs[good_dimindex_def,dimword_def,shift_def] )
  \\ simp[]
  \\ `2 ** shift(:'a) = dimindex(:'a) DIV 8`
    by ( fs[good_dimindex_def,dimword_def,shift_def] )
  \\ simp[]
  \\ simp[(* CONJUNCT2 (CONJUNCT2 list_Seq_def), *)
          wordSemTheory.evaluate_def,word_exp_rw,
          wordSemTheory.set_var_def,
          wordSemTheory.mem_store_def,
          wordSemTheory.get_var_def,lookup_insert]
  \\ reverse IF_CASES_TAC
  >- (
    `F` suffices_by rw[]
    \\ pop_assum mp_tac \\ simp []
    \\ imp_res_tac store_list_domain
    \\ fs[LENGTH_REPLICATE]
    \\ first_x_assum(qspec_then`byte_len(:'a) i-1`mp_tac)
    \\ simp[]
    \\ fs[WORD_MUL_LSL,word_mul_n2w]
    \\ Cases_on`byte_len(:'a) i = 0` \\ fs[]
    \\ Cases_on`byte_len(:'a) i` \\ fs[ADD1,GSYM word_add_n2w]
    \\ simp[WORD_MULT_CLAUSES,WORD_LEFT_ADD_DISTRIB]
    \\ NO_TAC)
  \\ fs[]
  \\ simp[CONJUNCT2 (CONJUNCT2 list_Seq_def),
          wordSemTheory.evaluate_def,word_exp_rw,
          wordSemTheory.set_var_def,
          wordSemTheory.mem_store_def,
          wordSemTheory.get_var_def,lookup_insert]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ pop_assum mp_tac
  \\ pop_assum mp_tac
  \\ assume_tac(GEN_ALL evaluate_WriteLastBytes)
  \\ SEP_I_TAC "evaluate"
  \\ pop_assum mp_tac
  \\ simp[wordSemTheory.get_vars_def,wordSemTheory.get_var_def,lookup_insert,APPLY_UPDATE_THM]
  \\ impl_tac
  >- (
    conj_tac >- fs[good_dimindex_def]
    \\ fs[memory_rel_def,heap_in_memory_store_def,FLOOKUP_UPDATE]
    \\ fs[FLOOKUP_DEF]
    \\ qpat_x_assum `free' + bytes_in_word + _ = _` mp_tac
    \\ simp_tac std_ss [WORD_ADD_EQ_SUB]
    \\ simp[aligned_add_sub] \\ rpt strip_tac \\ rveq
    \\ fs [byte_aligned_def]
    \\ rewrite_tac [GSYM WORD_ADD_ASSOC]
    \\ (alignmentTheory.aligned_add_sub_cor
          |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL |> match_mp_tac)
    \\ fs []
    \\ (alignmentTheory.aligned_add_sub_cor
          |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL |> match_mp_tac)
    \\ fs [GSYM byte_aligned_def]
    \\ fs [byte_aligned_bytes_in_word])
  \\ simp[] \\ disch_then kall_tac
  \\ strip_tac \\ fs[] \\ clean_tac \\ fs[]
  \\ fs [lookup_insert]
  \\ strip_tac \\ rveq \\ fs []
  \\ pop_assum mp_tac \\ simp[list_Seq_def]
  \\ strip_tac \\ clean_tac \\ fs[]
  \\ `lookup Replicate_location r.code = SOME (5,Replicate_code)` by
         (imp_res_tac lookup_RefByte_location \\ NO_TAC) \\ rfs []
  \\ qmatch_asmsub_abbrev_tac`LUPDATE lw (len-1) ls`
  \\ qmatch_assum_abbrev_tac`Abbrev(ls = REPLICATE len rw)`
  \\ `0 < len` by ( Cases_on`len` \\ fs[byte_len_def,markerTheory.Abbrev_def] )
  \\ `ls = REPLICATE (len-1) rw ++ [rw] ++ []`
  by (
    simp[Abbr`ls`,LIST_EQ_REWRITE,EL_REPLICATE,LENGTH_REPLICATE]
    \\ qx_gen_tac`z` \\ strip_tac
    \\ Cases_on`z = len-1` \\ simp[EL_APPEND1,EL_APPEND2,EL_REPLICATE,LENGTH_REPLICATE] )
  \\ `LUPDATE lw (len-1) ls = REPLICATE (len-1) rw ++ [lw] ++ []` by metis_tac[lupdate_append2,LENGTH_REPLICATE]
  \\ pop_assum SUBST_ALL_TAC
  \\ pop_assum kall_tac \\ fs[]
  \\ imp_res_tac store_list_append_imp
  \\ assume_tac (GEN_ALL Replicate_code_thm)
  \\ SEP_I_TAC "evaluate"
  \\ pop_assum mp_tac \\ fs[wordSemTheory.get_var_def,lookup_insert]
  \\ simp[UPDATE_EQ]
  \\ qmatch_goalsub_abbrev_tac`(a' =+ v)`
  \\ qhdtm_x_assum`store_list`mp_tac
  \\ drule0 (Q.GEN`a'`store_list_update_m_outside)
  \\ disch_then(qspec_then`a'`mp_tac)
  \\ impl_tac
  >- (
    simp[Abbr`a'`,LENGTH_REPLICATE]
    \\ rewrite_tac[GSYM WORD_ADD_ASSOC]
    \\ simp[WORD_EQ_ADD_LCANCEL]
    \\ CONV_TAC(PATH_CONV"brrlrr"(REWR_CONV WORD_MULT_COMM))
    \\ rewrite_tac[GSYM WORD_MULT_ASSOC]
    \\ `len < dimword (:α) DIV 16` by
          (unabbrev_all_tac \\ fs [])
    \\ qpat_x_assum `good_dimindex (:'a)` mp_tac
    \\ pop_assum mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ fs [good_dimindex_def] \\ rw [] \\ fs [bytes_in_word_def]
    \\ fs [word_add_n2w,word_mul_n2w,dimword_def])
  \\ ntac 2 strip_tac \\ rfs []
  \\ disch_then drule0
  \\ impl_tac THEN1 (
    simp[Abbr`len`,WORD_MUL_LSL,word_mul_n2w,LEFT_SUB_DISTRIB,n2w_sub]
    \\ fs [good_dimindex_def,dimword_def,state_rel_thm] \\ rfs []
    \\ unabbrev_all_tac \\ fs []
    \\ `byte_len (:α) i -1 < dimword (:'a)` by (fs [dimword_def])
    \\ imp_res_tac IMP_LESS_MustTerminate_limit \\ fs[])
  \\ strip_tac \\ fs []
  \\ qpat_x_assum`evaluate _ = (SOME _,_)` mp_tac
  \\ simp [WORD_MUL_LSL,n2w_sub,GSYM word_mul_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ strip_tac
  \\ simp [state_rel_thm]
  \\ fs []
  \\ fs [lookup_def]
  \\ qhdtm_x_assum `memory_rel` mp_tac
  \\ fs [EVAL ``join_env LN []``,code_oracle_rel_def,FLOOKUP_UPDATE]
  \\ fs[store_list_def]
  \\ fs[Abbr`a'`,Abbr`v`,LENGTH_REPLICATE]
  \\ clean_tac
  \\ fs[make_ptr_def,WORD_MUL_LSL]
  \\ strip_tac
  \\ fs[CaseEq"list",pop_env_def,CaseEq"stack",is_env_def] >> rveq >> fs[] >> rfs[]
  \\ conj_asm1_tac >- (
     drule wordPropsTheory.evaluate_stack_max_le
     \\ fs [wordSemTheory.state_fn_updates]
     \\ drule  option_le_add_indv
     \\ metis_tac [option_le_trans])
  \\ conj_tac >- (
     drule wordPropsTheory.evaluate_stack_max_le
     \\ fs [wordSemTheory.state_fn_updates]
     \\ strip_tac
     \\ imp_res_tac stack_rel_IMP_size_of_stack
     \\ drule_then match_mp_tac option_le_trans
     \\ fs[do_stack_def,CaseEq"list",pop_env_def,CaseEq"stack",stack_consumed_def,stack_rel_simp] >> rveq >> fs[]
     \\ imp_res_tac stack_rel_simp
     \\ rw[size_of_stack_eq,option_le_max_right,option_le_max,option_map2_max_add,AC option_add_comm option_add_assoc,option_le_eq_eqns,option_map2_max_add,stack_size_eq]
    )
  \\ conj_tac >- fs [limits_inv_def, FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
  \\ pop_assum kall_tac
  \\ pop_assum mp_tac
  \\ qmatch_abbrev_tac`P xx yy zz ⇒ P x' yy z'`
  \\ `xx = x'`
  by (
    simp[Abbr`xx`,Abbr`x'`,FUN_EQ_THM,APPLY_UPDATE_THM,Abbr`lw`]
    \\ simp[n2w_sub,WORD_LEFT_ADD_DISTRIB] \\ rw[]
    \\ simp[w2w_word_of_byte_w2w] )
  \\ rveq \\ qunabbrev_tac `P`
  \\ match_mp_tac memory_rel_rearrange
  \\ unabbrev_all_tac
  \\ imp_res_tac stack_rel_simp
  \\ fs[]
  \\ fs[FAPPLY_FUPDATE_THM]
  \\ rw [] \\ fs []
QED

(* TODO: copypaste from costProps *)
Theorem size_of_seen_SUBSET:
  ∀lims vs refs seen n1 seen1 refs1.
  (size_of lims vs refs seen = (n1,refs1,seen1))
  ⇒ domain seen ⊆  domain seen1
Proof
  ho_match_mp_tac size_of_ind \\ rw [size_of_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  >- (ho_match_mp_tac SUBSET_TRANS
     \\ asm_exists_tac \\ fs [])
 \\ every_case_tac \\ fs []
 \\ first_x_assum irule
 \\ rpt (pairarg_tac \\ fs [])
QED

Theorem size_of_seen_Block:
  ∀lims vs refs seen n1 refs1 seen1 ts tag l.
   size_of lims vs refs seen = (n1,refs1,seen1) ==>
   (MEM (Block ts tag l) vs /\ l <> [] ==>
    lookup ts seen1 = SOME())
Proof
  ho_match_mp_tac size_of_ind >> rpt strip_tac >>
  fs[size_of_def] >>
  rpt(pairarg_tac >> fs[] >> rveq) >>
  fs[size_of_def,DISJ_IMP_THM,FORALL_AND_THM]
  >- (dxrule_then assume_tac size_of_seen_SUBSET >>
      fs[SUBSET_DEF,domain_lookup])
  >- (res_tac >>
      dxrule_then assume_tac size_of_seen_SUBSET >>
      fs[SUBSET_DEF,domain_lookup]
     )
  >- (fs[CaseEq"bool",IS_SOME_EXISTS] >> rveq >> fs[] >>
      dxrule_then assume_tac size_of_seen_SUBSET >>
      fs[SUBSET_DEF,domain_lookup]
     )
QED

Theorem size_of_cons_seen_Block:
  ∀lims vs refs seen ts tag l.
   MEM (Block ts tag l) vs ==>
   size_of lims (Block ts tag l::vs) refs seen = size_of lims vs refs seen
Proof
  Cases_on `vs` >> rpt strip_tac
  >- fs[] >>
  Cases_on `size_of lims (h::t) refs seen` >>
  Cases_on `r` >>
  imp_res_tac size_of_seen_Block >>
  Cases_on `l` >>
  simp[size_of_def]
QED

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
  \\ `small_int (:'a) 0` by
     (fs [good_dimindex_def,dimword_def,small_int_def] \\ NO_TAC)
  \\ rpt_drule0 (IMP_memory_rel_Number
        |> REWRITE_RULE [CONJ_ASSOC]
        |> ONCE_REWRITE_RULE [CONJ_COMM])
  \\ fs [] \\ strip_tac
  \\ drule0 memory_rel_Number_EQ \\ fs []
  \\ strip_tac \\ fs [Smallnum_def]
  \\ eq_tac \\ rw [] \\ fs []
QED

Theorem state_rel_get_var_Number_IMP:
   state_rel c l1 l2 s t vs locs /\
    get_var i s.locals = SOME (Number (&n)) /\ small_int (:'a) (&n) ==>
    ?w. get_var (adjust_var i) t = SOME (Word (Smallnum (&n):'a word))
Proof
  strip_tac
  \\ rpt_drule0 state_rel_get_var_IMP
  \\ strip_tac \\ fs []
  \\ fs [state_rel_thm,get_vars_SOME_IFF_data] \\ rw []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,get_var_def]
  \\ drule0 memory_rel_drop \\ strip_tac
  \\ fs [memory_rel_def]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,get_var_def]
  \\ rpt_drule0 word_ml_inv_get_var_IMP
  \\ fs [get_var_def,wordSemTheory.get_var_def,adjust_var_def]
  \\ qpat_assum `lookup i s.locals = SOME (Number (&n))` assume_tac
  \\ rpt (disch_then drule0) \\ fs []
  \\ fs [word_ml_inv_def] \\ rw []
  \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def] \\ rfs []
  \\ rw [] \\ fs [word_addr_def,Smallnum_def]
  \\ match_mp_tac minus_2_word_and_id
  \\ fs [word_index,word_mul_n2w,bitTheory.BIT0_ODD,ODD_MULT]
QED

Theorem EXP_LEMMA1:
   4n * n * (2 ** k) = n * 2 ** (k + 2)
Proof
  fs [EXP_ADD]
QED

Theorem evaluate_Maxout_bits_code:
   n_reg <> dest /\ n < dimword (:'a) /\ rep_len < dimindex (:α) /\
    k < dimindex (:'a) /\
    lookup n_reg (t:('a,'c,'ffi) wordSem$state).locals = SOME (Word (n2w n:'a word)) ==>
    evaluate (Maxout_bits_code rep_len k dest n_reg,set_var dest (Word w) t) =
      (NONE,set_var dest (Word (w || maxout_bits n rep_len k)) t)
Proof
  fs [Maxout_bits_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_def,
      wordSemTheory.set_var_def,wordSemTheory.get_var_imm_def,
      asmTheory.word_cmp_def,lookup_insert,WORD_LO,word_exp_rw,
      maxout_bits_def] \\ rw [] \\ fs [insert_shadow]
  \\ sg `2 ** rep_len < dimword (:α)` \\ fs [] \\ fs [dimword_def]
QED

Theorem Make_ptr_bits_thm:
   tag_reg ≠ dest ∧ tag1 < dimword (:α) ∧ c.tag_bits < dimindex (:α) ∧
    len_reg ≠ dest ∧ len1 < dimword (:α) ∧ c.len_bits < dimindex (:α) ∧
    c.len_bits + 1 < dimindex (:α) /\
    FLOOKUP (t:('a,'c,'ffi) wordSem$state).store NextFree = SOME (Word f) /\
    FLOOKUP t.store CurrHeap = SOME (Word d) /\
    lookup tag_reg t.locals = SOME (Word (n2w tag1)) /\
    lookup len_reg t.locals = SOME (Word (n2w len1)) /\
    shift_length c < dimindex (:α) + shift (:α) ==>
    ?t1.
      evaluate (Make_ptr_bits_code c tag_reg len_reg dest,t) =
        (NONE,set_var dest (make_cons_ptr c (f-d) tag1 len1:'a word_loc) t)
Proof
  fs [Make_ptr_bits_code_def,list_Seq_def,wordSemTheory.evaluate_def,word_exp_rw]
  \\ fs [make_cons_ptr_thm] \\ strip_tac
  \\ pairarg_tac \\ fs []
  \\ pop_assum mp_tac
  \\ assume_tac (GEN_ALL evaluate_Maxout_bits_code)
  \\ SEP_I_TAC "evaluate"
  \\ pop_assum (qspec_then `tag1` mp_tac) \\ fs [] \\ rw []
  \\ assume_tac (GEN_ALL evaluate_Maxout_bits_code)
  \\ SEP_I_TAC "evaluate"
  \\ pop_assum (qspec_then `len1` mp_tac) \\ fs [] \\ rw []
  \\ fs [ptr_bits_def]
QED

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
  \\ rw[] \\ fs[make_ptr_def]
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
  \\ rw[] \\ fs[make_ptr_def]
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
  \\ rw[] \\ fs[make_ptr_def]
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
   ¬small_int (:α) (&w2n w) ∧
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
  \\ rw[] \\ fs[make_ptr_def]
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
   ¬small_int (:α) (&w2n w) ∧
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
  \\ rw[] \\ fs[make_ptr_def]
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
   ¬small_int (:α) i ∧ good_dimindex (:α) ∧ shift_length c < dimindex (:α) ∧
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

val assign_thm_goal =
  ``state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) [] locs /\
   (op_requires_names op ==> names_opt <> NONE) /\
   cut_state_opt names_opt s = SOME x /\
   get_vars args x.locals = SOME vals /\
   t.termdep > 1 /\
   do_app op vals x = Rval (v,s2) ==>
   ?q r.
     evaluate (FST (assign c n l dest op args names_opt),t) = (q,r) /\
     (q = SOME NotEnoughSpace ==>
      r.ffi = t.ffi /\ option_le r.stack_max s2.stack_max /\
      (c.gc_kind <> None ==> ~s2.safe_for_space)) /\
     (q <> SOME NotEnoughSpace ==>
      state_rel c l1 l2 (set_var dest v s2) r [] locs /\ q = NONE)``;

val evaluate_Assign =
  SIMP_CONV(srw_ss())[wordSemTheory.evaluate_def]``evaluate (Assign _ _, _)``

Theorem cut_names_adjust_set_insert_1:
   cut_names (adjust_set x) (insert 1 w l) =
    cut_names (adjust_set x) l
Proof
  fs [wordSemTheory.cut_names_def] \\ rw []
  \\ fs [lookup_inter_alt,lookup_insert]
  \\ rw [] \\ fs [SUBSET_DEF]
  \\ res_tac \\ fs [NOT_1_domain]
QED

Theorem cut_names_adjust_set_insert_3:
   cut_names (adjust_set x) (insert 3 w l) =
    cut_names (adjust_set x) l
Proof
  fs [wordSemTheory.cut_names_def] \\ rw []
  \\ fs [lookup_inter_alt,lookup_insert]
  \\ rw [] \\ fs [SUBSET_DEF]
  \\ res_tac \\ fs [NOT_3_domain]
QED

Theorem cut_names_adjust_set_insert_5:
   cut_names (adjust_set x) (insert 5 w l) =
    cut_names (adjust_set x) l
Proof
  fs [wordSemTheory.cut_names_def] \\ rw []
  \\ fs [lookup_inter_alt,lookup_insert]
  \\ rw [] \\ fs [SUBSET_DEF]
  \\ res_tac \\ fs [NOT_5_domain]
QED

Theorem word_bit_test_0:
   (1w && w) = 0w <=> ~word_bit 0 w
Proof
  fs [word_bit_test]
QED

Theorem MAP_Number_11_w2n_word8[local]:
    !ns ns'.
      MAP (Number ∘ $& ∘ w2n) ns = MAP (Number ∘ $& ∘ w2n) ns' <=>
      ns = ns':word8 list
Proof
  Induct \\ Cases_on `ns'` \\ fs []
QED

Theorem MAP_Word64_11[local]:
    !ns ns'.
      MAP (Word64) ns = MAP (Word64) ns' <=>
      ns = ns'
Proof
  Induct \\ Cases_on `ns'` \\ fs []
QED

Theorem v_to_list_EQ_SOME_NIL:
   v_to_list hv1 = SOME [] <=> ∃ts. hv1 = Block ts 0 []
Proof
  Cases_on `hv1` \\ fs [v_to_list_def]
  \\ Cases_on `l` \\ fs [v_to_list_def] \\ EVAL_TAC
  \\ Cases_on `t` \\ fs [v_to_list_def]
  \\ Cases_on `t'` \\ fs [v_to_list_def]
  \\ every_case_tac \\ fs []
QED

Theorem InstallCode_code_thm:
   !(t:('a,'c,'ffi) wordSem$state) c hv1 v1 q1 a1 a2 ret_val bptr s1 vars sp refs ts.
      memory_rel c t.be ts refs sp t.store t.memory t.mdomain
         ((hv1,a1)::vars) /\
      lookup InstallCode_location t.code = SOME (4,InstallCode_code c) /\
      lookup InstallData_location t.code = SOME (4,InstallData_code c) /\
      FLOOKUP t.store BitmapBuffer = SOME bptr /\
      v_to_bytes hv1 = SOME q1 /\
      LENGTH q1 ≤ t.code_buffer.space_left /\
      LENGTH q1 < t.clock /\
      get_var 0 t = SOME ret_val /\
      get_var 2 t = SOME a1 /\
      get_var 4 t = SOME a2 /\
      get_var 6 t = SOME (Word (t.code_buffer.position +
                                n2w (LENGTH t.code_buffer.buffer))) /\
      good_dimindex (:'a) ==>
      ?lsz smx.
      evaluate (InstallCode_code c,t) =
      case
        evaluate (InstallData_code c,t with <|
         locals := fromList2 [ret_val; bptr; a2;
           Word (t.code_buffer.position +
                 n2w (LENGTH t.code_buffer.buffer + LENGTH q1))];
         locals_size := lsz;
         clock := t.clock - LENGTH q1 - 1;
         code_buffer := t.code_buffer with
           <| buffer := t.code_buffer.buffer ++ q1 ;
              space_left := t.code_buffer.space_left - LENGTH q1
            |>;
        stack_max := smx |>) of
      | (NONE,s) => (SOME Error, s)
      | res => res
Proof
  Induct_on `q1` \\ fs [] THEN1
   (fs [v_to_bytes_def]
    \\ fs [some_def] \\ rw [] \\ rfs [MAP_Number_11_w2n_word8]
    \\ rveq \\ fs [v_to_list_EQ_SOME_NIL] \\ rveq
    \\ fs [InstallCode_code_def]
    \\ eval_tac \\ fs [wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,
         wordSemTheory.get_vars_def,wordSemTheory.get_var_def,lookup_insert]
    \\ rpt_drule0 memory_rel_Block_IMP \\ strip_tac \\ rveq \\ fs []
    \\ fs [wordSemTheory.bad_dest_args_def,wordSemTheory.find_code_def,
           wordSemTheory.add_ret_loc_def,wordSemTheory.dec_clock_def,
           wordSemTheory.call_env_def]
    \\ qmatch_goalsub_abbrev_tac `InstallData_code c, t1`
    \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ qexists_tac `t1.locals_size`
    \\ qexists_tac `t1.stack_max`
    \\ qmatch_goalsub_abbrev_tac `InstallData_code c, t2`
    \\ qsuff_tac `t1 = t2` THEN1 (rw [] \\ fs [])
    \\ unabbrev_all_tac \\ fs [wordSemTheory.state_component_equality,
         wordSemTheory.buffer_component_equality])
  \\ fs [v_to_bytes_def]
  \\ fs [some_def] \\ rw [] \\ rfs [MAP_Number_11_w2n_word8]
  \\ rveq \\ fs []
  \\ Cases_on `hv1` \\ fs [v_to_list_def]
  \\ Cases_on `l` \\ fs [v_to_list_def]
  \\ Cases_on `t'` \\ fs [v_to_list_def]
  \\ Cases_on `t''` \\ fs [v_to_list_def] \\ rveq \\ fs []
  \\ Cases_on `v_to_list h''` \\ fs [] \\ rveq \\ fs []
  \\ rename1 `v_to_list htl = _`
  \\ rpt_drule0 memory_rel_El_any
  \\ disch_then (qspec_then `0` mp_tac) \\ fs [] \\ strip_tac
  \\ rveq \\ fs []
  \\ rpt_drule0 (memory_rel_Number_IMP |> REWRITE_RULE [CONJ_ASSOC]
       |> ONCE_REWRITE_RULE [CONJ_COMM])
  \\ strip_tac \\ fs [Smallnum_def]
  \\ simp [InstallCode_code_def]
  \\ simp [Once wordSemTheory.evaluate_def,
           wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def]
  \\ IF_CASES_TAC THEN1
   (rpt_drule0 memory_rel_Block_IMP \\ strip_tac
    \\ fs [word_bit_test_0] \\ fs [word_bit_def])
  \\ once_rewrite_tac [list_Seq_def]
  \\ eval_tac \\ fs []
  \\ gvs [GSYM wordSemTheory.get_var_def]
  \\ rpt_drule0 (get_var_get_real_addr_lemma |> REWRITE_RULE [CONJ_ASSOC]
       |> ONCE_REWRITE_RULE [CONJ_COMM])
  \\ disch_then (qspec_then `2` mp_tac)
  \\ impl_tac THEN1 fs [memory_rel_def,heap_in_memory_store_def]
  \\ fs [] \\ disch_then kall_tac
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac \\ fs []
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac \\ fs []
  \\ simp [Once word_exp_set_var_ShiftVar_lemma,lookup_insert]
  \\ fs [wordSemTheory.get_var_def]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac \\ fs []
  \\ fs [wordSemTheory.get_var_def,lookup_insert]
  \\ fs [wordSemTheory.buffer_write_def]
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
  \\ qmatch_goalsub_abbrev_tac `_ ++ ww`
  \\ `ww = [h]` by
   (unabbrev_all_tac \\ fs [w2w_def,w2n_lsr] \\ Cases_on `h` \\ fs []
    \\ `(4 * n) < dimword (:α)` by fs [dimword_def,good_dimindex_def]
    \\ fs [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV])
  \\ qmatch_goalsub_abbrev_tac `InstallCode_code c, t88`
  \\ first_x_assum (qspec_then `t88` mp_tac)
  \\ fs [Abbr`t88`,fromList2_def,lookup_insert]
  \\ disch_then drule \\ fs [GSYM word_add_n2w,MAP_Number_11_w2n_word8]
  \\ strip_tac
  \\ fs[]
  \\ fs [ADD1,GSYM word_add_n2w]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ CASE_TAC \\ fs []
  \\ Cases_on `q` \\ fs []
  \\ qexists_tac `lsz`
  \\ qexists_tac `smx`
  \\ fs[]
QED

Definition w2w_upper_def:
  w2w_upper (w:word64) =
    if dimindex (:'a) = 32 then ((63 >< 32) w):'a word else w2w w
End

Theorem InstallData_code_thm:
   !(t:('a,'c,'ffi) wordSem$state) c hv2 v1 q2 a1 a2 ret_val s1 vars sp refs ts.
      memory_rel c t.be ts refs sp t.store t.memory t.mdomain
         ((hv2,a2)::vars) /\
      lookup InstallData_location t.code = SOME (4,InstallData_code c) /\
      lookup Install_location t.code = SOME (3,Install_code c) /\
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
          | (NONE,s) => (SOME Error, s)
      | res => res
Proof
  Induct_on `q2` \\ fs [] THEN1
   (fs [v_to_words_def]
    \\ fs [some_def] \\ rw [] \\ rfs [MAP_Word64_11]
    \\ rveq \\ fs [v_to_list_EQ_SOME_NIL] \\ rveq
    \\ fs [InstallData_code_def,list_Seq_def]
    \\ eval_tac \\ fs [wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,
         wordSemTheory.get_vars_def,wordSemTheory.get_var_def,lookup_insert]
    \\ rpt_drule0 memory_rel_Block_IMP \\ strip_tac \\ rveq \\ fs []
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

Theorem LENGTH_EQ_4:
   (LENGTH xs = 4 <=> ?a1 a2 a3 a4. xs = [a1;a2;a3;a4]) /\
    (4 = LENGTH xs <=> ?a1 a2 a3 a4. xs = [a1;a2;a3;a4])
Proof
  Cases_on `xs` \\ fs []
  \\ rpt (Cases_on `t` \\ fs [] ORELSE Cases_on `t'` \\ fs [])
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

Theorem consume_space_stack_max:
  consume_space a x = SOME s ⇒ x.stack_max = s.stack_max
Proof
  rw[consume_space_def]>>
  simp[]
QED

fun cases_on_op q = Cases_on q >|
  map (MAP_EVERY Cases_on) [[], [], [], [], [`b`], [`g`], [`m`], [], [`t`]];

Theorem do_app_aux_safe_for_space_mono:
  (do_app_aux op xs s = Rval (r,s1)) /\ s1.safe_for_space ==> s.safe_for_space
Proof
  cases_on_op `op` \\
  fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,AllCaseEqs(),
      bool_case_eq,ffiTheory.call_FFI_def,do_app_def,do_space_def,
      with_fresh_ts_def,closSemTheory.ref_case_eq,do_install_def,
      ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq,check_lim_def,
      semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,
      pair_case_eq,consume_space_def,dataLangTheory.op_space_reset_def,data_spaceTheory.op_space_req_def]
  \\ rw [] \\ fs [state_component_equality] \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ EVERY_CASE_TAC \\ fs []
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

Theorem state_rel_cut_state_opt_SOME:
  state_rel c l1 l2 s t [] locs ∧
  get_vars args x.locals = SOME vals ∧
  cut_state_opt (SOME kept_names) s = SOME x ⇒
  ∃y ws.
    cut_env (adjust_sets kept_names) t.locals = SOME y ∧
    get_vars (MAP adjust_var args) t = SOME ws ∧
    get_vars (MAP adjust_var args) (t with locals := y) = SOME ws ∧
    LENGTH args = LENGTH vals ∧ LENGTH args = LENGTH ws ∧
    state_rel c l1 l2 x t [] locs ∧
    state_rel c l1 l2 x (t with locals := y) [] locs
Proof
  rw []
  \\ drule_all state_rel_cut_IMP \\ strip_tac
  \\ drule cut_env_IMP_cut_env
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ gvs [cut_state_opt_def]
  \\ pop_assum $ qspecl_then [‘x.locals’,‘kept_names’] mp_tac
  \\ impl_keep_tac
  >-
   (gvs [cut_env_def,cut_state_def,AllCaseEqs()]
    \\ gvs [lookup_inter_alt,domain_inter])
  \\ strip_tac
  \\ gvs []
  \\ drule state_rel_cut_env_cut_env
  \\ disch_then $ drule_at $ Pos last
  \\ disch_then $ drule_at $ Pos last
  \\ strip_tac
  \\ ‘(x with locals := x.locals) = x’ by gvs [dataSemTheory.state_component_equality]
  \\ gvs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ gvs []
  \\ drule_all cut_env_get_vars_get_vars
  \\ simp_tac std_ss []
QED

Theorem assign_Install:
  (op = Install) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ ‘names_opt ≠ NONE’ by (first_x_assum irule \\ EVAL_TAC \\ simp [])
  \\ gvs [GSYM IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS]
  \\ rename [‘cut_state_opt (SOME kept_names) s’]
  \\ drule_all state_rel_cut_state_opt_SOME
  \\ strip_tac
  \\ qpat_x_assum ‘_ (t with locals := y) [] locs’ $ ASSUME_NAMED_TAC "with_locals"
  \\ `~s2.safe_for_space` by
    (drule do_app_safe_for_space_allowed_op \\ fs[allowed_op_def])
  \\ fs [assign_def] \\ rw []
  \\ gvs [do_app,REWRITE_RULE [METIS_PROVE [] ``~b\/c<=>(b==>c)``]
          do_install_def,UNCURRY,AllCaseEqs()]
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ rename1 `get_vars _ _ =
        SOME [hv1;hv2; Number (&LENGTH q1); Number (&LENGTH q2)]`
  \\ rename1 `get_vars [v1;v2;v3;v4] _ =
        SOME [_;_; Number (&LENGTH q1); Number (&LENGTH q2)]`
  \\ fs [dataLangTheory.op_requires_names_def,
         dataLangTheory.op_space_reset_def,cut_state_opt_def]
  \\ rename1 `state_rel c l1 l2 s1 t [] locs`
  \\ fs [dataSemTheory.cut_state_def]
  \\ Cases_on `dataSem$cut_env kept_names s.locals` \\ fs []
  \\ clean_tac \\ fs []
  \\ qabbrev_tac `s1 = s with locals := x`
  \\ rename [`cut_env (adjust_sets kept_names) t.locals = SOME y`]
  \\ qpat_assum `state_rel c l1 l2 s1 t [] locs` mp_tac
  \\ simp_tac std_ss [Once state_rel_thm] \\ strip_tac \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ qpat_x_assum `get_vars _ x = _` mp_tac
  \\ `x = s1.locals` by fs [Abbr`s1`]
  \\ pop_assum (fn th => rewrite_tac [th]) \\ strip_tac
  \\ rpt_drule0 memory_rel_lookup_var_IMP \\ strip_tac
  \\ fs [code_oracle_rel_def]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ rename [‘get_vars [adjust_var v1; adjust_var v2; adjust_var v3; adjust_var v4] _
              = SOME [_;_;temp_w3;temp_w4]’]
  \\ `?w3 w4. get_var (adjust_var v4) t = SOME (Word w4) ∧
              get_var (adjust_var v3) t = SOME (Word w3) ∧
              temp_w3 = Word w3 ∧ temp_w4 = Word w4` by
   (drule memory_rel_tl \\ strip_tac
    \\ drule memory_rel_tl \\ strip_tac
    \\ drule memory_rel_tl \\ strip_tac
    \\ imp_res_tac memory_rel_any_Number_IMP \\ fs [get_vars_SOME_IFF]
    \\ gvs [wordSemTheory.get_vars_def])
  \\ rveq
  \\ rpt_drule0 evaluate_BignumHalt
  \\ strip_tac \\ fs [] \\ IF_CASES_TAC >- fs [] \\ fs []
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ qpat_x_assum `_ = SOME (Word w4)` assume_tac
  \\ full_simp_tac std_ss [GSYM wordSemTheory.get_var_def]
  \\ rpt_drule0 evaluate_BignumHalt
  \\ strip_tac \\ fs [] \\ IF_CASES_TAC >- fs [] \\ fs []
  \\ ntac 2 (qpat_x_assum `_.ffi = _.ffi` kall_tac)
  \\ ntac 2 (qpat_x_assum `eveluate _ = (NONE,_)` kall_tac)
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [get_vars_SOME_IFF] \\ clean_tac
  \\ `w4 = n2w (4 * LENGTH q2) /\
      4 * LENGTH q2 < dimword (:'a) /\
      n2w (4 * LENGTH q2) >>> 2 = n2w (LENGTH q2):'a word` by
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
    \\ `(4 * LENGTH q2) < dimword (:α)`
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
    \\ qsuff_tac `state_rel c l1 l2 s1 t6 [] locs`
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
    \\ `dimindex (:α) DIV 8 = 2 ** shift (:α)` by
         fs [good_dimindex_def,shift_def]
    \\ `0 < dimword (:α) DIV 2 ** shift (:α) /\ 0 < 2 ** shift (:α) /\
        dimword (:α) = 2 ** shift (:α) * (dimword (:α) DIV 2 ** shift (:α))`
         by fs [good_dimindex_def,shift_def,dimword_def]
    \\ pop_assum (fn th => once_rewrite_tac [th])
    \\ simp [GSYM DIV_MOD_MOD_DIV,MULT_DIV]
    \\ match_mp_tac MOD_LESS_EQ \\ fs [])
  \\ `w3 = n2w (4 * LENGTH q1) /\
      4 * LENGTH q1 < dimword (:'a) /\
      n2w (4 * LENGTH q1) >>> 2 = n2w (LENGTH q1):'a word` by
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
    \\ `(4 * LENGTH q1) < dimword (:α)`
         by (fs [good_dimindex_def,dimword_def] \\ rfs [])
    \\ fs [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV])
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.get_var_def]
  \\ simp [Once word_exp_set_var_ShiftVar_lemma,lookup_insert]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ simp [Once word_exp_set_var_ShiftVar_lemma,lookup_insert]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ simp [Once word_exp_set_var_ShiftVar_lemma,lookup_insert]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.get_var_def,lookup_insert,wordSemTheory.get_var_imm_def]
  \\ IF_CASES_TAC THEN1
   (qmatch_goalsub_abbrev_tac `GiveUp, t6`
    \\ qsuff_tac `state_rel c l1 l2 s1 t6 [] locs`
    THEN1 (rw [] \\ imp_res_tac evaluate_GiveUp \\ fs [])
    \\ fs [Abbr `t6`]
    \\ full_simp_tac(srw_ss())[state_rel_def] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[lookup_insert,adjust_var_NEQ_1]
    \\ full_simp_tac(srw_ss())[inter_insert,domain_lookup,
         lookup_1_adjust_set,lookup_3_adjust_set,lookup_5_adjust_set]
    \\ metis_tac [])
  \\ `LENGTH q1 <= t.code_buffer.space_left` by
   (pop_assum mp_tac
    \\ fs [asmTheory.word_cmp_def,WORD_LO,NOT_LESS]
    \\ match_mp_tac (DECIDE ``m <= k ==> (n <= m ==> n <= k:num)``)
    \\ match_mp_tac MOD_LESS_EQ \\ fs [])
  \\ pop_assum mp_tac \\ pop_assum kall_tac \\ strip_tac
  \\ clean_tac \\ fs []
  \\ fs [list_Seq_def]
  \\ `lookup InstallCode_location t.code = SOME (4,InstallCode_code c) /\
      lookup InstallData_location t.code = SOME (4,InstallData_code c) /\
      lookup Install_location t.code = SOME (3,Install_code c)` by
       (fs [state_rel_def,code_rel_def,stubs_def] \\ NO_TAC) \\ fs []
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
  \\ qmatch_goalsub_abbrev_tac `InstallCode_code c, t88`
  \\ qspec_then `t88` mp_tac InstallCode_code_thm
  \\ qunabbrev_tac `t88` \\ fs [wordSemTheory.get_var_def,
       lookup_insert,fromList2_def]
  \\ disch_then drule \\ fs []
  \\ strip_tac \\ fs[] \\ pop_assum kall_tac
  \\ drule memory_rel_swap \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac `InstallData_code c, t88`
  \\ qspec_then `t88` mp_tac InstallData_code_thm
  \\ qunabbrev_tac `t88` \\ fs [wordSemTheory.get_var_def,
       lookup_insert,fromList2_def]
  \\ disch_then drule \\ fs []
  \\ impl_tac THEN1
   (`2 * dimword (:'a) <= MustTerminate_limit (:α)` by
        fs [wordSemTheory.MustTerminate_limit_def]
    \\ rfs [good_dimindex_def,dimword_def] \\ rfs [])
  \\ strip_tac \\ fs[] \\ pop_assum kall_tac
  \\ simp [Install_code_def,Once list_Seq_def,wordSemTheory.evaluate_def]
  \\ eval_tac
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac \\ fs [lookup_insert]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac \\ fs [lookup_insert]
  \\ fs [wordSemTheory.set_store_def]
  (* Install *)
  \\ rewrite_tac [list_Seq_def] \\ eval_tac
  \\ `s1.compile = s.compile` by fs [Abbr `s1`]
  \\ `s1.compile_oracle = s.compile_oracle` by fs [Abbr `s1`]
  \\ Cases_on `s.compile_oracle 0`
  \\ fs [lookup_insert,wordSemTheory.get_var_def,wordSemTheory.cut_env_def,
         wordSemTheory.buffer_flush_def,bytes_in_word_def]
  \\ simp [wordSemTheory.cut_envs_def,wordSemTheory.cut_names_def]
  \\ qmatch_goalsub_rename_tac `compile_part c (ar1,ar2)`
  \\ qmatch_goalsub_rename_tac `compile_part c (ar1,ar2)`
  \\ Cases_on `compile_part c (ar1,ar2)` \\ fs [w2w_upper_upper_w2w]
  \\ rveq \\ fs []
  \\ reverse IF_CASES_TAC
  THEN1 (sg `F` \\ fs [] \\ fs [shift_seq_def]
         \\ pop_assum mp_tac
         \\ DEP_REWRITE_TAC [w2w_upper_upper_w2w]
         \\ gvs [state_rel_def])
  \\ fs [inter_insert,wordSemTheory.get_vars_def,
         wordSemTheory.get_var_def,lookup_insert]
  \\ fs [list_Seq_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_def,
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
  \\ qpat_x_assum ‘state_rel c l1 l2 _ _ [] locs’ $ ASSUME_NAMED_TAC "state_rel_t"
  \\ LABEL_X_ASSUM "with_locals" mp_tac
  \\ simp [state_rel_thm]
  \\ strip_tac \\ gvs [FLOOKUP_SIMP,lookup_insert,adjust_var_11]
  \\ gvs [Abbr‘s1’]
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
    \\ qpat_x_assum `domain t.code = _` assume_tac
    \\ fs [EXTENSION,domain_lookup]
    \\ pop_assum (qspec_then `n` mp_tac)
    \\ Cases_on `lookup n s.code` \\ fs []
    THEN1
     (Cases_on `lookup n t.code` \\ fs []
      THEN1
       (strip_tac \\ qpat_x_assum `ALOOKUP _ _ = _` mp_tac
        \\ qspec_tac (`full_list`,`xs`)
        \\ Induct \\ fs [FORALL_PROD,ALOOKUP_def,compile_part_def] \\ rw [])
      \\ qpat_x_assum `∀n. EVERY _ _` (qspec_then `0` mp_tac)
      \\ fs [EVERY_MEM]
      \\ imp_res_tac ALOOKUP_MEM
      \\ disch_then drule \\ fs []
      \\ rpt (pop_assum kall_tac)
      \\ rewrite_tac [stubs_def,generated_bignum_stubs_eq,MAP,FST,APPEND]
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

Theorem LENGTH_EQ_5:
   (LENGTH xs = 5 <=> ?a1 a2 a3 a4 a5. xs = [a1;a2;a3;a4;a5]) /\
    (5 = LENGTH xs <=> ?a1 a2 a3 a4 a5. xs = [a1;a2;a3;a4;a5])
Proof
  Cases_on `xs` \\ fs []
  \\ rpt (Cases_on `t` \\ fs [] ORELSE Cases_on `t'` \\ fs [])
QED

Theorem memory_rel_get_num:
   memory_rel c be ts refs sp st m dm vars /\
    n < dimword (:'a) DIV 8 /\ good_dimindex (:'a) /\
    MEM (Number (&n),a:'a word_loc) vars ==>
    ?w. a = Word w /\ w >>> 2 = n2w n
Proof
  rw []
  \\ `memory_rel c be ts refs sp st m dm [Number (&n),a]` by
   (first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
    \\ fs [])
  \\ `small_int (:α) (&n)` by
       (fs [good_dimindex_def,dimword_def,small_int_def] \\ fs [])
  \\ imp_res_tac memory_rel_Number_IMP
  \\ fs [Smallnum_def] \\ rewrite_tac [GSYM w2n_11,w2n_lsr]
  \\ fs [good_dimindex_def,dimword_def]
  \\ `4 * n < dimword (:'a)` by fs [dimword_def]
  \\ fs [dimword_def]
  \\ match_mp_tac (MULT_DIV |> ONCE_REWRITE_RULE [MULT_COMM]) \\ fs []
QED

Theorem IN_domain_adjust_set_inter:
   x ∈ domain (adjust_set (inter s1 s2)) <=>
    x ∈ domain (adjust_set s1) /\
    x ∈ domain (adjust_set s2)
Proof
  fs [domain_lookup,lookup_adjust_set]
  \\ rw [] \\ fs [lookup_inter] \\ rfs []
  \\ every_case_tac \\ fs []
QED

Theorem get_var_to_word_exp:
   get_var r s = SOME (Word w) ⇒
  word_exp s (Op Add [Var r;Const 0w] ) = SOME (Word (w+0w)) ∧
  word_exp s (Op Add [Var r;Const 1w] ) = SOME (Word (w+1w)) ∧
  word_exp s (Op Add [Var r;Const 2w] ) = SOME (Word (w+2w)) ∧
  word_exp s (Op Add [Var r;Const 3w] ) = SOME (Word (w+3w))
Proof
  EVAL_TAC>>rw[]
QED

Theorem word_exp_set[local]:
  (word_exp s (Op Add [Var n; Const c]) =
  case get_var n s of
    SOME (Word w) => SOME (Word (w+c))
  | _ => NONE) ∧
  (word_exp s (Op Sub [Var n; Const c]) =
  case get_var n s of
    SOME (Word w) => SOME (Word (w-c))
  | _ => NONE)
Proof
  EVAL_TAC>>rw[]>>
  every_case_tac>>rw[]>>
  fs[]
QED

Theorem good_dimindex_w2w_byte[local]:
  good_dimindex (:'a) ⇒
  w2w (w2w (w:word8):'a word) = w
Proof
  rw[good_dimindex_def]>>
  simp[w2w_w2w]>>
  match_mp_tac WORD_ALL_BITS>>fs[]
QED

Theorem set_var_consts[local]:
  (set_var r v s).memory = s.memory ∧
  (set_var r v s).mdomain = s.mdomain ∧
  (set_var r v s).be = s.be ∧
  (set_var r v s).code = s.code
Proof
  fs[wordSemTheory.set_var_def]
QED

Theorem get_var_consts[local]:
  get_var r (s with memory:=m) = get_var r s
Proof
  EVAL_TAC>>rw[]
QED

Theorem CopyByteAdd_thm:
   !be n a1 a2 m dm ret_val l1 l2 (s:('a,'c,'ffi) wordSem$state) m1.
      word_copy_fwd be n a1 a2 m dm = SOME m1 /\
      s.memory = m /\ s.mdomain = dm /\
      s.be = be ∧
      good_dimindex(:'a) ∧
      lookup ByteCopyAdd_location s.code = SOME (5,ByteCopyAdd_code) /\
      w2n n DIV 4 <= s.clock /\
      get_var 0 s = SOME (Loc l1 l2) /\
      get_var 2 s = SOME (Word n) /\
      get_var 4 s = SOME (Word (a1:'a word)) /\
      get_var 6 s = SOME (Word a2) /\
      get_var 8 s = SOME ret_val ==>
      evaluate (ByteCopyAdd_code,s) =
        (SOME (Result (Loc l1 l2) [ret_val]),
         s with <| clock := s.clock - w2n n DIV 4 ;
                   memory := m1 ; locals := LN; locals_size := SOME 0;
                   stack_max :=
                   if n <₊ 4w then
                     s.stack_max
                   else
                     OPTION_MAP2 MAX s.stack_max
                       (OPTION_MAP2 $+ (stack_size s.stack)
                       (lookup ByteCopyAdd_location s.stack_size))|>)
Proof
  ho_match_mp_tac word_copy_fwd_ind >>
  rw[]>>
  qpat_x_assum`A=SOME m1` mp_tac>>
  simp[Once word_copy_fwd_def]>>
  rpt (IF_CASES_TAC)>>rw[]
  >-
    (fs[ByteCopyAdd_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,
        wordSemTheory.get_var_def,asmTheory.word_cmp_def,wordSemTheory.get_vars_def]>>
     EVAL_TAC>>fs[wordSemTheory.state_component_equality])
  >-
    (imp_res_tac get_var_to_word_exp>>
    fs[ByteCopyAdd_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,list_Seq_def,wordSemTheory.inst_def,wordSemTheory.get_vars_def]>>
    simp[word_exp_set,get_var_set_var_thm,set_var_consts]>>
    simp[good_dimindex_w2w_byte]>>
    simp[get_var_set_var_thm,get_var_consts]>>
    EVAL_TAC>>fs[wordSemTheory.state_component_equality]>>
    fs[WORD_LO]>>
    `w2n n DIV 4 = 0` by
      (match_mp_tac LESS_DIV_EQ_ZERO>>fs[])>>
    fs[])
  >-
    (FULL_CASE_TAC>>fs[]
    >-
      (imp_res_tac get_var_to_word_exp>>
      fs[ByteCopyAdd_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,list_Seq_def,wordSemTheory.inst_def,wordSemTheory.get_vars_def]>>
      simp[word_exp_set,get_var_set_var_thm,set_var_consts]>>
      simp[good_dimindex_w2w_byte]>>
      simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
      simp[good_dimindex_w2w_byte]>>
      simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
      EVAL_TAC>>fs[wordSemTheory.state_component_equality]>>
      fs[WORD_LO]>>
      `w2n n DIV 4 = 0` by
        (match_mp_tac LESS_DIV_EQ_ZERO>>fs[])>>
      fs[])
    >>
      (imp_res_tac get_var_to_word_exp>>
      fs[ByteCopyAdd_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,list_Seq_def,wordSemTheory.inst_def,wordSemTheory.get_vars_def]>>
      simp[word_exp_set,get_var_set_var_thm,set_var_consts]>>
      simp[good_dimindex_w2w_byte]>>
      simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
      simp[good_dimindex_w2w_byte]>>
      simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
      simp[good_dimindex_w2w_byte]>>
      simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
      EVAL_TAC>>fs[wordSemTheory.state_component_equality]>>
      fs[WORD_LO]>>
      `w2n n DIV 4 = 0` by
        (match_mp_tac LESS_DIV_EQ_ZERO>>fs[])>>
      fs[]))
  >>
    (imp_res_tac get_var_to_word_exp>>
    simp[ByteCopyAdd_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,list_Seq_def,wordSemTheory.inst_def,wordSemTheory.get_vars_def]>>
    simp[word_exp_set,get_var_set_var_thm,set_var_consts]>>
    simp[good_dimindex_w2w_byte]>>
    simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
    simp[good_dimindex_w2w_byte]>>
    simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
    simp[good_dimindex_w2w_byte]>>
    simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
    simp[good_dimindex_w2w_byte]>>
    simp[get_var_set_var_thm,get_var_consts,set_var_consts,wordSemTheory.get_vars_def]>>
    simp[wordSemTheory.bad_dest_args_def,wordSemTheory.find_code_def,wordSemTheory.add_ret_loc_def]>>
    `w2n n DIV 4 = (w2n (n+ -4w) DIV 4) +1` by
      (fs[WORD_NOT_LOWER]>>
      FULL_SIMP_TAC (std_ss) [WORD_SUB_INTRO,word_sub_w2n]>>
      simp[DIV_SUB]>>
      fs[WORD_LS]>>
      `0 < 4 ∧ 4 * 1 ≤ w2n n` by fs[]>>
      imp_res_tac DIV_SUB>>
      fs[]>>
      `0 < w2n n DIV 4` by
        (match_mp_tac bitTheory.DIV_GT0>>
        fs[])>>
      fs[])>>
    simp[]>>
    qmatch_goalsub_abbrev_tac`evaluate (_,s')`>>
    first_x_assum drule0 >>
    simp[]>>
    disch_then (qspecl_then [`ret_val`,`l1`,`l2`,`s'`] mp_tac)>>
    impl_tac>-
      (unabbrev_all_tac>>simp[wordSemTheory.call_env_def,wordSemTheory.dec_clock_def]>>
      simp[wordSemTheory.get_var_def,lookup_fromList2,lookup_fromList,set_var_consts])>>
    rw[]>>
    unabbrev_all_tac>>simp[wordSemTheory.call_env_def,wordSemTheory.dec_clock_def]>>
    simp[wordSemTheory.state_component_equality,wordSemTheory.set_var_def])
QED

Theorem CopyByteSub_thm:
   !be n a1 a2 m dm ret_val l1 l2 (s:('a,'c,'ffi) wordSem$state) m1.
      word_copy_bwd be n a1 a2 m dm = SOME m1 /\
      s.memory = m /\ s.mdomain = dm /\
      s.be = be ∧
      good_dimindex(:'a) ∧
      lookup ByteCopySub_location s.code = SOME (5,ByteCopySub_code) /\
      w2n n DIV 4 <= s.clock /\
      get_var 0 s = SOME (Loc l1 l2) /\
      get_var 2 s = SOME (Word n) /\
      get_var 4 s = SOME (Word (a1:'a word)) /\
      get_var 6 s = SOME (Word a2) /\
      get_var 8 s = SOME ret_val ==>
      evaluate (ByteCopySub_code,s) =
        (SOME (Result (Loc l1 l2) [ret_val]),
         s with <| clock := s.clock - w2n n DIV 4 ;
                   memory := m1 ; locals := LN; locals_size := SOME 0;
                   stack_max :=
                   if n <₊ 4w then
                     s.stack_max
                   else
                     OPTION_MAP2 MAX s.stack_max
                       (OPTION_MAP2 $+ (stack_size s.stack)
                       (lookup ByteCopySub_location s.stack_size))|>)
Proof
  ho_match_mp_tac word_copy_bwd_ind >>
  rw[]>>
  qpat_x_assum`A=SOME m1` mp_tac>>
  simp[Once word_copy_bwd_def]>>
  rpt (IF_CASES_TAC)>>rw[]
  >-
    (fs[ByteCopySub_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,
        wordSemTheory.get_vars_def]>>
    EVAL_TAC>>fs[wordSemTheory.state_component_equality])
  >-
    (imp_res_tac get_var_to_word_exp>>
    fs[ByteCopySub_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,list_Seq_def,wordSemTheory.inst_def,wordSemTheory.get_vars_def]>>
    simp[word_exp_set,get_var_set_var_thm,set_var_consts]>>
    simp[good_dimindex_w2w_byte]>>
    simp[get_var_set_var_thm,get_var_consts]>>
    EVAL_TAC>>fs[wordSemTheory.state_component_equality]>>
    fs[WORD_LO]>>
    `w2n n DIV 4 = 0` by
      (match_mp_tac LESS_DIV_EQ_ZERO>>fs[])>>
    fs[])
  >-
    (FULL_CASE_TAC>>fs[]
    >-
      (imp_res_tac get_var_to_word_exp>>
      fs[ByteCopySub_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,list_Seq_def,wordSemTheory.inst_def,wordSemTheory.get_vars_def]>>
      simp[word_exp_set,get_var_set_var_thm,set_var_consts]>>
      simp[good_dimindex_w2w_byte]>>
      simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
      simp[good_dimindex_w2w_byte]>>
      simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
      EVAL_TAC>>fs[wordSemTheory.state_component_equality]>>
      fs[WORD_LO]>>
      `w2n n DIV 4 = 0` by
        (match_mp_tac LESS_DIV_EQ_ZERO>>fs[])>>
      fs[])
    >>
      (imp_res_tac get_var_to_word_exp>>
      fs[ByteCopySub_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,list_Seq_def,wordSemTheory.inst_def,wordSemTheory.get_vars_def]>>
      simp[word_exp_set,get_var_set_var_thm,set_var_consts]>>
      simp[good_dimindex_w2w_byte]>>
      simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
      simp[good_dimindex_w2w_byte]>>
      simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
      simp[good_dimindex_w2w_byte]>>
      simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
      EVAL_TAC>>fs[wordSemTheory.state_component_equality]>>
      fs[WORD_LO]>>
      `w2n n DIV 4 = 0` by
        (match_mp_tac LESS_DIV_EQ_ZERO>>fs[])>>
      fs[]))
  >>
    (imp_res_tac get_var_to_word_exp>>
    simp[ByteCopySub_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,list_Seq_def,wordSemTheory.inst_def]>>
    simp[word_exp_set,get_var_set_var_thm,set_var_consts]>>
    simp[good_dimindex_w2w_byte]>>
    simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
    simp[good_dimindex_w2w_byte]>>
    simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
    simp[good_dimindex_w2w_byte]>>
    simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
    simp[good_dimindex_w2w_byte]>>
    simp[get_var_set_var_thm,get_var_consts,set_var_consts,wordSemTheory.get_vars_def]>>
    simp[wordSemTheory.bad_dest_args_def,wordSemTheory.find_code_def,wordSemTheory.add_ret_loc_def]>>
    `w2n n DIV 4 = (w2n (n+ -4w) DIV 4) +1` by
      (fs[WORD_NOT_LOWER]>>
      FULL_SIMP_TAC (std_ss) [WORD_SUB_INTRO,word_sub_w2n]>>
      simp[DIV_SUB]>>
      fs[WORD_LS]>>
      `0 < 4 ∧ 4 * 1 ≤ w2n n` by fs[]>>
      imp_res_tac DIV_SUB>>
      fs[]>>
      `0 < w2n n DIV 4` by
        (match_mp_tac bitTheory.DIV_GT0>>
        fs[])>>
      fs[])>>
    simp[]>>
    qmatch_goalsub_abbrev_tac`evaluate (_,s')`>>
    first_x_assum drule0 >>
    simp[]>>
    disch_then (qspecl_then [`ret_val`,`l1`,`l2`,`s'`] mp_tac)>>
    impl_tac>-
      (unabbrev_all_tac>>simp[wordSemTheory.call_env_def,wordSemTheory.dec_clock_def]>>
      simp[wordSemTheory.get_var_def,lookup_fromList2,lookup_fromList,set_var_consts])>>
    rw[]>>
    unabbrev_all_tac>>simp[wordSemTheory.call_env_def,wordSemTheory.dec_clock_def]>>
    simp[wordSemTheory.state_component_equality,wordSemTheory.set_var_def])
QED

Theorem push_env_store:
   (push_env x y s).store = s.store /\
    (push_env x y s).memory = s.memory /\
    (push_env x y s).mdomain = s.mdomain /\
    (push_env x y s).code = s.code /\
    (push_env x y s).be = s.be
Proof
  Cases_on `y`
  \\ fs [wordSemTheory.push_env_def]
  \\ TRY pairarg_tac \\ fs []
  \\ PairCases_on `x'` \\ fs [wordSemTheory.push_env_def]
  \\ TRY pairarg_tac \\ fs []
QED

Theorem not_less_zero_int_eq[local]:
    ~(i < 0:int) <=> ?n. i = &n
Proof
  Cases_on `i` \\ fs []
QED

Theorem assign_WordFromWord:
   (?b. op = WordOp (WordFromWord b)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac state_rel_cut_IMP \\ pop_assum mp_tac
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
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
    \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [eq_eval]
    \\ fs [adjust_var_11]
    \\ TRY (conj_tac THEN1 rw [])
    \\ simp[inter_insert_ODD_adjust_set]
    \\ simp[option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert
    \\ fs []
    \\ qmatch_goalsub_abbrev_tac`Number i,Word sn`
    \\ (qsuff_tac `sn = Smallnum i /\ small_int (:'a) i`
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
  \\ TOP_CASE_TAC \\ fs [] \\ fs [good_dimindex_def,list_Seq_def] \\ rfs []
  \\ fs [eq_eval,word_sh_def,Smallnum_def]
  \\ TRY(qpat_abbrev_tac `ww = _ >>> 2`
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
    \\ qexists_tac`x.space - 2` \\ fs[]
   )
QED

Theorem IS_SOME_lookup:
  IS_SOME (lookup n l) ⇔ n ∈ domain l
Proof
  gvs [IS_SOME_EXISTS,domain_lookup]
QED

Theorem IN_adjust_var_lemma:
  cut_env kept_names s_locals = SOME x ∧
  cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) ∧
  n ∈ domain x ⇒
  adjust_var n ∈ domain y2
Proof
  rw []
  \\ gvs [wordSemTheory.cut_envs_def,AllCaseEqs(),adjust_sets_def,
          wordSemTheory.cut_names_def,lookup_inter_alt,
          dataSemTheory.cut_env_def]
  \\ gvs [domain_union,domain_inter,adjust_var_IN_adjust_set]
  \\ gvs [SUBSET_DEF]
  \\ first_x_assum irule
  \\ simp [adjust_var_IN_adjust_set]
QED

Theorem cut_env_envs_lookup_lookup:
  cut_env kept_names s_locals = SOME x ∧
  cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) ∧
  k ∈ domain (adjust_set x) ⇒
  ∃v. lookup k t_locals = SOME v ∧
      lookup k y2 = SOME v
Proof
  rw []
  \\ gvs [wordSemTheory.cut_envs_def,AllCaseEqs(),adjust_sets_def,
          wordSemTheory.cut_names_def,lookup_inter_alt,
          dataSemTheory.cut_env_def]
  \\ simp [SF CONJ_ss]
  \\ gvs [IN_domain_adjust_set_inter]
  \\ gvs [SUBSET_DEF]
  \\ simp [GSYM domain_lookup]
QED

Theorem env_to_list_domain:
  env_to_list y2 p = (l,permute) ⇒
  domain (fromAList l) = domain y2
Proof
  rw [] \\ drule wordPropsTheory.env_to_list_lookup_equiv
  \\ gvs [EXTENSION]
  \\ simp [domain_lookup,lookup_fromAList]
QED

Theorem cut_envs_lookup_0:
  cut_envs (adjust_sets names) t_locals = SOME (y1,y2) ∧
  env_to_list y2 p = (q,r') ∧
  lookup 0 t_locals = SOME (Loc l1 l2) ⇒
  ALOOKUP q 0 = NONE ∧
  lookup 0 y1 = SOME (Loc l1 l2)
Proof
  strip_tac
  \\ gvs [wordSemTheory.cut_envs_def,AllCaseEqs(),adjust_sets_def,
          wordSemTheory.cut_names_def,lookup_inter_alt]
  \\ drule wordPropsTheory.env_to_list_lookup_equiv
  \\ simp [] \\ simp [lookup_inter_alt,NOT_0_domain]
QED

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

Theorem inter_union_distrib:
  ∀x y z. inter (union x y) z = union (inter x z) (inter y z)
Proof
  rw [] \\ DEP_REWRITE_TAC [spt_eq_thm] \\ gvs []
  \\ irule_at Any wf_union \\ gvs []
  \\ gvs [lookup_inter_alt,lookup_union]
  \\ rw [] \\ gvs []
QED

Theorem cut_envs_inter:
  cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) ∧
  cut_env kept_names s_locals = SOME x ⇒
  inter (fromAList (toAList y1)) (adjust_set x) = LN
Proof
  rw []
  \\ DEP_REWRITE_TAC [spt_eq_thm]
  \\ simp [wf_fromAList,lookup_fromAList,ALOOKUP_toAList,lookup_def,lookup_inter_alt]
  \\ rw [] \\ gvs [wordSemTheory.cut_envs_def,AllCaseEqs(),wordSemTheory.cut_names_def]
  \\ gvs [adjust_sets_def,lookup_inter_alt]
  \\ rw [] \\ gvs [NOT_0_domain]
QED

Theorem assign_CopyByte:
  (∃new_flag. op = MemOp (CopyByte new_flag) /\ ¬ new_flag) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [assign_def] \\ rw []
  \\ fs [do_app,allowed_op_def]
  \\ `?src srcoff le dst dstoff src_b dst_b. vals =
             [RefPtr src_b src; Number srcoff; Number le; RefPtr dst_b dst;
              Number dstoff]` by gvs [AllCaseEqs()]
  \\ fs [] \\ every_case_tac \\ fs [] \\ rveq
  \\ rename1 `lookup dst x.refs = SOME (ByteArray ys_fl ys)`
  \\ rename1 `lookup src x.refs = SOME (ByteArray xs_fl xs)`
  \\ fs [dataLangTheory.op_requires_names_def,
         dataLangTheory.op_space_reset_def,cut_state_opt_def]
  \\ Cases_on `names_opt` \\ fs []
  \\ fs [wordSemTheory.evaluate_def,wordSemTheory.add_ret_loc_def,
         wordSemTheory.bad_dest_args_def,wordSemTheory.find_code_def,
         get_names_def]
  \\ rpt_drule0 state_rel_get_vars_IMP \\ strip_tac \\ fs []
  \\ `lookup ByteCopy_location t.code = SOME (6,ByteCopy_code c)` by
       (fs [state_rel_def,code_rel_def,stubs_def] \\ NO_TAC) \\ fs []
  \\ fs [cut_state_opt_def,cut_state_def]
  \\ pop_assum kall_tac
  \\ rename1 `state_rel c l1 l2 s1 t [] locs`
  \\ Cases_on `dataSem$cut_env x'' s.locals` \\ fs []
  \\ clean_tac \\ fs [domain_adjust_sets]
  \\ qabbrev_tac `s1 = s with locals := x`
  \\ `?y. cut_env (adjust_sets x'') t.locals = SOME y` by
       (match_mp_tac (GEN_ALL cut_env_IMP_cut_env) \\ fs []
        \\ metis_tac []) \\ fs []
  \\ drule cut_env_IMP_cut_envs \\ strip_tac
  \\ fs [LENGTH_EQ_5] \\ rveq
  \\ qpat_assum `state_rel c l1 l2 s1 t [] locs` mp_tac
  \\ simp_tac std_ss [Once state_rel_thm] \\ strip_tac \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ qpat_x_assum `get_vars _ x = _` mp_tac
  \\ `x = s1.locals` by fs [Abbr`s1`]
  \\ pop_assum (fn th => rewrite_tac [th]) \\ strip_tac
  \\ rpt_drule0 memory_rel_lookup_var_IMP \\ strip_tac
  \\ fs []
  \\ `s.refs = s1.refs`     by rw [Abbr `s1`]
  \\ `s.space = s1.space`   by rw [Abbr `s1`]
  \\ `s.global = s1.global` by rw [Abbr `s1`]
  \\ `s.stack  = s1.stack`  by rw [Abbr `s1`]
  \\ `?xp yp len_n.
        srcoff = &xp /\ xp < dimword (:'a) DIV 8 /\
        dstoff = &yp /\ yp < dimword (:'a) DIV 8 /\
        le = &len_n /\ len_n < dimword (:'a) DIV 8` by
   (fs [semanticPrimitivesTheory.copy_array_def,not_less_zero_int_eq]
    \\ rveq \\ fs [NOT_LESS,integerTheory.INT_ADD,integerTheory.INT_ABS_NUM]
    \\ rpt_drule0 memory_rel_ByteArray_IMP
    \\ ntac 3 (drule0 memory_rel_tl \\ pop_assum kall_tac \\ strip_tac)
    \\ rpt_drule0 memory_rel_ByteArray_IMP
    \\ fs [good_dimindex_def,dimword_def]
    \\ rpt strip_tac \\ fs [])
  \\ rveq \\ fs []
  \\ `∃w. a3 = Word w ∧ w ⋙ 2 = n2w len_n` by
        (rpt_drule0 memory_rel_get_num \\ metis_tac [])
  \\ rveq \\ fs [] \\ ntac 2 (pop_assum mp_tac)
  \\ `∃w. a5 = Word w ∧ w ⋙ 2 = n2w yp` by
        (rpt_drule0 memory_rel_get_num \\ metis_tac [])
  \\ rveq \\ fs [] \\ ntac 2 (pop_assum mp_tac)
  \\ `∃w. a2 = Word w ∧ w ⋙ 2 = n2w xp` by
        (rpt_drule0 memory_rel_get_num \\ metis_tac [])
  \\ rveq \\ fs [] \\ rpt strip_tac
  \\ fs [ByteCopy_code_def,wordSemTheory.call_env_def,fromList2_def]
  \\ qpat_x_assum `wordSem$get_vars _ _ = _` kall_tac
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ fs [Unit_def] \\ eval_tac
  \\ `?wa1 addr1. a1 = Word wa1 /\ get_real_addr c t.store wa1 = SOME addr1`
          by (rpt_drule0 memory_rel_ByteArray_IMP \\ strip_tac \\ fs [])
  \\ `?wa2 addr2. a4 = Word wa2 /\ get_real_addr c t.store wa2 = SOME addr2`
          by (ntac 3 (drule0 memory_rel_tl \\ strip_tac)
              \\ rpt_drule0 memory_rel_ByteArray_IMP \\ strip_tac \\ fs [])
  \\ rveq \\ fs []
  \\ qmatch_goalsub_abbrev_tac `wordSem$evaluate (_,t7)`
  \\ `get_var 2 t7 = SOME (Word wa1)` by
      (unabbrev_all_tac \\ fs [wordSemTheory.get_var_def,lookup_insert])
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ `t7.store = t.store` by (unabbrev_all_tac \\ fs [push_env_store])
  \\ full_simp_tac std_ss [GSYM wordSemTheory.get_var_def]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ disch_then kall_tac
  \\ qunabbrev_tac `t7` \\ fs [eq_eval]
  \\ qmatch_goalsub_abbrev_tac `wordSem$evaluate (_,t7)`
  \\ `get_var 8 t7 = SOME (Word wa2)` by
      (unabbrev_all_tac \\ fs [wordSemTheory.get_var_def,lookup_insert])
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ `t7.store = t.store` by (unabbrev_all_tac \\ fs [push_env_store])
  \\ full_simp_tac std_ss [GSYM wordSemTheory.get_var_def]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ disch_then kall_tac
  \\ qunabbrev_tac `t7` \\ fs [eq_eval]
  \\ pop_assum kall_tac \\ clean_tac
  \\ once_rewrite_tac [list_Seq_def]
  \\ Cases_on `src = dst` (* alias case *) \\ rveq
  THEN1
   (`wa2 = wa1` by
     (drule0 memory_rel_swap \\ strip_tac
      \\ drule0 memory_rel_tl \\ strip_tac
      \\ drule0 memory_rel_swap \\ strip_tac
      \\ drule0 memory_rel_tl \\ strip_tac
      \\ drule memory_rel_RefPtr_EQ_IMP
      \\ gvs [])
    \\ fs [] \\ rveq
    \\ `memory_rel c t.be (THE s1.tstamps) s1.refs s1.space t.store t.memory t.mdomain
         ((RefPtr dst_b dst,Word wa1)::
            (join_env s1.locals
               (toAList (inter t.locals (adjust_set s1.locals))) ++
             [(the_global s1.global,t.store ' Globals)] ++
             flat s1.stack t.stack))` by
     (first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
      \\ fs [] \\ rw [] \\ fs [])
    \\ rpt_drule0 word_copy_array_alias_thm
    \\ strip_tac
    \\ qpat_x_assum `_ = SOME m1` mp_tac
    \\ fs [word_copy_array_def,GSYM WORD_NOT_LOWER]
    \\ IF_CASES_TAC \\ fs [] \\ strip_tac
    THEN1
     (once_rewrite_tac [wordSemTheory.evaluate_def] \\ eval_tac
      \\ fs [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def,
             lookup_insert,asmTheory.word_cmp_def,wordSemTheory.bad_dest_args_def,
             wordSemTheory.find_code_def,eq_eval,push_env_code]
      \\ `lookup ByteCopyAdd_location t.code = SOME (5,ByteCopyAdd_code)` by
           (fs [state_rel_def,code_rel_def,stubs_def] \\ NO_TAC) \\ fs []
      \\ fs []
      \\ assume_tac CopyByteAdd_thm \\ SEP_I_TAC "evaluate"
      \\ pop_assum drule0 \\ fs [eq_eval]
      \\ impl_tac THEN1
       (fs [push_env_store]
        \\ fs [good_dimindex_def,dimword_def] \\ rfs []
        \\ match_mp_tac LESS_EQ_TRANS
        \\ qexists_tac `dimword (:'a)` \\ conj_tac
        \\ TRY (fs [dimword_def,DIV_LE_X] \\ NO_TAC)
        \\ `2 <= dimword (:'a)` by fs [dimword_def]
        \\ fs [wordSemTheory.MustTerminate_limit_def])
      \\ fs [] \\ disch_then kall_tac
      \\ fs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def,
             wordSemTheory.set_vars_def,alist_insert_def]
      \\ Cases_on `env_to_list y2 t.permute`
      \\ fs [domain_union,domain_fromAList_toAList]
      \\ `domain (fromAList q) = domain y2` by
        (imp_res_tac env_to_list_domain \\ asm_simp_tac std_ss [])
      \\ asm_simp_tac std_ss [AC UNION_COMM UNION_ASSOC]
      \\ fs [state_rel_thm,lookup_insert,lookup_fromAList,adjust_var_11]
      \\ drule0 env_to_list_lookup_equiv \\ fs [] \\ strip_tac
      \\ conj_tac THEN1
       (drule_all cut_envs_lookup_0
        \\ simp [lookup_union,lookup_fromAList,ALOOKUP_toAList])
      \\ conj_tac THEN1
       (gen_tac \\ IF_CASES_TAC \\ asm_simp_tac std_ss []
        \\ full_simp_tac std_ss [IS_SOME_lookup,domain_union] \\ strip_tac
        \\ fs [Abbr‘s1’] \\ drule_all IN_adjust_var_lemma \\ simp_tac std_ss [])
      \\ conj_tac THEN1
         (simp[stack_size_eq,option_le_max_right,AC option_add_comm option_add_assoc])
      \\ conj_tac THEN1
         (imp_res_tac stack_rel_IMP_size_of_stack >>
          rfs[stack_size_eq,option_le_max,option_le_max_right,
              AC option_add_comm option_add_assoc,option_le_eq_eqns,
              option_map2_max_add,option_le_add])
      \\ simp [FAPPLY_FUPDATE_THM]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ match_mp_tac memory_rel_Unit
      \\ drule0 memory_rel_tl \\ fs []
      \\ match_mp_tac quotientTheory.EQ_IMPLIES
      \\ `s1.tstamps = s.tstamps` by fs [Abbr `s1`] \\ fs []
      \\ AP_TERM_TAC \\ fs []
      \\ fs [Abbr‘s1’]
      \\ AP_TERM_TAC \\ AP_TERM_TAC
      \\ simp [lookup_inter_alt,lookup_union,lookup_fromAList,ALOOKUP_toAList]
      \\ rw [] \\ drule_all cut_env_envs_lookup_lookup
      \\ rw [] \\ asm_simp_tac std_ss [])
    THEN1
     (rewrite_tac [wordSemTheory.evaluate_def,list_Seq_def] \\ eval_tac
      \\ fs [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def,
             lookup_insert,asmTheory.word_cmp_def,wordSemTheory.bad_dest_args_def,
             wordSemTheory.find_code_def,eq_eval,push_env_code]
      \\ `lookup ByteCopySub_location t.code = SOME (5,ByteCopySub_code)` by
           (fs [state_rel_def,code_rel_def,stubs_def] \\ NO_TAC) \\ fs []
      \\ fs []
      \\ assume_tac CopyByteSub_thm \\ SEP_I_TAC "evaluate"
      \\ pop_assum drule0 \\ fs [eq_eval]
      \\ impl_tac THEN1
       (fs [push_env_store]
        \\ fs [good_dimindex_def,dimword_def] \\ rfs []
        \\ match_mp_tac LESS_EQ_TRANS
        \\ qexists_tac `dimword (:'a)` \\ conj_tac
        \\ TRY (fs [dimword_def,DIV_LE_X] \\ NO_TAC)
        \\ `2 <= dimword (:'a)` by fs [dimword_def]
        \\ fs [wordSemTheory.MustTerminate_limit_def])
      \\ fs [] \\ disch_then kall_tac
      \\ fs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def,
             wordSemTheory.set_vars_def,alist_insert_def]
      \\ Cases_on `env_to_list y2 t.permute`
      \\ fs [domain_union,domain_fromAList_toAList]
      \\ `domain (fromAList q) = domain y2` by
        (imp_res_tac env_to_list_domain \\ asm_simp_tac std_ss [])
      \\ asm_simp_tac std_ss [AC UNION_COMM UNION_ASSOC]
      \\ fs [state_rel_thm,lookup_insert,lookup_fromAList,adjust_var_11]
      \\ drule0 env_to_list_lookup_equiv \\ fs [] \\ strip_tac
      \\ conj_tac THEN1
       (drule_all cut_envs_lookup_0
        \\ simp [lookup_union,lookup_fromAList,ALOOKUP_toAList])
      \\ conj_tac THEN1
       (gen_tac \\ IF_CASES_TAC \\ asm_simp_tac std_ss []
        \\ full_simp_tac std_ss [IS_SOME_lookup,domain_union] \\ strip_tac
        \\ fs [Abbr‘s1’] \\ drule_all IN_adjust_var_lemma \\ simp_tac std_ss [])
      \\ conj_tac THEN1
         (simp[stack_size_eq,option_le_max_right,AC option_add_comm option_add_assoc])
      \\ conj_tac THEN1
         (imp_res_tac stack_rel_IMP_size_of_stack >>
          rfs[stack_size_eq,option_le_max,option_le_max_right,
              AC option_add_comm option_add_assoc,option_le_eq_eqns,
              option_map2_max_add,option_le_add])
      \\ simp [FAPPLY_FUPDATE_THM]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ match_mp_tac memory_rel_Unit
      \\ drule0 memory_rel_tl \\ fs []
      \\ match_mp_tac quotientTheory.EQ_IMPLIES
      \\ `s1.tstamps = s.tstamps` by fs [Abbr `s1`] \\ fs []
      \\ AP_TERM_TAC \\ fs []
      \\ fs [Abbr‘s1’]
      \\ AP_TERM_TAC \\ AP_TERM_TAC
      \\ simp [lookup_inter_alt,lookup_union,lookup_fromAList,ALOOKUP_toAList]
      \\ rw [] \\ drule_all cut_env_envs_lookup_lookup
      \\ rw [] \\ asm_simp_tac std_ss []))
  THEN1
   (`memory_rel c t.be (THE s1.tstamps) s1.refs s1.space t.store t.memory t.mdomain
         ((RefPtr src_b src,Word wa1)::(RefPtr dst_b dst,Word wa2)::
            (join_env s1.locals
               (toAList (inter t.locals (adjust_set s1.locals))) ++
             [(the_global s1.global,t.store ' Globals)] ++
             flat s1.stack t.stack))` by
     (first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
      \\ fs [] \\ rw [] \\ fs [])
    \\ rpt_drule0 word_copy_array_thm
    \\ strip_tac
    \\ qpat_x_assum `_ = SOME m1` mp_tac
    \\ fs [word_copy_array_def,GSYM WORD_NOT_LOWER]
    \\ IF_CASES_TAC \\ fs [] \\ strip_tac
    THEN1
     (once_rewrite_tac [wordSemTheory.evaluate_def] \\ eval_tac
      \\ fs [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def,
             lookup_insert,asmTheory.word_cmp_def,wordSemTheory.bad_dest_args_def,
             wordSemTheory.find_code_def,eq_eval,push_env_code]
      \\ `lookup ByteCopyAdd_location t.code = SOME (5,ByteCopyAdd_code)` by
           (fs [state_rel_def,code_rel_def,stubs_def]) \\ fs []
      \\ fs []
      \\ assume_tac CopyByteAdd_thm \\ SEP_I_TAC "evaluate"
      \\ pop_assum drule0 \\ fs [eq_eval]
      \\ impl_tac THEN1
       (fs [push_env_store]
        \\ fs [good_dimindex_def,dimword_def] \\ rfs []
        \\ match_mp_tac LESS_EQ_TRANS
        \\ qexists_tac `dimword (:'a)` \\ conj_tac
        \\ TRY (fs [dimword_def,DIV_LE_X] \\ NO_TAC)
        \\ `2 <= dimword (:'a)` by fs [dimword_def]
        \\ fs [wordSemTheory.MustTerminate_limit_def])
      \\ fs [] \\ disch_then kall_tac
      \\ fs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def]
      \\ Cases_on `env_to_list y2 t.permute` \\ fs []
      \\ reverse $ IF_CASES_TAC
      >-
       (qsuff_tac ‘F’ >- asm_rewrite_tac []
        \\ pop_assum mp_tac
        \\ imp_res_tac env_to_list_domain
        \\ simp [domain_union,domain_fromAList_toAList,AC UNION_COMM UNION_ASSOC])
      \\ fs [state_rel_thm,lookup_insert,lookup_fromAList,adjust_var_11]
      \\ drule0 env_to_list_lookup_equiv \\ fs [] \\ strip_tac
      \\ simp [wordSemTheory.set_vars_def,alist_insert_def]
      \\ conj_tac THEN1
       (drule_all cut_envs_lookup_0
        \\ simp [lookup_union,lookup_fromAList,ALOOKUP_toAList,lookup_insert])
      \\ conj_tac THEN1
       (drule0 env_to_list_lookup_equiv \\ fs [] \\ strip_tac
        \\ IF_CASES_TAC \\ asm_simp_tac std_ss [lookup_insert,adjust_var_11]
        \\ full_simp_tac std_ss [IS_SOME_lookup,domain_union] \\ strip_tac
        \\ fs [Abbr‘s1’] \\ drule_all IN_adjust_var_lemma \\ simp_tac std_ss [])
      \\ conj_tac THEN1
       (simp[stack_size_eq,option_le_max_right,AC option_add_comm option_add_assoc])
      \\ conj_tac THEN1
         (imp_res_tac stack_rel_IMP_size_of_stack >>
          rfs[stack_size_eq,option_le_max,option_le_max_right,
              AC option_add_comm option_add_assoc,option_le_eq_eqns,
              option_map2_max_add,option_le_add])
      \\ simp [FAPPLY_FUPDATE_THM]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ match_mp_tac memory_rel_Unit
      \\ drule0 memory_rel_tl \\ fs [] \\ strip_tac
      \\ drule0 memory_rel_tl \\ fs [] \\ pop_assum kall_tac
      \\ match_mp_tac quotientTheory.EQ_IMPLIES
      \\ `s1.tstamps = s.tstamps` by fs [Abbr `s1`] \\ fs []
      \\ AP_TERM_TAC \\ fs []
      \\ fs [Abbr‘s1’]
      \\ AP_TERM_TAC \\ AP_TERM_TAC
      \\ simp [lookup_inter_alt,lookup_union,lookup_fromAList,ALOOKUP_toAList]
      \\ rw [] \\ drule_all cut_env_envs_lookup_lookup
      \\ rw [] \\ asm_simp_tac std_ss [])
    THEN1
     (rewrite_tac [wordSemTheory.evaluate_def,list_Seq_def] \\ eval_tac
      \\ fs [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def,
             lookup_insert,asmTheory.word_cmp_def,wordSemTheory.bad_dest_args_def,
             wordSemTheory.find_code_def,eq_eval,push_env_code]
      \\ `lookup ByteCopySub_location t.code = SOME (5,ByteCopySub_code)` by
           (fs [state_rel_def,code_rel_def,stubs_def] \\ NO_TAC) \\ fs []
      \\ fs []
      \\ assume_tac CopyByteSub_thm \\ SEP_I_TAC "evaluate"
      \\ pop_assum drule0 \\ fs [eq_eval]
      \\ impl_tac THEN1
       (fs [push_env_store]
        \\ fs [good_dimindex_def,dimword_def] \\ rfs []
        \\ match_mp_tac LESS_EQ_TRANS
        \\ qexists_tac `dimword (:'a)` \\ conj_tac
        \\ TRY (fs [dimword_def,DIV_LE_X] \\ NO_TAC)
        \\ `2 <= dimword (:'a)` by fs [dimword_def]
        \\ fs [wordSemTheory.MustTerminate_limit_def])
      \\ fs [] \\ disch_then kall_tac
      \\ fs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def]
      \\ Cases_on `env_to_list y2 t.permute` \\ fs []
      \\ reverse $ IF_CASES_TAC
      >-
       (qsuff_tac ‘F’ >- asm_rewrite_tac []
        \\ pop_assum mp_tac
        \\ imp_res_tac env_to_list_domain
        \\ simp [domain_union,domain_fromAList_toAList,AC UNION_COMM UNION_ASSOC])
      \\ fs [state_rel_thm,lookup_insert,lookup_fromAList,adjust_var_11]
      \\ drule0 env_to_list_lookup_equiv \\ fs [] \\ strip_tac
      \\ simp [wordSemTheory.set_vars_def,alist_insert_def]
      \\ conj_tac THEN1
       (drule_all cut_envs_lookup_0
        \\ simp [lookup_union,lookup_fromAList,ALOOKUP_toAList,lookup_insert])
      \\ conj_tac THEN1
       (drule0 env_to_list_lookup_equiv \\ fs [] \\ strip_tac
        \\ IF_CASES_TAC \\ asm_simp_tac std_ss [lookup_insert,adjust_var_11]
        \\ full_simp_tac std_ss [IS_SOME_lookup,domain_union] \\ strip_tac
        \\ fs [Abbr‘s1’] \\ drule_all IN_adjust_var_lemma \\ simp_tac std_ss [])
      \\ conj_tac THEN1
       (simp[stack_size_eq,option_le_max_right,AC option_add_comm option_add_assoc])
      \\ conj_tac THEN1
         (imp_res_tac stack_rel_IMP_size_of_stack >>
          rfs[stack_size_eq,option_le_max,option_le_max_right,
              AC option_add_comm option_add_assoc,option_le_eq_eqns,
              option_map2_max_add,option_le_add])
      \\ simp [FAPPLY_FUPDATE_THM]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ match_mp_tac memory_rel_Unit
      \\ drule0 memory_rel_tl \\ fs [] \\ strip_tac
      \\ drule0 memory_rel_tl \\ fs [] \\ pop_assum kall_tac
      \\ match_mp_tac quotientTheory.EQ_IMPLIES
      \\ `s1.tstamps = s.tstamps` by fs [Abbr `s1`] \\ fs []
      \\ AP_TERM_TAC \\ fs []
      \\ fs [Abbr‘s1’]
      \\ AP_TERM_TAC \\ AP_TERM_TAC
      \\ simp [lookup_inter_alt,lookup_union,lookup_fromAList,ALOOKUP_toAList]
      \\ rw [] \\ drule_all cut_env_envs_lookup_lookup
      \\ rw [] \\ asm_simp_tac std_ss []))
QED

Theorem evaluate_XorLoop:
  ∀a1 a2 l dm m l1 l2 (t1:('a,'c,'ffi) wordSem$state) m1.
    word_xor_bytes a1 a2 l dm m = SOME m1 ∧ t1.memory = m ∧ t1.mdomain = dm ∧
    w2n l < t1.clock ∧ good_dimindex (:'a) ∧
    lookup XorLoop_location t1.code = SOME (4,XorLoop_code) ∧
    get_var 0 t1 = SOME (Loc l1 l2) ∧
    get_var 2 t1 = SOME (Word a2) ∧
    get_var 4 t1 = SOME (Word a1) ∧
    get_var 6 t1 = SOME (Word l) ⇒
    ∃ck max_stack.
      evaluate (XorLoop_code,t1) =
      (SOME (Result (Loc l1 l2) [Word 2w]),
       t1 with <| memory := m1; clock := ck; stack_max := max_stack;
                  locals := LN; locals_size := SOME 0 |>) ∧
      (max_stack ≠ t1.stack_max ⇒
       max_stack = OPTION_MAP2 MAX t1.stack_max
                     (OPTION_MAP2 $+ (stack_size t1.stack)
                        (lookup XorLoop_location t1.stack_size)))
Proof
  ho_match_mp_tac word_xor_bytes_ind \\ rpt gen_tac \\ strip_tac
  \\ rpt gen_tac
  \\ once_rewrite_tac [word_xor_bytes_def]
  \\ simp [SF CONJ_ss,read_word_def]
  \\ rpt IF_CASES_TAC \\ simp []
  \\ rpt strip_tac
  \\ rpt var_eq_tac
  >~ [‘get_var 6 t1 = SOME (Word 0w)’] >-
   (fs [wordSemTheory.isWord_exists,theWord_def,wordSemTheory.get_var_def]
    \\ simp [XorLoop_code_def,eq_eval,wordSemTheory.flush_state_def,list_Seq_def]
    \\ simp [wordSemTheory.state_component_equality])
  >~ [‘get_var 6 t1 = SOME (Word l)’,‘l <+ 2w’] >-
   (fs [wordSemTheory.isWord_exists,theWord_def,wordSemTheory.get_var_def]
    \\ simp [XorLoop_code_def,eq_eval,wordSemTheory.flush_state_def,list_Seq_def,
             wordSemTheory.mem_store_def]
    \\ simp [wordSemTheory.state_component_equality])
  \\ fs [wordSemTheory.isWord_exists,theWord_def,wordSemTheory.get_var_def,
        read_word_def] \\ rfs [theWord_def] \\ fs []
  \\ simp [XorLoop_code_def,eq_eval]
  (* 4 loads *)
  \\ ntac 4 $ once_rewrite_tac [list_Seq_def]
  \\ simp [eq_eval]
  (* 3 arith *)
  \\ ntac 3 $ once_rewrite_tac [list_Seq_def]
  \\ simp [eq_eval]
  (* 2 stores *)
  \\ ntac 2 $ once_rewrite_tac [list_Seq_def]
  \\ simp [eq_eval,wordSemTheory.mem_store_def]
  (* 2 arith *)
  \\ ntac 2 $ once_rewrite_tac [list_Seq_def]
  \\ simp [eq_eval]
  (* tail call *)
  \\ simp [eq_eval,list_Seq_def]
  \\ fs [theWord_def]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate (XorLoop_code,t2)’
  \\ last_x_assum $ qspecl_then [‘l1’,‘l2’,‘t2’] mp_tac
  \\ impl_tac
  >-
   (simp [Abbr‘t2’,lookup_insert]
    \\ Cases_on ‘l’ \\ gvs [good_dimindex_def,dimword_def,WORD_LO]
    \\ asm_rewrite_tac [GSYM word_sub_def,addressTheory.word_arith_lemma2]
    \\ simp [dimword_def])
  \\ strip_tac
  \\ simp [Abbr‘t2’]
  \\ qpat_x_assum ‘evaluate _ = _’ kall_tac \\ fs []
  \\ simp [wordSemTheory.state_component_equality]
QED

Theorem assign_XorByte:
  op = MemOp XorByte ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [assign_def] \\ rw []
  \\ fs [do_app,allowed_op_def]
  \\ gvs [AllCaseEqs()]
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ rename [‘get_vars [h1;h2] x.locals = SOME [RefPtr dst_b dst; RefPtr src_b src]’]
  \\ rename1 `lookup dst x.refs = SOME (ByteArray ys_fl ys)`
  \\ rename1 `lookup src x.refs = SOME (ByteArray xs_fl xs)`
  \\ fs [dataLangTheory.op_requires_names_def,
         dataLangTheory.op_space_reset_def,cut_state_opt_def]
  \\ Cases_on `names_opt` \\ fs []
  \\ rename [‘cut_state kept_names s = SOME x’]
  \\ first_assum (mp_tac o last o CONJUNCTS o SRULE [state_rel_thm])
  \\ strip_tac
  \\ drule_all state_rel_get_vars_IMP \\ strip_tac
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC,APPEND]
  \\ drule_all memory_rel_lookup_var_IMP
  \\ gvs [LENGTH_EQ_2]
  \\ qpat_x_assum ‘_ t.mdomain _’ kall_tac
  \\ strip_tac
  \\ ‘good_dimindex (:'a) ∧ shift_length c < dimindex (:α)’ by fs [state_rel_thm]
  \\ dxrule memory_rel_swap \\ strip_tac
  \\ dxrule_all memory_rel_xor_bytes
  \\ ‘good_dimindex (:'a) ∧ shift_length c < dimindex (:α)’ by fs [state_rel_thm]
  \\ strip_tac \\ gvs []
  (* simulation of generated code *)
  \\ gvs [wordSemTheory.get_vars_def,CaseEq"option"]
  \\ qpat_x_assum ‘get_var (adjust_var h1) t = SOME _’ assume_tac
  \\ dxrule_then drule_all get_var_get_real_addr_lemma
  \\ full_simp_tac std_ss [wordSemTheory.get_var_def]
  \\ dxrule_then drule_all word_exp_real_addr
  \\ rpt strip_tac
  \\ rpt $ qpat_x_assum ‘get_real_addr c t.store _ = SOME _’ kall_tac
  \\ ntac 2 $ once_rewrite_tac [list_Seq_def]
  \\ simp [eq_eval]
  (* load *)
  \\ once_rewrite_tac [list_Seq_def]
  \\ simp [eq_eval,word_exp_SmallLsr,GSYM decode_length_def]
  \\ IF_CASES_TAC >-
   (qsuff_tac ‘F’ >- rewrite_tac []
    \\ fs [heap_in_memory_store_def,memory_rel_def])
  \\ simp []
  \\ ntac 3 $ pop_assum kall_tac
  (* two adds *)
  \\ ntac 2 $ once_rewrite_tac [list_Seq_def]
  \\ simp [eq_eval,get_names_def]
  (* call *)
  \\ fs [cut_state_opt_def,cut_state_def,CaseEq"option"]
  \\ qabbrev_tac `s1 = s with locals := env` \\ var_eq_tac
  \\ drule_all cut_env_IMP_cut_env \\ strip_tac
  \\ drule cut_env_IMP_cut_envs \\ strip_tac \\ fs []
  \\ once_rewrite_tac [list_Seq_def]
  \\ `lookup XorLoop_location t.code = SOME (4,XorLoop_code)` by
    fs [state_rel_def,code_rel_def,stubs_def]
  \\ simp [eq_eval,cut_envs_adjust_sets_insert_ODD,domain_adjust_sets]
  \\ Cases_on ‘env_to_list y2 t.permute’
  \\ simp [wordSemTheory.push_env_def]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate (XorLoop_code,t1)’
  \\ rename [‘insert 0 (Loc rl1 rl2) LN’]
  \\ drule evaluate_XorLoop
  \\ disch_then $ qspecl_then [‘rl1’,‘rl2’,‘t1’] mp_tac
  \\ impl_tac
  >-
   (simp [Abbr‘t1’,wordSemTheory.get_var_def,lookup_insert]
    \\ irule LESS_LESS_EQ_TRANS
    \\ irule_at Any w2n_lt
    \\ rewrite_tac [wordSemTheory.MustTerminate_limit_def]
    \\ ‘dimword (:α) < 2 * dimword (:α)’ by gvs [good_dimindex_def,dimword_def]
    \\ decide_tac)
  \\ qpat_x_assum ‘lookup XorLoop_location _ = _’ kall_tac
  \\ strip_tac \\ simp []
  \\ simp [Abbr‘t1’,wordSemTheory.pop_env_def]
  \\ reverse $ IF_CASES_TAC
  >-
   (qsuff_tac ‘F’ >- rewrite_tac []
    \\ fs [domain_union,domain_fromAList_toAList]
    \\ pop_assum mp_tac
    \\ drule env_to_list_domain
    \\ simp_tac std_ss [AC UNION_COMM UNION_ASSOC])
  \\ simp [wordSemTheory.set_vars_def,alist_insert_def]
  \\ qpat_x_assum ‘evaluate (XorLoop_code,_) = _’ kall_tac
  \\ fs [] \\ rpt var_eq_tac
  (* final part: proving state_rel *)
  \\ simp [list_Seq_def,eq_eval,data_to_wordTheory.Unit_def]
  \\ qpat_x_assum ‘state_rel c l1 l2 s1 t [] locs’ mp_tac
  \\ simp [state_rel_thm,dataSemTheory.set_var_def,lookup_insert]
  \\ strip_tac \\ pop_assum kall_tac
  \\ conj_tac >-
   (drule_all cut_envs_lookup_0
    \\ simp [lookup_union,lookup_fromAList,ALOOKUP_toAList])
  \\ conj_tac >-
   (gen_tac \\ IF_CASES_TAC \\ asm_simp_tac std_ss [adjust_var_11]
    \\ full_simp_tac std_ss [IS_SOME_lookup,domain_union] \\ strip_tac
    \\ fs [Abbr‘s1’] \\ drule_all IN_adjust_var_lemma \\ simp_tac std_ss [])
  \\ conj_tac >-
   (simp[stack_size_eq,option_le_max_right,AC option_add_comm option_add_assoc])
  \\ conj_tac >-
   (imp_res_tac stack_rel_IMP_size_of_stack
    \\ rfs[stack_size_eq,option_le_max,option_le_max_right,
           AC option_add_comm option_add_assoc,option_le_eq_eqns,
           option_map2_max_add,option_le_add])
  (* memory_rel *)
  \\ once_rewrite_tac [insert_insert] \\ rewrite_tac []
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
  \\ irule memory_rel_insert \\ rewrite_tac [APPEND]
  \\ irule memory_rel_Unit \\ asm_rewrite_tac []
  \\ qpat_x_assum ‘_ t.mdomain _’ mp_tac
  \\ match_mp_tac memory_rel_rearrange
  \\ simp [SF DNF_ss]
  \\ fs [join_env_def,inter_union_distrib]
  \\ drule_all cut_envs_inter \\ strip_tac \\ simp []
  \\ qunabbrev_tac ‘s1’ \\ simp []
  \\ qsuff_tac `inter (fromAList q) (adjust_set env) = inter t.locals (adjust_set env)`
  >- asm_simp_tac std_ss []
  \\ fs [spt_eq_thm,lookup_inter_alt]
  \\ rw [] \\ fs []
  \\ drule env_to_list_lookup_equiv
  \\ fs [lookup_insert,lookup_fromAList,adjust_var_11]
  \\ rpt strip_tac \\ fs []
  \\ fs [wordSemTheory.cut_envs_def,cut_env_def] \\ rveq
  \\ gvs [wordSemTheory.cut_names_def,AllCaseEqs()]
  \\ fs [lookup_inter_alt] \\ rw []
  \\ unabbrev_all_tac \\ fs [IN_domain_adjust_set_inter]
  \\ gvs [adjust_sets_def]
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
      lookup AppendMainLoop_location t.code = SOME (6,AppendMainLoop_code c) /\
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
  \\ fs [SIMP_RULE (srw_ss()) [] word_and_one_eq_0_iff]
  \\ strip_tac \\ fs []
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
    lookup AppendMainLoop_location t.code = SOME (6,AppendMainLoop_code c) /\
    lookup AppendLenLoop_location t.code = SOME (3,AppendLenLoop_code c) /\
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
         | (NONE,s) => (SOME Error, s) | res => res) /\
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
    \\ Cases_on `q` \\ fs []
    >>
    (conj_tac >- simp[option_le_max_right]
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
  \\ fs [SIMP_RULE (srw_ss()) [] word_and_one_eq_0_iff]
  \\ strip_tac \\ fs []
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
  \\ Cases_on `q` \\ fs [block_drop_def]
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
    lookup 4 t.locals = SOME (Word (n2w (12 * k))) /\
    lookup AppendLenLoop_location t.code = SOME (3,AppendLenLoop_code c) /\
    t.locals_size = lookup AppendLenLoop_location t.stack_size /\
    good_dimindex (:'a) /\
    LENGTH xs <= t.clock ==>
    ?locals smx.
      (case evaluate (AppendLenLoop_code c, t) of
        (NONE,s) => (SOME Error,s)
      | res => res) =
      (case evaluate (AppendLenLoop_code c,
              t with <| locals := locals;
                        clock := t.clock - LENGTH xs;
                        stack_max := smx
                      |>) of
        (NONE,s) => (SOME Error,s)
      | res => res) /\
      lookup 0 locals = SOME (Loc l1 l2) /\
      lookup 2 locals = SOME (Word 2w) /\
      lookup 4 locals = SOME (Word (n2w (12 * (k + LENGTH xs)))) /\
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

Theorem OPTION_MAP2_NONE_THM:
  (OPTION_MAP2 f NONE x = NONE) ∧
  (OPTION_MAP2 f x NONE = NONE)
Proof
  Cases_on`x`>>fs[OPTION_MAP2_THM]
QED

(* TODO: declared with [simp] further down *)
Theorem opt_map_plus_zero_id[local]:
  !n. OPTION_MAP2 $+ (SOME 0) n = (n:num option)
Proof
  Cases_on `n` >> fs []
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
  rpt strip_tac \\ drule (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ asm_rewrite_tac [] \\ pop_assum kall_tac
  \\ imp_res_tac state_rel_cut_IMP
  \\ fs [assign_def] \\ rveq
  \\ fs [dataLangTheory.op_requires_names_def,
         dataLangTheory.op_space_reset_def,cut_state_opt_def]
  \\ Cases_on `names_opt` \\ fs []
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app,allowed_op_def]
  \\ `?r1 r2. vals = [r1;r2]` by
     (Cases_on `vals` \\ fs [] \\ Cases_on `t'` \\ fs [] \\ Cases_on `t''` \\ fs [])
  \\ rveq \\ fs []
  \\ Cases_on `v_to_list r1` \\ fs []
  \\ Cases_on `v_to_list r2` \\ fs []
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ Cases_on `encode_header c 0 2` \\ fs []
  >- (
    conj_tac >-
      (drule_then match_mp_tac option_le_trans >>
       fs[with_fresh_ts_def,CaseEq"option",check_lim_def,opt_map_plus_zero_id] >>
       rveq >> simp[] >>
       FULL_SIMP_TAC std_ss [state_rel_def,option_le_max_right]) >>
    strip_tac >>
    `good_dimindex(:'a)` by metis_tac[state_rel_def] >>
    fs[good_dimindex_def,encode_header_def,dimword_def] >> fs[] >>
    spose_not_then strip_assume_tac >>
    fs[with_fresh_ts_def,CaseEq"option"] >> rveq >> fs[check_lim_def] >>
    metis_tac[state_rel_def,limits_inv_def])
  \\ rename1 `v_to_list r1 = SOME in1`
  \\ rename1 `v_to_list r2 = SOME in2`
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ rpt (qpat_x_assum `!x._` kall_tac)
  \\ clean_tac \\ fs [wordSemTheory.evaluate_def,domain_adjust_sets]
  \\ Cases_on `ws` \\ fs [] \\ Cases_on `t'` \\ fs [] \\ rveq
  \\ fs [get_vars_SOME_IFF]
  \\ fs [wordSemTheory.get_vars_def]
  \\ fs [wordSemTheory.bad_dest_args_def]
  \\ fs [wordSemTheory.add_ret_loc_def,wordSemTheory.find_code_def]
  \\ `lookup Append_location t.code = SOME (3, Append_code c)` by
       fs [state_rel_thm,code_rel_def,stubs_def] \\ fs []
  \\ fs [cut_state_opt_def,cut_state_def,get_names_def]
  \\ rename1 `state_rel c l1 l2 s1 t [] locs`
  \\ Cases_on `dataSem$cut_env x' s.locals` \\ fs []
  \\ clean_tac \\ fs []
  \\ qabbrev_tac `s1 = s with locals := x`
  \\ `?y. cut_env (adjust_sets x') t.locals = SOME y` by
       (match_mp_tac (GEN_ALL cut_env_IMP_cut_env) \\ fs []
        \\ metis_tac []) \\ fs []
  \\ drule cut_env_IMP_cut_envs \\ strip_tac
  \\ simp [Append_code_def]
  \\ simp [wordSemTheory.evaluate_def]
  \\ fs [asmTheory.word_cmp_def,wordSemTheory.get_var_imm_def]
  \\ simp [EVAL ``get_var 4 (call_env [Loc n l; h'; h] (lookup Append_location t.stack_size) s)``]
  \\ simp [EVAL ``get_var 2 (call_env [Loc n l; h'; h] (lookup Append_location t.stack_size) s)``]
  \\ simp [EVAL ``get_var 0 (call_env [Loc n l; h'; h] (lookup Append_location t.stack_size) s)``]
  \\ Cases_on `in1` \\ fs [v_to_list_SOME_NIL_IFF]
  THEN1
   (rveq \\ fs []
    \\ qpat_x_assum `state_rel c l1 l2 s1 t [] locs` mp_tac
    \\ simp [Once state_rel_thm,option_le_max_right] \\ strip_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ drule (GEN_ALL memory_rel_get_vars_IMP)
    \\ fs [Abbr`s1`]
    \\ disch_then drule
    \\ fs [wordSemTheory.get_vars_def]
    \\ fs [SIMP_RULE (srw_ss()) [] word_and_one_eq_0_iff]
    \\ strip_tac
    \\ drule memory_rel_Block_IMP \\ fs []
    \\ strip_tac \\ rveq \\ fs []
    \\ simp [wordSemTheory.dec_clock_def,
             wordSemTheory.push_env_def]
    \\ Cases_on `env_to_list y2 t.permute` \\ fs []
    \\ simp [wordSemTheory.call_env_def,
             wordSemTheory.pop_env_def,lookup_insert,
             wordSemTheory.get_var_def,fromList2_def]
    \\ reverse IF_CASES_TAC THEN1
     (sg `F` \\ fs [] \\ pop_assum mp_tac \\ simp []
      \\ imp_res_tac env_to_list_domain
      \\ simp [domain_union,domain_fromAList_toAList,AC UNION_COMM UNION_ASSOC])
    \\ fs [wordSemTheory.set_var_def,set_var_def]
    \\ fs [state_rel_thm]
    \\ fs [lookup_insert,adjust_var_11, call_env_def,with_fresh_ts_def,
           wordSemTheory.set_vars_def,alist_insert_def,
           push_env_def,set_var_def,wordSemTheory.set_var_def,IS_SOME_EXISTS]
    \\ fs [] \\ rveq \\ fs [list_to_v_def]
    \\ simp[option_le_max_right, check_lim_def, wordSemTheory.flush_state_def, allowed_op_def]
    \\ qmatch_goalsub_rename_tac `memory_rel _ _ ts1 _ _ _ _ _ _`
    \\ strip_tac THEN1
     (simp [lookup_union,lookup_fromAList,ALOOKUP_toAList]
      \\ drule_all cut_envs_lookup_0 \\ simp [])
    \\ conj_tac THEN1
     (gen_tac \\ IF_CASES_TAC \\ simp [] \\ fs [lookup_fromAList]
      \\ asm_rewrite_tac [GSYM IS_SOME_EXISTS,IS_SOME_lookup_domain]
      \\ rw[] \\ drule_all cut_envs_domain_IN \\ simp [])
    \\ conj_tac THEN1
      (fs[size_of_stack_eq,option_le_max_right,option_le_max,option_map2_max_add,AC option_add_comm option_add_assoc,option_le_eq_eqns,option_map2_max_add,stack_size_eq,opt_map_plus_zero_id] >>
       FULL_SIMP_TAC bool_ss [state_rel_def] >>
       imp_res_tac stack_rel_IMP_size_of_stack >> simp[option_le_add] >>
       metis_tac[option_le_flip_neg,option_le_trans]
      )
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs [flat_def]
    \\ rfs [THE_DEF]
    \\ drule memory_rel_tl \\ strip_tac
    \\ drule (GEN_ALL memory_rel_less_space)
    \\ disch_then (qspec_then `0` mp_tac) \\ fs []
    \\ fs [join_env_def,inter_union_distrib]
    \\ drule_all cut_envs_inter \\ strip_tac \\ simp []
    \\ qsuff_tac `inter (fromAList q) (adjust_set x) = inter t.locals (adjust_set x)`
    >- asm_simp_tac std_ss []
    \\ fs [spt_eq_thm,lookup_inter_alt]
    \\ rw [] \\ fs []
    \\ drule env_to_list_lookup_equiv
    \\ fs [lookup_insert,lookup_fromAList,adjust_var_11]
    \\ rpt strip_tac \\ fs []
    \\ fs [wordSemTheory.cut_envs_def,cut_env_def] \\ rveq
    \\ gvs [wordSemTheory.cut_names_def,AllCaseEqs()]
    \\ fs [lookup_inter_alt] \\ rw []
    \\ unabbrev_all_tac \\ fs [IN_domain_adjust_set_inter]
    \\ gvs [adjust_sets_def])
  \\ `?ww. h = Word ww /\ (1w && ww) <> 0w` by
   (imp_res_tac v_to_list_SOME_CONS_IMP \\ rveq \\ fs []
    \\ qpat_x_assum `state_rel c l1 l2 s1 t [] locs` mp_tac
    \\ simp [Once state_rel_thm,option_le_max_right] \\ strip_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ drule (GEN_ALL memory_rel_get_vars_IMP)
    \\ fs [Abbr`s1`]
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
  \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def,FLOOKUP_UPDATE,
           wordLangTheory.word_sh_def,wordSemTheory.get_store_def]
  \\ IF_CASES_TAC THEN1
   (sg `F` \\ fs []
    \\ fs [state_rel_thm,memory_rel_def,heap_in_memory_store_def])
  \\ simp []
  \\ qpat_x_assum `~(_ /\ _)` kall_tac
  \\ qmatch_goalsub_abbrev_tac `insert 7 (Word init_ptr)`
  \\ simp [list_Seq_def,eq_eval,wordSemTheory.set_store_def]
  \\ `lookup AppendMainLoop_location t.code = SOME (6,AppendMainLoop_code c)` by
       fs [state_rel_thm,code_rel_def,stubs_def] \\ fs []
  \\ rename1 `encode_header c 0 2 = SOME hdr`
  \\ rename1 `v_to_list r1 = SOME (i1::in1)`
  \\ qpat_x_assum `state_rel c l1 l2 s1 t [] locs` mp_tac
  \\ simp [Once state_rel_thm,option_le_max_right] \\ strip_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule (GEN_ALL memory_rel_get_vars_IMP)
  \\ fs [Abbr`s1`] \\ fs [] \\ disch_then drule
  \\ fs [wordSemTheory.get_vars_def] \\ strip_tac
  (* MEM *)
  \\ drule memory_rel_space_max
  \\ simp [] \\ strip_tac \\ fs []
  \\ drule (GEN_ALL memory_rel_IMP_word_list_exists) \\ fs []
  \\ disch_then (qspec_then `sp` mp_tac) \\ fs [] \\ strip_tac
  \\ Cases_on `3 * LENGTH (i1::in1) <= sp`
  THEN1
   (assume_tac (GEN_ALL evaluate_AppendMainLoop_code)
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
      \\ pop_assum mp_tac
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
    \\ strip_tac THEN1
      fs [code_oracle_rel_def, FLOOKUP_UPDATE]
    \\ strip_tac THEN1
     (simp [lookup_union,lookup_fromAList,ALOOKUP_toAList]
      \\ drule_all cut_envs_lookup_0 \\ simp [])
    \\ conj_tac THEN1
     (gen_tac \\ IF_CASES_TAC \\ simp [] \\ fs [lookup_fromAList]
      \\ asm_rewrite_tac [GSYM IS_SOME_EXISTS,IS_SOME_lookup_domain]
      \\ rw[] \\ drule_all cut_envs_domain_IN \\ simp [])
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
      qhdtm_x_assum `limits_inv` mp_tac
      \\ simp[limits_inv_def,FLOOKUP_UPDATE])
    \\ fs [memory_rel_Temp,
         MATCH_MP FUPDATE_COMMUTES (prove(``Temp p <> NextFree``,EVAL_TAC))]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs [flat_def]
    \\ simp [FAPPLY_FUPDATE_THM]
    \\ qmatch_asmsub_abbrev_tac `memory_rel _ _ _ _ _ _ _ _ (A ++ B::C)`
    \\ sg `memory_rel c t.be (THE s.tstamps) s.refs sp t.store m1 t.mdomain ((B::A) ++ C)`
    >-
     (irule memory_rel_rearrange
      \\ HINT_EXISTS_TAC
      \\ rw [] \\ fs [])
    \\ map_every qunabbrev_tac [`A`,`B`,`C`]
    (* MEM r2 *)
    \\ drule memory_rel_append
    \\ simp [make_cons_ptr_def]
    \\ impl_keep_tac
    >- fs [Abbr`init_ptr`, get_lowerbits_def, make_header_def, encode_header_def]
    \\ strip_tac
    \\ drule (GEN_ALL memory_rel_less_space)
    \\ disch_then (qspec_then `0` mp_tac) \\ fs []
    \\ fs [join_env_def]
    \\ match_mp_tac (METIS_PROVE [] ``x = y ==> x ==> y``)
    \\ fs [get_lowerbits_def]
    \\ AP_TERM_TAC \\ AP_TERM_TAC \\ fs []
    \\ AP_TERM_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC
    \\ rewrite_tac [inter_union_distrib]
    \\ drule_all cut_envs_inter \\ simp [] \\ strip_tac
    \\ fs [spt_eq_thm,lookup_inter_alt,lookup_union]
    \\ rw [] \\ fs []
    \\ drule env_to_list_lookup_equiv
    \\ fs [lookup_insert,lookup_fromAList,adjust_var_11]
    \\ rpt strip_tac \\ fs []
    \\ fs [wordSemTheory.cut_envs_def,cut_env_def] \\ rveq
    \\ gvs [wordSemTheory.cut_names_def,AllCaseEqs()]
    \\ fs [lookup_inter_alt] \\ rw []
    \\ unabbrev_all_tac \\ fs [IN_domain_adjust_set_inter]
    \\ gvs [adjust_sets_def])
  \\ assume_tac (GEN_ALL evaluate_AppendMainLoop_code_alt)
  \\ SEP_I_TAC "evaluate"
  \\ fs [lookup_insert,FLOOKUP_UPDATE]
  \\ pop_assum drule
  \\ rewrite_tac [markerTheory.Abbrev_def]
  \\ simp []
  \\ disch_then (qspec_then `SEP_T` mp_tac)
  \\ impl_tac THEN1
   (conj_tac THEN1 fs [stubs_def,code_rel_def]
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
    \\ fs [stubs_def,code_rel_def]
    \\ imp_res_tac memory_rel_list_limit
    \\ `2 * dimword (:'a) <= MustTerminate_limit (:α)` by
      fs [wordSemTheory.MustTerminate_limit_def]
    \\ rfs [good_dimindex_def,dimword_def] \\ rfs [] \\ fs [])
  \\ strip_tac \\ fs []
  \\ rpt (qpat_x_assum `lookup _ _ = _` mp_tac)
  \\ rpt strip_tac
  \\ `state_rel c l1 l2 ((s with <| locals := x ; space := sp ; stack_max :=
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
        t.store |+ (Temp 0w,h') |+ (Temp 1w,Word ww) |+
         (Temp 2w,Word init_ptr) |>) with memory := m1) [] locs` by
   (fs [state_rel_thm,FAPPLY_FUPDATE_THM]
    \\ conj_tac >- fs [code_oracle_rel_def, FLOOKUP_UPDATE]
    \\ fs [limits_inv_def, FLOOKUP_UPDATE]
    \\ conj_tac
    >- (rw[option_le_max_right])
    \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac memory_rel_rearrange)
    \\ fs[MEM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[])
  \\ simp [AppendLenLoop_code_def,Once list_Seq_def]
  \\ fs [eq_eval,FLOOKUP_UPDATE]
  \\ simp [Once list_Seq_def,eq_eval]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [eq_eval]
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
  \\ `dataSem$cut_env x' x = SOME x` by
   (fs [dataSemTheory.cut_env_def] \\ rveq
    \\ fs [domain_inter,spt_eq_thm]
    \\ fs [lookup_inter_alt])
  \\ disch_then drule
  \\ disch_then drule
  \\ disch_then (qspecl_then [`lookup AppendLenLoop_location s.stack_frame_sizes`,
                               `n`,`l`] assume_tac)
  \\ qmatch_assum_abbrev_tac `state_rel c n l s3 _ _ _`
  \\ `state_rel c n l (s3 with clock := tt.clock) tt [] ((l1,l2)::locs)` by
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
  THEN1 (fs [with_fresh_ts_def] \\ Cases_on `s.tstamps`  \\ fs [check_lim_def] \\ rveq \\
    unabbrev_all_tac >>
    conj_tac >- rw[call_env_def,push_env_def,dataSemTheory.dec_clock_def] >>
    conj_tac >-
      (drule_then match_mp_tac option_le_trans >>
       rw[call_env_def,push_env_def,dataSemTheory.dec_clock_def] >>
       rw[size_of_stack_eq,option_le_max_right,option_le_max,option_map2_max_add,AC option_add_comm option_add_assoc,option_le_eq_eqns,option_map2_max_add,stack_size_eq,option_le_add]
      ) >>
    rw[] >>
    spose_not_then strip_assume_tac >>
    first_x_assum drule >>
    impl_tac >-
      (`(bytes_in_word * n2w sp) ⋙ (shift (:α) − 2) = n2w (4 * sp):'a word` by
       (rewrite_tac [GSYM w2n_11,w2n_lsr]
        \\ fs [good_dimindex_def,bytes_in_word_def,shift_def,
               dimword_def,word_mul_n2w] \\ rfs []
        \\ fs [DIV_EQ_X]) >>
       pop_assum SUBST_ALL_TAC >>
       fs [word_add_n2w] >>
       fs [ADD_DIV_EQ] \\ fs [X_LE_DIV] >>
       simp [LEFT_SUB_DISTRIB] >>
       rw[SUB_LEFT_ADD] >-
         (fs[NOT_LESS_EQUAL] >>
          mp_tac (Q.INST [`m`|->`3`,`d`|->`sp`,`k`|->`sp+1`] IMP_MULT_DIV_LESS) >>
          impl_tac >- simp[] >>
          disch_then(assume_tac o SIMP_RULE std_ss [LESS_EQ,ADD1]) >>
          `3* (SUC (LENGTH in1)) <= 3 * (sp DIV 3)` by simp[] >>
          drule_then drule LESS_EQ_TRANS >> strip_tac >>
          metis_tac[LESS_EQ_ANTISYM]) >>
       fs[NOT_LESS_EQUAL] >>
       strip_assume_tac (MATCH_MP DIVISION (DECIDE ``0<3n``) |> Q.SPEC `sp`) >>
       qpat_x_assum `_ = _` (fn th => once_rewrite_tac [th]
          THEN rewrite_tac [LEFT_ADD_DISTRIB]
          THEN rewrite_tac [GSYM th]) >>
       fs [LEFT_SUB_DISTRIB] >>
       `(12 * SUC (LENGTH in1) + 4 * sp MOD 3) < dimword (:α)` by
        (`sp MOD 3 < 3` by fs []
         \\ qpat_x_assum `memory_rel c t.be _ s.refs s.space t.store t.memory t.mdomain
            ((r1,Word ww)::_)` assume_tac
         \\ drule (GEN_ALL memory_rel_list_limit)
         \\ rfs [good_dimindex_def] \\ rfs [dimword_def]
         \\ fs [LEFT_ADD_DISTRIB]
         \\ `sp MOD 3 < 3` by fs [] \\ simp []) >>
       fs [ADD_DIV_EQ] \\ fs [X_LE_DIV] >>
       simp [ADD_DIV_ADD_DIV |> PURE_ONCE_REWRITE_RULE[ADD_SYM]
                             |> PURE_ONCE_REWRITE_RULE[MULT_SYM]] >>
       simp [intLib.COOPER_PROVE ``12 * a DIV 4 = 3 * a``] >>
       simp[SUB_LEFT_LESS] >>
       `dimword (:'a) = 2**arch_size s.limits` by(fs[state_rel_def,limits_inv_def,dimword_def,
                                                     arch_size_def,good_dimindex_def]) >>
       pop_assum SUBST_ALL_TAC >>
       match_mp_tac LESS_EQ_LESS_TRANS >> HINT_EXISTS_TAC >>
       simp[] >>
       rpt(pop_assum kall_tac) >> intLib.COOPER_TAC) >>
    simp[call_env_def,push_env_def,dataSemTheory.dec_clock_def] >>
    qmatch_goalsub_abbrev_tac `cut_locals _ a_state` >>
    `cut_locals (fromList [(); ()]) a_state = a_state`
      by(rw[Abbr `a_state`,cut_locals_def,cut_env_def,domain_fromList] >>
         rw[dataSemTheory.state_component_equality] >>
         EVAL_TAC) >>
    pop_assum SUBST_ALL_TAC >>
    qunabbrev_tac `a_state` >>
    rfs[space_consumed_def] >>
    simp[NOT_LESS] >>
    match_mp_tac LESS_EQ_TRANS >> HINT_EXISTS_TAC >> simp[] >>
    simp[size_of_heap_def,stack_to_vs_def,extract_stack_def] >>
    simp[EVAL ``sptree$toList (fromList [a1; a2])``] >>
    qmatch_goalsub_abbrev_tac `size_of _ (r1::r2::rheap)` >>
    `size_of s.limits (r1::r2::rheap) s.refs LN =
     size_of s.limits rheap s.refs LN`
      by(`MEM r1 (r2::rheap)` by(fs[Abbr`rheap`,MEM_toList,get_vars_def,get_var_def,
                                    CaseEq "option"] >> metis_tac[]) >>
         Cases_on `r1` >> TRY(fs[v_to_list_def] >> NO_TAC) >>
         simp[size_of_cons_seen_Block] >>
         Cases_on `r2` >> TRY(fs[v_to_list_def] >> NO_TAC) >>
         match_mp_tac size_of_cons_seen_Block >>
         pop_assum kall_tac >>
         fs[Abbr`rheap`,MEM_toList,get_vars_def,get_var_def,
            CaseEq "option"] >> metis_tac[]) >>
    pop_assum SUBST_ALL_TAC >>
    qpat_abbrev_tac `zzz = ((λ(n,_,_). n) _)` >>
    simp[] >>
    `(bytes_in_word * n2w sp) ⋙ (shift (:α) − 2) = n2w (4 * sp):'a word` by
      (rewrite_tac [GSYM w2n_11,w2n_lsr]
       \\ fs [good_dimindex_def,bytes_in_word_def,shift_def,
              dimword_def,word_mul_n2w] \\ rfs []
       \\ fs [DIV_EQ_X]) >>
    pop_assum SUBST_ALL_TAC >>
    fs [word_add_n2w] >>
    fs [ADD_DIV_EQ] \\ fs [X_LE_DIV] >>
    simp [LEFT_SUB_DISTRIB] >>
    rw[SUB_LEFT_ADD] >-
      (fs[NOT_LESS_EQUAL] >>
       mp_tac (Q.INST [`m`|->`3`,`d`|->`sp`,`k`|->`sp+1`] IMP_MULT_DIV_LESS) >>
       impl_tac >- simp[] >>
       disch_then(assume_tac o SIMP_RULE std_ss [LESS_EQ,ADD1]) >>
       `3* (SUC (LENGTH in1)) <= 3 * (sp DIV 3)` by simp[] >>
       drule_then drule LESS_EQ_TRANS >> strip_tac >>
       metis_tac[LESS_EQ_ANTISYM]) >>
    fs[NOT_LESS_EQUAL] >>
    strip_assume_tac (MATCH_MP DIVISION (DECIDE ``0<3n``) |> Q.SPEC `sp`) >>
    qpat_x_assum `_ = _` (fn th => once_rewrite_tac [th]
       THEN rewrite_tac [LEFT_ADD_DISTRIB]
       THEN rewrite_tac [GSYM th]) >>
    fs [LEFT_SUB_DISTRIB] >>
    `(12 * SUC (LENGTH in1) + 4 * sp MOD 3) < dimword (:α)` by
     (`sp MOD 3 < 3` by fs []
      \\ qpat_x_assum `memory_rel c t.be _ s.refs s.space t.store t.memory t.mdomain
         ((r1,Word ww)::_)` assume_tac
      \\ drule (GEN_ALL memory_rel_list_limit)
      \\ rfs [good_dimindex_def] \\ rfs [dimword_def]
      \\ fs [LEFT_ADD_DISTRIB]
      \\ `sp MOD 3 < 3` by fs [] \\ simp []) >>
    fs [ADD_DIV_EQ] \\ fs [X_LE_DIV] >>
    `(4 * sp MOD 3 + 4) = 4 * (sp MOD 3 + 1)` by simp[] >>
    simp  [ADD_DIV_ADD_DIV |> PURE_ONCE_REWRITE_RULE[ADD_SYM]
                          |> PURE_ONCE_REWRITE_RULE[MULT_SYM]] >>
    simp [intLib.COOPER_PROVE ``12 * a DIV 4 = 3 * a``] >>
    simp[MULT_CLAUSES] >> rpt(pop_assum kall_tac) >> intLib.COOPER_TAC)
  \\ rveq \\ fs []
  \\ qabbrev_tac `new_sp = w2n ww11 DIV 4 + 1`
  \\ `3 * LENGTH (i1::in1) <= new_sp` by
   (`(bytes_in_word * n2w sp) ⋙ (shift (:α) − 2) = n2w (4 * sp):'a word` by
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
    \\ `12 * (sp DIV 3) < 12 * SUC (LENGTH in1)` by
           (fs [LT_MULT_LCANCEL,DIV_LT_X]) \\ fs []
    \\ `(12 * SUC (LENGTH in1) + 4 * sp MOD 3) < dimword (:α)` by
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
  \\ qpat_x_assum `state_rel c n l s4 aa2 [] ((l1,l2)::locs)` mp_tac
  \\ simp [Once state_rel_thm]
  \\ strip_tac \\ fs []
  \\ `lookup Append_location aa2.code = SOME (3,Append_code c)` by
        fs [code_rel_def,stubs_def] \\ simp [] \\ rfs []
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
  \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def,FLOOKUP_UPDATE,
           wordLangTheory.word_sh_def,
           wordSemTheory.get_store_def]
  \\ qmatch_goalsub_abbrev_tac `insert 7 (Word init_ptr2)`
  \\ simp [list_Seq_def,eq_eval,wordSemTheory.set_store_def]
  \\ `lookup AppendMainLoop_location aa2.code = SOME (6,AppendMainLoop_code c)` by
       fs [state_rel_thm,code_rel_def,stubs_def] \\ fs [] \\ rfs []
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
  \\ strip_tac
  THEN1
   (qpat_x_assum `code_oracle_rel c _ _ _ _ _ _ _` mp_tac
    \\ fs [code_oracle_rel_def,FLOOKUP_UPDATE, check_lim_def])
  \\ strip_tac
  >-
     (simp [lookup_insert]
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
      \\ fs [])
  \\ conj_tac
  >- (gen_tac
      \\ simp [lookup_insert]
      \\ IF_CASES_TAC \\ simp [adjust_var_11]
      \\ simp [lookup_fromAList,lookup_union]
      \\ simp [CaseEq"option",SF DNF_ss])
  \\ conj_tac >- (
    simp[option_le_max_right] >>
    drule evaluate_stack_max>>simp[]>>
    qmatch_goalsub_abbrev_tac`option_CASE sm1`>>
    strip_tac>>
    `option_le sm1 smx''` by
      (pop_assum mp_tac>>Cases_on`sm1`>>Cases_on`smx''`>>
      simp[miscTheory.the_def])>>
    qmatch_goalsub_abbrev_tac`option_le sm2 _`>>
    `option_le sm2 sm1` by
      (fs[Abbr`sm1`,Abbr`sm2`]>>
      simp[wordPropsTheory.stack_size_eq]>>
      simp[option_le_max_right]>>
      metis_tac[option_add_comm,option_le_add])>>
    metis_tac[option_le_trans])
  \\ conj_tac >-
    (drule_then match_mp_tac option_le_trans >>
     rw[option_le_max]
     >- (drule_then match_mp_tac option_le_trans >>
         rw[size_of_stack_eq,option_le_max_right,option_le_max,option_map2_max_add,AC option_add_comm option_add_assoc,option_le_eq_eqns,option_map2_max_add,stack_size_eq,option_le_add]
        ) >>
     imp_res_tac stack_rel_IMP_size_of_stack >>
     rw[size_of_stack_eq,option_le_max_right,option_le_max,option_map2_max_add,AC option_add_comm option_add_assoc,option_le_eq_eqns,option_map2_max_add,stack_size_eq,option_le_add])
  \\ conj_tac >- fs [limits_inv_def, FLOOKUP_UPDATE]
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
  >- fs [Abbr`init_ptr2`, get_lowerbits_def, make_header_def, encode_header_def]
  \\ strip_tac
  \\ drule (GEN_ALL memory_rel_less_space)
  \\ disch_then (qspec_then `0` mp_tac) \\ fs []
  \\ fs [join_env_def]
  \\ match_mp_tac memory_rel_rearrange
  \\ fs [] \\ rpt strip_tac \\ fs []
  >- fs [Abbr`init_ptr2`, get_lowerbits_def]
  \\ ntac 3 disj2_tac
  \\ disj1_tac
  \\ pop_assum mp_tac
  \\ fs [inter_union_distrib]
  \\ ‘inter (fromAList l') (adjust_set x) = LN’ by
   (DEP_REWRITE_TAC [spt_eq_thm]
    \\ simp [lookup_def,lookup_inter_alt,AllCaseEqs()]
    \\ qx_gen_tac ‘nn’
    \\ Cases_on ‘nn ∈ domain (adjust_set x)’ \\ simp []
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

Theorem do_app_AllocThunk:
   do_app (ThunkOp (AllocThunk m)) [v] x =
    case consume_space (1 + 1) x of
      NONE => Rerr (Rabort Rtype_error)
    | SOME s1 =>
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
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  \\ fs [assign_def] \\ fs [do_app_AllocThunk] \\ fs[do_app]
  \\ Cases_on `consume_space (LENGTH vals + 1) x` \\ fs [] \\ rveq
  \\ Cases_on `vals` \\ gvs []
  \\ Cases_on `t'` \\ gvs []
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
  \\ qabbrev_tac `new = LEAST ptr. ptr ∉ domain x.refs`
  \\ `new ∉ domain x.refs` by metis_tac [LEAST_NOTIN_spt_DOMAIN]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 memory_rel_AllocThunk \\ strip_tac
  \\ fs [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.set_store_def,FLOOKUP_UPDATE]
  \\ qpat_abbrev_tac `t5 = t with <| locals := _ ; store := _ |>`
  \\ pairarg_tac \\ fs []
  \\ `t.memory = t5.memory /\ t.mdomain = t5.mdomain` by
       (unabbrev_all_tac \\ fs []) \\ fs []
  \\ ntac 2 (pop_assum kall_tac)
  \\ drule0 evaluate_StoreEach
  \\ disch_then (qspecl_then [`[3; adjust_var h'']`,`1`] mp_tac)
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
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
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
    \\ `word_exp t (real_addr c (adjust_var h)) = SOME (Word x')` by
          metis_tac [get_real_offset_lemma,get_real_addr_lemma]
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
  \\ strip_tac \\ clean_tac
  \\ `word_exp t (real_addr c (adjust_var h)) = SOME (Word x'')` by
        metis_tac [get_real_offset_lemma,get_real_addr_lemma]
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

Theorem assign_ConfigGC:
   op = MemOp ConfigGC ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ asm_rewrite_tac [] \\ pop_assum kall_tac
  \\ imp_res_tac state_rel_cut_IMP \\ pop_assum mp_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs [do_app,allowed_op_def,AllCaseEqs()] \\ gvs []
  \\ drule_all state_rel_get_vars_IMP
  \\ strip_tac
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ fs[assign_def,EVAL ``op_requires_names (MemOp ConfigGC)``]
  \\ fs [list_Seq_def,eq_eval]
  \\ gvs [data_to_word_gcProofTheory.alloc_locals_insert_1]
  \\ reverse (Cases_on `c.call_empty_ffi`)
  THEN1
   (fs [SilentFFI_def,wordSemTheory.evaluate_def]
    \\ gvs [CaseEq"option"]
    \\ qpat_abbrev_tac `alll = alloc _ _ _`
    \\ `?x1 x2. alll = (x1,x2)` by (Cases_on `alll` \\ fs [])
    \\ unabbrev_all_tac \\ fs []
    \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` assume_tac
    \\ Cases_on `names_opt`
    \\ fs [cut_state_opt_def,cut_state_def] \\ rveq \\ fs []
    \\ gvs [CaseEq"option"]
    \\ rpt_drule0 (alloc_lemma |> Q.INST [`k`|->`0`])
    \\ fs [EVAL ``alloc_size 0``,get_names_def]
    \\ strip_tac \\ Cases_on `x1 = SOME NotEnoughSpace` \\ fs []
    >- (rw[option_le_max_right] >> res_tac >>
        simp[space_consumed_def] >> rfs[cut_locals_def] >>
        simp[NOT_LESS_EQUAL])
    \\ fs [state_rel_thm,set_var_def]
    \\ fs [lookup_insert,adjust_var_11,option_le_max_right]
    \\ strip_tac \\ rw [option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert
    \\ fs [] \\ match_mp_tac memory_rel_Unit \\ fs [])
  \\ fs [SilentFFI_def,wordSemTheory.evaluate_def,eq_eval]
  \\ ‘∃nf cu hl.
        FLOOKUP t.store NextFree = SOME (Word nf) ∧
        FLOOKUP t.store CurrHeap = SOME (Word cu) ∧
        FLOOKUP t.store HeapLength = SOME (Word hl)’ by
           fs [state_rel_thm,memory_rel_def,heap_in_memory_store_def]
  \\ fs [wordSemTheory.evaluate_def,SilentFFI_def,wordSemTheory.word_exp_def,
         wordSemTheory.set_var_def,EVAL ``read_bytearray a 0 m``,
         ffiTheory.call_FFI_def,EVAL ``write_bytearray a [] m dm b``,
         wordSemTheory.get_var_def,lookup_insert,list_Seq_def,
         wordSemTheory.the_words_def,wordLangTheory.word_op_def,
         cut_env_adjust_sets_insert_ODD,wordSemTheory.get_store_def]
  \\ Cases_on `names_opt`
  \\ fs [cut_state_opt_def,cut_state_def] \\ rveq \\ fs []
  \\ gvs [CaseEq"option"]
  \\ fs [get_names_def]
  \\ fs [cut_names_adjust_set_insert_3]
  \\ drule0 (GEN_ALL cut_env_IMP_cut_env) \\ fs []
  \\ `dataSem$cut_env x' env = SOME env` by
    (fs [dataSemTheory.cut_env_def] \\ rveq \\ fs[domain_inter,lookup_inter_alt])
  \\ disch_then drule0 \\ strip_tac \\ fs []
  \\ qpat_abbrev_tac `alll = alloc _ _ _`
  \\ `?x1 x2. alll = (x1,x2)` by (Cases_on `alll` \\ fs [])
  \\ unabbrev_all_tac \\ fs []
  \\ drule0 (GEN_ALL state_rel_cut_env_cut_env)
  \\ fs []
  \\ disch_then drule0
  \\ disch_then drule0
  \\ strip_tac
  \\ rpt_drule0 (alloc_lemma |> Q.INST [`k`|->`0`]) \\ fs []
  \\ disch_then drule0
  \\ rename [‘alloc _ (adjust_sets x8)’]
  \\ ‘alloc (alloc_size 0) (adjust_sets x8) (t with locals := y) = (x1,x2)’ by
      (qpat_x_assum ‘_ = (x1,x2)’ (rewrite_tac o single o GSYM)
       \\ simp [EVAL “alloc_size 0”] \\ AP_TERM_TAC
       \\ gvs [wordSemTheory.state_component_equality])
  \\ fs [] \\ fs [EVAL ``alloc_size 0``,ZERO_LT_dimword]
  \\ strip_tac
  \\ Cases_on `x1 = SOME NotEnoughSpace` \\ fs []
  >- (rw[option_le_max_right] >> res_tac >>
      simp[space_consumed_def] >> rfs[cut_locals_def] >>
      simp[NOT_LESS_EQUAL])
  \\ ‘∃nf cu hl.
        FLOOKUP x2.store NextFree = SOME (Word nf) ∧
        FLOOKUP x2.store CurrHeap = SOME (Word cu) ∧
        FLOOKUP x2.store HeapLength = SOME (Word hl)’ by
           fs [state_rel_thm,memory_rel_def,heap_in_memory_store_def]
  \\ fs [wordSemTheory.evaluate_def,SilentFFI_def,wordSemTheory.word_exp_def,
         wordSemTheory.set_var_def,EVAL ``read_bytearray a 0 m``,
         ffiTheory.call_FFI_def,EVAL ``write_bytearray a [] m dm b``,
         wordSemTheory.get_var_def,lookup_insert,list_Seq_def,
         wordSemTheory.the_words_def,wordLangTheory.word_op_def,
         cut_env_adjust_sets_insert_ODD,wordSemTheory.get_store_def]
  \\ rveq \\ fs []
  \\ drule cut_env_IMP_cut_env \\ simp []
  \\ ‘dataSem$cut_env x8 env = SOME env’ by
    gvs [dataSemTheory.cut_env_def,AllCaseEqs()]
  \\ disch_then drule
  \\ strip_tac \\ gvs []
  \\ drule state_rel_cut_env_cut_env \\ gvs []
  \\ disch_then drule_all
  \\ strip_tac
  \\ fs [state_rel_thm,set_var_def]
  \\ fs [lookup_insert,adjust_var_11,option_le_max_right]
  \\ conj_tac >- (rw [] \\ gvs [])
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert
  \\ fs [] \\ match_mp_tac memory_rel_Unit \\ fs []
QED

Theorem assign_WordToInt:
   op = WordOp WordToInt ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ asm_rewrite_tac [] \\ pop_assum kall_tac
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app,oneline do_word_app_def,allowed_op_def]
  \\ gvs [AllCaseEqs()]
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
      \\ `sn = Smallnum i ∧ small_int (:α) i` suffices_by (
        rw[]
        \\ match_mp_tac IMP_memory_rel_Number
        \\ simp[]
        \\ match_mp_tac (GEN_ALL memory_rel_less_space)
        \\ qexists_tac`x.space` \\ fs[] )
      \\ simp[Abbr`sn`,Abbr`i`]
      \\ fs [Smallnum_def]
      \\ rename [‘(31 >< 0) ccc ≪ 2 = _’]
      \\ Cases_on `ccc` \\ fs []
      \\ fs [word_extract_n2w,WORD_MUL_LSL,word_mul_n2w,
             bitTheory.BITS_THM2,dimword_def] \\ rfs []
      \\ fs [DIV_MOD_MOD_DIV]
      \\ fs [DIV_EQ_X] \\ rfs []
      \\ `w2n (n2w n ⋙ 29) = w2n 0w` by fs []
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
        \\ `w2n (n2w n ⋙ 29) <> w2n 0w` by fs []
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
      \\ qexists_tac `x.space − 2` \\ fs []
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
    \\ `sn = Smallnum i ∧ small_int (:α) i` suffices_by (
      rw[]
      \\ match_mp_tac IMP_memory_rel_Number
      \\ simp[]
      \\ match_mp_tac (GEN_ALL memory_rel_less_space)
      \\ qexists_tac`x.space` \\ fs[] )
    \\ simp[Abbr`sn`,Abbr`i`]
    \\ rename [‘w2w ccc ⋙ 61 = 0w’]
    \\ reverse conj_tac
    >- (`ccc >>> 61 = 0w`
        by (qpat_x_assum `w2w c' >>> 61 = 0w` mp_tac
            \\ srw_tac[wordsLib.WORD_BIT_EQ_ss][])
        \\ simp[small_int_def,wordsTheory.dimword_def]
        \\ wordsLib.n2w_INTRO_TAC 64
        \\ qpat_x_assum `ccc >>> 61 = 0w` mp_tac
        \\ blastLib.BBLAST_TAC)
    \\ simp_tac(std_ss++wordsLib.WORD_MUL_LSL_ss)
         [Smallnum_i2w,GSYM integerTheory.INT_MUL,
          integer_wordTheory.i2w_w2n_w2w,GSYM integer_wordTheory.word_i2w_mul,
          EVAL ``i2w 4 : 'a word``])
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
  \\ qexists_tac`x.space - 2` \\ fs[]
  \\ qmatch_goalsub_abbrev_tac`Number w1`
  \\ qmatch_asmsub_abbrev_tac`Number w2`
  \\ `w1 = w2` suffices_by simp[]
  \\ simp[Abbr`w1`,Abbr`w2`]
  \\ simp[w2n_w2w]
QED

Theorem push_env_tstamps:
  ∀x t s. (push_env x t s).tstamps = s.tstamps
Proof
  rw [push_env_def] \\ Cases_on `t` \\ rw [push_env_def]
QED

Theorem dec_clock_tstamps:
  ∀s. (dec_clock s).tstamps = s.tstamps
Proof
 rw [dataSemTheory.dec_clock_def]
QED

Theorem FromList1_code_thm:
   !k a b r x m1 a1 a2 a3 a4 a5 a6.
      lookup FromList1_location r.code = SOME (6,FromList1_code c) /\
      copy_list c r.store k (a,x,b,(r:('a,'c,'ffi) wordSem$state).memory,
        r.mdomain) = SOME (b1,m1) /\
      shift_length c < dimindex (:'a) /\ good_dimindex (:'a) /\
      get_var a1 r = SOME (Loc l1 l2) /\
      get_var a2 r = SOME (Word (b:'a word)) /\
      get_var a3 r = SOME a /\
      get_var a4 r = SOME (Word (n2w (4 * k))) /\
      get_var a5 r = SOME ret_val /\
      get_var a6 r = SOME x /\
      4 * k < dimword (:'a) /\
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
   state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) [] locs /\
    encode_header c (4 * tag) 0 <> (NONE:'a word option) /\
    get_vars [0; 1; 2] s.locals = SOME [v1; v2; Number (&(4 * tag))] /\
    t.clock = MustTerminate_limit (:'a) - 1 /\
    pop_env s = SOME s1 /\ is_env(HD s.stack) /\
    MEM v2 (toListA [] s1.locals) /\
    s.locals_size = lookup FromList_location s.stack_frame_sizes /\
    do_app (BlockOp (FromList tag)) [v1; v2] s1 = Rval (v,s2) ==>
    ?q r new_c.
      evaluate (FromList_code c,t) = (q,r) /\
      if q = SOME NotEnoughSpace then
        r.ffi = t.ffi /\
        option_le r.stack_max s2.stack_max /\
        (c.gc_kind <> None ==>
         (case (v1,v2) of
           (Number n,_) => ~small_num s.limits.arch_64_bit n \/
                           ~(Num n < dimword (:α) DIV 16) \/
                           ~(Num n < 2 ** c.len_size) \/
                           (s1.limits.heap_limit <
                             size_of_heap s1 + Num n + 1)
         ))
      else
        ?rv. q = SOME (Result (Loc l1 l2) [rv]) /\
             state_rel c r1 r2 (s2 with <| locals := LN;
                                           locals_size := SOME 0;
                                           clock := new_c;
                                           stack := s.stack|>)
                r [(v,rv)] locs
Proof
  fs [do_app_def,do_app_aux_def,do_space_def,
      dataLangTheory.op_space_reset_def]
  \\ Cases_on `v_to_list v2` \\ fs [with_fresh_ts_def]
  \\ reverse (Cases_on `v1 = Number (&LENGTH x)`)
  >- (Cases_on `x` \\ fs [])
  \\ fs [LENGTH_NIL] \\ strip_tac \\ rveq \\ fs [FromList_code_def]
  \\ once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ rpt_drule0 state_rel_get_vars_IMP
  \\ fs[wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def]
  \\ rpt_drule0 state_rel_get_vars_IMP \\ strip_tac \\ fs [LENGTH_EQ_3]
  \\ rveq \\ fs [adjust_var_def,get_vars_SOME_IFF,get_vars_SOME_IFF_data]
  \\ qpat_assum `get_var 0 s.locals = SOME (Number _)` assume_tac
  \\ rpt_drule0 state_rel_IMP_test_zero
  \\ fs [adjust_var_def] \\ strip_tac \\ fs [] \\ rveq
  \\ `small_int (:α) (&(4 * tag))` by (
    fs [encode_header_def,small_int_def,state_rel_thm,
        good_dimindex_def,dimword_def] \\ rfs [] \\ NO_TAC)
  \\ IF_CASES_TAC THEN1 (
    qpat_assum `get_var 2 s.locals = SOME (Number (&(4*tag)))` assume_tac
    \\ rpt_drule0 state_rel_get_var_Number_IMP \\ fs []
    \\ fs [LENGTH_NIL] \\ rveq \\ rw []
    \\ fs [list_Seq_def,wordSemTheory.evaluate_def,word_exp_rw,
           wordSemTheory.get_var_def,adjust_var_def,wordSemTheory.set_var_def,
           wordSemTheory.get_vars_def,wordSemTheory.flush_state_def]
    \\ rveq \\ fs [lookup_insert]
    \\ `lookup 0 t.locals = SOME (Loc l1 l2)` by fs [state_rel_def] \\ fs []
    \\ fs [state_rel_thm,wordSemTheory.call_env_def,lookup_def,with_fresh_ts_def]
    \\ reverse (Cases_on `s.tstamps`) \\ fs []
    \\ fs [] \\ rveq
    \\ fs [EVAL ``(toAList (inter (fromList2 []) (insert 0 () LN)))`` ]
    \\ fs [EVAL ``join_env LN []``,lookup_insert]
    \\ fs [BlockNil_def,Smallnum_def,WORD_MUL_LSL,word_mul_n2w]
    \\ `n2w (16 * tag) + 2w = BlockNil tag : 'a word` by
          fs [BlockNil_def,WORD_MUL_LSL,word_mul_n2w] \\ fs []
    \\ fs[pop_env_def,is_env_def,CaseEq "list",CaseEq"stack"]
    \\ rveq \\ fs[] \\ rfs[] \\ rveq
    \\ conj_tac >- metis_tac [option_le_add_indv]
    \\ conj_tac
    >- (fs [do_stack_def, stack_consumed_def, allowed_op_def,option_le_max_right])
    \\ match_mp_tac memory_rel_Cons_empty
    \\ fs [encode_header_def]
    \\ drule0 memory_rel_zero_space
    \\ match_mp_tac memory_rel_rearrange
    \\ fs [] \\ rw [] \\ fs [])
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw]
  \\ rpt_drule0 state_rel_get_vars_IMP \\ strip_tac \\ fs [LENGTH_EQ_2]
  \\ rveq \\ fs [adjust_var_def,get_vars_SOME_IFF]
  \\ fs [get_vars_SOME_IFF_data]
  \\ fs [GSYM wordSemTheory.get_var_def]
  \\ rpt_drule0 state_rel_get_var_Number_IMP_alt \\ fs []
  \\ strip_tac \\ rveq
  \\ fs [GSYM wordSemTheory.get_var_def]
  \\ rpt_drule0 evaluate_BignumHalt2
  \\ reverse(Cases_on `small_int (:α) (&(LENGTH x))`)
  >- (fs[] >> strip_tac >> fs[] >>
      conj_tac >-
        (fs[pop_env_def,is_env_def,CaseEq "list",CaseEq"stack",CaseEq"option",CaseEq"bool",check_lim_def,do_stack_def] >>
         rveq >> rfs[] >> fs[option_le_max_right,state_rel_def] >>
         metis_tac[option_le_trans]) >>
      fs[small_int_def,small_num_def,state_rel_def,limits_inv_def,good_dimindex_def,
         dimword_def] >> rfs[])
  \\ Cases_on `small_int (:α) (&(LENGTH x))` \\ fs [] \\ strip_tac \\ fs []
  \\ ntac 3 (pop_assum kall_tac)
  \\ fs []
  \\ ntac 2 (once_rewrite_tac [list_Seq_def])
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,wordSemTheory.get_var_def]
  \\ pairarg_tac \\ fs []
  \\ `state_rel c l1 l2 s (set_var 1 (Word w) t) [] locs` by
         fs [wordSemTheory.set_var_def,state_rel_insert_1]
  \\ rpt_drule0 AllocVar_thm
  \\ `?x. dataSem$cut_env (fromList [();();()]) s.locals = SOME x` by (
    fs [EVAL ``sptree$fromList [();();()]``,cut_env_def,domain_lookup,
              get_var_def,get_vars_SOME_IFF_data] \\ NO_TAC)
  \\ disch_then drule0
  \\ fs [get_var_set_var]
  \\ disch_then drule0
  \\ impl_tac THEN1 (unabbrev_all_tac \\ fs []
                     \\ fs [state_rel_def,EVAL ``good_dimindex (:'a)``,dimword_def])
  \\ strip_tac \\ fs []
  \\ reverse (Cases_on `res`) THEN1
    (fs [] >>
     conj_tac >-
        (fs[pop_env_def,is_env_def,CaseEq "list",CaseEq"stack",CaseEq"option",CaseEq"bool",check_lim_def,do_stack_def] >>
         rveq >> rfs[] >> fs[option_le_max_right,state_rel_def] >>
         metis_tac[option_le_trans]) >>
     strip_tac >> res_tac >>
     spose_not_then strip_assume_tac >>
     `w2n w = 4 * LENGTH x` by
       (qpat_assum `state_rel c l1 l2 s t [] locs` assume_tac
        \\ rpt_drule0 state_rel_get_var_Number_IMP
        \\ fs [adjust_var_def,wordSemTheory.get_var_def,small_num_def,Smallnum_def,
               state_rel_def,dimword_def,limits_inv_def,small_int_def,good_dimindex_def]
        \\ fs[]) >>
     fs[DIV_LT_X,intLib.COOPER_PROVE ``4 * k DIV 4 = k``] >>
     fs[pop_env_def,is_env_def,CaseEq "list",CaseEq"stack",CaseEq"option",CaseEq"bool",check_lim_def,do_stack_def] >>
     rveq >> rfs[] >> rveq >> rfs[] >>
     `size_of_heap (cut_locals (fromList [(); (); ()]) s) =
       size_of_heap
             (s with <|locals := e; locals_size := n; stack := xs|>)`
        by(fs[cut_locals_def,cut_env_def,size_of_heap_def,
              stack_to_vs_def,extract_stack_def
             ] >> rveq >>
           fs[fromList_def] >>
           rfs[] >>
           `inter s.locals (fromList [();();()]) =
            inter (insert 2 (THE(lookup 2 s.locals))
                   (insert 1 (THE(lookup 1 s.locals))
                    (insert 0 (THE(lookup 0 s.locals)) LN)))
                   (fromList [();();()])`
            by(fs[dataSemTheory.get_var_def] >>
               rw[inter_eq,lookup_inter,lookup_insert,lookup_fromList] >>
               fs[] >>
               fs[lookup_def] >> TOP_CASE_TAC >> rw[]) >>
           pop_assum(SUBST_ALL_TAC o SIMP_RULE list_ss [fromList_def]) >>
           rpt(CHANGED_TAC(simp[Once insert_def])) >>
           simp[inter_def,mk_BS_def,toList_def] >>
           fs[toList_def,toListA_def,dataSemTheory.get_var_def] >>
           `small_num s.limits.arch_64_bit (&(4 * tag))` by
             (fs[small_num_def,small_int_def,state_rel_def,limits_inv_def,
                 good_dimindex_def,dimword_def] >> rfs[] >> fs[]) >>
           `small_num s.limits.arch_64_bit (&SUC (LENGTH v7))` by
             (fs[small_num_def,small_int_def,state_rel_def,limits_inv_def,
                 good_dimindex_def,dimword_def] >> rfs[] >> fs[]) >>
           simp[size_of_Number_head] >>
           AP_TERM_TAC >>
           Cases_on `v2` >> TRY(fs[v_to_list_def]) >>
           match_mp_tac size_of_cons_seen_Block >>
           simp[]) >>
     metis_tac[NOT_LESS,LESS_EQ_ANTISYM]
    )
  \\ fs []
  \\ `?f cur. FLOOKUP s1'.store NextFree = SOME (Word f) /\
              FLOOKUP s1'.store CurrHeap = SOME (Word cur)` by
        (fs [state_rel_def,heap_in_memory_store_def] \\ NO_TAC)
  \\ ntac 5 (once_rewrite_tac [list_Seq_def])
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,lookup_insert,
         wordSemTheory.set_var_def]
  \\ qabbrev_tac `s0 = s with <|locals := x'; space := w2n w DIV 4 + 1|>`
  \\ `get_var 0 s0.locals = SOME (Number (&LENGTH x)) /\
      get_var 1 s0.locals = SOME v2 /\
      get_var 2 s0.locals = SOME (Number (&(4 * tag)))` by
   (unabbrev_all_tac \\ fs [get_var_def,cut_env_def]
    \\ rveq \\ fs [lookup_inter_alt] \\ EVAL_TAC \\ NO_TAC)
  \\ qpat_assum `get_var 1 s0.locals = SOME v2` assume_tac
  \\ rpt_drule0 state_rel_get_var_IMP \\ strip_tac
  \\ qpat_assum `get_var 2 s0.locals = SOME (Number (&(4 * tag)))` assume_tac
  \\ rpt_drule0 state_rel_get_var_Number_IMP \\ strip_tac \\ fs []
  \\ `small_int (:'a) (&LENGTH x)` by (fs [] \\ NO_TAC)
  \\ qpat_assum `get_var 0 s0.locals = SOME (Number (&LENGTH x))` assume_tac
  \\ rpt_drule0 state_rel_get_var_Number_IMP \\ strip_tac \\ fs []
  \\ fs [adjust_var_def] \\ fs [wordSemTheory.get_var_def]
  \\ qpat_assum `get_var 1 s0.locals = SOME v2` assume_tac
  \\ fs [lookup_insert]
  \\ `~(2 ≥ dimindex (:α)) /\ ~(4 ≥ dimindex (:α))` by
       (fs [state_rel_def,good_dimindex_def] \\ NO_TAC)
  \\ fs [lookup_insert]
  \\ assume_tac (GEN_ALL Make_ptr_bits_thm)
  \\ SEP_I_TAC "evaluate"
  \\ fs [wordSemTheory.set_var_def,lookup_insert] \\ rfs []
  \\ pop_assum (qspecl_then [`tag`,`LENGTH x`] mp_tac)
  \\ match_mp_tac (METIS_PROVE [] ``a /\ (a /\ b ==> c) ==> ((a ==> b) ==> c)``)
  \\ `16 * tag < dimword (:'a) /\ 4 * LENGTH x < dimword (:'a)` by
   (fs [encode_header_def,X_LT_DIV,small_int_def] \\ NO_TAC)
  \\ conj_tac THEN1
   (fs [Smallnum_def,shift_length_def]
    \\ rewrite_tac [GSYM w2n_11,w2n_lsr]
    \\ fs [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
    \\ fs [state_rel_def,heap_in_memory_store_def,shift_length_def])
  \\ strip_tac \\ fs []
  \\ `w2n w = 4 * LENGTH x` by
   (qpat_assum `state_rel c l1 l2 s t [] locs` assume_tac
    \\ rpt_drule0 state_rel_get_var_Number_IMP
    \\ fs [adjust_var_def,wordSemTheory.get_var_def,Smallnum_def] \\ NO_TAC)
  \\ fs [state_rel_thm,get_var_def]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [code_oracle_rel_def,FLOOKUP_UPDATE]
  \\ rpt_drule0 memory_rel_lookup \\ fs [adjust_var_def]
  \\ qabbrev_tac `hd = (Smallnum (&(4 * tag)) || (3w:'a word) ||
                       (Smallnum (&LENGTH x) << (dimindex (:α) − c.len_size - 2)))`
  \\ fs [list_Seq_def]
  \\ strip_tac \\ fs [LENGTH_NIL]
  \\ assume_tac (GEN_ALL FromList1_code_thm)
  \\ SEP_I_TAC "evaluate"
  \\ pop_assum mp_tac
  \\ fs [wordSemTheory.set_var_def,wordSemTheory.get_var_def,lookup_insert]
  \\ `lookup FromList1_location s1'.code = SOME (6,FromList1_code c)` by
       (fs [code_rel_def,stubs_def] \\ rfs [] \\ NO_TAC)
  \\ rfs []
  \\ disch_then (qspec_then `c` mp_tac)
  \\ `encode_header c (4 * tag) (LENGTH x) = SOME hd` by
   (fs [encode_header_def] \\ conj_tac THEN1
     (qpat_x_assum ‘LENGTH _ < dimword _ DIV 16’ mp_tac
      \\ qpat_x_assum ‘good_dimindex _’ mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ simp[dimword_def, good_dimindex_def, DISJ_IMP_THM, X_LT_DIV])
    \\ fs [make_header_def,Abbr`hd`]
    \\ fs [WORD_MUL_LSL,word_mul_n2w,Smallnum_def,EXP_LEMMA1]
    \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
    \\ fs [memory_rel_def,heap_in_memory_store_def]
    \\ fs [good_dimindex_def] \\ rfs [])
  \\ `LENGTH x < s0.space`
       by (fs [Abbr `s0`,SIMP_RULE std_ss [Once MULT_COMM] MULT_DIV])
  \\ rpt_drule0 memory_rel_FromList
  \\ Cases_on `x` \\  fs []
  \\ qabbrev_tac `x = h::t'`
  \\ `x ≠ []` by rw [Abbr `x`]
  \\ qpat_x_assum `Abbrev _` (K ALL_TAC)
  \\ Cases_on `s.tstamps` \\ fs []
  \\ fs [] \\ rveq
  \\ rename [`s.tstamps = SOME next_ts`]
  \\ strip_tac \\ fs []
  \\ disch_then drule
  \\ impl_tac THEN1
    (fs [Abbr `s0`,ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV,Smallnum_def])
  \\ strip_tac
  \\ fs [lookup_def,EVAL ``join_env LN []``]
  \\ fs [Abbr`s0`]
  \\ fs [FAPPLY_FUPDATE_THM,FLOOKUP_UPDATE]
  \\ rfs []
  \\ fs[pop_env_def,is_env_def,CaseEq "list",CaseEq"stack",CaseEq"option",CaseEq"bool",check_lim_def,do_stack_def]
  \\ rveq >> rfs[] >> rveq >> rfs[]
  \\ conj_tac >- (drule option_le_add_indv \\ rw [option_le_max_right])
  \\ conj_tac
  >- (imp_res_tac stack_rel_simp >>
      imp_res_tac stack_rel_IMP_size_of_stack >>
      fs[stack_size_eq,stack_consumed_def] >>
      simp[size_of_stack_eq,option_le_max_right,option_le_max,option_map2_max_add,AC option_add_comm option_add_assoc,option_le_eq_eqns,option_map2_max_add,stack_size_eq])
  \\ drule0 memory_rel_zero_space
  \\ match_mp_tac memory_rel_rearrange
  \\ fs [] \\ rw [] \\ fs []
QED

Theorem assign_FromList:
  (?tag. op = BlockOp (FromList tag)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ `option_le x.stack_max s2.stack_max` by
    metis_tac[do_app_stack_max]
  \\ asm_rewrite_tac [] \\ pop_assum kall_tac
  \\ rpt_drule0 state_rel_cut_IMP \\ strip_tac
  \\ fs [assign_def] \\ rveq
  \\ fs [dataLangTheory.op_requires_names_def,
         dataLangTheory.op_space_reset_def,cut_state_opt_def]
  \\ Cases_on `names_opt` \\ fs []
  \\ drule_all (state_rel_cut_state_opt_SOME |> SRULE [dataSemTheory.cut_state_opt_def])
  \\ strip_tac
  \\ qpat_x_assum ‘_ (t with locals := y) [] locs’ $ ASSUME_NAMED_TAC "with_locals"
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app,allowed_op_def]
  \\ `?v vs. vals = [Number (&LENGTH vs); v] /\ v_to_list v = SOME vs` by
         (every_case_tac \\ fs [] \\ rw [] \\ NO_TAC)
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ IF_CASES_TAC \\ fs []
  >- (conj_tac >-
       (fs[CaseEq "list",CaseEq"bool",state_rel_def,option_le_max_right,
           with_fresh_ts_def,ELIM_UNCURRY,CaseEq"option"] >>
        rveq >> fs[option_le_max_right,check_lim_def] >>
        metis_tac[option_le_trans]) >>
      strip_tac >> spose_not_then strip_assume_tac >>
      fs[CaseEq "list",CaseEq"bool",state_rel_def,option_le_max_right,
         with_fresh_ts_def,ELIM_UNCURRY,CaseEq"option"] >>
      rveq >> fs[option_le_max_right,check_lim_def,encode_header_def] >>
      fs[state_rel_def,arch_size_def,good_dimindex_def,limits_inv_def,dimword_def] >> rfs[])
  \\ clean_tac
  \\ drule0 lookup_RefByte_location \\ fs [get_names_def]
  \\ fs [wordSemTheory.evaluate_def,list_Seq_def,word_exp_rw,
         wordSemTheory.find_code_def,wordSemTheory.set_var_def]
  \\ fs [wordSemTheory.add_ret_loc_def,wordSemTheory.find_code_def]
  \\ fs [wordSemTheory.bad_dest_args_def,wordSemTheory.get_vars_def,
         wordSemTheory.get_var_def,lookup_insert]
  \\ disch_then kall_tac
  \\ fs [cut_state_opt_def,cut_state_def]
  \\ gvs [CaseEq"option"]
  (* x is now s1 *)
  \\ clean_tac \\ fs []
  \\ qabbrev_tac `s1 = s with locals := env`
  \\ rename [`cut_env (adjust_sets x') t.locals = SOME y`]
  \\ rename [‘get_vars [a1; a2] env = SOME [Number (&LENGTH vs); v']’]
  \\ imp_res_tac cut_env_IMP_cut_envs
  \\ fs[cut_envs_adjust_sets_ODD,domain_adjust_sets]
  \\ `dimword (:α) <> 0` by (assume_tac ZERO_LT_dimword \\ decide_tac)
  \\ fs [wordSemTheory.dec_clock_def]
  \\ Q.MATCH_GOALSUB_ABBREV_TAC `evaluate (FromList_code _,t4)`
  \\ rveq
  \\ `state_rel c l1 l2 (s1 with clock := MustTerminate_limit(:'a))
        (t with <| clock := MustTerminate_limit(:'a); termdep := t.termdep - 1 |>)
          [] locs` by
    (unabbrev_all_tac \\ fs [state_rel_def] \\ conj_tac >- metis_tac []
     \\ asm_exists_tac \\ fs [])
  \\ rpt_drule0 state_rel_call_env_push_env \\ fs []
  \\ `dataSem$get_vars [a1; a2] s.locals = SOME [Number (&LENGTH vs); v']` by
    (fs [dataSemTheory.get_vars_def] \\ every_case_tac \\ fs [cut_env_def]
     \\ clean_tac \\ fs [lookup_inter_alt,get_var_def] \\ NO_TAC)
  \\ `s1.locals = env` by (unabbrev_all_tac \\ fs []) \\ fs []
  \\ disch_then drule0 \\ fs []
  \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def]
  \\ `dataSem$cut_env x' s1.locals = SOME s1.locals` by
   (unabbrev_all_tac \\ fs []
    \\ fs [cut_env_def] \\ clean_tac
    \\ fs [domain_inter] \\ fs [lookup_inter_alt] \\ NO_TAC)
  \\ fs [] \\ rfs []
  \\ disch_then drule0 \\ fs []
  \\ disch_then (qspecl_then
       [`lookup FromList_location t.stack_size`, `n`,`l`,`NONE`] mp_tac) \\ fs []
  \\ strip_tac
  \\ `4 * tag < dimword (:'a) DIV 16` by (fs [encode_header_def] \\ NO_TAC)
  \\ rpt_drule0 state_rel_IMP_Number_arg
  \\ strip_tac
  \\ Cases_on `vs` \\ fs [with_fresh_ts_def]
  \\ `∃next_stamp. s.tstamps = SOME next_stamp` by (imp_res_tac state_rel_IMP_tstamps \\ fs [])
  \\ `s1.tstamps = s.tstamps` by rw [Abbr `s1`]
  \\ rpt_drule0 FromList_thm

  (* proof splits *)
  \\
    (simp [Once call_env_def,wordSemTheory.dec_clock_def,do_app_def,
           get_vars_def,get_var_def,lookup_insert,fromList_def,
           do_space_def,dataLangTheory.op_space_reset_def,
           call_env_def,do_app_aux_def,with_fresh_ts_def,
           is_env_def,dec_clock_tstamps,push_env_tstamps]
     \\ fs [check_lim_def, allowed_op_def] \\ rveq
     \\ disch_then
        (mp_tac o SIMP_RULE (srw_ss())
                [SimpL ``$==>``,push_env_def,pop_env_def,dataSemTheory.dec_clock_def,LET_THM])
     \\ simp[]
     \\ impl_tac
     >- (reverse conj_tac >- fs[state_rel_def] >>
         fs[GSYM toList_def,MEM_toList,get_vars_def,get_var_def,CaseEq"option"] >>
         goal_assum drule)
     \\ disch_then (qspecl_then [`l2`,`l1`] strip_assume_tac)
     \\ qmatch_assum_abbrev_tac
        `evaluate (FromList_code c,t5) = _`
     \\ `t5 = t4` by
       (unabbrev_all_tac \\
        fs [wordSemTheory.call_env_def,push_env_def,dataSemTheory.dec_clock_def,
            wordSemTheory.push_env_def,wordSemTheory.dec_clock_def,state_rel_def] \\
        pairarg_tac \\ fs [] \\ NO_TAC)
     \\ fs [] \\ Cases_on `q = SOME NotEnoughSpace` THEN1 (
      unabbrev_all_tac >> fs [allowed_op_def] >>
      conj_tac >-
       (fs[do_stack_def,size_of_stack_eq,stack_consumed_def] >>
        fs[size_of_stack_eq,option_le_max_right,option_le_max,option_map2_max_add,AC option_add_comm option_add_assoc,option_le_eq_eqns,option_map2_max_add,stack_size_eq] >>
        fs[state_rel_def] >>
        metis_tac[option_le_trans,option_map2_max_add,option_le_eq_eqns,option_le_add]
       ) >>
      strip_tac >> res_tac >>
      fs[push_env_def,dataSemTheory.dec_clock_def,space_consumed_def,
         size_of_heap_def,stack_to_vs_def] >>
      pop_assum (assume_tac o GSYM) >>
      fs[state_rel_def,limits_inv_def,arch_size_def,good_dimindex_def,dimword_def] >> rfs[]
      )
     \\ fs [state_fn_updates,wordSemTheory.set_var_def,set_var_def]
     \\ rpt_drule0 state_rel_pop_env_IMP
     \\ simp [push_env_def,call_env_def,pop_env_def,dataSemTheory.dec_clock_def]
     \\ strip_tac \\ fs [] \\ clean_tac
     \\ `domain t2.locals = domain y1 ∪ domain y2 ∧
        lookup 0 t2.locals = SOME (Loc l1 l2)` by
       (‘lookup 0 y1 = SOME (Loc l1 l2)’ by (drule state_rel_push_env_loc \\ simp [])
        \\ unabbrev_all_tac
        \\ rpt $ qpat_x_assum ‘state_rel c _ _ _ _ _ _’ kall_tac
        \\ drule_all evaluate_IMP_domain_union
        \\ simp_tac std_ss [])
     \\ fs [wordSemTheory.set_vars_def,alist_insert_def]
     \\ fs [do_stack_def]
     \\ qpat_x_assum ‘state_rel c _ _ _ _ _ _’ mp_tac
     \\ simp [state_rel_def]
     \\ fs [dataSemTheory.call_env_def,push_env_def,
            dataSemTheory.set_var_def,wordSemTheory.set_var_def]
     \\ strip_tac
     \\ fs [wordSemTheory.pop_env_def]
     \\ `t.clock = s.clock` by fs [state_rel_def] \\ fs []
     \\ unabbrev_all_tac \\ fs []
     \\ simp [lookup_insert]
     \\ conj_tac THEN1 (fs [lookup_insert,adjust_var_11] \\ rw [])
     \\ conj_tac
     >- (drule_then match_mp_tac option_le_trans \\
         fs[state_rel_def,stack_consumed_def,size_of_stack_eq,
            AC option_add_comm option_add_assoc] \\
         rw[size_of_stack_eq,option_le_max_right,option_le_max,option_map2_max_add,
            AC option_add_comm option_add_assoc,option_le_eq_eqns,
            option_map2_max_add,stack_size_eq,
            option_le_add,stack_consumed_def])
     \\ asm_exists_tac \\ fs []
     \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
     \\ match_mp_tac word_ml_inv_insert \\ fs [flat_def]
    )
QED

(* TODO: move to backendProps? *)
Theorem not_the_F_option_le:
  ~the F (OPTION_MAP ($> n) m) <=> option_le (SOME n) m
Proof
  Cases_on `m` >> rw[the_eqn]
QED

Theorem the_F_not_option_le:
  the F (OPTION_MAP ($> n) m) <=> ~option_le (SOME n) m
Proof
  Cases_on `m` >> rw[the_eqn]
QED

Theorem assign_RefByte:
  (?fl. op = MemOp (RefByte fl)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ `option_le x.stack_max s2.stack_max` by
    metis_tac[do_app_stack_max]
  \\ rpt_drule0 state_rel_cut_IMP \\ strip_tac
  \\ fs [assign_def] \\ rveq
  \\ fs [dataLangTheory.op_requires_names_def,
         dataLangTheory.op_space_reset_def,cut_state_opt_def]
  \\ Cases_on `names_opt` \\ fs []
  \\ qmatch_goalsub_abbrev_tac`Const tag`
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app, allowed_op_def]
  \\ `?i b. vals = [Number i; Number b]` by (every_case_tac \\ fs [] \\ NO_TAC)
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ Cases_on `0 <= i` \\ fs []
  \\ qpat_assum `_ = Rval (v,s2)` mp_tac
  \\ reverse IF_CASES_TAC >- fs [] \\ fs []
  \\ clean_tac \\ fs [wordSemTheory.evaluate_def]
  \\ simp[word_exp_rw,wordSemTheory.set_var_def,wordSemTheory.get_vars_def,
          wordSemTheory.get_var_def,domain_adjust_sets]
  \\ fs [wordSemTheory.bad_dest_args_def]
  \\ fs [wordSemTheory.add_ret_loc_def,wordSemTheory.find_code_def]
  \\ drule0 lookup_RefByte_location \\ fs [get_names_def,cut_envs_adjust_sets_ODD]
  \\ disch_then kall_tac
  \\ fs[get_vars_SOME_IFF]
  \\ simp[wordSemTheory.get_vars_def]
  \\ fs[wordSemTheory.get_var_def,lookup_insert]
  \\ fs [cut_state_opt_def,cut_state_def]
  (* x is now s1 *)
  \\ rename1 `state_rel c l1 l2 s1 t [] locs`
  \\ Cases_on `dataSem$cut_env x' s.locals` \\ fs []
  \\ clean_tac \\ fs []
  \\ qabbrev_tac `s1 = s with locals := x`
  \\ `?y. cut_env (adjust_sets x') t.locals = SOME y` by
       (match_mp_tac (GEN_ALL cut_env_IMP_cut_env) \\ fs []
        \\ metis_tac []) \\ fs []
  \\ drule cut_env_IMP_cut_envs \\ strip_tac
  \\ simp[]
  \\ `dimword (:α) <> 0` by (assume_tac ZERO_LT_dimword \\ decide_tac)
  \\ fs [wordSemTheory.dec_clock_def]
  \\ qmatch_goalsub_abbrev_tac `RefByte_code c,t4`
  \\ rename1 `lookup (adjust_var a1) _ = SOME w1`
  \\ rename1 `lookup (adjust_var a2) _ = SOME w2`
  \\ rename1 `get_vars [a1; a2] x = SOME [Number i; Number (&w2n w)]`
  \\ `state_rel c l1 l2 (s1 with clock := MustTerminate_limit(:'a))
        (t with <| clock := MustTerminate_limit(:'a); termdep := t.termdep - 1 |>) [] locs` by (
   unabbrev_all_tac \\ fs [state_rel_def] \\ conj_tac >- metis_tac [] \\
   asm_exists_tac \\ fs [] \\ NO_TAC)
  \\ rpt_drule0 state_rel_call_env_push_env \\ fs []
  \\ `get_vars [a1; a2] s.locals = SOME [Number i; Number (&w2n w)]` by
    (fs [dataSemTheory.get_vars_def] \\ every_case_tac \\ fs [cut_env_def]
     \\ clean_tac \\ fs [lookup_inter_alt,get_var_def] \\ NO_TAC)
  \\ `s1.locals = x` by (unabbrev_all_tac \\ fs []) \\ fs []
  \\ disch_then drule0 \\ fs []
  \\ simp[wordSemTheory.get_vars_def,wordSemTheory.get_var_def]
  \\ `dataSem$cut_env x' x = SOME x` by
   (unabbrev_all_tac \\ fs []
    \\ fs [cut_env_def] \\ clean_tac
    \\ fs [domain_inter] \\ fs [lookup_inter_alt])
  \\ disch_then drule0 \\ fs []
  \\ disch_then (qspecl_then [`lookup RefByte_location t.stack_size`, `n`,`l`,`NONE`] mp_tac)
  \\ fs []
  \\ strip_tac
  \\ `w2n (tag) DIV 4 < dimword (:'a) DIV 16`
  by (fs[Abbr`tag`,good_dimindex_def,state_rel_def] \\ rw[dimword_def] )
  \\ rpt_drule0 state_rel_IMP_Number_arg \\ strip_tac
  \\ rpt_drule0 RefByte_thm
  \\ simp [get_vars_def,call_env_def,get_var_def,lookup_fromList]
  \\ `w2n tag DIV 4 = if fl then 0 else 4`
  by (
    fs[Abbr`tag`] \\ rw[]
    \\ fs[state_rel_def,dimword_def,good_dimindex_def] )
  \\ `n2w (4 * if fl then 0 else 4) = tag`
  by (rw[Abbr`tag`] )
  \\ fs [do_app, allowed_op_def, check_lim_def] \\ rveq
  \\ fs [EVAL ``get_var 0 (call_env [x1;x2;x3] lsz y)``]
  \\ disch_then (mp_tac o CONV_RULE(RESORT_FORALL_CONV List.rev))
  \\ disch_then (qspecl_then [`fl`,`l2`,`l1`] mp_tac)
  \\ qmatch_goalsub_abbrev_tac `pop_env sx`
  \\ disch_then(qspec_then `THE(pop_env sx)` mp_tac)
  \\ impl_tac THEN1 (simp[Abbr `sx`,push_env_def,pop_env_def,dec_clock_def,is_env_def,
                          wordSemTheory.dec_clock_def,dataSemTheory.dec_clock_def] >>
                     fs[state_rel_def])
  \\ qpat_abbrev_tac `t5 = call_env [Loc n l; w1; w2; _] _ _`
  \\ `t5 = t4` by
   (unabbrev_all_tac \\ fs [wordSemTheory.call_env_def,
       wordSemTheory.push_env_def] \\ pairarg_tac \\ fs []
    \\ fs [wordSemTheory.env_to_list_def,wordSemTheory.dec_clock_def] \\
    fs[wordSemTheory.state_component_equality,push_env_def,dataSemTheory.dec_clock_def] \\
    fs[state_rel_def] \\ NO_TAC)
  \\ pop_assum (fn th => fs [th]) \\ strip_tac \\ fs []
  \\ Cases_on `q = SOME NotEnoughSpace` THEN1
   (unabbrev_all_tac >> fs [allowed_op_def] \\
    conj_tac >-
     (
      imp_res_tac evaluate_stack_max_le >>
      `s.stack_frame_sizes = t.stack_size` by fs[state_rel_def] >>
      `t.locals_size = s.locals_size` by fs[state_rel_def] >>
      `stack_size t.stack = size_of_stack s.stack`
        by (fs[state_rel_def] >> imp_res_tac stack_rel_IMP_size_of_stack) >>
      fs [wordSemTheory.call_env_def,wordSemTheory.push_env_def,ELIM_UNCURRY,stack_size_eq,
         option_le_max,option_le_max_right,push_env_def,size_of_stack_eq,dataSemTheory.dec_clock_def,
         AC option_add_comm option_add_assoc,option_map2_max_add,option_le_eq_eqns,option_le_add,
         call_env_def,push_env_def,dec_clock_def,pop_env_def] >>
      metis_tac[option_le_trans,option_le_eq_eqns,option_le_add]) >>
    strip_tac >> spose_not_then strip_assume_tac >>
    res_tac >>
    fs[space_consumed_def,dataSemTheory.pop_env_def,dataSemTheory.push_env_def,
       dataSemTheory.dec_clock_def,the_F_not_option_le]
   >- (qpat_assum `i < 0` mp_tac >> qpat_assum `0 <= i` mp_tac >>
       rpt(pop_assum kall_tac) >> intLib.COOPER_TAC)
   >- (fs[state_rel_def,dimword_def,good_dimindex_def,limits_inv_def,arch_size_def] >>
       rfs[])
   >- (rfs[state_rel_def,limits_inv_def])
   >> fs[size_of_heap_def,stack_to_vs_def,ELIM_UNCURRY]
   )
  \\ fs [state_fn_updates]
  \\ rpt_drule0 state_rel_pop_env_IMP
  \\ simp [push_env_def,call_env_def,pop_env_def,dataSemTheory.dec_clock_def]
  \\ strip_tac \\ fs [] \\ clean_tac
  \\ `domain t2.locals = domain y1 ∪ domain y2 ∧
      lookup 0 t2.locals = SOME (Loc l1 l2)` by
   (‘lookup 0 y1 = SOME (Loc l1 l2)’ by (drule state_rel_push_env_loc \\ simp [])
    \\ unabbrev_all_tac
    \\ rpt $ qpat_x_assum ‘state_rel c _ _ _ _ _ _’ kall_tac
    \\ drule_all evaluate_IMP_domain_union
    \\ simp_tac std_ss [])
  \\ fs []
  \\ fs [do_stack_def]
  \\ pop_assum mp_tac
  \\ pop_assum mp_tac
  \\ simp [state_rel_def]
  \\ fs [dataSemTheory.call_env_def,push_env_def,wordSemTheory.set_vars_def,
         dataSemTheory.set_var_def,wordSemTheory.set_var_def,alist_insert_def]
  \\ fs [wordSemTheory.pop_env_def]
  \\ `t.clock = s.clock` by fs [state_rel_def] \\ fs []
  \\ unabbrev_all_tac
  \\ fs [dataSemTheory.call_env_def,push_env_def,pop_env_def,dataSemTheory.dec_clock_def,
         dataSemTheory.set_var_def,wordSemTheory.set_var_def,size_of_stack_eq]
  \\ rpt (disch_then strip_assume_tac) \\ clean_tac \\ fs []
  \\ fs [state_rel_def,lookup_insert]
  \\ conj_tac THEN1 (fs [lookup_insert,adjust_var_11] \\ rw [])
  \\ conj_tac >-
      (drule_then match_mp_tac option_le_trans >>
       imp_res_tac stack_rel_IMP_size_of_stack >>
       rw[size_of_stack_eq,option_le_max_right,option_le_max,option_map2_max_add,
          AC option_add_comm option_add_assoc,option_le_eq_eqns,option_map2_max_add,
          stack_size_eq,option_le_add,option_le_refl] >>
       fs[state_rel_def,option_le_refl])
  \\ asm_exists_tac \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac word_ml_inv_insert \\ fs [flat_def]
QED

Theorem lookup_set_var:
  lookup x ((set_var x y z).locals) = SOME y
Proof
  rw[wordSemTheory.set_var_def,lookup_insert]
QED

Theorem lookup_2_call_env[local]:
  lookup 0 ((call_env (x::ts) a1 a2).locals) = SOME x ∧
  lookup 2 ((call_env (x::y::ts) a1 a2).locals) = SOME y ∧
  lookup 4 ((call_env (x::y::z::ts) a1 a2).locals) = SOME z
Proof
  gvs [wordSemTheory.call_env_def,lookup_fromList2,lookup_fromList]
QED

Theorem assign_RefArray:
  op = MemOp RefArray ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ `option_le x.stack_max s2.stack_max` by
    metis_tac[do_app_stack_max]
  \\ rpt_drule0 state_rel_cut_IMP \\ strip_tac
  \\ fs [assign_def] \\ rveq
  \\ fs [dataLangTheory.op_requires_names_def,
         dataLangTheory.op_space_reset_def,cut_state_opt_def]
  \\ Cases_on `names_opt` \\ fs []
  \\ drule_all (state_rel_cut_state_opt_SOME |> SRULE [cut_state_opt_def])
  \\ strip_tac
  \\ qpat_x_assum ‘_ (t with locals := y) [] locs’ $ ASSUME_NAMED_TAC "with_locals"
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app, allowed_op_def]
  \\ `?i w. vals = [Number i; w]` by (every_case_tac \\ fs [] \\ NO_TAC)
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ Cases_on `0 <= i` \\ fs []
  \\ drule0 NONNEG_INT \\ strip_tac \\ rveq \\ fs []
  \\ rename1 `&i`
  \\ simp[Once list_Seq_def]
  \\ simp[Once wordSemTheory.evaluate_def]
  \\ rveq \\ fs [adjust_var_def,get_vars_SOME_IFF]
  \\ fs [get_vars_SOME_IFF_data]
  \\ drule_all state_rel_get_var_Number_IMP_alt
  \\ strip_tac \\ rveq
  \\ drule_then drule evaluate_BignumHalt2
  \\ reverse(Cases_on `small_int (:α) (&i)`) \\ fs [] \\ strip_tac \\ fs []
  >- (conj_tac >-
       (fs[state_rel_def,option_le_max_right] >> metis_tac[option_le_trans]) >>
      fs[small_int_def,state_rel_def,dimword_def,arch_size_def,
         limits_inv_def,good_dimindex_def] >> rfs[])
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw]
  \\ fs [wordSemTheory.get_var_def,wordSemTheory.get_vars_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw]
  \\ fs [wordSemTheory.get_var_def]
  \\ `w' = n2w (4 * i) /\ 4 * i < dimword (:'a)` by
   (fs [state_rel_def,get_vars_SOME_IFF_data]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,get_var_def]
    \\ rpt_drule0 word_ml_inv_get_var_IMP
    \\ fs [get_var_def,wordSemTheory.get_var_def,adjust_var_def]
    \\ qpat_assum `lookup _ x.locals = SOME (Number (&i))` assume_tac
    \\ rpt (disch_then drule0) \\ fs []
    \\ fs [word_ml_inv_def] \\ rw []
    \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def] \\ rfs []
    \\ rw [] \\ fs [word_addr_def,Smallnum_def] \\ rw []
    \\ fs [small_int_def,X_LT_DIV]
    \\ match_mp_tac minus_2_word_and_id
    \\ fs [word_index,word_mul_n2w,bitTheory.BIT0_ODD,ODD_MULT] \\ NO_TAC)
  \\ rveq \\ fs []
  \\ `2 < dimindex (:α)` by
       (fs [state_rel_def,EVAL ``good_dimindex (:α)``] \\ NO_TAC) \\ fs []
  \\ `state_rel c l1 l2 x (set_var 1 (Word (n2w (4 * i))) t) [] locs` by
        fs [wordSemTheory.set_var_def,state_rel_insert_1]
  \\ `dataSem$cut_env x' x.locals = SOME x.locals`
    by(fs[cut_state_def,wordSemTheory.cut_env_def,CaseEq"option",
          cut_env_def] >> rveq >> fs[domain_inter] >>
       fs[GSYM lookup_inter_assoc] >>
       rw[lookup_inter_alt,domain_inter])
  \\ rpt_drule0 AllocVar_thm
  \\ qabbrev_tac `limit = MIN (2 ** c.len_size) (dimword (:α) DIV 16)`
  \\ fs [get_var_set_var_thm]
  \\ Cases_on `evaluate
       (AllocVar c limit x',set_var 1 (Word (n2w (4 * i))) t)`
  \\ fs []
  \\ disch_then drule
  \\ impl_tac THEN1 (unabbrev_all_tac \\ fs []
                     \\ fs [state_rel_def,EVAL ``good_dimindex (:'a)``,dimword_def])
  \\ strip_tac \\ fs [set_vars_sing]
  \\ fs[get_names_def]
  \\ rename [‘list_insert [a1; a2]’]
  \\ `list_insert [a1; a2] x' = x'`
     by (rw[list_insert_def] >> fs[get_var_def] >>
        `insert a1 () x' = x'`
          by(match_mp_tac lookup_IMP_insert_EQ >>
             fs[cut_state_def,cut_env_def,CaseEq"option",dataSemTheory.get_var_def] >>
             rveq >> fs[lookup_inter,CaseEq"option"]) >>
        pop_assum SUBST_ALL_TAC >>
        match_mp_tac lookup_IMP_insert_EQ >>
        fs[cut_state_def,cut_env_def,CaseEq"option",dataSemTheory.get_var_def] >>
        rveq >> fs[lookup_inter,CaseEq"option"])
  \\ pop_assum SUBST_ALL_TAC \\ fs[]
  \\ reverse IF_CASES_TAC \\ fs []
  >- (simp[do_stack_def,option_le_max_right] >>
      strip_tac >>
      spose_not_then strip_assume_tac >>
      fs[] >> qpat_x_assum `_ < limit ==> _` mp_tac >>
      impl_tac >- (fs[Abbr `limit`,intLib.COOPER_PROVE ``4 * k DIV 4 = k``,
                      small_int_def] >>
                   fs[good_dimindex_def,dimword_def,state_rel_def,arch_size_def,
                      limits_inv_def] >> rfs[]) >>
      fs[intLib.COOPER_PROVE ``4 * k DIV 4 = k``] >>
      fs[cut_locals_def,CaseEq"option",space_consumed_def] >>
      qsuff_tac `x with locals := x.locals = x` >>
      rw[] >> rw[dataSemTheory.state_component_equality])
  \\ rveq \\ fs []
  \\ simp[list_Seq_def]
  \\ clean_tac \\ fs [wordSemTheory.evaluate_def]
  \\ fs [wordSemTheory.bad_dest_args_def]
  \\ fs [wordSemTheory.add_ret_loc_def,wordSemTheory.find_code_def]
  \\ drule0 lookup_RefByte_location \\ fs [get_names_def]
  \\ disch_then kall_tac
  \\ fs [cut_state_opt_def,cut_state_def]
  \\ `r''.termdep = t.termdep` by
   (imp_res_tac wordSemTheory.evaluate_clock \\ fs [wordSemTheory.set_var_def])
  \\ fs[]
  \\ fs[wordSemTheory.get_vars_def,wordSemTheory.get_var_def,domain_adjust_sets]
  \\ drule state_rel_get_var_IMP
  \\ simp[]
  \\ disch_then imp_res_tac
  \\ fs[adjust_var_def]
  \\ drule state_rel_get_var_Number_IMP
  \\ simp[]
  \\ disch_then drule
  \\ disch_then drule
  \\ strip_tac
  \\ fs[adjust_var_def,wordSemTheory.get_var_def] >> rveq
  \\ drule (state_rel_cut_state_opt_SOME |> SRULE [cut_state_opt_def])
  \\ qabbrev_tac ‘s6 = x with <|locals := x.locals; space := 4 * i DIV 4 + 1|>’
  \\ ‘cut_state x' s6 = SOME s6’ by gvs [Abbr‘s6’,cut_state_def]
  \\ disch_then $ drule_at $ Pos last
  \\ disch_then $ qspecl_then [‘[]’,‘[]’] mp_tac
  \\ impl_tac >- EVAL_TAC
  \\ strip_tac \\ gvs []
  \\ drule cut_env_IMP_cut_envs \\ strip_tac \\ simp []
  \\ fs [RefArray_code_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw]
  \\ once_rewrite_tac [list_Seq_def]
  \\ gvs [lookup_2_call_env]
  \\ fs[lookup_fromList2,lookup_fromList]
  \\ fs[word_exp_rw,wordSemTheory.get_var_def]
  \\ IF_CASES_TAC
  THEN1 (fs [shift_def,state_rel_def,EVAL ``good_dimindex (:'a)``])
  \\ pop_assum kall_tac
  \\ fs[]
  \\ once_rewrite_tac [list_Seq_def]
  \\ once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ fs[wordSemTheory.dec_clock_def]
  (* \\ Cases_on `env_to_list y2 r''.permute`
  \\ fs[] *)
  \\ fs [word_exp_rw]
  \\ fs[EVAL ``(set_var x y z).store``]
  \\ `(?trig1. FLOOKUP r''.store TriggerGC = SOME (Word trig1)) /\
      (?eoh1. FLOOKUP r''.store EndOfHeap = SOME (Word eoh1)) /\
      (?cur1. FLOOKUP r''.store CurrHeap = SOME (Word cur1))` by
        (fs [state_rel_thm,memory_rel_def,heap_in_memory_store_def] \\ NO_TAC)
  \\ fs[lookup_set_var,wordSemTheory.set_store_def,FLOOKUP_SIMP,
        wordSemTheory.set_var_def]
  \\ simp[Once list_Seq_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ fs [word_exp_rw]
  \\ simp [wordSemTheory.set_var_def,lookup_insert,wordSemTheory.set_store_def]
  \\ fs[FLOOKUP_UPDATE,FAPPLY_FUPDATE_THM]
  \\ simp [wordSemTheory.evaluate_def,word_exp_rw,FLOOKUP_SIMP,
           wordSemTheory.set_var_def]
  \\ simp[Once list_Seq_def]
  \\ simp [wordSemTheory.evaluate_def,word_exp_rw,FLOOKUP_SIMP,
           wordSemTheory.set_var_def,wordSemTheory.set_store_def,lookup_insert,
           wordSemTheory.get_var_def,wordSemTheory.mem_store_def]
  \\ fs[lookup_set_var]
  \\ IF_CASES_TAC
  THEN1 (fs [shift_def,state_rel_def,EVAL ``good_dimindex (:'a)``])
  \\ pop_assum kall_tac
  \\ fs[]
  \\ fs [word_exp_rw,wordSemTheory.set_store_def,lookup_insert,
         wordSemTheory.get_var_def,wordSemTheory.mem_store_def,
         FLOOKUP_UPDATE,FAPPLY_FUPDATE_THM]
  \\ fs[wordSemTheory.set_var_def,lookup_insert]
  \\ fs[lookup_fromList2,lookup_fromList]
  \\ simp[Once list_Seq_def]
  \\ simp[Once list_Seq_def]
  \\ simp[wordSemTheory.evaluate_def]
  \\ fs [word_exp_rw,wordSemTheory.set_store_def,lookup_insert,
         wordSemTheory.get_var_def,wordSemTheory.mem_store_def,
         lookup_2_call_env,wordSemTheory.set_var_def]
  \\ `n2w (4 * i) ⋙ 2 = n2w i` by
   (once_rewrite_tac [GSYM w2n_11] \\ rewrite_tac [w2n_lsr]
    \\ fs [ONCE_REWRITE_RULE[MULT_COMM]MULT_DIV])
  \\ fs [WORD_LEFT_ADD_DISTRIB]
  \\ `good_dimindex(:'a)` by fs [state_rel_def]
  \\ fs [shift_lsl]
  \\ qhdtm_assum `state_rel` (strip_assume_tac o REWRITE_RULE[state_rel_thm])
  \\ fs[]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
  \\ drule memory_rel_lookup
  \\ ‘lookup a2 s6.locals = SOME w’ by
    (gvs [Abbr‘s6’]
     \\ Cases_on ‘cut_env x' s.locals’ \\ fs []
     \\ rveq \\ simp []
     \\ gvs [dataSemTheory.get_var_def])
  \\ ‘lookup (adjust_var a2) (union y2 y1) = SOME w'’ by
   (gvs [GSYM adjust_var_def]
    \\ qpat_x_assum ‘cut_envs _ _ = SOME (y1,y2)’ mp_tac
    \\ qpat_x_assum ‘_ = SOME x’ mp_tac
    \\ qpat_x_assum ‘get_var a2 x.locals = SOME w’ mp_tac
    \\ qpat_x_assum ‘lookup _ _ = SOME w'’ mp_tac
    \\ rpt $ pop_assum kall_tac
    \\ rw [] \\ gvs [CaseEq"option"]
    \\ gvs [wordSemTheory.cut_envs_def,dataSemTheory.cut_env_def,
            wordSemTheory.cut_names_def,AllCaseEqs(),get_var_def,
            lookup_inter_alt,adjust_sets_def,lookup_union,
            adjust_var_IN_adjust_set])
  \\ disch_then drule_all
  \\ strip_tac
  \\ drule memory_rel_RefArray
  \\ qabbrev_tac `new = LEAST ptr. ptr ∉ domain x.refs`
  \\ `new ∉ domain x.refs` by metis_tac [LEAST_NOTIN_spt_DOMAIN]
  \\ `encode_header c 2 i = SOME (make_header c 2w i)` by
   (fs[encode_header_def,memory_rel_def,heap_in_memory_store_def]
    \\ reverse conj_tac THEN1
     (fs[encode_header_def,memory_rel_def,heap_in_memory_store_def,EXP_SUB]
      \\ unabbrev_all_tac \\ fs [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
      \\ rfs [good_dimindex_def,dimword_def])
    \\ `1 < dimindex (:α) − (c.len_size + 2)` by
     (qpat_assum `c.len_size + _ < dimindex (:α)` mp_tac
      \\ rpt (pop_assum kall_tac) \\ decide_tac)
    \\ fs[good_dimindex_def,dimword_def])
  \\ gvs [Abbr‘s6’]
  \\ rpt(disch_then drule)
  \\ impl_tac >- simp []
  \\ `good_dimindex(:'a)` by(FULL_SIMP_TAC std_ss [state_rel_def])
  \\ simp[intLib.COOPER_PROVE ``4 * k DIV 4 = k``]
  \\ strip_tac
  \\ fs [store_list_def,FOUR_MUL_LSL]
  \\ fs [word_exp_rw,FLOOKUP_UPDATE,wordSemTheory.set_var_def,WORD_LEFT_ADD_DISTRIB]
  \\ qabbrev_tac `ww = eoh1 + -1w * bytes_in_word + -1w * (bytes_in_word * n2w i)`
  \\ qabbrev_tac `ww1 = trig1 + -1w * bytes_in_word + -1w * (bytes_in_word * n2w i)`
  \\ reverse IF_CASES_TAC
  >- (rfs[Smallnum_def] >>
      fs[memory_rel_def] >>
      imp_res_tac store_list_domain >>
      fs [word_exp_rw,FLOOKUP_UPDATE,wordSemTheory.set_var_def,WORD_LEFT_ADD_DISTRIB] >>
      qsuff_tac `eoh1 + -1w * bytes_in_word + -1w * (bytes_in_word * n2w i)
       = eoh1 + -1w * (bytes_in_word * n2w (i + 1))`
      >- (strip_tac >> fs[]) >>
      fs[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])
  \\ fs[list_Seq_def]
  \\ qmatch_goalsub_abbrev_tac `(Call _ _ _ _,bigenv)`
  \\ `lookup Replicate_location bigenv.code = SOME (5,Replicate_code)`
      by(imp_res_tac lookup_RefByte_location
         \\ fs[lookup_insert,lookup_fromList2,lookup_fromList,
               wordSemTheory.dec_clock_def,Abbr `bigenv`])
  \\ drule Replicate_code_thm
  \\ simp[wordSemTheory.get_var_def]
  \\ `i < bigenv.clock` by fs[Abbr`bigenv`]
  \\ disch_then(pop_assum o mp_then Any mp_tac)
  \\ qmatch_asmsub_abbrev_tac `insert 1 (Word www)`
  \\ `(eoh1 + bytes_in_word + -1w * (bytes_in_word * n2w (i + 1)))
      = www + bytes_in_word`
       by(fs[Abbr`www`,Smallnum_def,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])
  \\ fs[]
  \\ `store_list (www + bytes_in_word) (REPLICATE i w') bigenv.memory
                bigenv.mdomain = SOME m1`
     by(match_mp_tac EQ_TRANS >> HINT_EXISTS_TAC >>
        reverse conj_tac >- simp[] >>
        qpat_x_assum `store_list _ _ _ _ = _` kall_tac >>
        rw[Abbr `bigenv`] >>
        simp[make_header_def] >>
        rpt(AP_THM_TAC ORELSE AP_TERM_TAC) >>
        simp[Smallnum_def] >>
        simp[FOUR_MUL_LSL] >>
        fs[word_mul_n2w,LEFT_ADD_DISTRIB] >>
        rw[Abbr`www`,Smallnum_def,FOUR_MUL_LSL,Abbr`ww`,
           GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB] >>
        rpt(AP_THM_TAC ORELSE AP_TERM_TAC) >>
        fs[memory_rel_def,heap_in_memory_store_def])
  \\ disch_then drule
  \\ disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV rev))
  \\ disch_then(qspecl_then [`3`,`2`,`4`,`1`,`0`] mp_tac)
  \\ simp[Abbr `bigenv`,lookup_insert,lookup_fromList2,lookup_fromList,
          Smallnum_def,lookup_2_call_env]
  \\ strip_tac
  \\ simp[]
  \\ CASE_TAC
  >- (sg ‘F’ \\ fs []
      \\ gvs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def]
      \\ pairarg_tac \\ gvs [])
  \\ rename [‘domain t8.locals = domain y1 ∪ domain y2’]
  \\ ‘domain t8.locals = domain y1 ∪ domain y2’ by
    (qpat_x_assum ‘pop_env _ = _’ mp_tac
     \\ simp [wordSemTheory.pop_env_def,AllCaseEqs(),
             wordSemTheory.push_env_def,
             wordSemTheory.call_env_def]
     \\ pairarg_tac \\ simp []
     \\ strip_tac \\ gvs [domain_union,domain_fromAList_toAList]
     \\ drule env_to_list_domain
     \\ gvs [AC UNION_COMM UNION_ASSOC])
  \\ simp []
  \\ qpat_x_assum ‘pop_env _ = _’ mp_tac
  \\ fs[dataSemTheory.set_var_def]
  \\ simp [wordSemTheory.pop_env_def,AllCaseEqs(),
           wordSemTheory.push_env_def,
           wordSemTheory.call_env_def]
  \\ pairarg_tac \\ gvs [] \\ strip_tac \\ gvs []
  \\ simp [wordSemTheory.set_vars_def,alist_insert_def]
  \\ qpat_x_assum ‘state_rel _ _ _ _ _ _ _’ mp_tac
  \\ simp[state_rel_thm,lookup_insert,adjust_var_11]
  \\ rewrite_tac [GSYM adjust_var_def]
  \\ conj_tac
  THEN1 (* code_oracle_rel *)
   (fs [code_oracle_rel_def,FLOOKUP_UPDATE,bytes_in_word_def,n2w_sub]
    \\ once_rewrite_tac [GSYM word_sub_def]
    \\ rewrite_tac [WORD_LEFT_SUB_DISTRIB]
    \\ fs [GSYM bytes_in_word_def]
    \\ simp [FUN_EQ_THM,o_DEF,shift_seq_def,FORALL_PROD]
    \\ rewrite_tac [GSYM WORD_ADD_ASSOC]
    \\ AP_TERM_TAC \\ fs []
    \\ rewrite_tac [WORD_ADD_ASSOC]
    \\ once_rewrite_tac [WORD_ADD_COMM]
    \\ rewrite_tac [WORD_ADD_ASSOC,wordsTheory.WORD_ADD_LINV]
    \\ fs [])
  \\ conj_tac >-
   (simp [lookup_union,lookup_fromAList,CaseEq"option",ALOOKUP_toAList]
    \\ disj1_tac \\ drule_all lookup_loc_lemma \\ simp_tac std_ss [])
  \\ conj_tac >-
   (simp [wordSemTheory.set_vars_def,alist_insert_def,lookup_insert,adjust_var_11]
    \\ rw [] \\ pop_assum mp_tac
    \\ rewrite_tac [IS_SOME_EXISTS,GSYM domain_lookup]
    \\ drule adjust_var_cut_env_IMP_MEM \\ simp []
      \\ simp_tac std_ss []
    \\ qpat_x_assum ‘cut_env x' x.locals = SOME x.locals’ mp_tac
    \\ rpt $ pop_assum kall_tac
    \\ rewrite_tac [IS_SOME_EXISTS,GSYM domain_lookup]
    \\ gvs [cut_env_def,CaseEq"option"]
    \\ strip_tac
    \\ metis_tac [domain_inter,IN_INTER])
  \\ conj_tac THEN1
    (fs [wordSemTheory.call_env_def,wordSemTheory.push_env_def] >>
     imp_res_tac evaluate_stack_max_le >> fs[] >>
     match_mp_tac option_le_trans >> PURE_ONCE_REWRITE_TAC[CONJ_SYM] >>
     goal_assum drule >>
     rw[option_le_max_right,stack_size_eq,AC option_add_comm option_add_assoc])
  \\ conj_tac THEN1
    (fs [wordSemTheory.call_env_def,wordSemTheory.push_env_def] >>
     drule_then match_mp_tac option_le_trans >>
     imp_res_tac stack_rel_IMP_size_of_stack >>
     rw[size_of_stack_eq,option_le_max_right,option_le_max,
        option_map2_max_add,AC option_add_comm option_add_assoc,
        option_le_eq_eqns,option_map2_max_add,stack_size_eq,option_le_add])
  \\ conj_tac >- gvs [FLOOKUP_SIMP]
  \\ simp [wordSemTheory.set_vars_def,alist_insert_def,lookup_insert,adjust_var_11]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ irule memory_rel_insert
  \\ simp [FAPPLY_FUPDATE_THM]
  \\ qhdtm_x_assum `memory_rel` mp_tac
  \\ `EndOfHeap <> TriggerGC` by fs []
  \\ pop_assum (fn th => fs [MATCH_MP FUPDATE_COMMUTES th])
  \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,Abbr`ww1`]
  \\ `ww = www` by(unabbrev_all_tac >> simp[Smallnum_def])
  \\ simp[]
  \\ match_mp_tac (METIS_PROVE [] “x = y ⇒ x ⇒ y”)
  \\ AP_TERM_TAC
  \\ simp []
  \\ conj_tac >- gvs [make_ptr_def]
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ simp []
  \\ simp [lookup_inter_alt]
  \\ rw []
  \\ fs [lookup_union,lookup_fromAList,ALOOKUP_toAList]
  \\ imp_res_tac env_to_list_lookup_equiv
  \\ simp []
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
    if i < 0 then (0w - n2w (Num (-i))) << 2 else n2w (Num i) << 2
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
  rpt strip_tac \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ asm_rewrite_tac [] \\ pop_assum kall_tac
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
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
  \\ reverse BasicProvers.TOP_CASE_TAC >- (
    simp[Once wordSemTheory.evaluate_def]
    \\ simp[Once wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def]
    \\ simp[asmTheory.word_cmp_def]
    \\ rpt_drule0 memory_rel_any_Number_IMP \\ strip_tac
    \\ simp[]
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
      \\ simp[wordLangTheory.word_sh_def]
      \\ simp[wordSemTheory.set_var_def]
      \\ simp[wordSemTheory.word_exp_def]
      \\ fs[adjust_var_def,lookup_insert]
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
      \\ disch_then (qspec_then `(Smallnum i >> 2)` mp_tac)
      \\ `INT_MIN (:'a) <= 4 * i /\ 4 * i <= INT_MAX (:'a) ∧
          INT_MIN (:64) <= 4 * i /\ 4 * i <= INT_MAX (:64) ∧
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
          \\ `~BIT 29 n` by (match_mp_tac LESS_IMP_NOT_BIT \\ fs []) \\ fs []
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
      \\ qexists_tac`x.space - 3` \\ simp[]
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
    \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [eq_eval]
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
          \\ `4294967296 − Num (ABS i) < 4294967296` by decide_tac
          \\ drule0 DIV_MULT
          \\ simp_tac std_ss [])
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
      \\ Cases_on `i` \\ fs [Num_ABS_AND]
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
      \\ fs [eq_eval,wordSemTheory.inst_def]
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
      ))
  \\ simp[Once wordSemTheory.evaluate_def]
  \\ simp[Once wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def]
  \\ simp[asmTheory.word_cmp_def]
  \\ rpt_drule0 memory_rel_any_Number_IMP \\ strip_tac
  \\ simp[]
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
    \\ simp[wordLangTheory.word_sh_def]
    \\ simp[wordSemTheory.set_var_def]
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
    \\ qexists_tac`x.space - 2` \\ simp[]
    \\ fs[FAPPLY_FUPDATE_THM]
    \\ qmatch_asmsub_abbrev_tac`Word64 w1`
    \\ qmatch_goalsub_abbrev_tac`Word64 w2`
    \\ `w1 = w2` suffices_by (rw[] \\ fs[])
    \\ simp[Abbr`w1`,Abbr`w2`]
    \\ `INT_MIN (:'a) <= 4 * i /\ 4 * i <= INT_MAX (:'a)`
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
    \\ qexists_tac`x.space - 2`
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
  \\ qexists_tac`x.space - 2`
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

Theorem assign_TagEq:
   (?tag. op = BlockOp (TagEq tag)) ==> ^assign_thm_goal
Proof
  rpt strip_tac
   \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app,allowed_op_def] \\ rfs [] \\ every_case_tac \\ fs []
  \\ clean_tac \\ fs []
  \\ fs [Boolv_def] \\ rveq
  \\ fs [GSYM Boolv_def] \\ rveq
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_1] \\ clean_tac
  \\ qpat_x_assum `state_rel c l1 l2 x t [] locs` (fn th => NTAC 2 (mp_tac th))
  \\ strip_tac
  \\ simp_tac std_ss [state_rel_thm] \\ strip_tac \\ fs [] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac \\ fs []
  \\ fs [assign_def,list_Seq_def] \\ eval_tac
  \\ reverse IF_CASES_TAC THEN1
   (eval_tac
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
    \\ rename1 `get_vars [a1] x.locals = SOME [Block t5 n5 l5]`
    \\ `n5 <> tag` by
     (strip_tac \\ clean_tac
      \\ rpt_drule0 memory_rel_Block_IMP \\ strip_tac \\ fs []
      \\ CCONTR_TAC \\ fs []
      \\ imp_res_tac encode_header_tag_mask \\ NO_TAC)
    \\ fs [option_le_max_right] \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs [inter_insert_ODD_adjust_set_alt]
    \\ match_mp_tac memory_rel_Boolv_F \\ fs [])
  \\ imp_res_tac get_vars_1_imp
  \\ eval_tac \\ fs [wordSemTheory.get_var_def,asmTheory.word_cmp_def,
       wordSemTheory.get_var_imm_def,lookup_insert]
  \\ rpt_drule0 memory_rel_Block_IMP \\ strip_tac \\ fs []
  \\ fs [word_and_one_eq_0_iff |> SIMP_RULE (srw_ss()) []]
  \\ pop_assum mp_tac \\ IF_CASES_TAC \\ fs [] THEN1
   (fs [word_mul_n2w,word_add_n2w] \\ strip_tac
    \\ fs [LESS_DIV_16_IMP,DECIDE ``16 * n = 16 * m <=> n = m:num``]
    \\ IF_CASES_TAC \\ fs [lookup_insert]
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs [inter_insert_ODD_adjust_set_alt]
    \\ TRY (match_mp_tac memory_rel_Boolv_T)
    \\ TRY (match_mp_tac memory_rel_Boolv_F) \\ fs [])
  \\ strip_tac \\ fs []
  \\ `!w. word_exp (t with locals := insert 1 (Word w) t.locals)
        (real_addr c (adjust_var a1)) = SOME (Word a)` by
    (strip_tac \\ match_mp_tac (GEN_ALL get_real_addr_lemma)
     \\ fs [wordSemTheory.get_var_def,lookup_insert] \\ NO_TAC) \\ fs []
  \\ rpt_drule0 encode_header_tag_mask \\ fs []
  \\ fs [LESS_DIV_16_IMP,DECIDE ``16 * n = 16 * m <=> n = m:num``]
  \\ strip_tac \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs [inter_insert_ODD_adjust_set_alt]
  \\ TRY (match_mp_tac memory_rel_Boolv_T)
  \\ TRY (match_mp_tac memory_rel_Boolv_F) \\ fs []
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

Theorem assign_TagLenEq:
   (?tag len. op = BlockOp (TagLenEq tag len)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app,allowed_op_def] \\ rfs [] \\ every_case_tac \\ fs []
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [Boolv_def] \\ rveq
  \\ fs [GSYM Boolv_def] \\ rveq
  \\ fs [LENGTH_EQ_1] \\ clean_tac
  \\ fs [LENGTH_EQ_1] \\ clean_tac
  \\ qpat_x_assum `state_rel c l1 l2 x t [] locs` (fn th => NTAC 2 (mp_tac th))
  \\ strip_tac
  \\ simp_tac std_ss [state_rel_thm] \\ strip_tac \\ fs [] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac \\ fs []
  \\ fs [assign_def] \\ IF_CASES_TAC \\ fs [] \\ clean_tac
  THEN1 (* len = 0 case *)
   (reverse IF_CASES_TAC
    \\ fs [LENGTH_NIL]
    \\ imp_res_tac get_vars_1_imp \\ eval_tac
    \\ fs [wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def]
    THEN1
     (fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
      \\ imp_res_tac memory_rel_tag_limit
      \\ rpt_drule0 (DECIDE ``n < m /\ ~(k < m:num) ==> n <> k``) \\ fs [option_le_max_right]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ match_mp_tac memory_rel_Boolv_F \\ fs [])
    \\ rpt_drule0 memory_rel_test_nil_eq \\ strip_tac \\ fs []
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
           asmTheory.word_cmp_def]
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
  \\ CASE_TAC \\ fs [] THEN1
   (eval_tac \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ rpt_drule0 memory_rel_test_none_eq \\ strip_tac \\ fs []
    \\ match_mp_tac memory_rel_Boolv_F \\ fs [])
  \\ fs [list_Seq_def] \\ eval_tac \\ fs [wordSemTheory.get_var_imm_def]
  \\ imp_res_tac get_vars_1_imp \\ eval_tac
  \\ fs [wordSemTheory.get_var_def,lookup_insert,asmTheory.word_cmp_def]
  \\ rpt_drule0 memory_rel_Block_IMP \\ strip_tac \\ fs []
  \\ fs [word_and_one_eq_0_iff |> SIMP_RULE (srw_ss()) []]
  \\ IF_CASES_TAC \\ fs [] THEN1
   (IF_CASES_TAC \\ fs [] \\ drule0 encode_header_NEQ_0 \\ strip_tac \\ fs []
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
  \\ drule0 (GEN_ALL encode_header_EQ)
  \\ qpat_x_assum `encode_header _ _ _ = _` (assume_tac o GSYM)
  \\ disch_then drule0 \\ fs [] \\ impl_tac
  \\ TRY (fs [memory_rel_def,heap_in_memory_store_def] \\ NO_TAC) \\ fs []
  \\ disch_then kall_tac \\ fs [DECIDE ``4 * k = 4 * l <=> k = l:num``]
  \\ rw [lookup_insert,adjust_var_11] \\ fs []
  \\ rw [lookup_insert,adjust_var_11] \\ fs []
  \\ fs [inter_insert_ODD_adjust_set,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ TRY (match_mp_tac memory_rel_Boolv_F) \\ fs []
  \\ TRY (match_mp_tac memory_rel_Boolv_T) \\ fs []
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
   (?len. op = BlockOp (LenEq len)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app,allowed_op_def] \\ rfs [] \\ every_case_tac \\ fs []
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [Boolv_def] \\ rveq
  \\ fs [GSYM Boolv_def] \\ rveq
  \\ fs [LENGTH_EQ_1] \\ clean_tac
  \\ fs [LENGTH_EQ_1] \\ clean_tac
  \\ qpat_x_assum `state_rel c l1 l2 x t [] locs` (fn th => NTAC 2 (mp_tac th))
  \\ strip_tac
  \\ simp_tac std_ss [state_rel_thm] \\ strip_tac \\ fs [] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac \\ fs []
  \\ fs [assign_def] \\ IF_CASES_TAC \\ fs [] \\ clean_tac
  THEN1 (* len = 0 case *)
   (imp_res_tac get_vars_1_imp \\ eval_tac
    \\ fs [wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def]
    \\ rpt_drule0 memory_rel_Block_IMP \\ strip_tac \\ fs []
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
           asmTheory.word_cmp_def]
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
    \\ fs [inter_insert_ODD_adjust_set]
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ match_mp_tac memory_rel_Boolv_F \\ fs [])
  \\ Cases_on `payload = []` \\ fs [] \\ rveq \\ fs []
  THEN1
   (fs [list_Seq_def] \\ eval_tac \\ fs [wordSemTheory.get_var_imm_def]
    \\ fs [wordSemTheory.get_var_def,lookup_insert,asmTheory.word_cmp_def]
    \\ fs [inter_insert_ODD_adjust_set]
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ match_mp_tac memory_rel_Boolv_F \\ fs [])
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
  \\ fs [inter_insert_ODD_adjust_set]
  \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ TRY (match_mp_tac memory_rel_Boolv_T) \\ fs []
  \\ TRY (match_mp_tac memory_rel_Boolv_F) \\ fs []
QED

Theorem state_rel_upd_safe_pkheap:
  ! c l1 l2 s lcl hpk r locs. state_rel c l1 l2
               (s with <| locals := lcl; space := 0; stack_max := NONE|>)
               r [] locs <=>
  state_rel c l1 l2
               (s with
                <|locals := lcl; stack_max := NONE; space := 0; safe_for_space := F;
                  peak_heap_length := hpk|>)
               r [] locs
Proof
  rw [state_rel_def] \\ metis_tac []
QED

val eval_Call_Add = Q.SPEC `0` eval_Call_Arith
  |> SIMP_RULE std_ss [int_op_def,Arith_location_def];

val eval_Call_Sub = Q.SPEC `1` eval_Call_Arith
  |> SIMP_RULE std_ss [int_op_def,Arith_location_def];

val eval_Call_Mul = Q.SPEC `4` eval_Call_Arith
  |> SIMP_RULE std_ss [int_op_def,Arith_location_def];

val eval_Call_Div = Q.SPEC `5` eval_Call_Arith
  |> SIMP_RULE std_ss [int_op_def,Arith_location_def];

val eval_Call_Mod = Q.SPEC `6` eval_Call_Arith
  |> SIMP_RULE std_ss [int_op_def,Arith_location_def];

Theorem state_rel_ignore_safe_for_space[simp]:
  state_rel c l1 l2 (x with <|locals := l; space := s; safe_for_space := m |>) r t locs
  <=>
  state_rel c l1 l2 (x with <|locals := l; space := s |>) r t locs
Proof
  fs [state_rel_def]
QED

Theorem state_rel_peak_heap_length[simp]:
  state_rel c l1 l2 (x with <|locals := l; space := s; peak_heap_length := m |>) r t locs
  <=>
  state_rel c l1 l2 (x with <|locals := l; space := s |>) r t locs
Proof
  rw [state_rel_def]
QED

Theorem opt_map_plus_zero_id[simp]:
  !n. OPTION_MAP2 $+ (SOME 0) n = (n:num option)
Proof
  Cases_on `n` >> fs []
QED

Theorem small_num_small_int[simp]:
  good_dimindex (:α) ==>
  small_num (dimindex (:α) = 64) = small_int (:α)
Proof
  fs [small_num_def,small_int_def,FUN_EQ_THM,good_dimindex_def]
  \\ rw [] \\ fs [dimword_def]
QED

Theorem memory_rel_small_int:
  memory_rel c be ts refs sp st m dm ((Number i,Word(w:'a word))::vars) ∧
  word_bit 0 w ∧ good_dimindex (:α) ⇒
  ~small_int (:'a) i
Proof
  rw [] \\ CCONTR_TAC \\ fs []
  \\ ((first_assum o mp_then (Pos last) mp_tac) memory_rel_Number_IMP)
  \\ fs [] \\ CCONTR_TAC \\ rveq \\ fs []
  \\ fs [word_bit_test,Smallnum_bits]
QED

Theorem small_int_Smallnum_add:
  good_dimindex(:'a) /\ small_int(:'a)(i1 + i2)  ==>
  Smallnum i1 + (Smallnum i2):'a word = Smallnum(i1 + i2)
Proof
 rw[Smallnum_i2w,good_dimindex_def,small_int_def,
    integer_wordTheory.word_i2w_add,integerTheory.INT_LDISTRIB]
QED

Theorem small_int_INT_MIN_MAX:
  good_dimindex(:'a) /\ small_int (:'a) i ==>
  (INT_MIN (:'a) <= 4 * i /\ 4 * i <= INT_MAX (:'a))
Proof
 rw[small_int_def,good_dimindex_def,INT_MIN_def,INT_MAX_def]
 \\ rfs [dimword_def]
 \\ rw[] \\ intLib.COOPER_TAC
QED

Theorem small_int_w2i_Smallnum_add:
  good_dimindex(:'a) /\
  small_int (:'a) (i1 + i2) /\
  small_int (:'a) i1 /\
  small_int (:'a) i2 ==>
  w2i(Smallnum i1 + (Smallnum i2):'a word) = w2i(Smallnum i1:'a word) + w2i(Smallnum i2:'a word)
Proof
 rw[] >>
 rw[small_int_Smallnum_add,Smallnum_i2w] >>
 imp_res_tac small_int_INT_MIN_MAX >>
 simp[integer_wordTheory.w2i_i2w,integerTheory.INT_LDISTRIB]
QED

(* TODO: move? *)
Theorem OPTION_MAP2_NONE[simp]:
  (OPTION_MAP2 f NONE n = NONE) /\ (OPTION_MAP2 f n NONE = NONE)
Proof
  rw[OPTION_MAP2_DEF]
QED

Theorem state_rel_IMP_arch_64_bit:
  state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) xs locs ==>
  (s.limits.arch_64_bit = (dimindex (:'a) = 64))
Proof
  fs [state_rel_def,limits_inv_def]
QED

Theorem cut_state_opt_twice:
  dataSem$cut_state_opt names_opt s = SOME x ==>
  dataSem$cut_state_opt names_opt x = SOME x
Proof
  fs [dataSemTheory.cut_state_opt_def,CaseEq"option",cut_state_def,cut_env_def]
  \\ Cases_on `names_opt` \\ fs [] \\ rw [] \\ fs []
  \\ fs [domain_inter,dataSemTheory.state_component_equality]
  \\ fs [lookup_inter_alt]
QED

Theorem cut_state_opt_extra_const:
  dataSem$cut_state_opt names_opt s = SOME x ==>
  s.stack_frame_sizes = x.stack_frame_sizes ∧
  s.locals_size = x.locals_size
Proof
  fs [CaseEq"option",dataSemTheory.cut_state_opt_def,
      dataSemTheory.cut_state_def,dataSemTheory.cut_env_def]
  \\ rw [] \\ fs []
QED

Theorem assign_Add:
   op = IntOp Add ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ drule state_rel_IMP_arch_64_bit \\ strip_tac
  \\ fs [EVAL ``op_requires_names (IntOp Add)``]
  \\ fs [do_app,oneline do_int_app_def]
  \\ gvs[AllCaseEqs()]
  \\ rename1 `get_vars args x.locals = SOME [Number i1; Number i2]`
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [get_var_def]
  \\ qpat_x_assum `state_rel c l1 l2 x t [] locs` (fn th => NTAC 2 (mp_tac th))
  \\ strip_tac
  \\ simp_tac std_ss [Once state_rel_thm] \\ strip_tac \\ fs [] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac \\ fs []
  \\ rpt_drule0 memory_rel_Number_IMP_Word_2
  \\ strip_tac \\ clean_tac
  \\ rpt_drule0 memory_rel_Add \\ fs [] \\ strip_tac
  \\ fs [assign_def,Once list_Seq_def]
  \\ imp_res_tac get_vars_2_imp
  \\ eval_tac \\ fs [wordSemTheory.inst_def]
  \\ fs [assign_def,Once list_Seq_def]
  \\ eval_tac \\ fs [lookup_insert,wordSemTheory.get_var_def]
  \\ qabbrev_tac `mt = MustTerminate`
  \\ fs [assign_def,Once list_Seq_def]
  \\ eval_tac \\ fs [lookup_insert,wordSemTheory.get_var_def,
                     wordSemTheory.get_var_imm_def]
  \\ fs [word_cmp_Test_1,word_bit_or,word_bit_if_1_0]
  \\ IF_CASES_TAC THEN1
   (fs [list_Seq_def,state_rel_thm] \\ eval_tac
    \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def,lookup_insert,
           wordSemTheory.set_vars_def,wordSemTheory.set_var_def,alist_insert_def]
    \\ conj_tac THEN1 rw []
    \\ conj_tac >- rfs []
    \\ conj_tac >- rw [option_le_max_right]
    \\ fs [lookup_insert,adjust_var_NEQ,adjust_var_11]
    \\ fs [inter_insert_ODD_adjust_set]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ drule0 memory_rel_zero_space \\ fs [])
  \\ `~(small_int (:'a) i1 ∧
        small_int (:'a) i2 ∧
        small_int (:'a) (i1 + i2))` by
     (fs[] >> imp_res_tac memory_rel_small_int >> fs[]
      \\ drule memory_rel_swap \\ strip_tac
      \\ imp_res_tac memory_rel_small_int \\ fs []
      \\ CCONTR_TAC \\ fs []
      \\ imp_res_tac memory_rel_Number_IMP
      \\ fs[] \\ rveq
      \\ CCONTR_TAC \\ fs[]
      \\ qpat_x_assum `w2i _ ≠ _` mp_tac
      \\ fs[small_int_w2i_Smallnum_add])
  \\ simp [stack_consumed_def,OPTION_MAP2_NONE,miscTheory.the_def]
  \\ unabbrev_all_tac
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,t4)`
  \\ `state_rel c l1 l2 x t4 [] locs` by fs [Abbr`t4`,state_rel_insert_3_1]
  \\ drule (GEN_ALL eval_Call_Add)
  \\ disch_then drule \\ simp [Abbr`t4`]
  \\ `dataSem$cut_state_opt names_opt x = SOME x` by
    (imp_res_tac cut_state_opt_twice \\ asm_rewrite_tac [])
  \\ disch_then drule \\ simp []
  \\ disch_then (strip_assume_tac o SPEC_ALL) \\ simp []
  \\ reverse (Cases_on `q = SOME NotEnoughSpace`)
  \\ simp[] THEN1
   (first_x_assum drule \\ simp [state_rel_thm]
    \\ strip_tac \\ imp_res_tac data_to_word_gcProofTheory.stack_rel_IMP_size_of_stack
    \\ qpat_x_assum `option_le _ _` mp_tac \\ simp []
    \\ qpat_x_assum `option_le _ _` mp_tac \\ simp []
    \\ simp [AC option_add_comm option_add_assoc])
  \\ simp []
  \\ conj_tac THEN1
   (rpt (qpat_x_assum `~(_ /\ _)` kall_tac)
    \\ fs [state_rel_thm]
    \\ imp_res_tac data_to_word_gcProofTheory.stack_rel_IMP_size_of_stack \\ fs []
    \\ imp_res_tac cut_state_opt_extra_const
    \\ fs [AC option_add_comm option_add_assoc])
  \\ strip_tac \\ disj1_tac
  \\ CCONTR_TAC
  \\ rpt (qpat_x_assum `~(_ /\ _)` mp_tac)
  \\ fs [] \\ disch_then kall_tac
  \\ fs [limits_inv_def] \\ rfs [] \\ fs []
  \\ fs [space_consumed_def] \\ rfs []
  \\ CCONTR_TAC \\ fs [] \\ fs []
QED

Theorem small_int_Smallnum_sub:
  good_dimindex(:'a) /\ small_int(:'a)(i1 - i2)  ==>
  Smallnum i1 - (Smallnum i2):'a word = Smallnum(i1 - i2)
Proof
 rw[Smallnum_i2w,good_dimindex_def,small_int_def,
    word_i2w_sub,integerTheory.INT_LDISTRIB, integerTheory.INT_SUB_LDISTRIB]
   \\ rewrite_tac [GSYM word_i2w_sub] \\ fs []
QED

Theorem small_int_w2i_Smallnum_sub:
  good_dimindex(:'a) /\ small_int(:'a)(i1 - i2) /\ small_int(:'a) i1 /\ small_int(:'a) i2 ==>
  w2i(Smallnum i1 - (Smallnum i2):'a word) = w2i(Smallnum i1:'a word) - w2i(Smallnum i2:'a word)
Proof
  rw[] >>
  rw[small_int_Smallnum_sub,Smallnum_i2w] >>
  imp_res_tac small_int_INT_MIN_MAX >>
  drule integer_wordTheory.w2i_i2w >>
  strip_tac >> fs [] >>
  `i2w (4 * i1) + -1w * i2w (4 * i2) = i2w (4 * (i1 - i2))` by (
    rw [integerTheory.INT_SUB_LDISTRIB] >>
    rewrite_tac [GSYM word_i2w_sub] >>
    fs []) >>
  simp[] >>
  simp[integer_wordTheory.w2i_i2w,integerTheory.INT_LDISTRIB, integerTheory.INT_SUB_LDISTRIB]
QED

Theorem assign_Sub:
   op = IntOp Sub ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ drule state_rel_IMP_arch_64_bit \\ strip_tac
  \\ fs [EVAL ``op_requires_names (IntOp Sub)``]
  \\ fs [do_app,oneline do_int_app_def]
  \\ gvs[AllCaseEqs()]
  \\ rename1 `get_vars args x.locals = SOME [Number i1; Number i2]`
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [get_var_def]
  \\ qpat_x_assum `state_rel c l1 l2 x t [] locs` (fn th => NTAC 2 (mp_tac th))
  \\ strip_tac
  \\ simp_tac std_ss [Once state_rel_thm] \\ strip_tac \\ fs [] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac \\ fs []
  \\ rpt_drule0 memory_rel_Number_IMP_Word_2
  \\ strip_tac \\ clean_tac
  \\ rpt_drule0 memory_rel_Sub \\ fs [] \\ strip_tac
  \\ fs [assign_def,Once list_Seq_def]
  \\ imp_res_tac get_vars_2_imp
  \\ eval_tac \\ fs [wordSemTheory.inst_def]
  \\ fs [assign_def,Once list_Seq_def]
  \\ eval_tac \\ fs [lookup_insert,wordSemTheory.get_var_def]
  \\ qabbrev_tac `mt = MustTerminate`
  \\ fs [assign_def,Once list_Seq_def]
  \\ eval_tac \\ fs [lookup_insert,wordSemTheory.get_var_def,
                     wordSemTheory.get_var_imm_def]
  \\ fs [word_cmp_Test_1,word_bit_or,word_bit_if_1_0]
  \\ IF_CASES_TAC THEN1
   (fs [list_Seq_def,state_rel_thm] \\ eval_tac
    \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def,lookup_insert,
           wordSemTheory.set_vars_def,wordSemTheory.set_var_def,alist_insert_def]
    \\ conj_tac THEN1 rw []
    \\ conj_tac >- rfs []
    \\ conj_tac >- rw [option_le_max_right]
    \\ fs [lookup_insert,adjust_var_NEQ,adjust_var_11]
    \\ fs [inter_insert_ODD_adjust_set]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ drule0 memory_rel_zero_space \\ fs [])
  \\ `~(small_int (:'a) i1 ∧ small_int (:'a) i2 ∧
        small_int (:'a) (i1 - i2))` by
     (fs[] >> imp_res_tac memory_rel_small_int >> fs[]
      \\ drule memory_rel_swap \\ strip_tac
      \\ imp_res_tac memory_rel_small_int \\ fs []
      \\ CCONTR_TAC \\ fs []
      \\ imp_res_tac memory_rel_Number_IMP
      \\ fs[] \\ rveq
      \\ CCONTR_TAC \\ fs[]
      \\ qpat_x_assum `w2i _ ≠ _` mp_tac
      \\ fs[GSYM small_int_w2i_Smallnum_sub])
  \\ simp [stack_consumed_def,OPTION_MAP2_NONE,miscTheory.the_def]
  \\ unabbrev_all_tac
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,t4)`
  \\ `state_rel c l1 l2 x t4 [] locs` by fs [Abbr`t4`,state_rel_insert_3_1]
  \\ drule (GEN_ALL eval_Call_Sub)
  \\ disch_then drule \\ simp [Abbr`t4`]
  \\ `dataSem$cut_state_opt names_opt x = SOME x` by
    (imp_res_tac cut_state_opt_twice \\ asm_rewrite_tac [])
  \\ disch_then drule \\ simp []
  \\ disch_then (strip_assume_tac o SPEC_ALL) \\ simp []
  \\ reverse (Cases_on `q = SOME NotEnoughSpace`)
  \\ simp[] THEN1
   (first_x_assum drule \\ simp [state_rel_thm]
    \\ strip_tac \\ imp_res_tac data_to_word_gcProofTheory.stack_rel_IMP_size_of_stack
    \\ qpat_x_assum `option_le _ _` mp_tac \\ simp []
    \\ qpat_x_assum `option_le _ _` mp_tac \\ simp []
    \\ simp [AC option_add_comm option_add_assoc])
  \\ simp []
  \\ conj_tac THEN1
   (rpt (qpat_x_assum `~(_ /\ _)` kall_tac)
    \\ fs [state_rel_thm]
    \\ imp_res_tac data_to_word_gcProofTheory.stack_rel_IMP_size_of_stack \\ fs []
    \\ imp_res_tac cut_state_opt_extra_const
    \\ fs [AC option_add_comm option_add_assoc])
  \\ strip_tac \\ disj1_tac
  \\ CCONTR_TAC
  \\ rpt (qpat_x_assum `~(_ /\ _)` mp_tac)
  \\ fs [] \\ disch_then kall_tac
  \\ fs [limits_inv_def] \\ rfs [] \\ fs []
  \\ fs [space_consumed_def] \\ rfs []
  \\ CCONTR_TAC \\ fs [] \\ fs []
  \\ fs [stack_consumed_def,OPTION_MAP2_NONE,miscTheory.the_def]
QED

Theorem cut_state_opt_IMP_ffi:
   dataSem$cut_state_opt names_opt s = SOME x ==> x.ffi = s.ffi
Proof
  fs [dataSemTheory.cut_state_opt_def,dataSemTheory.cut_state_def]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
QED

Theorem quad_times_div_half_double:
  (4 * j) DIV 2 = 2 * (j:num)
Proof
  ONCE_REWRITE_TAC[MULT_COMM]
  \\ `j * 4 = (j * 2) * 2` by DECIDE_TAC
  \\ asm_rewrite_tac []
  \\ fs [MULT_DIV]
QED

Theorem w2n_mul_less:
  !w w'.
    (w2n (w:'a word) * w2n (w':'a word)) < dimword (:'a) ** 2
Proof
  rpt strip_tac >>
  PURE_REWRITE_TAC[ONE,TWO,EXP,MULT_CLAUSES,ADD_CLAUSES] >>
  match_mp_tac bitTheory.LESS_MULT_MONO2 >>
  strip_tac >> MATCH_ACCEPT_TAC w2n_lt
QED

Theorem assign_Mult:
  op = IntOp Mult ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ drule state_rel_IMP_arch_64_bit \\ strip_tac
  \\ fs [EVAL ``op_requires_names (IntOp Mult)``]
  \\ fs [do_app,oneline do_int_app_def]
  \\ gvs[AllCaseEqs()]
  \\ rename1 `get_vars args x.locals = SOME [Number i1; Number i2]`
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [get_var_def]
  \\ qpat_x_assum `state_rel c l1 l2 x t [] locs` (fn th => NTAC 2 (mp_tac th))
  \\ strip_tac
  \\ simp_tac std_ss [Once state_rel_thm] \\ strip_tac \\ fs [] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac \\ fs []
  \\ rfs []
  \\ rpt_drule0 memory_rel_Number_IMP_Word_2
  \\ strip_tac \\ clean_tac
  \\ fs [assign_def]
  \\ fs [get_vars_SOME_IFF,get_vars_SOME_IFF_data]
  \\ rveq \\ fs []
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval,wordSemTheory.inst_def]
  \\ `n2w (w2n w2 * w2n (w1 ⋙ 1)) = FST (single_mul w2 (w1 >>> 1) 0w) /\
      n2w (w2n w2 * w2n (w1 ⋙ 1) DIV dimword (:α)) =
        SND (single_mul w2 (w1 >>> 1) 0w)` by
    (fs [multiwordTheory.single_mul_def,GSYM word_mul_n2w] \\ NO_TAC) \\ fs []
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [eq_eval]
  \\ rewrite_tac [list_Seq_def]
  \\ once_rewrite_tac [``list_Seq [MustTerminate x]``
       |> REWRITE_CONV [list_Seq_def] |> GSYM]
  \\ once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ fs [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def,lookup_insert,
         asmTheory.word_cmp_def]
  \\ IF_CASES_TAC \\ fs []
  THEN1 (
    fs [eq_eval,wordSemTheory.set_vars_def,alist_insert_def]
    \\ fs [dataSemTheory.call_env_def,alist_insert_def,push_env_def,
           dataSemTheory.set_var_def,wordSemTheory.set_vars_def]
    \\ fs [state_rel_thm,lookup_insert,adjust_var_11]
    \\ conj_tac THEN1 (rw [] \\ fs [])
    \\ fs [inter_insert_ODD_adjust_set]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ conj_tac >- rfs []
    \\ conj_tac >- rw [option_le_max_right]
    \\ match_mp_tac memory_rel_insert
    \\ fs [APPEND]
    \\ once_rewrite_tac [integerTheory.INT_MUL_COMM]
    \\ match_mp_tac (memory_rel_Number_single_mul
        |> SIMP_RULE std_ss [LET_THM,AND_IMP_INTRO]
        |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)
        |> SIMP_RULE std_ss [LET_THM,AND_IMP_INTRO])
    \\ fs []
    \\ imp_res_tac memory_rel_zero_space \\ fs []
    \\ pop_assum kall_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ rpt_drule0 memory_rel_get_vars_IMP
    \\ disch_then (qspecl_then [`[Number i2; Number i1]`,
         `[Word w2; Word w1]`,`[a2;a1]`] mp_tac)
    \\ reverse impl_tac THEN1 fs []
    \\ fs [get_vars_SOME_IFF,wordSemTheory.get_var_def,get_vars_def])
  \\ `~(small_int (:'a) i1 /\
        small_int (:'a) i2 /\ 0 <= i1 /\ 0 <= i2 /\
        small_int (:'a) (i1 * i2))` by
   (CCONTR_TAC \\ fs []
    \\ `~word_bit 0 w1` by (spose_not_then strip_assume_tac
                            \\ imp_res_tac memory_rel_small_int)
    \\ drule memory_rel_swap \\ strip_tac
    \\ `~word_bit 0 w2` by (spose_not_then strip_assume_tac
                            \\ imp_res_tac memory_rel_small_int)
    \\ first_x_assum (mp_then (Pos last) mp_tac (GEN_ALL memory_rel_Number_IMP))
    \\ first_x_assum (mp_then (Pos last) mp_tac (GEN_ALL memory_rel_Number_IMP))
    \\ rpt strip_tac \\ rfs []
    \\ fs []
    \\ dxrule NONNEG_INT
    \\ dxrule NONNEG_INT
    \\ rpt strip_tac
    \\ fs []
    \\ fs [multiwordTheory.single_mul_def]
    \\ fs [GSYM word_bit_test_0]
    \\ fs [WORD_LEFT_AND_OVER_OR]
    \\ fs [DIV_MOD_MOD_DIV, w2n_mul_less]
    \\ fs [DIV_EQ_X, NOT_LESS]  (* we are in the large number case *)
    \\ Cases_on `Smallnum (&j) = 0w` >- fs [dimword_def]
    \\ Cases_on `Smallnum (&j') = 0w` >- fs [dimword_def]
    \\ rfs[w2n_lsr]
    \\ fs [Smallnum_def,small_int_def, X_LT_DIV]
    \\ fs [small_int_def]
    \\ qpat_x_assum `dimword (:α) <= _` mp_tac
    \\ simp [GSYM NOT_LESS]
    \\ fs [good_dimindex_def, dimword_def] \\ rfs []
    \\ fs [quad_times_div_half_double])
  \\ simp [stack_consumed_def,OPTION_MAP2_NONE,miscTheory.the_def]
  \\ unabbrev_all_tac
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,t4)`
  \\ `state_rel c l1 l2 x t4 [] locs` by
        (fs [Abbr`t4`,state_rel_thm,lookup_insert]
         \\ rfs [inter_insert_ODD_adjust_set_alt])
  \\ drule (GEN_ALL eval_Call_Mul)
  \\ disch_then drule \\ simp [Abbr`t4`]
  \\ `dataSem$cut_state_opt names_opt x = SOME x` by
    (imp_res_tac cut_state_opt_twice \\ asm_rewrite_tac [])
  \\ `get_vars [a1; a2] x.locals = SOME [Number i1; Number i2]` by
        simp [get_vars_SOME_IFF_data]
  \\ disch_then drule \\ simp []
  \\ disch_then (strip_assume_tac o SPEC_ALL) \\ simp []
  \\ qpat_x_assum `_ = (_,_)` mp_tac
  \\ simp [list_Seq_def] \\ disch_then kall_tac
  \\ reverse (Cases_on `q = SOME NotEnoughSpace`)
  \\ simp[] THEN1
   (IF_CASES_TAC THEN1 (rfs [] \\ fs [])
    \\ first_x_assum drule \\ simp [state_rel_thm]
    \\ strip_tac \\ imp_res_tac data_to_word_gcProofTheory.stack_rel_IMP_size_of_stack
    \\ qpat_x_assum `option_le _ _` mp_tac \\ simp []
    \\ qpat_x_assum `option_le _ _` mp_tac \\ simp []
    \\ simp [AC option_add_comm option_add_assoc])
  \\ simp []
  \\ IF_CASES_TAC THEN1 (rfs [] \\ fs [])
  \\ conj_tac THEN1
   (rpt (qpat_x_assum `~(_ /\ _)` kall_tac)
    \\ fs [state_rel_thm]
    \\ imp_res_tac data_to_word_gcProofTheory.stack_rel_IMP_size_of_stack \\ fs []
    \\ imp_res_tac cut_state_opt_extra_const
    \\ fs [AC option_add_comm option_add_assoc])
  \\ strip_tac \\ disj1_tac
  \\ CCONTR_TAC
  \\ rpt (qpat_x_assum `~(_ /\ _)` mp_tac)
  \\ fs [] \\ disch_then kall_tac
  \\ fs [limits_inv_def] \\ rfs [] \\ fs []
  \\ fs [space_consumed_def] \\ rfs []
  \\ CCONTR_TAC \\ fs [] \\ fs []
QED

Theorem word_bit_lsr_dimindex_1:
   word_bit 0 ((w1 ⋙ (dimindex (:'a) − 1)):'a word) <=> word_msb w1
Proof
  fs [word_bit_def,word_lsr_def,fcpTheory.FCP_BETA,word_msb_def]
QED

Theorem state_rel_Number_IMP:
   state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) [] locs /\
    get_var a1 s.locals = SOME (Number i1) /\
    lookup (adjust_var a1) t.locals = SOME v1 ==>
    ?w1. (v1 = Word w1) /\
         (~(word_bit 0 w1) <=> small_int (:'a) i1) /\
         (~(word_msb w1) /\ ~(word_bit 0 w1) ==> 0 <= i1 /\ w1 = n2w (4 * Num i1))
Proof
  fs [state_rel_thm] \\ rw []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ drule0 (GEN_ALL memory_rel_get_var_IMP)
  \\ disch_then (qspec_then `a1` mp_tac)
  \\ fs [get_var_def,wordSemTheory.get_var_def]
  \\ rw [] \\ rpt_drule0 memory_rel_any_Number_IMP \\ rw [] \\ fs []
  \\ fs [word_bit_def] \\ strip_tac
  \\ imp_res_tac memory_rel_Number_IMP \\ fs [] \\ rveq
  \\ rpt_drule0 memory_rel_Number_word_msb \\ fs []
  \\ Cases_on `i1` \\ fs [Smallnum_def]
QED

Theorem option_le_add_comm:
  option_le (OPTION_MAP2 $+ a b) c ==>
    option_le (OPTION_MAP2 $+ b a) c
Proof
  Cases_on `a` >> Cases_on `b` >> Cases_on `c` >> fs [OPTION_MAP2_DEF, option_le_def]
QED

Theorem IN_adjust_set_IN:
  y ∈ domain (adjust_set x) ⇒ (y − 2) DIV 2 ∈ domain x
Proof
  rw [domain_lookup,adjust_set_def,lookup_fromAList]
  \\ imp_res_tac ALOOKUP_MEM
  \\ gvs [MEM_MAP,EXISTS_PROD]
  \\ imp_res_tac MEM_toAList
  \\ simp [adjust_var_def,MULT_TO_DIV]
QED

Theorem assign_Div:
  op = IntOp Div ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [EVAL ``op_requires_names (IntOp Div)``]
  \\ fs [do_app,oneline do_int_app_def]
  \\ gvs[AllCaseEqs()]
  \\ rename1 `get_vars args x.locals = SOME [Number i1; Number i2]`
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [assign_def]
  \\ fs [get_vars_SOME_IFF]
  \\ fs [get_vars_SOME_IFF_data]
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ rename1 `lookup (adjust_var a1) t.locals = SOME v1`
  \\ rename1 `lookup (adjust_var a2) t.locals = SOME v2`
  \\ `?w1. v1 = Word w1 /\
        (~(word_bit 0 w1) <=> small_int (:'a) i1) /\
        (~(word_msb w1) /\ ~(word_bit 0 w1) ==> 0 <= i1 /\ w1 = n2w (4 * Num i1))` by
          (metis_tac [state_rel_Number_IMP])
  \\ `?w2. v2 = Word w2 /\
        (~(word_bit 0 w2) <=> small_int (:'a) i2) /\
        (~(word_msb w2) /\ ~(word_bit 0 w2) ==> 0 <= i2 /\ w2 = n2w (4 * Num i2))` by
          (metis_tac [state_rel_Number_IMP])
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [eq_eval]
  \\ simp [word_bit_test_0]
  \\ IF_CASES_TAC THEN1
   (fs [word_bit_or,word_bit_lsr_dimindex_1] \\ rveq
    \\ `?n1. i1 = & n1` by (Cases_on `i1` \\ fs [])
    \\ `?n2. i2 = & n2` by (Cases_on `i2` \\ fs [])
    \\ fs [] \\ rveq
    \\ `4 * n2 < dimword (:'a) /\ 4 * n1 < dimword (:'a)` by
          fs [small_int_def,X_LT_DIV]
    \\ `n2w (4 * n2) <> 0w` by fs []
    \\ `small_int (:α) (&(n1 DIV n2))` by
     (fs [small_int_def,DIV_LT_X]
      \\ rfs [good_dimindex_def,state_rel_thm,dimword_def] \\ rfs [])
    \\ Cases_on `c.has_div` \\ fs [] THEN1
     (fs [list_Seq_def,eq_eval,wordSemTheory.inst_def,insert_shadow]
      \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [eq_eval]
      \\ simp [state_rel_thm,adjust_var_11,
           lookup_insert,
           code_oracle_rel_def,FLOOKUP_UPDATE,
           dataSemTheory.call_env_def,alist_insert_def,
           push_env_def,
           dataSemTheory.set_var_def,wordSemTheory.set_vars_def]
      \\ fs [state_rel_thm,adjust_var_11,lookup_insert,
             code_oracle_rel_def,FLOOKUP_UPDATE,
             dataSemTheory.call_env_def,alist_insert_def,
             push_env_def,dataSemTheory.set_var_def,wordSemTheory.set_vars_def]
      \\ conj_tac THEN1 (rw [] \\ fs [])
      \\ conj_tac >- rw [option_le_max_right]
      \\ fs [inter_insert_ODD_adjust_set]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
      \\ `(n2w (4 * n1) / n2w (4 * n2)) ≪ 2 = Smallnum (&(n1 DIV n2))` by
       (fs [wordsTheory.word_quot_def,word_div_def,Smallnum_def]
        \\ fs [WORD_MUL_LSL,word_mul_n2w,GSYM DIV_DIV_DIV_MULT,
               MULT_DIV |> ONCE_REWRITE_RULE [MULT_COMM]])
      \\ fs [] \\ match_mp_tac IMP_memory_rel_Number \\ fs []
      \\ imp_res_tac memory_rel_zero_space \\ fs [])
    \\ Cases_on `c.has_longdiv` \\ fs [] THEN1
     (fs [list_Seq_def,eq_eval,wordSemTheory.inst_def,insert_shadow]
      \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [eq_eval]
      \\ reverse IF_CASES_TAC THEN1
       (sg `F` \\ rfs [DIV_LT_X]
        \\ pop_assum mp_tac
        \\ Cases_on `n2` \\ fs [MULT_CLAUSES])
      \\ simp [state_rel_thm,adjust_var_11,
           lookup_insert,
           code_oracle_rel_def,FLOOKUP_UPDATE,
           dataSemTheory.call_env_def,alist_insert_def,
           push_env_def,
           dataSemTheory.set_var_def,wordSemTheory.set_vars_def]
      \\ fs [state_rel_thm,adjust_var_11,lookup_insert,code_oracle_rel_def,
             FLOOKUP_UPDATE,dataSemTheory.call_env_def,alist_insert_def,
             push_env_def,dataSemTheory.set_var_def,wordSemTheory.set_vars_def]
      \\ conj_tac THEN1 (rw [] \\ fs [])
      \\ conj_tac >- rw [option_le_max_right]
      \\ fs [inter_insert_ODD_adjust_set]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
      \\ `n2w (4 * n1 DIV (4 * n2)) ≪ 2 = Smallnum (&(n1 DIV n2))` by
       (fs [wordsTheory.word_quot_def,word_div_def,Smallnum_def]
        \\ fs [WORD_MUL_LSL,word_mul_n2w,GSYM DIV_DIV_DIV_MULT,
               MULT_DIV |> ONCE_REWRITE_RULE [MULT_COMM]] \\ NO_TAC)
      \\ fs [] \\ match_mp_tac IMP_memory_rel_Number \\ fs []
      \\ imp_res_tac memory_rel_zero_space \\ fs [])
    \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
    \\ once_rewrite_tac [list_Seq_def] \\ fs []
    \\ once_rewrite_tac [wordSemTheory.evaluate_def]
    \\ rewrite_tac [insert_shadow]
    \\ qpat_x_assum `state_rel c l1 l2 x t [] locs`
          (mp_tac o REWRITE_RULE [state_rel_thm])
    \\ fs [] \\ strip_tac
    \\ fs [eq_eval,code_rel_def,stubs_def,cut_names_adjust_set_insert_1]
    \\ Cases_on `names_opt` \\ fs [cut_state_opt_def,cut_state_def]
    \\ Cases_on `dataSem$cut_env x' s.locals` \\ fs []
    \\ imp_res_tac cut_env_IMP_cut_env
    \\ drule_all cut_env_IMP_cut_envs \\ strip_tac \\ fs []
    \\ Cases_on `env_to_list y2 t.permute` \\ fs []
    \\ fs [get_names_def,wordSemTheory.push_env_def,domain_adjust_sets,
           cut_envs_adjust_sets_ODD]
    \\ qmatch_goalsub_abbrev_tac `evaluate (LongDiv_code c,t2)`
    \\ qspecl_then [`t2`,`n`,`l+1`,`c`] mp_tac evaluate_LongDiv_code'
    \\ fs [] \\ disch_then (qspecl_then [`0w`,`n2w (4 * n1)`,`n2w (4 * n2)`] mp_tac)
    \\ fs [multiwordTheory.single_div_def]
    \\ impl_tac THEN1
     (unabbrev_all_tac
      \\ fs [lookup_insert,wordSemTheory.MustTerminate_limit_def,
             mc_multiwordTheory.single_div_pre_def]
      \\ fs [DIV_LT_X] \\ Cases_on `n2` \\ fs [MULT_CLAUSES])
    \\ rewrite_tac [DISJ_EQ_IMP]
    \\ strip_tac \\ fs []
    \\ fs [wordSemTheory.pop_env_def,Abbr `t2`]
    \\ reverse IF_CASES_TAC THEN1
     (sg `F` \\ fs [] \\ pop_assum mp_tac \\ fs []
      \\ drule env_to_list_domain
      \\ simp [domain_union,domain_fromAList_toAList,
               AC UNION_ASSOC UNION_COMM])
    \\ fs [list_Seq_def,eq_eval]
    \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [lookup_insert]
    \\ simp [state_rel_thm,lookup_insert,code_oracle_rel_def,FLOOKUP_UPDATE,
             adjust_var_11,dataSemTheory.call_env_def,alist_insert_def,
             push_env_def,dataSemTheory.set_var_def,wordSemTheory.set_vars_def]
    \\ fs [state_rel_thm,lookup_insert,code_oracle_rel_def,FLOOKUP_UPDATE,
           adjust_var_11,dataSemTheory.call_env_def,alist_insert_def,push_env_def,
           dataSemTheory.set_var_def,wordSemTheory.set_vars_def]
    \\ rveq \\ fs []
    \\ conj_tac THEN1
     (drule_all cut_envs_lookup_0
      \\ simp [lookup_union,lookup_fromAList,ALOOKUP_toAList])
    \\ conj_tac THEN1
     (gen_tac \\ IF_CASES_TAC \\ asm_simp_tac std_ss []
      \\ full_simp_tac std_ss [IS_SOME_lookup,domain_union] \\ strip_tac
      \\ drule_all IN_adjust_var_lemma \\ simp [])
    \\ conj_tac >- (
      qpat_x_assum `~_ ==> _` (strip_assume_tac o REWRITE_RULE [IMP_DISJ_THM])
      \\ rveq \\ fs []
      \\ fs [stack_size_eq2, wordSemTheory.stack_size_frame_def]
      \\ match_mp_tac option_le_trans \\ asm_exists_tac
      \\ fs [option_le_max_right])
    \\ conj_tac >- (
      rveq \\ fs [stack_consumed_def]
      \\ reverse IF_CASES_TAC THEN1 (fs [limits_inv_def] \\ rfs [])
      \\ fs [stack_size_eq2, wordSemTheory.stack_size_frame_def]
      \\ drule stack_rel_IMP_size_of_stack \\ simp[]
      \\ qpat_x_assum `~_ ==> _` (strip_assume_tac o REWRITE_RULE [IMP_DISJ_THM])
      \\ rveq \\ fs []
      \\ strip_tac \\ rw[option_le_max]
      >-
        (match_mp_tac option_le_trans
        \\ qexists_tac `s.stack_max`
        \\ fs [option_le_max_right, option_le_max])
      >-
        (simp[option_le_max_right]>>
        metis_tac [option_le_trans, option_le_add_comm])
      \\ rfs[option_le_max_right,option_le_max,stack_size_eq2,
           wordSemTheory.stack_size_frame_def,
           AC option_add_comm option_add_assoc]
      \\ simp[option_le_eq_eqns,option_le_max_right]
      \\ qmatch_goalsub_abbrev_tac `option_le xx (OPTION_MAP2 $+ _ (yy:num option))`
      \\ Cases_on `yy` THEN1 simp [OPTION_MAP2_DEF]
      \\ Cases_on `xx` \\ simp [OPTION_MAP2_DEF])
    \\ fs [inter_insert_ODD_adjust_set]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert
    \\ fs [FAPPLY_FUPDATE_THM,memory_rel_Temp]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ `n2w (4 * n1 DIV (4 * n2)) ≪ 2 = Smallnum (&(n1 DIV n2))` by
       (fs [wordsTheory.word_quot_def,word_div_def,Smallnum_def]
        \\ fs [WORD_MUL_LSL,word_mul_n2w,GSYM DIV_DIV_DIV_MULT,
               MULT_DIV |> ONCE_REWRITE_RULE [MULT_COMM]] \\ NO_TAC)
    \\ fs [] \\ match_mp_tac IMP_memory_rel_Number \\ fs []
    \\ imp_res_tac memory_rel_zero_space \\ fs [APPEND]
    \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
    \\ fs [] \\ rw [] \\ fs [] \\ disj1_tac
    \\ pop_assum mp_tac
    \\ fs [join_env_def,MEM_MAP,MEM_FILTER,FUN_EQ_THM]
    \\ simp [EXISTS_PROD]
    \\ strip_tac
    \\ rename1 `MEM (y_1,y_2) _`
    \\ qexistsl [`y_1`,`y_2`] \\ fs [MEM_toAList]
    \\ fs [lookup_inter_alt,lookup_union]
    \\ fs [cut_env_def,wordSemTheory.cut_envs_def] \\ rveq
    \\ fs [wordSemTheory.cut_names_def]
    \\ fs [lookup_inter_alt]
    \\ ‘lookup y_1 (fromAList (toAList y1)) = NONE’ by
     (qpat_x_assum ‘y_1 ≠ 0’ mp_tac
      \\ simp [lookup_fromAList,ALOOKUP_toAList]
      \\ qpat_x_assum ‘_ = SOME (y1,y2)’ mp_tac
      \\ rpt $ pop_assum kall_tac
      \\ gvs [adjust_sets_def,AllCaseEqs()]
      \\ rw [] \\ gvs [lookup_inter_alt])
    \\ fs [AllCaseEqs()]
    \\ drule0 env_to_list_lookup_equiv
    \\ fs [lookup_fromAList] \\ strip_tac \\ fs []
    \\ gvs [lookup_inter_alt,IN_domain_adjust_set_inter]
    \\ simp [IN_adjust_set_IN])
  (* these were lost through rewriting at the start of the proof *)
  \\ `get_vars [a1;a2] x.locals = SOME [(Number i1); (Number i2)]` by fs [get_vars_def]
  \\ `get_vars (MAP adjust_var [a1;a2]) t = SOME [(Word w1); (Word w2)]` by (
     fs [wordSemTheory.get_vars_def, wordSemTheory.get_var_def] \\ every_case_tac \\ fs [])
  \\ qpat_x_assum `state_rel c l1 l2 x t [] locs` (fn th => NTAC 2 (mp_tac th))
  \\ strip_tac
  \\ simp_tac std_ss [Once state_rel_thm] \\ strip_tac \\ fs [] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac \\ fs []
  \\ drule state_rel_IMP_arch_64_bit \\ strip_tac
  \\ `~(small_int (:'a) i1 ∧ small_int (:'a) i2 ∧ 0 <= i1 /\ 0 <= i2 /\
        small_int (:'a) (i1 / i2))` by
   (CCONTR_TAC \\ fs []
    \\ `~word_bit 0 w1` by (spose_not_then strip_assume_tac
                            \\ imp_res_tac memory_rel_small_int)
    \\ fs []
    \\ drule memory_rel_swap
    \\ strip_tac
    \\ `~word_bit 0 w2` by (spose_not_then strip_assume_tac
                            \\ imp_res_tac memory_rel_small_int)
    \\ fs []
    \\ first_x_assum (mp_then (Pos last) mp_tac (GEN_ALL memory_rel_Number_IMP))
    \\ first_x_assum (mp_then (Pos last) mp_tac (GEN_ALL memory_rel_Number_IMP))
    \\ rpt strip_tac \\ rfs []
    \\ imp_res_tac NONNEG_INT
    \\ fs [word_bit_or, word_bit_lsr_dimindex_1, small_int_def, Smallnum_def]
    \\ rveq
    \\ fs [word_msb_n2w_numeric, small_int_def,
       INT_MIN_def, good_dimindex_def, dimword_def] \\ rveq \\ fs []
    \\ rfs [] \\ fs [])
  \\ simp [stack_consumed_def,OPTION_MAP2_NONE,miscTheory.the_def,list_Seq_def]
  \\ unabbrev_all_tac
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,t4)`
  \\ `state_rel c l1 l2 x t4 [] locs` by
        (fs [Abbr`t4`,state_rel_thm,lookup_insert]
         \\ rfs [inter_insert_ODD_adjust_set_alt])
  \\ drule (GEN_ALL eval_Call_Div)
  \\ disch_then drule \\ simp [Abbr`t4`]
  \\ `dataSem$cut_state_opt names_opt x = SOME x` by
    (imp_res_tac cut_state_opt_twice \\ asm_rewrite_tac [])
  \\ `get_vars [a1; a2] x.locals = SOME [Number i1; Number i2]` by
        simp [get_vars_SOME_IFF_data]
  \\ disch_then drule \\ simp []
  \\ disch_then (strip_assume_tac o SPEC_ALL) \\ simp []
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ qpat_x_assum `_ = (_,_)` mp_tac
  \\ simp [list_Seq_def] \\ disch_then kall_tac
  \\ reverse (Cases_on `q = SOME NotEnoughSpace`)
  \\ simp[] THEN1
   (IF_CASES_TAC THEN1 (rfs [] \\ fs [])
    \\ first_x_assum drule \\ simp [state_rel_thm]
    \\ strip_tac \\ imp_res_tac data_to_word_gcProofTheory.stack_rel_IMP_size_of_stack
    \\ qpat_x_assum `option_le _ _` mp_tac \\ simp []
    \\ qpat_x_assum `option_le _ _` mp_tac \\ simp []
    \\ simp [AC option_add_comm option_add_assoc])
  \\ simp []
  \\ IF_CASES_TAC THEN1 (rfs [] \\ fs [])
  \\ conj_tac THEN1
   (rpt (qpat_x_assum `~(_ /\ _)` kall_tac)
    \\ fs [state_rel_thm]
    \\ imp_res_tac data_to_word_gcProofTheory.stack_rel_IMP_size_of_stack \\ fs []
    \\ imp_res_tac cut_state_opt_extra_const
    \\ fs [AC option_add_comm option_add_assoc])
  \\ strip_tac \\ disj1_tac
  \\ CCONTR_TAC
  \\ rpt (qpat_x_assum `~(_ /\ _)` mp_tac)
  \\ fs [] \\ disch_then kall_tac
  \\ fs [limits_inv_def] \\ rfs [] \\ fs []
  \\ fs [space_consumed_def] \\ rfs []
  \\ CCONTR_TAC \\ fs [] \\ fs []
QED

Theorem assign_Mod:
  op = (IntOp Mod) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [EVAL ``op_requires_names (IntOp Mod)``]
  \\ fs [do_app,oneline do_int_app_def]
  \\ gvs[AllCaseEqs()]
  \\ rename1 `get_vars args x.locals = SOME [Number i1; Number i2]`
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [assign_def]
  \\ fs [get_vars_SOME_IFF]
  \\ fs [get_vars_SOME_IFF_data]
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ rename1 `lookup (adjust_var a1) t.locals = SOME v1`
  \\ rename1 `lookup (adjust_var a2) t.locals = SOME v2`
  \\ `?w1. v1 = Word w1 /\
        (~(word_bit 0 w1) <=> small_int (:'a) i1) /\
        (~(word_msb w1) /\ ~(word_bit 0 w1) ==> 0 <= i1 /\ w1 = n2w (4 * Num i1))` by
          (metis_tac [state_rel_Number_IMP])
  \\ `?w2. v2 = Word w2 /\
        (~(word_bit 0 w2) <=> small_int (:'a) i2) /\
        (~(word_msb w2) /\ ~(word_bit 0 w2) ==> 0 <= i2 /\ w2 = n2w (4 * Num i2))` by
          (metis_tac [state_rel_Number_IMP])
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [eq_eval]
  \\ simp [word_bit_test_0]
  \\ IF_CASES_TAC THEN1
   (fs [word_bit_or,word_bit_lsr_dimindex_1] \\ rveq
    \\ `?n1. i1 = & n1` by (Cases_on `i1` \\ fs [])
    \\ `?n2. i2 = & n2` by (Cases_on `i2` \\ fs [])
    \\ fs [] \\ rveq
    \\ `4 * n2 < dimword (:'a) /\ 4 * n1 < dimword (:'a)` by
          fs [small_int_def,X_LT_DIV]
    \\ `n2w (4 * n2) <> 0w` by fs []
    \\ `small_int (:α) (&(n1 MOD n2))` by
     (fs [small_int_def,DIV_LT_X]
      \\ match_mp_tac LESS_TRANS
      \\ qexists_tac `n2` \\ fs [])
    \\ Cases_on `c.has_div` \\ fs [] THEN1
     (fs [list_Seq_def,eq_eval,wordSemTheory.inst_def,insert_shadow]
      \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [eq_eval]
      \\ simp [state_rel_thm,adjust_var_11,lookup_insert,code_oracle_rel_def,
               FLOOKUP_UPDATE,dataSemTheory.call_env_def,alist_insert_def,
               push_env_def,dataSemTheory.set_var_def,wordSemTheory.set_vars_def]
      \\ fs [state_rel_thm,adjust_var_11,lookup_insert,code_oracle_rel_def,
             FLOOKUP_UPDATE,dataSemTheory.call_env_def,alist_insert_def,
             push_env_def,dataSemTheory.set_var_def,wordSemTheory.set_vars_def]
      \\ conj_tac THEN1 (rw [] \\ fs [])
      \\ conj_tac >- rw [option_le_max_right]
      \\ fs [inter_insert_ODD_adjust_set]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
      \\ `(n2w (4 * n1) / n2w (4 * n2)) = n2w (n1 DIV n2)` by
       (fs [wordsTheory.word_quot_def,word_div_def,Smallnum_def]
        \\ fs [WORD_MUL_LSL,word_mul_n2w,GSYM DIV_DIV_DIV_MULT,
               MULT_DIV |> ONCE_REWRITE_RULE [MULT_COMM]])
      \\ fs [] \\ qmatch_goalsub_abbrev_tac `Word ww`
      \\ qsuff_tac `ww = Smallnum (&(n1 MOD n2))`
      THEN1 (rw [] \\ match_mp_tac IMP_memory_rel_Number \\ fs []
             \\ imp_res_tac memory_rel_zero_space \\ fs [])
      \\ fs [Abbr`ww`,Smallnum_def]
      \\ `(n1 DIV n2) < dimword (:α)` by
        (fs [DIV_LT_X] \\Cases_on `n2` \\ fs [MULT_CLAUSES] \\ NO_TAC)
      \\ fs [WORD_EQ_SUB_RADD |> SIMP_RULE (srw_ss()) []]
      \\ rewrite_tac [word_add_n2w] \\ AP_TERM_TAC
      \\ rewrite_tac [GSYM LEFT_ADD_DISTRIB] \\ AP_TERM_TAC
      \\ `0 < n2` by fs []
      \\ drule0 DIVISION
      \\ disch_then (qspec_then `n1` (fn th => simp [Once th])))
    \\ Cases_on `c.has_longdiv` \\ fs [] THEN1
     (fs [list_Seq_def,eq_eval,wordSemTheory.inst_def,insert_shadow]
      \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [eq_eval]
      \\ reverse IF_CASES_TAC THEN1
       (sg `F` \\ rfs [DIV_LT_X]
        \\ pop_assum mp_tac
        \\ Cases_on `n2` \\ fs [MULT_CLAUSES])
      \\ simp [state_rel_thm,adjust_var_11,lookup_insert,
               code_oracle_rel_def,FLOOKUP_UPDATE,push_env_def,
               dataSemTheory.call_env_def,alist_insert_def,
               dataSemTheory.set_var_def,wordSemTheory.set_vars_def]
      \\ fs [state_rel_thm,adjust_var_11,lookup_insert,code_oracle_rel_def,
             FLOOKUP_UPDATE,dataSemTheory.call_env_def,alist_insert_def,
             push_env_def,dataSemTheory.set_var_def,wordSemTheory.set_vars_def]
      \\ conj_tac THEN1 (rw [] \\ fs [])
      \\ conj_tac >- rw [option_le_max_right]
      \\ fs [inter_insert_ODD_adjust_set]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
      \\ `n2w ((4 * n1) MOD (4 * n2)) = Smallnum (&(n1 MOD n2))` by
       (fs [wordsTheory.word_quot_def,word_div_def,Smallnum_def]
        \\ fs [MOD_COMMON_FACTOR] \\ NO_TAC)
      \\ fs [] \\ match_mp_tac IMP_memory_rel_Number \\ fs []
      \\ imp_res_tac memory_rel_zero_space \\ fs [])
    \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
    \\ once_rewrite_tac [list_Seq_def] \\ fs []
    \\ once_rewrite_tac [wordSemTheory.evaluate_def]
    \\ rewrite_tac [insert_shadow]
    \\ qpat_x_assum `state_rel c l1 l2 x t [] locs`
          (mp_tac o REWRITE_RULE [state_rel_thm])
    \\ fs [] \\ strip_tac
    \\ fs [eq_eval,code_rel_def,stubs_def,cut_names_adjust_set_insert_1]
    \\ Cases_on `names_opt` \\ fs [cut_state_opt_def,cut_state_def]
    \\ Cases_on `dataSem$cut_env x' s.locals` \\ fs []
    \\ imp_res_tac cut_env_IMP_cut_env
    \\ drule_all cut_env_IMP_cut_envs \\ strip_tac \\ fs []
    \\ Cases_on `env_to_list y2 t.permute` \\ fs []
    \\ fs [get_names_def,wordSemTheory.push_env_def,domain_adjust_sets,
           cut_envs_adjust_sets_ODD]
    \\ qmatch_goalsub_abbrev_tac `evaluate (LongDiv_code c,t2)`
    \\ qspecl_then [`t2`,`n`,`l+1`,`c`] mp_tac evaluate_LongDiv_code'
    \\ fs [] \\ disch_then (qspecl_then [`0w`,`n2w (4 * n1)`,`n2w (4 * n2)`] mp_tac)
    \\ fs [multiwordTheory.single_div_def]
    \\ impl_tac THEN1
     (unabbrev_all_tac
      \\ fs [lookup_insert,wordSemTheory.MustTerminate_limit_def,
             mc_multiwordTheory.single_div_pre_def]
      \\ fs [DIV_LT_X] \\ Cases_on `n2` \\ fs [MULT_CLAUSES])
    \\ rewrite_tac [DISJ_EQ_IMP]
    \\ strip_tac \\ fs []
    \\ fs [wordSemTheory.pop_env_def,Abbr `t2`]
    \\ reverse IF_CASES_TAC THEN1
     (sg `F` \\ fs [] \\ pop_assum mp_tac \\ fs []
      \\ drule env_to_list_domain
      \\ simp [domain_union,domain_fromAList_toAList,
               AC UNION_ASSOC UNION_COMM])
    \\ fs [list_Seq_def,eq_eval]
    \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [lookup_insert]
    \\ simp [state_rel_thm,lookup_insert,code_oracle_rel_def,FLOOKUP_UPDATE,
             adjust_var_11,dataSemTheory.call_env_def,alist_insert_def,
             push_env_def,dataSemTheory.set_var_def,wordSemTheory.set_vars_def]
    \\ fs [state_rel_thm,lookup_insert,code_oracle_rel_def,FLOOKUP_UPDATE,
           adjust_var_11,dataSemTheory.call_env_def,alist_insert_def,push_env_def,
           dataSemTheory.set_var_def,wordSemTheory.set_vars_def,
           wordSemTheory.get_store_def]
    \\ rveq \\ fs []
    \\ conj_tac THEN1
     (drule_all cut_envs_lookup_0
      \\ simp [lookup_union,lookup_fromAList,ALOOKUP_toAList])
    \\ conj_tac THEN1
     (gen_tac \\ IF_CASES_TAC \\ asm_simp_tac std_ss []
      \\ full_simp_tac std_ss [IS_SOME_lookup,domain_union] \\ strip_tac
      \\ drule_all IN_adjust_var_lemma \\ simp [])
    \\ conj_tac >- (
      qpat_x_assum `~_ ==> _` (strip_assume_tac o REWRITE_RULE [IMP_DISJ_THM])
      \\ rveq \\ fs []
      \\ fs [stack_size_eq2, wordSemTheory.stack_size_frame_def]
      \\ match_mp_tac option_le_trans \\ asm_exists_tac
      \\ fs [option_le_max_right])
    \\ conj_tac >- (
      rveq \\ fs [stack_consumed_def]
      \\ reverse IF_CASES_TAC THEN1 (fs [limits_inv_def] \\ rfs [])
      \\ fs [stack_size_eq2, wordSemTheory.stack_size_frame_def]
      \\ drule stack_rel_IMP_size_of_stack \\ simp[]
      \\ qpat_x_assum `~_ ==> _` (strip_assume_tac o REWRITE_RULE [IMP_DISJ_THM])
      \\ rveq \\ fs []
      \\ strip_tac \\ rw[option_le_max]
      >-
        (match_mp_tac option_le_trans
        \\ qexists_tac `s.stack_max`
        \\ fs [option_le_max_right, option_le_max])
      >-
        (simp[option_le_max_right]>>
        metis_tac [option_le_trans, option_le_add_comm])
      \\ rfs[option_le_max_right,option_le_max,stack_size_eq2,
           wordSemTheory.stack_size_frame_def,
           AC option_add_comm option_add_assoc]
      \\ simp[option_le_eq_eqns,option_le_max_right]
      \\ qmatch_goalsub_abbrev_tac `option_le xx (OPTION_MAP2 $+ _ (yy:num option))`
      \\ Cases_on `yy` THEN1 simp [OPTION_MAP2_DEF]
      \\ Cases_on `xx` \\ simp [OPTION_MAP2_DEF])
    \\ fs [inter_insert_ODD_adjust_set]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert
    \\ fs [FAPPLY_FUPDATE_THM,memory_rel_Temp]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ `n2w ((4 * n1) MOD (4 * n2)) = Smallnum (&(n1 MOD n2))` by
       (fs [wordsTheory.word_quot_def,word_div_def,Smallnum_def]
        \\ fs [MOD_COMMON_FACTOR])
    \\ fs [] \\ match_mp_tac IMP_memory_rel_Number \\ fs []
    \\ imp_res_tac memory_rel_zero_space \\ fs [APPEND]
    \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
    \\ fs [] \\ rw [] \\ fs [] \\ disj1_tac
    \\ pop_assum mp_tac
    \\ fs [join_env_def,MEM_MAP,MEM_FILTER,FUN_EQ_THM]
    \\ simp [EXISTS_PROD]
    \\ strip_tac
    \\ rename1 `MEM (y_1,y_2) _`
    \\ qexistsl [`y_1`,`y_2`] \\ fs [MEM_toAList]
    \\ fs [lookup_inter_alt,lookup_union]
    \\ fs [cut_env_def,wordSemTheory.cut_envs_def] \\ rveq
    \\ fs [wordSemTheory.cut_names_def]
    \\ fs [lookup_inter_alt]
    \\ ‘lookup y_1 (fromAList (toAList y1)) = NONE’ by
     (qpat_x_assum ‘y_1 ≠ 0’ mp_tac
      \\ simp [lookup_fromAList,ALOOKUP_toAList]
      \\ qpat_x_assum ‘_ = SOME (y1,y2)’ mp_tac
      \\ rpt $ pop_assum kall_tac
      \\ gvs [adjust_sets_def,AllCaseEqs()]
      \\ rw [] \\ gvs [lookup_inter_alt])
    \\ fs [AllCaseEqs()]
    \\ drule0 env_to_list_lookup_equiv
    \\ fs [lookup_fromAList] \\ strip_tac \\ fs []
    \\ gvs [lookup_inter_alt,IN_domain_adjust_set_inter]
    \\ simp [IN_adjust_set_IN])
  (* these were lost through rewriting at the start of the proof *)
  \\ `get_vars [a1;a2] x.locals = SOME [(Number i1); (Number i2)]` by fs [get_vars_def]
  \\ `get_vars (MAP adjust_var [a1;a2]) t = SOME [(Word w1); (Word w2)]` by (
     fs [wordSemTheory.get_vars_def, wordSemTheory.get_var_def] \\ every_case_tac \\ fs [])
  \\ qpat_x_assum `state_rel c l1 l2 x t [] locs` (fn th => NTAC 2 (mp_tac th))
  \\ strip_tac
  \\ simp_tac std_ss [Once state_rel_thm] \\ strip_tac \\ fs [] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac \\ fs []
  \\ drule state_rel_IMP_arch_64_bit \\ strip_tac
  \\ `~(small_int (:'a) i1 ∧ small_int (:'a) i2 ∧ 0 <= i1 /\ 0 <= i2 /\
        small_int (:'a) (i1 % i2))` by
   (CCONTR_TAC \\ fs []
    \\ `~word_bit 0 w1` by (spose_not_then strip_assume_tac
                            \\ imp_res_tac memory_rel_small_int)
    \\ fs []
    \\ drule memory_rel_swap
    \\ strip_tac
    \\ `~word_bit 0 w2` by (spose_not_then strip_assume_tac
                            \\ imp_res_tac memory_rel_small_int)
    \\ fs []
    \\ first_x_assum (mp_then (Pos last) mp_tac (GEN_ALL memory_rel_Number_IMP))
    \\ first_x_assum (mp_then (Pos last) mp_tac (GEN_ALL memory_rel_Number_IMP))
    \\ rpt strip_tac \\ rfs []
    \\ imp_res_tac NONNEG_INT
    \\ fs [word_bit_or, word_bit_lsr_dimindex_1, small_int_def, Smallnum_def]
    \\ rveq
    \\ fs [word_msb_n2w_numeric, small_int_def,
       INT_MIN_def, good_dimindex_def, dimword_def] \\ rveq \\ fs [] \\ rfs [] \\ fs [])
  \\ simp [stack_consumed_def,OPTION_MAP2_NONE,miscTheory.the_def,list_Seq_def]
  \\ unabbrev_all_tac
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,t4)`
  \\ `state_rel c l1 l2 x t4 [] locs` by
        (fs [Abbr`t4`,state_rel_thm,lookup_insert]
         \\ rfs [inter_insert_ODD_adjust_set_alt])
  \\ drule (GEN_ALL eval_Call_Mod)
  \\ disch_then drule \\ simp [Abbr`t4`]
  \\ `dataSem$cut_state_opt names_opt x = SOME x` by
    (imp_res_tac cut_state_opt_twice \\ asm_rewrite_tac [])
  \\ `get_vars [a1; a2] x.locals = SOME [Number i1; Number i2]` by
        simp [get_vars_SOME_IFF_data]
  \\ disch_then drule \\ simp []
  \\ disch_then (strip_assume_tac o SPEC_ALL) \\ simp []
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ qpat_x_assum `_ = (_,_)` mp_tac
  \\ simp [list_Seq_def] \\ disch_then kall_tac
  \\ reverse (Cases_on `q = SOME NotEnoughSpace`)
  \\ simp[] THEN1
   (IF_CASES_TAC THEN1 (rfs [] \\ fs [])
    \\ first_x_assum drule \\ simp [state_rel_thm]
    \\ strip_tac \\ imp_res_tac data_to_word_gcProofTheory.stack_rel_IMP_size_of_stack
    \\ qpat_x_assum `option_le _ _` mp_tac \\ simp []
    \\ qpat_x_assum `option_le _ _` mp_tac \\ simp []
    \\ simp [AC option_add_comm option_add_assoc])
  \\ simp []
  \\ IF_CASES_TAC THEN1 (rfs [] \\ fs [])
  \\ conj_tac THEN1
   (rpt (qpat_x_assum `~(_ /\ _)` kall_tac)
    \\ fs [state_rel_thm]
    \\ imp_res_tac data_to_word_gcProofTheory.stack_rel_IMP_size_of_stack \\ fs []
    \\ imp_res_tac cut_state_opt_extra_const
    \\ fs [AC option_add_comm option_add_assoc])
  \\ strip_tac \\ disj1_tac
  \\ CCONTR_TAC
  \\ rpt (qpat_x_assum `~(_ /\ _)` mp_tac)
  \\ fs [] \\ disch_then kall_tac
  \\ fs [limits_inv_def] \\ rfs [] \\ fs []
  \\ fs [space_consumed_def] \\ rfs []
  \\ CCONTR_TAC \\ fs [] \\ fs []
QED

Theorem assign_LengthByte:
   op = MemOp LengthByte ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app, allowed_op_def] \\ rfs [] \\ every_case_tac \\ fs []
  \\ rveq \\ fs [state_fn_updates]
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_1] \\ clean_tac
  \\ fs [get_var_def]
  \\ simp [state_rel_thm] \\ eval_tac
  \\ fs [state_rel_thm] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ rpt_drule0 memory_rel_ByteArray_IMP \\ fs []
  \\ qpat_abbrev_tac`ttt = COND _ _ _`
  \\ rw []
  \\ fs [assign_def]
  \\ fs [wordSemTheory.get_vars_def]
  \\ Cases_on `get_var (adjust_var a1) t` \\ fs [] \\ clean_tac
  \\ eval_tac
  \\ fs [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def]
  \\ fs [asmTheory.word_cmp_def,word_and_one_eq_0_iff
           |> SIMP_RULE (srw_ss()) []]
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ `word_exp t (real_addr c (adjust_var a1)) = SOME (Word a)` by (
    match_mp_tac (GEN_ALL get_real_addr_lemma)
    \\ fs [wordSemTheory.get_var_def] \\ NO_TAC) \\ fs []
  \\ IF_CASES_TAC
  >- ( fs[good_dimindex_def] \\ rfs[shift_def] )
  \\ pop_assum kall_tac
  \\ simp[]
  \\ `2 < dimindex (:'a)` by (
    fs [good_dimindex_def] \\ fs [])
  \\ fs [] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
  >- fs [option_le_max_right]
  \\ fs [WORD_MUL_LSL,WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w]
  \\ fs [word_mul_n2w]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ fs[good_dimindex_def,markerTheory.Abbrev_def]
  \\ rfs[shift_def,bytes_in_word_def,WORD_LEFT_ADD_DISTRIB,word_mul_n2w]
  \\ match_mp_tac (IMP_memory_rel_Number_num3
       |> SIMP_RULE std_ss [WORD_MUL_LSL,word_mul_n2w]) \\ fs []
  \\ fs[good_dimindex_def]
QED

Theorem assign_Length:
   op = MemOp Length ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app, allowed_op_def] \\ rfs [] \\ every_case_tac \\ fs []
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_1] \\ clean_tac
  \\ fs [get_var_def]
  \\ simp [state_rel_thm] \\ eval_tac
  \\ fs [state_rel_thm] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ rpt_drule0 memory_rel_ValueArray_IMP \\ fs [] \\ rw []
  \\ fs [assign_def]
  \\ fs [wordSemTheory.get_vars_def]
  \\ Cases_on `get_var (adjust_var a1) t` \\ fs [] \\ clean_tac
  \\ eval_tac
  \\ fs [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def]
  \\ fs [asmTheory.word_cmp_def,word_and_one_eq_0_iff
           |> SIMP_RULE (srw_ss()) []]
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ `word_exp t (real_addr c (adjust_var a1)) = SOME (Word a)` by
       (match_mp_tac (GEN_ALL get_real_addr_lemma)
        \\ fs [wordSemTheory.get_var_def] \\ NO_TAC) \\ fs []
  \\ fs [GSYM NOT_LESS,GREATER_EQ]
  \\ `c.len_size <> 0` by
      (fs [memory_rel_def,heap_in_memory_store_def] \\ NO_TAC)
  \\ fs [NOT_LESS]
  \\ `~(dimindex (:α) <= 2)` by
         (fs [good_dimindex_def] \\ NO_TAC)
  \\ fs [] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
  >- fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ fs [decode_length_def]
  \\ match_mp_tac IMP_memory_rel_Number_num \\ fs []
QED

Theorem assign_LengthBlock:
   op = BlockOp LengthBlock ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app, allowed_op_def] \\ rfs [] \\ every_case_tac \\ fs []
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_1] \\ clean_tac
  \\ fs [get_var_def]
  \\ simp [state_rel_thm] \\ eval_tac
  \\ fs [state_rel_thm] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ drule0 memory_rel_Block_IMP \\ fs [] \\ rw []
  \\ fs [assign_def]
  \\ fs [wordSemTheory.get_vars_def]
  \\ Cases_on `get_var (adjust_var a1) t` \\ fs [] \\ clean_tac
  \\ eval_tac
  \\ fs [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def]
  \\ fs [asmTheory.word_cmp_def,word_and_one_eq_0_iff
           |> SIMP_RULE (srw_ss()) []]
  \\ reverse (Cases_on `w ' 0`) \\ fs [] THEN1
   (fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
    >- fs [option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ match_mp_tac (IMP_memory_rel_Number |> Q.INST [`i`|->`0`]
          |> SIMP_RULE std_ss [EVAL ``Smallnum 0``])
    \\ fs [] \\ fs [good_dimindex_def,dimword_def]
    \\ EVAL_TAC \\ rw [good_dimindex_def,dimword_def])
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ `word_exp t (real_addr c (adjust_var a1)) = SOME (Word a)` by
       (match_mp_tac (GEN_ALL get_real_addr_lemma)
        \\ fs [wordSemTheory.get_var_def] \\ NO_TAC) \\ fs []
  \\ fs [GSYM NOT_LESS,GREATER_EQ]
  \\ `c.len_size <> 0` by
      (fs [memory_rel_def,heap_in_memory_store_def] \\ NO_TAC)
  \\ fs [NOT_LESS]
  \\ `~(dimindex (:α) <= 2)` by
         (fs [good_dimindex_def] \\ NO_TAC)
  \\ fs [] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
  >- fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ fs [decode_length_def]
  \\ match_mp_tac IMP_memory_rel_Number_num \\ fs []
QED

Theorem assign_BoundsCheckBlock:
   assign c secn l dest (BlockOp BoundsCheckBlock) args names =
      case args of
      | [v1;v2] => (list_Seq [If Test (adjust_var v1) (Imm 1w)
                               (Assign 1 (Const 0w))
                               (Assign 1
                                 (let addr = real_addr c (adjust_var v1) in
                                  let header = Load addr in
                                  let k = dimindex (:'a) - c.len_size in
                                    Shift Lsr header k));
                              Assign 3 (ShiftVar Ror (adjust_var v2) 2);
                              If Lower 3 (Reg 1)
                               (Assign (adjust_var dest) TRUE_CONST)
                               (Assign (adjust_var dest) FALSE_CONST)],l)
      | _ => (Skip:'a wordLang$prog,l)
Proof
  fs [assign_def] \\ every_case_tac \\ fs []
QED

Theorem assign_BoundsCheckBlock[allow_rebind]:
   op = BlockOp BoundsCheckBlock ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app,allowed_op_def] \\ rfs [] \\ every_case_tac \\ fs []
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [get_var_def]
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
    \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
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
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
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

Theorem assign_BoundsCheckArray:
   assign c secn l dest (MemOp BoundsCheckArray) args names =
      case args of
      | [v1;v2] => (list_Seq [Assign 1
                               (let addr = real_addr c (adjust_var v1) in
                                let header = Load addr in
                                let k = dimindex (:'a) - c.len_size in
                                  Shift Lsr header k);
                              Assign 3 (ShiftVar Ror (adjust_var v2) 2);
                              If Lower 3 (Reg 1)
                               (Assign (adjust_var dest) TRUE_CONST)
                               (Assign (adjust_var dest) FALSE_CONST)],l)
      | _ => (Skip:'a wordLang$prog,l)
Proof
  fs [assign_def] \\ every_case_tac \\ fs []
QED

Theorem assign_BoundsCheckArray[allow_rebind]:
   op = MemOp BoundsCheckArray ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app,allowed_op_def] \\ rfs [] \\ every_case_tac \\ fs []
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [get_var_def]
  \\ simp [state_rel_thm] \\ eval_tac
  \\ fs [state_rel_thm,option_le_max_right] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ drule0 (GEN_ALL memory_rel_ValueArray_IMP) \\ fs [] \\ rw []
  \\ fs [assign_BoundsCheckArray]
  \\ fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF]
  \\ qmatch_asmsub_rename_tac `(Number i,w2)`
  \\ `?wi. w2 = Word wi` by
    (drule0 memory_rel_tl \\ strip_tac
     \\ imp_res_tac memory_rel_any_Number_IMP \\ simp [] \\ NO_TAC)
  \\ rveq
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [eq_eval]
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ `word_exp t (real_addr c (adjust_var a1)) = SOME (Word a)` by
       (match_mp_tac (GEN_ALL get_real_addr_lemma)
        \\ fs [wordSemTheory.get_var_def] \\ NO_TAC) \\ fs []
  \\ fs [eq_eval,word_sh_def]
  \\ fs [list_Seq_def,eq_eval]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
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

Theorem assign_BoundsCheckByte:
   assign c secn l dest (MemOp (BoundsCheckByte leq)) args names =
      case args of
      | [v1;v2] => (list_Seq [Assign 1
                               (let addr = real_addr c (adjust_var v1) in
                                let header = Load addr in
                                let extra = (if dimindex (:'a) = 32 then 2 else 3) in
                                let k = dimindex (:'a) - c.len_size - extra in
                                  Op Sub [Shift Lsr header k; Const bytes_in_word]);
                              Assign 3 (ShiftVar Ror (adjust_var v2) 2);
                              (if leq then If NotLower 1 (Reg 3) else
                                           If Lower 3 (Reg 1))
                               (Assign (adjust_var dest) TRUE_CONST)
                               (Assign (adjust_var dest) FALSE_CONST)],l)
      | _ => (Skip:'a wordLang$prog,l)
Proof
  fs [assign_def] \\ every_case_tac \\ fs []
QED

Theorem assign_BoundsCheckByte[allow_rebind]:
   (?leq. op = MemOp (BoundsCheckByte leq)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app,allowed_op_def] \\ rfs [] \\ every_case_tac \\ fs []
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [get_var_def]
  \\ simp [state_rel_thm] \\ eval_tac
  \\ fs [state_rel_thm,option_le_max_right] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ drule0 (GEN_ALL memory_rel_ByteArray_IMP) \\ fs [] \\ rw []
  \\ fs [assign_BoundsCheckByte]
  \\ fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF]
  \\ qmatch_asmsub_rename_tac `(Number i,w2)`
  \\ `?wi. w2 = Word wi` by
    (drule0 memory_rel_tl \\ strip_tac
     \\ imp_res_tac memory_rel_any_Number_IMP \\ simp [] \\ NO_TAC)
  \\ rveq
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [eq_eval]
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ `word_exp t (real_addr c (adjust_var a1)) = SOME (Word a)` by
       (match_mp_tac (GEN_ALL get_real_addr_lemma)
        \\ fs [wordSemTheory.get_var_def] \\ NO_TAC) \\ fs []
  \\ fs [eq_eval,word_sh_def]
  \\ fs [list_Seq_def,eq_eval]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
  \\ `c.len_size < dimindex (:α) /\
      ~(dimindex (:α) ≥ c.len_size + dimindex (:α))` by
         (fs [memory_rel_def,heap_in_memory_store_def] \\ NO_TAC)
  \\ fs [eq_eval,WORD_LO_word_0,adjust_var_11]
  \\ fs [good_dimindex_def] \\ rfs []
  \\ fs [decode_length_def,wordsTheory.WORD_NOT_LOWER]
  \\ drule0 memory_rel_tl \\ strip_tac
  \\ drule0 (GEN_ALL memory_rel_bounds_check)
  \\ disch_then (qspec_then `LENGTH l'` mp_tac)
  \\ impl_tac
  \\ TRY (fs [small_int_def,dimword_def,good_dimindex_def] \\ rfs [] \\ NO_TAC)
  \\ fs [GSYM word_add_n2w]
  \\ strip_tac \\ fs [bytes_in_word_def]
  \\ IF_CASES_TAC
  \\ fs [] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
  \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
  \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [])
  \\ fs [good_dimindex_def]
QED

Theorem assign_LessConstSmall:
   assign c secn l dest (IntOp (LessConstSmall i)) args names =
      case args of
      | [v1] => (If Less (adjust_var v1) (Imm (n2w (4 * i)))
                  (Assign (adjust_var dest) TRUE_CONST)
                  (Assign (adjust_var dest) FALSE_CONST),l)
      | _ => (Skip:'a wordLang$prog,l)
Proof
  fs [assign_def] \\ every_case_tac \\ fs []
QED

Theorem assign_LessSmallConst[allow_rebind]:
   (?i. op = IntOp (LessConstSmall i)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app,oneline do_int_app_def]
  \\ gvs[AllCaseEqs()]
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_1] \\ clean_tac
  \\ fs [get_var_def]
  \\ fs [state_rel_thm] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ `?k. i' = &k` by (Cases_on `i'` \\ fs [] \\ NO_TAC) \\ rveq \\ fs []
  \\ `small_int (:'a) (&k)` by
       (fs [small_int_def,good_dimindex_def,dimword_def] \\ NO_TAC)
  \\ imp_res_tac memory_rel_Number_IMP \\ fs [] \\ rveq \\ fs []
  \\ fs [assign_LessConstSmall]
  \\ fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF]
  \\ fs [eq_eval,WORD_LO_word_0,adjust_var_11]
  \\ fs [Smallnum_def]
  \\ `n2w (4 * k) < (n2w (4 * i):'a word) <=> k < i` by
    (fs [word_lt_n2w,bitTheory.BIT_def,bitTheory.BITS_THM]
     \\ fs [good_dimindex_def,LESS_DIV_EQ_ZERO,dimword_def] \\ NO_TAC)
  \\ fs []
  \\ qpat_abbrev_tac `bool_res <=> k < i`
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
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
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
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
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
  \\ ‘(16w * n2w tag = 16w * n2w tag' :α word) ⇔  (tag = 1 ⇔ tag' = 1)’ by
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

Theorem assign_WordTest[allow_rebind]:
  (∃ws test. op = WordOp (WordTest ws test)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
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

Theorem Compare1_code_thm:
   !l a1 a2 dm m res (t:('a,'c,'ffi) wordSem$state).
      word_cmp_loop l a1 a2 dm m = SOME res /\
      dm = t.mdomain /\
      m = t.memory /\
      lookup Compare1_location t.code = SOME (4,Compare1_code) /\
      lookup Compare1_location t.stack_size = t.locals_size ∧
      get_var 0 t = SOME (Loc l1 l2) /\
      get_var 2 t = SOME (Word l) /\
      get_var 4 t = SOME (Word a1) /\
      get_var 6 t = SOME (Word a2) /\
      w2n l <= t.clock ==>
      ?ck smx.
        evaluate (Compare1_code,t) =
          (SOME (Result (Loc l1 l2) [Word res]),
           t with <| clock := ck; locals := LN ; locals_size := SOME 0;
                     stack_max := smx |>) /\
        option_le smx (OPTION_MAP2 MAX t.stack_max
                                       (OPTION_MAP2 $+ (stack_size t.stack) t.locals_size)) /\
        t.clock <= w2n l + ck
Proof
  ho_match_mp_tac word_cmp_loop_ind \\ rw []
  \\ qpat_assum `_ = SOME res` mp_tac
  \\ once_rewrite_tac [word_cmp_loop_def,Compare1_code_def]
  \\ IF_CASES_TAC \\ fs [] \\ strip_tac \\ rveq
  THEN1
   (eval_tac \\ fs [wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,
      wordSemTheory.get_var_def,lookup_insert,wordSemTheory.call_env_def,
      wordSemTheory.get_vars_def, wordSemTheory.flush_state_def,
      fromList2_def,wordSemTheory.state_component_equality]
    \\ fs[option_le_max_right])
  \\ every_case_tac \\ fs [wordsTheory.WORD_LOWER_REFL] \\ rveq
  THEN1
   (fs [list_Seq_def]
    \\ eval_tac \\ fs [wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,
         wordSemTheory.get_var_def,lookup_insert,wordSemTheory.call_env_def,
         wordSemTheory.get_vars_def, wordSemTheory.flush_state_def,
         fromList2_def,wordSemTheory.state_component_equality]
    \\ fs[option_le_max_right])
  \\ `t.clock <> 0` by (Cases_on `l` \\ fs [] \\ NO_TAC)
  \\ fs [list_Seq_def]
  \\ eval_tac \\ fs [wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,
         wordSemTheory.get_var_def,lookup_insert,wordSemTheory.call_env_def,
         fromList2_def,wordSemTheory.state_component_equality,
         wordSemTheory.get_vars_def,wordSemTheory.bad_dest_args_def,
         wordSemTheory.add_ret_loc_def,wordSemTheory.find_code_def,
         wordSemTheory.flush_state_def,option_le_max_right]
  \\ qmatch_goalsub_abbrev_tac`evaluate (Compare1_code,t1)`
  \\ rfs []
  \\ first_x_assum (qspec_then `t1` mp_tac)
  \\ impl_tac THEN1
   (unabbrev_all_tac
    \\ fs [wordSemTheory.dec_clock_def,lookup_insert]
    \\ Cases_on `l` \\ fs []
    \\ Cases_on `n` \\ fs [GSYM word_add_n2w,ADD1])
  \\ strip_tac \\ fs [wordSemTheory.state_component_equality]
  \\ unabbrev_all_tac \\ fs [wordSemTheory.dec_clock_def,lookup_insert]
  \\ Cases_on `l` \\ fs []
  \\ Cases_on `n` \\ fs [ADD1,GSYM word_add_n2w]
  \\ fs[option_le_max_right]
QED

Theorem word_exp_insert:
   (m <> n ==>
     (word_exp (t with locals := insert n w t.locals) (real_addr c m) =
      word_exp t (real_addr c m))) /\
    (~(m IN {n;n1}) ==>
     (word_exp (t with locals := insert n w (insert n1 w1 t.locals)) (real_addr c m) =
      word_exp t (real_addr c m)))
Proof
  fs [wordSemTheory.word_exp_def,real_addr_def,wordSemTheory.get_store_def]
  \\ rpt (IF_CASES_TAC \\ fs [])
  \\ fs [wordSemTheory.word_exp_def,real_addr_def,
         wordSemTheory.get_store_def,
         wordSemTheory.get_var_def] \\ fs [lookup_insert]
QED

Theorem Compare_code_thm:
   memory_rel c be ts refs sp st m dm
      ((Number i1,Word v1)::(Number i2,Word v2)::vars) /\
    dm = (t:('a,'c,'ffi) wordSem$state).mdomain /\
    m = t.memory /\
    st = t.store /\
    (~word_bit 0 v1 ==> word_bit 0 v2) /\
    shift_length c < dimindex (:'a) /\
    lookup Compare1_location t.code = SOME (4,Compare1_code) /\
    get_var 0 t = SOME (Loc l1 l2) /\
    get_var 2 t = SOME (Word (v1:'a word)) /\
    get_var 4 t = SOME (Word (v2:'a word)) /\
    dimword (:'a) < t.clock /\
    c.len_size <> 0 /\
    c.len_size < dimindex (:α) /\
    good_dimindex (:'a) ==>
    ?ck smx.
      evaluate (Compare_code c,t) =
        (SOME (Result (Loc l1 l2) [Word (word_cmp_res i1 i2)]),
         t with <| clock := ck; locals := LN; locals_size := SOME 0;
                   stack_max := smx|>) /\
        option_le smx (OPTION_MAP2 MAX
                         t.stack_max
                           (OPTION_MAP2 $+ (stack_size t.stack)
                                           (lookup Compare1_location t.stack_size)))
Proof
  rw [] \\ drule0 memory_rel_Number_cmp
  \\ fs [] \\ strip_tac \\ fs []
  \\ pop_assum mp_tac
  \\ IF_CASES_TAC THEN1 fs []
  \\ pop_assum kall_tac
  \\ IF_CASES_TAC THEN1
   (fs [] \\ rw [] \\ fs [Compare_code_def]
    \\ rpt_drule0 get_real_addr_lemma \\ rw []
    \\ fs [list_Seq_def]
    \\ eval_tac \\ fs [wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,
         wordSemTheory.get_var_def,wordSemTheory.get_vars_def,
         lookup_insert,wordSemTheory.call_env_def,
         fromList2_def,wordSemTheory.state_component_equality,word_bit_test,
         wordSemTheory.flush_state_def,option_le_max_right])
  \\ pop_assum mp_tac \\ fs []
  \\ Cases_on `word_bit 0 v1` \\ fs []
  \\ reverse (Cases_on `word_bit 0 v2`) \\ fs []
  THEN1
   (`memory_rel c be ts refs sp t.store t.memory t.mdomain
        ((Number i2,Word v2)::(Number i1,Word v1)::vars)` by
     (first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
      \\ fs [] \\ rw [] \\ fs [])
    \\ drule0 memory_rel_Number_cmp
    \\ fs [] \\ strip_tac \\ fs []
    \\ `word_cmp_res i1 i2 = if (16w && x2) = 0w then 2w else 0w:'a word` by
     (fs [word_cmp_res_def] \\ rfs []
      \\ rw [] \\ fs []
      \\ Cases_on `i2 < i1` \\ fs [] \\ intLib.COOPER_TAC)
    \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
    \\ qpat_assum `_ = SOME (Word v1)` assume_tac
    \\ fs [Compare_code_def]
    \\ rpt_drule0 get_real_addr_lemma \\ rw []
    \\ fs [list_Seq_def]
    \\ eval_tac \\ fs [wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,
         wordSemTheory.get_var_def,wordSemTheory.get_vars_def,
         lookup_insert,wordSemTheory.call_env_def,
         fromList2_def,wordSemTheory.state_component_equality,word_bit_test,
         option_le_max_right,wordSemTheory.flush_state_def])
  \\ `shift (:'a) <> 0 /\ shift (:'a) < dimindex (:'a)` by
          (fs [good_dimindex_def,shift_def] \\ NO_TAC)
  \\ strip_tac \\ fs []
  \\ Cases_on `x1 = x2` \\ fs [] \\ rveq
  THEN1
   (pop_assum mp_tac \\ IF_CASES_TAC \\ fs [] \\ strip_tac
    \\ rpt_drule0 get_real_addr_lemma \\ rw []
    \\ qpat_assum `_ = SOME (Word v1)` assume_tac
    \\ rpt_drule0 get_real_addr_lemma \\ rw []
    \\ fs [Compare_code_def]
    \\ fs [list_Seq_def]
    \\ eval_tac \\ fs [wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,
         lookup_insert,wordSemTheory.call_env_def,
         fromList2_def,wordSemTheory.state_component_equality,word_bit_test,
         word_exp_insert,wordSemTheory.get_vars_def,
         wordSemTheory.get_var_def,lookup_insert,wordSemTheory.call_env_def,
         fromList2_def,wordSemTheory.state_component_equality,
         wordSemTheory.get_vars_def,wordSemTheory.bad_dest_args_def,
         wordSemTheory.add_ret_loc_def,wordSemTheory.find_code_def]
    \\ qpat_abbrev_tac `t1 = _ with locals := _`
    \\ drule0 Compare1_code_thm
    \\ fs [GSYM decode_length_def]
    \\ disch_then (qspec_then `t1` mp_tac)
    \\ impl_tac
    \\ TRY
     (strip_tac \\ fs [] \\ unabbrev_all_tac
      \\ fs [wordSemTheory.state_component_equality,wordSemTheory.dec_clock_def]
      \\ NO_TAC)
    \\ fs [] \\ unabbrev_all_tac
    \\ fs [wordSemTheory.state_component_equality,wordSemTheory.dec_clock_def,
           wordSemTheory.get_var_def,lookup_insert,shift_lsl]
    \\ Cases_on `decode_length c x1` \\ fs [])
  \\ rpt_drule0 get_real_addr_lemma \\ rw []
  \\ qpat_assum `_ = SOME (Word v1)` assume_tac
  \\ rpt_drule0 get_real_addr_lemma \\ rw []
  \\ rpt IF_CASES_TAC
  \\ fs [Compare_code_def,list_Seq_def]
  \\ eval_tac \\ fs [wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,
       wordSemTheory.get_var_def,lookup_insert,wordSemTheory.call_env_def,
       fromList2_def,wordSemTheory.state_component_equality,word_bit_test,
       word_exp_insert,GSYM decode_length_def,wordSemTheory.flush_state_def,
       wordSemTheory.get_vars_def,option_le_max_right]
QED

Theorem word_cmp_Less_word_cmp_res:
   !i i'. good_dimindex (:'a) ==>
           (word_cmp Less (word_cmp_res i i') (1w:'a word) <=> i < i')
Proof
  rw [] \\ fs [good_dimindex_def]
  \\ fs [word_cmp_res_def,asmTheory.word_cmp_def]
  \\ rw [] \\ fs [WORD_LT] \\ fs [word_msb_def,word_index,dimword_def]
QED

Theorem word_cmp_NotLess_word_cmp_res:
   !i i'. good_dimindex (:'a) ==>
           (word_cmp NotLess (1w:'a word) (word_cmp_res i i') <=> (i <= i'))
Proof
  rw [] \\ fs [good_dimindex_def]
  \\ fs [word_cmp_res_def,asmTheory.word_cmp_def]
  \\ rw [] \\ fs [WORD_LT] \\ fs [word_msb_def,word_index,dimword_def]
  \\ intLib.COOPER_TAC
QED

Theorem word_cmp_not_NotLess_word_cmp_res:
   !i i'. good_dimindex (:'a) ==>
           (~word_cmp NotLess (1w:'a word) (word_cmp_res i i') <=> (i' < i))
Proof
  rw [] \\ fs [good_dimindex_def]
  \\ fs [word_cmp_res_def,asmTheory.word_cmp_def]
  \\ rw [] \\ fs [WORD_LT] \\ fs [word_msb_def,word_index,dimword_def]
  \\ intLib.COOPER_TAC
QED

Theorem not_word_cmp_Less_word_cmp_res:
   !i i'. good_dimindex (:'a) ==>
           (~word_cmp Less (word_cmp_res i i') (1w:'a word) <=> (i' <= i))
Proof
  rw [] \\ fs [good_dimindex_def]
  \\ fs [word_cmp_res_def,asmTheory.word_cmp_def]
  \\ rw [] \\ fs [WORD_LT] \\ fs [word_msb_def,word_index,dimword_def]
  \\ intLib.COOPER_TAC
QED

Theorem IMP_spt_eq:
   wf t1 /\ wf t2 /\ (∀n. lookup n t1 = lookup n t2) ==> (t1 = t2)
Proof
  metis_tac [spt_eq_thm]
QED

Theorem env_to_list_cut_env_IMP:
   env_to_list x t.permute = (l,permute) /\ cut_env y s = SOME x ==>
    (fromAList l = x)
Proof
  strip_tac \\ match_mp_tac IMP_spt_eq
  \\ fs [wf_fromAList]
  \\ drule0 env_to_list_lookup_equiv
  \\ fs [lookup_fromAList]
  \\ fs [wordSemTheory.cut_env_def] \\ rveq \\ rw []
  \\ gvs [wordSemTheory.cut_envs_def,AllCaseEqs(),wordSemTheory.cut_names_def]
  \\ irule wf_union \\ rpt conj_tac \\ irule wf_inter
QED

Theorem dimword_LESS_MustTerminate_limit:
   good_dimindex (:'a) ==> dimword (:α) < MustTerminate_limit (:α) - 1
Proof
  strip_tac \\ fs [wordSemTheory.MustTerminate_limit_def,dimword_def]
  \\ match_mp_tac (DECIDE ``1 < n ==> n < (2 * n + k) - 1n``)
  \\ fs [good_dimindex_def]
QED

Theorem assign_Less:
   op = IntOp Less ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ ‘names_opt ≠ NONE’ by (first_x_assum irule \\ EVAL_TAC \\ simp [])
  \\ gvs [GSYM IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS]
  \\ rename [‘cut_state_opt (SOME kept_names) s’]
  \\ drule_all state_rel_cut_state_opt_SOME \\ strip_tac
  \\ qpat_x_assum ‘_ (t with locals := y) [] locs’ $ ASSUME_NAMED_TAC "with_locals"
  \\ qpat_x_assum `_  s t [] locs`$ ASSUME_NAMED_TAC "old"
  \\ fs [do_app,oneline do_int_app_def]
  \\ gvs[AllCaseEqs()]
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [get_var_def]
  \\ qabbrev_tac ‘t0 = t with locals := y’
  \\ fs [Boolv_def] \\ rveq \\ fs [GSYM Boolv_def]
  \\ qpat_assum `state_rel c l1 l2 x _ [] locs`
           (assume_tac o REWRITE_RULE [state_rel_thm])
  \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule memory_rel_get_vars_IMP
  \\ disch_then drule
  \\ simp [] \\ strip_tac
  \\ rpt_drule0 memory_rel_Number_cmp
  \\ strip_tac \\ fs [] \\ rveq
  \\ fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF]
  \\ fs [wordSemTheory.get_var_def]
  \\ fs [assign_def,list_Seq_def] \\ eval_tac
  \\ fs [lookup_insert,wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def,
         word_cmp_Test_1,word_bit_or]
  \\ IF_CASES_TAC THEN1
   (fs [lookup_insert,state_rel_thm]
    \\ fs [wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def]
    \\ IF_CASES_TAC \\ fs [lookup_insert,inter_insert_ODD_adjust_set]
    \\ (conj_tac >- (fs [lookup_insert,adjust_var_11] \\ rw []))
    \\ (conj_tac >- rfs[option_le_max_right])
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
    \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [])
    \\ match_mp_tac (GEN_ALL memory_rel_zero_space)
    \\ first_x_assum $ irule_at Any)
  \\ pop_assum mp_tac
  \\ rpt_drule0 (Compare_code_thm |> INST_TYPE [``:'b``|->``:'ffi``])
  \\ ho_match_mp_tac (METIS_PROVE []
         ``((!x1 x2 x3. (b2 ==> b0 x1 x2 x3) ==> b1 x1 x2 x3) ==> b3) ==>
           ((!x1 x2 x3. b0 x1 x2 x3 ==> b1 x1 x2 x3) ==> b2 ==> b3)``)
  \\ strip_tac
  \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def,lookup_insert,
         wordSemTheory.bad_dest_args_def,wordSemTheory.find_code_def]
  \\ `lookup Compare_location t.code = SOME (3,Compare_code c)` by
       (fs [state_rel_def,code_rel_def,stubs_def] \\ NO_TAC)
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
    \\ fs [state_rel_def,code_rel_def,stubs_def]
    \\ fs [memory_rel_def,word_ml_inv_def,heap_in_memory_store_def]
    \\ fs [dimword_LESS_MustTerminate_limit]
    \\ rpt strip_tac \\ simp [])
  \\ strip_tac \\ fs []
  \\ rfs[]
  \\ imp_res_tac evaluate_stack_max_le
  \\ `?t2. pop_env t1 = SOME t2 /\
           domain t2.locals = domain y1 ∪ domain y2` by
   (unabbrev_all_tac
    \\ fs [wordSemTheory.call_env_def,wordSemTheory.push_env_def,
           wordSemTheory.pop_env_def] \\ pairarg_tac
    \\ fs [domain_union,domain_fromAList_toAList]
    \\ imp_res_tac env_to_list_lookup_equiv
    \\ fs [domain_lookup,EXTENSION,lookup_fromAList, AC DISJ_COMM DISJ_ASSOC])
  \\ fs []
  \\ fs [lookup_insert,word_cmp_Less_word_cmp_res]
  \\ rw [] \\ fs []
  \\ unabbrev_all_tac
  \\ fs [wordSemTheory.pop_env_def,wordSemTheory.call_env_def,
         wordSemTheory.push_env_def,wordSemTheory.dec_clock_def]
  \\ pairarg_tac \\ fs [] \\ rveq \\ fs []
  \\ fs[CaseEq "bool",CaseEq"prod",CaseEq"option",CaseEq"list",CaseEq"stack_frame",
        FST_EQ_EQUIV,ELIM_UNCURRY] >> rveq >> fs[lookup_insert]
  \\ rfs[wordSemTheory.set_vars_def,alist_insert_def]
  \\ rewrite_tac [push_if] \\ simp []
  \\ simp [state_rel_thm]
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
  \\ qpat_x_assum ‘state_rel c l1 l2 x t [] locs’ $ ASSUME_NAMED_TAC "state_rel_t"
  \\ LABEL_X_ASSUM "with_locals" assume_tac
  \\ gvs [state_rel_thm]
  \\ conj_tac >- rw []
  \\ conj_tac >-
      (rfs[option_le_max_right,option_le_max,stack_size_eq2,wordSemTheory.stack_size_frame_def,
           AC option_add_comm option_add_assoc])
  \\ conj_tac >-
      (match_mp_tac option_le_trans \\ goal_assum drule \\
       rpt(qpat_x_assum `option_le _.stack_max _.stack_max` mp_tac) \\
       simp[] \\
       imp_res_tac stack_rel_IMP_size_of_stack \\ pop_assum mp_tac \\
       rpt(pop_assum kall_tac) \\
       rw[option_le_max_right,option_le_max,stack_size_eq2,
          wordSemTheory.stack_size_frame_def,
          AC option_add_comm option_add_assoc,state_rel_def,
          option_map2_max_add,option_le_eq_eqns,
          option_le_add])
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs [inter_insert_ODD_adjust_set_alt]
  \\ match_mp_tac (GEN_ALL memory_rel_zero_space)
  \\ qexists_tac `x.space`
  \\ imp_res_tac word_cmp_Less_word_cmp_res
  \\ imp_res_tac not_word_cmp_Less_word_cmp_res
  \\ simp[]
  \\ fs[WORD_LESS_REFL]
  \\ IF_CASES_TAC \\ simp []
  \\ rpt (match_mp_tac memory_rel_Boolv_T)
  \\ rpt (match_mp_tac memory_rel_Boolv_F) \\ fs []
QED

Theorem assign_LessEq:
   op = IntOp LessEq ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ ‘names_opt ≠ NONE’ by (first_x_assum irule \\ EVAL_TAC \\ simp [])
  \\ gvs [GSYM IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS]
  \\ rename [‘cut_state_opt (SOME kept_names) s’]
  \\ drule_all state_rel_cut_state_opt_SOME \\ strip_tac
  \\ qpat_x_assum ‘_ (t with locals := y) [] locs’ $ ASSUME_NAMED_TAC "with_locals"
  \\ qpat_x_assum `_  s t [] locs`$ ASSUME_NAMED_TAC "old"
  \\ fs [do_app,oneline do_int_app_def]
  \\ gvs[AllCaseEqs()]
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [get_var_def]
  \\ qabbrev_tac ‘t0 = t with locals := y’
  \\ fs [Boolv_def] \\ rveq \\ fs [GSYM Boolv_def]
  \\ qpat_assum `state_rel c l1 l2 x _ [] locs`
           (assume_tac o REWRITE_RULE [state_rel_thm])
  \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule memory_rel_get_vars_IMP
  \\ disch_then drule
  \\ simp [] \\ strip_tac
  \\ rpt_drule0 memory_rel_Number_cmp
  \\ strip_tac \\ fs [] \\ rveq
  \\ fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF]
  \\ fs [wordSemTheory.get_var_def]
  \\ fs [assign_def,list_Seq_def] \\ eval_tac
  \\ fs [lookup_insert,wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def,
         word_cmp_Test_1,word_bit_or]
  \\ IF_CASES_TAC THEN1
   (fs [lookup_insert,state_rel_thm]
    \\ fs [wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def]
    \\ gvs [WORD_LESS_OR_EQ,WORD_NOT_LESS]
    \\ IF_CASES_TAC \\ fs [lookup_insert,inter_insert_ODD_adjust_set]
    \\ (conj_tac >- (fs [lookup_insert,adjust_var_11] \\ rw []))
    \\ (conj_tac >- rfs[option_le_max_right])
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ gvs [integerTheory.INT_LE_LT]
    \\ rpt (match_mp_tac memory_rel_Boolv_T \\ fs [])
    \\ rpt (match_mp_tac memory_rel_Boolv_F \\ fs [])
    \\ match_mp_tac (GEN_ALL memory_rel_zero_space)
    \\ first_x_assum $ irule_at Any)
  \\ pop_assum mp_tac
  \\ rpt_drule0 (Compare_code_thm |> INST_TYPE [``:'b``|->``:'ffi``])
  \\ ho_match_mp_tac (METIS_PROVE []
         ``((!x1 x2 x3. (b2 ==> b0 x1 x2 x3) ==> b1 x1 x2 x3) ==> b3) ==>
           ((!x1 x2 x3. b0 x1 x2 x3 ==> b1 x1 x2 x3) ==> b2 ==> b3)``)
  \\ strip_tac
  \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def,lookup_insert,
         wordSemTheory.bad_dest_args_def,wordSemTheory.find_code_def]
  \\ `lookup Compare_location t.code = SOME (3,Compare_code c)` by
       (fs [state_rel_def,code_rel_def,stubs_def] \\ NO_TAC)
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
    \\ fs [state_rel_def,code_rel_def,stubs_def]
    \\ fs [memory_rel_def,word_ml_inv_def,heap_in_memory_store_def]
    \\ fs [dimword_LESS_MustTerminate_limit]
    \\ rpt strip_tac \\ simp [])
  \\ strip_tac \\ fs []
  \\ rfs[]
  \\ imp_res_tac evaluate_stack_max_le
  \\ `?t2. pop_env t1 = SOME t2 /\
           domain t2.locals = domain y1 ∪ domain y2` by
   (unabbrev_all_tac
    \\ fs [wordSemTheory.call_env_def,wordSemTheory.push_env_def,
           wordSemTheory.pop_env_def] \\ pairarg_tac
    \\ fs [domain_union,domain_fromAList_toAList]
    \\ imp_res_tac env_to_list_lookup_equiv
    \\ fs [domain_lookup,EXTENSION,lookup_fromAList, AC DISJ_COMM DISJ_ASSOC])
  \\ fs []
  \\ fs [lookup_insert,word_cmp_Less_word_cmp_res]
  \\ rw [] \\ fs []
  \\ unabbrev_all_tac
  \\ fs [wordSemTheory.pop_env_def,wordSemTheory.call_env_def,
         wordSemTheory.push_env_def,wordSemTheory.dec_clock_def]
  \\ pairarg_tac \\ fs [] \\ rveq \\ fs []
  \\ fs[CaseEq "bool",CaseEq"prod",CaseEq"option",CaseEq"list",CaseEq"stack_frame",
        FST_EQ_EQUIV,ELIM_UNCURRY] >> rveq >> fs[lookup_insert]
  \\ rfs[wordSemTheory.set_vars_def,alist_insert_def]
  \\ rewrite_tac [push_if] \\ simp []
  \\ simp [state_rel_thm]
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
  \\ qpat_x_assum ‘state_rel c l1 l2 x t [] locs’ $ ASSUME_NAMED_TAC "state_rel_t"
  \\ LABEL_X_ASSUM "with_locals" assume_tac
  \\ gvs [state_rel_thm]
  \\ conj_tac >- rw []
  \\ conj_tac >-
      (rfs[option_le_max_right,option_le_max,stack_size_eq2,wordSemTheory.stack_size_frame_def,
           AC option_add_comm option_add_assoc])
  \\ conj_tac >-
      (match_mp_tac option_le_trans \\ goal_assum drule \\
       rpt(qpat_x_assum `option_le _.stack_max _.stack_max` mp_tac) \\
       simp[] \\
       imp_res_tac stack_rel_IMP_size_of_stack \\ pop_assum mp_tac \\
       rpt(pop_assum kall_tac) \\
       rw[option_le_max_right,option_le_max,stack_size_eq2,
          wordSemTheory.stack_size_frame_def,
          AC option_add_comm option_add_assoc,state_rel_def,
          option_map2_max_add,option_le_eq_eqns,
          option_le_add])
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs [inter_insert_ODD_adjust_set_alt]
  \\ match_mp_tac (GEN_ALL memory_rel_zero_space)
  \\ qexists_tac `x.space`
  \\ imp_res_tac word_cmp_NotLess_word_cmp_res
  \\ imp_res_tac word_cmp_not_NotLess_word_cmp_res
  \\ simp[]
  \\ fs[WORD_LESS_REFL]
  \\ IF_CASES_TAC \\ simp []
  \\ rpt (match_mp_tac memory_rel_Boolv_T)
  \\ rpt (match_mp_tac memory_rel_Boolv_F) \\ fs []
QED

Theorem word_exp_set_var_ShiftVar:
   word_exp (set_var v (Word w) t) (ShiftVar sow v n) =
    OPTION_MAP Word (case sow of Lsl => SOME (w << n)
                         | Lsr => SOME (w >>> n)
                         | Asr => SOME (w >> n)
                         | Ror => SOME (word_ror w n))
Proof
  once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
  \\ eval_tac \\ fs [lookup_insert] \\ fs []
QED

Theorem MemEqList_thm[local]:
  !offset t xs dm m b a.
      word_mem_eq (a + offset) xs dm m = SOME b /\
      get_var 3 t = SOME (Word a) /\ dm = t.mdomain /\ m = t.memory ==>
      ?x. evaluate (MemEqList offset xs,t) =
            (NONE,t with locals := ((if b then insert 1 (Word 18w) else I) o
                                    (if xs <> [] then insert 5 x else I)) t.locals)
Proof
  Induct_on `xs`
  THEN1 (fs [MemEqList_def,eq_eval,word_mem_eq_def])
  \\ fs [word_mem_eq_def]
  \\ rpt strip_tac
  \\ Cases_on `t.memory (a + offset)` \\ fs [isWord_def]
  \\ fs [MemEqList_def,eq_eval,word_mem_eq_def]
  \\ reverse IF_CASES_TAC
  THEN1 (fs [] \\ metis_tac [])
  \\ fs [] \\ rveq
  \\ full_simp_tac std_ss [GSYM WORD_ADD_ASSOC]
  \\ qmatch_goalsub_abbrev_tac `(MemEqList _ _, t6)`
  \\ first_x_assum (qspecl_then [`offset+bytes_in_word`,`t6`,`b`,`a`] mp_tac)
  \\ fs [Abbr`t6`,eq_eval]
  \\ strip_tac \\ fs []
  \\ Cases_on `b`
  \\ fs [wordSemTheory.state_component_equality]
  \\ rw [] \\ fs [insert_shadow]
  \\ metis_tac []
QED
Theorem MemEqList_thm = MemEqList_thm
  |> Q.SPEC `0w` |> SIMP_RULE std_ss [WORD_ADD_0];

Theorem assign_EqualConst:
   (?p. op = BlockOp (EqualConst p)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ rveq \\ fs []
  \\ rpt_drule0 state_rel_cut_IMP \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app,allowed_op_def] \\ rfs [] \\ every_case_tac \\ fs []
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_1] \\ clean_tac
  \\ fs [get_var_def]
  \\ fs [Boolv_def] \\ rveq \\ fs [GSYM Boolv_def,option_le_max_right]
  \\ qpat_assum `state_rel c l1 l2 x t [] locs`
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
      \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
      \\ rfs[]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
      \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs []))
    \\ fs [] \\ TOP_CASE_TAC \\ fs []
    \\ fs [bignum_words_def] \\ pairarg_tac \\ fs [CaseEq"option"]
    THEN1
     (fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF] \\ fs [eq_eval]
      \\ fs [lookup_insert,state_rel_thm] \\ rpt strip_tac
      \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
      \\ rfs[]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
      \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs []))
    \\ fs [word_bit_test,make_ptr_def]
    \\ IF_CASES_TAC
    THEN1
     (fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF] \\ fs [eq_eval]
      \\ fs [lookup_insert,state_rel_thm] \\ rpt strip_tac
      \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
      \\ rfs[]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
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
    \\ qmatch_goalsub_abbrev_tac `(MemEqList 0w wss,t9)`
    \\ `word_mem_eq a wss t9.mdomain t9.memory = SOME (j = i)` by fs [Abbr`t9`,Abbr`wss`]
    \\ rpt_drule0 MemEqList_thm
    \\ impl_tac THEN1 fs [eq_eval,Abbr `t9`]
    \\ strip_tac \\ fs []
    \\ `wss <> []` by (gvs [Abbr‘wss’])
    \\ fs []
    \\ IF_CASES_TAC \\ fs [] \\ rveq
    \\ unabbrev_all_tac
    \\ fs [lookup_insert,state_rel_thm] \\ rpt strip_tac
    \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def]
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
    \\ rfs[]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
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
      \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
      \\ rfs[]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
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
    \\ qmatch_goalsub_abbrev_tac `(MemEqList 0w wss,t9)`
    \\ `word_mem_eq a wss t9.mdomain t9.memory =
       SOME (ss = implode (MAP (CHR ∘ w2n) l'))` by fs [Abbr`t9`,Abbr`wss`]
    \\ rpt_drule0 MemEqList_thm
    \\ impl_tac THEN1 fs [eq_eval,Abbr `t9`]
    \\ strip_tac \\ fs []
    \\ `wss <> []` by (gvs [Abbr‘wss’,part_to_words_def,AllCaseEqs()])
    \\ fs []
    \\ IF_CASES_TAC \\ fs [] \\ rveq
    \\ unabbrev_all_tac
    \\ fs [lookup_insert,state_rel_thm] \\ rpt strip_tac
    \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def]
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
    \\ rfs[]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
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
     (fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF]
      \\ fs [list_Seq_def,eq_eval]
      \\ rename1 `get_real_addr c t.store w = SOME a`
      \\ qmatch_goalsub_abbrev_tac `word_exp t6`
      \\ `get_real_addr c t6.store w = SOME a` by fs [Abbr`t6`]
      \\ drule0 (get_real_addr_lemma |> REWRITE_RULE [CONJ_ASSOC]
                                     |> ONCE_REWRITE_RULE [CONJ_COMM] |> GEN_ALL)
      \\ disch_then (qspec_then `(adjust_var a1)` mp_tac)
      \\ impl_tac THEN1 fs [Abbr `t6`,eq_eval]
      \\ strip_tac \\ fs []
      \\ qmatch_goalsub_abbrev_tac `(MemEqList 0w wss,t9)`
      \\ `word_mem_eq (a+bytes_in_word) wss t9.mdomain t9.memory =
         SOME (other64 = w64)` by fs [Abbr`t9`,Abbr`wss`]
      \\ rpt_drule0 MemEqList_thm
      \\ impl_tac THEN1 fs [eq_eval,Abbr `t9`]
      \\ strip_tac \\ fs []
      \\ `wss <> []` by (gvs [Abbr‘wss’])
      \\ fs []
      \\ IF_CASES_TAC \\ fs [] \\ rveq
      \\ unabbrev_all_tac
      \\ fs [lookup_insert,state_rel_thm] \\ rpt strip_tac
      \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def]
      \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs [option_le_max_right]
      \\ rfs[]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
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
      shift_length c < dimindex (:'a) /\
      lookup Equal_location t.code = SOME (3,Equal_code c) /\
      lookup Equal1_location t.code = SOME (4,Equal1_code) /\
      lookup Compare1_location t.code = SOME (4,Compare1_code) /\
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
      shift_length c < dimindex (:'a) /\
      lookup Equal_location t.code = SOME (3,Equal_code c) /\
      lookup Equal1_location t.code = SOME (4,Equal1_code) /\
      lookup Compare1_location t.code = SOME (4,Compare1_code) /\
      get_var 0 t = SOME (Loc l1 l2) /\
      get_var 2 t = SOME (Word (w:'a word)) /\
      get_var 4 t = SOME (Word (a1:'a word)) /\
      get_var 6 t = SOME (Word (a2:'a word)) /\
      sane_locals_size t /\
      c.len_size <> 0 /\
      c.len_size < dimindex (:α) /\
      good_dimindex (:'a) ==>
      ?ck new_p smx.
        evaluate (Equal1_code,t) =
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
      \\ fs [eq_eval,list_Seq_def]
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
    \\ fs [eq_eval]
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
      \\ pairarg_tac \\ fs [] \\ fs [eq_eval,sane_locals_size_def])
    \\ strip_tac \\ fs []
    \\ Cases_on `pop_env (t1 with <|locals := LN; locals_size := SOME 0;
                                    stack_max := smx; permute := new_p;
                                    clock := ck|>)` \\ fs []
    THEN1
     (pop_assum mp_tac \\ unabbrev_all_tac
      \\ fs [eq_eval,
             wordSemTheory.push_env_def,
             wordSemTheory.pop_env_def]
      \\ pairarg_tac \\ fs [eq_eval])
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
    \\ fs [eq_eval]
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
    \\ Cases_on `x0 ≠ 1w` \\ fs [eq_eval,alist_insert_def]
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
    \\ fs [eq_eval]
    \\ `t2.code = t.code /\ t2.clock = ck` by
     (unabbrev_all_tac
      \\ fs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def]
      \\ pairarg_tac \\ fs [] \\ rveq
      \\ fs [wordSemTheory.state_component_equality,eq_eval])
    \\ rewrite_tac [list_Seq_def] \\ fs [eq_eval]
    \\ qmatch_goalsub_abbrev_tac `(Equal1_code, t5)`
    \\ first_x_assum (qspecl_then [`t5`,`l1`,`l2`] mp_tac)
    \\ impl_tac THEN1
     (unabbrev_all_tac
      \\ fs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def]
      \\ pairarg_tac \\ fs [] \\ rveq
      \\ fs [wordSemTheory.state_component_equality,eq_eval,sane_locals_size_def]
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
   (strip_tac \\ rveq \\ fs [eq_eval]
    \\ fs [wordSemTheory.state_component_equality,wordSemTheory.flush_state_def,
           option_le_max_right])
  \\ ntac 2 (once_rewrite_tac [list_Seq_def])
  \\ fs [eq_eval]
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
  \\ fs [eq_eval]
  \\ qmatch_goalsub_abbrev_tac `word_exp t6`
  \\ `get_real_addr c t6.store v1 = SOME x1` by fs [Abbr`t6`]
  \\ drule0 (get_real_addr_lemma |> REWRITE_RULE [CONJ_ASSOC]
              |> ONCE_REWRITE_RULE [CONJ_COMM] |> GEN_ALL)
  \\ disch_then (qspec_then `2` mp_tac)
  \\ impl_tac THEN1 fs [Abbr `t6`,eq_eval]
  \\ strip_tac \\ fs []
  (* second real_addr *)
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [eq_eval]
  \\ qmatch_goalsub_abbrev_tac `word_exp t7`
  \\ `get_real_addr c t7.store v2 = SOME x2` by fs [Abbr`t7`]
  \\ drule0 (get_real_addr_lemma |> REWRITE_RULE [CONJ_ASSOC]
              |> ONCE_REWRITE_RULE [CONJ_COMM] |> GEN_ALL)
  \\ disch_then (qspec_then `4` mp_tac)
  \\ impl_tac THEN1 fs [Abbr `t7`,eq_eval]
  \\ strip_tac \\ fs []
  (* -- *)
  \\ ntac 2 (once_rewrite_tac [list_Seq_def])
  \\ fs [eq_eval]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [eq_eval]
  \\ reverse IF_CASES_TAC \\ rewrite_tac []
  THEN1
   (pop_assum kall_tac \\ fs []
    \\ fs [] \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
    \\ IF_CASES_TAC THEN1
     (fs [] \\ strip_tac \\ rw [] \\ fs []
      \\ fs [wordSemTheory.state_component_equality,
             wordSemTheory.flush_state_def,option_le_max_right])
    \\ fs [] \\ rveq
    \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval,word_bit_test]
    \\ IF_CASES_TAC THEN1
     (fs [] \\ strip_tac \\ rw [] \\ fs []
      \\ fs [wordSemTheory.state_component_equality,
             wordSemTheory.flush_state_def,option_le_max_right])
    \\ once_rewrite_tac [list_Seq_def]
    \\ once_rewrite_tac [list_Seq_def]
    \\ fs [eq_eval,word_bit_test]
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
    \\ ntac 3 (once_rewrite_tac [list_Seq_def]) \\ fs [eq_eval]
    \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [eq_eval]
    \\ fs [GSYM decode_length_def,shift_lsl]
    \\ ntac 3 (once_rewrite_tac [list_Seq_def]) \\ fs [eq_eval]
    \\ fs [GSYM NOT_LESS]
    \\ qmatch_goalsub_abbrev_tac `(Compare1_code, t9)`
    \\ drule0 Compare1_code_thm
    \\ disch_then (qspec_then `t9` mp_tac)
    \\ impl_tac THEN1 (fs [Abbr`t9`,eq_eval])
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
  \\ ntac 2 (once_rewrite_tac [list_Seq_def]) \\ fs [eq_eval]
  \\ IF_CASES_TAC
  THEN1 (fs [] \\ rveq \\ fs [wordSemTheory.state_component_equality,
                              wordSemTheory.flush_state_def,option_le_max_right])
  \\ ntac 1 (once_rewrite_tac [list_Seq_def]) \\ fs [eq_eval]
  \\ IF_CASES_TAC
  THEN1 (fs [] \\ rveq \\ fs [wordSemTheory.state_component_equality,
                              wordSemTheory.flush_state_def,option_le_max_right])
  \\ fs []
  \\ ntac 1 (once_rewrite_tac [list_Seq_def]) \\ fs [eq_eval]
  \\ reverse IF_CASES_TAC
  THEN1 (fs [] \\ rveq \\ fs [wordSemTheory.state_component_equality,
                              wordSemTheory.flush_state_def,option_le_max_right])
  \\ fs []
  \\ ntac 4 (once_rewrite_tac [list_Seq_def]) \\ fs [eq_eval]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [eq_eval]
  \\ fs [GSYM decode_length_def,shift_lsl]
  \\ qmatch_goalsub_abbrev_tac `(Equal1_code,t8)`
  \\ first_x_assum (qspecl_then [`t8`,`l1`,`l2`] mp_tac)
  \\ impl_tac THEN1 (unabbrev_all_tac \\ fs [eq_eval,sane_locals_size_def])
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
    shift_length c < dimindex (:'a) /\
    t.locals_size = lookup Equal_location t.stack_size /\
    lookup Equal_location t.code = SOME (3,Equal_code c) /\
    lookup Equal1_location t.code = SOME (4,Equal1_code) /\
    lookup Compare1_location t.code = SOME (4,Compare1_code) /\
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
  \\ ‘names_opt ≠ NONE’ by (first_x_assum irule \\ EVAL_TAC \\ simp [])
  \\ gvs [GSYM IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS]
  \\ rename [‘cut_state_opt (SOME kept_names) s’]
  \\ drule_all state_rel_cut_state_opt_SOME \\ strip_tac
  \\ qpat_x_assum ‘_ (t with locals := y) [] locs’ $ ASSUME_NAMED_TAC "with_locals"
  \\ qpat_x_assum `_  s t [] locs`$ ASSUME_NAMED_TAC "old"
  \\ fs [do_app,oneline do_int_app_def]
  \\ gvs[AllCaseEqs()]
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [get_var_def]
  \\ qabbrev_tac ‘t0 = t with locals := y’
  \\ fs [Boolv_def] \\ rveq \\ fs [GSYM Boolv_def]
  \\ qpat_assum `state_rel c l1 l2 x _ [] locs`
           (assume_tac o REWRITE_RULE [state_rel_thm])
  \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule memory_rel_get_vars_IMP
  \\ disch_then drule
  \\ simp [] \\ strip_tac
  \\ rename1 `memory_rel _ _ _ _ _ _ _ _ ((h_1,a_1)::(h_2,a_2)::_)`
  \\ rpt_drule0 memory_rel_simple_eq
  \\ strip_tac \\ fs [] \\ rveq
  \\ fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF]
  \\ fs [wordSemTheory.get_var_def]
  \\ fs [assign_def]
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
    \\ pop_assum kall_tac
    \\ simp [state_rel_thm,lookup_insert,adjust_var_11]
    \\ fs [lookup_insert,inter_insert_ODD_adjust_set]
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
  \\ `lookup Equal_location t.code = SOME (3,Equal_code c)` by
       (fs [state_rel_def,code_rel_def,stubs_def] \\ NO_TAC)
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
    \\ fs [state_rel_def,code_rel_def,stubs_def]
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
  \\ qpat_x_assum ‘state_rel c l1 l2 x t [] locs’ $ ASSUME_NAMED_TAC "state_rel_t"
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

Theorem assign_WordOpW8:
   (?opw. op = WordOp (WordOpw W8 opw)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
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
  \\ `small_int (:'a) (&w2n w1) ∧ small_int (:'a) (&w2n w2)`
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
  \\ (conj_tac >- rw[])
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs[]
  >- ( match_mp_tac memory_rel_And \\ fs[] )
  >- ( match_mp_tac memory_rel_Or \\ fs[] )
  >- ( match_mp_tac memory_rel_Xor \\ fs[] )
  >- (
    qmatch_goalsub_abbrev_tac`Word w`
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
      \\ qmatch_goalsub_abbrev_tac`a * b MOD q`
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
  >- (
    qmatch_goalsub_abbrev_tac`Word w`
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
        qmatch_goalsub_abbrev_tac`(a * b) MOD f DIV d`
        \\ qspecl_then[`a * b`,`d`,`f DIV d`]mp_tac (GSYM DIV_MOD_MOD_DIV)
        \\ (impl_tac >- fs[Abbr`d`,Abbr`f`,good_dimindex_def,dimword_def])
        \\ `d * (f DIV d) = f` by fs[good_dimindex_def,Abbr`f`,Abbr`d`,dimword_def]
        \\ pop_assum SUBST_ALL_TAC
        \\ disch_then (CHANGED_TAC o SUBST_ALL_TAC)
        \\ unabbrev_all_tac
        \\ qmatch_goalsub_abbrev_tac`a * (b * d) DIV d`
        \\ `a * (b * d) DIV d = a * b`
        by (
          qspecl_then[`d`,`a * b`]mp_tac MULT_DIV
          \\ impl_tac >- simp[Abbr`d`]
          \\ simp[] )
        \\ pop_assum SUBST_ALL_TAC
        \\ fs[Abbr`a`,Abbr`d`,dimword_def,good_dimindex_def]
        \\ qmatch_goalsub_abbrev_tac`(a * b) MOD q`
        \\ qspecl_then[`a`,`b`,`q DIV a`](mp_tac o GSYM) MOD_COMMON_FACTOR
        \\ (impl_tac >- simp[Abbr`a`,Abbr`q`])
        \\ simp[Abbr`a`,Abbr`q`] \\ disch_then kall_tac
        \\ `b < 256` by simp[Abbr`b`]
        \\ simp[] )
      \\ simp[word_2comp_n2w]
      \\ qmatch_goalsub_abbrev_tac`(4 * (b * d)) MOD f`
      \\ qmatch_goalsub_abbrev_tac`f - y MOD f`
      \\ `f = d * 2**10`
      by (
        unabbrev_all_tac
        \\ fs[dimword_def,good_dimindex_def] )
      \\ qunabbrev_tac`f`
      \\ pop_assum SUBST_ALL_TAC
      \\ fs[]
      \\ qmatch_goalsub_abbrev_tac`m MOD (1024 * d) DIV d`
      \\ qspecl_then[`m`,`d`,`1024`]mp_tac DIV_MOD_MOD_DIV
      \\ impl_tac >- simp[Abbr`d`] \\ simp[]
      \\ disch_then(CHANGED_TAC o SUBST_ALL_TAC o SYM)
      \\ qspecl_then[`1024 * d`,`(m DIV d) MOD 1024`]mp_tac LESS_MOD
      \\ impl_tac
      >- (
        qspecl_then[`m DIV d`,`1024`]mp_tac MOD_LESS
        \\ impl_tac >- simp[]
        \\ `1024 < 1024 * d`
        by (
          simp[Abbr`d`,ONE_LT_EXP]
          \\ fs[good_dimindex_def] )
        \\ decide_tac )
      \\ disch_then (CHANGED_TAC o SUBST_ALL_TAC)
      \\ fs[Abbr`m`,Abbr`y`]
      \\ qspecl_then[`d`,`4 * b`,`1024`]mp_tac MOD_COMMON_FACTOR
      \\ impl_tac >- simp[Abbr`d`] \\ simp[]
      \\ disch_then(CHANGED_TAC o SUBST_ALL_TAC o SYM)
      \\ qmatch_assum_rename_tac`n2 < 256n`
      \\ `n2 <= 256` by simp[]
      \\ drule0 LESS_EQ_ADD_SUB
      \\ qmatch_assum_rename_tac`n1 < n2`
      \\ disch_then(qspec_then`n1`(CHANGED_TAC o SUBST_ALL_TAC))
      \\ REWRITE_TAC[LEFT_ADD_DISTRIB]
      \\ simp[LEFT_SUB_DISTRIB,Abbr`b`]
      \\ `4 * (d * n2) - 4 * (d * n1) = (4 * d) * (n2 - n1)` by simp[]
      \\ pop_assum (CHANGED_TAC o SUBST_ALL_TAC)
      \\ `1024 * d - 4 * d * (n2 - n1) = (1024 - 4 * (n2 - n1)) * d` by simp[]
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
    \\ fs[good_dimindex_def,dimword_def] )
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
         wordSemTheory.set_var_def,wordSemTheory.get_var_def]
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
  dimindex (:'a) = 32 ∧ 1 < c.len_size ∧ 1 < 30 − c.len_size ⇒
  encode_header c 3 2 ≠ (NONE:'a word option)
Proof
  gvs [encode_header_def,dimword_def]
QED

Theorem assign_WordOpW64:
   (?opw. op = WordOp (WordOpw W64 opw)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ asm_rewrite_tac [] \\ pop_assum kall_tac
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app,oneline do_word_app_def,allowed_op_def]
  \\ gvs [AllCaseEqs()]
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ clean_tac
  \\ rename [‘get_vars [e1;e2] x.locals’]
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
   (?sh n. op = WordOp (WordShift W8 sh n)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ asm_rewrite_tac [] \\ pop_assum kall_tac
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
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
  \\ `small_int (:α) (&w2n ww)` by simp[small_int_w2n]
  \\ rpt_drule0 memory_rel_Number_IMP
  \\ strip_tac \\ clean_tac
  \\ imp_res_tac get_vars_1_imp
  \\ fs[wordSemTheory.get_var_def]
  \\ simp[assign_def]
  \\ BasicProvers.CASE_TAC \\ eval_tac
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
    \\ `small_int (:'a) i`
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
      \\ qspecl_then[`n2w(w2n w)`,`2`]mp_tac WORD_MUL_LSL
      \\ simp[] \\ disch_then (SUBST_ALL_TAC o SYM)
      \\ simp[]
      \\ `10 < dimindex(:'a)` by fs[good_dimindex_def]
      \\ simp[]
      \\ qspecl_then[`n2w(w2n (w<<n))`,`2`]mp_tac WORD_MUL_LSL
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
    \\ `small_int (:'a) i`
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
      \\ qmatch_goalsub_abbrev_tac`4w * ww`
      \\ `4w * ww = ww << 2` by simp[WORD_MUL_LSL]
      \\ pop_assum SUBST_ALL_TAC
      \\ qspecl_then[`ww`,`2`]mp_tac lsl_lsr
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
    >- (fs[good_dimindex_def,MIN_DEF] \\ rfs[])
    \\ simp[lookup_insert]
    \\ IF_CASES_TAC
    >- (fs[good_dimindex_def,MIN_DEF] \\ rfs[])
    \\ simp[lookup_insert,option_le_max_right]
    \\ conj_tac >- rw[]
    \\ ntac 2 (pop_assum kall_tac)
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert
    \\ qmatch_goalsub_abbrev_tac`Number i`
    \\ qmatch_goalsub_abbrev_tac`Word w`
    \\ `small_int (:'a) i` by simp[Abbr`i`]
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
  >-
   (qmatch_asmsub_rename_tac `WordShift W8 Ror kk`
    \\ `~(2 ≥ dimindex (:α))` by (fs [good_dimindex_def] \\ fs [])
    \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
    \\ fs [lookup_insert,adjust_var_11,option_le_max_right] \\ rw []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert
    \\ qmatch_goalsub_abbrev_tac`Number i8`
    \\ qmatch_goalsub_abbrev_tac`Word w8`
    \\ `small_int (:'a) i8` by simp[Abbr`i8`]
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
           [METIS_PROVE [] ``b1 /\ 2n <= i /\ c <=>
              b1 /\ 2n <= i /\ (b1 /\ 2n <= i ==> c)``]
      \\ simp [fcpTheory.CART_EQ,word_or_def,fcpTheory.FCP_BETA,
             word_lsr_def,word_lsl_def,w2w,word_ror_def]
      \\ rpt strip_tac
      \\ reverse (Cases_on `2 <= i`) \\ fs []
      THEN1
       (fs [fcpTheory.FCP_BETA] \\ CCONTR_TAC \\ fs []
        \\ `kk MOD 8 < 8` by fs [] \\ decide_tac)
      \\ `kk MOD 8 < 8` by fs []
      \\ simp []
      \\ reverse (Cases_on `i < 10`)
      THEN1
       (simp [fcpTheory.FCP_BETA]
        \\ CCONTR_TAC \\ fs []
        \\ rfs [fcpTheory.FCP_BETA])
      \\ fs []
      \\ `kk MOD 8 < 8` by fs []
      \\ simp [fcpTheory.FCP_BETA]
      \\ qpat_x_assum `2 ≤ i` mp_tac
      \\ simp [Once LESS_EQ_EXISTS] \\ strip_tac
      \\ rfs [] \\ rveq
      \\ `p < 8 /\ kk MOD 8 < 8` by fs []
      \\ once_rewrite_tac [GSYM MOD_PLUS]
      \\ drule0 (DECIDE ``n < 8n ==> n=0 \/ n=1 \/ n=2 \/ n=3 \/
                                    n=4 \/ n=5 \/ n=6 \/ n=7``)
      \\ strip_tac \\ fs []
      \\ drule0 (DECIDE ``n < 8n ==> n=0 \/ n=1 \/ n=2 \/ n=3 \/
                                    n=4 \/ n=5 \/ n=6 \/ n=7``)
      \\ strip_tac \\ fs [w2w]))
QED

val assign_WordShift64 =
  ``assign c n l dest (WordOp (WordShift W64 sh n)) [e1] names_opt``
  |> SIMP_CONV (srw_ss()) [assign_def]

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
    \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
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
    \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [lookup_insert]
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
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [lookup_insert]
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
  (?sh n. op = WordOp (WordShift W64 sh n)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ asm_rewrite_tac [] \\ pop_assum kall_tac
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
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
    \\ qexists_tac`x.space-2` \\ simp[]
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

val assign_FP_cmp = SIMP_CONV (srw_ss()) [assign_def]
  ``((assign (c:data_to_word$config) (secn:num) (l:num) (dest:num) (WordOp (FP_cmp fpc))
       (args:num list) (names:num_set option)):'a wordLang$prog # num)``;

val assign_FP_top = SIMP_CONV (srw_ss()) [assign_def]
  ``((assign (c:data_to_word$config) (secn:num) (l:num) (dest:num) (WordOp (FP_top fpt))
       (args:num list) (names:num_set option)):'a wordLang$prog # num)``;

val assign_FP_bop = SIMP_CONV (srw_ss()) [assign_def]
  ``((assign (c:data_to_word$config) (secn:num) (l:num) (dest:num) (WordOp (FP_bop fpb))
       (args:num list) (names:num_set option)):'a wordLang$prog # num)``;

val assign_FP_uop = SIMP_CONV (srw_ss()) [assign_def]
  ``((assign (c:data_to_word$config) (secn:num) (l:num) (dest:num) (WordOp (FP_uop fpu))
       (args:num list) (names:num_set option)):'a wordLang$prog # num)``;

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
   (?fpc. op = WordOp (FP_cmp fpc)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ asm_rewrite_tac [] \\ pop_assum kall_tac
  \\ imp_res_tac state_rel_cut_IMP \\ pop_assum mp_tac
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app,oneline do_word_app_def,allowed_op_def]
  \\ gvs [AllCaseEqs()]
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ clean_tac
  \\ rename[‘get_vars [e1;e2] x.locals’]
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
    \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
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
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
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
  (?fpt. op = WordOp (FP_top fpt)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ asm_rewrite_tac [] \\ pop_assum kall_tac
  \\ imp_res_tac state_rel_cut_IMP \\ pop_assum mp_tac
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app,oneline do_word_app_def,allowed_op_def,space_consumed_def]
  \\ gvs [AllCaseEqs()]
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ clean_tac
  \\ rename[‘get_vars [e1;e2;e3] x.locals’]
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
   (?fpb. op = WordOp (FP_bop fpb)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ asm_rewrite_tac [] \\ pop_assum kall_tac
  \\ imp_res_tac state_rel_cut_IMP \\ pop_assum mp_tac
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app,oneline do_word_app_def,allowed_op_def]
  \\ every_case_tac \\ fs[]
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ clean_tac
  \\ rename[‘get_vars [e1;e2] x.locals’]
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
  \\ (qpat_abbrev_tac `ww = fp64_add _ _ _`
      ORELSE qpat_abbrev_tac `ww = fp64_sub _ _ _`
      ORELSE qpat_abbrev_tac `ww = fp64_mul _ _ _`
      ORELSE qpat_abbrev_tac `ww = fp64_div _ _ _`)
  \\ disch_then (qspec_then `ww` mp_tac) \\ fs []
  \\ TRY impl_tac \\ TRY (rw [] \\ NO_TAC)
  \\ strip_tac \\ fs [FAPPLY_FUPDATE_THM]
  \\ rveq \\ fs [] \\ rw []
  \\ qhdtm_x_assum `limits_inv` mp_tac
  \\ simp[limits_inv_def,FLOOKUP_UPDATE]
QED

Theorem assign_FP_uop:
   (?fpu. op = WordOp (FP_uop fpu)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ asm_rewrite_tac [] \\ pop_assum kall_tac
  \\ imp_res_tac state_rel_cut_IMP \\ pop_assum mp_tac
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app,oneline do_word_app_def,allowed_op_def]
  \\ every_case_tac \\ fs[]
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ clean_tac
  \\ rename[‘get_vars [e1] x.locals’]
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
  \\ (qpat_abbrev_tac `ww = fp64_abs _`
      ORELSE qpat_abbrev_tac `ww = fp64_negate _`
      ORELSE qpat_abbrev_tac `ww = fp64_sqrt _ _`)
  \\ disch_then (qspec_then `ww` mp_tac) \\ fs []
  \\ strip_tac \\ fs [FAPPLY_FUPDATE_THM]
  \\ rveq \\ fs [] \\ rw []
  \\ qhdtm_x_assum `limits_inv` mp_tac
  \\ simp[limits_inv_def,FLOOKUP_UPDATE]
QED

Theorem assign_Label:
   (?lab. op = Label lab) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ fs [assign_def] \\ fs [do_app,allowed_op_def]
  \\ Cases_on `vals` \\ fs []
  \\ qpat_assum `_ = Rval (v,s2)` mp_tac
  \\ IF_CASES_TAC \\ fs []
  \\ rveq \\ fs []
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  \\ simp [state_rel_thm] \\ eval_tac
  \\ fs [state_rel_thm] \\ eval_tac
  \\ fs [domain_lookup,lookup_map]
  \\ reverse IF_CASES_TAC THEN1
   (sg `F` \\ fs [code_rel_def]
    \\ rename1 `lookup _ s2.code = SOME zzz` \\ PairCases_on `zzz`
    \\ res_tac \\ fs []) \\ fs []
  \\ fs [lookup_insert,FAPPLY_FUPDATE_THM,adjust_var_11,FLOOKUP_UPDATE]
  \\ rw [] \\ fs [] \\ rw [] \\ fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ match_mp_tac memory_rel_CodePtr \\ fs []
QED

Theorem do_app_Ref:
   do_app (MemOp Ref) vals x =
    case consume_space (LENGTH vals + 1) x of
      NONE => Rerr (Rabort Rtype_error)
    | SOME s1 =>
      Rval
      (RefPtr T (LEAST ptr. ptr ∉ domain s1.refs),
         s1 with
           <| refs := insert (LEAST ptr. ptr ∉ domain s1.refs) (ValueArray vals) s1.refs;
           safe_for_space := (do_stack (MemOp Ref) vals (do_lim_safe s1 (MemOp Ref) vals)).safe_for_space;
           stack_max :=
             (do_stack (MemOp Ref) vals (do_lim_safe s1 (MemOp Ref) vals)).stack_max
           |>)
Proof
  fs [do_app,allowed_op_def,consume_space_def] \\ rw[] >> Cases_on `vals` \\ fs [LET_THM]
QED

Theorem assign_Ref:
   op = MemOp Ref ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ asm_rewrite_tac [] \\ pop_assum kall_tac
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  \\ fs [assign_def] \\ fs [do_app_Ref] \\ fs[do_app]
  \\ Cases_on `consume_space (LENGTH vals + 1) x` \\ fs [] \\ rveq
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ clean_tac
  \\ fs [consume_space_def] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ TOP_CASE_TAC \\ fs []
  >- (conj_tac >- (fs[state_rel_def] >> rw[option_le_max_right] >> metis_tac[option_le_trans]) >>
               fs[encode_header_def] >>
      fs[encode_header_def,state_rel_def,good_dimindex_def,limits_inv_def,dimword_def,
          memory_rel_def,heap_in_memory_store_def,consume_space_def,arch_size_def] >> rfs[NOT_LESS]
     )
  \\ simp [state_rel_thm] \\ eval_tac
  \\ fs [state_rel_thm] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs [NOT_LESS,DECIDE ``n + 1 <= m <=> n < m:num``]
  \\ strip_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ qabbrev_tac `new = LEAST ptr. ptr ∉ domain x.refs`
  \\ `new ∉ domain x.refs` by metis_tac [LEAST_NOTIN_spt_DOMAIN]
  \\ qpat_assum `_ = LENGTH _` assume_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 memory_rel_Ref \\ strip_tac
  \\ fs [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.set_store_def,FLOOKUP_UPDATE]
  \\ qpat_abbrev_tac `t5 = t with <| locals := _ ; store := _ |>`
  \\ pairarg_tac \\ fs []
  \\ `t.memory = t5.memory /\ t.mdomain = t5.mdomain` by
       (unabbrev_all_tac \\ fs []) \\ fs []
  \\ ntac 2 (pop_assum kall_tac)
  \\ drule0 evaluate_StoreEach
  \\ disch_then (qspecl_then [`3::MAP adjust_var args`,`1`] mp_tac)
  \\ impl_tac THEN1
   (fs [wordSemTheory.get_vars_def,Abbr`t5`,wordSemTheory.get_var_def,
        lookup_insert,get_vars_with_store,get_vars_adjust_var] \\ NO_TAC)
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

Theorem assign_Update:
   op = MemOp Update ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  \\ fs [do_app,allowed_op_def] \\ every_case_tac \\ fs [] \\ clean_tac
  \\ fs [INT_EQ_NUM_LEMMA] \\ clean_tac
  \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_3] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [bvlSemTheory.Unit_def] \\ rveq
  \\ fs [GSYM bvlSemTheory.Unit_def] \\ rveq
  \\ fs [assign_def] \\ eval_tac \\ fs [state_rel_thm]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs []
  \\ imp_res_tac get_vars_3_IMP \\ fs []
  \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_3] \\ clean_tac
  \\ imp_res_tac get_vars_3_IMP \\ fs [] \\ strip_tac
  \\ drule0 reorder_lemma \\ strip_tac
  \\ drule0 (memory_rel_Update |> GEN_ALL) \\ fs []
  \\ strip_tac \\ clean_tac
  \\ `word_exp t (real_offset c (adjust_var a2)) = SOME (Word y) /\
      word_exp t (real_addr c (adjust_var a1)) = SOME (Word x')` by
        metis_tac [get_real_offset_lemma,get_real_addr_lemma]
  \\ fs [] \\ eval_tac \\ fs [EVAL ``word_exp s1 Unit``]
  \\ fs [wordSemTheory.mem_store_def]
  \\ fs [lookup_insert,adjust_var_11]
  \\ rw [] \\ fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ match_mp_tac memory_rel_Unit \\ fs []
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
  \\ rw [] \\ fs []
QED

Theorem assign_El:
   op = MemOp El ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  \\ fs [do_app,CaseEq"list",CaseEq"dataSem$v",CaseEq"bool"]
  \\ rveq \\ fs []
  THEN1
   (fs [INT_EQ_NUM_LEMMA] \\ clean_tac
    \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_2] \\ clean_tac
    \\ imp_res_tac state_rel_get_vars_IMP
    \\ fs [assign_def] \\ eval_tac \\ fs [state_rel_thm]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ disch_then drule0 \\ fs []
    \\ imp_res_tac get_vars_2_IMP \\ fs []
    \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_2] \\ clean_tac
    \\ imp_res_tac get_vars_2_IMP \\ fs [] \\ strip_tac
    \\ drule0 (memory_rel_El |> GEN_ALL) \\ fs []
    \\ strip_tac \\ clean_tac
    \\ rename [`get_real_addr c t.store ptr_w = SOME x1`]
    \\ `word_exp t (real_offset c (adjust_var a2)) = SOME (Word y) /\
        word_exp t (real_addr c (adjust_var a1)) = SOME (Word x1)` by
          metis_tac [get_real_offset_lemma,get_real_addr_lemma]
    \\ fs [] \\ eval_tac
    \\ fs [lookup_insert,adjust_var_11]
    \\ rw [] \\ fs []
    THEN1 metis_tac [option_le_trans,option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
    \\ fs [] \\ rw [] \\ fs [])
  \\ fs [INT_EQ_NUM_LEMMA] \\ clean_tac
  \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_2] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [assign_def] \\ eval_tac \\ fs [state_rel_thm,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs []
  \\ imp_res_tac get_vars_2_IMP \\ fs []
  \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_2] \\ clean_tac
  \\ imp_res_tac get_vars_2_IMP \\ fs [] \\ strip_tac
  \\ fs [CaseEq"option",CaseEq"ref",CaseEq"bool"] \\ rveq \\ fs []
  \\ drule0 (memory_rel_Deref |> GEN_ALL) \\ fs []
  \\ strip_tac \\ clean_tac
  \\ `word_exp t (real_offset c (adjust_var a2)) = SOME (Word y) /\
      word_exp t (real_addr c (adjust_var a1)) = SOME (Word x')` by
        metis_tac [get_real_offset_lemma,get_real_addr_lemma]
  \\ fs [] \\ eval_tac
  \\ fs [lookup_insert,adjust_var_11]
  \\ rw [] \\ fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
  \\ fs [] \\ rw [] \\ fs []
QED

Theorem assign_ElemAt:
   (∃n. op = BlockOp (ElemAt n)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
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
          metis_tac [get_real_addr_lemma]
    \\ fs [] \\ eval_tac
    \\ fs [lookup_insert,adjust_var_11]
    \\ rw [] \\ fs []
    THEN1 metis_tac [option_le_trans,option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
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
  \\ `word_exp t (real_addr c (adjust_var a1)) = SOME (Word x')` by
        metis_tac [get_real_offset_lemma,get_real_addr_lemma]
  \\ fs [] \\ eval_tac
  \\ fs [lookup_insert,adjust_var_11]
  \\ rw [] \\ fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
  \\ fs [] \\ rw [] \\ fs []
QED

Theorem assign_UpdateByte:
   op = MemOp UpdateByte ==> ^assign_thm_goal
Proof[exclude_simps = INT_OF_NUM NUM_EQ0]
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs[]
  \\ fs[do_app,allowed_op_def] \\ every_case_tac \\ fs[] \\ clean_tac
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ rename [‘get_vars [e1;e2;e3] x.locals’]
  \\ imp_res_tac get_vars_3_IMP
  \\ fs [] \\ rveq
  \\ fs[] \\ rveq
  \\ fs[state_rel_thm,set_var_def,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP )
  \\ strip_tac
  \\ fs[get_vars_def]
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ rpt_drule0 memory_rel_ByteArray_IMP
  \\ strip_tac \\ clean_tac
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ imp_res_tac memory_rel_tl
  \\ `small_int (:'a) i`
  by (
    simp[small_int_def]
    \\ fs[good_dimindex_def]
    \\ rfs[dimword_def]
    \\ intLib.COOPER_TAC )
  \\ rpt_drule0 memory_rel_Number_IMP
  \\ imp_res_tac memory_rel_tl
  \\ `small_int (:'a) (&w2n w)`
  by (match_mp_tac small_int_w2n \\ fs[])
  \\ rpt_drule0 memory_rel_Number_IMP
  \\ ntac 2 (qhdtm_x_assum`memory_rel` kall_tac)
  \\ ntac 2 strip_tac \\ clean_tac
  \\ qpat_x_assum`get_var (adjust_var e2) _ = _`assume_tac
  \\ rpt_drule0 get_real_byte_offset_lemma
  \\ simp[assign_def,list_Seq_def] \\ eval_tac
  \\ fs[wordSemTheory.get_var_def]
  \\ simp[lookup_insert,wordSemTheory.inst_def]
  \\ `2 < dimindex(:'a)` by fs[good_dimindex_def]
  \\ simp[wordSemTheory.get_var_def,Unit_def]
  \\ eval_tac
  \\ simp[lookup_insert]
  \\ rpt strip_tac
  \\ simp[Smallnum_i2w,GSYM integer_wordTheory.word_i2w_mul]
  \\ qspecl_then[`ii`,`2`](mp_tac o Q.GEN`ii` o SYM) WORD_MUL_LSL
  \\ `i2w 4 = 4w` by EVAL_TAC
  \\ simp[]
  \\ `i2w i << 2 >>> 2 = i2w i`
  by (
    match_mp_tac lsl_lsr
    \\ Cases_on`i`
    \\ fs[small_int_def,X_LT_DIV,dimword_def,integer_wordTheory.i2w_def] )
  \\ pop_assum (CHANGED_TAC o SUBST_ALL_TAC)
  \\ `w2w w << 2 >>> 2 = w2w w`
  by (
    match_mp_tac lsl_lsr
    \\ simp[w2n_w2w]
    \\ reverse IF_CASES_TAC >- fs[good_dimindex_def]
    \\ fs[small_int_def,X_LT_DIV])
  \\ pop_assum (CHANGED_TAC o SUBST_ALL_TAC)
  \\ simp[w2w_w2w]
  \\ `dimindex(:8) ≤ dimindex(:α)` by fs[good_dimindex_def]
  \\ simp[integer_wordTheory.w2w_i2w]
  \\ `i2w i = n2w (Num i)`
  by (
    rw[integer_wordTheory.i2w_def]
    \\ `F` by intLib.COOPER_TAC )
  \\ pop_assum (CHANGED_TAC o SUBST_ALL_TAC)
  \\ disch_then kall_tac
  \\ qpat_x_assum`∀i. _ ⇒ mem_load_byte_aux _ _ _ _ = _`(qspec_then`Num i`mp_tac)
  \\ impl_tac
  >- (
    fs[GSYM integerTheory.INT_OF_NUM]
    \\ REWRITE_TAC[GSYM integerTheory.INT_LT]
    \\ PROVE_TAC[] )
  \\ simp[wordSemTheory.mem_load_byte_aux_def]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ strip_tac
  \\ simp[wordSemTheory.mem_store_byte_aux_def]
  \\ simp[lookup_insert]
  \\ conj_tac >- rw[]
  \\ fs[inter_insert_ODD_adjust_set,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert
  \\ simp[]
  \\ match_mp_tac memory_rel_Unit
  \\ first_x_assum(qspecl_then[`Num i`,`w`]mp_tac)
  \\ impl_tac
  >- (
    fs[GSYM integerTheory.INT_OF_NUM]
    \\ REWRITE_TAC[GSYM integerTheory.INT_LT]
    \\ PROVE_TAC[] )
  \\ simp[theWord_def] \\ strip_tac
  \\ simp[WORD_ALL_BITS]
  \\ drule0 memory_rel_tl \\ simp[] \\ strip_tac
  \\ drule0 memory_rel_tl \\ simp[] \\ strip_tac
  \\ drule0 memory_rel_tl \\ simp[]
QED

Theorem assign_DerefByte:
   op = MemOp DerefByte ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs[]
  \\ fs[do_app,allowed_op_def] \\ every_case_tac \\ fs[] \\ clean_tac
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ imp_res_tac get_vars_2_IMP
  \\ fs[state_rel_thm,set_var_def,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP )
  \\ strip_tac
  \\ fs[get_vars_def]
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ fs[]
  \\ rpt_drule0 memory_rel_ByteArray_IMP
  \\ strip_tac \\ clean_tac
  \\ first_x_assum(qspec_then`ARB`kall_tac)
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ imp_res_tac memory_rel_tl
  \\ rename1 `i < &LENGTH l'`
  \\ `small_int (:'a) i`
  by (
    simp[small_int_def]
    \\ fs[good_dimindex_def]
    \\ rfs[dimword_def]
    \\ intLib.COOPER_TAC )
  \\ rpt_drule0 memory_rel_Number_IMP
  \\ qhdtm_x_assum`memory_rel` kall_tac
  \\ strip_tac
  \\ clean_tac
  \\ qpat_x_assum`get_var _ _ = SOME (Word(Smallnum _))`assume_tac
  \\ rpt_drule0 get_real_byte_offset_lemma
  \\ simp[assign_def,list_Seq_def] \\ eval_tac
  \\ simp[wordSemTheory.inst_def]
  \\ eval_tac
  \\ fs[Smallnum_i2w,GSYM integer_wordTheory.word_i2w_mul]
  \\ qspecl_then[`i2w i`,`2`](mp_tac o SYM) WORD_MUL_LSL
  \\ `i2w 4 = 4w` by EVAL_TAC
  \\ simp[]
  \\ `i2w i << 2 >>> 2 = i2w i`
  by (
    match_mp_tac lsl_lsr
    \\ REWRITE_TAC[GSYM integerTheory.INT_LT,
                   GSYM integerTheory.INT_MUL,
                   integer_wordTheory.w2n_i2w]
    \\ simp[]
    \\ reverse(Cases_on`i`) \\ fs[]
    >- (
      fs[dimword_def, integerTheory.INT_MOD0] )
    \\ simp[integerTheory.INT_MOD,dimword_def]
    \\ fs[small_int_def,dimword_def]
    \\ fs[X_LT_DIV] )
  \\ simp[]
  \\ first_x_assum(qspec_then`Num i`mp_tac)
  \\ impl_tac >- ( Cases_on`i` \\ fs[] )
  \\ `i2w i = n2w (Num i)`
  by (
    rw[integer_wordTheory.i2w_def]
    \\ Cases_on`i` \\ fs[] )
  \\ fs[]
  \\ `¬(2 ≥ dimindex(:α))` by fs[good_dimindex_def]
  \\ simp[lookup_insert]
  \\ ntac 4 strip_tac
  \\ conj_tac >- rw[]
  \\ fs[inter_insert_ODD_adjust_set,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert
  \\ qmatch_goalsub_abbrev_tac`(Number j,Word k)`
  \\ `small_int (:α) j` by (simp[Abbr`j`,small_int_w2n])
  \\ `k = Smallnum j`
  by (
    fs[small_int_def,Abbr`j`]
    \\ qmatch_goalsub_abbrev_tac`w2n w8`
    \\ Q.ISPEC_THEN`w8`strip_assume_tac w2n_lt
    \\ simp[integer_wordTheory.i2w_def,Smallnum_i2w]
    \\ simp[Abbr`k`,WORD_MUL_LSL]
    \\ simp[GSYM word_mul_n2w]
    \\ simp[w2w_def] )
  \\ simp[]
  \\ match_mp_tac IMP_memory_rel_Number
  \\ fs[]
QED

Theorem assign_Const:
   (?i. op = IntOp (Const i)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ fs [do_app,allowed_op_def,oneline do_int_app_def]
  \\ gvs[AllCaseEqs()]
  \\ rpt var_eq_tac
  \\ fs [assign_def]
  \\ Cases_on `i` \\ fs []
  \\ fs [wordSemTheory.evaluate_def,wordSemTheory.word_exp_def]
  \\ fs [state_rel_def,wordSemTheory.set_var_def,set_var_def,
        lookup_insert,adjust_var_11]
  \\ rw [] \\ fs []
  \\ fs[option_le_max_right]
  \\ asm_exists_tac \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac word_ml_inv_insert \\ fs []
  \\ TRY (match_mp_tac word_ml_inv_zero) \\ fs []
  \\ TRY (match_mp_tac word_ml_inv_num) \\ fs []
  \\ TRY (match_mp_tac word_ml_inv_neg_num) \\ fs []
QED

Theorem assign_GlobalsPtr:
   op = GlobOp GlobalsPtr ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ fs [do_app,allowed_op_def]
  \\ gvs [AllCaseEqs()]
  \\ fs [assign_def,wordSemTheory.evaluate_def,wordSemTheory.word_exp_def,
         wordSemTheory.get_store_def,wordSemTheory.set_var_def]
  \\ fs [state_rel_thm,set_var_def]
  \\ fs [the_global_def,miscTheory.the_def]
  \\ fs [FLOOKUP_DEF,wordSemTheory.set_var_def,lookup_insert,
         adjust_var_11,miscTheory.the_def,set_var_def]
  \\ conj_tac >- rw []
  \\ conj_tac >- fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ pop_assum mp_tac
  \\ match_mp_tac memory_rel_rearrange
  \\ fs [] \\ rw [] \\ fs [the_def]
QED

Theorem assign_Global:
   (∃n. op = GlobOp (Global n)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  \\ fs [do_app,CaseEq"list",CaseEq"dataSem$v",CaseEq"bool"]
  \\ gvs [AllCaseEqs(),set_var_def]
  \\ rveq \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ ‘∃curr.
        FLOOKUP t.store CurrHeap = SOME (Word curr) ∧
        glob_real_inv c curr (FLOOKUP t.store Globals) (FLOOKUP t.store GlobReal)’
          by fs [memory_rel_def,heap_in_memory_store_def,state_rel_def]
  \\ fs [glob_real_inv_def]
  \\ fs [assign_def] \\ eval_tac \\ fs [state_rel_thm,option_le_max_right]
  \\ gvs [the_global_def,miscTheory.the_def]
  \\ qmatch_asmsub_abbrev_tac ‘(xs1 ++ [(RefPtr T ptr,t.store ' Globals)] ++ xs2)’
  \\ ‘memory_rel c t.be (THE x.tstamps) x.refs x.space t.store t.memory
          t.mdomain ((RefPtr T ptr,t.store ' Globals) :: (xs1 ++ xs2))’ by
      (first_x_assum (fn th => mp_tac th \\ match_mp_tac memory_rel_rearrange)
       \\ fs [] \\ rw [] \\ fs [])
  \\ drule0 (memory_rel_Deref' |> GEN_ALL) \\ fs []
  \\ disch_then drule \\ strip_tac \\ fs []
  \\ drule memory_rel_RefPtr_IMP' \\ fs [] \\ strip_tac
  \\ gvs [get_real_simple_addr_def]
  \\ gvs[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ gvs [FLOOKUP_DEF]
  \\ fs [lookup_insert,adjust_var_11]
  \\ rw [] \\ fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
  \\ fs [] \\ rw [] \\ fs []
QED

Theorem assign_SetGlobal:
   (∃n. op = GlobOp (SetGlobal n)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  \\ fs [do_app,allowed_op_def] \\ every_case_tac \\ fs [] \\ clean_tac
  \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_1] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [bvlSemTheory.Unit_def] \\ rveq
  \\ fs [GSYM bvlSemTheory.Unit_def] \\ rveq
  \\ fs [assign_def] \\ eval_tac \\ fs [state_rel_thm]
  \\ rfs [the_global_def,miscTheory.the_def]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs []
  \\ imp_res_tac get_vars_1_IMP \\ fs []
  \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_1] \\ clean_tac
  \\ qmatch_goalsub_abbrev_tac ‘(_,_)::(xs1++[(RefPtr br ref_ptr,_)]++xs2)’
  \\ strip_tac
  \\ ‘memory_rel c t.be (THE x.tstamps) x.refs x.space t.store t.memory t.mdomain
        ((RefPtr br ref_ptr,t.store ' Globals)::(h,a1')::(xs1 ++ xs2))’ by
      (first_x_assum (fn th => mp_tac th \\ match_mp_tac memory_rel_rearrange)
       \\ fs [] \\ rw [] \\ fs [])
  \\ ‘∃curr.
        FLOOKUP t.store CurrHeap = SOME (Word curr) ∧
        glob_real_inv c curr (FLOOKUP t.store Globals) (FLOOKUP t.store GlobReal)’
          by fs [memory_rel_def,heap_in_memory_store_def,state_rel_def]
  \\ drule memory_rel_RefPtr_IMP' \\ fs [] \\ strip_tac
  \\ fs [glob_real_inv_def]
  \\ fs [wordSemTheory.get_vars_def,AllCaseEqs()]
  \\ ‘memory_rel c t.be (THE x.tstamps) x.refs x.space t.store t.memory t.mdomain
        ((h,a1')::(RefPtr br ref_ptr,t.store ' Globals)::(xs1 ++ xs2))’ by
      (first_x_assum (fn th => mp_tac th \\ match_mp_tac memory_rel_rearrange)
       \\ fs [] \\ rw [] \\ fs [])
  \\ drule0 (memory_rel_Update' |> GEN_ALL) \\ fs []
  \\ disch_then drule \\ strip_tac
  \\ fs [] \\ gvs[get_real_simple_addr_def]
  \\ gvs[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,wordSemTheory.mem_store_def,
         wordSemTheory.get_var_def]
  \\ gvs [FLOOKUP_DEF,wordSemTheory.word_exp_def,data_to_wordTheory.Unit_def]
  \\ fs [lookup_insert,adjust_var_11]
  \\ rw [] \\ fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ match_mp_tac memory_rel_Unit \\ fs []
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
  \\ rw [] \\ fs []
QED

Theorem assign_SetGlobalsPtr:
   op = GlobOp SetGlobalsPtr ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ fs [do_app,allowed_op_def]
  \\ gvs [AllCaseEqs()]
  \\ drule_all state_rel_get_vars_IMP \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ fs [assign_def]
  \\ fs[wordSemTheory.evaluate_def,wordSemTheory.word_exp_def,Unit_def]
  \\ ‘isWord h’ by
   (fs [state_rel_def,wordSemTheory.set_var_def,lookup_insert,
         adjust_var_11,miscTheory.the_def,set_var_def,
         wordSemTheory.set_store_def,code_oracle_rel_def,FLOOKUP_UPDATE]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ drule0 (GEN_ALL word_ml_inv_get_vars_IMP)
    \\ disch_then drule0
    \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def]
    \\ strip_tac
    \\ gvs [word_ml_inv_def,abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def]
    \\ fs [word_addr_def,isWord_def])
  \\ Cases_on ‘h’ \\ fs [isWord_def]
  \\ gvs [wordSemTheory.get_vars_def,AllCaseEqs()]
  \\ rename [‘_ = SOME (Word www)’]
  \\ eval_tac \\ fs [state_rel_thm,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs []
  \\ imp_res_tac get_vars_1_IMP \\ fs []
  \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def]
  \\ rename [‘(real_addr c (adjust_var y))’]
  \\ strip_tac
  \\ drule_all memory_rel_RefPtr_IMP' \\ strip_tac
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
  \\ rw [] \\ rw [] \\ fs []
  \\ fs [state_rel_def,wordSemTheory.set_var_def,lookup_insert,
         adjust_var_11,miscTheory.the_def,set_var_def,word_sh_def,
         wordSemTheory.set_store_def,code_oracle_rel_def,FLOOKUP_UPDATE,
         wordSemTheory.the_words_def,word_op_def,memory_rel_def]
  \\ rw [] \\ fs [option_le_max_right]
  \\ qexists_tac ‘heap’
  \\ qexists_tac ‘limit’
  \\ qexists_tac ‘a'’
  \\ qexists_tac ‘sp’
  \\ qexists_tac ‘sp1’
  \\ qexists_tac ‘gens’
  \\ fs [heap_in_memory_store_def,FLOOKUP_UPDATE,glob_real_inv_def]
  \\ fs [the_global_def,miscTheory.the_def]
  \\ gvs [get_real_simple_addr_def]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (GEN_ALL word_ml_inv_get_vars_IMP)
  \\ disch_then drule0
  \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def,option_le_max_right]
  \\ strip_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac word_ml_inv_insert \\ fs []
  \\ match_mp_tac word_ml_inv_Unit
  \\ pop_assum mp_tac \\ fs []
  \\ match_mp_tac word_ml_inv_rearrange \\ rw [] \\ fs []
  \\ fs [FAPPLY_FUPDATE_THM]
QED

Theorem IMP:
   b1 \/ b2 <=> ~b1 ==> b2
Proof
  Cases_on `b1` \\ Cases_on `b2` \\ fs []
QED

Definition memcopy_def:
  memcopy k a1 a2 m dm =
    if k = 0n then SOME m else
      if a1 IN dm /\ a2 IN dm then
        memcopy (k-1) (a1+bytes_in_word) (a2+bytes_in_word) ((a2 =+ m a1) m) dm
      else NONE
End

Theorem MemCopy_thm:
   !ret_val l1 l2 k a1 a2 (s:('a,'c,'ffi) wordSem$state) m dm m1.
      memcopy k a1 a2 m dm  = SOME m1 /\
      s.memory = m /\ s.mdomain = dm /\
      lookup MemCopy_location s.code = SOME (5,MemCopy_code) /\
      k <= s.clock /\ 4 * k < dimword (:'a) /\
      get_var 0 s = SOME (Loc l1 l2) /\
      get_var 2 s = SOME (Word (n2w (4 * k))) /\
      get_var 4 s = SOME (Word (a1:'a word)) /\
      get_var 6 s = SOME (Word a2) /\
      get_var 8 s = SOME ret_val ==>
      ?smx.
      evaluate (MemCopy_code,s) =
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
  \\ qmatch_goalsub_abbrev_tac `(MemCopy_code,s5)`
  \\ first_x_assum (qspecl_then [`a1 + bytes_in_word`,
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
  \\ fs [good_dimindex_def] \\ rfs [shift_def]
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

Theorem INTRO_IS_SOME:
   (?v. x = SOME v) <=> IS_SOME x
Proof
  Cases_on `x` \\ fs []
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
  \\ `small_int (:'a) (& startptr)` by
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
  rpt strip_tac \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [do_app,allowed_op_def] \\ every_case_tac \\ fs [] \\ rveq
  \\ `?startptr len. i = &startptr /\ i' = & len` by
       (Cases_on `i` \\ Cases_on `i'` \\ fs [] \\ NO_TAC) \\ rveq \\ fs []
  \\ imp_res_tac state_rel_IMP_tstamps \\ fs [with_fresh_ts_def]
  \\ rveq \\ fs []
  \\ pop_assum mp_tac
  \\ pop_assum mp_tac
  \\ fs []
  \\ fs [integerTheory.int_gt,integerTheory.INT_ADD,NOT_LESS]
  \\ fs [IMP] \\ strip_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ clean_tac
  \\ `?a1 a2 a3 a4 arest. args = a1::a2::a3::a4::arest` by
   (Cases_on `args` \\ fs []
    \\ rpt (rename1 `LENGTH args = _` \\ Cases_on `args` \\ fs []) \\ NO_TAC)
  \\ rveq \\ fs []
  \\ rewrite_tac [assign_ConsExtend_expand] \\ fs []
  \\ CASE_TAC THEN1
     (simp [check_lim_def,space_consumed_def]
      \\ fs [check_lim_def,option_le_max_right,state_rel_def,
          space_consumed_def,encode_header_def,CaseEq"bool",arch_size_def,
          limits_inv_def,good_dimindex_def,dimword_def] >>
      rfs[] >> metis_tac[option_le_trans])
  \\ fs []
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [get_vars_SOME_IFF_eq] \\ rveq \\ fs []
  \\ full_simp_tac std_ss [GSYM wordSemTheory.get_var_def]
  \\ rpt_drule0 evaluate_BignumHalt2
  \\ rename1 `LENGTH t7 = LENGTH ys7`
  \\ `?w4. get_var (adjust_var a4) t = SOME (Word w4) /\
           (~(w4 ' 0) ==> small_int (:α) (&(len + LENGTH t7)) /\
                          w4 = Smallnum (&(len + LENGTH t7)))` by
   (fs [state_rel_thm] \\ eval_tac
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
        drule state_rel_get_var_Number_IMP_alt >>
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
  \\ `state_rel c l1 l2 x t5 [] locs` by
       (unabbrev_all_tac \\ fs [state_rel_insert_1])
  \\ qmatch_goalsub_abbrev_tac `AllocVar c lim nms` \\ fs [] \\ strip_tac
  \\ `?xx. dataSem$cut_env nms x.locals = SOME xx` by
   (fs [dataSemTheory.cut_env_def,dataLangTheory.op_requires_names_def]
    \\ fs [EVAL ``op_space_reset (BlockOp (ConsExtend tag))``]
    \\ Cases_on `names_opt` \\ fs [cut_state_opt_def]
    \\ fs [cut_state_def,dataSemTheory.cut_env_def]
    \\ every_case_tac \\ fs [] \\ rveq \\ fs [domain_inter]
    \\ unabbrev_all_tac \\ fs [get_names_def]
    \\ simp_tac bool_ss [domain_list_insert,SUBSET_DEF]
    \\ imp_res_tac get_vars_IMP_domain \\ fs [domain_inter]
    \\ fs [EVERY_MEM] \\ rw [] \\ fs [SUBSET_DEF] \\ NO_TAC)
  \\ `get_var 1 t5 = SOME (Word (n2w (4 * (len + LENGTH t7))))` by
   (fs [wordSemTheory.get_var_def,Abbr`t5`,lookup_insert] \\ rveq
    \\ fs [Smallnum_def] \\ NO_TAC)
  \\ rpt_drule0 AllocVar_thm
  \\ impl_tac THEN1
    (unabbrev_all_tac \\ fs []
     \\ fs [dimword_def,good_dimindex_def,state_rel_thm])
  \\ reverse (Cases_on `res`)
  THEN1
    (fs [check_lim_def] >>
     rpt strip_tac >> fs[] >>
     rveq >> fs[option_le_max_right] >>
     (* TODO: horrendous case of generated names *)
     reverse(Cases_on `(4 * (len + LENGTH ys'³')) MOD dimword (:α) DIV 4 < lim`) >-
       (fs[Abbr`lim`,dimword_def,good_dimindex_def,state_rel_def,arch_size_def,limits_inv_def] >>
        rfs[] >>
        fs[NOT_LESS] >>
        fs[X_LE_DIV] >>
        qmatch_asmsub_abbrev_tac `nnn MOD mmm` >>
        `0 < mmm` by(fs[Abbr`mmm`]) >>
        dxrule_then (qspec_then `nnn` strip_assume_tac) MOD_LESS_EQ >>
        drule_then (drule_then strip_assume_tac) LESS_EQ_TRANS >>
        fs[Abbr`nnn`,Abbr`mmm`]) >>
     res_tac >>
     fs[space_consumed_def] >>
     rfs[] >>
     spose_not_then strip_assume_tac >> fs[] >>
     `arch_size x.limits = dimindex(:'a)`
       by(rfs[state_rel_def,good_dimindex_def,dimword_def,arch_size_def,limits_inv_def]) >>
     fs[] >>
     fs[dimword_def] >>
     `4*(len + LENGTH ys'³') < 2 ** dimindex (:α) DIV 4` by
       (qpat_x_assum `len + _ < 2 ** dimindex (:α) DIV 16` mp_tac >>
        disch_then (mp_tac o ONCE_REWRITE_RULE [DECIDE ``n < p:num ⇔ 4 * n < 4 * p``]) >>
        strip_tac >> drule_then match_mp_tac LESS_LESS_EQ_TRANS >>
        fs[good_dimindex_def,state_rel_def]
       ) >>
     `4*(len + LENGTH ys'³') < 2 ** dimindex (:α)`
       by(drule_then match_mp_tac LESS_LESS_EQ_TRANS >>
          fs[good_dimindex_def,state_rel_def]) >>
     fs[MOD_LESS] >>
     dxrule_then dxrule LESS_EQ_LESS_TRANS >> strip_tac >>
     fs[MULT_DIV |> ONCE_REWRITE_RULE [MULT_COMM]] >>
     fs[cut_state_opt_def,cut_state_def,CaseEq"option",
        dataLangTheory.op_requires_names_def,dataLangTheory.op_space_reset_def,
        cut_locals_def,cut_env_def,get_names_def] >> rveq >> rfs[] >>
     qsuff_tac `inter s.locals (inter names nms) = inter s.locals names` >-
       (disch_then (SUBST_ALL_TAC o ONCE_REWRITE_RULE [inter_assoc]) >> fs[]) >>
     rw[lookup_inter_alt,domain_inter,Abbr `nms`,get_names_def,domain_list_insert_thm] >>
     rw[] >> fs[]
    )
  \\ fs [check_lim_def]
  \\ strip_tac
  \\ ntac 2 (pop_assum mp_tac)
  \\ simp [Once state_rel_thm]
  \\ rpt strip_tac
  \\ qabbrev_tac `ys3 = ys'''` \\ pop_assum kall_tac
  \\ `4 * (len + LENGTH ys3) < dimword (:'a)` by
   (fs [small_int_def] \\ rfs []
    \\ fs [dimword_def,good_dimindex_def,state_rel_def]
    \\ rfs [] \\ fs [] \\ NO_TAC)
  \\ `((4 * (len + LENGTH ys3)) MOD dimword (:α) DIV 4 + 1) =
      len + LENGTH ys3 + 1` by
   (qsuff_tac `(4 * (len + LENGTH ys3)) < dimword (:α)`
    THEN1 fs [DIV_EQ_X,MULT_CLAUSES]
    \\ fs [dimword_def,good_dimindex_def] \\ rfs [] \\ fs [])
  \\ fs [] \\ fs [state_rel_thm]
  \\ drule0 memory_rel_IMP_free_space \\ strip_tac \\ fs []
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [lookup_insert] \\ rveq
  \\ qabbrev_tac `tot_len = len + LENGTH ys3`
  \\ `lookup (adjust_var a2) s1.locals = SOME (Word (n2w (4 * startptr))) /\
      lookup (adjust_var a3) s1.locals = SOME (Word (n2w (4 * len))) /\
      lookup (adjust_var a4) s1.locals = SOME (Word (n2w (4 * tot_len))) /\
      ?ws1 w_ptr a_ptr.
        get_vars (MAP adjust_var t7) s1 = SOME ws1 /\
        lookup (adjust_var a1) s1.locals = SOME (Word w_ptr) /\
        (l' <> [] ==> get_real_addr c s1.store w_ptr = SOME a_ptr) /\
        memory_rel c s1.be next_stamp x.refs (len + (LENGTH ys3 + 1)) s1.store
         s1.memory s1.mdomain
            ((Block n0 n' l',Word w_ptr)::(ZIP (ys7,ws1) ++
               join_env xx
                 (toAList (inter s1.locals (adjust_set xx))) ++
               [(the_global x.global,s1.store ' Globals)] ++
               flat x.stack s1.stack))` by
   (full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ `get_vars (a1::a2::a3::a4::t7) xx =
          SOME (Block n0 n' l'::Number (&startptr)::Number (&len)::
                Number (&tot_len)::ys7)` by
     (rpt_drule0 get_vars_cut_env \\ disch_then match_mp_tac
      \\ fs[Abbr`nms`,domain_list_insert,EVERY_MEM] \\ NO_TAC)
    \\ `?w1 w2 w3 w4 ws1. get_vars
          (adjust_var a1::adjust_var a2::adjust_var a3::adjust_var a4::
             MAP adjust_var t7) s1 = SOME (w1::w2::w3::w4::ws1) /\
         LENGTH ws1 = LENGTH t7` by
     (qsuff_tac `!xs bs. get_vars xs xx = SOME bs ==>
                   ?bs1. get_vars (MAP adjust_var xs) s1 = SOME bs1`
      THEN1
       (disch_then drule0 \\ strip_tac \\ fs []
        \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
        \\ imp_res_tac get_vars_IMP_LENGTH_word \\ fs []
        \\ rpt (Cases_on `bs1` \\ fs [] \\ TRY (rename1 `SUC _ = LENGTH bs1`)))
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
    \\ rw [] \\ fs [] \\ NO_TAC)
  \\ fs []
  \\ `10 < dimindex (:'a)` by (fs [good_dimindex_def] \\ NO_TAC)
  \\ once_rewrite_tac [list_Seq_def]
  \\ `n2w (4 * tot_len) ⋙ 2 = n2w tot_len:'a word` by
      (rewrite_tac [GSYM w2n_11,w2n_lsr,w2n_n2w] \\ fs [] \\ rfs [] \\ NO_TAC)
  \\ fs [eq_eval,wordLangTheory.word_sh_def]
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
  \\ `?m1. store_list nfree ws2 s2.memory s2.mdomain = SOME m1 /\
           (word_list nfree ws2 *
            word_list_exists (nfree + bytes_in_word * n2w (LENGTH ws2))
             (len + (LENGTH ys7 + 1) − LENGTH ws2) * other)
                (fun2set (m1,s1.mdomain))` by
   (unabbrev_all_tac \\ fs []
    \\ drule0 IMP_store_list_SOME \\ fs []
    \\ disch_then (qspec_then `ws2` mp_tac)
    \\ imp_res_tac get_vars_IMP_LENGTH_word \\ fs []
    \\ strip_tac \\ fs [] \\ NO_TAC)
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
    \\ rfs [])
  \\ strip_tac
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ pop_assum kall_tac
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ `shift (:'a) < dimindex (:'a)` by
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
  \\ fs [] \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
  \\ fs [Abbr `s3`,eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval]
  \\ `(4 * len) < dimword (:α)` by
       (fs [dimword_def,good_dimindex_def,Abbr `tot_len`] \\ rfs [] \\ fs [])
  \\ simp []
  \\ `!n. IS_SOME (lookup n x.locals) <=> IS_SOME (lookup n xx)` by
   (qpat_x_assum `cut_env nms x.locals = SOME xx` mp_tac
    \\ fs [EVAL ``op_requires_names (BlockOp (ConsExtend tag))``]
    \\ qpat_x_assum `cut_state_opt names_opt s = SOME x` mp_tac
    \\ Cases_on `names_opt` \\ fs [cut_state_opt_def]
    \\ fs [cut_state_def,cut_env_def]
    \\ IF_CASES_TAC \\ fs []
    \\ strip_tac \\ rveq \\ fs []
    \\ strip_tac \\ rveq \\ fs [domain_inter]
    \\ rpt strip_tac \\ rveq
    \\ fs [lookup_inter_alt,Abbr `nms`,domain_list_insert,SUBSET_DEF,get_names_def]
    \\ metis_tac [])
  \\ `(inter s1.locals (adjust_set xx)) =
      (inter s1.locals (adjust_set x.locals))` by
   (qsuff_tac `domain (adjust_set xx) = domain (adjust_set x.locals)`
    THEN1 fs [spt_eq_thm,lookup_inter_alt]
    \\ fs [EXTENSION,domain_lookup] \\ rpt strip_tac
    \\ fs [optionTheory.IS_SOME_EXISTS]
    \\ fs [lookup_adjust_set,domain_lookup] \\ NO_TAC)
  \\ sg `join_env x.locals
          (toAList (inter s1.locals (adjust_set x.locals))) =
        join_env xx (toAList (inter s1.locals (adjust_set xx)))`
  THEN1
   (asm_rewrite_tac [join_env_def,MAP_EQ_f]
    \\ fs [MEM_FILTER,FORALL_PROD,MEM_toAList,lookup_inter_alt] \\ rw []
    \\ first_x_assum (qspec_then `p_1` mp_tac)
    \\ IF_CASES_TAC \\ fs []
    \\ first_x_assum (qspec_then `(p_1 − 2) DIV 2` mp_tac)
    \\ fs [cut_env_def] \\ rveq \\ fs []
    \\ fs [domain_lookup,lookup_adjust_set]
    \\ rfs [lookup_inter_alt])
  \\ rpt_drule0 memory_rel_store_list_to_unused \\ strip_tac
  \\ `encode_header c (4 * tag) tot_len = SOME full_header` by
   (fs [encode_header_def,make_header_def,Abbr `full_header`]
    \\ `n2w (4 * tot_len):'a word = n2w tot_len << 2` by
          fs [WORD_MUL_LSL,word_mul_n2w]
    \\ `2 + (dimindex (:α) − (c.len_size + 2)) = dimindex (:α) − c.len_size` by
         fs [memory_rel_def,heap_in_memory_store_def]
    \\ fs [] \\ unabbrev_all_tac \\ fs []
    \\ fs [good_dimindex_def] \\ rfs [dimword_def] \\ fs [])
  \\ rfs [get_vars_delete_lemma] \\ rveq \\ fs []
  \\ Cases_on `len = 0` \\ fs []
  THEN1
   (once_rewrite_tac [list_Seq_def] \\ simp [eq_eval]
    \\ fs [state_rel_thm,FAPPLY_FUPDATE_THM,lookup_insert,adjust_var_11]
    \\ fs [inter_insert_ODD_adjust_set,code_oracle_rel_def,FLOOKUP_UPDATE]
    \\ conj_tac THEN1 (rw [] \\ fs [])
    \\ conj_tac THEN1 (fs[option_le_max_right])
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ drule0 memory_rel_tl
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ strip_tac \\ rpt_drule0 memory_rel_Cons_alt
    \\ fs [Abbr`tot_len`] \\ imp_res_tac get_vars_IMP_LENGTH_word \\ fs []
    \\ full_simp_tac (std_ss++ARITH_ss) [GSYM LENGTH_NIL,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ fs [GSYM bytes_in_word_mul_eq_shift,AND_IMP_INTRO]
    \\ disch_then match_mp_tac
    \\ rfs []
    \\ drule0 IMP_store_list_SOME
    \\ disch_then (qspec_then `(Word full_header::ws1)` mp_tac)
    \\ simp_tac std_ss []
    \\ impl_tac THEN1 fs []
    \\ asm_rewrite_tac [] \\ simp_tac std_ss []
    \\ qspec_tac (`fun2set (m1,s1.mdomain)`,`ss`)
    \\ rewrite_tac [GSYM SEP_IMP_def,GSYM STAR_ASSOC]
    \\ match_mp_tac SEP_IMP_STAR
    \\ fs [SEP_IMP_REFL] \\ fs [SEP_IMP_def,SEP_T_def])
  \\ fs [list_Seq_def]
  \\ `?the_names. names_opt = SOME the_names` by
      (Cases_on `names_opt` \\ fs [EVAL ``op_requires_names (BlockOp (ConsExtend tag))``])
  \\ rveq \\ fs [get_names_def,cut_state_opt_def]
  \\ `lookup MemCopy_location s1.code = SOME (5,MemCopy_code)` by
     (qpat_x_assum `code_rel c _ _` mp_tac
      \\ simp [code_rel_def,stubs_def])
  \\ `s1.termdep <> 0` by
   (imp_res_tac wordSemTheory.evaluate_clock \\ fs []
    \\ unabbrev_all_tac \\ fs [])
  \\ fs [eq_eval] \\ pop_assum kall_tac
  \\ fs [cut_envs_adjust_sets_insert_ODD,domain_adjust_sets]
  \\ `?the_env. cut_env (adjust_sets the_names) s1.locals = SOME the_env` by
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
    \\ last_x_assum irule
    \\ qpat_x_assum ‘_ = SOME xx’ mp_tac
    \\ simp [dataSemTheory.cut_env_def]
    \\ strip_tac \\ gvs []
    \\ rewrite_tac [domain_inter,IN_INTER]
    \\ pop_assum mp_tac
    \\ simp [SUBSET_DEF,SF CONJ_ss]
    \\ qunabbrev_tac ‘nms’
    \\ simp [domain_list_insert])
  \\ drule cut_env_IMP_cut_envs \\ strip_tac
  \\ fs [] \\ simp [wordSemTheory.push_env_def]
  \\ Cases_on `env_to_list y2 s1.permute` \\ fs []
  \\ `n2w (4 * startptr) ≪ (shift (:α) − 2) =
      n2w startptr * bytes_in_word :'a word` by
    fs [good_dimindex_def,shift_def,bytes_in_word_def,word_mul_n2w,WORD_MUL_LSL]
  \\ rfs [] \\ fs []
  \\ fs []
  \\ qmatch_goalsub_abbrev_tac
    `insert 8 ar8 (insert 6 (Word ar6)
                   (insert 4 (Word ar4) (insert 2 _ (insert 0 ar0 _))))`
  \\ qmatch_goalsub_abbrev_tac `(MemCopy_code,s88)`
  \\ sg `?m2 ws2.
              memcopy len ar4 ar6 m1 s1.mdomain = SOME m2 /\
              (word_list nfree (Word full_header::(ws1 ++ ws2)) * SEP_T)
                (fun2set (m2,s1.mdomain)) /\ LENGTH ws2 = len /\
              memory_rel c s1.be next_stamp x.refs (len + (LENGTH ys3 + 1)) s1.store m2
               s1.mdomain
               ((ZIP (ys7 ++ TAKE len (DROP startptr l'),ws1 ++ ws2) ++
                   join_env xx
                     (toAList (inter s1.locals (adjust_set xx))) ++
                   [(the_global x.global,s1.store ' Globals)] ++
                   flat x.stack s1.stack))`
  THEN1
   (simp [Abbr`ar4`,Abbr`ar6`]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac IMP_memcopy \\ fs []
    \\ qexists_tac `w_ptr`
    \\ qexists_tac `n0`
    \\ qexists_tac `other`
    \\ qexists_tac `n'`
    \\ qexists_tac `(len + (LENGTH ys3 + 1) − SUC (LENGTH ws1))`
    \\ qexists_tac `a1`
    \\ fs [] \\ rfs []
    \\ qpat_x_assum `_ = SOME (Word wx)` (fn th => fs [GSYM th])
    \\ rpt (pop_assum kall_tac)
    \\ fs [real_addr_def] \\ rw []
    \\ fs [eq_eval,FLOOKUP_UPDATE,wordSemTheory.get_store_def])
  \\ rpt_drule0 MemCopy_thm
  \\ disch_then (qspecl_then [`ar8`,`n`,`l`,`s88`] mp_tac)
  \\ impl_tac THEN1
   (unabbrev_all_tac \\ fs [wordSemTheory.get_var_def,lookup_insert]
    \\ match_mp_tac LESS_EQ_TRANS
    \\ qexists_tac `dimword (:α)`
    \\ conj_tac THEN1 (fs [dimword_def,good_dimindex_def] \\ rfs [])
    \\ fs [wordSemTheory.MustTerminate_limit_def])
  \\ strip_tac \\ fs []
  \\ qunabbrev_tac `s88` \\ fs [wordSemTheory.pop_env_def]
  \\ reverse IF_CASES_TAC >-
   (sg `F` \\ fs [] \\ pop_assum mp_tac \\ simp []
    \\ imp_res_tac env_to_list_domain
    \\ simp [domain_union,domain_fromAList_toAList,AC UNION_COMM UNION_ASSOC])
  \\ fs [state_rel_thm,code_oracle_rel_def,FLOOKUP_UPDATE,
         wordSemTheory.set_vars_def,alist_insert_def]
  \\ conj_tac THEN1
   (simp [lookup_union,lookup_fromAList,ALOOKUP_toAList,lookup_insert]
    \\ drule_all cut_envs_lookup_0 \\ simp [])
  \\ conj_tac THEN1
   (gen_tac \\ IF_CASES_TAC \\ simp []
    \\ fs [lookup_fromAList,lookup_insert,adjust_var_11]
    \\ asm_rewrite_tac [GSYM IS_SOME_EXISTS,IS_SOME_lookup_domain]
    \\ rename [‘kk ∈ _ ⇒ _’]
    \\ simp_tac std_ss [IN_UNION]
    \\ strip_tac
    \\ qpat_x_assum ‘_ = SOME (y1,y2)’ mp_tac
    \\ simp [wordSemTheory.cut_envs_def,CaseEq"option"]
    \\ simp [adjust_sets_def]
    \\ simp [wordSemTheory.cut_names_def,CaseEq"option"]
    \\ strip_tac \\ rpt var_eq_tac
    \\ simp [domain_inter,adjust_var_IN_adjust_set]
    \\ qpat_x_assum ‘cut_state the_names s = SOME x’ mp_tac
    \\ simp [dataSemTheory.cut_state_def,dataSemTheory.cut_env_def,CaseEq"option"]
    \\ strip_tac \\ rpt var_eq_tac \\ fs []
    \\ qpat_x_assum ‘cut_env (adjust_sets the_names) s1.locals = _’ mp_tac
    \\ simp [wordSemTheory.cut_env_def,CaseEq"option",EXISTS_PROD]
    \\ simp [adjust_sets_def]
    \\ simp [wordSemTheory.cut_envs_def,CaseEq"option",EXISTS_PROD]
    \\ simp_tac (srw_ss()) [wordSemTheory.cut_names_def,CaseEq"option",EXISTS_PROD]
    \\ strip_tac
    \\ qsuff_tac ‘kk ∈ domain the_names’
    >- (simp [] \\ strip_tac
        \\ fs [SUBSET_DEF]
        \\ first_x_assum irule
        \\ simp [adjust_var_IN_adjust_set])
    \\ qpat_x_assum ‘∀n. _ ⇔ IS_SOME (lookup n xx)’ $ mp_tac o GSYM
    \\ rewrite_tac [IS_SOME_lookup,domain_inter]
    \\ strip_tac \\ fs [])
  \\ conj_tac THEN1
   (drule evaluate_stack_max_le >>
    simp[option_le_max,stack_size_eq,AC option_add_comm option_add_assoc])
  \\ conj_tac THEN1
   (drule_then match_mp_tac option_le_trans >>
    imp_res_tac stack_rel_IMP_size_of_stack >>
    rw[option_le_max,option_le_max_right,AC option_add_comm option_add_assoc,
       stack_size_eq,option_le_eq_eqns,option_le_add])
  \\ simp [FAPPLY_FUPDATE_THM]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ rewrite_tac [inter_union_distrib]
  \\ ‘inter (fromAList (toAList y1)) (adjust_set x.locals) = LN’ by
    (irule cut_envs_inter
     \\ first_assum $ irule_at $ Pos hd
     \\ gvs [cut_state_def,CaseEq"option"]
     \\ last_x_assum $ irule_at Any)
  \\ simp []
  \\ sg `join_env xx (toAList (inter s1.locals (adjust_set xx))) =
         join_env x.locals (toAList (inter (fromAList q) (adjust_set x.locals)))`
  THEN1
   (fs [wordSemTheory.cut_env_def] \\ rveq \\ res_tac
    \\ fs [cut_state_def,cut_env_def] \\ rveq
    \\ Cases_on `domain the_names ⊆ domain s.locals` \\ fs [] \\ rveq \\ fs []
    \\ fs [join_env_def]
    \\ match_mp_tac (METIS_PROVE [] ``f x = g x /\ x = y ==> f x = g y``)
    \\ conj_tac THEN1
     (fs [MAP_EQ_f,FORALL_PROD,MEM_FILTER,MEM_toAList,lookup_inter_alt]
      \\ rpt strip_tac \\ rw [] \\ sg `F` \\ fs []
      \\ pop_assum mp_tac \\ fs [Abbr `nms`,domain_list_insert])
    \\ AP_TERM_TAC \\ AP_TERM_TAC
    \\ fs [spt_eq_thm,lookup_inter_alt]
    \\ rw [] \\ fs []
    \\ drule0 env_to_list_lookup_equiv
    \\ fs [lookup_insert,lookup_fromAList,adjust_var_11]
    \\ rpt strip_tac \\ fs []
    \\ gvs [wordSemTheory.cut_envs_def,CaseEq"option",
            wordSemTheory.cut_names_def,adjust_sets_def]
    \\ fs [lookup_inter_alt] \\ rw []
    \\ sg `F` \\ fs [] \\ pop_assum mp_tac \\ simp []
    \\ qpat_x_assum `_ IN _` mp_tac
    \\ fs [IN_domain_adjust_set_inter])
  \\ fs [] \\ pop_assum kall_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 memory_rel_Cons_alt
  \\ disch_then (qspecl_then [`tag`,`full_header`] mp_tac)
  \\ reverse impl_tac
  THEN1 fs [shift_lsl,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [Abbr `tot_len`] \\ CCONTR_TAC \\ fs [DROP_NIL]
QED

Theorem assign_Cons:
   (?tag. op = BlockOp (Cons tag)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
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
    \\ qexists_tac `Data (Word (n2w (16 * tag + 2)))`
    \\ qexists_tac `hs` \\ fs [word_addr_def]
    \\ reverse conj_tac
    THEN1 (fs [GSYM word_mul_n2w,GSYM word_add_n2w,BlockNil_and_lemma])
    \\ `n2w (16 * tag + 2) = BlockNil tag : 'a word` by
         fs [BlockNil_def,WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
    \\ fs [cons_thm_EMPTY])
  \\ fs [assign_def] \\ CASE_TAC \\ fs []
  >-
    (fs[state_rel_def]>>
     conj_tac >- metis_tac[backendPropsTheory.option_le_trans,do_app_stack_max,option_le_max_right] >>
     strip_tac >>
     fs[do_app,CaseEq"bool",CaseEq"option"] >>
     imp_res_tac get_vars_IMP_LENGTH >>
     rveq >> fs[arch_size_def,limits_inv_def,good_dimindex_def,encode_header_def] >>
     rfs[dimword_def,with_fresh_ts_def,consume_space_def,
         IS_SOME_EXISTS] >>
     rveq >> fs[check_lim_def] >> rveq >> fs[]
    )
  \\ fs [do_app,allowed_op_def] \\ every_case_tac \\ fs []
  \\ imp_res_tac state_rel_IMP_tstamps \\ fs [with_fresh_ts_def]
  \\ rveq \\ fs []
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ clean_tac
  \\ fs [consume_space_def] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
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
  \\ disch_then (qspecl_then [`3::MAP adjust_var args`,`1`] mp_tac)
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

Theorem assign_FFI:
   (?n. op = FFI n) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ drule data_to_word_gcProofTheory.cut_env_IMP_cut_env
  \\ disch_then $ qspecl_then [‘x.locals’,‘THE names_opt’] mp_tac
  \\ impl_tac
  >-
   (gvs [dataLangTheory.op_requires_names_def]
    \\ Cases_on ‘names_opt’
    \\ gvs [cut_state_opt_def,cut_state_def,CaseEq"option"])
  \\ strip_tac
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ drule data_to_word_gcProofTheory.state_rel_cut_env_cut_env
  \\ pop_assum $ ASSUME_NAMED_TAC "old"
  \\ disch_then $ drule_at $ Pos last
  \\ disch_then $ qspec_then ‘x.locals’ mp_tac
  \\ impl_tac >-
   (gvs [dataLangTheory.op_requires_names_def]
    \\ Cases_on ‘names_opt’
    \\ gvs [cut_state_opt_def,cut_state_def,CaseEq"option",
            cut_env_def,lookup_inter_alt,domain_inter])
  \\ ‘(x with locals := x.locals) = x’ by gvs [dataSemTheory.state_component_equality]
  \\ pop_assum $ rewrite_tac o single
  \\ strip_tac
  \\ simp []
  \\ fs[do_app,allowed_op_def] \\ clean_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ rename [‘get_vars [e1;e2] x.locals’]
  \\ fs [bvlSemTheory.Unit_def] \\ rveq
  \\ fs [GSYM bvlSemTheory.Unit_def] \\ rveq
  \\ imp_res_tac get_vars_2_imp
  \\ qabbrev_tac ‘ty = t with locals := y’
  \\ fs[state_rel_thm,set_var_def,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP )
  \\ qunabbrev_tac ‘ty’
  \\ strip_tac
  \\ fs[get_vars_def]
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ rpt_drule0 memory_rel_ByteArray_IMP
  \\ drule0 memory_rel_tl \\ strip_tac
  \\ rpt_drule0 memory_rel_ByteArray_IMP
  \\ pop_assum kall_tac
  \\ ntac 2 strip_tac \\ clean_tac
  \\ simp[assign_def,list_Seq_def] \\ eval_tac
  \\ ‘get_var (adjust_var e1) t = SOME (Word w') ∧
      get_var (adjust_var e2) t = SOME (Word w)’ by
    (gvs [wordSemTheory.get_var_def,wordSemTheory.get_vars_def,AllCaseEqs()]
     \\ conj_tac \\ drule_then irule cut_env_lookup \\ simp [])
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (Word _)`
     (fn thm => rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ simp[]
  \\ rename1`_ ∧ ffi_name = «»`
  \\ Cases_on`¬c.call_empty_ffi ∧ ffi_name = «»`
  >- (
    fs[wordSemTheory.evaluate_def]
    \\ ntac 2 strip_tac
    \\ simp[Unit_def,wordSemTheory.word_exp_def]
    \\ conj_tac
    >- (
      qhdtm_x_assum`call_FFI`mp_tac
      \\ simp[ffiTheory.call_FFI_def] )
    \\ LABEL_X_ASSUM "old" assume_tac
    \\ gvs [state_rel_thm]
    \\ simp[wordSemTheory.set_var_def,lookup_insert,option_le_max_right]
    \\ conj_tac >- (rw[] \\ metis_tac[])
    >> full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert
    >> simp[option_le_max_right]
    >> full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ match_mp_tac memory_rel_Unit
    \\ DEP_REWRITE_TAC[insert_unchanged]
    \\ fs[FLOOKUP_DEF,ffiTheory.call_FFI_def]
    \\ metis_tac[memory_rel_zero_space])
  \\ pop_assum (SUBST_ALL_TAC o EQF_INTRO)
  \\ rewrite_tac[]
  \\ eval_tac
  \\ qpat_abbrev_tac`tt = t with locals := _`
  \\ `get_var (adjust_var e1) tt = get_var (adjust_var e1) t`
  by fs[Abbr`tt`,wordSemTheory.get_var_def,lookup_insert]
  \\ `get_var (adjust_var e2) tt = get_var (adjust_var e2) t`
  by fs[Abbr`tt`,wordSemTheory.get_var_def,lookup_insert]
  \\ rfs[]
  \\ ‘get_var (adjust_var e1) tt = SOME (Word w') ∧
      get_var (adjust_var e2) tt = SOME (Word w)’ by fs [wordSemTheory.get_var_def]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (Word _)`
     (fn thm=> rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ `tt.store = t.store` by simp[Abbr`tt`]
  \\ simp[]
  \\ qpat_abbrev_tac`ex1 = if ffi_name = «» then _ else _`
  \\ qpat_abbrev_tac`ex2 = if ffi_name = «» then _ else _`
  \\ IF_CASES_TAC >- ( fs[shift_def] )
  \\ simp[wordSemTheory.get_var_def,lookup_insert]
  \\ qpat_x_assum`¬_`kall_tac
  \\ BasicProvers.TOP_CASE_TAC
  >- (
    `F` suffices_by rw[]
    \\ pop_assum mp_tac
    \\ simp[bvi_to_dataTheory.op_requires_names_eqn])
  \\ qpat_abbrev_tac`ttt = t with locals := _`
  \\ `get_var (adjust_var e1) ttt = get_var (adjust_var e1) t`
  by fs[Abbr`ttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ `get_var (adjust_var e2) ttt = get_var (adjust_var e2) t`
  by fs[Abbr`ttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ rfs[]
  \\ ‘get_var (adjust_var e1) ttt = SOME (Word w') ∧
      get_var (adjust_var e2) ttt = SOME (Word w)’ by fs [wordSemTheory.get_var_def]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (WORD _)`
     (fn thm=> rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ `ttt.store = t.store` by simp[Abbr`ttt`]
  \\ simp[]
  \\ qunabbrev_tac`ex1`
  \\ qunabbrev_tac`ex2`
  \\ Cases_on`ffi_name = «»` \\ fs[]
  >- (
    eval_tac
    \\ fs[lookup_insert,wordSemTheory.word_exp_def,ffiTheory.call_FFI_def]
    \\ fs[read_bytearray_def,wordSemTheory.write_bytearray_def]
    \\ fs[cut_env_adjust_sets_insert_ODD]
    \\ qmatch_goalsub_abbrev_tac`read_bytearray aa len g`
    \\ qmatch_asmsub_rename_tac`LENGTH ls + 4`
    \\ qispl_then[`ls`,`LENGTH ls`,`aa`]mp_tac IMP_read_bytearray_GENLIST
    \\ impl_tac >- simp[]
    \\ `len = LENGTH ls`
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
    \\ conj_tac >- rw []
    >> full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ match_mp_tac memory_rel_Unit \\ fs[]
    \\ qpat_x_assum ‘memory_rel _ _ _ _ _ _ _ _ _’ assume_tac
    \\ dxrule memory_rel_tl \\ strip_tac
    \\ dxrule memory_rel_tl
    \\ rpt $ qpat_x_assum ‘memory_rel _ _ _ _ _ _ _ _ _’ kall_tac
    \\ strip_tac
    \\ drule memory_rel_zero_space
    \\ rename [‘(insert n9 (ByteArray F l9) x.refs)’]
    \\ qsuff_tac ‘insert n9 (ByteArray F l9) x.refs = x.refs’ >- simp []
    \\ irule sptreeTheory.insert_unchanged
    \\ gvs [])
  \\ eval_tac
  \\ qpat_abbrev_tac`tttt = t with locals := _`
  \\ `get_var (adjust_var e1) tttt = get_var (adjust_var e1) t`
  by fs[Abbr`tttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ `get_var (adjust_var e2) tttt = get_var (adjust_var e2) t`
  by fs[Abbr`tttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ rfs[]
  \\ ‘get_var (adjust_var e1) tttt = SOME (Word w') ∧
      get_var (adjust_var e2) tttt = SOME (Word w)’ by fs [wordSemTheory.get_var_def]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (WORD _)`
     (fn thm=> rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ `tttt.store = t.store` by simp[Abbr`tttt`]
  \\ simp[]
  \\ IF_CASES_TAC >- ( fs[shift_def] )
  \\ simp[]
  \\ qpat_abbrev_tac`ttttt = t with locals := _`
  \\ `get_var (adjust_var e1) ttttt = get_var (adjust_var e1) t`
  by fs[Abbr`ttttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ `get_var (adjust_var e2) ttttt = get_var (adjust_var e2) t`
  by fs[Abbr`ttttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ qpat_x_assum`¬_` kall_tac
  \\ rfs[]
  \\ ‘get_var (adjust_var e1) ttttt = SOME (Word w') ∧
      get_var (adjust_var e2) ttttt = SOME (Word w)’ by fs [wordSemTheory.get_var_def]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (WORD _)`
     (fn thm => rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ `ttttt.store = t.store` by simp[Abbr`ttttt`]
  \\ simp[]
  \\ simp[wordSemTheory.get_var_def,lookup_insert]
  \\ qmatch_goalsub_abbrev_tac`read_bytearray aa len g`
  \\ qmatch_asmsub_rename_tac`LENGTH ls + 4`
  \\ qispl_then[`ls`,`LENGTH ls`,`aa`]mp_tac IMP_read_bytearray_GENLIST
  \\ impl_tac >- simp[]
  \\ `len = LENGTH ls`
  by (
    simp[Abbr`len`]
    \\ rfs[good_dimindex_def] \\ rfs[shift_def]
    \\ simp[bytes_in_word_def,GSYM word_add_n2w]
    \\ simp[dimword_def] )
  \\ fs[] \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`read_bytearray aa2 len2 _`
  \\ qispl_then[`l'`,`LENGTH l'`,`aa2`]mp_tac IMP_read_bytearray_GENLIST
  \\ impl_tac >- simp[]
  \\ `len2 = LENGTH l'`
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
  \\ conj_tac >- rw []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ match_mp_tac memory_rel_insert
  \\ rewrite_tac [APPEND]
  \\ match_mp_tac memory_rel_Unit \\ asm_rewrite_tac []
  \\ qpat_x_assum ‘memory_rel c t.be (THE x.tstamps) _ _ _ _ _ _’ assume_tac
  \\ rename [‘(RefPtr b7 n7,Word w7)::(RefPtr b8 n8,Word w8)::_’]
  \\ dxrule memory_rel_zero_space \\ strip_tac
  \\ dxrule memory_rel_tl \\ strip_tac
  \\ rename [‘insert n8 (ByteArray F new_bytes) x.refs’]
  \\ drule memory_rel_write_bytearray \\ simp []
  \\ disch_then $ qspec_then ‘new_bytes’ mp_tac
  \\ impl_tac
  >- gvs [ffiTheory.call_FFI_def,AllCaseEqs()]
  \\ strip_tac
  \\ dxrule memory_rel_tl \\ strip_tac
QED

Theorem assign_FFI_final:
   state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) [] locs /\
   (op_requires_names (FFI i) ==> names_opt <> NONE) /\
   cut_state_opt names_opt s = SOME x /\
   get_vars args x.locals = SOME vals /\
   t.termdep > 1 /\
   do_app (FFI i) vals x = Rerr(Rabort(Rffi_error f)) ==>
   ?q r.
     evaluate (FST (assign c n l dest (FFI i) args names_opt),t) = (q,r) /\
     option_le r.stack_max s.stack_max /\
     q <> SOME NotEnoughSpace /\ r.ffi = t.ffi /\ q = SOME(FinalFFI f)
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ drule data_to_word_gcProofTheory.cut_env_IMP_cut_env
  \\ disch_then $ qspecl_then [‘x.locals’,‘THE names_opt’] mp_tac
  \\ impl_tac
  >-
   (gvs [dataLangTheory.op_requires_names_def]
    \\ Cases_on ‘names_opt’
    \\ gvs [cut_state_opt_def,cut_state_def,CaseEq"option"])
  \\ strip_tac
  \\ rename [‘cut_env _ _ = SOME t_cut’]
  \\ ‘s.stack_max = x.stack_max’ by
   (gvs [dataLangTheory.op_requires_names_def]
    \\ Cases_on ‘names_opt’
    \\ gvs [cut_state_opt_def,cut_state_def,CaseEq"option"])
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ fs[do_app, allowed_op_def] \\ clean_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ gvs [AllCaseEqs()]
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ rename [‘get_vars [e1;e2] x.locals’]
  \\ fs [bvlSemTheory.Unit_def] \\ rveq
  \\ fs [GSYM bvlSemTheory.Unit_def] \\ rveq
  \\ imp_res_tac get_vars_2_imp
  \\ fs[state_rel_thm,set_var_def,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP )
  \\ strip_tac
  \\ fs[get_vars_def,AllCaseEqs()] \\ clean_tac
  \\ rpt_drule0 memory_rel_ByteArray_IMP
  \\ drule0 memory_rel_tl \\ strip_tac
  \\ rpt_drule0 memory_rel_ByteArray_IMP
  \\ pop_assum kall_tac
  \\ ntac 2 strip_tac \\ clean_tac
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (Word _)`
     (fn thm => rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ simp[assign_def,list_Seq_def] \\ eval_tac
  \\ simp[]
  \\ rename1`_ ∧ ffi_name = «»`
  \\ Cases_on`ffi_name = «»`
  >- (
    fs[wordSemTheory.evaluate_def]
    \\ ntac 2 strip_tac
    \\ simp[Unit_def,wordSemTheory.word_exp_def]
    \\ rveq
    \\ qhdtm_x_assum`call_FFI`mp_tac
    \\ simp[ffiTheory.call_FFI_def])
  \\ rpt disch_tac
  \\ rewrite_tac[]
  \\ eval_tac
  \\ qpat_abbrev_tac`tt = t with locals := _`
  \\ `get_var (adjust_var e1) tt = get_var (adjust_var e1) t`
  by fs[Abbr`tt`,wordSemTheory.get_var_def,lookup_insert]
  \\ `get_var (adjust_var e2) tt = get_var (adjust_var e2) t`
  by fs[Abbr`tt`,wordSemTheory.get_var_def,lookup_insert]
  \\ gvs[wordSemTheory.get_vars_def,CaseEq"option"]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (WORD _)`
     (fn thm=> rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ `tt.store = t.store` by simp[Abbr`tt`]
  \\ simp[]
  \\ IF_CASES_TAC >- ( fs[shift_def] )
  \\ simp[wordSemTheory.get_var_def,lookup_insert]
  \\ qpat_x_assum`¬_`kall_tac
  \\ BasicProvers.TOP_CASE_TAC
  >- (
    `F` suffices_by rw[]
    \\ pop_assum mp_tac
    \\ simp[bvi_to_dataTheory.op_requires_names_eqn])
  \\ qpat_abbrev_tac`ttt = t with locals := _`
  \\ `get_var (adjust_var e1) ttt = get_var (adjust_var e1) t`
  by fs[Abbr`ttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ `get_var (adjust_var e2) ttt = get_var (adjust_var e2) t`
  by fs[Abbr`ttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ rfs[]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (Word _)`
     (fn thm => rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ `ttt.store = t.store` by simp[Abbr`ttt`]
  \\ simp[]
  \\ eval_tac
  \\ qpat_abbrev_tac`tttt = t with locals := _`
  \\ `get_var (adjust_var e1) tttt = get_var (adjust_var e1) t`
  by fs[Abbr`tttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ `get_var (adjust_var e2) tttt = get_var (adjust_var e2) t`
  by fs[Abbr`tttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ rfs[]
  \\ ‘get_var (adjust_var e1) tttt = SOME (Word w') ∧
      get_var (adjust_var e2) tttt = SOME (Word w)’ by gvs [wordSemTheory.get_var_def]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (Word _)`
     (fn thm=> rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ `tttt.store = t.store` by simp[Abbr`tttt`]
  \\ simp[lookup_insert]
  \\ qpat_abbrev_tac`ttttt = t with locals := _`
  \\ `get_var (adjust_var e1) ttttt = get_var (adjust_var e1) t`
  by fs[Abbr`ttttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ `get_var (adjust_var e2) ttttt = get_var (adjust_var e2) t`
  by fs[Abbr`ttttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ simp [cut_env_adjust_sets_ODD]
  \\ qpat_x_assum`¬_` kall_tac
  \\ ‘get_var (adjust_var e1) ttttt = SOME (Word w') ∧
      get_var (adjust_var e2) ttttt = SOME (Word w)’ by gvs [wordSemTheory.get_var_def]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (Word _)`
     (fn thm=> rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ `ttttt.store = t.store` by simp[Abbr`ttttt`]
  \\ simp[]
  \\ simp[wordSemTheory.get_var_def,lookup_insert]
  \\ gvs [Abbr‘ttttt’,lookup_insert]
  \\ qmatch_goalsub_abbrev_tac`read_bytearray aa len g`
  \\ qmatch_asmsub_rename_tac`LENGTH ls + 4`
  \\ qispl_then[`ls`,`LENGTH ls`,`aa`]mp_tac IMP_read_bytearray_GENLIST
  \\ impl_tac >- simp[]
  \\ `len = LENGTH ls`
  by (
    simp[Abbr`len`]
    \\ rfs[good_dimindex_def] \\ rfs[shift_def]
    \\ simp[bytes_in_word_def,GSYM word_add_n2w]
    \\ simp[dimword_def] )
  \\ fs[] \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`read_bytearray aa2 len2 _`
  \\ qispl_then[`ws`,`LENGTH ws`,`aa2`]mp_tac IMP_read_bytearray_GENLIST
  \\ impl_tac >- simp[]
  \\ `len2 = LENGTH ws`
  by (
    simp[Abbr`len2`]
    \\ rfs[good_dimindex_def] \\ rfs[shift_def]
    \\ simp[bytes_in_word_def,GSYM word_add_n2w]
    \\ simp[dimword_def] )
  \\ fs[]
  \\ rpt strip_tac
  \\ simp[Unit_def]
  \\ fs [dataSemTheory.cut_state_opt_def]
  \\ gvs [wordSemTheory.flush_state_def]
QED

Theorem getWords_acc:
  ∀ws acc.
    getWords ws acc =
      let (cs,c) = getWords ws [] in (REVERSE acc ++ cs,c)
Proof
  Induct THEN1 fs [getWords_def]
  \\ Cases \\ Cases_on ‘r’ \\ rewrite_tac [getWords_def]
  \\ simp_tac (srw_ss()) []
  \\ pop_assum (once_rewrite_tac o single)
  \\ rw [] \\ pairarg_tac \\ fs []
QED

Theorem getWords_thm:
  ∀ws cs rest.
    getWords ws [] = (cs,rest) ⇒
    ws = MAP (λ(b,c). (b, Word c)) cs ++ rest
Proof
  Induct \\ fs [getWords_def, AllCaseEqs()]
  \\ rw [] \\ fs []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [getWords_acc]
  \\ fs [] \\ pairarg_tac \\ gvs []
  \\ rw [] \\ fs []
QED

Theorem store_list_word_cond_add_IMP:
  ∀y2 m a m1 free.
    store_list free (MAP (word_cond_add c (a:'a word))
      (MAP (λ(b,c). (b,Word c)) y2)) m dm = SOME m1 ⇒
    const_addresses free y2 dm ∧
    const_writes free (a ≪ (shift_length c − shift (:α))) y2 m = m1
Proof
  Induct
  \\ fs [wordSemTheory.const_addresses_def,
         wordSemTheory.const_writes_def,store_list_def]
  \\ rpt gen_tac \\ strip_tac
  \\ res_tac \\ fs [] \\ gvs []
  \\ Cases_on ‘h’ \\ Cases_on ‘r’ \\ Cases_on ‘q’
  \\ fs [wordSemTheory.const_addresses_def,word_cond_add_def,
         wordSemTheory.const_writes_def,store_list_def]
QED

Theorem evaluate_StoreAnyConsts:
  ∀r1 r2 r3 vs w (s:('a,'c,'ffi) wordSem$state) free m dm m1.
    store_list free (MAP (word_cond_add c (a:'a word)) vs) m dm = SOME m1 ∧
    m = s.memory ∧ dm = s.mdomain ∧ ALL_DISTINCT [r1;r2;r3] ∧
    EVERY (good_loc (domain s.code) o SND) (w::vs) ∧
    lookup r2 s.locals = SOME (Word free) ∧
    lookup r3 s.locals = SOME (Word (a ≪ (shift_length c − shift (:α)))) ⇒
    ∃ll.
      evaluate (StoreAnyConsts r1 r2 r3 vs w, s) =
        (NONE, s with <| memory := m1;
                         locals := ll;
                         store := s.store |+ (NextFree, Word
                           (free + bytes_in_word * n2w (LENGTH vs))) |>) ∧
      lookup r1 ll = SOME (word_cond_add c a w) ∧
      ∀n. ~ MEM n [r1;r2;r3] ⇒ lookup n ll = lookup n s.locals
Proof
  ho_match_mp_tac StoreAnyConsts_ind \\ rw []
  THEN1
   (Cases_on ‘w’
    \\ fs [StoreAnyConsts_def,wordSemTheory.evaluate_def,wordSemTheory.word_exp_def,
          wordSemTheory.set_store_def,store_list_def,wordSemTheory.get_var_def]
    \\ Cases_on ‘r’ \\ gvs [] \\ Cases_on ‘q’
    \\ gvs [StoreAnyConsts_def,wordSemTheory.evaluate_def,wordSemTheory.word_exp_def,
            wordSemTheory.set_store_def,store_list_def,word_cond_add_def,
            wordSemTheory.get_var_def,
            wordSemTheory.the_words_def,wordLangTheory.word_op_def,wordSemTheory.set_var_def,
            wordSemTheory.state_component_equality,good_loc_def,lookup_insert])
  \\ fs [StoreAnyConsts_def]
  \\ rename [‘SND xx’] \\ PairCases_on ‘xx’ \\ fs []
  \\ reverse (Cases_on ‘xx1’) \\ gvs []
  THEN1
   (once_rewrite_tac [list_Seq_def]
    \\ once_rewrite_tac [list_Seq_def]
    \\ once_rewrite_tac [list_Seq_def]
    \\ once_rewrite_tac [list_Seq_def]
    \\ gvs [good_loc_def]
    \\ fs [wordSemTheory.evaluate_def,wordSemTheory.word_exp_def,lookup_insert,
           wordSemTheory.set_store_def,store_list_def,word_cond_add_def,
           wordSemTheory.get_var_def,wordSemTheory.mem_store_def,
           wordSemTheory.the_words_def,wordLangTheory.word_op_def,wordSemTheory.set_var_def]
    \\ qmatch_goalsub_abbrev_tac ‘wordSem$evaluate (_,s1)’
    \\ last_x_assum (qspec_then ‘s1’ mp_tac)
    \\ fs [Abbr‘s1’]
    \\ ‘∀xx0. word_cond_add c a (xx0,Loc n 0) = Loc n 0’ by (Cases \\ fs [word_cond_add_def])
    \\ fs [lookup_insert] \\ strip_tac \\ fs []
    \\ fs [wordSemTheory.state_component_equality]
    \\ fs [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ rw [] \\ ntac 10 (simp [Once insert_swap,insert_shadow]))
  \\ pairarg_tac \\ fs []
  \\ qabbrev_tac ‘input = (xx0,Word c')::vs’
  \\ ‘SUC (LENGTH vs) = LENGTH input’ by fs [Abbr‘input’,ADD1]
  \\ ‘(word_cond_add c a (xx0,Word c')::MAP (word_cond_add c a) vs) =
      MAP (word_cond_add c a) input’ by fs [Abbr‘input’]
  \\ drule getWords_thm \\ fs []
  \\ strip_tac
  \\ ‘EVERY (good_loc (domain s.code) ∘ SND) input’ by fs [good_loc_def,EVERY_MAP,Abbr‘input’]
  \\ pop_assum mp_tac
  \\ pop_assum mp_tac
  \\ pop_assum kall_tac
  \\ pop_assum kall_tac \\ rw []
  \\ fs [store_list_APPEND,AllCaseEqs()]
  \\ drule store_list_word_cond_add_IMP \\ strip_tac
  \\ fs [wordSemTheory.evaluate_def,wordSemTheory.word_exp_def,lookup_insert,
         wordSemTheory.set_store_def,store_list_def,word_cond_add_def,
         wordSemTheory.get_var_def,wordSemTheory.mem_store_def,
         wordSemTheory.the_words_def,wordLangTheory.word_op_def,wordSemTheory.set_var_def,
         wordSemTheory.unset_var_def]
  \\ qmatch_goalsub_abbrev_tac ‘wordSem$evaluate (_,s1)’
  \\ last_x_assum (qspec_then ‘s1’ mp_tac)
  \\ fs [Abbr‘s1’]
  \\ fs [lookup_insert]
  \\ strip_tac \\ fs []
  \\ fs [wordSemTheory.state_component_equality]
  \\ fs [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,lookup_delete]
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
  ∀parts (off:'a word) m aa (t:('a,'c,'ffi) wordSem$state) (s:('c,'ffi) dataSem$state).
    parts_to_words c m aa parts off = NONE ∧ good_dimindex (:'a) ∧
    heap_in_memory_store heap a sp sp1 gens c t.store t.memory t.mdomain limit ⇒
    limits_inv s.limits (FLOOKUP t.store HeapLength) t.stack_limit
               c.len_size c.has_fp_ops c.has_fp_tern ⇒
    EXISTS ($¬ ∘ lim_safe_part s.limits) parts
Proof[exclude_simps = EXP_LE_LOG_SIMP EXP_LT_LOG_SIMP LE_EXP_LOG_SIMP
                      LT_EXP_LOG_SIMP LOG_NUMERAL EXP_LT_1
                      ONE_LE_EXP TWO_LE_EXP]
  Induct
  \\ fs [parts_to_words_def,AllCaseEqs(),PULL_EXISTS]
  \\ rpt gen_tac
  \\ reverse (Cases_on ‘part_to_words c m h off’)
  THEN1 (gvs [] \\ rw [] \\ res_tac \\ fs [])
  \\ fs [] \\ disch_tac
  \\ simp [limits_inv_def] \\ strip_tac
  \\ disj1_tac \\ strip_tac
  \\ Cases_on ‘∃n l. h = Con n l’
  THEN1
   (gvs [part_to_words_def,arch_size_def,CaseEq "bool"]
    \\ Cases_on ‘l’
    \\ gvs [good_dimindex_def,dimword_def,encode_header_def])
  \\ Cases_on ‘∃i. h = Int i’
  THEN1
   (gvs [part_to_words_def,arch_size_def]
    \\ gvs [AllCaseEqs(),multiwordTheory.i2mw_def,encode_header_def]
    THEN1
     (Cases_on ‘i < 0’ \\ fs [b2w_def,EVAL “1w ≪ 2 ‖ 3w”]
      \\ gvs [good_dimindex_def,dimword_def,NOT_LESS]
      \\ ‘7 < 2 ** 4 ∧ 3 < 2 ** 4’ by EVAL_TAC
      \\ drule_all LESS_EQ_LESS_TRANS
      \\ simp [EXP_BASE_LT_MONO]
      \\ fs [heap_in_memory_store_def])
    THEN1
     (qpat_x_assum ‘~(n < m:num)’ mp_tac
      \\ Cases_on ‘i < 0’ \\ gvs [good_dimindex_def,dimword_def]
      \\ ntac 10 (fs [dimword_def] \\ EVAL_TAC))
    \\ gvs [bignum_size]
    \\ qsuff_tac ‘2 ** c.len_size ≤ 2 ** (dimindex (:α) − 4)’
    THEN1 decide_tac
    \\ fs [heap_in_memory_store_def])
  \\ Cases_on ‘h’ \\ gvs [part_to_words_def,arch_size_def]
  \\ gvs [good_dimindex_def,dimword_def,byte_len_def,encode_header_def,
          AllCaseEqs(),NOT_LESS]
  \\ imp_res_tac TWO_POW_LEMMA
  \\ fs [heap_in_memory_store_def,encode_header_def,AllCaseEqs()]
QED

Theorem assign_Build:
   (∃parts. op = BlockOp (Build parts)) ==> ^assign_thm_goal
Proof[exclude_simps = EXP_LE_LOG_SIMP EXP_LT_LOG_SIMP LE_EXP_LOG_SIMP
                      LT_EXP_LOG_SIMP LOG_NUMERAL EXP_LT_1
                      ONE_LE_EXP TWO_LE_EXP]
  rpt strip_tac \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ Cases_on ‘FST (assign c n l dest (BlockOp (Build parts)) args names_opt) = GiveUp’
  THEN1
   (asm_rewrite_tac [] >> fs [] >>
    fs[state_rel_def] >>
    conj_tac >- metis_tac[backendPropsTheory.option_le_trans,
                          do_app_stack_max,option_le_max_right] >>
    pop_assum mp_tac >>
    ‘x.limits = s.limits’ by
      (Cases_on ‘names_opt’ \\ gvs [cut_state_opt_def,cut_state_def,AllCaseEqs()]) >>
    simp [assign_def]
    \\ reverse (Cases_on ‘const_parts_to_words c parts’)
    THEN1 (fs [] \\ PairCases_on ‘x'’ \\ fs [] \\ EVAL_TAC) \\ fs []
    \\ qsuff_tac ‘EXISTS ($¬ ∘ lim_safe_part s.limits) parts’
    THEN1 (strip_tac \\ gvs[do_app,CaseEq"bool",CaseEq"option",AllCaseEqs()] >>
           imp_res_tac get_vars_IMP_LENGTH >>
           rveq >> fs[arch_size_def,limits_inv_def,good_dimindex_def] >>
           gvs [consume_space_def,AllCaseEqs()])
    \\ fs [const_parts_to_words_def]
    \\ drule_all parts_to_words_NONE \\ rewrite_tac [])
  \\ gvs [assign_def]
  \\ fs [] \\ Cases_on ‘const_parts_to_words c parts’ THEN1 fs []
  \\ rename [‘_ = SOME y’]
  \\ PairCases_on ‘y’ \\ fs []
  \\ qpat_x_assum ‘_ ≠ _’ kall_tac
  \\ qexists_tac ‘NONE’ \\ fs []
  \\ ‘∃free curr.
        FLOOKUP t.store NextFree = SOME (Word free) ∧
        FLOOKUP t.store CurrHeap = SOME (Word curr) ∧
        good_dimindex (:'a) ∧ shift_length c < dimindex (:α)’ by
          fs [state_rel_thm,memory_rel_def,heap_in_memory_store_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,wordSemTheory.word_exp_def,wordSemTheory.set_var_def,
         wordSemTheory.get_store_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,wordSemTheory.word_exp_def,wordSemTheory.set_var_def,
         wordSemTheory.the_words_def,wordLangTheory.word_op_def,wordLangTheory.word_sh_def,
         wordSemTheory.get_var_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ qpat_x_assum ‘state_rel c l1 l2 x t [] locs’ mp_tac
  \\ simp [Once state_rel_thm] \\ strip_tac
  \\ Cases_on ‘x.tstamps’ \\ gvs [get_var_def,wordSemTheory.get_store_def]
  \\ rename [‘x.tstamps = SOME ts’]
  \\ fs [do_app]
  \\ qabbrev_tac ‘x3 = if SUM (MAP part_space_req parts) = 0 then SOME x
                       else consume_space (SUM (MAP part_space_req parts)) x’
  \\ ‘x3 = consume_space (SUM (MAP part_space_req parts)) x’ by
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
  \\ qmatch_goalsub_abbrev_tac ‘wordSem$evaluate (_,s1)’
  \\ ‘t.memory = s1.memory ∧ t.mdomain = s1.mdomain’ by fs [Abbr‘s1’]
  \\ fs []
  \\ drule evaluate_StoreAnyConsts
  \\ disch_then (qspecl_then [‘adjust_var dest’,‘1’,‘3’,‘(y0,y1)’,‘s1’] mp_tac)
  \\ impl_tac THEN1
   (rgs [Abbr‘s1’,lookup_insert]
    \\ irule const_parts_to_words_good_loc \\ fs []
    \\ first_x_assum $ irule_at Any
    \\ gvs [EVERY_MEM] \\ rw [] \\ res_tac \\ fs [code_rel_def])
  \\ strip_tac \\ fs []
  \\ fs [state_rel_thm,dataSemTheory.set_var_def,lookup_insert,lookup_delete,Abbr‘s1’,
         FLOOKUP_UPDATE,FAPPLY_FUPDATE_THM,adjust_var_11,option_le_max_right]
  \\ conj_tac THEN1
   (rw [] \\ res_tac
    \\ first_x_assum (qspec_then ‘adjust_var n’ mp_tac)
    \\ fs [adjust_var_11])
  \\ ‘(inter ll (adjust_set (insert dest v x.locals))) =
      (inter (insert (adjust_var dest) (word_cond_add c (-1w * curr + free) (y0,y1)) t.locals)
            (adjust_set (insert dest v x.locals)))’ by
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
  \\ qexists_tac ‘x.space − LENGTH y2’ \\ fs []
QED

fun foldr1 f (x::xs) = foldr f x xs | foldr1 f [] = fail();

Theorem join_lemma[local] =
  METIS_PROVE [] “(b1 ⇒ x) ∧ (b2 ⇒ x) ⇒ (b1 ∨ b2 ⇒ x)”;

Theorem imp_assign[local] =
  DB.match ["-"] “_ ==> ^assign_thm_goal” |> map (#1 o #2)
  |> foldr1 (fn (x,y) => MATCH_MP join_lemma (CONJ x y));

Theorem assign_thm:
  ^assign_thm_goal
Proof
  strip_tac
  \\ Cases_on `op = GlobOp AllocGlobal`
  >- (fs [do_app] \\ every_case_tac \\ fs [])
  \\ Cases_on `op = IntOp Greater`
  >- (fs [do_app] \\ every_case_tac \\ fs [])
  \\ Cases_on `op = IntOp GreaterEq`
  >- (fs [do_app] \\ every_case_tac \\ fs [])
  \\ Cases_on`op = MemOp (CopyByte T)`
  >- (fs[do_app_def,do_space_def,do_app_aux_def] \\ every_case_tac \\ fs[])
  \\ irule imp_assign
  \\ asm_rewrite_tac []
  \\ rpt $ first_assum $ irule_at Any
  \\ Cases_on ‘∃i. op = IntOp i’
  >- (fs [] \\ fs [] \\ gvs [] \\ Cases_on ‘i’ \\ gvs [])
  \\ Cases_on ‘∃i. op = GlobOp i’
  >- (fs [] \\ fs [] \\ gvs [] \\ Cases_on ‘i’ \\ gvs [])
  \\ Cases_on ‘∃i. op = MemOp i’
  >- (fs [] \\ fs [] \\ gvs [] \\ Cases_on ‘i’ \\ gvs []
      \\ qhdtm_x_assum`do_app`mp_tac \\ EVAL_TAC)
  \\ Cases_on ‘∃i. op = BlockOp i’
  >- (fs [] \\ fs [] \\ gvs [] \\ Cases_on ‘i’ \\ gvs []
      \\ qhdtm_x_assum`do_app`mp_tac \\ EVAL_TAC)
  \\ Cases_on ‘∃i. op = WordOp i’
  >- (fs [] \\ fs [] \\ gvs [] \\ Cases_on ‘i’ \\ gvs [] \\ Cases_on ‘w’ \\ gvs [])
  \\ Cases_on ‘∃i. op = ThunkOp i’
  >- (fs [] \\ fs [] \\ gvs [] \\ Cases_on ‘i’ \\ gvs []
      \\ qhdtm_x_assum`do_app`mp_tac \\ EVAL_TAC)
  \\ Cases_on ‘op’ \\ gvs []
QED
