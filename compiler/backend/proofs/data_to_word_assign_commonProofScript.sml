(*
  Part of the correctness proof for data_to_word: lemmas shared by
  the assign proofs
*)
Theory data_to_word_assign_commonProof
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

(* Lemmas shared with data_to_word_bignumProof *)

val _ = augment_srw_ss [rewrites [CONJUNCT2 data_to_wordTheory.arch_size]];

val _ = temp_delsimps ["NORMEQ_CONV", "fromAList_def", "domain_union",
                       "domain_inter", "domain_difference",
                       "domain_map", "sptree.map_def", "sptree.lookup_rwts",
                       "sptree.insert_notEmpty", "sptree.isEmpty_union"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = augment_srw_ss [rewrites [integer_wordTheory.i2w_pos, integer_wordTheory.i2w_w2i,
  integer_wordTheory.i2w_minus_1,
  data_to_wordTheory.get_lowerbits_def,data_to_wordTheory.make_ptr_def,
  data_to_wordTheory.make_cons_ptr_def]]

val eval_tac = fs [wordSemTheory.evaluate_def,
  wordSemTheory.word_exp_def, wordSemTheory.set_var_def,
  set_var_def, wordSemTheory.the_words_def, wordSemTheory.get_store_def,
  wordSemTheory.mem_load_def,wordSemTheory.word_op_def,
  wordSemTheory.word_sh_def]

fun rpt_drule th = drule (th |> GEN_ALL) \\ rpt (disch_then drule \\ fs [])

Theorem eq_eval =
  LIST_CONJ [wordSemTheory.evaluate_def,wordSemTheory.get_var_def,
             lookup_insert,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,
             wordSemTheory.word_exp_def,wordSemTheory.set_var_def,
             wordSemTheory.call_env_def,fromList2_def,wordSemTheory.mem_load_def,
             wordSemTheory.bad_dest_args_def,wordSemTheory.get_vars_def,
             wordSemTheory.find_code_def,wordSemTheory.add_ret_loc_def,
             list_insert_def,wordSemTheory.dec_clock_def,wordSemTheory.the_words_def,
             wordSemTheory.word_op_def]

Theorem word_exp_set_var_ShiftVar_lemma:
   word_exp (t:('a,'c,'ffi) wordSem$state) (ShiftVar (dimindex (:'a)) sow v n) =
    case lookup v t.locals of
    | SOME (Word w) =>
        OPTION_MAP Word
          (case sow of Lsl => SOME (w << n)
                     | Lsr => SOME (w >>> n)
                     | Asr => SOME (w >> n)
                     | Ror => SOME (word_ror w n))
    | _ => FAIL (word_exp t (ShiftVar (dimindex (:'a)) sow v n)) "lookup failed"
Proof
  Cases_on `lookup v t.locals` \\ fs [] \\ rw [FAIL_DEF]
  \\ Cases_on ‘x’ \\ gvs []
  \\ fs [ShiftVar_def]
  \\ cases_on ‘sow’ \\ gvs []
  \\ `!m. m < dimindex (:'a) ==> m MOD dimword (:'a) = m` by
       (rw [] \\ metis_tac [dimindex_lt_dimword,LESS_TRANS])
  \\ rw [] \\ gvs [wordSemTheory.word_exp_def,wordSemTheory.get_var_def,wordSemTheory.word_sh_def,
                    wordsTheory.mod_dimindex]
  (* Ror case: n MOD dimindex >= dimindex is impossible *)
  \\ TRY (qspec_then `n` assume_tac (MATCH_MP MOD_LESS DIMINDEX_GT_0) \\
          gvs [GSYM NOT_LESS,GREATER_EQ] \\ NO_TAC)
  (* Ror case: rotation by 0 *)
  \\ TRY (Cases_on `n < dimindex (:'a)` \\ gvs [] \\ NO_TAC)
  (* Asr case: dimindex <= n *)
  \\ `dimindex (:'a) - 1 < dimindex (:'a)` by
       (Cases_on `dimindex (:'a)` \\ fs [])
  \\ res_tac
  \\ gvs [word_asr_dimindex]
  \\ gvs [fcpTheory.CART_EQ,word_asr_def,fcpTheory.FCP_BETA]
  \\ rw [] \\ gvs [WORD_NEG_1_T,word_0]
  \\ `i = 0` by fs [] \\ gvs [word_msb_def]
QED

Theorem word_cmp_Test_1:
   word_cmp Test w 1w <=> ~(word_bit 0 w)
Proof
  EVAL_TAC \\ fs [word_and_one_eq_0_iff,word_bit_def]
QED

Theorem word_bit_if_1_0:
   word_bit 0 (if b then 1w else 0w) <=> b
Proof
  Cases_on `b` \\ EVAL_TAC
QED

Theorem get_real_addr_lemma:
   shift_length c < dimindex (:'a) /\
    good_dimindex (:'a) /\
    arch_width_bits c.arch_width = dimindex (:'a) /\
    get_var v (t:('a,'c,'ffi) wordSem$state) = SOME (Word ptr_w) /\
    get_real_addr c t.store ptr_w = SOME x ==>
    word_exp t (real_addr c v) = SOME (Word (x:'a word))
Proof
  strip_tac
  \\ fs [get_real_addr_def] \\ every_case_tac \\ fs []
  \\ fs [wordSemTheory.get_var_def,real_addr_def]
  \\ eval_tac \\ fs [] \\ rw [wordSemTheory.get_var_def]
  \\ eval_tac \\ fs [] \\ rw [] \\ fs []
  \\ fs [good_dimindex_def,dimword_def] \\ rw []
  \\ rfs [backend_commonTheory.word_shift_def]
  \\ fs [DECIDE ``(a:num) <= b ==> a - b = 0``]
QED

Theorem memory_rel_lookup:
   memory_rel c be ts refs s st m dm
      (join_env l1 (toAList (inter l2 (adjust_set l1))) ++ xs) ∧
    lookup n l1 = SOME x ∧ lookup (adjust_var n) l2 = SOME w ⇒
    memory_rel c be ts refs s st m dm
     ((x,w)::(join_env l1 (toAList (inter l2 (adjust_set l1))) ++ xs))
Proof
  fs [memory_rel_def] \\ rw [] \\ asm_exists_tac \\ fs []
  \\ rpt_drule (Q.INST [`ys`|->`[]`] word_ml_inv_lookup
        |> SIMP_RULE std_ss [APPEND])
QED

Theorem IMP_LESS_MustTerminate_limit[simp]:
   i < dimword (:α) ==>
    i < MustTerminate_limit (:α) − 1
Proof
  rewrite_tac [wordSemTheory.MustTerminate_limit_def] \\ decide_tac
QED

Theorem TWO_LESS_MustTerminate_limit[simp]:
   2 < MustTerminate_limit (:α) /\
    ~(MustTerminate_limit (:α) <= 1)
Proof
  fs [wordSemTheory.MustTerminate_limit_def,dimword_def]
  \\ Cases_on `dimindex (:'a)` \\ fs [dimword_def,MULT_CLAUSES,EXP]
  \\ Cases_on `n` \\ fs [EXP] \\ Cases_on `2 ** n'` \\ fs []
QED

Theorem push_env_code:
   (push_env y NONE t).code = t.code
Proof
  fs [wordSemTheory.push_env_def] \\ pairarg_tac \\ fs []
QED

Theorem Replicate_code_thm:
   !n a r m1 a1 a2 a3 a4 a5.
      arch_width_bits c.arch_width = dimindex(:'a) /\
      (?md. lookup Replicate_location r.code = SOME (5,Replicate_code c,md)) /\
      store_list (a + bytes_in_word) (REPLICATE n v)
        (r:('a,'c,'ffi) wordSem$state).memory r.mdomain = SOME m1 /\
      get_var a1 r = SOME (Loc l1 l2) /\
      get_var a2 r = SOME (Word a) /\
      get_var a3 r = SOME v /\
      get_var a4 r = SOME (Word (n2w (2 * n))) /\
      get_var a5 (r:('a,'c,'ffi) wordSem$state) = SOME ret_val /\
      2 * n < dimword (:'a) /\
      n < r.clock ==>
      ?m.
        evaluate (Call NONE (SOME Replicate_location) [a1;a2;a3;a4;a5] NONE,r) =
          (SOME (Result (Loc l1 l2) [ret_val]),
           r with <| memory := m1 ; clock := r.clock - n - 1; locals := LN;
                     locals_size := SOME 0; stack_max := m |>) ∧
        option_le m
          (OPTION_MAP2 MAX r.stack_max
             (OPTION_MAP2 $+ (stack_size r.stack)
                (lookup Replicate_location r.stack_size)))
Proof
  Induct \\ rw [] \\ simp [wordSemTheory.evaluate_def]
  \\ simp [wordSemTheory.get_vars_def,wordSemTheory.bad_dest_args_def,
        wordSemTheory.find_code_def,wordSemTheory.add_ret_loc_def]
  \\ rw [] \\ simp [Replicate_code_def]
  \\ `arch_bytes c.arch_width = dimindex(:'a) DIV 8` by
       (Cases_on `c.arch_width` \\ gvs[asmTheory.arch_bytes_def,asmTheory.arch_width_bits_def]
        \\ qpat_x_assum `_ = dimindex(:α)` (assume_tac o SYM) \\ fs[])
  \\ fs[bytes_in_word_def]
  \\ simp [wordSemTheory.evaluate_def,wordSemTheory.call_env_def,
         wordSemTheory.get_var_def,wordSemTheory.get_vars_def,
         word_exp_rw,bytes_in_word_def,fromList2_def,
         asmTheory.word_cmp_def,wordSemTheory.dec_clock_def]
  \\ fs [store_list_def,bytes_in_word_def,REPLICATE,wordSemTheory.flush_state_def]
  THEN1 (rw [wordSemTheory.state_component_equality])
  \\ NTAC 3 (once_rewrite_tac [list_Seq_def])
  \\ simp [wordSemTheory.evaluate_def,wordSemTheory.call_env_def,
           wordSemTheory.get_var_def,word_exp_rw,bytes_in_word_def,fromList2_def,
           wordSemTheory.set_var_def,wordSemTheory.mem_store_def,
           asmTheory.word_cmp_def,wordSemTheory.dec_clock_def]
  \\ fs [list_Seq_def]
  \\ SEP_I_TAC "evaluate"
  \\ fs [wordSemTheory.call_env_def,
           wordSemTheory.get_var_def,word_exp_rw,bytes_in_word_def,fromList2_def,
           wordSemTheory.set_var_def,wordSemTheory.mem_store_def,
           asmTheory.word_cmp_def,wordSemTheory.dec_clock_def]
  \\ rfs [] \\ fs [MULT_CLAUSES,GSYM word_add_n2w] \\ fs [ADD1]
  \\ fs [wordSemTheory.state_component_equality]
QED

Theorem MAP_FST_EQ_IMP_IS_SOME_ALOOKUP:
   !xs ys.
      MAP FST xs = MAP FST ys ==>
      IS_SOME (ALOOKUP xs n) = IS_SOME (ALOOKUP ys n)
Proof
  Induct \\ fs [] \\ Cases \\ Cases_on `ys` \\ fs []
  \\ Cases_on `h` \\ fs [] \\ rw []
QED

Theorem domain_adjust_sets:
  domain (FST (adjust_sets kept_names)) ≠ {}
Proof
  gvs [adjust_sets_def]
QED

Theorem env_to_list_domain_eq:
  env_to_list y2 t.permute = (l',permute) ∧
  MAP FST l' = MAP FST ms ⇒
  domain (fromAList ms) = domain y2
Proof
  rw [] \\ drule env_to_list_lookup_equiv \\ rw []
  \\ fs [domain_fromAList]
  \\ qpat_x_assum ‘MAP _ _ = _’ $ assume_tac o GSYM
  \\ gvs [] \\ simp [EXTENSION,domain_lookup]
  \\ qpat_x_assum ‘∀n. ALOOKUP _ n = _’ $ assume_tac o GSYM
  \\ gvs [] \\ rewrite_tac [GSYM IS_SOME_EXISTS]
  \\ rewrite_tac [IS_SOME_ALOOKUP_EQ]
QED

Theorem size_of_LE_append:
  !vs ys lims refs seen.
    FST (size_of lims ys refs seen) <= FST (size_of lims (vs ++ ys) refs seen)
Proof
  Induct \\ rw []
  \\ once_rewrite_tac [data_to_word_gcProofTheory.size_of_cons]
  \\ Cases_on `size_of lims (vs ++ ys) refs seen`
  \\ rename1 `_ = (n1,rr1)` \\ PairCases_on `rr1`
  \\ Cases_on `size_of lims [h] rr10 rr11`
  \\ rename1 `size_of lims [h] _ _ = (n2,rr2)` \\ PairCases_on `rr2`
  \\ fs []
  \\ last_x_assum (qspecl_then [`ys`,`lims`,`refs`,`seen`] assume_tac) \\ gvs []
QED

Theorem size_of_heap_LE_args:
  !vs s. size_of_heap s <= size_of_heap_args vs s
Proof
  rw [dataSemTheory.size_of_heap_def, dataSemTheory.size_of_heap_args_def]
  \\ qspecl_then [`vs`,`stack_to_vs s`,`s.limits`,`s.refs`,`LN`] mp_tac size_of_LE_append
  \\ rpt (pairarg_tac \\ fs [])
QED

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]
val _ = temp_delsimps ["DIV_NUMERAL_THM"]

Definition byte_copy_flush_def:
  byte_copy_flush be d carry (b:'a word) m =
    if d = 0 then m else
      (b =+ Word (carry || (theWord (m b) &&
        (if be then -1w >>> (8 * d) else -1w << (8 * d))))) m
End

Theorem byte_copy_flush_nonzero:
  d <> 0 /\ m b = Word old ==>
  byte_copy_flush be d carry b m =
    (b =+ Word (carry || (old &&
      (if be then -1w >>> (8 * d) else -1w << (8 * d))))) m
Proof
  simp [byte_copy_flush_def,theWord_def]
QED

Theorem i2w_neg:
  i2w (-&n) = -n2w n
Proof
  rw[integer_wordTheory.i2w_def] >> fs[integerTheory.NUM_OF_INT] >>
  `n = 0` by intLib.ARITH_TAC >> fs[]
QED

Theorem i2w_sub1:
  i2w (&n - 1) = n2w n + -1w
Proof
  PURE_REWRITE_TAC [integerTheory.int_sub,
    GSYM integer_wordTheory.word_i2w_add,
    integer_wordTheory.i2w_pos,integer_wordTheory.i2w_minus_1]
  \\ simp []
QED

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
val all_ones_def = data_to_word_memoryProofTheory.all_ones_def;
val maxout_bits_def = data_to_word_memoryProofTheory.maxout_bits_def;
val ptr_bits_def = data_to_word_memoryProofTheory.ptr_bits_def;
val Smallnum_def = LIST_CONJ [data_to_word_memoryProofTheory.Smallnum_def,
                             data_to_wordTheory.Smallnum_def];
val get_lowerbits_def = data_to_word_memoryProofTheory.get_lowerbits_def;
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

(* This list must list all auxiliary definitions used in assign_def *)

Theorem assign_def_extras =
  LIST_CONJ
  [LoadWord64_def,WriteWord64_def,BignumHalt_def,LoadBignum_def,
   AnyArith_code_def,Add_code_def,Sub_code_def,Mul_code_def,
   SmallDivMod_def,SmallnumCompare_def,SmallnumMul_def,SmallnumDivLoop_def,
   SmallnumUnsignedDiv_def,SmallnumDiv_def,SmallnumDivCall_def,
   Div_code_def,Mod_code_def, Compare1_code_def, Compare_code_def,
   Equal1_code_def, Equal_code_def, LongDiv1_code_def, LongDiv_code_def,
   ShiftVar_def, generated_bignum_stubs_eq, DivCode_def,
   AddNumSize_def, AnyHeader_def, WriteWord64_on_32_def,
   WriteWord32_on_32_def, AllocVar_def, SilentFFI_def,
   WordOp64_on_32_def, WordShift64_on_32_def, Make_ptr_bits_code_def,
   ShiftW8_def, WordShiftVar64_def, WordShiftVar64_on_32_def];

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

Theorem push_if:
  (∀f x y b. (if b then f x else f y) = f (if b then x else y)) ∧
  (∀f h x b. (if b then f x else h x) = (if b then f else h) x)
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

Theorem evaluate_StoreEach = Q.prove(`
  !xs ys t offset m1.
      store_list (a + n2w offset) ys t.memory t.mdomain = SOME m1 /\
      get_vars xs t = SOME ys /\
      get_var i t = SOME (Word (a:'a word)) /\
      arch_width_bits c.arch_width = dimindex(:'a) ==>
      evaluate (StoreEach c i xs offset, t) = (NONE,t with memory := m1)`,
  Induct
  \\ fs [store_list_def,StoreEach_def,data_to_wordTheory.arch_size] \\ eval_tac
  \\ fs [wordSemTheory.state_component_equality,
           wordSemTheory.get_vars_def,store_list_def,
           wordSemTheory.get_var_def]
  \\ rw [] \\ fs [] \\ CASE_TAC \\ fs []
  \\ Cases_on `get_vars xs t` \\ fs [] \\ clean_tac
  \\ fs [store_list_def,wordSemTheory.mem_store_def]
  \\ `(t with memory := m1) =
      (t with memory := (a + n2w offset =+ x) t.memory) with memory := m1` by
       (fs [wordSemTheory.state_component_equality] \\ NO_TAC)
  \\ pop_assum (fn th => rewrite_tac [th])
  \\ first_x_assum match_mp_tac
  \\ fs [bytes_in_word_def,GSYM word_add_n2w]
  \\ asm_exists_tac \\ fs []
  \\ rename1 `get_vars qs t = SOME ts`
  \\ pop_assum mp_tac
  \\ qspec_tac (`ts`,`ts`)
  \\ qspec_tac (`qs`,`qs`)
  \\ Induct \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def]
  \\ rw [] \\ every_case_tac \\ fs [])
  |> Q.SPECL [`xs`,`ys`,`t`,`0`] |> SIMP_RULE (srw_ss()) [] |> GEN_ALL;

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

Theorem word_exp_real_addr:
   get_real_addr c t.store ptr_w = SOME a /\
    shift_length c < dimindex (:α) ∧ good_dimindex (:α) /\
    arch_width_bits c.arch_width = dimindex (:α) /\
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
    arch_width_bits c.arch_width = dimindex (:α) /\
    lookup (adjust_var a1) t.locals = SOME (Word ptr_w) ==>
    !w1 w2.
      word_exp
        (t with locals := insert 3 (Word (w1:'a word)) (insert 1 (Word w2) t.locals))
        (real_addr c (adjust_var a1)) = SOME (Word a)
Proof
  rpt strip_tac \\ match_mp_tac (GEN_ALL get_real_addr_lemma)
  \\ fs [wordSemTheory.get_var_def,lookup_insert]
QED

Theorem shifted_header_or:
  sh < dimindex (:'a) /\ k < 2 ** sh ==>
  ((n2w n:'a word) << sh || n2w k) = n2w (n * 2 ** sh + k)
Proof
  strip_tac
  \\ `2 ** sh <= 2 ** dimindex (:'a)` by
       (irule bitTheory.TWOEXP_MONO2 \\ decide_tac)
  \\ `k < dimword (:'a)` by
       (irule LESS_LESS_EQ_TRANS
        \\ qexists_tac `2 ** sh`
        \\ fs [dimword_def])
  \\ `n2w k && ((n2w n:'a word) << sh) = 0w` by
       (irule word_and_lsl_eq_0 \\ fs [w2n_n2w])
  \\ `((n2w n:'a word) << sh || n2w k) =
      (n2w n:'a word) << sh + n2w k` by
       (irule (SPEC_ALL WORD_ADD_OR |> PURE_ONCE_REWRITE_RULE [EQ_SYM_EQ])
        \\ fs [WORD_AND_COMM])
  \\ asm_rewrite_tac []
  \\ simp [WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
QED

Theorem multiplied_header_or:
  sh < dimindex (:'a) /\ k < 2 ** sh ==>
  ((n2w (n * 2 ** sh):'a word) || n2w k) =
  n2w (n * 2 ** sh + k)
Proof
  strip_tac
  \\ `n2w (n * 2 ** sh):'a word = n2w n << sh` by
       simp [WORD_MUL_LSL,word_mul_n2w,MULT_COMM]
  \\ asm_rewrite_tac []
  \\ irule shifted_header_or
  \\ fs []
QED

Theorem memory_rel_arch_width:
  memory_rel c be ts refs sp st (m:'a word -> 'a word_loc) dm vars ==>
  arch_width_bits c.arch_width = dimindex (:'a)
Proof
  rw [memory_rel_def,heap_in_memory_store_def]
QED

Theorem arch_bytes_word:
  arch_width_bits c.arch_width = dimindex (:'a) ==>
  n2w (arch_bytes c.arch_width) = (bytes_in_word:'a word)
Proof
  Cases_on `c.arch_width`
  \\ rw[asmTheory.arch_width_bits_def,asmTheory.arch_bytes_def,bytes_in_word_def]
  \\ qpat_x_assum `_ = dimindex (:'a)` (assume_tac o SYM) \\ fs []
QED

val _ = augment_srw_ss [rewrites [arch_bytes_word]];
val eval_tac = imp_res_tac state_rel_arch_width
  \\ imp_res_tac memory_rel_arch_width \\ eval_tac
  \\ fs [GSYM word_mul_n2w];

Theorem memory_rel_len_size:
  memory_rel c be ts refs sp st (m:'a word -> 'a word_loc) dm vars ==>
  c.len_size <> 0 /\ c.len_size + 9 < dimindex (:'a)
Proof
  rw [memory_rel_def,heap_in_memory_store_def] \\ fs []
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

Theorem lookup_IMP_insert_EQ:
   !t x y. lookup x t = SOME y ==> insert x y t = t
Proof
  Induct \\ fs [lookup_def,Once insert_def] \\ rw []
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

(* TODO: should probably replace evaluate_GiveUp directly *)

Theorem evaluate_GiveUp2:
  state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) NONE locs ==>
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
   state_rel c l1 l2 s t NONE locs /\
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
   !k i. state_rel c l1 l2 s t NONE locs /\
          get_var k s.locals = SOME (Number i) /\
          get_var (2 * k + 2) t = SOME a1 ==>
          ?w:'a word. a1 = Word w /\ w ' 0 = ~small_int (dimindex (:'a)) i
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

Theorem state_rel_get_var_Number_IMP:
   state_rel c l1 l2 s t vs locs /\
    get_var i s.locals = SOME (Number (&n)) /\ small_int (dimindex (:'a)) (&n) ==>
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
   (4n * n * (2 ** k) = n * 2 ** (k + 2)) /\
   (2n * n * (2 ** k) = n * 2 ** (k + 1)) /\
   (2n * (n * (2 ** k)) = n * 2 ** (k + 1))
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
  strip_tac
  \\ `k < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword \\ decide_tac)
  \\ fs [Maxout_bits_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_def,
      wordSemTheory.set_var_def,wordSemTheory.get_var_imm_def,
      asmTheory.word_cmp_def,lookup_insert,WORD_LO,word_exp_rw,
      maxout_bits_def] \\ rw [] \\ fs [insert_shadow]
  \\ sg `2 ** rep_len < dimword (:α)` \\ fs [] \\ fs [dimword_def]
QED

Theorem Make_ptr_bits_thm:
   arch_width_bits c.arch_width = dimindex(:α) ∧
   tag_reg ≠ dest ∧ tag1 < dimword (:α) ∧ c.tag_bits < dimindex (:α) ∧
    len_reg ≠ dest ∧ len1 < dimword (:α) ∧ c.len_bits < dimindex (:α) ∧
    c.len_bits + 1 < dimindex (:α) /\
    FLOOKUP (t:('a,'c,'ffi) wordSem$state).store NextFree = SOME (Word f) /\
    FLOOKUP t.store CurrHeap = SOME (Word d) /\
    lookup tag_reg t.locals = SOME (Word (n2w tag1)) /\
    lookup len_reg t.locals = SOME (Word (n2w len1)) /\
    shift_length c < dimindex (:α) + shift (dimindex (:α)) ==>
    ?t1.
      evaluate (Make_ptr_bits_code c tag_reg len_reg dest,t) =
        (NONE,set_var dest (make_cons_ptr c (f-d) tag1 len1:'a word_loc) t)
Proof
  strip_tac
  \\ `shift_length c − shift (dimindex (:'a)) < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword \\ decide_tac)
  \\ fs [Make_ptr_bits_code_def,list_Seq_def,wordSemTheory.evaluate_def,word_exp_rw]
  \\ fs [make_cons_ptr_thm]
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

Theorem assign_goal = ASSUME
  ``state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) NONE locs ∧
   (op_requires_names op ≠ (names_opt = NONE)) ∧
   cut_state_opt names_opt s = SOME x ∧
   get_vars args s.locals = SOME vals ∧
   t.termdep > 1 ∧
   do_app op vals x = Rval (v,s2) ==>
   ?q r.
     evaluate (FST (assign c n l dest op args names_opt),t) = (q,r) ∧
     (q = SOME NotEnoughSpace ==>
      r.ffi = t.ffi ∧ option_le r.stack_max s2.stack_max ∧
      (c.gc_kind <> None ==> ~s2.safe_for_space)) ∧
     (q <> SOME NotEnoughSpace ==>
      state_rel c l1 l2 (set_var dest v s2) r NONE locs ∧ q = NONE)``;

val assign_thm_goal = concl assign_goal;

Theorem assign_link_goal = ASSUME
  ``state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) NONE locs ∧
   ptr_eq_link c s t ∧
   (op_requires_names op ≠ (names_opt = NONE)) ∧
   cut_state_opt names_opt s = SOME x ∧
   get_vars args s.locals = SOME vals ∧
   t.termdep > 1 ∧
   do_app op vals x = Rval (v,s2) ==>
   ?q r.
     evaluate (FST (assign c n l dest op args names_opt),t) = (q,r) ∧
     (q = SOME NotEnoughSpace ==>
      r.ffi = t.ffi ∧ option_le r.stack_max s2.stack_max ∧
      (c.gc_kind <> None ==> ~s2.safe_for_space)) ∧
     (q <> SOME NotEnoughSpace ==>
      state_rel c l1 l2 (set_var dest v s2) r NONE locs ∧ q = NONE ∧
      ptr_eq_link c s2 r)``;

val assign_thm_link_goal = concl assign_link_goal;

Theorem list_Seq_ptr_eq_free:
  !xs. ptr_eq_free ns (list_Seq xs) = EVERY (ptr_eq_free ns) xs
Proof
  ho_match_mp_tac list_Seq_ind \\ rw [list_Seq_def, ptr_eq_free_def]
QED

Theorem StoreEach_ptr_eq_free:
  !c v xs offset. ptr_eq_free ns (StoreEach c v xs offset)
Proof
  Induct_on `xs` \\ gvs [StoreEach_def, ptr_eq_free_def]
QED

Theorem MemEqList_ptr_eq_free:
  !c a xs. ptr_eq_free ns (MemEqList c a xs)
Proof
  Induct_on `xs` \\ gvs [MemEqList_def, ptr_eq_free_def]
QED

Theorem StoreAnyConsts_ptr_eq_free:
  !r1 r2 r3 vs v. ptr_eq_free ns (StoreAnyConsts r1 r2 r3 vs v)
Proof
  Cases_on `v` \\ rw [StoreAnyConsts_def, ptr_eq_free_def]
QED

val ptr_eq_free_eval_tac = computeLib.RESTR_EVAL_TAC
  [``int_bitwise$int_or``, ``int_bitwise$int_and``, ``int_bitwise$int_xor``];

Theorem SmallnumDivLoop_ptr_eq_free[local]:
  ∀k. ptr_eq_free ns (SmallnumDivLoop bits k)
Proof
  Induct \\ simp [SmallnumDivLoop_def] \\ ptr_eq_free_eval_tac \\ simp []
QED

Theorem stubs_ptr_eq_free:
  EVERY (λ(n,a,p).
      n ∉ {Install_location; InstallData_location} ⇒
      ptr_eq_free (set (MAP FST (stubs c)) DIFF
        {Install_location; InstallData_location}) p)
    (stubs c)
Proof
  ptr_eq_free_eval_tac \\ rw [] \\ ptr_eq_free_eval_tac
  \\ simp [SmallnumDivLoop_ptr_eq_free]
QED

Theorem code_rel_ptr_eq_free:
  code_rel c s_code (t_code : (num # wordLang$prog # metadata) num_map) ⇒
  code_ptr_eq_free (set (MAP FST (stubs c)) DIFF
    {Install_location; InstallData_location}) t_code
Proof
  rw [code_rel_def, stubs_md_def, code_ptr_eq_free_def, MEM_MAP, EXISTS_PROD]
  \\ assume_tac stubs_ptr_eq_free
  \\ gvs [EVERY_MEM, FORALL_PROD, MEM_MAP, EXISTS_PROD]
  \\ res_tac \\ simp [] \\ metis_tac []
QED

Theorem assign_ptr_eq_free:
  op ≠ BlockOp PtrEqual ∧ op ≠ Install ⇒
  ptr_eq_free (set (MAP FST (stubs c)) DIFF
      {Install_location; InstallData_location})
    (FST (assign c n l dest op args names_opt : wordLang$prog # num))
Proof
  strip_tac
  \\ simp [assign_def, all_assign_defs, arg1_def, arg2_def, arg3_def, arg4_def]
  \\ simp [ptr_eq_free_def, oneline AssignCmp_def, SetBool_def, GiveUp_def,
           BignumHalt_def, AllocVar_def, SilentFFI_def, list_Seq_ptr_eq_free,
           StoreEach_ptr_eq_free, Make_ptr_bits_code_def,
           StoreAnyConsts_ptr_eq_free, Maxout_bits_code_def,
           MemEqList_ptr_eq_free, WriteWord64_def, WordOp64_on_32_def,
           WriteWord64_on_32_def, LoadWord64_def, WordShift64_on_32_def,
           LoadBignum_def, WriteWord32_on_32_def]
  \\ rpt (TOP_CASE_TAC
          \\ simp [ptr_eq_free_def, list_Seq_ptr_eq_free, StoreEach_ptr_eq_free,
                   MemEqList_ptr_eq_free, StoreAnyConsts_ptr_eq_free])
  \\ gvs []
  \\ TRY ((rename1 `WordShiftVar64_on_32 sh` ORELSE rename1 `WordShiftVar64 sh`)
          \\ Cases_on `sh`)
  \\ ptr_eq_free_eval_tac
  \\ rw [] \\ ptr_eq_free_eval_tac \\ simp []
QED

Theorem assign_ptr_eq_link:
  op ≠ BlockOp PtrEqual ∧ op ≠ Install ∧
  state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) NONE locs ∧
  ptr_eq_link c s t ∧
  cut_state_opt names_opt s = SOME x ∧
  do_app op vals x = Rval (v,s2) ∧
  evaluate (FST (assign c n l dest op args names_opt),t) = (q,r) ⇒
  ptr_eq_link c s2 r
Proof
  rw [ptr_eq_link_def]
  >- (imp_res_tac wordPropsTheory.evaluate_consts \\ fs [])
  \\ imp_res_tac cut_state_opt_const
  \\ imp_res_tac dataPropsTheory.do_app_ptr_eq_oracle
  \\ drule evaluate_ptr_eq_free
  \\ disch_then (qspec_then `set (MAP FST (stubs c)) DIFF
       {Install_location; InstallData_location}` mp_tac)
  \\ impl_tac
  >- (
    simp [assign_ptr_eq_free]
    \\ fs [state_rel_thm]
    \\ imp_res_tac code_rel_ptr_eq_free \\ simp [])
  \\ simp []
QED

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

Theorem v_to_list_EQ_SOME_NIL:
   v_to_list hv1 = SOME [] <=> ∃ts. hv1 = Block ts 0 []
Proof
  Cases_on `hv1` \\ fs [v_to_list_def]
  \\ Cases_on `l` \\ fs [v_to_list_def] \\ EVAL_TAC
  \\ Cases_on `t` \\ fs [v_to_list_def]
  \\ Cases_on `t'` \\ fs [v_to_list_def]
  \\ every_case_tac \\ fs []
QED

Theorem LENGTH_EQ_4:
   (LENGTH xs = 4 <=> ?a1 a2 a3 a4. xs = [a1;a2;a3;a4]) /\
    (4 = LENGTH xs <=> ?a1 a2 a3 a4. xs = [a1;a2;a3;a4])
Proof
  Cases_on `xs` \\ fs []
  \\ rpt (Cases_on `t` \\ fs [] ORELSE Cases_on `t'` \\ fs [])
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

Theorem state_rel_cut_state_opt_SOME:
  state_rel c l1 l2 s t NONE locs ∧
  get_vars args s.locals = SOME vals ∧
  cut_state_opt (SOME kept_names) s = SOME x ⇒
  ∃y ws.
    cut_env (adjust_sets kept_names) t.locals = SOME y ∧
    get_vars (MAP adjust_var args) t = SOME ws ∧
    LENGTH args = LENGTH vals ∧ LENGTH args = LENGTH ws ∧
    state_rel c l1 l2 x t NONE locs ∧
    state_rel c l1 l2 x (t with locals := y) NONE locs
Proof
  rw []
  \\ drule_all data_to_word_gcProofTheory.state_rel_cut_IMP \\ strip_tac
  \\ drule_all data_to_word_gcProofTheory.state_rel_get_vars_IMP \\ strip_tac
  \\ imp_res_tac data_to_word_gcProofTheory.get_vars_IMP_LENGTH
  \\ ‘∃kenv. dataSem$cut_env kept_names s.locals = SOME kenv’ by
       gvs [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
  \\ drule_all data_to_word_gcProofTheory.cut_env_IMP_cut_env \\ strip_tac
  \\ gvs []
  \\ ‘x = s with locals := kenv’ by
       gvs [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
  \\ gvs []
  \\ metis_tac [data_to_word_gcProofTheory.state_rel_cut_env_cut_env]
QED

Theorem cut_state_opt_SOME_eq:
  cut_state_opt (SOME names) s = SOME x ==>
  x = s with locals := mk_wf (inter s.locals names)
Proof
  rw [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def,
      dataSemTheory.cut_env_def, AllCaseEqs()]
QED

val mk_wf_inter = MATCH_MP wf_mk_id (SPEC_ALL wf_inter) |> GEN_ALL;
val state_rel_cut_env' =
  state_rel_cut_env |> REWRITE_RULE [GSYM AND_IMP_INTRO];

Theorem state_rel_cut_state_opt_set_var:
  state_rel c l1 l2 (set_var dest v s2) r NONE locs /\
  cut_state_opt (SOME names) s2 = SOME s2_cut ==>
  state_rel c l1 l2 (set_var dest v s2_cut) r NONE locs
Proof
  strip_tac
  \\ imp_res_tac cut_state_opt_SOME_eq
  \\ `domain names SUBSET domain s2.locals` by
    (fs [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def,
         dataSemTheory.cut_env_def, AllCaseEqs()])
  \\ gvs [dataSemTheory.set_var_def, mk_wf_inter]
  \\ `cut_env (insert dest () names) (insert dest v s2.locals) =
      SOME (insert dest v (inter s2.locals names))` by (
    rw [dataSemTheory.cut_env_def]
    >- (rw [domain_insert, SUBSET_DEF] \\ fs [SUBSET_DEF, domain_lookup])
    \\ DEP_REWRITE_TAC [spt_eq_thm]
    \\ simp [wf_mk_wf, wf_insert, wf_inter,
             lookup_mk_wf, lookup_insert, lookup_inter, inter_insert,
             domain_insert]
    \\ rw [lookup_inter])
  \\ first_x_assum (mp_tac o GEN_ALL o SIMP_RULE (srw_ss()) [] o
       MATCH_MP state_rel_cut_env')
  \\ disch_then imp_res_tac
QED

(* Two-stage cut: narrowing an args-augmented cut (list_insert args ns) down to
   ns gives the same env as cutting ns directly. *)

Theorem cut_env_cut_env_list_insert:
  dataSem$cut_env (list_insert vs ns) env = SOME env_wide /\
  dataSem$cut_env ns env = SOME env_narrow ==>
  dataSem$cut_env ns env_wide = SOME env_narrow
Proof
  rw [dataSemTheory.cut_env_def, AllCaseEqs()]
  >- gvs [sptreeTheory.domain_inter, sptreeTheory.domain_list_insert,
          pred_setTheory.SUBSET_DEF]
  \\ simp [sptreeTheory.spt_eq_thm, sptreeTheory.wf_mk_wf,
           sptreeTheory.lookup_mk_wf, sptreeTheory.lookup_inter]
  \\ rw [] \\ rpt (CASE_TAC \\ rw [])
  \\ fs [sptreeTheory.lookup_NONE_domain, sptreeTheory.domain_list_insert,
         sptreeTheory.domain_lookup]
QED

(* A join_env pair-list over (l1,l2) is contained in the one over any
   lookup-supermaps (l1',l2') — moves memory_rel pairs between a cut env
   and the full env (with memory_rel_rearrange). *)

Theorem join_env_submap_MEM:
  (!k v. lookup k l1 = SOME v ==> lookup k l1' = SOME v) /\
  (!k v. lookup k l2 = SOME v ==> lookup k l2' = SOME v) /\
  MEM p (join_env l1 (toAList (inter l2 (adjust_set l1)))) ==>
  MEM p (join_env l1' (toAList (inter l2' (adjust_set l1'))))
Proof
  rw [join_env_def, MEM_MAP, MEM_FILTER, EXISTS_PROD, MEM_toAList]
  \\ qmatch_asmsub_rename_tac `lookup nn (inter l2 _) = SOME vv`
  \\ qexists_tac `nn` \\ gvs [lookup_inter_alt]
  \\ gvs [domain_lookup, lookup_adjust_set, ODD_EVEN] \\ res_tac \\ fs []
QED

Theorem size_of_app_Number:
  !xs ys lims i refs seen.
    size_of lims (xs ++ Number i::ys) refs seen =
    let (n,refs',seen') = size_of lims (xs ++ ys) refs seen in
    let k = if small_num lims.arch_64_bit i then 0
            else bignum_size lims.arch_64_bit i in
    (n + k,refs',seen')
Proof
  Induct
  >- (rpt strip_tac >> Cases_on ‘ys’ >> simp [size_of_def]
      >> rpt (pairarg_tac >> fs []) >> fs [])
  >> rpt strip_tac
  >> ‘!tail. size_of lims (h::tail) refs seen =
        let (n1,refs1,seen1) = size_of lims tail refs seen in
        let (n2,refs2,seen2) = size_of lims [h] refs1 seen1 in
        (n1+n2,refs2,seen2)’ by simp [Once size_of_cons]
  >> simp []
  >> last_x_assum (qspecl_then [‘ys’,‘lims’,‘i’,‘refs’,‘seen’] mp_tac)
  >> rpt (pairarg_tac >> fs []) >> rw [] >> fs []
QED

Theorem toList_delete_split:
  !k spt vv.
    sptree$lookup k spt = SOME vv ==>
    ?pre post.
      sptree$toList spt = pre ++ [vv] ++ post /\
      sptree$toList (sptree$delete k spt) = pre ++ post
Proof
  ho_match_mp_tac sptreeTheory.lookup_ind >>
  rpt conj_tac >> rpt strip_tac >>
  fs [sptreeTheory.lookup_def, sptreeTheory.delete_def,
      data_to_word_gcProofTheory.toListA_mk, sptreeTheory.toList_def,
      sptreeTheory.toListA_def]
  (* BN case *)
  >- (Cases_on ‘EVEN k’ >> fs [data_to_word_gcProofTheory.toListA_mk]
      >- (qexistsl_tac [‘pre’, ‘post ++ toListA [] t2’] >>
          simp [Once sptreeTheory.toListA_append,sptreeTheory.toListA_def] >>
          simp [Once sptreeTheory.toListA_append])
      >- (qexistsl_tac [‘toListA [] t1 ++ pre’, ‘post’] >>
          simp [Once sptreeTheory.toListA_append,sptreeTheory.toListA_def] >>
          simp [Once sptreeTheory.toListA_append]))
  (* BS case *)
  \\ Cases_on ‘k = 0’ >> fs [data_to_word_gcProofTheory.toListA_mk]
  >- (qexistsl_tac [‘toListA [] t1’, ‘toListA [] t2’] >>
      simp [sptreeTheory.toListA_def, Once sptreeTheory.toListA_append] >>
      simp [Once sptreeTheory.toListA_append]) >>
  Cases_on ‘EVEN k’ >> fs [data_to_word_gcProofTheory.toListA_mk]
  >- (qexistsl_tac [‘pre’, ‘post ++ [a] ++ toListA [] t2’] >>
      simp [sptreeTheory.toListA_def, Once sptreeTheory.toListA_append] >>
      simp [Once sptreeTheory.toListA_append])
  >- (qexistsl_tac [‘toListA [] t1 ++ [a] ++ pre’, ‘post’] >>
      simp [sptreeTheory.toListA_def, Once sptreeTheory.toListA_append] >>
      simp [Once sptreeTheory.toListA_append])
QED

Theorem size_of_heap_delete_Number_LE:
  !k s i.
    sptree$lookup k s.locals = SOME (Number i) ==>
    size_of_heap (s with locals := sptree$delete k s.locals) <= size_of_heap s
Proof
  rpt strip_tac >>
  drule toList_delete_split >> strip_tac >>
  simp [size_of_heap_def, stack_to_vs_def] >>
  ‘pre ++ [Number i] ++ post ++ FLAT (MAP extract_stack s.stack) ++ global_to_vs s.global =
   pre ++ Number i :: (post ++ FLAT (MAP extract_stack s.stack) ++ global_to_vs s.global)’
    by simp [] >>
  pop_assum SUBST_ALL_TAC >>
  ‘pre ++ post ++ FLAT (MAP extract_stack s.stack) ++ global_to_vs s.global =
   pre ++ (post ++ FLAT (MAP extract_stack s.stack) ++ global_to_vs s.global)’
    by simp [] >>
  pop_assum SUBST_ALL_TAC >>
  rewrite_tac [size_of_app_Number] >>
  rpt (pairarg_tac >> fs [])
QED

Theorem wf_FOLDR_delete:
  !ks (L:'a num_map). sptree$wf L ==> sptree$wf (FOLDR sptree$delete L ks)
Proof
  Induct >> rw [sptreeTheory.wf_delete]
QED

Theorem lookup_FOLDR_delete:
  !ks (L:'a num_map) h.
    sptree$lookup h (FOLDR sptree$delete L ks) =
    if MEM h ks then NONE else sptree$lookup h L
Proof
  Induct >> rw [sptreeTheory.lookup_delete] >> Cases_on ‘h = h'’ >> fs []
QED

Theorem size_of_heap_FOLDR_delete_Number_LE:
  !ks L (state:('a,'b)dataSem$state).
    sptree$wf L /\
    (!k. MEM k ks ==> sptree$lookup k L = NONE \/
                      ?i. sptree$lookup k L = SOME (Number i)) ==>
    size_of_heap (state with locals := FOLDR sptree$delete L ks) <=
    size_of_heap (state with locals := L)
Proof
  Induct >> rw [] >>
  ‘wf (FOLDR sptree$delete L ks)’ by simp [wf_FOLDR_delete] >>
  Cases_on ‘lookup h (FOLDR sptree$delete L ks) = NONE’
  >- (‘h NOTIN domain (FOLDR sptree$delete L ks)’ by
        (fs [domain_lookup, lookup_FOLDR_delete] >> rw []) >>
      ‘delete h (FOLDR sptree$delete L ks) = FOLDR sptree$delete L ks’
        by metis_tac [sptreeTheory.delete_fail] >>
      simp [] >> first_x_assum match_mp_tac >> metis_tac []) >>
  ‘?i. lookup h (FOLDR sptree$delete L ks) = SOME (Number i)’ by
    (fs [lookup_FOLDR_delete] >>
     Cases_on ‘MEM h ks’ >> fs [] >>
     last_x_assum (qspec_then ‘h’ mp_tac) >> simp []) >>
  irule LESS_EQ_TRANS >>
  qexists_tac ‘size_of_heap (state' with locals := FOLDR sptree$delete L ks)’ >>
  conj_tac
  >- (qspecl_then [‘h’, ‘state' with locals := FOLDR sptree$delete L ks’, ‘i’]
        mp_tac size_of_heap_delete_Number_LE >>
      simp []) >>
  first_x_assum (qspecl_then [‘L’, ‘state'’] mp_tac) >> simp [] >>
  disch_then irule >>
  rw [] >> last_x_assum (qspec_then ‘k’ mp_tac) >> simp []
QED

(* end size_of_heap monotonicity helpers *)

Theorem int_or_zero[local]:
  int_or i 0 = i
Proof
once_rewrite_tac[int_bit_equiv] >> simp[int_bit_or,int_bit_def]
QED

Theorem i2w_int_or:
  i2w(int_or i j)=(i2w i || i2w j:'a word)
Proof
mp_tac (Q.INST [`op`|->`Or`,`ws`|->`[i;j]`] word_simpProofTheory.int_op_correct) >> simp[wordSemTheory.word_op_def,word_simpTheory.int_op_def,int_or_zero,integer_wordTheory.i2w_pos]
QED

Theorem int_mod_mod_factor[local]:
  j <> 0 /\ j*k <> 0 ==> i % (j*k) % j = i % j
Proof
rpt strip_tac >>
 `i = i / (j*k) * (j*k) + i % (j*k)` by metis_tac[integerTheory.INT_DIVISION] >>
 `i / (j*k) * (j*k) = (i / (j*k) * k) * j` by simp[AC integerTheory.INT_MUL_COMM integerTheory.INT_MUL_ASSOC] >>
 qpat_x_assum `_ = _ + i % (j*k)` (mp_tac o AP_TERM ``\x:int. x % j``) >>
 simp[integerTheory.INT_MOD_ADD_MULTIPLES]
QED

Theorem i2w_mod_pow2:
  0 < k /\ k <= dimindex (:'a) ==> (i2w(i % &(2 ** k)):'a word) = ((k-1) -- 0) (i2w i)
Proof
rpt strip_tac >>
 `MIN (k-1) (dimindex(:'a)-1) = k-1` by (rw[MIN_DEF] >> fs[] >> decide_tac) >>
 CONV_TAC(RAND_CONV(RAND_CONV(REWR_CONV(GSYM n2w_w2n)))) >>
 asm_simp_tac std_ss [word_bits_n2w,bitTheory.BITS_ZERO3] >>
 `k-1+1=k` by decide_tac >> asm_rewrite_tac[] >>
 `dimword(:'a) = 2 ** k * 2 ** (dimindex(:'a)-k)` by
  (simp[dimword_def,GSYM EXP_ADD] >> AP_TERM_TAC >> decide_tac) >>
 `&w2n(i2w i:'a word) % &(2 ** k) = i % &(2 ** k)` by
  (rewrite_tac[integer_wordTheory.w2n_i2w] >>
   asm_rewrite_tac[] >> PURE_REWRITE_TAC[GSYM integerTheory.INT_MUL] >> irule int_mod_mod_factor >> simp[])
 >> asm_simp_tac std_ss [ADD1] >>
 qpat_x_assum `_ = i % _` (fn th => once_rewrite_tac[GSYM th]) >>
 asm_simp_tac std_ss [integerTheory.INT_MOD,integer_wordTheory.i2w_pos]
QED

Theorem compiler_ptr_bits_i2w:
  i2w(data_to_word$ptr_bits c tag len)=(ptr_bits c tag len:'a word)
Proof
simp[data_to_wordTheory.ptr_bits_def,ptr_bits_def,i2w_int_or,compiler_maxout_bits_i2w]
QED

Theorem state_rel_small_shift_length:
  state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem$state) vs locs ==> 0 < small_shift_length c /\ small_shift_length c <= dimindex(:'a)
Proof
fs[state_rel_def,small_shift_length_def,shift_length_def] >> rpt strip_tac >> decide_tac
QED

val _=augment_srw_ss[rewrites[i2w_int_or,i2w_mod_pow2,compiler_ptr_bits_i2w]];

Theorem IN_domain_adjust_set_inter:
   x ∈ domain (adjust_set (inter s1 s2)) <=>
    x ∈ domain (adjust_set s1) /\
    x ∈ domain (adjust_set s2)
Proof
  fs [domain_lookup,lookup_adjust_set]
  \\ rw [] \\ fs [lookup_inter] \\ rfs []
  \\ every_case_tac \\ fs []
QED

Theorem word_exp_ShiftVar_bits:
   bits = dimindex (:'a) ==>
   word_exp (t:('a,'c,'ffi) wordSem$state) (ShiftVar bits sow v n) =
    case lookup v t.locals of
    | SOME (Word w) =>
        OPTION_MAP Word
          (case sow of Lsl => SOME (w << n)
                     | Lsr => SOME (w >>> n)
                     | Asr => SOME (w >> n)
                     | Ror => SOME (word_ror w n))
    | _ => FAIL (word_exp t (ShiftVar bits sow v n)) "lookup failed"
Proof
  rw [] \\ simp [word_exp_set_var_ShiftVar_lemma]
QED

Theorem arch_width_eq32:
   width = Arch32 <=> arch_width_bits width = 32
Proof
  Cases_on `width` \\ simp [asmTheory.arch_width_bits_def]
QED

Theorem arch_bytes_scaled_word:
   arch_width_bits c.arch_width = dimindex(:'a) ==>
   n2w (n * arch_bytes c.arch_width) = (n2w n * bytes_in_word:'a word)
Proof
  rpt strip_tac \\ simp [GSYM word_mul_n2w]
QED

val _ = augment_srw_ss [rewrites [arch_width_eq32, arch_bytes_scaled_word]];

Theorem IS_SOME_lookup:
  IS_SOME (lookup n l) ⇔ n ∈ domain l
Proof
  gvs [IS_SOME_EXISTS,domain_lookup]
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

Theorem dimword_LESS_MustTerminate_limit:
   good_dimindex (:'a) ==> dimword (:α) < MustTerminate_limit (:α) - 1
Proof
  strip_tac \\ fs [wordSemTheory.MustTerminate_limit_def,dimword_def]
  \\ match_mp_tac (DECIDE ``1 < n ==> n < (2 * n + k) - 1n``)
  \\ fs [good_dimindex_def]
QED

Theorem small_int_Smallnum_sub:
  good_dimindex(:'a) /\ small_int (dimindex (:'a))(i1 - i2)  ==>
  Smallnum i1 - (Smallnum i2):'a word = Smallnum(i1 - i2)
Proof
 rw[Smallnum_i2w,good_dimindex_def,small_int_def,
    word_i2w_sub,integerTheory.INT_LDISTRIB, integerTheory.INT_SUB_LDISTRIB]
   \\ rewrite_tac [GSYM word_i2w_sub] \\ fs []
QED

Theorem OPTION_MAP2_NONE_THM:
  (OPTION_MAP2 f NONE x = NONE) ∧
  (OPTION_MAP2 f x NONE = NONE)
Proof
  Cases_on`x`>>fs[OPTION_MAP2_THM]
QED

Theorem opt_map_plus_zero_id[simp]:
  !n. OPTION_MAP2 $+ (SOME 0) n = (n:num option)
Proof
  Cases_on `n` >> fs []
QED

Theorem cut_state_refs_same:
  ∀n s x. dataSem$cut_state n s = SOME x ⇒ s.refs = x.refs
Proof
  simp [dataSemTheory.cut_state_def, CaseEq"option", PULL_EXISTS]
QED

(* ConfigGC: assign-specific helper + body *)

Theorem configGC_size_of_heap_LE:
  !ns s x k1 k2 i1 i2 (state:('a,'b)dataSem$state).
    dataSem$cut_state_opt (SOME (sptree$insert k2 () (sptree$insert k1 () ns))) s
      = SOME x /\
    sptree$lookup k1 x.locals = SOME (Number i1) /\
    sptree$lookup k2 x.locals = SOME (Number i2) /\
    state.refs = s.refs /\ state.limits = s.limits /\
    state.stack = s.stack /\ state.global = s.global ==>
    size_of_heap (state with locals := sptree$mk_wf (sptree$inter s.locals ns)) <=
    size_of_heap (state with locals := x.locals)
Proof
  rpt strip_tac >>
  gvs [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def,
       dataSemTheory.cut_env_def, AllCaseEqs()] >>
  qabbrev_tac ‘extras = FILTER (λa. lookup a ns = NONE) [k1;k2]’ >>
  qsuff_tac ‘FOLDR sptree$delete (inter s.locals (insert k2 () (insert k1 () ns))) extras
              = inter s.locals ns’
  >- (disch_then (assume_tac o SYM) >> pop_assum SUBST_ALL_TAC >>
      irule size_of_heap_FOLDR_delete_Number_LE >>
      conj_tac
      >- (rw [Abbr ‘extras’] >>
          fs [sptreeTheory.lookup_inter, sptreeTheory.lookup_insert] >>
          every_case_tac >> fs []) >>
      simp [sptreeTheory.wf_inter]) >>
  ‘wf (FOLDR sptree$delete (inter s.locals (insert k2 () (insert k1 () ns))) extras)
   /\ wf (inter s.locals ns)’
    by simp [wf_FOLDR_delete, sptreeTheory.wf_inter] >>
  rfs [sptreeTheory.spt_eq_thm] >>
  rw [lookup_FOLDR_delete, Abbr ‘extras’, sptreeTheory.lookup_inter,
      sptreeTheory.lookup_insert] >>
  every_case_tac >> fs [] >> rveq >> fs []
QED

(* Prepending values to the size_of root list never shrinks the heap count.
   Basis for the args-aware do_space bridge (replaces the two-stage size_of
   narrow/wide reconciliation helpers). *)
(* size_of_LE_append and size_of_heap_LE_args are inherited from
   data_to_word_bignumProof (used there by eval_Call_Arith). *)

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

(* Variant of call_env_push_env_dec_clock_lift that also absorbs a `locals
   := insert k v t.locals` field update inside the dec_clock. *)

Theorem call_env_push_env_dec_clock_lift_locals:
  call_env (args:'a word_loc list) b (push_env (y1,y2) NONE
    (wordSem$dec_clock ((t:('a,'c,'ffi) wordSem$state) with
      <|locals := insert k v t.locals; clock := ck'; termdep := tp|>))) =
  (call_env args b (push_env (y1,y2) NONE t)) with
    <|clock := ck' - 1; termdep := tp|>
Proof
  simp [wordSemTheory.dec_clock_def, wordSemTheory.call_env_def,
        wordSemTheory.push_env_def]
  \\ pairarg_tac \\ fs []
  \\ simp [wordSemTheory.state_component_equality]
QED

Theorem call_env_push_env_dec_clock_stack_max:
  (call_env args ls (push_env env F (dec_clock (s:('c,'ffi) dataSem$state)))).stack_max =
    OPTION_MAP2 MAX
      (OPTION_MAP2 MAX s.stack_max
         (OPTION_MAP2 (($+):num->num->num) s.locals_size (size_of_stack s.stack)))
      (OPTION_MAP2 (($+):num->num->num)
         (OPTION_MAP2 (($+):num->num->num) s.locals_size (size_of_stack s.stack)) ls)
Proof
  simp [dataSemTheory.call_env_def, dataSemTheory.push_env_def,
        dataSemTheory.dec_clock_def, dataSemTheory.size_of_stack_def,
        dataSemTheory.size_of_stack_frame_def]
QED

Theorem option_le_stackmax_bridge:
  ∀(m:num option) (l_size:num option) (s_size:num option)
    (ls_R:num option) (ls_Re:num option).
    option_le
      (OPTION_MAP2 MAX
         (OPTION_MAP2 MAX
            (OPTION_MAP2 MAX m (OPTION_MAP2 (($+):num->num->num) l_size s_size))
            (OPTION_MAP2 (($+):num->num->num)
               (OPTION_MAP2 (($+):num->num->num) l_size s_size) ls_R))
         (OPTION_MAP2 (($+):num->num->num) (OPTION_MAP2 MAX ls_R ls_Re)
            (OPTION_MAP2 (($+):num->num->num) s_size l_size)))
      (OPTION_MAP2 MAX m
         (OPTION_MAP2 (($+):num->num->num) (OPTION_MAP2 MAX ls_R ls_Re)
            (OPTION_MAP2 (($+):num->num->num) s_size l_size)))
Proof
  rpt strip_tac
  \\ Cases_on ‘m’ \\ Cases_on ‘l_size’ \\ Cases_on ‘s_size’
  \\ Cases_on ‘ls_R’ \\ Cases_on ‘ls_Re’
  \\ fs [OPTION_MAP2_DEF, backendPropsTheory.option_le_def]
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

Theorem compiler_tag_mask_i2w:
  arch_width_bits c.arch_width = dimindex (:'a) /\
  c.len_size + 9 < dimindex (:'a) ==>
  i2w (data_to_word$tag_mask c) = (data_to_word_memoryProof$tag_mask c:'a word)
Proof
  rpt strip_tac
  \\ `data_to_word$tag_mask c =
      data_to_word$all_ones (dimindex(:'a) - c.len_size) 2` by
    simp [data_to_wordTheory.tag_mask_def,data_to_wordTheory.all_ones_def]
  \\ asm_rewrite_tac []
  \\ simp [compiler_all_ones_i2w,
           data_to_word_memoryProofTheory.tag_mask_def,all_ones_def]
QED

val _ = augment_srw_ss [rewrites [compiler_tag_mask_i2w]];

Theorem state_rel_upd_safe_pkheap:
  ! c l1 l2 s lcl hpk r locs. state_rel c l1 l2
               (s with <| locals := lcl; space := 0; stack_max := NONE|>)
               r NONE locs <=>
  state_rel c l1 l2
               (s with
                <|locals := lcl; stack_max := NONE; space := 0; safe_for_space := F;
                  peak_heap_length := hpk|>)
               r NONE locs
Proof
  rw [state_rel_def] \\ metis_tac []
QED

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

(* TODO: move? *)

Theorem OPTION_MAP2_NONE[simp]:
  (OPTION_MAP2 f NONE n = NONE) /\ (OPTION_MAP2 f n NONE = NONE)
Proof
  rw[OPTION_MAP2_DEF]
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

Theorem cut_state_opt_IMP_ffi:
   dataSem$cut_state_opt names_opt s = SOME x ==> x.ffi = s.ffi
Proof
  fs [dataSemTheory.cut_state_opt_def,dataSemTheory.cut_state_def]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
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

Theorem Compare1_code_thm:
   !l a1 a2 dm m res c (t:('a,'c,'ffi) wordSem$state).
      word_cmp_loop l a1 a2 dm m = SOME res /\
      arch_width_bits c.arch_width = dimindex (:'a) /\
      dm = t.mdomain /\
      m = t.memory /\
      (?md. lookup Compare1_location t.code = SOME (4,Compare1_code c,md)) /\
      lookup Compare1_location t.stack_size = t.locals_size ∧
      get_var 0 t = SOME (Loc l1 l2) /\
      get_var 2 t = SOME (Word l) /\
      get_var 4 t = SOME (Word a1) /\
      get_var 6 t = SOME (Word a2) /\
      w2n l <= t.clock ==>
      ?ck smx.
        evaluate (Compare1_code c,t) =
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
  \\ qmatch_goalsub_abbrev_tac`evaluate (Compare1_code c,t1)`
  \\ rfs []
  \\ first_x_assum (qspecl_then [`c`,`t1`] mp_tac)
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

Theorem word_cmp_Less_word_cmp_res:
   !i i'. good_dimindex (:'a) ==>
           (word_cmp Less (word_cmp_res i i') (1w:'a word) <=> i < i')
Proof
  rw [] \\ fs [good_dimindex_def]
  \\ fs [word_cmp_res_def,asmTheory.word_cmp_def]
  \\ rw [] \\ fs [WORD_LT] \\ fs [word_msb_def,word_index,dimword_def]
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

Theorem compiler_Smallnum_i2w:
  i2w (data_to_word$Smallnum i) = (data_to_word_memoryProof$Smallnum i:'a word)
Proof
  simp [data_to_wordTheory.Smallnum_def,GSYM data_to_word_memoryProofTheory.Smallnum_i2w]
QED

val _ = augment_srw_ss [rewrites [compiler_Smallnum_i2w]];

Theorem INTRO_IS_SOME:
   (?v. x = SOME v) <=> IS_SOME x
Proof
  Cases_on `x` \\ fs []
QED

