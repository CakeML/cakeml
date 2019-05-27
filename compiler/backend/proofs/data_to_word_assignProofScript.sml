(*
  Part of the correctness proof for data_to_word
*)
open preamble int_bitwiseTheory dataSemTheory dataPropsTheory copying_gcTheory
     data_to_word_memoryProofTheory data_to_word_gcProofTheory
     data_to_word_bignumProofTheory data_to_wordTheory wordPropsTheory
     labPropsTheory whileTheory set_sepTheory semanticsPropsTheory
     helperLib alignmentTheory blastLib
     word_bignumTheory wordLangTheory word_bignumProofTheory
     gen_gc_partialTheory gc_sharedTheory word_gcFunctionsTheory;
local open gen_gcTheory in end

val _ = new_theory "data_to_word_assignProof";

val _ = set_grammar_ancestry
  ["data_to_word_memoryProof",
   "data_to_word_gcProof",
   "dataSem", "wordSem", "data_to_word"
  ];

fun drule0 th =
  first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))

val _ = hide "next";
val _ = hide "el";
val shift_def = backend_commonTheory.word_shift_def
val isWord_def = wordSemTheory.isWord_def
val theWord_def = wordSemTheory.theWord_def

val _ = temp_overload_on("FALSE_CONST",``Const (n2w 2:'a word)``)
val _ = temp_overload_on("TRUE_CONST",``Const (n2w 18:'a word)``)

val assign_def =
  data_to_wordTheory.assign_def
  |> REWRITE_RULE [arg1_def, arg2_def, arg3_def, arg4_def, all_assign_defs];

val clean_tac = rpt var_eq_tac \\ rpt (qpat_x_assum `T` kall_tac)
fun rpt_drule0 th = drule0 (th |> GEN_ALL) \\ rpt (disch_then drule0 \\ fs [])

val state_rel_def = data_to_word_gcProofTheory.state_rel_def
val code_rel_def = data_to_word_gcProofTheory.code_rel_def

val do_app = LIST_CONJ [do_app_def,do_app_aux_def,do_space_def,
  data_spaceTheory.op_space_req_def,
  dataLangTheory.op_space_reset_def]

val eval_tac = fs [wordSemTheory.evaluate_def,
  wordSemTheory.word_exp_def, wordSemTheory.set_var_def, set_var_def,
  wordSemTheory.the_words_def, wordSemTheory.mem_load_def,
  wordLangTheory.word_op_def, wordLangTheory.word_sh_def]

(* This list must list all auxiliary definitions used in assign_def *)
val assign_def_extras = save_thm("assign_def_extras",LIST_CONJ
  [LoadWord64_def,WriteWord64_def,BignumHalt_def,LoadBignum_def,
   AnyArith_code_def,Add_code_def,Sub_code_def,Mul_code_def,
   Div_code_def,Mod_code_def, Compare1_code_def, Compare_code_def,
   Equal1_code_def, Equal_code_def, LongDiv1_code_def, LongDiv_code_def,
   ShiftVar_def, generated_bignum_stubs_eq, DivCode_def,
   AddNumSize_def, AnyHeader_def, WriteWord64_on_32_def,
   WriteWord32_on_32_def, AllocVar_def, SilentFFI_def,
   WordOp64_on_32_def, WordShift64_on_32_def, Make_ptr_bits_code_def]);

Theorem get_vars_SING:
   dataSem$get_vars args s = SOME [w] ==> ?y. args = [y]
Proof
  Cases_on `args` \\ fs [get_vars_def]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ Cases_on `t` \\ fs [get_vars_def]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
QED

Theorem INT_EQ_NUM_LEMMA:
   0 <= (i:int) <=> ?index. i = & index
Proof
  Cases_on `i` \\ fs []
QED

Theorem memory_rel_lookup_var_IMP:
   memory_rel c be refs sp st m dm
     (join_env ll
        (toAList (inter t.locals (adjust_set ll))) ++ envs) ∧
    get_vars n ll = SOME x ∧
    get_vars (MAP adjust_var n) (t:('a,'c,'ffi) wordSem$state) = SOME w ⇒
    memory_rel c be refs sp st m dm
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
  \\ fs [labPropsTheory.good_dimindex_def,dimword_def] \\ rw []
QED

Theorem get_real_byte_offset_lemma:
   get_var v t = SOME (Word (w:α word)) ∧ good_dimindex (:α) ⇒
   word_exp t (real_byte_offset v) = SOME (Word (bytes_in_word + (w >>> 2)))
Proof
  rw[real_byte_offset_def,wordSemTheory.get_var_def]
  \\ eval_tac \\ fs[good_dimindex_def]
QED

Theorem reorder_lemma:
   memory_rel c be x.refs x.space t.store t.memory t.mdomain (x1::x2::x3::xs) ==>
    memory_rel c be x.refs x.space t.store t.memory t.mdomain (x3::x1::x2::xs)
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

Theorem heap_in_memory_store_IMP_UPDATE:
   heap_in_memory_store heap a sp sp1 gens c st m dm l ==>
    heap_in_memory_store heap a sp sp1 gens c (st |+ (Globals,h)) m dm l
Proof
  fs [heap_in_memory_store_def,FLOOKUP_UPDATE]
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
  \\ rw [] \\ match_mp_tac evaluate_GiveUp \\ fs []
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

Theorem RefArray_thm:
   state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) [] locs /\
    get_vars [0;1] s.locals = SOME vals /\
    t.clock = MustTerminate_limit (:'a) - 1 /\
    do_app RefArray vals s = Rval (v,s2) ==>
    ?q r new_c.
      evaluate (RefArray_code c,t) = (q,r) /\
      if q = SOME NotEnoughSpace then
        r.ffi = t.ffi
      else
        ?rv. q = SOME (Result (Loc l1 l2) rv) /\
             state_rel c r1 r2 (s2 with <| locals := LN; clock := new_c |>)
                r [(v,rv)] locs
Proof
  fs [RefArray_code_def]
  \\ fs [do_app_def,do_space_def,EVAL ``op_space_reset RefArray``,do_app_aux_def]
  \\ Cases_on `vals` \\ fs []
  \\ Cases_on `t'` \\ fs []
  \\ Cases_on `h` \\ fs []
  \\ Cases_on `t''` \\ fs []
  \\ IF_CASES_TAC \\ fs [] \\ rw []
  \\ drule0 NONNEG_INT \\ strip_tac \\ rveq \\ fs []
  \\ rename1 `get_vars [0; 1] s.locals = SOME [Number (&i); el]`
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw]
  \\ rpt_drule0 state_rel_get_vars_IMP \\ strip_tac \\ fs [LENGTH_EQ_2]
  \\ rveq \\ fs [adjust_var_def,get_vars_SOME_IFF]
  \\ fs [get_vars_SOME_IFF_data]
  \\ drule0 (Q.SPEC `0` state_rel_get_var_Number_IMP_alt) \\ fs []
  \\ strip_tac \\ rveq
  \\ rpt_drule0 evaluate_BignumHalt
  \\ Cases_on `small_int (:α) (&i)` \\ fs [] \\ strip_tac \\ fs []
  \\ ntac 3 (pop_assum kall_tac)
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw]
  \\ fs [wordSemTheory.get_var_def]
  \\ `w = n2w (4 * i) /\ 4 * i < dimword (:'a)` by
   (fs [state_rel_def,get_vars_SOME_IFF_data]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,get_var_def]
    \\ rpt_drule0 word_ml_inv_get_var_IMP
    \\ fs [get_var_def,wordSemTheory.get_var_def,adjust_var_def]
    \\ qpat_assum `lookup 0 s.locals = SOME (Number (&i))` assume_tac
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
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw]
  \\ `state_rel c l1 l2 s (set_var 1 (Word (n2w (4 * i))) t) [] locs` by
        fs [wordSemTheory.set_var_def,state_rel_insert_1]
  \\ rpt_drule0 AllocVar_thm
  \\ `?x. dataSem$cut_env (fromList [();()]) s.locals = SOME x` by
    (fs [EVAL ``sptree$fromList [(); ()]``,cut_env_def,domain_lookup,
         get_var_def,get_vars_SOME_IFF_data] \\ NO_TAC)
  \\ disch_then drule0
  \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def]
  \\ qabbrev_tac `limit = MIN (2 ** c.len_size) (dimword (:α) DIV 16)`
  \\ fs [get_var_set_var_thm]
  \\ Cases_on `evaluate
       (AllocVar c limit (fromList [(); ()]),set_var 1 (Word (n2w (4 * i))) t)`
  \\ fs []
  \\ disch_then drule0
  \\ impl_tac THEN1 (unabbrev_all_tac \\ fs []
                     \\ fs [state_rel_def,EVAL ``good_dimindex (:'a)``,dimword_def])
  \\ strip_tac \\ fs [set_vars_sing]
  \\ reverse IF_CASES_TAC \\ fs []
  \\ rveq \\ fs []
  \\ fs [dataSemTheory.call_env_def,push_env_def,
         dataSemTheory.set_var_def,wordSemTheory.set_var_def]
  \\ qabbrev_tac `new = LEAST ptr. ptr ∉ FDOM s.refs`
  \\ `new ∉ FDOM s.refs` by metis_tac [LEAST_NOTIN_FDOM]
  \\ fs [] \\ fs [list_Seq_def]
  \\ once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ fs [word_exp_rw]
  \\ `(?trig1. FLOOKUP r.store TriggerGC = SOME (Word trig1)) /\
      (?eoh1. FLOOKUP r.store EndOfHeap = SOME (Word eoh1)) /\
      (?cur1. FLOOKUP r.store CurrHeap = SOME (Word cur1))` by
        (fs [state_rel_thm,memory_rel_def,heap_in_memory_store_def] \\ NO_TAC)
  \\ fs []
  \\ `lookup 2 r.locals = SOME (Word (n2w (4 * i)))` by
   (qabbrev_tac `s9 = s with <|locals := x; space := 4 * i DIV 4 + 1|>`
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
    \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def]
    \\ rw [] \\ fs [word_addr_def,Smallnum_def] \\ rfs []
    \\ fs [small_int_def,X_LT_DIV,word_addr_def]
    \\ match_mp_tac minus_2_word_and_id
    \\ fs [word_index,word_mul_n2w,bitTheory.BIT0_ODD,ODD_MULT] \\ NO_TAC)
  \\ fs []
  \\ IF_CASES_TAC
  THEN1 (fs [shift_def,state_rel_def,EVAL ``good_dimindex (:'a)``])
  \\ asm_rewrite_tac [] \\ pop_assum kall_tac \\ fs []
  \\ once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ fs [word_exp_rw]
  \\ simp [wordSemTheory.set_var_def,lookup_insert,wordSemTheory.set_store_def]
  \\ `n2w (4 * i) ⋙ 2 = n2w i` by
   (once_rewrite_tac [GSYM w2n_11] \\ rewrite_tac [w2n_lsr]
    \\ fs [ONCE_REWRITE_RULE[MULT_COMM]MULT_DIV])
  \\ fs [WORD_LEFT_ADD_DISTRIB]
  \\ `good_dimindex(:'a)` by fs [state_rel_def]
  \\ fs [shift_lsl]
  \\ once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ fs [word_exp_rw,FLOOKUP_UPDATE,wordSemTheory.set_var_def,WORD_LEFT_ADD_DISTRIB]
  \\ qabbrev_tac `ww = eoh1 + -1w * bytes_in_word + -1w * (bytes_in_word * n2w i)`
  \\ qabbrev_tac `ww1 = trig1 + -1w * bytes_in_word + -1w * (bytes_in_word * n2w i)`
  \\ fs [Once insert_insert]
  \\ once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ fs [word_exp_rw,wordSemTheory.set_var_def]
  \\ once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ fs [word_exp_rw,wordSemTheory.set_var_def,wordSemTheory.set_store_def]
  \\ fs [FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
  \\ IF_CASES_TAC
  THEN1 (fs [shift_def,state_rel_def,EVAL ``good_dimindex (:'a)``])
  \\ asm_rewrite_tac [] \\ pop_assum kall_tac \\ fs []
  \\ fs [wordSemTheory.set_var_def]
  \\ once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ fs [word_exp_rw,wordSemTheory.set_var_def,lookup_insert]
  \\ once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ fs [word_exp_rw,wordSemTheory.set_store_def,lookup_insert,
         wordSemTheory.get_var_def,wordSemTheory.mem_store_def]
  \\ qpat_assum `state_rel c l1 l2 _ _ _ _` mp_tac
  \\ simp_tac std_ss [Once state_rel_thm] \\ strip_tac \\ fs []
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 memory_rel_lookup
  \\ `lookup 1 x = SOME el` by
   (fs [cut_env_def] \\ rveq \\ fs []
    \\ fs [lookup_inter_alt,get_vars_SOME_IFF_data,get_var_def]
    \\ EVAL_TAC \\ NO_TAC)
  \\ `?w6. lookup (adjust_var 1) r.locals = SOME w6` by
   (`IS_SOME (lookup 1 x)` by fs [] \\ res_tac \\ fs []
    \\ Cases_on `lookup (adjust_var 1) r.locals` \\ fs [])
  \\ rpt (disch_then drule0) \\ strip_tac
  \\ rpt_drule0 memory_rel_RefArray
  \\ `encode_header c 2 i = SOME (make_header c 2w i)` by
   (fs[encode_header_def,memory_rel_def,heap_in_memory_store_def]
    \\ reverse conj_tac THEN1
     (fs[encode_header_def,memory_rel_def,heap_in_memory_store_def,EXP_SUB]
      \\ unabbrev_all_tac \\ fs [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
      \\ rfs [labPropsTheory.good_dimindex_def,dimword_def])
    \\ `1 < dimindex (:α) − (c.len_size + 2)` by
     (qpat_assum `c.len_size + _ < dimindex (:α)` mp_tac
      \\ rpt (pop_assum kall_tac) \\ decide_tac)
    \\ fs[good_dimindex_def,dimword_def])
  \\ rpt (disch_then drule0)
  \\ impl_tac THEN1 (fs [ONCE_REWRITE_RULE[MULT_COMM]MULT_DIV])
  \\ strip_tac
  \\ fs [LET_THM]
  \\ `trig1 = trig /\ eoh1 = eoh /\ cur1 = curr` by
        (fs [FLOOKUP_DEF] \\ NO_TAC) \\ rveq \\ fs []
  \\ `eoh + -1w * (bytes_in_word * n2w (i + 1)) = ww` by
      (unabbrev_all_tac \\ fs [WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w] \\ NO_TAC)
  \\ fs [] \\ pop_assum kall_tac
  \\ fs [store_list_def,FOUR_MUL_LSL]
  \\ `(n2w i ≪ (dimindex (:α) − (c.len_size + 2) + 2) ‖ make_header c 2w 0) =
      make_header c 2w i:'a word` by
   (fs [make_header_def,WORD_MUL_LSL,word_mul_n2w,LEFT_ADD_DISTRIB]
    \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
    \\ fs [memory_rel_def,heap_in_memory_store_def] \\ NO_TAC) \\ fs []
  \\ `lookup Replicate_location r.code = SOME (5,Replicate_code)` by
         (imp_res_tac lookup_RefByte_location \\ NO_TAC)
  \\ assume_tac (GEN_ALL Replicate_code_thm)
  \\ SEP_I_TAC "evaluate"
  \\ fs [wordSemTheory.get_var_def,lookup_insert] \\ rfs []
  \\ pop_assum drule0
  \\ impl_tac THEN1 (fs [adjust_var_def] \\ fs [state_rel_def]
                     \\ `i < dimword (:'a)` by decide_tac \\ fs [])
  \\ strip_tac \\ fs []
  \\ pop_assum mp_tac \\ fs []
  \\ strip_tac \\ fs []
  \\ simp [state_rel_thm]
  \\ fs []
  \\ fs [lookup_def]
  \\ qpat_assum `memory_rel _ _ _ _ _ _ _ _` mp_tac
  \\ fs [EVAL ``join_env LN []``]
  \\ fs [code_oracle_rel_def,FLOOKUP_UPDATE]
  \\ drule memory_rel_zero_space
  \\ `EndOfHeap <> TriggerGC` by fs []
  \\ pop_assum (fn th => fs [MATCH_MP FUPDATE_COMMUTES th])
  \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,Abbr`ww1`]
  \\ match_mp_tac memory_rel_rearrange
  \\ fs [] \\ rw [] \\ rw []
  \\ fs [FAPPLY_FUPDATE_THM]
  \\ disj1_tac
  \\ fs [make_ptr_def]
  \\ qunabbrev_tac `ww`
  \\ AP_THM_TAC \\ AP_TERM_TAC \\ fs []
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
  \\ fs [wordSemTheory.set_var_def,lookup_insert,word_of_byte_def,
         insert_shadow,wordSemTheory.evaluate_def,word_exp_rw]
QED

Theorem w2w_shift_shift:
   good_dimindex (:'a) ==> ((w2w (w:word8) ≪ 2 ⋙ 2) : 'a word) = w2w w
Proof
  fs [labPropsTheory.good_dimindex_def,fcpTheory.CART_EQ,
      word_lsl_def,word_lsr_def,fcpTheory.FCP_BETA,w2w]
  \\ rw [] \\ fs [] \\ EQ_TAC \\ rw [] \\ rfs [fcpTheory.FCP_BETA,w2w]
QED

fun sort_tac n =
  CONV_TAC(PATH_CONV(String.concat(List.tabulate(n,(K "lr"))))(REWR_CONV set_byte_sort)) \\
  simp[labPropsTheory.good_dimindex_def]

Theorem evaluate_WriteLastBytes:
   good_dimindex(:'a) ∧ w2n n < dimindex(:'a) DIV 8 ∧
   get_vars [av;bv;nv] (s:('a,'c,'ffi)wordSem$state) = SOME [Word (a:'a word); Word b; Word n] ∧
   byte_aligned a ∧ a ∈ s.mdomain ∧ s.memory a = Word w
  ⇒
   evaluate (WriteLastBytes av bv nv,s) =
     (NONE, s with memory := (a =+ Word (last_bytes (w2n n) (w2w b) 0w w s.be)) s.memory)
Proof
  rw[labPropsTheory.good_dimindex_def]
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
  \\ fs[w2n_add_byte_align_lemma,labPropsTheory.good_dimindex_def]
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
  >- ( simp[Once set_byte_sort,labPropsTheory.good_dimindex_def] )
  >- ( map_every sort_tac [1,2,1])
  >- ( Cases_on`n` \\ fs[dimword_def] \\ rfs[] )
  >- ( simp[Once set_byte_sort,labPropsTheory.good_dimindex_def] )
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

Theorem RefByte_thm:
   state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) [] locs /\
    get_vars [0;1;2] s.locals = SOME (vals ++ [Number &(if fl then 0 else 4)]) /\
    t.clock = MustTerminate_limit (:'a) - 1 /\
    do_app (RefByte fl) vals s = Rval (v,s2) ==>
    ?q r new_c.
      evaluate (RefByte_code c,t) = (q,r) /\
      if q = SOME NotEnoughSpace then
        r.ffi = t.ffi
      else
        ?rv. q = SOME (Result (Loc l1 l2) rv) /\
             state_rel c r1 r2 (s2 with <| locals := LN; clock := new_c |>)
                r [(v,rv)] locs
Proof
  qpat_abbrev_tac`tag = if fl then _ else _`
  \\ fs [RefByte_code_def]
  \\ fs [do_app_def,do_space_def,EVAL ``op_space_reset (RefByte fl)``,do_app_aux_def]
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
  \\ rpt_drule0 evaluate_BignumHalt
  \\ Cases_on `small_int (:α) (&i)` \\ fs [] \\ strip_tac \\ fs []
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
  \\ qabbrev_tac `wA = ((bytes_in_word + n2w i + -1w)
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
  \\ rveq \\ fs []
  \\ fs [dataSemTheory.call_env_def,push_env_def,
         dataSemTheory.set_var_def,wordSemTheory.set_var_def]
  \\ qabbrev_tac `new = LEAST ptr. ptr ∉ FDOM s.refs`
  \\ `new ∉ FDOM s.refs` by metis_tac [LEAST_NOTIN_FDOM]
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
      \\ fs[labPropsTheory.good_dimindex_def,dimword_def] )
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
  \\ qabbrev_tac `var5 = (bytes_in_word + n2w i + -1w:'a word) ⋙ shift (:α)`
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
      labPropsTheory.good_dimindex_def,word_add_n2w,dimword_def] \\ rfs []
    \\ fs [GSYM word_add_n2w] \\ fs [word_add_n2w,dimword_def]
    \\ fs [DIV_DIV_DIV_MULT] \\ NO_TAC)
  \\ fs [wordSemTheory.set_var_def,lookup_insert]
  \\ rpt_drule0 memory_rel_RefByte_alt
  \\ disch_then (qspecl_then [`w`,`i`,`fl`] mp_tac) \\ fs []
  \\ impl_tac THEN1
   (unabbrev_all_tac \\ fs []
    \\ fs [labPropsTheory.good_dimindex_def,dimword_def] \\ rfs [])
  \\ strip_tac \\ fs [FLOOKUP_DEF] \\ rveq \\ clean_tac
  \\ `var5 = n2w (byte_len (:α) i)` by
   (unabbrev_all_tac
    \\ rewrite_tac [GSYM w2n_11,w2n_lsr,byte_len_def]
    \\ fs [bytes_in_word_def,shift_def,labPropsTheory.good_dimindex_def]
    \\ fs [word_add_n2w]
    THEN1
     (sg `i + 3 < dimword (:'a)`
      \\ sg `i + 3 DIV 4 < dimword (:'a)` \\ fs []
      \\ rfs [dimword_def] \\ fs [DIV_LT_X])
    THEN1
     (sg `i + 7 < dimword (:'a)`
      \\ sg `i + 7 DIV 8 < dimword (:'a)` \\ fs []
      \\ rfs [dimword_def] \\ fs [DIV_LT_X]) \\ NO_TAC)
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
    \\ fs [labPropsTheory.good_dimindex_def,GSYM word_add_n2w,WORD_MUL_LSL]
    \\ fs [word_mul_n2w,word_add_n2w,shift_def,RIGHT_ADD_DISTRIB]
    \\ NO_TAC)
  \\ rveq \\ pop_assum kall_tac
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,
         wordSemTheory.get_var_def,lookup_insert,
         wordSemTheory.mem_store_def,store_list_def]
  \\ IF_CASES_TAC
  >- (
    simp[Once wordSemTheory.evaluate_def,
         wordSemTheory.get_var_def,lookup_insert,
         wordSemTheory.call_env_def]
    \\ fs[state_rel_thm,fromList2_def,lookup_def]
    \\ fs[make_ptr_def,join_env_NIL,FAPPLY_FUPDATE_THM]
    \\ fs[WORD_MUL_LSL,word_mul_n2w]
    \\ `4 * byte_len (:'a) i = 0`
    by (
      match_mp_tac (MP_CANON MOD_EQ_0_0)
      \\ qexists_tac`dimword(:'a)`
      \\ simp[]
      \\ rfs[Abbr`limit`,labPropsTheory.good_dimindex_def,dimword_def]
      \\ fs[] \\ NO_TAC)
    \\ fs [code_oracle_rel_def,FLOOKUP_UPDATE]
    \\ fs[REPLICATE,LUPDATE_def,store_list_def]
    \\ rveq
    \\ qhdtm_x_assum`memory_rel`mp_tac
    \\ simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ qmatch_goalsub_abbrev_tac`(RefPtr new,val)::(ll++rest)`
    \\ fs[]
    \\ match_mp_tac memory_rel_rearrange
    \\ rpt (pop_assum kall_tac)
    \\ fs [] \\ rw [] \\ fs [])
  \\ once_rewrite_tac[list_Seq_def]
  \\ simp[wordSemTheory.evaluate_def,word_exp_rw]
  \\ simp[wordSemTheory.set_var_def]
  \\ once_rewrite_tac[list_Seq_def]
  \\ simp[wordSemTheory.evaluate_def,word_exp_rw,
          asmTheory.word_cmp_def,wordSemTheory.get_var_def]
  \\ `(bytes_in_word:'a word) + -1w = n2w (2 ** shift(:'a) - 1)`
  by ( fs[bytes_in_word_def,labPropsTheory.good_dimindex_def,shift_def] )
  \\ simp[WORD_AND_EXP_SUB1]
  \\ `i MOD 2 ** (shift(:'a)) < dimword(:'a)`
  by (
    match_mp_tac LESS_LESS_EQ_TRANS
    \\ qexists_tac`2 ** shift(:'a)`
    \\ simp[]
    \\ fs[labPropsTheory.good_dimindex_def,dimword_def,shift_def] )
  \\ simp[]
  \\ `2 ** shift(:'a) = dimindex(:'a) DIV 8`
    by ( fs[labPropsTheory.good_dimindex_def,dimword_def,shift_def] )
  \\ simp[]
  \\ IF_CASES_TAC \\ fs[]
  >- (
    simp[list_Seq_def]
    \\ `lookup Replicate_location r.code = SOME (5,Replicate_code)` by
           (imp_res_tac lookup_RefByte_location \\ NO_TAC)
    \\ assume_tac (GEN_ALL Replicate_code_thm)
    \\ SEP_I_TAC "evaluate"
    \\ fs[wordSemTheory.get_var_def,lookup_insert] \\ rfs[]
    \\ pop_assum mp_tac \\ disch_then drule0
    \\ impl_tac THEN1
     (fs [WORD_MUL_LSL,word_mul_n2w,state_rel_def]
      \\ fs [labPropsTheory.good_dimindex_def,dimword_def] \\ rfs []
      \\ unabbrev_all_tac \\ fs []
      \\ `byte_len (:α) i < dimword (:'a)` by (fs [dimword_def])
      \\ fs [IMP_LESS_MustTerminate_limit])
    \\ fs [WORD_MUL_LSL,word_mul_n2w]
    \\ disch_then kall_tac
    \\ simp[state_rel_thm,lookup_def]
    \\ fs[make_ptr_def,join_env_NIL,FAPPLY_FUPDATE_THM]
    \\ fs [WORD_MUL_LSL,word_mul_n2w]
    \\ fs [code_oracle_rel_def,FLOOKUP_UPDATE]
    \\ qhdtm_x_assum`memory_rel`mp_tac
    \\ simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_rearrange
    \\ rpt (pop_assum kall_tac)
    \\ rw [] \\ fs [] \\ rw [])
  \\ simp[CONJUNCT2 (CONJUNCT2 list_Seq_def),
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
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ pop_assum mp_tac
  \\ assume_tac(GEN_ALL evaluate_WriteLastBytes)
  \\ SEP_I_TAC "evaluate"
  \\ pop_assum mp_tac
  \\ simp[wordSemTheory.get_vars_def,wordSemTheory.get_var_def,lookup_insert,APPLY_UPDATE_THM]
  \\ impl_tac
  >- (
    conj_tac >- fs[labPropsTheory.good_dimindex_def]
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
  \\ pop_assum mp_tac \\ simp[list_Seq_def]
  \\ simp[Once wordSemTheory.evaluate_def,word_exp_rw,wordSemTheory.set_var_def]
  \\ strip_tac \\ clean_tac \\ fs[]
  \\ `lookup Replicate_location r.code = SOME (5,Replicate_code)` by
         (imp_res_tac lookup_RefByte_location \\ NO_TAC)
  \\ qmatch_asmsub_abbrev_tac`LUPDATE lw (len-1) ls`
  \\ qmatch_assum_abbrev_tac`Abbrev(ls = REPLICATE len rw)`
  \\ `0 < len` by ( Cases_on`len` \\ fs[] )
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
    \\ fs [labPropsTheory.good_dimindex_def,dimword_def,state_rel_thm] \\ rfs []
    \\ unabbrev_all_tac \\ fs []
    \\ `byte_len (:α) i -1 < dimword (:'a)` by (fs [dimword_def])
    \\ imp_res_tac IMP_LESS_MustTerminate_limit \\ fs[])
  \\ simp[WORD_MUL_LSL,n2w_sub,GSYM word_mul_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ disch_then kall_tac
  \\ simp [state_rel_thm]
  \\ fs []
  \\ fs [lookup_def]
  \\ qhdtm_x_assum `memory_rel` mp_tac
  \\ fs [EVAL ``join_env LN []``,code_oracle_rel_def,FLOOKUP_UPDATE]
  \\ fs[store_list_def]
  \\ fs[Abbr`a'`,Abbr`v`,LENGTH_REPLICATE]
  \\ clean_tac
  \\ fs[make_ptr_def,WORD_MUL_LSL]
  \\ qmatch_abbrev_tac`P xx yy zz ⇒ P x' yy z'`
  \\ `xx = x'`
  by (
    simp[Abbr`xx`,Abbr`x'`,FUN_EQ_THM,APPLY_UPDATE_THM,Abbr`lw`]
    \\ simp[n2w_sub,WORD_LEFT_ADD_DISTRIB] \\ rw[]
    \\ simp[w2w_word_of_byte_w2w] )
  \\ rveq \\ qunabbrev_tac `P`
  \\ match_mp_tac memory_rel_rearrange
  \\ unabbrev_all_tac \\ rpt (pop_assum kall_tac)
  \\ fs[FAPPLY_FUPDATE_THM]
  \\ rw [] \\ fs []
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
        (SOME (Result (Loc l1 l2) ret_val),
         r with <| memory := m1 ; clock := r.clock - k - 1; locals := LN ;
                   store := r.store |+ (NextFree, Word b1) |>)
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
             wordSemTheory.get_var_def,word_exp_rw,fromList2_def,
             asmTheory.word_cmp_def,wordSemTheory.dec_clock_def,lookup_insert,
             wordSemTheory.mem_store_def,list_Seq_def,wordSemTheory.set_var_def,
             wordSemTheory.set_store_def])
  \\ Cases_on `a` \\ fs []
  \\ Cases_on `get_real_addr c r.store c'` \\ fs []
  \\ qabbrev_tac `m9 = (b =+ x) r.memory`
  \\ ntac 2 (simp [Once list_Seq_def])
  \\ simp [wordSemTheory.evaluate_def,word_exp_rw,wordSemTheory.call_env_def,
           wordSemTheory.get_var_def,word_exp_rw,fromList2_def,
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
       r with <|locals := insert 6 _ _ ; memory := m9 ; clock := _ |> `
  \\ first_x_assum (qspecl_then [`(m9 (x1 + 2w * bytes_in_word))`,
         `b + bytes_in_word`,`r7`,`m9 (x1 + bytes_in_word)`,`m1`,
         `0`,`2`,`4`,`6`,`8`,`10`] mp_tac)
  \\ reverse impl_tac THEN1
    (strip_tac \\ fs [] \\ rw [wordSemTheory.state_component_equality,Abbr `r7`])
  \\ unabbrev_all_tac \\ fs []
  \\ fs [wordSemTheory.get_var_def,lookup_insert]
  \\ fs [MULT_CLAUSES,GSYM word_add_n2w]
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
     (fs [labPropsTheory.good_dimindex_def,dimword_def,small_int_def] \\ NO_TAC)
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

Theorem FromList_thm:
   state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) [] locs /\
    encode_header c (4 * tag) 0 <> (NONE:'a word option) /\
    get_vars [0; 1; 2] s.locals = SOME [v1; v2; Number (&(4 * tag))] /\
    t.clock = MustTerminate_limit (:'a) - 1 /\
    do_app (FromList tag) [v1; v2] s = Rval (v,s2) ==>
    ?q r new_c.
      evaluate (FromList_code c,t) = (q,r) /\
      if q = SOME NotEnoughSpace then
        r.ffi = t.ffi
      else
        ?rv. q = SOME (Result (Loc l1 l2) rv) /\
             state_rel c r1 r2 (s2 with <| locals := LN; clock := new_c |>)
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
  \\ `small_int (:α) (&(4 * tag))` by
     (fs [encode_header_def,small_int_def,state_rel_thm,
          labPropsTheory.good_dimindex_def,dimword_def] \\ rfs [] \\ NO_TAC)
  \\ IF_CASES_TAC THEN1
   (qpat_assum `get_var 2 s.locals = SOME (Number (&(4*tag)))` assume_tac
    \\ rpt_drule0 state_rel_get_var_Number_IMP \\ fs []
    \\ fs [LENGTH_NIL] \\ rveq \\ rw []
    \\ fs [list_Seq_def,wordSemTheory.evaluate_def,word_exp_rw,
           wordSemTheory.get_var_def,adjust_var_def,wordSemTheory.set_var_def]
    \\ rveq \\ fs [lookup_insert]
    \\ `lookup 0 t.locals = SOME (Loc l1 l2)` by fs [state_rel_def] \\ fs []
    \\ fs [state_rel_thm,wordSemTheory.call_env_def,lookup_def,with_fresh_ts_def]
    \\ reverse (Cases_on `s.tstamps`)
    \\ fs [] \\ rveq
    \\ fs [EVAL ``(toAList (inter (fromList2 []) (insert 0 () LN)))`` ]
    \\ fs [EVAL ``join_env LN []``,lookup_insert]
    \\ fs [BlockNil_def,Smallnum_def,WORD_MUL_LSL,word_mul_n2w]
    \\ `n2w (16 * tag) + 2w = BlockNil tag : 'a word` by
          fs [BlockNil_def,WORD_MUL_LSL,word_mul_n2w] \\ fs []
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
  \\ rpt_drule0 state_rel_get_var_Number_IMP_alt \\ fs []
  \\ strip_tac \\ rveq
  \\ rpt_drule0 evaluate_BignumHalt
  \\ Cases_on `small_int (:α) (&(LENGTH x))` \\ fs [] \\ strip_tac \\ fs []
  \\ ntac 3 (pop_assum kall_tac)
  \\ fs []
  \\ ntac 2 (once_rewrite_tac [list_Seq_def])
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,wordSemTheory.get_var_def]
  \\ pairarg_tac \\ fs []
  \\ `state_rel c l1 l2 s (set_var 1 (Word w) t) [] locs` by
        fs [wordSemTheory.set_var_def,state_rel_insert_1]
  \\ rpt_drule0 AllocVar_thm
  \\ `?x. dataSem$cut_env (fromList [();();()]) s.locals = SOME x` by
    (fs [EVAL ``sptree$fromList [();();()]``,cut_env_def,domain_lookup,
         get_var_def,get_vars_SOME_IFF_data] \\ NO_TAC)
  \\ disch_then drule0
  \\ fs [get_var_set_var]
  \\ disch_then drule0
  \\ impl_tac THEN1 (unabbrev_all_tac \\ fs []
                     \\ fs [state_rel_def,EVAL ``good_dimindex (:'a)``,dimword_def])
  \\ strip_tac \\ fs []
  \\ reverse (Cases_on `res`) \\ fs []
  \\ `?f cur. FLOOKUP s1.store NextFree = SOME (Word f) /\
              FLOOKUP s1.store CurrHeap = SOME (Word cur)` by
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
       (fs [state_rel_def,labPropsTheory.good_dimindex_def] \\ NO_TAC)
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
  \\ `lookup FromList1_location s1.code = SOME (6,FromList1_code c)` by
       (fs [code_rel_def,stubs_def] \\ rfs [] \\ NO_TAC)
  \\ rfs []
  \\ disch_then (qspec_then `c` mp_tac)
  \\ `encode_header c (4 * tag) (LENGTH x) = SOME hd` by
   (fs [encode_header_def] \\ conj_tac THEN1
     (fs [encode_header_def,dimword_def,labPropsTheory.good_dimindex_def]
      \\ rfs [] \\ conj_tac \\ fs [] \\ rfs [DIV_LT_X]
      \\ fs [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV])
    \\ fs [make_header_def,Abbr`hd`]
    \\ fs [WORD_MUL_LSL,word_mul_n2w,Smallnum_def,EXP_LEMMA1]
    \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
    \\ fs [memory_rel_def,heap_in_memory_store_def]
    \\ fs [labPropsTheory.good_dimindex_def] \\ rfs [])
  \\ rpt_drule0 memory_rel_FromList
  \\ Cases_on `x` \\  fs []
  \\ qabbrev_tac `x = h::t'`
  \\ `x ≠ []` by rw [Abbr `x`]
  \\ qpat_x_assum `Abbrev _` (K ALL_TAC)
  \\ Cases_on `s.tstamps`
  \\ fs [] \\ rveq
  \\ TRY (qpat_assum `s.tstamps = NONE` (K (disch_then (mp_tac o Q.SPEC `0`))))
  \\ TRY (qpat_assum `s.tstamps = SOME _` (K (disch_then (mp_tac o Q.SPEC `x''`))))
  \\ (impl_tac THEN1
    (fs [Abbr `s0`,ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV])
  \\ strip_tac
  \\ disch_then drule0
  \\ impl_tac THEN1
   (fs [Abbr `s0`,ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
    \\ fs [Smallnum_def,dimword_def,labPropsTheory.good_dimindex_def] \\ rfs [])
  \\ strip_tac \\ fs [lookup_def,EVAL ``join_env LN []``]
  \\ fs [Abbr`s0`]
  \\ fs [FAPPLY_FUPDATE_THM,FLOOKUP_UPDATE]
  \\ drule0 memory_rel_zero_space
  \\ match_mp_tac memory_rel_rearrange
  \\ fs [] \\ rw [] \\ fs [])
QED

val get_var_get_real_addr_lemma =
    GEN_ALL(CONV_RULE(LAND_CONV(move_conj_left(
                                   same_const``wordSem$get_var`` o #1 o
                                   strip_comb o lhs)))
                     get_real_addr_lemma)

Theorem evaluate_LoadWord64:
   memory_rel c be refs sp t.store t.memory t.mdomain ((Word64 w,v)::vars) ∧
   shift_length c < dimindex(:α) ∧ dimindex(:α) = 64 ∧
   get_var src (t:('a,'c,'ffi) state) = SOME v
   ==>
   evaluate (LoadWord64 c dest src,t) = (NONE, set_var dest (Word (w2w w)) t)
Proof
  rw[LoadWord64_def] \\ eval_tac
  \\ rpt_drule0 memory_rel_Word64_IMP
  \\ impl_keep_tac >- fs[good_dimindex_def]
  \\ strip_tac \\ rfs[] \\ clean_tac
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ simp[] \\ disch_then drule0
  \\ simp[] \\ rw[]
  \\ rpt(AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ simp[FUN_EQ_THM]
  \\ rw[WORD_w2w_EXTRACT]
QED

Theorem evaluate_WriteWord64:
   memory_rel c be refs sp t.store t.memory t.mdomain
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
     memory_rel c be refs (sp-2) (t.store |+ (NextFree, nf)) m' t.mdomain
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
  \\ qmatch_abbrev_tac`memory_rel c be refs sp' st' m' md vars'`
  \\ qmatch_assum_abbrev_tac`memory_rel c be refs sp' st' m'' md vars'`
  \\ `m' = m''` suffices_by simp[]
  \\ simp[Abbr`m'`,Abbr`m''`,FUN_EQ_THM,APPLY_UPDATE_THM]
  \\ rw[] \\ fs[]
  \\ fs [addressTheory.WORD_EQ_ADD_CANCEL]
  \\ pop_assum mp_tac \\ EVAL_TAC
  \\ fs [dimword_def]
QED

Theorem evaluate_WriteWord64_on_32:
   memory_rel c be refs sp t.store t.memory t.mdomain
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
     memory_rel c be refs (sp-3) (t.store |+ (NextFree, nf)) m' t.mdomain
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
  \\ qmatch_abbrev_tac`memory_rel c be refs sp' st' m' md vars'`
  \\ qmatch_assum_abbrev_tac`memory_rel c be refs sp' st' m'' md vars'`
  \\ `m' = m''` suffices_by simp[]
  \\ simp[Abbr`m'`,Abbr`m''`,FUN_EQ_THM,APPLY_UPDATE_THM]
  \\ rw[] \\ fs[]
  \\ fs [addressTheory.WORD_EQ_ADD_CANCEL]
  \\ pop_assum mp_tac \\ EVAL_TAC \\ fs [dimword_def]
  \\ pop_assum mp_tac \\ EVAL_TAC \\ fs [dimword_def]
QED

val Num_ABS_AND = prove(
  ``Num (ABS (& n)) = n /\ Num (ABS (- & n)) = n``,
  intLib.COOPER_TAC);

Theorem evaluate_WriteWord64_on_32_num:
   memory_rel c be refs sp t.store t.memory t.mdomain
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
     memory_rel c be refs (sp-3) (t.store |+ (NextFree, nf)) m' t.mdomain
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
  \\ qmatch_abbrev_tac`memory_rel c be refs sp' st' m' md vars'`
  \\ qmatch_assum_abbrev_tac`memory_rel c be refs sp' st' m'' md vars'`
  \\ `m' = m''` suffices_by simp[]
  \\ simp[Abbr`m'`,Abbr`m''`,FUN_EQ_THM,APPLY_UPDATE_THM]
  \\ rw[] \\ fs[]
  \\ fs [addressTheory.WORD_EQ_ADD_CANCEL]
  \\ pop_assum mp_tac \\ EVAL_TAC
  \\ fs [dimword_def]
  \\ rfs [bytes_in_word_def,dimword_def]
QED

Theorem evaluate_WriteWord32_bignum:
   memory_rel c be refs sp t.store t.memory t.mdomain
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
     memory_rel c be refs (sp-2) (t.store |+ (NextFree, nf)) m' t.mdomain
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
  \\ qmatch_abbrev_tac`memory_rel c be refs sp' st' m' md vars'`
  \\ qmatch_assum_abbrev_tac`memory_rel c be refs sp' st' m'' md vars'`
  \\ `m' = m''` suffices_by simp[]
  \\ simp[Abbr`m'`,Abbr`m''`,FUN_EQ_THM,APPLY_UPDATE_THM]
  \\ rw[] \\ fs[]
  \\ fs [addressTheory.WORD_EQ_ADD_CANCEL]
  \\ pop_assum mp_tac \\ EVAL_TAC
  \\ fs [dimword_def]
QED

Theorem evaluate_WriteWord64_bignum:
   memory_rel c be refs sp t.store t.memory t.mdomain
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
     memory_rel c be refs (sp-2) (t.store |+ (NextFree, nf)) m' t.mdomain
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
  \\ qmatch_abbrev_tac`memory_rel c be refs sp' st' m' md vars'`
  \\ qmatch_assum_abbrev_tac`memory_rel c be refs sp' st' m'' md vars'`
  \\ `m' = m''` suffices_by simp[]
  \\ simp[Abbr`m'`,Abbr`m''`,FUN_EQ_THM,APPLY_UPDATE_THM]
  \\ rw[] \\ fs[]
  \\ fs [addressTheory.WORD_EQ_ADD_CANCEL]
  \\ pop_assum mp_tac \\ EVAL_TAC
  \\ fs [dimword_def]
QED

Theorem evaluate_LoadBignum:
   memory_rel c be refs sp t.store t.memory t.mdomain ((Number i,v)::vars) ∧
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
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ simp[lookup_insert]
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
     (q = SOME NotEnoughSpace ==> r.ffi = t.ffi) /\
     (q <> SOME NotEnoughSpace ==>
     state_rel c l1 l2 (set_var dest v s2) r [] locs /\ q = NONE)``;

val evaluate_Assign =
  SIMP_CONV(srw_ss())[wordSemTheory.evaluate_def]``evaluate (Assign _ _, _)``

Theorem cut_env_adjust_set_insert_1:
   cut_env (adjust_set x) (insert 1 w l) =
    cut_env (adjust_set x) l
Proof
  fs [wordSemTheory.cut_env_def] \\ rw []
  \\ fs [lookup_inter_alt,lookup_insert]
  \\ rw [] \\ fs [SUBSET_DEF]
  \\ res_tac \\ fs [NOT_1_domain]
QED

Theorem cut_env_adjust_set_insert_3:
   cut_env (adjust_set x) (insert 3 w l) =
    cut_env (adjust_set x) l
Proof
  fs [wordSemTheory.cut_env_def] \\ rw []
  \\ fs [lookup_inter_alt,lookup_insert]
  \\ rw [] \\ fs [SUBSET_DEF]
  \\ res_tac \\ fs [NOT_3_domain]
QED

Theorem cut_env_adjust_set_insert_5:
   cut_env (adjust_set x) (insert 5 w l) =
    cut_env (adjust_set x) l
Proof
  fs [wordSemTheory.cut_env_def] \\ rw []
  \\ fs [lookup_inter_alt,lookup_insert]
  \\ rw [] \\ fs [SUBSET_DEF]
  \\ res_tac \\ fs [NOT_5_domain]
QED

Theorem word_bit_test_0:
   (1w && w) = 0w <=> ~word_bit 0 w
Proof
  fs [word_bit_test]
QED

val MAP_Number_11_w2n_word8 = prove(
  ``!ns ns'.
      MAP (Number ∘ $& ∘ w2n) ns = MAP (Number ∘ $& ∘ w2n) ns' <=>
      ns = ns':word8 list``,
  Induct \\ Cases_on `ns'` \\ fs []);

val MAP_Word64_11 = prove(
  ``!ns ns'.
      MAP (Word64) ns = MAP (Word64) ns' <=>
      ns = ns'``,
  Induct \\ Cases_on `ns'` \\ fs []);

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
   !(t:('a,'c,'ffi) wordSem$state) c hv1 v1 q1 a1 a2 ret_val bptr s1 vars sp refs.
      memory_rel c t.be refs sp t.store t.memory t.mdomain
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
      evaluate (InstallCode_code c,t) =
      case
        evaluate (InstallData_code c,t with <|
         locals := fromList2 [ret_val; bptr; a2;
           Word (t.code_buffer.position +
                 n2w (LENGTH t.code_buffer.buffer + LENGTH q1))];
         clock := t.clock - LENGTH q1 - 1;
         code_buffer := t.code_buffer with
           <| buffer := t.code_buffer.buffer ++ q1 ;
              space_left := t.code_buffer.space_left - LENGTH q1 |> |>) of
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
  \\ disch_then kall_tac
  \\ fs [ADD1,GSYM word_add_n2w]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ CASE_TAC \\ fs []
  \\ Cases_on `q` \\ fs []
QED

val w2w_upper_def = Define `
  w2w_upper (w:word64) =
    if dimindex (:'a) = 32 then ((63 >< 32) w):'a word else w2w w`

Theorem InstallData_code_thm:
   !(t:('a,'c,'ffi) wordSem$state) c hv2 v1 q2 a1 a2 ret_val s1 vars sp refs.
      memory_rel c t.be refs sp t.store t.memory t.mdomain
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
                  space_left := t.data_buffer.space_left - LENGTH q2 |> |>) of
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
  \\ disch_then kall_tac
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

val MAP_FST_MAP_compile_part = prove(
  ``!full_list. MAP FST (MAP (compile_part c) full_list) = MAP FST full_list``,
  Induct \\ fs [FORALL_PROD,compile_part_def]);

val memory_rel_ignore_buffers = prove(
  ``memory_rel c be refs sp (st |+ (BitmapBuffer,x)) m dm vars =
    memory_rel c be refs sp st m dm vars /\
    memory_rel c be refs sp (st |+ (CodeBuffer,x)) m dm vars =
    memory_rel c be refs sp st m dm vars``,
  fs [memory_rel_def,heap_in_memory_store_def,FLOOKUP_UPDATE]);

val compile_part_loc_IMP = prove(
  ``compile_part c (a1,a2) = (n,x) ==> n = a1``,
  PairCases_on `a2` \\ fs [compile_part_def]);

Theorem assign_Install:
   (op = Install) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs [assign_def] \\ rw []
  \\ fs [do_app,REWRITE_RULE [METIS_PROVE [] ``~b\/c<=>(b==>c)``]
           do_install_def,UNCURRY]
  \\ every_case_tac \\ fs [] \\ rveq \\ fs [] \\ clean_tac
  \\ rename1 `get_vars [v1;v2;v3;v4] _ =
        SOME [hv1;hv2; Number (&LENGTH q1); Number (&LENGTH q2)]`
  \\ fs [dataLangTheory.op_requires_names_def,
         dataLangTheory.op_space_reset_def,cut_state_opt_def]
  \\ Cases_on `names_opt` \\ fs []
  \\ rpt_drule0 state_rel_get_vars_IMP \\ strip_tac \\ fs []
  \\ fs [cut_state_opt_def,cut_state_def]
  \\ rename1 `state_rel c l1 l2 s1 t [] locs`
  \\ Cases_on `dataSem$cut_env x' s.locals` \\ fs []
  \\ clean_tac \\ fs []
  \\ qabbrev_tac `s1 = s with locals := x`
  \\ `?y. cut_env (adjust_set x') t.locals = SOME y` by
       (match_mp_tac (GEN_ALL cut_env_IMP_cut_env) \\ fs []
        \\ metis_tac []) \\ fs []
  \\ fs [LENGTH_EQ_4] \\ rveq
  \\ qpat_assum `state_rel c l1 l2 s1 t [] locs` mp_tac
  \\ simp_tac std_ss [Once state_rel_thm] \\ strip_tac \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ qpat_x_assum `get_vars _ x = _` mp_tac
  \\ `x = s1.locals` by fs [Abbr`s1`]
  \\ pop_assum (fn th => rewrite_tac [th]) \\ strip_tac
  \\ rpt_drule0 memory_rel_lookup_var_IMP \\ strip_tac
  \\ fs [code_oracle_rel_def]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ `?w3 w4. get_var (adjust_var v4) t = SOME (Word w4) /\
              get_var (adjust_var v3) t = SOME (Word w3)` by
   (drule memory_rel_tl \\ strip_tac
    \\ drule memory_rel_tl \\ strip_tac
    \\ drule memory_rel_tl \\ strip_tac
    \\ imp_res_tac memory_rel_any_Number_IMP \\ fs [get_vars_SOME_IFF])
  \\ rpt_drule0 evaluate_BignumHalt
  \\ strip_tac \\ fs [] \\ IF_CASES_TAC \\ fs []
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ qpat_x_assum `_ = SOME (Word w4)` assume_tac
  \\ rpt_drule0 evaluate_BignumHalt
  \\ strip_tac \\ fs [] \\ IF_CASES_TAC \\ fs []
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
         wordSemTheory.find_code_def,wordSemTheory.set_var_def]
  \\ fs [wordSemTheory.add_ret_loc_def,wordSemTheory.find_code_def]
  \\ fs [wordSemTheory.bad_dest_args_def,wordSemTheory.get_vars_def,
         wordSemTheory.get_var_def,lookup_insert,data_to_wordTheory.get_names_def,
         cut_env_adjust_set_insert_1,
         cut_env_adjust_set_insert_3,
         cut_env_adjust_set_insert_5]
  \\ fs [wordSemTheory.evaluate_def,wordSemTheory.call_env_def,
         wordSemTheory.push_env_def,wordSemTheory.dec_clock_def]
  \\ Cases_on `env_to_list y t.permute` \\ fs []
  \\ qmatch_goalsub_abbrev_tac `InstallCode_code c, t88`
  \\ qspec_then `t88` mp_tac InstallCode_code_thm
  \\ qunabbrev_tac `t88` \\ fs [wordSemTheory.get_var_def,
       lookup_insert,fromList2_def]
  \\ disch_then drule \\ fs []
  \\ disch_then (fn th => simp [th])
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
  \\ disch_then (fn th => simp [th])
  \\ simp [Install_code_def,Once list_Seq_def,wordSemTheory.evaluate_def]
  \\ eval_tac
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac \\ fs [lookup_insert]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac \\ fs [lookup_insert]
  \\ fs [wordSemTheory.set_store_def]
  (* Install *)
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ `s1.compile = s.compile` by fs [Abbr `s1`]
  \\ `s1.compile_oracle = s.compile_oracle` by fs [Abbr `s1`]
  \\ Cases_on `s.compile_oracle 0`
  \\ fs [lookup_insert,wordSemTheory.get_var_def,wordSemTheory.cut_env_def,
         wordSemTheory.buffer_flush_def,bytes_in_word_def]
  \\ PairCases_on `z` \\ fs []
  \\ qmatch_goalsub_rename_tac `compile_part c (ar1,ar2)`
  \\ Cases_on `compile_part c (ar1,ar2)` \\ fs [w2w_upper_upper_w2w]
  \\ rveq \\ fs []
  \\ reverse IF_CASES_TAC
  THEN1 (sg `F` \\ fs [] \\ fs [shift_seq_def])
  \\ fs [inter_insert]
  \\ fs [list_Seq_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_def,
         lookup_insert,wordSemTheory.call_env_def,wordSemTheory.pop_env_def]
  \\ reverse IF_CASES_TAC
  THEN1
   (sg `F` \\ fs []
    \\ drule env_to_list_lookup_equiv
    \\ fs [EXTENSION,domain_lookup,lookup_fromAList]
    \\ fs[GSYM IS_SOME_EXISTS]
    \\ CCONTR_TAC \\ fs [])
  \\ fs []
  \\ fs [state_rel_thm,lookup_insert,adjust_var_11]
  \\ rpt strip_tac
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
    \\ qunabbrev_tac `s1` \\ fs []
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
  THEN1
   (drule env_to_list_lookup_equiv
    \\ fs [EXTENSION,domain_lookup,lookup_fromAList]
    \\ strip_tac \\ fs [lookup_inter,lookup_0_adjust_set])
  THEN1
   (rw [] \\ fs [dataSemTheory.cut_env_def]
    \\ drule env_to_list_lookup_equiv
    \\ fs [EXTENSION,domain_lookup,lookup_fromAList]
    \\ strip_tac \\ fs [lookup_inter]
    \\ fs [lookup_adjust_var_adjust_set]
    \\ rveq \\ fs [Abbr `s1`]
    \\ fs [lookup_inter]
    \\ Cases_on `lookup n s.locals` \\ fs []
    \\ Cases_on `lookup n x'` \\ fs []
    \\ `IS_SOME (lookup n s.locals)` by fs []
    \\ res_tac \\ CASE_TAC \\ fs [])
  \\ fs [FAPPLY_FUPDATE_THM,memory_rel_ignore_buffers]
  \\ imp_res_tac compile_part_loc_IMP \\ fs [] \\ rveq \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs [inter_insert_ODD_adjust_set_alt]
  \\ match_mp_tac memory_rel_CodePtr
  \\ drule env_to_list_lookup_equiv \\ strip_tac
  \\ qunabbrev_tac `s1` \\ fs []
  \\ qsuff_tac `inter (fromAList q) (adjust_set x) =
                inter t.locals (adjust_set x)`
  THEN1 asm_simp_tac std_ss []
  \\ fs [lookup_inter_alt,lookup_fromAList]
  \\ rw [] \\ fs [cut_env_def] \\ rveq \\ fs []
  \\ fs [domain_inter,adjust_set_inter]
QED

Theorem LENGTH_EQ_5:
   (LENGTH xs = 5 <=> ?a1 a2 a3 a4 a5. xs = [a1;a2;a3;a4;a5]) /\
    (5 = LENGTH xs <=> ?a1 a2 a3 a4 a5. xs = [a1;a2;a3;a4;a5])
Proof
  Cases_on `xs` \\ fs []
  \\ rpt (Cases_on `t` \\ fs [] ORELSE Cases_on `t'` \\ fs [])
QED

Theorem memory_rel_get_num:
   memory_rel c be refs sp st m dm vars /\
    n < dimword (:'a) DIV 8 /\ good_dimindex (:'a) /\
    MEM (Number (&n),a:'a word_loc) vars ==>
    ?w. a = Word w /\ w >>> 2 = n2w n
Proof
  rw []
  \\ `memory_rel c be refs sp st m dm [Number (&n),a]` by
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

Theorem ZERO_IN_adjust_set:
   0 ∈ domain (adjust_set the_names)
Proof
  fs [domain_lookup,lookup_adjust_set]
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

val word_exp_set = Q.prove(`
  (word_exp s (Op Add [Var n; Const c]) =
  case get_var n s of
    SOME (Word w) => SOME (Word (w+c))
  | _ => NONE) ∧
  (word_exp s (Op Sub [Var n; Const c]) =
  case get_var n s of
    SOME (Word w) => SOME (Word (w-c))
  | _ => NONE)`,
  EVAL_TAC>>rw[]>>
  every_case_tac>>rw[]>>
  fs[]);

val good_dimindex_w2w_byte = Q.prove(`
  good_dimindex (:'a) ⇒
  w2w (w2w (w:word8):'a word) = w`,
  rw[good_dimindex_def]>>
  simp[w2w_w2w]>>
  match_mp_tac WORD_ALL_BITS>>fs[]);

val set_var_consts = Q.prove(`
  (set_var r v s).memory = s.memory ∧
  (set_var r v s).mdomain = s.mdomain ∧
  (set_var r v s).be = s.be ∧
  (set_var r v s).code = s.code`,
  fs[wordSemTheory.set_var_def]);

val get_var_consts = Q.prove(`
  get_var r (s with memory:=m) = get_var r s`,
  EVAL_TAC>>rw[]);

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
        (SOME (Result (Loc l1 l2) ret_val),
         s with <| clock := s.clock - w2n n DIV 4 ;
                   memory := m1 ; locals := LN |>)
Proof
  ho_match_mp_tac word_copy_fwd_ind >>
  rw[]>>
  qpat_x_assum`A=SOME m1` mp_tac>>
  simp[Once word_copy_fwd_def]>>
  rpt (IF_CASES_TAC)>>rw[]
  >-
    (fs[ByteCopyAdd_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def]>>
    EVAL_TAC>>fs[wordSemTheory.state_component_equality])
  >-
    (imp_res_tac get_var_to_word_exp>>
    fs[ByteCopyAdd_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,list_Seq_def,wordSemTheory.inst_def]>>
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
      fs[ByteCopyAdd_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,list_Seq_def,wordSemTheory.inst_def]>>
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
      fs[ByteCopyAdd_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,list_Seq_def,wordSemTheory.inst_def]>>
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
    simp[ByteCopyAdd_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,list_Seq_def,wordSemTheory.inst_def]>>
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
        (SOME (Result (Loc l1 l2) ret_val),
         s with <| clock := s.clock - w2n n DIV 4 ;
                   memory := m1 ; locals := LN |>)
Proof
  ho_match_mp_tac word_copy_bwd_ind >>
  rw[]>>
  qpat_x_assum`A=SOME m1` mp_tac>>
  simp[Once word_copy_bwd_def]>>
  rpt (IF_CASES_TAC)>>rw[]
  >-
    (fs[ByteCopySub_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def]>>
    EVAL_TAC>>fs[wordSemTheory.state_component_equality])
  >-
    (imp_res_tac get_var_to_word_exp>>
    fs[ByteCopySub_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,list_Seq_def,wordSemTheory.inst_def]>>
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
      fs[ByteCopySub_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,list_Seq_def,wordSemTheory.inst_def]>>
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
      fs[ByteCopySub_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,list_Seq_def,wordSemTheory.inst_def]>>
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

val not_less_zero_int_eq = prove(
  ``~(i < 0:int) <=> ?n. i = &n``,
  Cases_on `i` \\ fs []);

Theorem assign_WordFromWord:
   (?b. op = WordFromWord b) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac state_rel_cut_IMP \\ pop_assum mp_tac
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ Cases_on `b`
  THEN1
   (fs[do_app,case_eq_thms]
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
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert
    \\ fs []
    \\ qmatch_goalsub_abbrev_tac`Number i,Word sn`
    \\ qsuff_tac `sn = Smallnum i /\ small_int (:'a) i`
    \\ TRY (rw [] \\ fs []
            \\ match_mp_tac IMP_memory_rel_Number  \\ fs [good_dimindex_def])
    \\ unabbrev_all_tac
    \\ fs [small_int_def,dimword_def,w2w_def,Smallnum_def]
    \\ Cases_on `c'` \\ fs [word_extract_n2w]
    \\ rewrite_tac [LSL_BITWISE]
    \\ rewrite_tac [WORD_AND_EXP_SUB1 |> Q.SPEC `8` |> SIMP_RULE (srw_ss()) []]
    \\ fs [WORD_MUL_LSL,word_mul_n2w,dimword_def]
    \\ fs [bitTheory.BITS_THM]
    \\ rw [] \\ TRY (match_mp_tac LESS_TRANS \\ qexists_tac `256` \\ fs [])
    \\ rewrite_tac [GSYM (EVAL ``256n * 16777216``)]
    \\ rewrite_tac [MATCH_MP MOD_MULT_MOD (DECIDE ``0 < 256n /\ 0 < 16777216n``)])
  \\ fs[do_app,case_eq_thms]
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
  \\ qpat_abbrev_tac `ww = _ >>> 2`
  \\ `ww = n2w (w2n w)` by
   (unabbrev_all_tac
    \\ once_rewrite_tac [GSYM w2n_11]
    \\ rewrite_tac [w2n_lsr]
    \\ Cases_on `w` \\ fs [dimword_def]
    \\ once_rewrite_tac [MULT_COMM] \\ fs [MULT_DIV])
  \\ rveq \\ fs []
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
    \\ fs [FAPPLY_FUPDATE_THM])
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
    \\ fs [FAPPLY_FUPDATE_THM,w2w_def]
    \\ Cases_on `w` \\ fs [] \\ rfs [dimword_def] \\ fs []
    \\ match_mp_tac (GEN_ALL memory_rel_less_space)
    \\ qexists_tac`x.space - 2` \\ fs[])
QED

Theorem assign_CopyByte:
   (?new_flag. op = CopyByte new_flag /\ ¬ new_flag) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [assign_def] \\ rw []
  \\ fs [do_app]
  \\ `?src srcoff le dst dstoff. vals =
             [RefPtr src; Number srcoff; Number le; RefPtr dst;
              Number dstoff]` by
   (Cases_on `vals` \\ fs []
    \\ rename1 `LENGTH args = SUC (LENGTH rest)` \\ Cases_on `rest` \\ fs []
    \\ rename1 `_ = SUC(SUC (LENGTH rest))` \\ Cases_on `rest` \\ fs []
    \\ rename1 `_ = SUC(SUC(SUC (LENGTH rest)))` \\ Cases_on `rest` \\ fs []
    \\ rename1 `_ = SUC(SUC(SUC(SUC (LENGTH rest))))`
    \\ Cases_on `rest` \\ fs []
    \\ rename1 `_ = SUC(SUC(SUC(SUC(SUC (LENGTH rest)))))`
    \\ Cases_on `rest` \\ fs []
    \\ rename1 `_ = SOME (h1::h2::h3::h4::h5::_)`
    \\ Cases_on `h5` \\ fs []
    \\ Cases_on `h4` \\ fs []
    \\ Cases_on `h3` \\ fs []
    \\ Cases_on `h2` \\ fs []
    \\ Cases_on `h1` \\ fs [])
  \\ fs [] \\ every_case_tac \\ fs [] \\ rveq
  \\ rename1 `FLOOKUP x.refs dst = SOME (ByteArray ys_fl ys)`
  \\ rename1 `FLOOKUP x.refs src = SOME (ByteArray xs_fl xs)`
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
  \\ clean_tac \\ fs []
  \\ qabbrev_tac `s1 = s with locals := x`
  \\ `?y. cut_env (adjust_set x'') t.locals = SOME y` by
       (match_mp_tac (GEN_ALL cut_env_IMP_cut_env) \\ fs []
        \\ metis_tac []) \\ fs []
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
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ disch_then kall_tac
  \\ qunabbrev_tac `t7` \\ fs [eq_eval]
  \\ qmatch_goalsub_abbrev_tac `wordSem$evaluate (_,t7)`
  \\ `get_var 8 t7 = SOME (Word wa2)` by
      (unabbrev_all_tac \\ fs [wordSemTheory.get_var_def,lookup_insert])
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ `t7.store = t.store` by (unabbrev_all_tac \\ fs [push_env_store])
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
      \\ drule0 memory_rel_RefPtr_EQ \\ fs [])
    \\ fs [] \\ rveq
    \\ `memory_rel c t.be s1.refs s1.space t.store t.memory t.mdomain
         ((RefPtr dst,Word wa1)::
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
      \\ fs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def]
      \\ Cases_on `env_to_list y t.permute` \\ fs []
      \\ `domain (fromAList q) = domain y` by
          (drule0 env_to_list_lookup_equiv
           \\ fs [EXTENSION,domain_lookup,lookup_fromAList]) \\ fs []
      \\ fs [state_rel_thm,lookup_insert,lookup_fromAList,adjust_var_11]
      \\ drule0 env_to_list_lookup_equiv \\ fs [] \\ strip_tac
      \\ conj_tac THEN1
       (drule0 env_to_list_lookup_equiv
        \\ fs [lookup_insert,lookup_fromAList]
        \\ fs [wordSemTheory.cut_env_def] \\ rveq
        \\ pop_assum imp_res_tac
        \\ fs [cut_state_def,cut_env_def] \\ rveq
        \\ simp [lookup_inter_alt,ZERO_IN_adjust_set])
      \\ conj_tac THEN1
        (drule0 env_to_list_lookup_equiv
         \\ fs [lookup_insert,lookup_fromAList,adjust_var_11]
         \\ rw [] \\ rw [] \\ fs [] \\ unabbrev_all_tac \\ fs []
         \\ fs [wordSemTheory.cut_env_def] \\ rveq
         \\ qpat_x_assum `!x._` imp_res_tac
         \\ fs [cut_state_def,cut_env_def] \\ rveq
         \\ Cases_on `domain x'' ⊆ domain s.locals` \\ fs [] \\ rveq
         \\ fs [] \\ fs [lookup_inter_alt,adjust_var_IN_adjust_set]
         \\ rw [] \\ fs [])
      \\ simp [FAPPLY_FUPDATE_THM]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ match_mp_tac memory_rel_Unit
      \\ drule0 memory_rel_tl \\ fs []
      \\ match_mp_tac quotientTheory.EQ_IMPLIES
      \\ AP_TERM_TAC \\ fs []
      \\ fs [wordSemTheory.cut_env_def] \\ rveq
      \\ qpat_x_assum `!x._` imp_res_tac
      \\ fs [cut_state_def,cut_env_def] \\ rveq
      \\ Cases_on `domain x'' ⊆ domain s.locals` \\ fs [] \\ rveq \\ fs []
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
      \\ fs [lookup_inter_alt] \\ rw []
      \\ sg `F` \\ fs [] \\ pop_assum mp_tac \\ simp []
      \\ unabbrev_all_tac \\ fs [IN_domain_adjust_set_inter])
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
      \\ Cases_on `env_to_list y t.permute` \\ fs []
      \\ `domain (fromAList q) = domain y` by
          (drule0 env_to_list_lookup_equiv
           \\ fs [EXTENSION,domain_lookup,lookup_fromAList]) \\ fs []
      \\ fs [state_rel_thm,lookup_insert,lookup_fromAList,adjust_var_11]
      \\ drule0 env_to_list_lookup_equiv \\ fs [] \\ strip_tac
      \\ conj_tac THEN1
       (drule0 env_to_list_lookup_equiv
        \\ fs [lookup_insert,lookup_fromAList]
        \\ fs [wordSemTheory.cut_env_def] \\ rveq
        \\ qpat_x_assum `!x._` imp_res_tac
        \\ fs [cut_state_def,cut_env_def] \\ rveq
        \\ simp [lookup_inter_alt,ZERO_IN_adjust_set])
      \\ conj_tac THEN1
        (drule0 env_to_list_lookup_equiv
         \\ fs [lookup_insert,lookup_fromAList,adjust_var_11]
         \\ rw [] \\ rw [] \\ fs [] \\ unabbrev_all_tac \\ fs []
         \\ fs [wordSemTheory.cut_env_def] \\ rveq
         \\ qpat_x_assum `!x._` imp_res_tac
         \\ fs [cut_state_def,cut_env_def] \\ rveq
         \\ Cases_on `domain x'' ⊆ domain s.locals` \\ fs [] \\ rveq
         \\ fs [] \\ fs [lookup_inter_alt,adjust_var_IN_adjust_set]
         \\ rw [] \\ fs [])
      \\ simp [FAPPLY_FUPDATE_THM]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ match_mp_tac memory_rel_Unit
      \\ drule0 memory_rel_tl \\ fs []
      \\ match_mp_tac quotientTheory.EQ_IMPLIES
      \\ AP_TERM_TAC \\ fs []
      \\ fs [wordSemTheory.cut_env_def] \\ rveq
      \\ qpat_x_assum `!x._` imp_res_tac
      \\ fs [cut_state_def,cut_env_def] \\ rveq
      \\ Cases_on `domain x'' ⊆ domain s.locals` \\ fs [] \\ rveq \\ fs []
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
      \\ fs [lookup_inter_alt] \\ rw []
      \\ sg `F` \\ fs [] \\ pop_assum mp_tac \\ simp []
      \\ unabbrev_all_tac \\ fs [IN_domain_adjust_set_inter]))
  THEN1
   (`memory_rel c t.be s1.refs s1.space t.store t.memory t.mdomain
         ((RefPtr src,Word wa1)::(RefPtr dst,Word wa2)::
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
      \\ fs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def]
      \\ Cases_on `env_to_list y t.permute` \\ fs []
      \\ `domain (fromAList q) = domain y` by
          (drule0 env_to_list_lookup_equiv
           \\ fs [EXTENSION,domain_lookup,lookup_fromAList]) \\ fs []
      \\ fs [state_rel_thm,lookup_insert,lookup_fromAList,adjust_var_11]
      \\ drule0 env_to_list_lookup_equiv \\ fs [] \\ strip_tac
      \\ conj_tac THEN1
       (drule0 env_to_list_lookup_equiv
        \\ fs [lookup_insert,lookup_fromAList]
        \\ fs [wordSemTheory.cut_env_def] \\ rveq
        \\ qpat_x_assum `!x._` imp_res_tac
        \\ fs [cut_state_def,cut_env_def] \\ rveq
        \\ simp [lookup_inter_alt,ZERO_IN_adjust_set])
      \\ conj_tac THEN1
        (drule0 env_to_list_lookup_equiv
         \\ fs [lookup_insert,lookup_fromAList,adjust_var_11]
         \\ rw [] \\ rw [] \\ fs [] \\ unabbrev_all_tac \\ fs []
         \\ fs [wordSemTheory.cut_env_def] \\ rveq
         \\ qpat_x_assum `!x._` imp_res_tac
         \\ fs [cut_state_def,cut_env_def] \\ rveq
         \\ Cases_on `domain x'' ⊆ domain s.locals` \\ fs [] \\ rveq
         \\ fs [] \\ fs [lookup_inter_alt,adjust_var_IN_adjust_set]
         \\ rw [] \\ fs [])
      \\ simp [FAPPLY_FUPDATE_THM]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ match_mp_tac memory_rel_Unit
      \\ drule0 memory_rel_tl \\ fs [] \\ strip_tac
      \\ drule0 memory_rel_tl \\ fs [] \\ pop_assum kall_tac
      \\ match_mp_tac quotientTheory.EQ_IMPLIES
      \\ AP_TERM_TAC \\ fs []
      \\ fs [wordSemTheory.cut_env_def] \\ rveq
      \\ qpat_x_assum `!x._` imp_res_tac
      \\ fs [cut_state_def,cut_env_def] \\ rveq
      \\ Cases_on `domain x'' ⊆ domain s.locals` \\ fs [] \\ rveq \\ fs []
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
      \\ fs [lookup_inter_alt] \\ rw []
      \\ sg `F` \\ fs [] \\ pop_assum mp_tac \\ simp []
      \\ unabbrev_all_tac \\ fs [IN_domain_adjust_set_inter])
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
      \\ Cases_on `env_to_list y t.permute` \\ fs []
      \\ `domain (fromAList q) = domain y` by
          (drule0 env_to_list_lookup_equiv
           \\ fs [EXTENSION,domain_lookup,lookup_fromAList]) \\ fs []
      \\ fs [state_rel_thm,lookup_insert,lookup_fromAList,adjust_var_11]
      \\ drule0 env_to_list_lookup_equiv \\ fs [] \\ strip_tac
      \\ conj_tac THEN1
       (drule0 env_to_list_lookup_equiv
        \\ fs [lookup_insert,lookup_fromAList]
        \\ fs [wordSemTheory.cut_env_def] \\ rveq
        \\ qpat_x_assum `!x._` imp_res_tac
        \\ fs [cut_state_def,cut_env_def] \\ rveq
        \\ simp [lookup_inter_alt,ZERO_IN_adjust_set])
      \\ conj_tac THEN1
        (drule0 env_to_list_lookup_equiv
         \\ fs [lookup_insert,lookup_fromAList,adjust_var_11]
         \\ rw [] \\ rw [] \\ fs [] \\ unabbrev_all_tac \\ fs []
         \\ fs [wordSemTheory.cut_env_def] \\ rveq
         \\ qpat_x_assum `!x._` imp_res_tac
         \\ fs [cut_state_def,cut_env_def] \\ rveq
         \\ Cases_on `domain x'' ⊆ domain s.locals` \\ fs [] \\ rveq
         \\ fs [] \\ fs [lookup_inter_alt,adjust_var_IN_adjust_set]
         \\ rw [] \\ fs [])
      \\ simp [FAPPLY_FUPDATE_THM]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ match_mp_tac memory_rel_Unit
      \\ drule0 memory_rel_tl \\ fs [] \\ strip_tac
      \\ drule0 memory_rel_tl \\ fs [] \\ pop_assum kall_tac
      \\ match_mp_tac quotientTheory.EQ_IMPLIES
      \\ AP_TERM_TAC \\ fs []
      \\ fs [wordSemTheory.cut_env_def] \\ rveq
      \\ qpat_x_assum `!x._` imp_res_tac
      \\ fs [cut_state_def,cut_env_def] \\ rveq
      \\ Cases_on `domain x'' ⊆ domain s.locals` \\ fs [] \\ rveq \\ fs []
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
      \\ fs [lookup_inter_alt] \\ rw []
      \\ sg `F` \\ fs [] \\ pop_assum mp_tac \\ simp []
      \\ unabbrev_all_tac \\ fs [IN_domain_adjust_set_inter]))
QED

(* This equality captures all the information that is preserved
   after `v_to_list` *)
val eq_upto_ts_def = tDefine"eq_upto_ts"`
  eq_upto_ts (Block _ tag1 []) (Block _ tag2 []) = (tag1 = tag2)
∧ eq_upto_ts (Block _ tag1 (x1::xs1)) (Block _ tag2 (x2::xs2)) =
    (tag1 = tag2 ∧ x1 = x2 ∧ EVERY2 eq_upto_ts xs1 xs2)
∧ eq_upto_ts x y = (x = y)`
(wf_rel_tac `measure (\ (x,y). v_size x + v_size y)`
\\ rw [v1_size_map]
\\ ho_match_mp_tac LESS_TRANS
\\ Q.EXISTS_TAC `SUM (MAP v_size xs1) + SUM (MAP v_size xs2) + 1`
\\ fs [Once MEM_SPLIT_APPEND_first,SUM_APPEND])
;

val _ = Parse.add_infix("≅ts",425,Parse.NONASSOC);
val _ = Parse.overload_on("≅ts",``eq_upto_ts``);

Theorem eq_imp_upto_ts:
   ∀x y. x = y ⇒  x ≅ts y
Proof
  ho_match_mp_tac (theorem "eq_upto_ts_ind")
  \\ rw [eq_upto_ts_def]
  \\ Induct_on `xs1` \\ rw [eq_upto_ts_def]
QED

Theorem eq_upto_ts_refl:
   ∀v. v ≅ts v
Proof
  Induct
  \\ rw [eq_upto_ts_def]
  \\ Induct_on `l` \\ rw [eq_upto_ts_def,eq_imp_upto_ts]
  \\ Induct_on `l` \\ rw [eq_upto_ts_def,eq_imp_upto_ts]
QED

Theorem v_to_list_IFF_list_to_v:
   !r2 in2. v_to_list r2 = SOME in2 <=> ?r3. r3 = list_to_v in2 /\ r2 ≅ts r3
Proof
  recInduct v_to_list_ind
  \\ rw [] \\ fs [v_to_list_def,list_to_v_def,eq_upto_ts_def]
  \\ TRY (eq_tac \\ rw [list_to_v_def,eq_upto_ts_def])
  \\ fs [v_to_list_def,list_to_v_def,eq_upto_ts_def]
  \\ fs [case_eq_thms] \\ rveq \\ fs []
  \\ rveq \\ fs [list_to_v_def,eq_upto_ts_def,eq_upto_ts_refl]
  \\ Cases_on `in2` \\ fs [list_to_v_def,eq_upto_ts_def,eq_upto_ts_refl]
QED

Theorem v_to_list_SOME_NIL_IFF:
   !v. v_to_list v = SOME [] <=> ?ts. v = Block ts nil_tag []
Proof
  recInduct v_to_list_ind
  \\ rw [] \\ fs [v_to_list_def,list_to_v_def]
  \\ TRY (eq_tac \\ rw [list_to_v_def])
  \\ fs [v_to_list_def,list_to_v_def]
  \\ fs [case_eq_thms] \\ rveq \\ fs []
  \\ rveq \\ fs [list_to_v_def]
  \\ Cases_on `in2` \\ fs [list_to_v_def]
QED

Theorem v_to_list_SOME_CONS_IMP:
   v_to_list v = SOME (x::xs) ==> ?ts ys. v = Block ts cons_tag [x;ys] ∧
                                        ys ≅ts list_to_v xs
Proof
  Cases_on `v`
  \\ rw [v_to_list_IFF_list_to_v,list_to_v_def,eq_upto_ts_def]
  \\ Cases_on `l` \\ fs [v_to_list_IFF_list_to_v,list_to_v_def,eq_upto_ts_def]
QED

Theorem eq_upto_ts_list_to_v_Block:
   ∀v vl. v ≅ts list_to_v vl ⇒ ∃ts t l. v = Block ts t l
Proof
  rw [] \\ Cases_on `vl` \\ Cases_on `v` \\ fs [list_to_v_def,eq_upto_ts_def]
QED

Theorem eq_upto_ts_list_to_v_Cons:
   ∀v vl vs. v ≅ts list_to_v (vs::vl) ⇒ ∃ts t l. v = Block ts t (vs::l)
Proof
  rw [] \\ Cases_on `vl` \\ Cases_on `v` \\ fs [list_to_v_def,eq_upto_ts_def]
  \\ Cases_on `l` \\ fs [list_to_v_def,eq_upto_ts_def]
QED

Theorem v_to_list_IMP_list_to_v:
   !r2 in2. v_to_list r2 = SOME in2 ==> ?r3. r3 = list_to_v in2 ∧ r2 ≅ts r3
Proof
  fs [v_to_list_IFF_list_to_v]
QED


Theorem eq_upto_ts_get_refs:
   ∀x y. x ≅ts y ⇒ get_refs x = get_refs y
Proof
  ho_match_mp_tac (theorem "eq_upto_ts_ind")
  \\ rw [eq_upto_ts_def,get_refs_def]
  \\ rw [eq_upto_ts_def,get_refs_def]
  \\ AP_TERM_TAC
  \\ rw [MAP_EQ_EVERY2]
  >- METIS_TAC [GEN_ALL LIST_REL_LENGTH]
  \\ ntac 2 (last_x_assum mp_tac)
  \\ EVERY (map Q.SPEC_TAC [(`xs2`,`y`),(`xs1`,`x`)])
  \\ ho_match_mp_tac LIST_REL_ind
  \\ rw []
QED

Theorem eq_upto_ts_get_refs_map:
   ∀x y.
    LIST_REL (λa' a. a' ≅ts a) x y
    ⇒ MAP (λa. get_refs a) x  = MAP (λa. get_refs a) y
Proof
  Induct
  \\ rw []
  \\ rw [eq_upto_ts_get_refs]
QED

Theorem eq_upto_ts_reachable_refs:
   ∀v v' vars refs n.
    v ≅ts v' ⇒ reachable_refs (v::vars) refs n = reachable_refs (v'::vars) refs n
Proof
  ho_match_mp_tac (theorem "eq_upto_ts_ind")
  \\ rw [eq_upto_ts_def,reachable_refs_def]
  \\ EQ_TAC \\ rw []
  >- (EVERY (map Q.EXISTS_TAC [`Block v' tag1 []`,`r`]) \\ fs [get_refs_def])
  >- (EVERY (map Q.EXISTS_TAC [`x`,`r`]) \\ fs [get_refs_def])
  >- (EVERY (map Q.EXISTS_TAC [`Block v0 tag1 []`,`r`]) \\ fs [get_refs_def])
  >- (EVERY (map Q.EXISTS_TAC [`x`,`r`]) \\ fs [get_refs_def])
  >- (EVERY (map Q.EXISTS_TAC [`Block v3 tag1 (x1::xs2)`,`r`])
     \\ first_assum (mp_then Any assume_tac eq_upto_ts_get_refs_map)
     \\ fs [get_refs_def,eq_upto_ts_get_refs_map])
  >- (EVERY (map Q.EXISTS_TAC [`x`,`r`]) \\ fs [get_refs_def])
  >- (EVERY (map Q.EXISTS_TAC [`Block v2 tag1 (x1::xs1)`,`r`])
     \\ first_assum (mp_then Any assume_tac eq_upto_ts_get_refs_map)
     \\ fs [get_refs_def,eq_upto_ts_get_refs_map])
  >- (EVERY (map Q.EXISTS_TAC [`x`,`r`]) \\ fs [get_refs_def])
QED

Theorem eq_upto_ts_v_inv:
   ∀v lv c w f heap.
  v ≅ts list_to_v lv ∧ v_inv c v (w,f,heap) ⇒ v_inv c (list_to_v lv) (w,f,heap)
Proof
  `∀v v'. v ≅ts v'
   ⇒ ∀lv c w f heap. v' = list_to_v lv ∧ v_inv c v (w,f,heap)
      ⇒ v_inv c v' (w,f,heap)`
  suffices_by METIS_TAC []
  \\ ho_match_mp_tac (theorem "eq_upto_ts_ind")
  \\ rw [eq_upto_ts_def,v_inv_def]
  \\ fs [list_to_v_def]
  >- (Cases_on `lv` \\ fs [list_to_v_def])
  >- (Q.EXISTS_TAC `x'::ys` \\ rw []
     \\ pop_assum (K ALL_TAC)
     \\ Induct_on `ys`
     \\ rw [] \\ fs []
     \\ rw []
     \\ Cases_on `lv` \\ fs [list_to_v_def]
     \\ rveq \\ fs [])
  \\ Cases_on `lv` \\ fs [list_to_v_def]
QED

Theorem eq_upto_ts_mem_rel:
   ∀v vl c be refs sp m dm st l vars.
    v ≅ts (list_to_v vl) ∧ memory_rel c be refs sp st m dm ((v,l)::vars)
    ⇒ memory_rel c be refs sp st m dm ((list_to_v vl,l)::vars)
Proof
  `∀v v'. v ≅ts v'
    ⇒ ∀vl c be refs sp m dm st l vars.
       v' = list_to_v vl ∧ memory_rel c be refs sp st m dm ((v,l)::vars)
       ⇒ memory_rel c be refs sp st m dm ((v',l)::vars)`
  suffices_by METIS_TAC []
  \\ ho_match_mp_tac (theorem "eq_upto_ts_ind")
  \\ rw [eq_upto_ts_def,v_inv_def]
  \\ fs [list_to_v_def,memory_rel_def]
  \\ EVERY (map Q.EXISTS_TAC [`heap`,`limit`,`a`,`sp'`,`sp1`,`gens`])
  \\ fs [word_ml_inv_def] \\ Q.EXISTS_TAC `hs` \\ rw []
  \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def] \\ Q.EXISTS_TAC `f` \\ rw []
  \\ METIS_TAC [eq_upto_ts_def,eq_upto_ts_v_inv,eq_upto_ts_reachable_refs]
QED

val evaluate_AppendMainLoop_code = prove(
  ``!xs ww (t:('a,'c,'ffi)wordSem$state) vars ptr hdr l k frame r1 r2 next_free.
      memory_rel c t.be (s:('c,'ffi) dataSem$state).refs sp t.store t.memory t.mdomain
         ((list_to_v xs,Word ww)::vars) /\ xs <> [] /\
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
      (word_list_exists next_free (3 * LENGTH xs) * frame)
         (fun2set (t.memory,t.mdomain)) /\ LENGTH xs <= t.clock ==>
      ?m1 ws.
        evaluate (AppendMainLoop_code c,t) =
          (SOME (Result (Loc r1 r2) tmp2),
           t with <| locals := LN ;
                     store := t.store |+ (NextFree, Word (next_free +
                        bytes_in_word * n2w (3 * LENGTH xs))) ;
                     memory := m1 ;
                     clock := t.clock - (LENGTH xs - 1) |>) /\
        LENGTH ws = LENGTH xs /\
        (word_list next_free (append_writes c ptr hdr ws tmp0) * frame)
          (fun2set (m1,t.mdomain)) /\
        memory_rel c t.be s.refs sp t.store m1 t.mdomain
          (ZIP (xs,ws)++vars)``,
  strip_tac
  \\ completeInduct_on `LENGTH xs` \\ fs [PULL_FORALL]
  \\ rpt strip_tac \\ rveq \\ fs []
  \\ Cases_on `xs` \\ fs [] \\ clean_tac
  \\ once_rewrite_tac [AppendMainLoop_code_def]
  \\ fs [list_to_v_def]
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
   (fs [list_to_v_def]
    \\ rpt_drule0 memory_rel_Block_IMP
    \\ fs [SIMP_RULE (srw_ss()) [] word_and_one_eq_0_iff]
    \\ disch_then kall_tac
    \\ rewrite_tac [list_Seq_def]
    \\ fs [eq_eval,wordSemTheory.set_var_def,wordSemTheory.mem_store_def]
    \\ SEP_R_TAC \\ fs [eq_eval,wordSemTheory.set_store_def]
    \\ fs [wordSemTheory.state_component_equality]
    \\ qexists_tac `[t.memory (a + bytes_in_word)]` \\ fs []
    \\ fs [append_writes_def,word_list_def]
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
  \\ fs [list_to_v_def]
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
  \\ impl_tac THEN1
   (fs [AC STAR_COMM STAR_ASSOC]
    \\ unabbrev_all_tac \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ fs [markerTheory.Abbrev_def]
    \\ reverse conj_tac THEN1
     (qpat_x_assum `_ ≤ sp` assume_tac
      \\ fs [LESS_EQ_EXISTS]
      \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB] \\ rveq)
    \\ `memory_rel c t.be s.refs sp t.store t.memory t.mdomain
         ((list_to_v (h'::t''),Word w)::(h,t.memory (a + bytes_in_word))::vars)` by
     (first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
      \\ rw [] \\ fs [list_to_v_def])
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
  \\ IF_CASES_TAC THEN1 fs []
  \\ fs [WORD_MUL_LSL,word_mul_n2w,word_list_def,SEP_CLAUSES,
         AC STAR_COMM STAR_ASSOC]
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
  \\ fs [] \\ rw [] \\ fs []);

val STOP_def = Define `STOP x = x`;

val evaluate_AppendMainLoop_code_alt = prove(
  ``!xs ww (t:('a,'c,'ffi)wordSem$state) vars ptr hdr l k frame r1 r2 next_free.
      memory_rel c t.be (s:('c,'ffi) dataSem$state).refs sp t.store t.memory t.mdomain
         ((list_to_v xs,Word ww)::vars) /\ xs <> [] /\
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
      ?m1 ww2.
        evaluate (AppendMainLoop_code c,t) =
          (case STOP evaluate (AppendLenLoop_code c,
              t with <| locals := fromList2 [Loc r1 r2; Word ww2; Word 0w] ;
                        memory := m1 ;
                        clock := t.clock - ((sp - k) DIV 3 + 1) |>) of
           | (NONE,s) => (SOME Error, s) | res => res) /\
        memory_rel c t.be s.refs sp t.store m1 t.mdomain
          ((list_to_v (DROP ((sp - k) DIV 3) xs),Word ww2)::vars)``,
  strip_tac
  \\ completeInduct_on `LENGTH xs` \\ fs [PULL_FORALL]
  \\ rpt strip_tac \\ rveq \\ fs []
  \\ Cases_on `xs` \\ fs [] \\ clean_tac
  \\ once_rewrite_tac [AppendMainLoop_code_def]
  \\ fs [list_to_v_def]
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
    \\ qmatch_goalsub_abbrev_tac `STOP _ (_,ttt)`
    \\ qmatch_goalsub_abbrev_tac `AppendLenLoop_code c, ttt2`
    \\ `ttt2 = ttt` by
      (unabbrev_all_tac \\ fs [wordSemTheory.state_component_equality])
    \\ fs [STOP_def]
    \\ Cases_on `evaluate (AppendLenLoop_code c,ttt)` \\ fs []
    \\ Cases_on `q` \\ fs []
    \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
    \\ fs [] \\ rw [] \\ fs [list_to_v_def])
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
  THEN1
   (fs [list_to_v_def] \\ sg `F` \\ fs []
    \\ qpat_x_assum `~bbb` mp_tac \\ simp []
    \\ fs [good_dimindex_def,bytes_in_word_def,dimword_def]
    \\ rfs [WORD_LO,dimword_def,word_mul_n2w])
  \\ fs [list_to_v_def]
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
  \\ impl_tac THEN1
   (fs [AC STAR_COMM STAR_ASSOC]
    \\ unabbrev_all_tac \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ fs [markerTheory.Abbrev_def]
    \\ reverse conj_asm2_tac THEN1
     (fs [good_dimindex_def,bytes_in_word_def]
      \\ rfs [dimword_def,word_mul_n2w,WORD_LO]
      \\ rewrite_tac [GSYM word_sub_def,addressTheory.word_arith_lemma2]
      \\ fs [LEFT_SUB_DISTRIB,LEFT_ADD_DISTRIB])
    \\ `memory_rel c t.be s.refs sp t.store t.memory t.mdomain
         ((list_to_v (h'::t''),Word w)::(h,t.memory (a + bytes_in_word))::vars)` by
     (first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
      \\ rw [] \\ fs [list_to_v_def])
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
  \\ qmatch_goalsub_abbrev_tac `STOP _ ttt`
  \\ Cases_on `STOP evaluate ttt` \\ fs []
  \\ qpat_x_assum `k + 3 ≤ sp` assume_tac
  \\ `((sp − k) DIV 3) = SUC ((sp − (k + 3)) DIV 3)` by
   (pop_assum (strip_assume_tac o REWRITE_RULE [LESS_EQ_EXISTS])
    \\ fs [ADD_DIV_EQ,ADD1])
  \\ fs [DROP] \\ fs [ADD1] \\ unabbrev_all_tac \\ fs []
  \\ qexists_tac `ww2` \\ fs []
  \\ Cases_on `q` \\ fs [DROP]
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
  \\ fs [] \\ rw [] \\ fs [])
  |> SPEC_ALL |> Q.INST [`k`|->`0`]
  |> SIMP_RULE std_ss [] |> GEN_ALL;

val evaluate_AppendLenLoop_code = prove(
  ``!k (t:('a,'c,'ffi)wordSem$state) c xs l1 l2 (w:'a word) vars.
      memory_rel c t.be refs sp t.store t.memory t.mdomain
        ((list_to_v xs,Word w)::vars) /\
      lookup 0 t.locals = SOME (Loc l1 l2) /\
      lookup 2 t.locals = SOME (Word w) /\
      lookup 4 t.locals = SOME (Word (n2w (12 * k))) /\
      lookup AppendLenLoop_location t.code = SOME (3,AppendLenLoop_code c) /\
      good_dimindex (:'a) /\
      LENGTH xs <= t.clock ==>
      ?locals.
        (case evaluate (AppendLenLoop_code c, t) of
          (NONE,s) => (SOME Error,s)
        | res => res) =
        (case evaluate (AppendLenLoop_code c,
                t with <| locals := locals ;
                          clock := t.clock - LENGTH xs |>) of
          (NONE,s) => (SOME Error,s)
        | res => res) /\
        lookup 0 locals = SOME (Loc l1 l2) /\
        lookup 2 locals = SOME (Word 2w) /\
        lookup 4 locals = SOME (Word (n2w (12 * (k + LENGTH xs))))``,
  Induct_on `xs` THEN1
   (fs [] \\ rw [] \\ qexists_tac `t.locals` \\ fs []
    \\ `t with <|locals := t.locals; clock := t.clock|> = t`
          by fs [wordSemTheory.state_component_equality] \\ fs []
    \\ fs [list_to_v_def]
    \\ rpt_drule0 memory_rel_Block_IMP
    \\ EVAL_TAC \\ fs [])
  \\ rw []
  \\ simp [Once AppendLenLoop_code_def]
  \\ fs [list_to_v_def]
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
     (Cases_on `xs` \\ fs [list_to_v_def]
      \\ rpt_drule0 memory_rel_Block_IMP \\ fs [] \\ rw [] \\ fs [])
  \\ disch_then (qspecl_then [`xx`,`vars`] mp_tac)
  \\ impl_tac THEN1
   (fs [LEFT_ADD_DISTRIB,word_add_n2w]
    \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
    \\ fs [] \\ rw [] \\ fs [list_to_v_def])
  \\ strip_tac \\ fs []
  \\ fs [LEFT_ADD_DISTRIB,word_add_n2w]
  \\ rw []
  \\ qexists_tac `locals` \\ fs []
  \\ fs [LEFT_ADD_DISTRIB,word_add_n2w,ADD1]
  \\ qmatch_goalsub_abbrev_tac `(AppendLenLoop_code c,ttt)`
  \\ Cases_on `evaluate (AppendLenLoop_code c,ttt)`
  \\ Cases_on `q` \\ fs [])
  |> Q.SPEC `0` |> SIMP_RULE std_ss [] |> Q.GEN `refs`;

Theorem assign_ListAppend:
   op = ListAppend ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac state_rel_cut_IMP
  \\ fs [assign_def] \\ rveq
  \\ fs [dataLangTheory.op_requires_names_def,
         dataLangTheory.op_space_reset_def,cut_state_opt_def]
  \\ Cases_on `names_opt` \\ fs []
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app]
  \\ `?r1 r2. vals = [r1;r2]` by
     (Cases_on `vals` \\ fs [] \\ Cases_on `t'` \\ fs [] \\ Cases_on `t''` \\ fs [])
  \\ rveq \\ fs []
  \\ Cases_on `v_to_list r1` \\ fs []
  \\ Cases_on `v_to_list r2` \\ fs []
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ Cases_on `encode_header c 0 2` \\ fs []
  \\ rename1 `v_to_list r1 = SOME in1`
  \\ rename1 `v_to_list r2 = SOME in2`
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ rpt (qpat_x_assum `!x._` kall_tac)
  \\ clean_tac \\ fs [wordSemTheory.evaluate_def]
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
  \\ `?y. cut_env (adjust_set x') t.locals = SOME y` by
       (match_mp_tac (GEN_ALL cut_env_IMP_cut_env) \\ fs []
        \\ metis_tac []) \\ fs []
  \\ simp [Append_code_def]
  \\ simp [wordSemTheory.evaluate_def]
  \\ fs [asmTheory.word_cmp_def,wordSemTheory.get_var_imm_def]
  \\ simp [EVAL ``get_var 4 (call_env [Loc n l; h'; h] s)``]
  \\ simp [EVAL ``get_var 2 (call_env [Loc n l; h'; h] s)``]
  \\ simp [EVAL ``get_var 0 (call_env [Loc n l; h'; h] s)``]
  \\ Cases_on `in1` \\ fs [v_to_list_SOME_NIL_IFF]
  THEN1
   (rveq \\ fs []
    \\ qpat_x_assum `state_rel c l1 l2 s1 t [] locs` mp_tac
    \\ simp [Once state_rel_thm] \\ strip_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ drule (GEN_ALL memory_rel_get_vars_IMP)
    \\ fs [Abbr`s1`]
    \\ disch_then drule
    \\ fs [wordSemTheory.get_vars_def]
    \\ fs [SIMP_RULE (srw_ss()) [] word_and_one_eq_0_iff]
    \\ strip_tac \\ drule memory_rel_Block_IMP \\ fs []
    \\ strip_tac \\ rveq \\ fs []
    \\ simp [wordSemTheory.dec_clock_def,
             wordSemTheory.push_env_def]
    \\ Cases_on `env_to_list y t.permute` \\ fs []
    \\ simp [wordSemTheory.call_env_def,
             wordSemTheory.pop_env_def]
    \\ reverse IF_CASES_TAC THEN1
     (sg `F` \\ fs [] \\ pop_assum mp_tac \\ simp []
      \\ drule env_to_list_lookup_equiv
      \\ fs [EXTENSION,domain_lookup,lookup_fromAList])
    \\ fs [wordSemTheory.set_var_def,set_var_def]
    \\ fs [state_rel_thm]
    \\ fs [lookup_insert,adjust_var_11, call_env_def,
           push_env_def,set_var_def,wordSemTheory.set_var_def]
    \\ strip_tac THEN1
     (drule env_to_list_lookup_equiv \\ strip_tac
      \\ fs [lookup_fromAList,wordSemTheory.cut_env_def]
      \\ rveq \\ fs [] \\ fs [lookup_inter_alt]
      \\ fs [adjust_set_def,domain_lookup,lookup_fromAList])
    \\ conj_tac THEN1
     (rw [] \\ fs [lookup_fromAList]
      \\ drule env_to_list_lookup_equiv \\ strip_tac
      \\ fs [lookup_fromAList,wordSemTheory.cut_env_def]
      \\ rveq \\ fs [lookup_inter_alt,adjust_var_IN_adjust_set]
      \\ rw [] \\ fs [cut_env_def]
      \\ rveq \\ fs [lookup_inter_alt])
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs [flat_def]
    \\ drule v_to_list_IMP_list_to_v \\ strip_tac \\ rveq \\ fs []
    \\ drule memory_rel_tl \\ strip_tac
    \\ drule (GEN_ALL memory_rel_less_space)
    \\ disch_then (qspec_then `0` mp_tac) \\ fs []
    \\ fs [join_env_def]
    \\ match_mp_tac (METIS_PROVE [] ``x = y ==> x ==> y``)
    \\ sg `inter t.locals (adjust_set x) = inter (fromAList q) (adjust_set x)`
    >- (fs [spt_eq_thm,lookup_inter_alt]
        \\ rw [] \\ fs []
        \\ drule env_to_list_lookup_equiv
        \\ fs [lookup_insert,lookup_fromAList,adjust_var_11]
        \\ rpt strip_tac \\ fs []
        \\ fs [wordSemTheory.cut_env_def,cut_env_def] \\ rveq
        \\ fs [lookup_inter_alt] \\ rw []
        \\ sg `F` \\ fs [] \\ pop_assum mp_tac \\ simp []
        \\ unabbrev_all_tac \\ fs [IN_domain_adjust_set_inter])
    (* ASK: is there a better way?  *)
    \\ qpat_x_assum `memory_rel _ _ _ _ _ _ _ _` mp_tac
    \\ ONCE_ASM_REWRITE_TAC []
    \\ qmatch_goalsub_abbrev_tac `((r2,h')::refs)`
    \\ rw []
    \\ EQ_TAC \\ rw []
    >- rpt_drule0 eq_upto_ts_mem_rel
    (* Not a fan *)
    >- (pop_assum (K ALL_TAC)
       \\ rpt_drule0 memory_rel_zero_space
        \\ rw []))
  \\ `?ww. h = Word ww /\ (1w && ww) <> 0w` by
   (imp_res_tac v_to_list_SOME_CONS_IMP \\ rveq \\ fs []
    \\ qpat_x_assum `state_rel c l1 l2 s1 t [] locs` mp_tac
    \\ simp [Once state_rel_thm] \\ strip_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ drule (GEN_ALL memory_rel_get_vars_IMP)
    \\ fs [Abbr`s1`]
    \\ disch_then drule
    \\ fs [wordSemTheory.get_vars_def]
    \\ fs [SIMP_RULE (srw_ss()) [] word_and_one_eq_0_iff]
    \\ strip_tac \\ drule memory_rel_Block_IMP \\ fs []
    \\ strip_tac \\ rveq \\ fs [])
  \\ fs []
  \\ simp [wordSemTheory.push_env_def,wordSemTheory.dec_clock_def]
  \\ Cases_on `env_to_list y t.permute` \\ fs []
  \\ simp [wordSemTheory.call_env_def,fromList2_def]
  \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def]
  \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def]
  \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def]
  \\ `?next_free trig_gc curr.
         FLOOKUP t.store NextFree = SOME (Word next_free) /\
         FLOOKUP t.store TriggerGC = SOME (Word trig_gc) /\
         FLOOKUP t.store CurrHeap = SOME (Word curr)` by
        fs [state_rel_thm,memory_rel_def,heap_in_memory_store_def]
  \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def,FLOOKUP_UPDATE]
  \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def,FLOOKUP_UPDATE]
  \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def,FLOOKUP_UPDATE,
           wordLangTheory.word_sh_def]
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
  \\ fs [v_to_list_IFF_list_to_v] \\ rveq \\ fs []
  \\ qpat_x_assum `state_rel c l1 l2 s1 t [] locs` mp_tac
  \\ simp [Once state_rel_thm] \\ strip_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule (GEN_ALL memory_rel_get_vars_IMP)
  \\ fs [Abbr`s1`] \\ fs [] \\ disch_then drule
  \\ fs [wordSemTheory.get_vars_def] \\ strip_tac
  (* MEM *)
  \\ qpat_assum `r1 ≅ts _` (mp_then Any assume_tac eq_upto_ts_mem_rel)
  \\ pop_assum drule \\ disch_tac
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
     (reverse conj_tac THEN1
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
      \\ drule env_to_list_lookup_equiv
      \\ fs [EXTENSION,domain_lookup,lookup_fromAList])
    \\ fs []
    \\ fs [wordSemTheory.set_var_def,set_var_def]
    \\ fs [state_rel_thm]
    \\ fs [lookup_insert,adjust_var_11,
           call_env_def,push_env_def,
           dataSemTheory.set_var_def,wordSemTheory.set_var_def]
    \\ strip_tac THEN1
      fs [code_oracle_rel_def, FLOOKUP_UPDATE]
    \\ strip_tac THEN1
     (drule env_to_list_lookup_equiv \\ strip_tac
      \\ fs [lookup_fromAList,wordSemTheory.cut_env_def]
      \\ rveq \\ fs [] \\ fs [lookup_inter_alt]
      \\ fs [adjust_set_def,domain_lookup,lookup_fromAList])
    \\ conj_tac THEN1
     (rw [] \\ fs [lookup_fromAList]
      \\ drule env_to_list_lookup_equiv \\ strip_tac
      \\ fs [lookup_fromAList,wordSemTheory.cut_env_def]
      \\ rveq \\ fs [lookup_inter_alt,adjust_var_IN_adjust_set]
      \\ rw [] \\ fs [cut_env_def]
      \\ rveq \\ fs [lookup_inter_alt])
    \\ fs [memory_rel_Temp,
         MATCH_MP FUPDATE_COMMUTES (prove(``Temp p <> NextFree``,EVAL_TAC))]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs [flat_def]
    \\ simp [FAPPLY_FUPDATE_THM]
    \\ qmatch_asmsub_abbrev_tac `memory_rel _ _ _ _ _ _ _ (A ++ B::C)`
    \\ sg `memory_rel c t.be s.refs sp t.store m1 t.mdomain ((B::A) ++ C)`
    >-
     (irule memory_rel_rearrange
      \\ HINT_EXISTS_TAC
      \\ rw [] \\ fs [])
    \\ map_every qunabbrev_tac [`A`,`B`,`C`]
    (* MEM r2 *)
    \\ qpat_assum `r2 ≅ts _` (mp_then Any assume_tac eq_upto_ts_mem_rel)
    \\ fs []
    \\ pop_assum drule \\ disch_tac
    (* This is quite fiddly  *)
    \\ pop_assum (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM APPEND_ASSOC])
    \\ pop_assum (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM APPEND_ASSOC])
    \\ rpt_drule0 (memory_rel_append  |> SIMP_RULE std_ss [APPEND])
    \\ simp [make_cons_ptr_def]
    \\ impl_keep_tac
    >- fs [Abbr`init_ptr`, get_lowerbits_def, make_header_def, encode_header_def]
    \\ strip_tac
    \\ drule (GEN_ALL memory_rel_less_space)
    \\ disch_then (qspec_then `0` mp_tac) \\ fs []
    \\ fs [join_env_def]
    \\ match_mp_tac (METIS_PROVE [] ``x = y ==> x ==> y``)
    \\ fs [Abbr`init_ptr`, get_lowerbits_def]
    \\ AP_TERM_TAC \\ AP_TERM_TAC \\ fs []
    \\ AP_TERM_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC
    \\ fs [spt_eq_thm,lookup_inter_alt]
    \\ rw [] \\ fs []
    \\ drule env_to_list_lookup_equiv
    \\ fs [lookup_insert,lookup_fromAList,adjust_var_11]
    \\ rpt strip_tac \\ fs []
    \\ fs [wordSemTheory.cut_env_def,cut_env_def] \\ rveq
    \\ fs [lookup_inter_alt] \\ rw []
    \\ sg `F` \\ fs [] \\ pop_assum mp_tac \\ simp []
    \\ unabbrev_all_tac \\ fs [IN_domain_adjust_set_inter])
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
    \\ drule memory_rel_list_limit
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
   (fs [stubs_def,code_rel_def]
    \\ imp_res_tac memory_rel_list_limit
    \\ `2 * dimword (:'a) <= MustTerminate_limit (:α)` by
          fs [wordSemTheory.MustTerminate_limit_def]
    \\ rfs [good_dimindex_def,dimword_def] \\ rfs [] \\ fs [])
  \\ strip_tac \\ fs []
  \\ rpt (qpat_x_assum `lookup _ _ = _` mp_tac)
  \\ pop_assum kall_tac
  \\ rpt strip_tac
  \\ `state_rel c l1 l2 ((s with <| locals := x ; space := sp |>)
          with clock := s.clock + 1)
       ((t with <| clock := t.clock + 1;
        store :=
        t.store |+ (Temp 0w,h') |+ (Temp 1w,Word ww) |+
         (Temp 2w,Word init_ptr) |>) with memory := m1) [] locs` by
   (fs [state_rel_thm,FAPPLY_FUPDATE_THM]
    \\ conj_tac >- fs [code_oracle_rel_def, FLOOKUP_UPDATE]
    \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac memory_rel_rearrange)
    \\ fs[MEM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[])
  \\ simp [AppendLenLoop_code_def,Once list_Seq_def]
  \\ fs [eq_eval,FLOOKUP_UPDATE]
  \\ simp [Once list_Seq_def,eq_eval]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [eq_eval]
  \\ simp [Once list_Seq_def,eq_eval,FLOOKUP_UPDATE]
  \\ simp [Once list_Seq_def,eq_eval,FLOOKUP_UPDATE]
  \\ simp [Once list_Seq_def,eq_eval,FLOOKUP_UPDATE]
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
  \\ fs [] \\ pop_assum kall_tac
  \\ disch_then drule
  \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def]
  \\ `dataSem$cut_env x' x = SOME x` by
   (fs [dataSemTheory.cut_env_def] \\ rveq
    \\ fs [domain_inter,spt_eq_thm]
    \\ fs [lookup_inter_alt])
  \\ disch_then drule
  \\ disch_then drule
  \\ disch_then (qspecl_then [`n`,`l`] assume_tac)
  \\ qmatch_assum_abbrev_tac `state_rel c n l s3 _ _ _`
  \\ `state_rel c n l (s3 with clock := tt.clock) tt [] ((l1,l2)::locs)` by
   (qunabbrev_tac `s3` \\ pop_assum mp_tac
    \\ simp [state_rel_thm]
    \\ fs [call_env_def,wordSemTheory.call_env_def,push_env_def,
           wordSemTheory.push_env_def,Abbr`tt`]
    \\ fs [eq_eval,FAPPLY_FUPDATE_THM]
    \\ strip_tac
    \\ conj_tac THEN1
     (fs [fromList_def,lookup_insert] \\ rw []
      \\ fs [adjust_var_def,lookup_def])
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
  THEN1 (unabbrev_all_tac \\ fs [call_env_def,push_env_def])
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
      \\ qpat_x_assum `memory_rel c t.be s.refs s.space t.store t.memory t.mdomain
         ((list_to_v (i1::in1),Word ww)::vars)` assume_tac
      \\ drule memory_rel_list_limit
      \\ rfs [good_dimindex_def] \\ rfs [dimword_def]
      \\ fs [LEFT_ADD_DISTRIB]
      \\ `sp MOD 3 < 3` by fs [] \\ simp [])
    \\ fs [ADD_DIV_EQ] \\ fs [X_LE_DIV])
  \\ pop_assum mp_tac \\ pop_assum kall_tac
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
     (qpat_x_assum `memory_rel c t.be s.refs s.space t.store t.memory t.mdomain
         ((list_to_v (i1::in1),Word ww)::vars)` assume_tac
      \\ drule memory_rel_list_limit
      \\ rfs [good_dimindex_def] \\ rfs [dimword_def])
    \\ fs []) \\ simp []
  \\ simp [Append_code_def]
  \\ simp [wordSemTheory.evaluate_def,eq_eval]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ drule (GEN_ALL memory_rel_get_vars_IMP)
  \\ disch_then drule
  \\ simp [wordSemTheory.get_vars_def,wordSemTheory.get_var_def,
           EVAL ``MAP adjust_var [0; 1]``,list_to_v_def]
  \\ strip_tac
  \\ first_assum (mp_then Any assume_tac eq_upto_ts_list_to_v_Cons)
  \\ first_assum (mp_then Any assume_tac eq_upto_ts_list_to_v_Block)
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
  \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def,FLOOKUP_UPDATE]
  \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def]
  \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def,FLOOKUP_UPDATE]
  \\ simp [Once list_Seq_def,eq_eval,wordSemTheory.set_store_def,FLOOKUP_UPDATE,
           wordLangTheory.word_sh_def]
  \\ qmatch_goalsub_abbrev_tac `insert 7 (Word init_ptr2)`
  \\ simp [list_Seq_def,eq_eval,wordSemTheory.set_store_def]
  \\ `lookup AppendMainLoop_location aa2.code = SOME (6,AppendMainLoop_code c)` by
       fs [state_rel_thm,code_rel_def,stubs_def] \\ fs [] \\ rfs []
  \\ fs [v_to_list_IFF_list_to_v] \\ rveq \\ fs []
  \\ drule memory_rel_space_max
  \\ simp [] \\ strip_tac \\ fs []
  \\ assume_tac (GEN_ALL evaluate_AppendMainLoop_code)
  \\ SEP_I_TAC "evaluate"
  \\ fs [lookup_insert,FLOOKUP_UPDATE]
  \\ fs [GSYM list_to_v_def]
  \\ pop_assum mp_tac
  \\ qpat_assum `Block ts _ _ ≅ts _` (mp_then Any assume_tac eq_upto_ts_mem_rel)
  \\ pop_assum drule \\ disch_tac
  \\ disch_tac
  \\ pop_assum drule \\ fs []
  \\ disch_then (qspec_then `0` mp_tac)
  \\ simp [markerTheory.Abbrev_def]
  \\ disch_then (qspec_then `SEP_T` mp_tac)
  \\ impl_tac THEN1
   (conj_asm1_tac THEN1 fs [Abbr `s4`]
    \\ reverse conj_tac THEN1
     (qpat_x_assum `memory_rel c t.be s.refs s.space t.store t.memory t.mdomain
         ((list_to_v (i1::in1),Word ww)::vars)` assume_tac
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
  \\ Cases_on `o'` \\ fs [stack_rel_def]
  \\ reverse IF_CASES_TAC THEN1
   (sg `F` \\ fs [] \\ pop_assum mp_tac \\ simp []
    \\ qspecl_then [`AllocVar c ll ss`,`tt`] mp_tac
         (wordPropsTheory.evaluate_stack_swap
            |> INST_TYPE [``:'c``|->``:'ffi``,``:'b``|->``:'c``])
    \\ fs []
    \\ `tt.stack = StackFrame q NONE::t.stack` by fs [Abbr`tt`] \\ fs []
    \\ fs [wordPropsTheory.s_key_eq_def]
    \\ fs [wordPropsTheory.s_frame_key_eq_def]
    \\ strip_tac \\ pop_assum kall_tac
    \\ fs [dataSemTheory.dec_clock_def]
    \\ rw [] \\ drule env_to_list_lookup_equiv
    \\ fs [EXTENSION,domain_lookup,lookup_fromAList]
    \\ fs[GSYM IS_SOME_EXISTS]
    \\ imp_res_tac MAP_FST_EQ_IMP_IS_SOME_ALOOKUP \\ metis_tac [])
  \\ fs []
  \\ fs [wordSemTheory.set_var_def,set_var_def]
  \\ fs [state_rel_thm]
  \\ fs [lookup_insert,adjust_var_11,
         dataSemTheory.call_env_def,
         push_env_def,dataSemTheory.set_var_def,wordSemTheory.set_var_def]
  \\ fs [wordSemTheory.dec_clock_def,dataSemTheory.dec_clock_def]
  \\ simp [FAPPLY_FUPDATE_THM,memory_rel_Temp]
  \\ fs [memory_rel_Temp,
         MATCH_MP FUPDATE_COMMUTES (prove(``Temp p <> NextFree``,EVAL_TAC))]
  \\ fs [contains_loc_def,lookup_fromAList]
  \\ strip_tac
  THEN1
   (qpat_x_assum `code_oracle_rel c _ _ _ _ _ _ _` mp_tac
    \\ fs [code_oracle_rel_def,FLOOKUP_UPDATE])
  \\ strip_tac
  THEN1 (rw[] \\ fs [adjust_var_11])
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs [flat_def]
  \\ simp [FAPPLY_FUPDATE_THM]
  \\ qmatch_asmsub_abbrev_tac `memory_rel _ _ _ _ _ _ _ (A ++ B::C)`
  \\ sg `memory_rel c aa2.be s.refs sp' aa2.store m1' aa2.mdomain ((B::A) ++ C)`
  >-
   (irule memory_rel_rearrange
    \\ HINT_EXISTS_TAC
    \\ rw [] \\ fs [])
  \\ map_every qunabbrev_tac [`A`,`B`,`C`]
  \\ qpat_assum `Block ts' _ _ ≅ts _` (mp_then Any assume_tac eq_upto_ts_mem_rel)
  \\ pop_assum (pop_assum o (fn t => t o SIMP_RULE std_ss [APPEND]) o (mp_then Any assume_tac))
  \\ rpt_drule0 (memory_rel_append  |> SIMP_RULE std_ss [APPEND])
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

Theorem assign_ConfigGC:
   op = ConfigGC ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac state_rel_cut_IMP \\ pop_assum mp_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app]
  \\ every_case_tac \\ fs[]
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ fs[assign_def,EVAL ``op_requires_names ConfigGC``]
  \\ fs [list_Seq_def,eq_eval]
  \\ reverse (Cases_on `c.call_empty_ffi`)
  THEN1
   (fs [SilentFFI_def,wordSemTheory.evaluate_def]
    \\ fs [case_eq_thms]
    \\ qpat_abbrev_tac `alll = alloc _ _ _`
    \\ `?x1 x2. alll = (x1,x2)` by (Cases_on `alll` \\ fs [])
    \\ unabbrev_all_tac \\ fs []
    \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` assume_tac
    \\ Cases_on `names_opt`
    \\ fs [cut_state_opt_def,cut_state_def,case_eq_thms] \\ rveq \\ fs []
    \\ rpt_drule0 (alloc_lemma |> Q.INST [`k`|->`0`])
    \\ fs [EVAL ``alloc_size 0``,get_names_def]
    \\ strip_tac \\ Cases_on `x1 = SOME NotEnoughSpace` \\ fs []
    \\ fs [state_rel_thm,set_var_def]
    \\ fs [lookup_insert,adjust_var_11]
    \\ strip_tac \\ rw []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert
    \\ fs [] \\ match_mp_tac memory_rel_Unit \\ fs [])
  \\ fs [SilentFFI_def,wordSemTheory.evaluate_def,eq_eval]
  \\ fs [wordSemTheory.evaluate_def,SilentFFI_def,wordSemTheory.word_exp_def,
         wordSemTheory.set_var_def,EVAL ``read_bytearray 0w 0 m``,
         ffiTheory.call_FFI_def,EVAL ``write_bytearray a [] m dm b``,
         wordSemTheory.get_var_def,lookup_insert]
  \\ Cases_on `names_opt`
  \\ fs [cut_state_opt_def,cut_state_def,case_eq_thms] \\ rveq \\ fs []
  \\ fs [get_names_def]
  \\ fs [cut_env_adjust_set_insert_3]
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
  \\ qmatch_assum_abbrev_tac `alloc _ _ t6 = _`
  \\ `t6 = t with locals := insert 1 (Word (alloc_size 0)) y` by
   (unabbrev_all_tac \\ fs [wordSemTheory.state_component_equality]
    \\ fs [EVAL ``alloc_size 0``,ZERO_LT_dimword])
  \\ fs [] \\ fs [EVAL ``alloc_size 0``,ZERO_LT_dimword]
  \\ strip_tac
  \\ Cases_on `x1 = SOME NotEnoughSpace` \\ fs []
  \\ rveq \\ fs []
  \\ imp_res_tac alloc_NONE_IMP_cut_env \\ fs []
  \\ fs [state_rel_thm,set_var_def]
  \\ fs [lookup_insert,adjust_var_11]
  \\ strip_tac \\ rw []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert
  \\ fs [] \\ match_mp_tac memory_rel_Unit \\ fs []
QED

Theorem assign_WordToInt:
   op = WordToInt ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app]
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
  \\ Cases_on `dimindex (:α) = 32` \\ simp []
  THEN1
   (BasicProvers.TOP_CASE_TAC >- simp[]
    \\ BasicProvers.TOP_CASE_TAC >- simp[]
    \\ eval_tac
    \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
    \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
    \\ drule0 memory_rel_Word64_IMP \\ fs [] \\ strip_tac
    \\ fs [get_vars_def]
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
      \\ fs [GSYM join_env_locals_def]
      \\ first_x_assum (fn th => mp_tac th THEN
           match_mp_tac (METIS_PROVE [] ``x=y ==> x ==> y``) THEN
           AP_TERM_TAC)
      \\ fs [FAPPLY_FUPDATE_THM]
      \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
      \\ Cases_on `c'` \\ rfs [word_extract_n2w,dimword_def,bitTheory.BITS_THM]
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
      \\ simp[inter_insert_ODD_adjust_set]
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
      \\ Cases_on `c'` \\ fs []
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
        \\ Cases_on `c'` \\ fs []
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
      \\ fs [GSYM join_env_locals_def]
      \\ fs [FAPPLY_FUPDATE_THM]
      \\ match_mp_tac (GEN_ALL memory_rel_less_space)
      \\ qexists_tac `x.space − 2` \\ fs []
      \\ first_x_assum (fn th => mp_tac th THEN
           match_mp_tac (METIS_PROVE [] ``x=y ==> x ==> y``) THEN
           AP_TERM_TAC)
      \\ fs [FAPPLY_FUPDATE_THM]
      \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
      \\ Cases_on `c'` \\ fs []
      \\ fs [word_extract_n2w,WORD_MUL_LSL,word_mul_n2w,
             bitTheory.BITS_THM2,dimword_def] \\ rfs []
      \\ fs [DIV_MOD_MOD_DIV]
      \\ fs [DIV_EQ_X] \\ rfs []))
  \\ BasicProvers.TOP_CASE_TAC >- simp[]
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
    \\ simp[inter_insert_ODD_adjust_set]
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
    \\ reverse conj_tac
    >- (`c' >>> 61 = 0w`
        by (qpat_x_assum `w2w c' >>> 61 = 0w` mp_tac
            \\ srw_tac[wordsLib.WORD_BIT_EQ_ss][])
        \\ simp[small_int_def,wordsTheory.dimword_def]
        \\ wordsLib.n2w_INTRO_TAC 64
        \\ qpat_x_assum `c' >>> 61 = 0w` mp_tac
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
  \\ fs[FAPPLY_FUPDATE_THM]
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

Theorem with_fresh_ts_state:
   ∀s ts tag lv.
    with_fresh_ts s (λts s'. Rval (Block ts tag lv,s')) =
     Rval (Block (with_fresh_ts s K) tag lv, with_fresh_ts s (λx y. y))
Proof
  rw [with_fresh_ts_def] \\ Cases_on `s.tstamps` \\ fs []
QED

Theorem with_fresh_ts_state_eq:
   (∀s. (with_fresh_ts s (λx y. y)).ffi = s.ffi) ∧
   (∀s. (with_fresh_ts s (λx y. y)).locals = s.locals) ∧
   (∀s. (with_fresh_ts s (λx y. y)).stack = s.stack) ∧
   (∀s. (with_fresh_ts s (λx y. y)).global = s.global) ∧
   (∀s. (with_fresh_ts s (λx y. y)).handler = s.handler) ∧
   (∀s. (with_fresh_ts s (λx y. y)).code = s.code) ∧
   (∀s. (with_fresh_ts s (λx y. y)).refs = s.refs) ∧
   (∀s. (with_fresh_ts s (λx y. y)).compile = s.compile) ∧
   (∀s. (with_fresh_ts s (λx y. y)).compile_oracle = s.compile_oracle) ∧
   (∀s. (with_fresh_ts s (λx y. y)).clock = s.clock) ∧
   (∀s. (with_fresh_ts s (λx y. y)).space = s.space)
Proof
   rw [with_fresh_ts_def] \\ Cases_on `s.tstamps` \\ fs []
QED

Theorem assign_FromList:
   (?tag. op = FromList tag) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP \\ strip_tac
  \\ fs [assign_def] \\ rveq
  \\ fs [dataLangTheory.op_requires_names_def,
         dataLangTheory.op_space_reset_def,cut_state_opt_def]
  \\ Cases_on `names_opt` \\ fs []
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app]
  \\ `?v vs. vals = [Number (&LENGTH vs); v] /\ v_to_list v = SOME vs` by
         (every_case_tac \\ fs [] \\ rw [] \\ NO_TAC)
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ IF_CASES_TAC \\ fs []
  \\ clean_tac
  \\ drule0 lookup_RefByte_location \\ fs [get_names_def]
  \\ fs [wordSemTheory.evaluate_def,list_Seq_def,word_exp_rw,
         wordSemTheory.find_code_def,wordSemTheory.set_var_def]
  \\ fs [wordSemTheory.add_ret_loc_def,wordSemTheory.find_code_def]
  \\ fs [wordSemTheory.bad_dest_args_def,wordSemTheory.get_vars_def,
         wordSemTheory.get_var_def,lookup_insert]
  \\ disch_then kall_tac
  \\ fs [cut_state_opt_def,cut_state_def]
  \\ rename1 `state_rel c l1 l2 s1 t [] locs`
  \\ Cases_on `dataSem$cut_env x' s.locals` \\ fs []
  \\ clean_tac \\ fs []
  \\ qabbrev_tac `s1 = s with locals := x`
  \\ `?y. cut_env (adjust_set x') t.locals = SOME y` by
       (match_mp_tac (GEN_ALL cut_env_IMP_cut_env) \\ fs []
        \\ metis_tac []) \\ fs []
  \\ Cases_on `lookup (adjust_var a1) t.locals` \\ fs []
  \\ Cases_on `lookup (adjust_var a2) t.locals` \\ fs []
  \\ fs[cut_env_adjust_set_insert_1]
  \\ `dimword (:α) <> 0` by (assume_tac ZERO_LT_dimword \\ decide_tac)
  \\ fs [wordSemTheory.dec_clock_def]
  \\ Q.MATCH_GOALSUB_ABBREV_TAC `evaluate (FromList_code _,t4)`
  \\ rveq
  \\ `state_rel c l1 l2 (s1 with clock := MustTerminate_limit(:'a))
        (t with <| clock := MustTerminate_limit(:'a); termdep := t.termdep - 1 |>)
          [] locs` by (fs [state_rel_def] \\ asm_exists_tac \\ fs [] \\ NO_TAC)
  \\ rpt_drule0 state_rel_call_env_push_env \\ fs []
  \\ `dataSem$get_vars [a1; a2] s.locals = SOME [Number (&LENGTH vs); v']` by
    (fs [dataSemTheory.get_vars_def] \\ every_case_tac \\ fs [cut_env_def]
     \\ clean_tac \\ fs [lookup_inter_alt,get_var_def] \\ NO_TAC)
  \\ `s1.locals = x` by (unabbrev_all_tac \\ fs []) \\ fs []
  \\ disch_then drule0 \\ fs []
  \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def]
  \\ `dataSem$cut_env x' s1.locals = SOME s1.locals` by
   (unabbrev_all_tac \\ fs []
    \\ fs [cut_env_def] \\ clean_tac
    \\ fs [domain_inter] \\ fs [lookup_inter_alt] \\ NO_TAC)
  \\ fs [] \\ rfs []
  \\ disch_then drule0 \\ fs []
  \\ disch_then (qspecl_then [`n`,`l`,`NONE`] mp_tac) \\ fs []
  \\ strip_tac
  \\ `4 * tag < dimword (:'a) DIV 16` by (fs [encode_header_def] \\ NO_TAC)
  \\ rpt_drule0 state_rel_IMP_Number_arg
  \\ strip_tac
  \\ Cases_on `vs` \\ fs [with_fresh_ts_def]
  \\ Cases_on `s.tstamps` \\ fs []
  \\ `s1.tstamps = s.tstamps` by rw [Abbr `s1`]
  \\ rpt_drule0 FromList_thm
  \\ (simp [Once call_env_def,wordSemTheory.dec_clock_def,do_app_def,
           get_vars_def,get_var_def,lookup_insert,fromList_def,
           do_space_def,dataLangTheory.op_space_reset_def,
           call_env_def,do_app_aux_def,with_fresh_ts_def,
           dec_clock_tstamps,push_env_tstamps]
  \\ disch_then (qspecl_then [`l2`,`l1`] strip_assume_tac)
  \\ qmatch_assum_abbrev_tac
       `evaluate (FromList_code c,t5) = _`
  \\ `t5 = t4` by
   (unabbrev_all_tac \\ fs [wordSemTheory.call_env_def,
       wordSemTheory.push_env_def] \\ pairarg_tac \\ fs [] \\ NO_TAC)
  \\ fs [] \\ Cases_on `q = SOME NotEnoughSpace` THEN1 fs [] \\ fs []
  \\ rpt_drule0 state_rel_pop_env_IMP
  \\ simp [push_env_def,call_env_def,pop_env_def,dataSemTheory.dec_clock_def]
  \\ strip_tac \\ fs [] \\ clean_tac
  \\ `domain t2.locals = domain y` by
   (qspecl_then [`FromList_code c`,`t4`] mp_tac
         (wordPropsTheory.evaluate_stack_swap
            |> INST_TYPE [``:'b``|->``:'c``,``:'c``|->``:'ffi``])
    \\ fs [] \\ fs [wordSemTheory.pop_env_def]
    \\ Cases_on `r'.stack` \\ fs []
    \\ qmatch_assum_rename_tac `r'.stack = hr::tr`
    \\ Cases_on `hr` \\ fs []
    \\ rename1 `r2.stack = StackFrame ns opt::tr`
    \\ unabbrev_all_tac
    \\ fs [wordSemTheory.call_env_def,wordSemTheory.push_env_def]
    \\ pairarg_tac \\ Cases_on `opt`
    \\ fs [wordPropsTheory.s_key_eq_def,
          wordPropsTheory.s_frame_key_eq_def]
    \\ rw [] \\ drule0 env_to_list_lookup_equiv
    \\ fs [EXTENSION,domain_lookup,lookup_fromAList]
    \\ fs[GSYM IS_SOME_EXISTS]
    \\ imp_res_tac MAP_FST_EQ_IMP_IS_SOME_ALOOKUP \\ metis_tac []) \\ fs []
  \\ pop_assum mp_tac
  \\ pop_assum mp_tac
  \\ simp [state_rel_def]
  \\ fs [dataSemTheory.call_env_def,push_env_def,
         dataSemTheory.set_var_def,wordSemTheory.set_var_def]
  \\ fs [wordSemTheory.pop_env_def]
  \\ `t.clock = s.clock` by fs [state_rel_def] \\ fs []
  \\ unabbrev_all_tac \\ fs []
  \\ rpt (disch_then strip_assume_tac) \\ clean_tac \\ fs []
  \\ strip_tac THEN1
   (fs [lookup_insert,stack_rel_def,state_rel_def,contains_loc_def,
        wordSemTheory.pop_env_def] \\ rfs[] \\ clean_tac
    \\ every_case_tac \\ fs [] \\ clean_tac \\ fs [lookup_fromAList]
    \\ fs [wordSemTheory.push_env_def]
    \\ pairarg_tac \\ fs []
    \\ drule0 env_to_list_lookup_equiv
    \\ fs[contains_loc_def])
  \\ conj_tac THEN1 (fs [lookup_insert,adjust_var_11] \\ rw [])
  \\ asm_exists_tac \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac word_ml_inv_insert \\ fs [flat_def]
  \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac word_ml_inv_rearrange)
  \\ fs[MEM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[])
QED

Theorem assign_RefByte:
   (?fl. op = RefByte fl) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP \\ strip_tac
  \\ fs [assign_def] \\ rveq
  \\ fs [dataLangTheory.op_requires_names_def,
         dataLangTheory.op_space_reset_def,cut_state_opt_def]
  \\ Cases_on `names_opt` \\ fs []
  \\ qmatch_goalsub_abbrev_tac`Const tag`
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app]
  \\ `?i b. vals = [Number i; Number b]` by (every_case_tac \\ fs [] \\ NO_TAC)
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ Cases_on `0 <= i` \\ fs []
  \\ qpat_assum `_ = Rval (v,s2)` mp_tac
  \\ reverse IF_CASES_TAC \\ fs []
  \\ clean_tac \\ fs [wordSemTheory.evaluate_def]
  \\ simp[word_exp_rw,wordSemTheory.set_var_def]
  \\ fs [wordSemTheory.bad_dest_args_def]
  \\ fs [wordSemTheory.add_ret_loc_def,wordSemTheory.find_code_def]
  \\ drule0 lookup_RefByte_location \\ fs [get_names_def]
  \\ disch_then kall_tac
  \\ fs[get_vars_SOME_IFF]
  \\ simp[wordSemTheory.get_vars_def]
  \\ fs[wordSemTheory.get_var_def,lookup_insert]
  \\ fs [cut_state_opt_def,cut_state_def]
  \\ rename1 `state_rel c l1 l2 s1 t [] locs`
  \\ Cases_on `dataSem$cut_env x' s.locals` \\ fs []
  \\ clean_tac \\ fs []
  \\ qabbrev_tac `s1 = s with locals := x`
  \\ `?y. cut_env (adjust_set x') t.locals = SOME y` by
       (match_mp_tac (GEN_ALL cut_env_IMP_cut_env) \\ fs []
        \\ metis_tac []) \\ fs []
  \\ simp[cut_env_adjust_set_insert_1]
  \\ `dimword (:α) <> 0` by (assume_tac ZERO_LT_dimword \\ decide_tac)
  \\ fs [wordSemTheory.dec_clock_def]
  \\ qmatch_goalsub_abbrev_tac `RefByte_code c,t4`
  \\ rename1 `lookup (adjust_var a1) _ = SOME w1`
  \\ rename1 `lookup (adjust_var a2) _ = SOME w2`
  \\ rename1 `get_vars [a1; a2] x = SOME [Number i; Number (&w2n w)]`
  \\ `state_rel c l1 l2 (s1 with clock := MustTerminate_limit(:'a))
        (t with <| clock := MustTerminate_limit(:'a); termdep := t.termdep - 1 |>)
          [] locs` by (fs [state_rel_def] \\ asm_exists_tac \\ fs [] \\ NO_TAC)
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
  \\ disch_then (qspecl_then [`n`,`l`,`NONE`] mp_tac) \\ fs []
  \\ strip_tac
  \\ `w2n (tag) DIV 4 < dimword (:'a) DIV 16`
  by (fs[Abbr`tag`,labPropsTheory.good_dimindex_def,state_rel_def] \\ rw[dimword_def] )
  \\ rpt_drule0 state_rel_IMP_Number_arg \\ strip_tac
  \\ rpt_drule0 RefByte_thm
  \\ simp [get_vars_def,call_env_def,get_var_def,lookup_fromList]
  \\ `w2n tag DIV 4 = if fl then 0 else 4`
  by (
    fs[Abbr`tag`] \\ rw[]
    \\ fs[state_rel_def,dimword_def,good_dimindex_def] )
  \\ `n2w (4 * if fl then 0 else 4) = tag`
  by (rw[Abbr`tag`] )
  \\ fs [do_app]
  \\ fs [EVAL ``get_var 0 (call_env [x1;x2;x3] y)``]
  \\ disch_then (qspecl_then [`l1`,`l2`,`fl`] mp_tac)
  \\ impl_tac THEN1 EVAL_TAC
  \\ qpat_abbrev_tac `t5 = call_env [Loc n l; w1; w2; _] _`
  \\ `t5 = t4` by
   (unabbrev_all_tac \\ fs [wordSemTheory.call_env_def,
       wordSemTheory.push_env_def] \\ pairarg_tac \\ fs []
    \\ fs [wordSemTheory.env_to_list_def,wordSemTheory.dec_clock_def] \\ NO_TAC)
  \\ pop_assum (fn th => fs [th]) \\ strip_tac \\ fs []
  \\ Cases_on `q = SOME NotEnoughSpace` THEN1 fs [] \\ fs []
  \\ rpt_drule0 state_rel_pop_env_IMP
  \\ simp [push_env_def,call_env_def,pop_env_def,dataSemTheory.dec_clock_def]
  \\ strip_tac \\ fs [] \\ clean_tac
  \\ `domain t2.locals = domain y` by
   (qspecl_then [`RefByte_code c`,`t4`] mp_tac
         (wordPropsTheory.evaluate_stack_swap
            |> INST_TYPE [``:'b``|->``:'c``,``:'c``|->``:'ffi``])
    \\ fs [] \\ fs [wordSemTheory.pop_env_def]
    \\ Cases_on `r'.stack` \\ fs [] \\ Cases_on `h` \\ fs []
    \\ rename1 `r2.stack = StackFrame ns opt::t'`
    \\ unabbrev_all_tac
    \\ fs [wordSemTheory.call_env_def,wordSemTheory.push_env_def]
    \\ pairarg_tac \\ Cases_on `opt`
    \\ fs [wordPropsTheory.s_key_eq_def,
          wordPropsTheory.s_frame_key_eq_def]
    \\ rw [] \\ drule0 env_to_list_lookup_equiv
    \\ fs [EXTENSION,domain_lookup,lookup_fromAList]
    \\ fs[GSYM IS_SOME_EXISTS]
    \\ imp_res_tac MAP_FST_EQ_IMP_IS_SOME_ALOOKUP \\ metis_tac []) \\ fs []
  \\ pop_assum mp_tac
  \\ pop_assum mp_tac
  \\ simp [state_rel_def]
  \\ fs [dataSemTheory.call_env_def,push_env_def,
         dataSemTheory.set_var_def,wordSemTheory.set_var_def]
  \\ fs [wordSemTheory.pop_env_def]
  \\ `t.clock = s.clock` by fs [state_rel_def] \\ fs []
  \\ unabbrev_all_tac \\ fs []
  \\ rpt (disch_then strip_assume_tac) \\ clean_tac \\ fs []
  \\ strip_tac THEN1
   (fs [lookup_insert,stack_rel_def,state_rel_def,contains_loc_def,
        wordSemTheory.pop_env_def] \\ rfs[] \\ clean_tac
    \\ every_case_tac \\ fs [] \\ clean_tac \\ fs [lookup_fromAList]
    \\ fs [wordSemTheory.push_env_def]
    \\ pairarg_tac \\ fs []
    \\ drule0 env_to_list_lookup_equiv
    \\ fs[contains_loc_def])
  \\ conj_tac THEN1 (fs [lookup_insert,adjust_var_11] \\ rw [])
  \\ asm_exists_tac \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac word_ml_inv_insert \\ fs [flat_def]
  \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac word_ml_inv_rearrange)
  \\ fs[MEM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
QED

Theorem assign_RefArray:
   op = RefArray ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP \\ strip_tac
  \\ fs [assign_def] \\ rveq
  \\ fs [dataLangTheory.op_requires_names_def,
         dataLangTheory.op_space_reset_def,cut_state_opt_def]
  \\ Cases_on `names_opt` \\ fs []
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app]
  \\ `?i w. vals = [Number i; w]` by (every_case_tac \\ fs [] \\ NO_TAC)
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ Cases_on `0 <= i` \\ fs []
  \\ clean_tac \\ fs [wordSemTheory.evaluate_def]
  \\ fs [wordSemTheory.bad_dest_args_def]
  \\ fs [wordSemTheory.add_ret_loc_def,wordSemTheory.find_code_def]
  \\ drule0 lookup_RefByte_location \\ fs [get_names_def]
  \\ disch_then kall_tac
  \\ fs [cut_state_opt_def,cut_state_def]
  \\ rename1 `state_rel c l1 l2 s1 t [] locs`
  \\ Cases_on `dataSem$cut_env x' s.locals` \\ fs []
  \\ clean_tac \\ fs []
  \\ qabbrev_tac `s1 = s with locals := x`
  \\ `?y. cut_env (adjust_set x') t.locals = SOME y` by
       (match_mp_tac (GEN_ALL cut_env_IMP_cut_env) \\ fs []
        \\ metis_tac []) \\ fs []
  \\ `dimword (:α) <> 0` by (assume_tac ZERO_LT_dimword \\ decide_tac)
  \\ fs [wordSemTheory.dec_clock_def]
  \\ qpat_abbrev_tac `t4 = wordSem$call_env [Loc n l; _; _] _ with clock := _`
  \\ rename1 `get_vars [adjust_var a1; adjust_var a2] t = SOME [w1;w2]`
  \\ rename1 `get_vars [a1; a2] x = SOME [Number i;v2]`
  \\ `state_rel c l1 l2 (s1 with clock := MustTerminate_limit(:'a))
        (t with <| clock := MustTerminate_limit(:'a); termdep := t.termdep - 1 |>)
          [] locs` by (fs [state_rel_def] \\ asm_exists_tac \\ fs [] \\ NO_TAC)
  \\ rpt_drule0 state_rel_call_env_push_env \\ fs []
  \\ `get_vars [a1; a2] s.locals = SOME [Number i; v2]` by
    (fs [dataSemTheory.get_vars_def] \\ every_case_tac \\ fs [cut_env_def]
     \\ clean_tac \\ fs [lookup_inter_alt,get_var_def] \\ NO_TAC)
  \\ `s1.locals = x` by (unabbrev_all_tac \\ fs []) \\ fs []
  \\ disch_then drule0 \\ fs []
  \\ `dataSem$cut_env x' x = SOME x` by
   (unabbrev_all_tac \\ fs []
    \\ fs [cut_env_def] \\ clean_tac
    \\ fs [domain_inter] \\ fs [lookup_inter_alt])
  \\ disch_then drule0 \\ fs []
  \\ disch_then (qspecl_then [`n`,`l`,`NONE`] mp_tac) \\ fs []
  \\ strip_tac
  \\ rpt_drule0 RefArray_thm
  \\ simp [get_vars_def,call_env_def,get_var_def,lookup_fromList]
  \\ fs [do_app]
  \\ fs [EVAL ``get_var 0 (call_env [x1;x2;x3] y)``]
  \\ disch_then (qspecl_then [`l1`,`l2`] mp_tac)
  \\ impl_tac THEN1 EVAL_TAC
  \\ qpat_abbrev_tac `t5 = call_env [Loc n l; w1; w2] _`
  \\ `t5 = t4` by
   (unabbrev_all_tac \\ fs [wordSemTheory.call_env_def,
       wordSemTheory.push_env_def] \\ pairarg_tac \\ fs []
    \\ fs [wordSemTheory.env_to_list_def,wordSemTheory.dec_clock_def] \\ NO_TAC)
  \\ pop_assum (fn th => fs [th]) \\ strip_tac \\ fs []
  \\ Cases_on `q = SOME NotEnoughSpace` THEN1 fs [] \\ fs []
  \\ rpt_drule0 state_rel_pop_env_IMP
  \\ simp [push_env_def,call_env_def,pop_env_def,dataSemTheory.dec_clock_def]
  \\ strip_tac \\ fs [] \\ clean_tac
  \\ `domain t2.locals = domain y` by
   (qspecl_then [`RefArray_code c`,`t4`] mp_tac
         (wordPropsTheory.evaluate_stack_swap
            |> INST_TYPE [``:'b``|->``:'c``,``:'c``|->``:'ffi``])
    \\ fs [] \\ fs [wordSemTheory.pop_env_def]
    \\ Cases_on `r'.stack` \\ fs [] \\ Cases_on `h` \\ fs []
    \\ rename1 `r2.stack = StackFrame ns opt::t'`
    \\ unabbrev_all_tac
    \\ fs [wordSemTheory.call_env_def,wordSemTheory.push_env_def]
    \\ pairarg_tac \\ Cases_on `opt`
    \\ fs [wordPropsTheory.s_key_eq_def,
          wordPropsTheory.s_frame_key_eq_def]
    \\ rw [] \\ drule0 env_to_list_lookup_equiv
    \\ fs [EXTENSION,domain_lookup,lookup_fromAList]
    \\ fs[GSYM IS_SOME_EXISTS]
    \\ imp_res_tac MAP_FST_EQ_IMP_IS_SOME_ALOOKUP \\ metis_tac []) \\ fs []
  \\ pop_assum mp_tac
  \\ pop_assum mp_tac
  \\ simp [state_rel_def]
  \\ fs [dataSemTheory.call_env_def,push_env_def,
         dataSemTheory.set_var_def,wordSemTheory.set_var_def]
  \\ fs [wordSemTheory.pop_env_def]
  \\ `t.clock = s.clock` by fs [state_rel_def] \\ fs []
  \\ unabbrev_all_tac \\ fs []
  \\ rpt (disch_then strip_assume_tac) \\ clean_tac \\ fs []
  \\ strip_tac THEN1
   (fs [lookup_insert,stack_rel_def,state_rel_def,contains_loc_def,
        wordSemTheory.pop_env_def] \\ rfs[] \\ clean_tac
    \\ every_case_tac \\ fs [] \\ clean_tac \\ fs [lookup_fromAList]
    \\ fs [wordSemTheory.push_env_def]
    \\ pairarg_tac \\ fs []
    \\ drule0 env_to_list_lookup_equiv
    \\ fs[contains_loc_def])
  \\ conj_tac THEN1 (fs [lookup_insert,adjust_var_11] \\ rw [])
  \\ asm_exists_tac \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac word_ml_inv_insert \\ fs [flat_def]
  \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac word_ml_inv_rearrange)
  \\ fs[MEM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
QED

val LENGTH_n2mw_1 = prove(
  ``LENGTH ((n2mw n) :'a word list) = 1 <=> n <> 0 /\ n < dimword (:'a)``,
  once_rewrite_tac [multiwordTheory.n2mw_def] \\ rw []
  \\ once_rewrite_tac [multiwordTheory.n2mw_def] \\ rw []
  \\ fs [dimword_def,DIV_EQ_0]);

val WordFromInt_DIV_LEMMA = prove(
  ``kk < B * B /\ 0 < B ==> B * (kk DIV B) <= B * B − B``,
  rw []
  \\ `kk DIV B < B` by fs [DIV_LT_X]
  \\ `B² − B = B * (B - 1)` by fs [LEFT_SUB_DISTRIB]
  \\ fs []);

val explode_less_32 = prove(
  ``(!n. n < 32n ==> P (n:num)) <=>
    P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5 /\ P 6 /\ P 7 /\ P 8 /\ P 9 /\
    P 10 /\ P 11 /\ P 12 /\ P 13 /\ P 14 /\ P 15 /\ P 16 /\ P 17 /\ P 18 /\ P 19 /\
    P 20 /\ P 21 /\ P 22 /\ P 23 /\ P 24 /\ P 25 /\ P 26 /\ P 27 /\ P 28 /\ P 29 /\
    P 30 /\ P 31``,
  rw [] \\ eq_tac \\ fs [] \\ rw []
  \\ rpt (Cases_on `n` \\ fs [] \\ Cases_on `n'` \\ fs []));

val LESS_IMP_NOT_BIT = prove(
  ``!k n. n < 2 ** k ==> ~BIT k n``,
  fs [bitTheory.BIT_def,bitTheory.BITS_THM,LESS_DIV_EQ_ZERO]);

Theorem Smallnum_alt:
   Smallnum i =
    if i < 0 then (0w - n2w (Num (-i))) << 2 else n2w (Num i) << 2
Proof
  Cases_on `i` \\ fs [WORD_MUL_LSL,Smallnum_def,GSYM word_mul_n2w]
  \\ once_rewrite_tac [SIMP_CONV (srw_ss()) [] ``-w:'a word``]
  \\ simp_tac std_ss [AC WORD_MULT_COMM WORD_MULT_ASSOC]
QED

val BIT_lemma = prove(
  ``BIT n (2 ** k - i) <=> if n < k /\ i < 2n ** k /\ i <> 0
                           then BIT n (2 ** (MAX n i + 1) - i)
                           else BIT n (2 ** k - i)``,
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
  \\ rw [MAX_DEF] \\ fs []);

val BIT_Lemma2 = prove(
  ``BIT m (2 ** k - n) = if n <> 0 /\ n <= 2 ** m /\ m < k then T
                         else BIT m (2n ** k - n)``,
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
  \\ fs [LESS_DIV_EQ_ZERO]);

Theorem assign_WordFromInt:
   op = WordFromInt ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app]
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
  \\ BasicProvers.TOP_CASE_TAC >- simp[]
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
        \\ rveq \\ fs []
        \\ strip_tac \\ conj_tac THEN1 rw []
        \\ `Word64 (n2w (Num (ABS i))) = Word64 (i2w i)` by
              (Cases_on `i` \\ fs [integer_wordTheory.i2w_def,Num_ABS_AND])
        \\ fs [FAPPLY_FUPDATE_THM])
      THEN1
       (assume_tac (GEN_ALL evaluate_WriteWord64_on_32)
        \\ SEP_I_TAC "evaluate" \\ fs [eq_eval]
        \\ fs [GSYM join_env_locals_def]
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
        \\ fs [FAPPLY_FUPDATE_THM]))
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
      \\ fs [GSYM join_env_locals_def]
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
      \\ fs [FAPPLY_FUPDATE_THM])
    THEN1
     (Cases_on `n2mw (Num (ABS i))` \\ fs []
      \\ Cases_on `t'` \\ fs []
      \\ fs [word_list_def] \\ SEP_R_TAC \\ fs []
      \\ fs [list_Seq_def,eq_eval] \\ SEP_R_TAC
      \\ fs [eq_eval,wordSemTheory.inst_def]
      \\ assume_tac (GEN_ALL evaluate_WriteWord64_on_32)
      \\ SEP_I_TAC "evaluate" \\ fs [eq_eval]
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
      \\ fs [FAPPLY_FUPDATE_THM]))
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
    \\ clean_tac \\ fs[code_oracle_rel_def,FLOOKUP_UPDATE]
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
    \\ clean_tac \\ fs[code_oracle_rel_def,FLOOKUP_UPDATE]
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
  \\ clean_tac \\ fs[code_oracle_rel_def,FLOOKUP_UPDATE]
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
   (?tag. op = TagEq tag) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
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
    \\ fs [] \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
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
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
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
  \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs [inter_insert_ODD_adjust_set_alt]
  \\ TRY (match_mp_tac memory_rel_Boolv_T)
  \\ TRY (match_mp_tac memory_rel_Boolv_F) \\ fs []
QED

Theorem assign_TagLenEq:
   (?tag len. op = TagLenEq tag len) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
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
  THEN1
   (reverse IF_CASES_TAC
    \\ fs [LENGTH_NIL]
    \\ imp_res_tac get_vars_1_imp \\ eval_tac
    \\ fs [wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def]
    THEN1
     (fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
      \\ imp_res_tac memory_rel_tag_limit
      \\ rpt_drule0 (DECIDE ``n < m /\ ~(k < m:num) ==> n <> k``) \\ fs []
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ match_mp_tac memory_rel_Boolv_F \\ fs [])
    \\ rpt_drule0 memory_rel_test_nil_eq \\ strip_tac \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ TRY (match_mp_tac memory_rel_Boolv_F) \\ fs []
    \\ TRY (match_mp_tac memory_rel_Boolv_T) \\ fs [])
  \\ CASE_TAC \\ fs [] THEN1
   (eval_tac \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
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
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
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
  \\ fs [inter_insert_ODD_adjust_set]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ TRY (match_mp_tac memory_rel_Boolv_F) \\ fs []
  \\ TRY (match_mp_tac memory_rel_Boolv_T) \\ fs []
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

Theorem assign_Add:
   op = Add ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [EVAL ``op_requires_names Add``]
  \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs [] \\ rveq
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
    \\ fs [lookup_insert,adjust_var_NEQ,adjust_var_11]
    \\ fs [inter_insert_ODD_adjust_set]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ drule0 memory_rel_zero_space \\ fs [])
  \\ unabbrev_all_tac
  \\ match_mp_tac eval_Call_Add
  \\ fs [state_rel_insert_3_1]
QED

Theorem assign_Sub:
   op = Sub ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [EVAL ``op_requires_names Sub``]
  \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs [] \\ rveq
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
    \\ fs [lookup_insert,adjust_var_NEQ,adjust_var_11]
    \\ fs [inter_insert_ODD_adjust_set]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ drule0 memory_rel_zero_space \\ fs [])
  \\ unabbrev_all_tac
  \\ match_mp_tac eval_Call_Sub
  \\ fs [state_rel_insert_3_1]
QED

Theorem cut_state_opt_IMP_ffi:
   dataSem$cut_state_opt names_opt s = SOME x ==> x.ffi = s.ffi
Proof
  fs [dataSemTheory.cut_state_opt_def,dataSemTheory.cut_state_def]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
QED

Theorem assign_Mult:
   op = Mult ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [EVAL ``op_requires_names Mult``]
  \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs [] \\ rveq
  \\ rename1 `get_vars args x.locals = SOME [Number i1; Number i2]`
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [assign_def]
  \\ fs [get_vars_SOME_IFF,get_vars_SOME_IFF_data]
  \\ pop_assum kall_tac
  \\ `(?w1. a1' = Word w1) /\ (?w2. a2' = Word w2)` by
         metis_tac [state_rel_get_var_Number_IMP_alt,adjust_var_def]
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
  THEN1
   (fs [eq_eval,wordSemTheory.set_vars_def,alist_insert_def]
    \\ fs [dataSemTheory.call_env_def,alist_insert_def,push_env_def,
           dataSemTheory.set_var_def,wordSemTheory.set_vars_def]
    \\ fs [state_rel_thm,lookup_insert,adjust_var_11]
    \\ conj_tac THEN1 (rw [] \\ fs [])
    \\ fs [inter_insert_ODD_adjust_set]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
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
  \\ rewrite_tac [list_Seq_def]
  \\ fs [dataSemTheory.call_env_def,alist_insert_def,push_env_def,
         dataSemTheory.set_var_def,wordSemTheory.set_vars_def]
  \\ imp_res_tac cut_state_opt_IMP_ffi \\ fs []
  \\ match_mp_tac (eval_Call_Mul |> REWRITE_RULE [list_Seq_def])
  \\ fs []
  \\ fs [get_vars_def,get_var_def]
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` mp_tac
  \\ fs [state_rel_thm,lookup_insert]
  \\ fs [inter_insert_ODD_adjust_set_alt]
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

Theorem assign_Div:
   op = Div ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [EVAL ``op_requires_names Div``]
  \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs [] \\ rveq
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
    \\ fs [eq_eval,code_rel_def,stubs_def,cut_env_adjust_set_insert_1]
    \\ Cases_on `names_opt` \\ fs [cut_state_opt_def,cut_state_def]
    \\ Cases_on `dataSem$cut_env x' s.locals` \\ fs []
    \\ imp_res_tac cut_env_IMP_cut_env
    \\ fs [get_names_def,wordSemTheory.push_env_def]
    \\ Cases_on `env_to_list y t.permute` \\ fs []
    \\ qmatch_goalsub_abbrev_tac `evaluate (LongDiv_code c,t2)`
    \\ qspecl_then [`t2`,`n`,`l+1`,`c`] mp_tac evaluate_LongDiv_code
    \\ fs [] \\ disch_then (qspecl_then [`0w`,`n2w (4 * n1)`,`n2w (4 * n2)`] mp_tac)
    \\ fs [multiwordTheory.single_div_def]
    \\ impl_tac THEN1
     (unabbrev_all_tac
      \\ fs [lookup_insert,wordSemTheory.MustTerminate_limit_def,
             mc_multiwordTheory.single_div_pre_def]
      \\ fs [DIV_LT_X] \\ Cases_on `n2` \\ fs [MULT_CLAUSES])
    \\ strip_tac \\ fs []
    \\ fs [wordSemTheory.pop_env_def,Abbr `t2`]
    \\ reverse IF_CASES_TAC THEN1
     (sg `F` \\ fs [] \\ pop_assum mp_tac \\ fs []
      \\ drule0 env_to_list_lookup_equiv
      \\ fs [domain_lookup,EXTENSION,lookup_fromAList])
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
     (drule0 env_to_list_lookup_equiv \\ fs []
      \\ drule0 cut_env_adjust_set_lookup_0 \\ fs [lookup_fromAList])
    \\ conj_tac THEN1
     (rw [] \\ fs []
      \\ drule0 env_to_list_lookup_equiv \\ fs []
      \\ drule0 cut_env_IMP_MEM \\ fs [lookup_fromAList]
      \\ drule0 (GEN_ALL adjust_var_cut_env_IMP_MEM) \\ fs []
      \\ drule0 (GEN_ALL cut_env_IMP_MEM) \\ fs []
      \\ strip_tac \\ fs [])
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
    \\ fs [join_env_def,MEM_MAP,MEM_FILTER]
    \\ Cases_on `y'` \\ fs []
    \\ rename1 `MEM (y1,y2) _`
    \\ qexists_tac `(y1,y2)` \\ fs [MEM_toAList]
    \\ fs [lookup_inter_alt]
    \\ fs [cut_env_def,wordSemTheory.cut_env_def] \\ rveq
    \\ fs [domain_lookup] \\ rfs [lookup_adjust_set]
    \\ fs [domain_lookup,lookup_inter_alt]
    \\ drule0 env_to_list_lookup_equiv
    \\ fs [lookup_fromAList] \\ strip_tac \\ fs [] \\ fs [lookup_inter_alt])
  \\ pop_assum kall_tac
  \\ fs [list_Seq_def]
  \\ once_rewrite_tac [wordSemTheory.evaluate_def] \\ fs []
  \\ fs [dataSemTheory.call_env_def,alist_insert_def,push_env_def,
         dataSemTheory.set_var_def,wordSemTheory.set_vars_def]
  \\ imp_res_tac cut_state_opt_IMP_ffi \\ fs []
  \\ match_mp_tac (eval_Call_Div |> REWRITE_RULE [list_Seq_def])
  \\ fs [get_vars_SOME_IFF_data,insert_shadow]
  \\ fs [GSYM wordSemTheory.set_var_def]
  \\ fs [wordSemTheory.set_var_def,state_rel_insert_1]
QED

Theorem assign_Mod:
   op = Mod ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [EVAL ``op_requires_names Mod``]
  \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs [] \\ rveq
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
    \\ fs [eq_eval,code_rel_def,stubs_def,cut_env_adjust_set_insert_1]
    \\ Cases_on `names_opt` \\ fs [cut_state_opt_def,cut_state_def]
    \\ Cases_on `dataSem$cut_env x' s.locals` \\ fs []
    \\ imp_res_tac cut_env_IMP_cut_env
    \\ fs [get_names_def,wordSemTheory.push_env_def]
    \\ Cases_on `env_to_list y t.permute` \\ fs []
    \\ qmatch_goalsub_abbrev_tac `evaluate (LongDiv_code c,t2)`
    \\ qspecl_then [`t2`,`n`,`l+1`,`c`] mp_tac evaluate_LongDiv_code
    \\ fs [] \\ disch_then (qspecl_then [`0w`,`n2w (4 * n1)`,`n2w (4 * n2)`] mp_tac)
    \\ fs [multiwordTheory.single_div_def]
    \\ impl_tac THEN1
     (unabbrev_all_tac
      \\ fs [lookup_insert,wordSemTheory.MustTerminate_limit_def,
             mc_multiwordTheory.single_div_pre_def]
      \\ fs [DIV_LT_X] \\ Cases_on `n2` \\ fs [MULT_CLAUSES])
    \\ strip_tac \\ fs []
    \\ fs [wordSemTheory.pop_env_def,Abbr `t2`]
    \\ reverse IF_CASES_TAC THEN1
     (sg `F` \\ fs [] \\ pop_assum mp_tac \\ fs []
      \\ drule0 env_to_list_lookup_equiv
      \\ fs [domain_lookup,EXTENSION,lookup_fromAList])
    \\ fs [list_Seq_def,eq_eval,FLOOKUP_UPDATE]
    \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [lookup_insert]
    \\ simp [state_rel_thm,lookup_insert,code_oracle_rel_def,FLOOKUP_UPDATE,
             adjust_var_11,dataSemTheory.call_env_def,alist_insert_def,
             push_env_def,dataSemTheory.set_var_def,wordSemTheory.set_vars_def]
    \\ fs [state_rel_thm,lookup_insert,code_oracle_rel_def,FLOOKUP_UPDATE,
           adjust_var_11,dataSemTheory.call_env_def,alist_insert_def,
           push_env_def,dataSemTheory.set_var_def,wordSemTheory.set_vars_def]
    \\ rveq \\ fs []
    \\ conj_tac THEN1
     (drule0 env_to_list_lookup_equiv \\ fs []
      \\ drule0 cut_env_adjust_set_lookup_0 \\ fs [lookup_fromAList])
    \\ conj_tac THEN1
     (rw [] \\ fs []
      \\ drule0 env_to_list_lookup_equiv \\ fs []
      \\ drule0 cut_env_IMP_MEM \\ fs [lookup_fromAList]
      \\ drule0 (GEN_ALL adjust_var_cut_env_IMP_MEM) \\ fs []
      \\ drule0 (GEN_ALL cut_env_IMP_MEM) \\ fs []
      \\ strip_tac \\ fs [])
    \\ fs [inter_insert_ODD_adjust_set]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert
    \\ fs [FAPPLY_FUPDATE_THM,memory_rel_Temp]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ `n2w ((4 * n1) MOD (4 * n2)) = Smallnum (&(n1 MOD n2))` by
       (fs [wordsTheory.word_quot_def,word_div_def,Smallnum_def]
        \\ fs [MOD_COMMON_FACTOR] \\ NO_TAC)
    \\ fs [] \\ match_mp_tac IMP_memory_rel_Number \\ fs []
    \\ imp_res_tac memory_rel_zero_space \\ fs [APPEND]
    \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
    \\ fs [] \\ rw [] \\ fs [] \\ disj1_tac
    \\ fs [join_env_def,MEM_MAP,MEM_FILTER]
    \\ Cases_on `y'` \\ fs []
    \\ rename1 `MEM (y1,y2) _`
    \\ qexists_tac `(y1,y2)` \\ fs [MEM_toAList]
    \\ fs [lookup_inter_alt]
    \\ fs [cut_env_def,wordSemTheory.cut_env_def] \\ rveq
    \\ fs [domain_lookup] \\ rfs [lookup_adjust_set]
    \\ fs [domain_lookup,lookup_inter_alt]
    \\ drule0 env_to_list_lookup_equiv
    \\ fs [lookup_fromAList] \\ strip_tac \\ fs [] \\ fs [lookup_inter_alt])
  \\ pop_assum kall_tac
  \\ fs [list_Seq_def]
  \\ once_rewrite_tac [wordSemTheory.evaluate_def] \\ fs []
  \\ fs [dataSemTheory.call_env_def,alist_insert_def,push_env_def,
         dataSemTheory.set_var_def,wordSemTheory.set_vars_def]
  \\ imp_res_tac cut_state_opt_IMP_ffi \\ fs []
  \\ match_mp_tac (eval_Call_Mod |> REWRITE_RULE [list_Seq_def])
  \\ fs [get_vars_SOME_IFF_data,insert_shadow]
  \\ fs [GSYM wordSemTheory.set_var_def]
  \\ fs [wordSemTheory.set_var_def,state_rel_insert_1]
QED

Theorem assign_LengthByte:
   op = LengthByte ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
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
  \\ `word_exp t (real_addr c (adjust_var a1)) = SOME (Word a)` by
       (match_mp_tac (GEN_ALL get_real_addr_lemma)
        \\ fs [wordSemTheory.get_var_def] \\ NO_TAC) \\ fs []
  \\ IF_CASES_TAC
  >- ( fs[good_dimindex_def] \\ rfs[shift_def] )
  \\ pop_assum kall_tac
  \\ simp[]
  \\ `2 < dimindex (:'a)` by
       (fs [labPropsTheory.good_dimindex_def] \\ fs [])
  \\ fs [] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
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
   op = Length ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
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
         (fs [labPropsTheory.good_dimindex_def] \\ NO_TAC)
  \\ fs [] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ fs [decode_length_def]
  \\ match_mp_tac IMP_memory_rel_Number_num \\ fs []
QED

Theorem assign_LengthBlock:
   op = LengthBlock ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
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
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ match_mp_tac (IMP_memory_rel_Number |> Q.INST [`i`|->`0`]
          |> SIMP_RULE std_ss [EVAL ``Smallnum 0``])
    \\ fs [] \\ fs [labPropsTheory.good_dimindex_def,dimword_def]
    \\ EVAL_TAC \\ rw [labPropsTheory.good_dimindex_def,dimword_def])
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ `word_exp t (real_addr c (adjust_var a1)) = SOME (Word a)` by
       (match_mp_tac (GEN_ALL get_real_addr_lemma)
        \\ fs [wordSemTheory.get_var_def] \\ NO_TAC) \\ fs []
  \\ fs [GSYM NOT_LESS,GREATER_EQ]
  \\ `c.len_size <> 0` by
      (fs [memory_rel_def,heap_in_memory_store_def] \\ NO_TAC)
  \\ fs [NOT_LESS]
  \\ `~(dimindex (:α) <= 2)` by
         (fs [labPropsTheory.good_dimindex_def] \\ NO_TAC)
  \\ fs [] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ fs [decode_length_def]
  \\ match_mp_tac IMP_memory_rel_Number_num \\ fs []
QED

Theorem assign_BoundsCheckBlock:
   assign c secn l dest BoundsCheckBlock args names =
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
QED ;

Theorem assign_BoundsCheckBlock:
   op = BoundsCheckBlock ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [get_var_def]
  \\ simp [state_rel_thm] \\ eval_tac
  \\ fs [state_rel_thm] \\ eval_tac
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
    \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def]
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
  \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
  \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [])
QED

Theorem assign_BoundsCheckArray:
   assign c secn l dest BoundsCheckArray args names =
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
QED ;

Theorem assign_BoundsCheckArray:
   op = BoundsCheckArray ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [get_var_def]
  \\ simp [state_rel_thm] \\ eval_tac
  \\ fs [state_rel_thm] \\ eval_tac
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
  \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
  \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [])
QED

Theorem assign_BoundsCheckByte:
   assign c secn l dest (BoundsCheckByte leq) args names =
      case args of
      | [v1;v2] => (list_Seq [Assign 1
                               (let addr = real_addr c (adjust_var v1) in
                                let header = Load addr in
                                let extra = (if dimindex (:'a) = 32 then 2 else 3) in
                                let k = dimindex (:'a) - c.len_size - extra in
                                let kk = (if dimindex (:'a) = 32 then 3w else 7w) in
                                  Op Sub [Shift Lsr header k; Const kk]);
                              Assign 3 (ShiftVar Ror (adjust_var v2) 2);
                              (if leq then If NotLower 1 (Reg 3) else
                                           If Lower 3 (Reg 1))
                               (Assign (adjust_var dest) TRUE_CONST)
                               (Assign (adjust_var dest) FALSE_CONST)],l)
      | _ => (Skip:'a wordLang$prog,l)
Proof
  fs [assign_def] \\ every_case_tac \\ fs []
QED

Theorem assign_BoundsCheckByte:
   (?leq. op = BoundsCheckByte leq) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [get_var_def]
  \\ simp [state_rel_thm] \\ eval_tac
  \\ fs [state_rel_thm] \\ eval_tac
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
  \\ strip_tac \\ fs []
  \\ IF_CASES_TAC
  \\ fs [] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
  \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
  \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [])
  \\ fs [good_dimindex_def]
QED

Theorem assign_LessConstSmall:
   assign c secn l dest (LessConstSmall i) args names =
      case args of
      | [v1] => (If Less (adjust_var v1) (Imm (n2w (4 * i)))
                  (Assign (adjust_var dest) TRUE_CONST)
                  (Assign (adjust_var dest) FALSE_CONST),l)
      | _ => (Skip:'a wordLang$prog,l)
Proof
  fs [assign_def] \\ every_case_tac \\ fs []
QED

Theorem assign_LessSmallConst:
   (?i. op = LessConstSmall i) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
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
  \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def]
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
      get_var 0 t = SOME (Loc l1 l2) /\
      get_var 2 t = SOME (Word l) /\
      get_var 4 t = SOME (Word a1) /\
      get_var 6 t = SOME (Word a2) /\
      w2n l <= t.clock ==>
      ?ck.
        evaluate (Compare1_code,t) =
          (SOME (Result (Loc l1 l2) (Word res)),
           t with <| clock := ck; locals := LN |>) /\
        t.clock <= w2n l + ck
Proof
  ho_match_mp_tac word_cmp_loop_ind \\ rw []
  \\ qpat_assum `_ = SOME res` mp_tac
  \\ once_rewrite_tac [word_cmp_loop_def,Compare1_code_def]
  \\ IF_CASES_TAC \\ fs [] \\ strip_tac \\ rveq
  THEN1
   (eval_tac \\ fs [wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,
      wordSemTheory.get_var_def,lookup_insert,wordSemTheory.call_env_def,
      fromList2_def,wordSemTheory.state_component_equality])
  \\ every_case_tac \\ fs [wordsTheory.WORD_LOWER_REFL] \\ rveq
  THEN1
   (fs [list_Seq_def]
    \\ eval_tac \\ fs [wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,
         wordSemTheory.get_var_def,lookup_insert,wordSemTheory.call_env_def,
         fromList2_def,wordSemTheory.state_component_equality])
  \\ `t.clock <> 0` by (Cases_on `l` \\ fs [] \\ NO_TAC)
  \\ fs [list_Seq_def]
  \\ eval_tac \\ fs [wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,
         wordSemTheory.get_var_def,lookup_insert,wordSemTheory.call_env_def,
         fromList2_def,wordSemTheory.state_component_equality,
         wordSemTheory.get_vars_def,wordSemTheory.bad_dest_args_def,
         wordSemTheory.add_ret_loc_def,wordSemTheory.find_code_def]
  \\ qpat_abbrev_tac `t1 = wordSem$dec_clock _ with locals := _`
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
QED

Theorem word_exp_insert:
   (m <> n ==>
     (word_exp (t with locals := insert n w t.locals) (real_addr c m) =
      word_exp t (real_addr c m))) /\
    (~(m IN {n;n1}) ==>
     (word_exp (t with locals := insert n w (insert n1 w1 t.locals)) (real_addr c m) =
      word_exp t (real_addr c m)))
Proof
  fs [wordSemTheory.word_exp_def,real_addr_def]
  \\ IF_CASES_TAC \\ fs []
  \\ fs [wordSemTheory.word_exp_def,real_addr_def] \\ fs [lookup_insert]
QED

Theorem Compare_code_thm:
   memory_rel c be refs sp st m dm
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
    ?ck.
      evaluate (Compare_code c,t) =
        (SOME (Result (Loc l1 l2) (Word (word_cmp_res i1 i2))),
         t with <| clock := ck; locals := LN |>)
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
         wordSemTheory.get_var_def,lookup_insert,wordSemTheory.call_env_def,
         fromList2_def,wordSemTheory.state_component_equality,word_bit_test])
  \\ pop_assum mp_tac \\ fs []
  \\ Cases_on `word_bit 0 v1` \\ fs []
  \\ reverse (Cases_on `word_bit 0 v2`) \\ fs []
  THEN1
   (`memory_rel c be refs sp t.store t.memory t.mdomain
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
         wordSemTheory.get_var_def,lookup_insert,wordSemTheory.call_env_def,
         fromList2_def,wordSemTheory.state_component_equality,word_bit_test])
  \\ `shift (:'a) <> 0 /\ shift (:'a) < dimindex (:'a)` by
          (fs [labPropsTheory.good_dimindex_def,shift_def] \\ NO_TAC)
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
         wordSemTheory.get_var_def,lookup_insert,wordSemTheory.call_env_def,
         fromList2_def,wordSemTheory.state_component_equality,word_bit_test,
         word_exp_insert,wordSemTheory.get_vars_def,
         wordSemTheory.get_var_def,lookup_insert,wordSemTheory.call_env_def,
         fromList2_def,wordSemTheory.state_component_equality,
         wordSemTheory.get_vars_def,wordSemTheory.bad_dest_args_def,
         wordSemTheory.add_ret_loc_def,wordSemTheory.find_code_def]
    \\ qpat_abbrev_tac `t1 = wordSem$dec_clock _ with locals := _`
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
       word_exp_insert,GSYM decode_length_def]
QED

Theorem word_cmp_Less_word_cmp_res:
   !i i'. good_dimindex (:'a) ==>
           (word_cmp Less (word_cmp_res i i') (1w:'a word) <=> i < i')
Proof
  rw [] \\ fs [labPropsTheory.good_dimindex_def]
  \\ fs [word_cmp_res_def,asmTheory.word_cmp_def]
  \\ rw [] \\ fs [WORD_LT] \\ fs [word_msb_def,word_index,dimword_def]
QED

Theorem word_cmp_NotLess_word_cmp_res:
   !i i'. good_dimindex (:'a) ==>
           (word_cmp NotLess (1w:'a word) (word_cmp_res i i') <=> (i <= i'))
Proof
  rw [] \\ fs [labPropsTheory.good_dimindex_def]
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
QED

Theorem dimword_LESS_MustTerminate_limit:
   good_dimindex (:'a) ==> dimword (:α) < MustTerminate_limit (:α) - 1
Proof
  strip_tac \\ fs [wordSemTheory.MustTerminate_limit_def,dimword_def]
  \\ match_mp_tac (DECIDE ``1 < n ==> n < (2 * n + k) - 1n``)
  \\ fs [labPropsTheory.good_dimindex_def]
QED

Theorem assign_Less:
   op = Less ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [get_var_def]
  \\ fs [Boolv_def] \\ rveq \\ fs [GSYM Boolv_def]
  \\ qpat_assum `state_rel c l1 l2 x t [] locs`
           (assume_tac o REWRITE_RULE [state_rel_thm])
  \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
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
    \\ IF_CASES_TAC \\ fs []
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
    \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
    \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [])
    \\ match_mp_tac (GEN_ALL memory_rel_zero_space)
    \\ metis_tac [])
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
  \\ fs [wordSemTheory.add_ret_loc_def]
  \\ fs [dataLangTheory.op_requires_names_def,
         dataLangTheory.op_space_reset_def]
  \\ TOP_CASE_TAC THEN1
   (Cases_on `names_opt` \\ fs []
    \\ fs [cut_state_opt_def,cut_state_def]
    \\ Cases_on `dataSem$cut_env x' s.locals` \\ fs []
    \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` assume_tac
    \\ rpt_drule0 cut_env_IMP_cut_env
    \\ CCONTR_TAC \\ fs [get_names_def]
    \\ fs [wordSemTheory.cut_env_def,SUBSET_DEF])
  \\ fs []
  \\ qpat_abbrev_tac `t1 = wordSem$call_env _ _`
  \\ first_x_assum (qspecl_then [`t1`,`l`,`n`] mp_tac)
  \\ impl_tac THEN1
   (unabbrev_all_tac
    \\ fs [wordSemTheory.call_env_def,wordSemTheory.push_env_def,
           wordSemTheory.dec_clock_def]
    \\ pairarg_tac \\ fs []
    \\ fs [fromList2_def,lookup_insert]
    \\ fs [state_rel_def,code_rel_def,stubs_def]
    \\ fs [memory_rel_def,word_ml_inv_def,heap_in_memory_store_def]
    \\ fs [dimword_LESS_MustTerminate_limit]
    \\ rpt strip_tac \\ simp [] \\ NO_TAC)
  \\ strip_tac \\ fs []
  \\ `?t2. pop_env t1 = SOME t2 /\ domain t2.locals = domain x'` by
   (unabbrev_all_tac
    \\ fs [wordSemTheory.call_env_def,wordSemTheory.push_env_def,
           wordSemTheory.pop_env_def] \\ pairarg_tac \\ fs []
    \\ imp_res_tac env_to_list_lookup_equiv
    \\ fs [domain_lookup,EXTENSION,lookup_fromAList] \\ NO_TAC)
  \\ fs []
  \\ fs [lookup_insert,word_cmp_Less_word_cmp_res]
  \\ rw [] \\ fs []
  \\ unabbrev_all_tac
  \\ fs [wordSemTheory.pop_env_def,wordSemTheory.call_env_def,
         wordSemTheory.push_env_def,wordSemTheory.dec_clock_def]
  \\ pairarg_tac \\ fs [] \\ rveq \\ fs []
  \\ simp [state_rel_thm]
  \\ fs [lookup_insert]
  \\ rpt_drule0 env_to_list_cut_env_IMP \\ fs []
  \\ disch_then kall_tac
  \\ fs [lookup_insert,FAPPLY_FUPDATE_THM,adjust_var_11,FLOOKUP_UPDATE]
  \\ fs [inter_insert_ODD_adjust_set]
  \\ fs [wordSemTheory.cut_env_def] \\ rveq
  \\ conj_tac
  \\ TRY (fs [lookup_inter,lookup_insert,adjust_set_def,fromAList_def] \\ NO_TAC)
  \\ `domain (adjust_set (get_names names_opt)) SUBSET domain t.locals` by
   (Cases_on `names_opt` \\ fs [get_names_def]
    \\ fs [SUBSET_DEF,domain_lookup]
    \\ rw [] \\ res_tac \\ fs []
    \\ rveq \\ fs [lookup_ODD_adjust_set] \\ NO_TAC)
  \\ `domain (adjust_set x.locals) SUBSET
      domain (inter t.locals (adjust_set (get_names names_opt)))` by
   (fs [SUBSET_DEF,domain_lookup,lookup_inter_alt] \\ rw []
    \\ Cases_on `names_opt` \\ fs [get_names_def]
    \\ fs [SUBSET_DEF,domain_lookup]
    \\ fs [cut_state_opt_def,cut_state_def,cut_env_def]
    \\ qpat_x_assum `_ = SOME x` mp_tac
    \\ IF_CASES_TAC \\ fs [] \\ rw [] \\ fs [adjust_set_inter]
    \\ fs [lookup_inter_alt,domain_lookup] \\ NO_TAC)
  \\ `!n. IS_SOME (lookup n x.locals) ==>
          n ∈ domain (get_names names_opt) /\
          IS_SOME (lookup (adjust_var n) t.locals)` by
   (qx_gen_tac `k` \\ disch_then assume_tac
    \\ Cases_on `lookup k x.locals` \\ fs []
    \\ Cases_on `names_opt` \\ fs [get_names_def]
    \\ fs [SUBSET_DEF,domain_lookup]
    \\ fs [cut_state_opt_def,cut_state_def,cut_env_def]
    \\ qpat_x_assum `_ = SOME x` mp_tac
    \\ IF_CASES_TAC \\ fs [] \\ rw [] \\ fs [adjust_set_inter]
    \\ fs [lookup_inter_alt,domain_lookup] \\ NO_TAC)
  \\ conj_tac
  \\ TRY (rw [] \\ once_rewrite_tac [lookup_inter_alt]
          \\ fs [lookup_insert,adjust_var_IN_adjust_set] \\ NO_TAC)
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs [inter_insert_ODD_adjust_set_alt]
  \\ match_mp_tac (GEN_ALL memory_rel_zero_space)
  \\ qexists_tac `x.space`
  \\ TRY (match_mp_tac memory_rel_Boolv_T)
  \\ TRY (match_mp_tac memory_rel_Boolv_F) \\ fs []
  \\ qsuff_tac `inter (inter t.locals (adjust_set (get_names names_opt)))
                 (adjust_set x.locals) = inter t.locals (adjust_set x.locals)`
  \\ asm_simp_tac std_ss [] \\ fs []
  \\ fs [lookup_inter_alt,SUBSET_DEF]
  \\ rw [] \\ fs [domain_inter] \\ res_tac
QED

Theorem assign_LessEq:
   op = LessEq ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [get_var_def]
  \\ fs [Boolv_def] \\ rveq \\ fs [GSYM Boolv_def]
  \\ qpat_assum `state_rel c l1 l2 x t [] locs`
           (assume_tac o REWRITE_RULE [state_rel_thm])
  \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
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
    \\ `i <= i' <=> w1 <= w2` by
          (fs [integerTheory.INT_LE_LT,WORD_LESS_OR_EQ] \\ NO_TAC)
    \\ fs [WORD_NOT_LESS,intLib.COOPER_PROVE ``~(i < j) <=> j <= i:int``]
    \\ simp [word_less_lemma1]
    \\ IF_CASES_TAC \\ fs []
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
    \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
    \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [])
    \\ match_mp_tac (GEN_ALL memory_rel_zero_space)
    \\ metis_tac [])
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
  \\ fs [wordSemTheory.add_ret_loc_def]
  \\ fs [dataLangTheory.op_requires_names_def,
         dataLangTheory.op_space_reset_def]
  \\ TOP_CASE_TAC THEN1
   (Cases_on `names_opt` \\ fs []
    \\ fs [cut_state_opt_def,cut_state_def]
    \\ Cases_on `dataSem$cut_env x' s.locals` \\ fs []
    \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` assume_tac
    \\ rpt_drule0 cut_env_IMP_cut_env
    \\ CCONTR_TAC \\ fs [get_names_def]
    \\ fs [wordSemTheory.cut_env_def,SUBSET_DEF])
  \\ fs []
  \\ qpat_abbrev_tac `t1 = wordSem$call_env _ _`
  \\ first_x_assum (qspecl_then [`t1`,`l`,`n`] mp_tac)
  \\ impl_tac THEN1
   (unabbrev_all_tac
    \\ fs [wordSemTheory.call_env_def,wordSemTheory.push_env_def,
           wordSemTheory.dec_clock_def]
    \\ pairarg_tac \\ fs []
    \\ fs [fromList2_def,lookup_insert]
    \\ fs [state_rel_def,code_rel_def,stubs_def]
    \\ fs [memory_rel_def,word_ml_inv_def,heap_in_memory_store_def]
    \\ fs [dimword_LESS_MustTerminate_limit]
    \\ rpt strip_tac \\ simp [] \\ NO_TAC)
  \\ strip_tac \\ fs []
  \\ `?t2. pop_env t1 = SOME t2 /\ domain t2.locals = domain x'` by
   (unabbrev_all_tac
    \\ fs [wordSemTheory.call_env_def,wordSemTheory.push_env_def,
           wordSemTheory.pop_env_def] \\ pairarg_tac \\ fs []
    \\ imp_res_tac env_to_list_lookup_equiv
    \\ fs [domain_lookup,EXTENSION,lookup_fromAList] \\ NO_TAC)
  \\ fs []
  \\ fs [lookup_insert,word_cmp_NotLess_word_cmp_res]
  \\ rw [] \\ fs []
  \\ unabbrev_all_tac
  \\ fs [wordSemTheory.pop_env_def,wordSemTheory.call_env_def,
         wordSemTheory.push_env_def,wordSemTheory.dec_clock_def]
  \\ pairarg_tac \\ fs [] \\ rveq \\ fs []
  \\ simp [state_rel_thm]
  \\ fs [lookup_insert]
  \\ rpt_drule0 env_to_list_cut_env_IMP \\ fs []
  \\ disch_then kall_tac
  \\ fs [lookup_insert,FAPPLY_FUPDATE_THM,adjust_var_11,FLOOKUP_UPDATE]
  \\ fs [inter_insert_ODD_adjust_set]
  \\ fs [wordSemTheory.cut_env_def] \\ rveq
  \\ conj_tac
  \\ TRY (fs [lookup_inter,lookup_insert,adjust_set_def,fromAList_def] \\ NO_TAC)
  \\ `domain (adjust_set (get_names names_opt)) SUBSET domain t.locals` by
   (Cases_on `names_opt` \\ fs [get_names_def]
    \\ fs [SUBSET_DEF,domain_lookup]
    \\ rw [] \\ res_tac \\ fs []
    \\ rveq \\ fs [lookup_ODD_adjust_set] \\ NO_TAC)
  \\ `domain (adjust_set x.locals) SUBSET
      domain (inter t.locals (adjust_set (get_names names_opt)))` by
   (fs [SUBSET_DEF,domain_lookup,lookup_inter_alt] \\ rw []
    \\ Cases_on `names_opt` \\ fs [get_names_def]
    \\ fs [SUBSET_DEF,domain_lookup]
    \\ fs [cut_state_opt_def,cut_state_def,cut_env_def]
    \\ qpat_x_assum `_ = SOME x` mp_tac
    \\ IF_CASES_TAC \\ fs [] \\ rw [] \\ fs [adjust_set_inter]
    \\ fs [lookup_inter_alt,domain_lookup] \\ NO_TAC)
  \\ `!n. IS_SOME (lookup n x.locals) ==>
          n ∈ domain (get_names names_opt) /\
          IS_SOME (lookup (adjust_var n) t.locals)` by
   (qx_gen_tac `k` \\ disch_then assume_tac
    \\ Cases_on `lookup k x.locals` \\ fs []
    \\ Cases_on `names_opt` \\ fs [get_names_def]
    \\ fs [SUBSET_DEF,domain_lookup]
    \\ fs [cut_state_opt_def,cut_state_def,cut_env_def]
    \\ qpat_x_assum `_ = SOME x` mp_tac
    \\ IF_CASES_TAC \\ fs [] \\ rw [] \\ fs [adjust_set_inter]
    \\ fs [lookup_inter_alt,domain_lookup] \\ NO_TAC)
  \\ conj_tac
  \\ TRY (rw [] \\ once_rewrite_tac [lookup_inter_alt]
          \\ fs [lookup_insert,adjust_var_IN_adjust_set] \\ NO_TAC)
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs [inter_insert_ODD_adjust_set_alt]
  \\ match_mp_tac (GEN_ALL memory_rel_zero_space)
  \\ qexists_tac `x.space`
  \\ TRY (match_mp_tac memory_rel_Boolv_T)
  \\ TRY (match_mp_tac memory_rel_Boolv_F) \\ fs []
  \\ qsuff_tac `inter (inter t.locals (adjust_set (get_names names_opt)))
                 (adjust_set x.locals) = inter t.locals (adjust_set x.locals)`
  \\ asm_simp_tac std_ss [] \\ fs []
  \\ fs [lookup_inter_alt,SUBSET_DEF]
  \\ rw [] \\ fs [domain_inter] \\ res_tac
QED

Theorem cut_env_IMP_domain:
   wordSem$cut_env x y = SOME t ==> domain t = domain x
Proof
  fs [wordSemTheory.cut_env_def] \\ rw []
  \\ fs [SUBSET_DEF,EXTENSION,domain_inter] \\ metis_tac []
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

Theorem MemEqList_thm = Q.prove(`
  !offset t xs dm m b a.
      word_mem_eq (a + offset) xs dm m = SOME b /\
      get_var 3 t = SOME (Word a) /\ dm = t.mdomain /\ m = t.memory ==>
      ?x. evaluate (MemEqList offset xs,t) =
            (NONE,t with locals := ((if b then insert 1 (Word 18w) else I) o
                                    (if xs <> [] then insert 5 x else I)) t.locals)`,
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
  \\ metis_tac [])
  |> Q.SPEC `0w` |> SIMP_RULE std_ss [WORD_ADD_0];

Theorem assign_EqualInt:
   (?i. op = EqualInt i) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ rveq \\ fs []
  \\ rpt_drule0 state_rel_cut_IMP \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_1] \\ clean_tac
  \\ fs [get_var_def]
  \\ fs [Boolv_def] \\ rveq \\ fs [GSYM Boolv_def]
  \\ qpat_assum `state_rel c l1 l2 x t [] locs`
           (assume_tac o REWRITE_RULE [state_rel_thm])
  \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ qmatch_asmsub_rename_tac `(Number j,a7)`
  \\ `?w. a7 = Word w` by
        (imp_res_tac memory_rel_any_Number_IMP \\ fs [] \\ NO_TAC)
  \\ rveq
  \\ rpt_drule0 memory_rel_Number_const_test
  \\ disch_then (qspec_then `i` mp_tac)
  \\ fs [assign_def,GSYM small_int_def]
  \\ IF_CASES_TAC THEN1
   (fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF] \\ fs [eq_eval]
    \\ Cases_on `i = j` \\ fs [] \\ rveq \\ fs []
    \\ fs [lookup_insert,state_rel_thm] \\ rpt strip_tac
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
    \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs []))
  \\ fs [] \\ TOP_CASE_TAC \\ fs []
  THEN1
   (fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF] \\ fs [eq_eval]
    \\ fs [lookup_insert,state_rel_thm] \\ rpt strip_tac
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
    \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs []))
  \\ fs [word_bit_test]
  \\ IF_CASES_TAC
  THEN1
   (fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF] \\ fs [eq_eval]
    \\ fs [lookup_insert,state_rel_thm] \\ rpt strip_tac
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
    \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs []))
  \\ strip_tac
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
  \\ qmatch_goalsub_abbrev_tac `(MemEqList 0w ws,t9)`
  \\ `word_mem_eq a ws t9.mdomain t9.memory = SOME (j = i)` by fs [Abbr`t9`,Abbr`ws`]
  \\ rpt_drule0 MemEqList_thm
  \\ impl_tac THEN1 fs [eq_eval,Abbr `t9`]
  \\ strip_tac \\ fs []
  \\ `ws <> []` by
     (fs [bignum_words_def,multiwordTheory.i2mw_def]
      \\ every_case_tac \\ fs [markerTheory.Abbrev_def] \\ fs [] \\ rveq \\ fs [])
  \\ fs []
  \\ IF_CASES_TAC \\ fs [] \\ rveq
  \\ unabbrev_all_tac
  \\ fs [lookup_insert,state_rel_thm] \\ rpt strip_tac
  \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def]
  \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
  \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [])
QED

Theorem Equal_code_lemma:
   (!c st dm m l v1 v2 t l1 l2 q1 q2 res l'.
      word_eq c st dm m l v1 v2 = SOME (res,l') /\
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
      good_dimindex (:'a) ==>
      ?ck new_p.
        evaluate (Equal_code c,t) =
          (SOME (Result (Loc l1 l2) (Word res)),
           t with <| clock := ck; locals := LN; permute := new_p |>) /\
        l' <= ck) /\
    (!c st dm m l w a1 a2 t l1 l2 res l'.
      word_eq_list c st dm m l w a1 a2 = SOME (res,l') /\
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
      c.len_size <> 0 /\
      c.len_size < dimindex (:α) /\
      good_dimindex (:'a) ==>
      ?ck new_p.
        evaluate (Equal1_code,t) =
          (SOME (Result (Loc l1 l2) (Word res)),
           t with <| clock := ck; locals := LN; permute := new_p |>) /\
        l' <= ck)
Proof
  ho_match_mp_tac word_eq_ind \\ reverse (rpt strip_tac) \\ rveq
  \\ qpat_x_assum `_ = SOME (res,_)` mp_tac
  \\ once_rewrite_tac [word_eq_def]
  THEN1
   (IF_CASES_TAC THEN1
     (fs [Equal1_code_def] \\ strip_tac \\ rveq
      \\ fs [eq_eval,list_Seq_def]
      \\ fs [wordSemTheory.state_component_equality])
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
    THEN1 (fs [wordSemTheory.cut_env_def,domain_lookup] \\ fs [])
    \\ qmatch_goalsub_abbrev_tac `(Equal_code c, t1)`
    \\ first_x_assum (qspecl_then [`t1`,`Equal1_location`,`1`] mp_tac)
    \\ impl_tac THEN1
     (unabbrev_all_tac \\ fs [lookup_insert,wordSemTheory.push_env_def]
      \\ pairarg_tac \\ fs [] \\ fs [eq_eval])
    \\ strip_tac \\ fs []
    \\ Cases_on `pop_env (t1 with <|permute := new_p; clock := ck|>)` \\ fs []
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
      \\ rveq \\ fs [lookup_inter_alt,lookup_insert]
      \\ rw [] \\ fs [lookup_def])
    \\ fs [] \\ imp_res_tac cut_env_IMP_domain \\ fs [eq_eval]
    \\ reverse IF_CASES_TAC THEN1
     (sg `F` \\ fs [] \\ pop_assum mp_tac \\ fs []
      \\ fs [EXTENSION] \\ rw [] \\ EQ_TAC \\ rw [])
    \\ pop_assum kall_tac \\ fs []
    \\ once_rewrite_tac [list_Seq_def]
    \\ Cases_on `x0 ≠ 1w` \\ fs [eq_eval]
    THEN1
     (rveq \\ fs []
      \\ unabbrev_all_tac
      \\ fs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def]
      \\ pairarg_tac \\ fs [] \\ rveq
      \\ fs [wordSemTheory.state_component_equality])
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
      \\ fs [wordSemTheory.state_component_equality,eq_eval])
    \\ strip_tac \\ fs []
    \\ rveq \\ fs []
    \\ unabbrev_all_tac
    \\ fs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def]
    \\ pairarg_tac \\ fs [] \\ rveq
    \\ fs [wordSemTheory.state_component_equality])
  \\ rewrite_tac [Equal_code_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ Cases_on `v1 = v2` \\ fs []
  THEN1
   (strip_tac \\ rveq \\ fs [eq_eval]
    \\ fs [wordSemTheory.state_component_equality])
  \\ ntac 2 (once_rewrite_tac [list_Seq_def])
  \\ fs [eq_eval]
  \\ fs [GSYM (SIMP_CONV (srw_ss()) [word_bit_test] ``~word_bit 0 (w && w1)``)]
  \\ fs [word_bit_and]
  \\ IF_CASES_TAC
  THEN1 (fs [] \\ rw [] \\ fs [] \\ fs [wordSemTheory.state_component_equality])
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
  \\ reverse IF_CASES_TAC
  THEN1
   (pop_assum kall_tac \\ fs []
    \\ fs [] \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
    \\ IF_CASES_TAC THEN1
     (fs [] \\ strip_tac \\ rw [] \\ fs []
      \\ fs [wordSemTheory.state_component_equality])
    \\ fs [] \\ rveq
    \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval,word_bit_test]
    \\ IF_CASES_TAC THEN1
     (fs [] \\ strip_tac \\ rw [] \\ fs []
      \\ fs [wordSemTheory.state_component_equality])
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
      \\ fs [wordSemTheory.state_component_equality])
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
    \\ fs [wordSemTheory.state_component_equality,Abbr`t9`])
  \\ fs []
  \\ qpat_abbrev_tac `other_case = list_Seq _`
  \\ pop_assum kall_tac
  \\ fs [word_is_clos_def]
  \\ strip_tac
  \\ ntac 2 (once_rewrite_tac [list_Seq_def]) \\ fs [eq_eval]
  \\ IF_CASES_TAC
  THEN1 (fs [] \\ rveq \\ fs [wordSemTheory.state_component_equality])
  \\ ntac 1 (once_rewrite_tac [list_Seq_def]) \\ fs [eq_eval]
  \\ IF_CASES_TAC
  THEN1 (fs [] \\ rveq \\ fs [wordSemTheory.state_component_equality])
  \\ fs []
  \\ ntac 1 (once_rewrite_tac [list_Seq_def]) \\ fs [eq_eval]
  \\ reverse IF_CASES_TAC
  THEN1 (fs [] \\ rveq \\ fs [wordSemTheory.state_component_equality])
  \\ fs []
  \\ ntac 4 (once_rewrite_tac [list_Seq_def]) \\ fs [eq_eval]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [eq_eval]
  \\ fs [GSYM decode_length_def,shift_lsl]
  \\ qmatch_goalsub_abbrev_tac `(Equal1_code,t8)`
  \\ first_x_assum (qspecl_then [`t8`,`l1`,`l2`] mp_tac)
  \\ impl_tac THEN1 (unabbrev_all_tac \\ fs [eq_eval])
  \\ strip_tac \\ fs []
  \\ fs [Abbr`t8`,wordSemTheory.state_component_equality]
QED

Theorem Equal_code_thm:
   memory_rel c be refs sp st m dm ((q1,Word v1)::(q2,Word v2)::vars) /\
    word_eq c st dm m l v1 v2 = SOME (res,l') /\
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
    good_dimindex (:'a) ==>
    ?ck new_p.
      evaluate (Equal_code c,t) =
        (SOME (Result (Loc l1 l2) (Word res)),
         t with <| clock := ck; locals := LN; permute := new_p |>) /\
      l' <= ck
Proof
  strip_tac
  \\ match_mp_tac (Equal_code_lemma |> CONJUNCT1)
  \\ fs [] \\ asm_exists_tac \\ fs []
QED

Theorem assign_Equal:
   op = Equal ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [get_var_def]
  \\ fs [Boolv_def] \\ rveq \\ fs [GSYM Boolv_def]
  \\ qpat_assum `state_rel c l1 l2 x t [] locs`
           (assume_tac o REWRITE_RULE [state_rel_thm])
  \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ rename1 `memory_rel _ _ _ _ _ _ _ ((h_1,a_1)::(h_2,a_2)::_)`
  \\ rpt_drule0 memory_rel_simple_eq
  \\ strip_tac \\ rveq \\ fs []
  \\ fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF]
  \\ fs [wordSemTheory.get_var_def]
  \\ fs [assign_def,list_Seq_def] \\ eval_tac
  \\ fs [lookup_insert,wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def,
         word_cmp_Test_1,word_bit_and]
  \\ IF_CASES_TAC THEN1
   (first_x_assum drule0 \\ pop_assum kall_tac \\ strip_tac
    \\ fs [lookup_insert,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def]
    \\ IF_CASES_TAC \\ fs []
    \\ fs [state_rel_thm]
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
    \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
    \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [])
    \\ match_mp_tac (GEN_ALL memory_rel_zero_space)
    \\ metis_tac [])
  \\ IF_CASES_TAC THEN1
   (fs [lookup_insert,asmTheory.word_cmp_def]
    \\ rpt_drule0 memory_rel_ptr_eq \\ rw [] \\ rveq \\ fs []
    \\ fs [state_rel_thm]
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
    \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
    \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [])
    \\ match_mp_tac (GEN_ALL memory_rel_zero_space)
    \\ metis_tac [])
  \\ fs []
  \\ rpt_drule0 word_eq_thm
  \\ strip_tac
  \\ rpt_drule0 (Equal_code_thm |> INST_TYPE [``:'b``|->``:'ffi``])
  \\ strip_tac
  \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def,lookup_insert,
         wordSemTheory.bad_dest_args_def,wordSemTheory.find_code_def]
  \\ `lookup Equal_location t.code = SOME (3,Equal_code c)` by
       (fs [state_rel_def,code_rel_def,stubs_def] \\ NO_TAC)
  \\ fs [wordSemTheory.add_ret_loc_def]
  \\ fs [dataLangTheory.op_requires_names_def,
         dataLangTheory.op_space_reset_def]
  \\ TOP_CASE_TAC THEN1
   (Cases_on `names_opt` \\ fs []
    \\ fs [cut_state_opt_def,cut_state_def]
    \\ Cases_on `dataSem$cut_env x' s.locals` \\ fs []
    \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` assume_tac
    \\ rpt_drule0 cut_env_IMP_cut_env
    \\ CCONTR_TAC \\ fs [get_names_def]
    \\ fs [wordSemTheory.cut_env_def,SUBSET_DEF])
  \\ fs []
  \\ qpat_abbrev_tac `t1 = wordSem$call_env _ _`
  \\ first_x_assum (qspecl_then [`t1`,`l`,`n`] mp_tac)
  \\ impl_tac THEN1
   (unabbrev_all_tac
    \\ fs [wordSemTheory.call_env_def,wordSemTheory.push_env_def,
           wordSemTheory.dec_clock_def]
    \\ pairarg_tac \\ fs []
    \\ fs [fromList2_def,lookup_insert]
    \\ fs [state_rel_def,code_rel_def,stubs_def]
    \\ fs [memory_rel_def,word_ml_inv_def,heap_in_memory_store_def])
  \\ strip_tac \\ fs []
  \\ `?t2. pop_env (t1 with <|permute := new_p; clock := ck|>) = SOME t2 /\
           domain t2.locals = domain x'` by
   (unabbrev_all_tac
    \\ fs [wordSemTheory.call_env_def,wordSemTheory.push_env_def,
           wordSemTheory.pop_env_def] \\ pairarg_tac \\ fs []
    \\ imp_res_tac env_to_list_lookup_equiv
    \\ fs [domain_lookup,EXTENSION,lookup_fromAList] \\ NO_TAC)
  \\ fs []
  \\ fs [lookup_insert,asmTheory.word_cmp_def] \\ rveq
  \\ rw [] \\ fs []
  \\ unabbrev_all_tac
  \\ fs [wordSemTheory.pop_env_def,wordSemTheory.call_env_def,
         wordSemTheory.push_env_def,wordSemTheory.dec_clock_def]
  \\ pairarg_tac \\ fs [] \\ rveq \\ fs []
  \\ simp [state_rel_thm]
  \\ fs [lookup_insert]
  \\ rpt_drule0 env_to_list_cut_env_IMP \\ fs []
  \\ disch_then kall_tac
  \\ fs [lookup_insert,FAPPLY_FUPDATE_THM,adjust_var_11,FLOOKUP_UPDATE]
  \\ fs [inter_insert_ODD_adjust_set]
  \\ fs [wordSemTheory.cut_env_def] \\ rveq
  \\ conj_tac
  \\ TRY (fs [lookup_inter,lookup_insert,adjust_set_def,fromAList_def] \\ NO_TAC)
  \\ `domain (adjust_set (get_names names_opt)) SUBSET domain t.locals` by
   (Cases_on `names_opt` \\ fs [get_names_def]
    \\ fs [SUBSET_DEF,domain_lookup]
    \\ rw [] \\ res_tac \\ fs []
    \\ rveq \\ fs [lookup_ODD_adjust_set] \\ NO_TAC)
  \\ `domain (adjust_set x.locals) SUBSET
      domain (inter t.locals (adjust_set (get_names names_opt)))` by
   (fs [SUBSET_DEF,domain_lookup,lookup_inter_alt] \\ rw []
    \\ Cases_on `names_opt` \\ fs [get_names_def]
    \\ fs [SUBSET_DEF,domain_lookup]
    \\ fs [cut_state_opt_def,cut_state_def,cut_env_def]
    \\ qpat_x_assum `_ = SOME x` mp_tac
    \\ IF_CASES_TAC \\ fs [] \\ rw [] \\ fs [adjust_set_inter]
    \\ fs [lookup_inter_alt,domain_lookup] \\ NO_TAC)
  \\ `!n. IS_SOME (lookup n x.locals) ==>
          n ∈ domain (get_names names_opt) /\
          IS_SOME (lookup (adjust_var n) t.locals)` by
   (qx_gen_tac `k` \\ disch_then assume_tac
    \\ Cases_on `lookup k x.locals` \\ fs []
    \\ Cases_on `names_opt` \\ fs [get_names_def]
    \\ fs [SUBSET_DEF,domain_lookup]
    \\ fs [cut_state_opt_def,cut_state_def,cut_env_def]
    \\ qpat_x_assum `_ = SOME x` mp_tac
    \\ IF_CASES_TAC \\ fs [] \\ rw [] \\ fs [adjust_set_inter]
    \\ fs [lookup_inter_alt,domain_lookup] \\ NO_TAC)
  \\ conj_tac
  \\ TRY (rw [] \\ once_rewrite_tac [lookup_inter_alt]
          \\ fs [lookup_insert,adjust_var_IN_adjust_set] \\ NO_TAC)
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs [inter_insert_ODD_adjust_set_alt]
  \\ match_mp_tac (GEN_ALL memory_rel_zero_space)
  \\ qexists_tac `x.space`
  \\ TRY (match_mp_tac memory_rel_Boolv_T)
  \\ TRY (match_mp_tac memory_rel_Boolv_F) \\ fs []
  \\ qsuff_tac `inter (inter t.locals (adjust_set (get_names names_opt)))
                 (adjust_set x.locals) = inter t.locals (adjust_set x.locals)`
  \\ asm_simp_tac std_ss [] \\ fs []
  \\ fs [lookup_inter_alt,SUBSET_DEF]
  \\ rw [] \\ fs [domain_inter] \\ res_tac
QED

Theorem assign_WordOpW8:
   (?opw. op = WordOp W8 opw) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app]
  \\ every_case_tac \\ fs[]
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
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
  \\ Cases_on`opw` \\ simp[] \\ eval_tac \\ fs[lookup_insert]
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
  ``assign c n l dest (WordOp W64 opw) [e1; e2] names_opt``
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
  \\ fs [WordOp64_on_32_def,semanticPrimitivesPropsTheory.opw_lookup_def,
         list_Seq_def]
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
    \\ AP_THM_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC
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
  \\ AP_THM_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC
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

Theorem assign_WordOpW64:
   (?opw. op = WordOp W64 opw) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app]
  \\ every_case_tac \\ fs[]
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
  \\ clean_tac
  \\ simp[state_rel_thm] \\ eval_tac
  \\ fs[state_rel_thm] \\ eval_tac
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
  \\ Cases_on `dimindex (:'a) = 64` \\ simp [] THEN1
   (TOP_CASE_TAC \\ fs [] \\ clean_tac
    \\ eval_tac
    \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
    \\ rpt_drule0 get_var_get_real_addr_lemma
    \\ qpat_x_assum `get_var (adjust_var e2) t =
         SOME (Word (get_addr c ptr (Word 0w)))` assume_tac
    \\ rpt_drule0 get_var_get_real_addr_lemma
    \\ qpat_abbrev_tac`sow = word_op_CASE opw _ _ _ _ _`
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
  \\ `dimindex (:'a) = 32` by rfs [good_dimindex_def] \\ fs [] \\ rveq
  \\ eval_tac
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
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
  \\ assume_tac evaluate_WordOp64_on_32 \\ rfs []
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
  \\ disch_then (qspec_then `opw_lookup opw c' c''` mp_tac)
  \\ simp []
  \\ impl_tac
  THEN1 (fs [consume_space_def,good_dimindex_def] \\ rw [] \\ fs [])
  \\ strip_tac \\ fs []
  \\ fs[FAPPLY_FUPDATE_THM]
  \\ fs [consume_space_def]
  \\ rveq \\ fs [] \\ rw [] \\ fs [code_oracle_rel_def,FLOOKUP_UPDATE]
QED

Theorem assign_WordShiftW8:
   (?sh n. op = WordShift W8 sh n) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app]
  \\ every_case_tac \\ fs[]
  \\ clean_tac
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
  \\ qhdtm_x_assum`$some`mp_tac
  \\ DEEP_INTRO_TAC some_intro \\ fs[]
  \\ strip_tac \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ simp[state_rel_thm] \\ eval_tac
  \\ fs[state_rel_thm] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs[] \\ strip_tac
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
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
    \\ simp[lookup_insert]
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
    \\ simp[lookup_insert]
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
    \\ simp[lookup_insert]
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
    \\ fs [lookup_insert,adjust_var_11] \\ rw []
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
      \\ once_rewrite_tac [GSYM (MATCH_MP MOD_PLUS (DECIDE ``0<8n``))]
      \\ drule0 (DECIDE ``n < 8n ==> n=0 \/ n=1 \/ n=2 \/ n=3 \/
                                    n=4 \/ n=5 \/ n=6 \/ n=7``)
      \\ strip_tac \\ fs []
      \\ drule0 (DECIDE ``n < 8n ==> n=0 \/ n=1 \/ n=2 \/ n=3 \/
                                    n=4 \/ n=5 \/ n=6 \/ n=7``)
      \\ strip_tac \\ fs [w2w]))
QED

val assign_WordShift64 =
  ``assign c n l dest (WordShift W64 sh n) [e1] names_opt``
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
      \\ once_rewrite_tac [GSYM (MATCH_MP MOD_PLUS (DECIDE ``0<64n``))]
      \\ qabbrev_tac `nn = n MOD 64` \\ fs []
      \\ simp [GSYM SUB_MOD])
    THEN1
     (Cases_on `i + n MOD 64 < 32` \\ fs [w2w,fcpTheory.FCP_BETA]
      \\ once_rewrite_tac [GSYM (MATCH_MP MOD_PLUS (DECIDE ``0<64n``))]
      \\ qabbrev_tac `nn = n MOD 64` \\ fs [])
    THEN1
     (Cases_on `i + n MOD 64 < 64` \\ fs [w2w,fcpTheory.FCP_BETA]
      \\ once_rewrite_tac [DECIDE ``i+(n+32)=(i+32)+n:num``]
      \\ once_rewrite_tac [GSYM (MATCH_MP MOD_PLUS (DECIDE ``0<64n``))]
      \\ `n MOD 64 < 64` by fs []
      \\ qabbrev_tac `nn = n MOD 64` \\ fs []
      \\ simp [GSYM SUB_MOD])
    THEN1
     (Cases_on `i + n MOD 64 < 64` \\ fs [w2w,fcpTheory.FCP_BETA]
      \\ once_rewrite_tac [GSYM (MATCH_MP MOD_PLUS (DECIDE ``0<64n``))]
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
   (?sh n. op = WordShift W64 sh n) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app]
  \\ every_case_tac \\ fs[]
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
  \\ clean_tac
  \\ simp[assign_def]
  \\ TOP_CASE_TAC \\ fs[]
  \\ TOP_CASE_TAC \\ fs[]
  THEN1 (* dimindex (:'a) = 64 *)
   (`dimindex (:'a) = 64` by fs [state_rel_def,good_dimindex_def]
    \\ fs [] \\ clean_tac
    \\ fs[state_rel_thm] \\ eval_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ strip_tac
    \\ fs[wordSemTheory.get_vars_def]
    \\ qpat_x_assum`_ = SOME [_]`mp_tac
    \\ TOP_CASE_TAC \\ fs[] \\ strip_tac \\ clean_tac
    \\ rpt_drule0 evaluate_LoadWord64
    \\ rfs[good_dimindex_def] \\ rfs[]
    \\ disch_then drule0
    \\ simp[list_Seq_def]
    \\ simp[Once wordSemTheory.evaluate_def]
    \\ disch_then kall_tac
    \\ simp[Once wordSemTheory.evaluate_def]
    \\ simp[Once wordSemTheory.evaluate_def,word_exp_set_var_ShiftVar]
    \\ eval_tac
    \\ qmatch_goalsub_abbrev_tac`OPTION_MAP Word opt`
    \\ `∃w. opt = SOME w`
    by ( simp[Abbr`opt`] \\ CASE_TAC \\ simp[] )
    \\ qunabbrev_tac`opt` \\ simp[]
    \\ qhdtm_x_assum`memory_rel`kall_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,GSYM join_env_locals_def]
    \\ assume_tac(GEN_ALL evaluate_WriteWord64)
    \\ SEP_I_TAC "evaluate" \\ fs[]
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
    \\ qmatch_abbrev_tac`memory_rel c be refs sp' st' m' md vars'`
    \\ qmatch_assum_abbrev_tac`memory_rel c be refs sp' st' m' md vars''`
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
    >-
     (simp[fcpTheory.CART_EQ]
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
  \\ fs [inter_insert_ODD_adjust_set_alt]
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
  \\ qpat_x_assum `code_oracle_rel _ _ _ _ _ _ _ _` mp_tac
  \\ rpt (pop_assum kall_tac)
  \\ fs [code_oracle_rel_def,FLOOKUP_UPDATE]
QED

val assign_FP_cmp = SIMP_CONV (srw_ss()) [assign_def]
  ``((assign (c:data_to_word$config) (secn:num) (l:num) (dest:num) (FP_cmp fpc)
       (args:num list) (names:num_set option)):'a wordLang$prog # num)``;

val assign_FP_top = SIMP_CONV (srw_ss()) [assign_def]
  ``((assign (c:data_to_word$config) (secn:num) (l:num) (dest:num) (FP_top fpt)
       (args:num list) (names:num_set option)):'a wordLang$prog # num)``;

val assign_FP_bop = SIMP_CONV (srw_ss()) [assign_def]
  ``((assign (c:data_to_word$config) (secn:num) (l:num) (dest:num) (FP_bop fpb)
       (args:num list) (names:num_set option)):'a wordLang$prog # num)``;

val assign_FP_uop = SIMP_CONV (srw_ss()) [assign_def]
  ``((assign (c:data_to_word$config) (secn:num) (l:num) (dest:num) (FP_uop fpu)
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

val fp_greater = prove(
  ``fp64_greaterThan a b = fp64_lessThan b a /\
    fp64_greaterEqual a b = fp64_lessEqual b a``,
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
                realTheory.REAL_LT_TOTAL,word1_cases]);

Theorem assign_FP_cmp:
   (?fpc. op = FP_cmp fpc) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac state_rel_cut_IMP \\ pop_assum mp_tac
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app]
  \\ every_case_tac \\ fs[]
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
  \\ clean_tac
  \\ fs[state_rel_thm] \\ eval_tac
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
  \\ TOP_CASE_TAC THEN1 fs []
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
           fpSemTheory.fp_cmp_def]
    \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
    \\ fs [lookup_insert,adjust_var_11]
    \\ conj_tac \\ TRY (rw [] \\ NO_TAC)
    \\ fs [] \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
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
         fpSemTheory.fp_cmp_def,extract_append_id]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
  \\ fs [lookup_insert,adjust_var_11]
  \\ rpt (disch_then kall_tac)
  \\ conj_tac \\ TRY (rw [] \\ NO_TAC)
  \\ fs [] \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert
  \\ fs [inter_insert_ODD_adjust_set_alt,fp_greater]
  \\ rw [] \\ fs [WORD_MUL_LSL]
  \\ TRY (match_mp_tac memory_rel_Boolv_T)
  \\ TRY (match_mp_tac memory_rel_Boolv_F)
  \\ fs []
QED

Theorem assign_FP_top:
  (?fpt. op = FP_top fpt) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac state_rel_cut_IMP \\ pop_assum mp_tac
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app]
  \\ every_case_tac \\ fs[]
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_3]
  \\ clean_tac
  \\ fs[state_rel_thm] \\ eval_tac
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
  \\ TOP_CASE_TAC THEN1 fs []
  \\ Cases_on `dimindex (:'a) = 64` \\ simp [] THEN1
   (TOP_CASE_TAC \\ fs [] \\ clean_tac
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
           fpSemTheory.fp_top_def]
    \\ assume_tac(GEN_ALL evaluate_WriteWord64)
    \\ SEP_I_TAC "evaluate" \\ fs[]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,GSYM join_env_locals_def]
    \\ first_x_assum drule0
    \\ simp[wordSemTheory.get_var_def]
    \\ fs[lookup_insert,good_dimindex_def,consume_space_def]
    \\ strip_tac
    \\ clean_tac \\ fs[]
    \\ conj_tac \\ TRY (rw [] \\ NO_TAC)
    \\ fs [FAPPLY_FUPDATE_THM] \\ rfs [w2w_w2w_64, fpSemTheory.fpfma_def]
    \\ rpt_drule0 memory_rel_less_space
    \\ disch_then match_mp_tac \\ fs [])
  \\ TOP_CASE_TAC \\ fs []
  \\ `dimindex (:'a) = 32` by rfs [good_dimindex_def] \\ fs [] \\ rveq
  \\ eval_tac
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
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
         fpSemTheory.fp_top_def,WORD_MUL_LSL]
  \\ rpt (disch_then kall_tac)
  \\ assume_tac(GEN_ALL evaluate_WriteWord64_on_32)
  \\ SEP_I_TAC "evaluate" \\ fs[]
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
QED

Theorem assign_FP_bop:
   (?fpb. op = FP_bop fpb) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac state_rel_cut_IMP \\ pop_assum mp_tac
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app]
  \\ every_case_tac \\ fs[]
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
  \\ clean_tac
  \\ fs[state_rel_thm] \\ eval_tac
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
  \\ TOP_CASE_TAC THEN1 fs []
  \\ Cases_on `dimindex (:'a) = 64` \\ simp [] THEN1
   (TOP_CASE_TAC \\ fs [] \\ clean_tac
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
           fpSemTheory.fp_bop_def]
    \\ assume_tac(GEN_ALL evaluate_WriteWord64)
    \\ SEP_I_TAC "evaluate" \\ fs[]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,GSYM join_env_locals_def]
    \\ first_x_assum drule0
    \\ simp[wordSemTheory.get_var_def]
    \\ fs[lookup_insert,good_dimindex_def,consume_space_def]
    \\ strip_tac
    \\ clean_tac \\ fs[]
    \\ conj_tac \\ TRY (rw [] \\ NO_TAC)
    \\ fs [FAPPLY_FUPDATE_THM] \\ rfs [w2w_w2w_64]
    \\ rpt_drule0 memory_rel_less_space
    \\ disch_then match_mp_tac \\ fs [])
  \\ TOP_CASE_TAC \\ fs []
  \\ `dimindex (:'a) = 32` by rfs [good_dimindex_def] \\ fs [] \\ rveq
  \\ eval_tac
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
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
         fpSemTheory.fp_bop_def,WORD_MUL_LSL]
  \\ rpt (disch_then kall_tac)
  \\ assume_tac(GEN_ALL evaluate_WriteWord64_on_32)
  \\ SEP_I_TAC "evaluate" \\ fs[]
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
QED

Theorem assign_FP_uop:
   (?fpu. op = FP_uop fpu) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac state_rel_cut_IMP \\ pop_assum mp_tac
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs[do_app]
  \\ every_case_tac \\ fs[]
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_1]
  \\ clean_tac
  \\ fs[state_rel_thm] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ fs[wordSemTheory.get_vars_def]
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ drule0 memory_rel_Word64_IMP \\ fs []
  \\ strip_tac
  \\ clean_tac \\ rfs []
  \\ simp [assign_FP_uop]
  \\ TOP_CASE_TAC THEN1 fs []
  \\ Cases_on `dimindex (:'a) = 64` \\ simp [] THEN1
   (TOP_CASE_TAC \\ fs [] \\ clean_tac
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
           fpSemTheory.fp_uop_def,fp_uop_inst_def]
    \\ assume_tac(GEN_ALL evaluate_WriteWord64)
    \\ SEP_I_TAC "evaluate" \\ fs[]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,GSYM join_env_locals_def]
    \\ first_x_assum drule0
    \\ simp[wordSemTheory.get_var_def]
    \\ fs[lookup_insert,good_dimindex_def,consume_space_def]
    \\ strip_tac
    \\ clean_tac \\ fs[]
    \\ conj_tac \\ TRY (rw [] \\ NO_TAC)
    \\ fs [FAPPLY_FUPDATE_THM] \\ rfs [w2w_w2w_64]
    \\ rpt_drule0 memory_rel_less_space
    \\ disch_then match_mp_tac \\ fs [])
  \\ TOP_CASE_TAC \\ fs []
  \\ `dimindex (:'a) = 32` by rfs [good_dimindex_def] \\ fs [] \\ rveq
  \\ eval_tac
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ qpat_x_assum `get_var (adjust_var e1) t =
       SOME (Word (get_addr c _ (Word 0w)))` assume_tac
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ Cases_on `fpu` \\ fs [fp_bop_inst_def]
  \\ rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.inst_def,wordSemTheory.get_var_def,lookup_insert,
         wordSemTheory.set_fp_var_def,wordSemTheory.get_fp_var_def,
         FLOOKUP_UPDATE,wordSemTheory.set_var_def,w2w_select_id,
         fpSemTheory.fp_bop_def,WORD_MUL_LSL,
         fpSemTheory.fp_uop_def,fp_uop_inst_def]
  \\ rpt (disch_then kall_tac)
  \\ assume_tac(GEN_ALL evaluate_WriteWord64_on_32)
  \\ SEP_I_TAC "evaluate" \\ fs[]
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
QED

Theorem assign_Label:
   (?lab. op = Label lab) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ fs [assign_def] \\ fs [do_app]
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
  \\ rw [] \\ fs [] \\ rw [] \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ match_mp_tac memory_rel_CodePtr \\ fs []
QED

Theorem do_app_Ref:
   do_app Ref vals x =
    case consume_space (LENGTH vals + 1) x of
      NONE => Rerr (Rabort Rtype_error)
    | SOME s1 =>
      Rval
      (RefPtr (LEAST ptr. ptr ∉ FDOM s1.refs),
         s1 with
             refs := (s1.refs |+ ((LEAST ptr. ptr ∉ FDOM s1.refs),ValueArray vals)))
Proof
  fs [do_app] \\ Cases_on `vals` \\ fs [LET_THM]
QED

Theorem assign_Ref:
   op = Ref ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  \\ fs [assign_def] \\ fs [do_app_Ref]
  \\ Cases_on `consume_space (LENGTH vals + 1) x` \\ fs [] \\ rveq
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ clean_tac
  \\ fs [consume_space_def] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ TOP_CASE_TAC \\ fs []
  \\ simp [state_rel_thm] \\ eval_tac
  \\ fs [state_rel_thm] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs [NOT_LESS,DECIDE ``n + 1 <= m <=> n < m:num``]
  \\ strip_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ qabbrev_tac `new = LEAST ptr. ptr ∉ FDOM x.refs`
  \\ `new ∉ FDOM x.refs` by metis_tac [LEAST_NOTIN_FDOM]
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
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ fs [make_ptr_def]
  \\ `TriggerGC <> EndOfHeap` by fs []
  \\ pop_assum (fn th => fs [MATCH_MP FUPDATE_COMMUTES th])
QED

Theorem assign_Update:
   op = Update ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  \\ fs [do_app] \\ every_case_tac \\ fs [] \\ clean_tac
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
  \\ rw [] \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ match_mp_tac memory_rel_Unit \\ fs []
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
  \\ rw [] \\ fs []
QED

Theorem assign_Deref:
   op = Deref ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  \\ fs [do_app] \\ every_case_tac \\ fs [] \\ clean_tac
  \\ fs [INT_EQ_NUM_LEMMA] \\ clean_tac
  \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_2] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [assign_def] \\ eval_tac \\ fs [state_rel_thm]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs []
  \\ imp_res_tac get_vars_2_IMP \\ fs []
  \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_2] \\ clean_tac
  \\ imp_res_tac get_vars_2_IMP \\ fs [] \\ strip_tac
  \\ drule0 (memory_rel_Deref |> GEN_ALL) \\ fs []
  \\ strip_tac \\ clean_tac
  \\ `word_exp t (real_offset c (adjust_var a2)) = SOME (Word y) /\
      word_exp t (real_addr c (adjust_var a1)) = SOME (Word x)` by
        metis_tac [get_real_offset_lemma,get_real_addr_lemma]
  \\ fs [] \\ eval_tac
  \\ fs [lookup_insert,adjust_var_11]
  \\ rw [] \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
  \\ fs [] \\ rw [] \\ fs []
QED

Theorem assign_UpdateByte:
   op = UpdateByte ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs[]
  \\ fs[do_app] \\ every_case_tac \\ fs[] \\ clean_tac
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_3] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_3] \\ clean_tac
  \\ imp_res_tac get_vars_3_IMP
  \\ fs [] \\ rveq
  \\ fs[] \\ rveq
  \\ fs[state_rel_thm,set_var_def]
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
  \\ fs[inter_insert_ODD_adjust_set]
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
   op = DerefByte ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs[]
  \\ fs[do_app] \\ every_case_tac \\ fs[] \\ clean_tac
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2] \\ clean_tac
  \\ imp_res_tac get_vars_2_IMP
  \\ fs[state_rel_thm,set_var_def]
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
  \\ fs[inter_insert_ODD_adjust_set]
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

Theorem assign_El:
   op = El ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  \\ fs [do_app] \\ every_case_tac \\ fs [] \\ clean_tac
  \\ fs [INT_EQ_NUM_LEMMA] \\ clean_tac
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
  \\ `word_exp t (real_offset c (adjust_var a2)) = SOME (Word y) /\
      word_exp t (real_addr c (adjust_var a1)) = SOME (Word x)` by
        metis_tac [get_real_offset_lemma,get_real_addr_lemma]
  \\ fs [] \\ eval_tac
  \\ fs [lookup_insert,adjust_var_11]
  \\ rw [] \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
  \\ fs [] \\ rw [] \\ fs []
QED

Theorem assign_Const:
   (?i. op = Const i) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ fs [do_app] \\ every_case_tac \\ fs []
  \\ rpt var_eq_tac
  \\ fs [assign_def]
  \\ Cases_on `i` \\ fs []
  \\ fs [wordSemTheory.evaluate_def,wordSemTheory.word_exp_def]
  \\ fs [state_rel_def,wordSemTheory.set_var_def,set_var_def,
        lookup_insert,adjust_var_11]
  \\ rw [] \\ fs []
  \\ asm_exists_tac \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac word_ml_inv_insert \\ fs []
  \\ TRY (match_mp_tac word_ml_inv_zero) \\ fs []
  \\ TRY (match_mp_tac word_ml_inv_num) \\ fs []
  \\ TRY (match_mp_tac word_ml_inv_neg_num) \\ fs []
QED

Theorem assign_GlobalsPtr:
   op = GlobalsPtr ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ fs [do_app] \\ every_case_tac \\ fs []
  \\ rpt var_eq_tac
  \\ fs [assign_def]
  \\ fs[wordSemTheory.evaluate_def,wordSemTheory.word_exp_def]
  \\ fs [state_rel_def]
  \\ fs [the_global_def,libTheory.the_def]
  \\ fs [FLOOKUP_DEF,wordSemTheory.set_var_def,lookup_insert,
         adjust_var_11,libTheory.the_def,set_var_def]
  \\ rw [] \\ fs []
  \\ asm_exists_tac \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac word_ml_inv_insert \\ fs []
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
  \\ fs [] \\ rw [] \\ fs []
QED

Theorem assign_SetGlobalsPtr:
   op = SetGlobalsPtr ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ fs [do_app] \\ every_case_tac \\ fs []
  \\ rpt var_eq_tac
  \\ fs [assign_def]
  \\ imp_res_tac get_vars_SING \\ fs []
  \\ `args <> []` by (strip_tac \\ fs [dataSemTheory.get_vars_def])
  \\ fs[wordSemTheory.evaluate_def,wordSemTheory.word_exp_def,Unit_def]
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ Cases_on `ws` \\ fs [LENGTH_NIL] \\ rpt var_eq_tac
  \\ pop_assum (fn th => assume_tac th THEN mp_tac th)
  \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def]
  \\ every_case_tac \\ fs [] \\ rpt var_eq_tac
  \\ fs [state_rel_def,wordSemTheory.set_var_def,lookup_insert,
         adjust_var_11,libTheory.the_def,set_var_def,
         wordSemTheory.set_store_def,code_oracle_rel_def,FLOOKUP_UPDATE]
  \\ rpt_drule0 heap_in_memory_store_IMP_UPDATE
  \\ disch_then (qspec_then `h` assume_tac)
  \\ rw [] \\ fs []
  \\ asm_exists_tac \\ fs [the_global_def,libTheory.the_def]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (GEN_ALL word_ml_inv_get_vars_IMP)
  \\ disch_then drule0
  \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def]
  \\ strip_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac word_ml_inv_insert \\ fs []
  \\ match_mp_tac word_ml_inv_Unit
  \\ pop_assum mp_tac \\ fs []
  \\ match_mp_tac word_ml_inv_rearrange \\ rw [] \\ fs []
QED

Theorem IMP:
   b1 \/ b2 <=> ~b1 ==> b2
Proof
  Cases_on `b1` \\ Cases_on `b2` \\ fs []
QED

val memcopy_def = Define `
  memcopy k a1 a2 m dm =
    if k = 0n then SOME m else
      if a1 IN dm /\ a2 IN dm then
        memcopy (k-1) (a1+bytes_in_word) (a2+bytes_in_word) ((a2 =+ m a1) m) dm
      else NONE`

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
      evaluate (MemCopy_code,s) =
        (SOME (Result (Loc l1 l2) ret_val),
         s with <| clock := s.clock - k ;
                   memory := m1 ; locals := LN |>)
Proof
  ntac 3 gen_tac
  \\ Induct \\ simp [Once memcopy_def]
  \\ rw [] \\ simp [MemCopy_code_def] \\ fs [eq_eval]
  THEN1 (fs [wordSemTheory.state_component_equality])
  \\ ntac 5 (once_rewrite_tac [list_Seq_def])
  \\ fs [eq_eval,wordSemTheory.mem_store_def]
  \\ fs [list_Seq_def,eq_eval]
  \\ fs [MULT_CLAUSES,GSYM word_add_n2w]
  \\ qmatch_goalsub_abbrev_tac `(MemCopy_code,s5)`
  \\ first_x_assum (qspecl_then [`a1 + bytes_in_word`,
      `a2 + bytes_in_word`,`s5`] mp_tac)
  \\ qunabbrev_tac `s5` \\ fs [lookup_insert,ADD1]
QED

val assign_ConsExtend = save_thm("assign_ConsExtend",
  ``assign c n l dest (ConsExtend tag) args names_opt``
  |> SIMP_CONV (srw_ss()) [assign_def])

Theorem get_vars_IMP_domain:
   !xs s y.
      get_vars xs s = SOME y ==>
      EVERY (\x. x IN domain s) xs
Proof
  Induct \\ fs [get_vars_SOME_IFF_data_eq] \\ rw []
  \\ fs [get_var_def,domain_lookup]
QED

Theorem memory_rel_IMP_free_space:
   memory_rel c be refs sp st m dm vars ==>
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
      memory_rel c be refs n st m dm vars /\
      store_list nfree ws2 m dm = SOME m1 /\
      FLOOKUP st NextFree = SOME (Word nfree) /\ LENGTH ws2 <= n ==>
      memory_rel c be refs n st m1 dm vars
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

Theorem cut_env_adjust_set_insert_ODD:
   ODD n ==> cut_env (adjust_set the_names) (insert n w s) =
              cut_env (adjust_set the_names) s
Proof
  reverse (rw [wordSemTheory.cut_env_def] \\ fs [SUBSET_DEF])
  \\ res_tac \\ fs []
  THEN1 (rveq \\ fs [domain_lookup,lookup_adjust_set]
         \\ every_case_tac \\ fs [])
  \\ fs [lookup_inter_alt,lookup_insert]
  \\ rw [] \\ pop_assum mp_tac
  \\ simp [domain_lookup,lookup_adjust_set]
  \\ rw [] \\ fs []
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
   memory_rel c s1.be x.refs sp s1.store m1 s1.mdomain
      ((Block ts' n' l',Word w_ptr)::(ZIP (ys7,ws1) ++ vars)) /\
    startptr < LENGTH l' /\ LENGTH ys7 = LENGTH ws1 /\ good_dimindex (:α) /\
    lookup (adjust_var a1) s1.locals = SOME (Word (w_ptr:'a word)) /\
    word_exp s1 (real_addr c (adjust_var a1)) = SOME (Word wx) ==>
    memory_rel c s1.be x.refs sp s1.store m1 s1.mdomain
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
  !len startptr m1 m2 ws1 ys7 k.
      memory_rel c s1.be x.refs sp s1.store m1 s1.mdomain
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
        memory_rel c s1.be x.refs sp s1.store m2 s1.mdomain
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
  \\ `memory_rel c s1.be x.refs sp s1.store m4 s1.mdomain
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

Theorem assign_ConsExtend:
   (?tag. op = ConsExtend tag) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [do_app] \\ every_case_tac \\ fs [] \\ rveq
  \\ `?startptr len. i = &startptr /\ i' = & len` by
       (Cases_on `i` \\ Cases_on `i'` \\ fs [] \\ NO_TAC) \\ rveq \\ fs [with_fresh_ts_state]
  \\ pop_assum mp_tac
  \\ fs [integerTheory.int_gt,integerTheory.INT_ADD,NOT_LESS]
  \\ fs [IMP] \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ clean_tac
  \\ `?a1 a2 a3 a4 arest. args = a1::a2::a3::a4::arest` by
   (Cases_on `args` \\ fs []
    \\ rpt (rename1 `LENGTH args = _` \\ Cases_on `args` \\ fs []) \\ NO_TAC)
  \\ rveq \\ fs []
  \\ rewrite_tac [assign_ConsExtend] \\ fs []
  \\ CASE_TAC THEN1 fs [] \\ fs []
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ fs [get_vars_SOME_IFF_eq] \\ rveq \\ fs []
  \\ rpt_drule0 evaluate_BignumHalt
  \\ rename1 `LENGTH t7 = LENGTH ys7`
  \\ `?w4. get_var (adjust_var a4) t = SOME (Word w4) /\
           (~(w4 ' 0) ==> small_int (:α) (&(len + LENGTH t7)) /\
                          w4 = Smallnum (&(len + LENGTH t7)))` by
   (fs [state_rel_thm] \\ eval_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ fs [wordSemTheory.get_vars_def]
    \\ rename1 `get_var (adjust_var a4) t = SOME x4`
    \\ ntac 3 (strip_tac \\ drule0 memory_rel_tl)
    \\ strip_tac
    \\ drule0 (memory_rel_any_Number_IMP |> ONCE_REWRITE_RULE [CONJ_COMM])
    \\ fs [] \\ strip_tac \\ rveq \\ fs [] \\ strip_tac
    \\ imp_res_tac memory_rel_Number_IMP \\ rfs [] \\ NO_TAC)
  \\ disch_then drule0 \\ strip_tac \\ fs []
  \\ Cases_on `w4 ' 0` THEN1 (fs []) \\ fs []
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
    \\ fs [EVAL ``op_space_reset (ConsExtend tag)``]
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
  \\ reverse (Cases_on `res`) THEN1 (fs []) \\ fs []
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
        memory_rel c s1.be x.refs (len + (LENGTH ys3 + 1)) s1.store
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
    \\ qpat_x_assum `memory_rel _ _ _ _ _ _ _ _` kall_tac
    \\ rpt strip_tac
    \\ qpat_x_assum `memory_rel _ _ _ _ _ _ _ _` mp_tac \\ rfs []
    \\ match_mp_tac memory_rel_rearrange
    \\ rw [] \\ fs [] \\ NO_TAC)
  \\ fs []
  \\ `10 < dimindex (:'a)` by (fs [labPropsTheory.good_dimindex_def] \\ NO_TAC)
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
       (fs [labPropsTheory.good_dimindex_def,shift_def] \\ NO_TAC)
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
    \\ fs [EVAL ``op_requires_names (ConsExtend tag)``]
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
   (once_rewrite_tac [list_Seq_def] \\ simp [eq_eval,with_fresh_ts_state_eq]
    \\ fs [state_rel_thm,FAPPLY_FUPDATE_THM,lookup_insert,adjust_var_11]
    \\ fs [inter_insert_ODD_adjust_set,code_oracle_rel_def,FLOOKUP_UPDATE]
    \\ conj_tac THEN1 (rw [] \\ fs [])
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
      (Cases_on `names_opt` \\ fs [EVAL ``op_requires_names (ConsExtend tag)``])
  \\ rveq \\ fs [get_names_def,cut_state_opt_def]
  \\ `lookup MemCopy_location s1.code = SOME (5,MemCopy_code)` by
     (qpat_x_assum `code_rel c _ _` mp_tac
      \\ simp [code_rel_def,stubs_def])
  \\ `s1.termdep <> 0` by
   (imp_res_tac wordSemTheory.evaluate_clock \\ fs []
    \\ unabbrev_all_tac \\ fs [])
  \\ fs [eq_eval] \\ pop_assum kall_tac
  \\ fs [cut_env_adjust_set_insert_ODD]
  \\ `?the_env. cut_env (adjust_set the_names) s1.locals = SOME the_env` by
   (simp [wordSemTheory.cut_env_def,domain_lookup,SUBSET_DEF,
          lookup_adjust_set]
    \\ rpt strip_tac
    \\ rename1 `(if (name = _) then _ else _) = _`
    \\ Cases_on `name = 0` \\ fs []
    \\ fs [ODD_EVEN]
    \\ rpt_drule0 IMP_adjust_var
    \\ disch_then (fn th => once_rewrite_tac [GSYM th])
    \\ fs [INTRO_IS_SOME]
    \\ first_x_assum match_mp_tac
    \\ fs [cut_env_def,cut_state_def] \\ rveq
    \\ Cases_on `domain the_names ⊆ domain s.locals` \\ fs [] \\ rveq \\ fs []
    \\ fs [lookup_inter_alt]
    \\ fs [SUBSET_DEF,domain_lookup] \\ res_tac \\ fs []
    \\ qsuff_tac `((name − 2) DIV 2) IN domain nms`
    THEN1 (fs [domain_lookup] \\ rw [] \\ fs [])
    \\ fs [domain_list_insert,Abbr `nms`] \\ fs [domain_lookup])
  \\ fs [] \\ simp [wordSemTheory.push_env_def]
  \\ Cases_on `env_to_list the_env s1.permute` \\ fs []
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
              memory_rel c s1.be x.refs (len + (LENGTH ys3 + 1)) s1.store m2
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
    \\ fs [eq_eval,FLOOKUP_UPDATE])
  \\ rpt_drule0 MemCopy_thm
  \\ disch_then (qspecl_then [`ar8`,`n`,`l`,`s88`] mp_tac)
  \\ impl_tac THEN1
   (unabbrev_all_tac \\ fs [wordSemTheory.get_var_def,lookup_insert]
    \\ match_mp_tac LESS_EQ_TRANS
    \\ qexists_tac `dimword (:α)`
    \\ conj_tac THEN1 (fs [dimword_def,good_dimindex_def] \\ rfs [])
    \\ fs [wordSemTheory.MustTerminate_limit_def])
  \\ strip_tac \\ fs [with_fresh_ts_state_eq] \\ pop_assum kall_tac
  \\ qunabbrev_tac `s88` \\ fs [wordSemTheory.pop_env_def]
  \\ `domain (fromAList q) = domain the_env` by
   (drule0 env_to_list_lookup_equiv
    \\ fs [EXTENSION,domain_lookup,lookup_fromAList]) \\ fs []
  \\ fs [state_rel_thm,code_oracle_rel_def,FLOOKUP_UPDATE]
  \\ conj_tac THEN1
   (drule0 env_to_list_lookup_equiv
    \\ fs [lookup_insert,lookup_fromAList]
    \\ fs [wordSemTheory.cut_env_def] \\ rveq
    \\ rpt strip_tac \\ qpat_x_assum `!x._` imp_res_tac
    \\ fs [cut_state_def,cut_env_def] \\ rveq
    \\ simp [lookup_inter_alt,ZERO_IN_adjust_set])
  \\ conj_tac THEN1
   (drule0 env_to_list_lookup_equiv
    \\ fs [lookup_insert,lookup_fromAList,adjust_var_11]
    \\ rw [] \\ rw [] \\ fs []
    \\ fs [wordSemTheory.cut_env_def] \\ rveq \\ res_tac
    \\ fs [cut_state_def,cut_env_def] \\ rveq
    \\ Cases_on `domain the_names ⊆ domain s.locals` \\ fs [] \\ rveq
    \\ fs [] \\ fs [lookup_inter_alt,adjust_var_IN_adjust_set]
    \\ rw [] \\ fs [])
  \\ simp [FAPPLY_FUPDATE_THM]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
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
    \\ fs [lookup_inter_alt] \\ rw []
    \\ sg `F` \\ fs [] \\ pop_assum mp_tac \\ simp []
    \\ qpat_x_assum `_ IN _` mp_tac
    \\ fs [IN_domain_adjust_set_inter])
  \\ fs [] \\ pop_assum kall_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 memory_rel_Cons_alt
  \\ disch_then (qspecl_then [`with_fresh_ts (x with space := 0) K`,
                              `tag`,`full_header`] mp_tac)
  \\ reverse impl_tac
  THEN1 fs [shift_lsl,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [Abbr `tot_len`] \\ CCONTR_TAC \\ fs [DROP_NIL]
QED

Theorem assign_Cons:
   (?tag. op = Cons tag) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ Cases_on `LENGTH args = 0` THEN1
   (fs [assign_def] \\ IF_CASES_TAC \\ fs []
    \\ fs [LENGTH_NIL] \\ rpt var_eq_tac
    \\ fs [do_app] \\ every_case_tac \\ fs [with_fresh_ts_state]
    \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
    \\ TRY (Cases_on `vals`) \\ fs [] \\ clean_tac
    \\ eval_tac \\ clean_tac
    \\ fs [state_rel_def,lookup_insert,adjust_var_11,with_fresh_ts_state_eq]
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
  \\ fs [do_app] \\ every_case_tac \\ fs []
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ clean_tac
  \\ fs [consume_space_def] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ simp [state_rel_thm] \\ eval_tac
  \\ fs [state_rel_thm] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs [NOT_LESS,DECIDE ``n + 1 <= m <=> n < m:num``]
  \\ strip_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ `vals <> [] /\ (LENGTH vals = LENGTH ws)` by fs []
  \\ rpt_drule0 memory_rel_Cons1
  \\ fs [with_fresh_ts_state] \\ rveq \\ fs [with_fresh_ts_state_eq]
  \\ qpat_abbrev_tac `x5 = with_fresh_ts (x with space := _) K`
  \\ strip_tac
  \\ pop_assum (assume_tac o Q.SPEC `x5`)
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
         code_oracle_rel_def,FLOOKUP_UPDATE]
  \\ rw [] \\ fs [] \\ rw [] \\ fs []
  \\ fs [inter_insert_ODD_adjust_set]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ fs [make_cons_ptr_def,get_lowerbits_def]
QED

Theorem assign_FFI:
   (?n. op = FFI n) ==> ^assign_thm_goal
Proof
  (* (* new proof *) *)
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ fs[do_app] \\ clean_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2] \\ clean_tac
  \\ fs [bvlSemTheory.Unit_def] \\ rveq
  \\ fs [GSYM bvlSemTheory.Unit_def] \\ rveq
  \\ imp_res_tac get_vars_2_imp
  \\ fs[state_rel_thm,set_var_def]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP )
  \\ strip_tac
  \\ fs[get_vars_def]
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ rpt_drule0 memory_rel_ByteArray_IMP
  \\ drule0 memory_rel_tl \\ strip_tac
  \\ rpt_drule0 memory_rel_ByteArray_IMP
  \\ pop_assum kall_tac
  \\ ntac 2 strip_tac \\ clean_tac
  \\ simp[assign_def,list_Seq_def] \\ eval_tac
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (Word _)`
     (fn thm => rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ simp[]
  \\ rename1`_ ∧ ffi_name = ""`
  \\ Cases_on`¬c.call_empty_ffi ∧ ffi_name = ""`
  >- (
    fs[wordSemTheory.evaluate_def]
    \\ ntac 2 strip_tac
    \\ simp[Unit_def,wordSemTheory.word_exp_def]
    \\ conj_tac
    >- (
      qhdtm_x_assum`call_FFI`mp_tac
      \\ simp[ffiTheory.call_FFI_def] )
    \\ simp[wordSemTheory.set_var_def,lookup_insert]
    \\ conj_tac >- (rw[] \\ metis_tac[])
    >> full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert
    >> full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ match_mp_tac memory_rel_Unit
    \\ DEP_REWRITE_TAC[FUPDATE_ELIM]
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
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (WORD _)`
     (fn thm=> rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ `tt.store = t.store` by simp[Abbr`tt`]
  \\ simp[]
  \\ qpat_abbrev_tac`ex1 = if ffi_name = "" then _ else _`
  \\ qpat_abbrev_tac`ex2 = if ffi_name = "" then _ else _`
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
  \\ qpat_x_assum `get_var _ _ = SOME (WORD _)`
     (fn thm=> rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ `ttt.store = t.store` by simp[Abbr`ttt`]
  \\ simp[]
  \\ qunabbrev_tac`ex1`
  \\ qunabbrev_tac`ex2`
  \\ Cases_on`ffi_name = ""` \\ fs[]
  >- (
    eval_tac
    \\ fs[lookup_insert,wordSemTheory.word_exp_def,ffiTheory.call_FFI_def]
    \\ fs[read_bytearray_def,wordSemTheory.write_bytearray_def]
    \\ fs[cut_env_adjust_set_insert_ODD]
    \\ fs[wordSemTheory.cut_env_def] \\ clean_tac
    \\ reverse IF_CASES_TAC >- (
      `F` suffices_by rw[]
      >> pop_assum mp_tac
      >> fs[cut_state_opt_def]
      >> drule0 (#1(EQ_IMP_RULE cut_state_eq_some))
      >> strip_tac
      >> clean_tac
      >> rw[SUBSET_DEF,domain_lookup]
      >> fs[dataSemTheory.cut_env_def]
      >> clean_tac >> fs[]
      >> Cases_on`x=0` >- metis_tac[]
      >> qmatch_assum_abbrev_tac`lookup x ss = SOME _`
      >> `x ∈ domain ss` by metis_tac[domain_lookup]
      >> qunabbrev_tac`ss`
      >> imp_res_tac domain_adjust_set_EVEN
      >> `∃z. x = adjust_var z`
      by (
          simp[adjust_var_def]
          \\ fs[EVEN_EXISTS]
          \\ Cases_on`m` \\ fs[ADD1,LEFT_ADD_DISTRIB] )
      >> rveq
      >> fs[lookup_adjust_var_adjust_set_SOME_UNIT]
      >> last_x_assum(qspec_then`z`mp_tac)
      >> simp[lookup_inter]
      >> fs[IS_SOME_EXISTS]
      >> disch_then match_mp_tac
      >> BasicProvers.CASE_TAC
      >> fs[SUBSET_DEF,domain_lookup]
      >> res_tac >> fs[])
    \\ fs[]
    \\ qmatch_goalsub_abbrev_tac`read_bytearray aa len g`
    \\ qmatch_asmsub_rename_tac`LENGTH ls + 3`
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
    \\ ntac 6 strip_tac
    \\ conj_tac >- fs[adjust_set_def,domain_fromAList]
    \\ simp[adjust_var_IN_adjust_set]
    \\ conj_tac >- (
      rw[] \\
      fs[cut_state_opt_def] \\
      fs[cut_state_eq_some] \\
      clean_tac \\
      fs[cut_env_def] \\ clean_tac \\
      simp[lookup_inter_alt] )
    >> full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ DEP_REWRITE_TAC[FUPDATE_ELIM]
    \\ conj_tac >- fs[FLOOKUP_DEF]
    \\ match_mp_tac memory_rel_insert
    >> full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ match_mp_tac memory_rel_Unit \\ fs[]
    \\ match_mp_tac (MP_CANON (GEN_ALL memory_rel_rearrange))
    \\ qmatch_asmsub_abbrev_tac `memory_rel _ _ _ _ _ _ _ (join_env a1 a2 ++ a3)`
    \\ qexists_tac `join_env a1 a2 ++ a3`
    \\ reverse conj_tac >- metis_tac[memory_rel_zero_space]
    \\ rpt strip_tac >> unabbrev_all_tac
    \\ fs[MEM_APPEND]
    \\ fs[join_env_def,MEM_MAP,PULL_EXISTS,MEM_FILTER,MEM_toAList,EXISTS_PROD,lookup_inter_alt]
    \\ metis_tac[])
  \\ eval_tac
  \\ qpat_abbrev_tac`tttt = t with locals := _`
  \\ `get_var (adjust_var e1) tttt = get_var (adjust_var e1) t`
  by fs[Abbr`tttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ `get_var (adjust_var e2) tttt = get_var (adjust_var e2) t`
  by fs[Abbr`tttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ rfs[]
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
  \\ `get_var (adjust_var e2) tttt = get_var (adjust_var e2) t`
  by fs[Abbr`ttttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ qpat_x_assum`¬_` kall_tac
  \\ rfs[]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (WORD _)`
     (fn thm=> rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ `ttttt.store = t.store` by simp[Abbr`ttttt`]
  \\ simp[]
  \\ simp[wordSemTheory.get_var_def,lookup_insert]
  \\ qmatch_goalsub_abbrev_tac`read_bytearray aa len g`
  \\ qmatch_asmsub_rename_tac`LENGTH ls + 3`
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
  \\ qispl_then[`l''`,`LENGTH l''`,`aa2`]mp_tac IMP_read_bytearray_GENLIST
  \\ impl_tac >- simp[]
  \\ `len2 = LENGTH l''`
  by (
    simp[Abbr`len2`]
    \\ rfs[good_dimindex_def] \\ rfs[shift_def]
    \\ simp[bytes_in_word_def,GSYM word_add_n2w]
    \\ simp[dimword_def] )
  \\ fs[]
  \\ rpt strip_tac
  \\ simp[Unit_def]
  \\ eval_tac
  \\ simp[lookup_insert]
  \\ fs[wordSemTheory.cut_env_def] \\ clean_tac
  \\ simp[lookup_inter,lookup_insert,lookup_adjust_var_adjust_set]
  \\ IF_CASES_TAC
     >- (fs[adjust_set_def,lookup_fromAList,cut_state_opt_def,cut_state_def,cut_env_def]
         >> Cases_on `domain x' ⊆ domain s.locals` >> fs[]
         >> fs[domain_fromAList,MAP_MAP_o,o_DEF,pairTheory.ELIM_UNCURRY,adjust_var_def,
               lookup_insert,lookup_inter,lookup_fromAList]
         >> fs[Q.prove(`!(n:num). 2 * n + 2 ≠ 7`, intLib.COOPER_TAC),
               Q.prove(`!(n:num). 2 * n + 2 ≠ 5`, intLib.COOPER_TAC),
               Q.prove(`!(n:num). 2 * n + 2 ≠ 3`, intLib.COOPER_TAC),
               Q.prove(`!(n:num). 2 * n + 2 ≠ 1`, intLib.COOPER_TAC)]
         >> `!(n:num). 2 * n + 2 ≠ 7` by intLib.COOPER_TAC
         >> fs[]
         >> conj_tac
            >- (rpt strip_tac
                >> IF_CASES_TAC >> fs[IS_SOME_EXISTS]
                >> qmatch_asmsub_abbrev_tac `set st ⊆ _`
                >> `7 ∉ set st`
                   by(fs[Abbr `st`,MEM_MAP] >> rpt strip_tac >> DISJ1_TAC >> intLib.COOPER_TAC)
                   >> drule0 SUBSET_INSERT_EQ_SUBSET >> disch_then (fn thm => fs[thm])
                >> pop_assum kall_tac
                >> `5 ∉ set st`
                   by(fs[Abbr `st`,MEM_MAP] >> rpt strip_tac >> DISJ1_TAC >> intLib.COOPER_TAC)
                >> drule0 SUBSET_INSERT_EQ_SUBSET >> disch_then (fn thm => fs[thm])
                >> pop_assum kall_tac
                >> `3 ∉ set st`
                   by(fs[Abbr `st`,MEM_MAP] >> rpt strip_tac >> DISJ1_TAC >> intLib.COOPER_TAC)
                >> drule0 SUBSET_INSERT_EQ_SUBSET >> disch_then (fn thm => fs[thm])
                >> pop_assum kall_tac
                >> `1 ∉ set st`
                   by(fs[Abbr `st`,MEM_MAP] >> rpt strip_tac >> DISJ1_TAC >> intLib.COOPER_TAC)
                >> drule0 SUBSET_INSERT_EQ_SUBSET >> disch_then (fn thm => fs[thm])
                >> pop_assum kall_tac
                >> rveq >> fs[state_component_equality,lookup_inter]
                >> Cases_on `lookup n s.locals` >> fs[]
                >> Cases_on `lookup n x'` >> fs[]
                >> `2 * n + 2 ∈ set st`
                   by(fs[Abbr `st`,MEM_MAP]
                      >> qexists_tac `(n,())`
                      >> fs[MEM_toAList])
                >> `(2 * n + 2) ∈ domain t.locals` by metis_tac[SUBSET_DEF]
                >> fs[domain_lookup]
                >> TOP_CASE_TAC >> fs[ALOOKUP_NONE,MAP_MAP_o,o_DEF] >> fs[MEM_MAP]
                >> pop_assum(qspec_then `(n,())` assume_tac) >> fs[MEM_toAList])
            >> fs[SIMP_RULE std_ss
                            [adjust_set_def,adjust_var_def,pairTheory.ELIM_UNCURRY]
                            inter_insert_ODD_adjust_set_alt]
            >> full_simp_tac std_ss [GSYM APPEND_ASSOC]
            >> match_mp_tac (SIMP_RULE std_ss [adjust_set_def,adjust_var_def,
                                               pairTheory.ELIM_UNCURRY]
                                       memory_rel_insert)
            >> fs[]
            >> match_mp_tac (SIMP_RULE std_ss [adjust_set_def,adjust_var_def,
                                               pairTheory.ELIM_UNCURRY]
                                       memory_rel_Unit)
            >> fs[]
            >> rename1 `call_FFI _ _ _ l'' = FFI_return _ r'`
            >> `LENGTH r' = LENGTH l''`
            by (
             qhdtm_x_assum`call_FFI`mp_tac
             \\ simp[ffiTheory.call_FFI_def]
             \\ rpt(pop_assum kall_tac)
             \\ every_case_tac \\ rpt strip_tac \\ fs[])
            >> qmatch_asmsub_abbrev_tac`((RefPtr n''',Word w)::vars)`
            >> `∀n. n ≤ LENGTH l'' ⇒
              let new_m = write_bytearray (aa2 + n2w (LENGTH l'' - n)) (DROP (LENGTH l'' - n) r') t.memory t.mdomain t.be in
              memory_rel c t.be (x.refs |+ (n''',ByteArray F (TAKE (LENGTH l'' - n) l'' ++ DROP (LENGTH l'' - n) r'))) x.space t.store
                new_m t.mdomain ((RefPtr n''',Word w)::vars) ∧
              (∀i v. i < LENGTH l'' ⇒
                memory_rel c t.be (x.refs |+ (n''',ByteArray F (LUPDATE v i (TAKE (LENGTH l'' - n) l'' ++ DROP (LENGTH l'' - n) r'))))
                  x.space t.store
                  ((byte_align (aa2 + n2w i) =+
                    Word (set_byte (aa2 + n2w i) v
                           (theWord (new_m (byte_align (aa2 + n2w i)))) t.be)) new_m)
                   t.mdomain ((RefPtr n''',Word w)::vars))`
          by (
            Induct \\ simp[]
            >- (
              first_x_assum (mp_tac o GSYM)
              \\ simp[DROP_LENGTH_NIL_rwt,wordSemTheory.write_bytearray_def]
              \\ qpat_abbrev_tac`refs = x.refs |+ _`
              \\ `refs = x.refs`
              by(
                simp[Abbr`refs`,FLOOKUP_EXT,FUN_EQ_THM,FLOOKUP_UPDATE]
                \\ rw[] \\ rw[]
                \\ qpat_x_assum `_ = SOME (ByteArray F _)` mp_tac \\ fs[]
                \\ rw[]
                )
              \\ rw[]
              >- (qpat_x_assum `memory_rel _ _ _ _ _ _ _ (_ :: _ :: _)` mp_tac
                 \\ rw[] \\ drule0 memory_rel_tl \\ simp[])
              \\ first_x_assum drule0
              \\ simp[]
              )
            \\ strip_tac \\ fs[]
            \\ qpat_abbrev_tac`ls2 = TAKE _ _ ++ _`
            \\ qmatch_asmsub_abbrev_tac`ByteArray F ls1`
            \\ `ls2 = LUPDATE (EL (LENGTH l'' - SUC n) r') (LENGTH l'' - SUC n) ls1`
            by (
              simp[Abbr`ls1`,Abbr`ls2`,LIST_EQ_REWRITE,EL_APPEND_EQN,EL_LUPDATE,DROP_def,TAKE_def]
              \\ rw[] \\ fs[] \\ simp[EL_TAKE,HD_DROP,EL_DROP] )
            \\ qunabbrev_tac`ls2` \\ fs[]
            \\ qmatch_goalsub_abbrev_tac`EL i r'`
            \\ `i < LENGTH l''` by simp[Abbr`i`]
            \\ first_x_assum(qspecl_then[`i`,`EL i r'`]mp_tac)
            \\ impl_tac >- rw[]
            \\ `DROP i r' = EL i r'::DROP(LENGTH l'' - n)r'`
            by (
              Cases_on`r'` \\ fs[Abbr`i`]
              \\ simp[LIST_EQ_REWRITE,ADD1,EL_DROP,EL_CONS,PRE_SUB1]
              >- rfs[]
              \\ Induct \\ rw[ADD1]
              \\ simp[EL_DROP]
              \\ `x'' + LENGTH l'' - n = SUC(x'' + LENGTH l'' - (n+1))` by decide_tac
              \\ pop_assum (CHANGED_TAC o SUBST1_TAC)
              \\ simp[EL] \\ NO_TAC)
            \\ first_assum SUBST1_TAC
            \\ qpat_abbrev_tac`wb = write_bytearray _ (_ :: _) _ _ _`
            \\ qpat_abbrev_tac `wb1 = write_bytearray _ _ _ _ _`
            \\ qpat_abbrev_tac`wb2 = _ wb1`
            \\ `wb2 = wb`
            by (
              simp[Abbr`wb2`,Abbr`wb`,wordSemTheory.write_bytearray_def]
              \\ `aa2 + n2w i + 1w = aa2 + n2w (LENGTH l'' - n)`
              by(
                simp[Abbr`i`,ADD1]
                \\ REWRITE_TAC[GSYM WORD_ADD_ASSOC]
                \\ AP_TERM_TAC
                \\ simp[word_add_n2w] )
              \\ pop_assum SUBST_ALL_TAC \\ simp[]
              \\ simp[wordSemTheory.mem_store_byte_aux_def]
              \\ last_x_assum drule0
              \\ simp[Abbr`g`,wordSemTheory.mem_load_byte_aux_def]
              \\ BasicProvers.TOP_CASE_TAC \\ simp[] \\ strip_tac
              \\ qmatch_assum_rename_tac`t.memory _ = Word v`
              \\ `∃v. wb1 (byte_align (aa2 + n2w i)) = Word v`
              by (
                `isWord (wb1 (byte_align (aa2 + n2w i)))`
                suffices_by (metis_tac[isWord_def,wordSemTheory.word_loc_nchotomy])
                \\ simp[Abbr`wb1`]
                \\ match_mp_tac write_bytearray_isWord
                \\ simp[isWord_def] )
              \\ simp[theWord_def] )
            \\ qunabbrev_tac`wb2`
            \\ pop_assum SUBST_ALL_TAC
            \\ strip_tac
            \\ conj_tac >- first_assum ACCEPT_TAC
            \\ drule0 (GEN_ALL memory_rel_ByteArray_IMP)
            \\ simp[FLOOKUP_UPDATE]
            \\ strip_tac
            \\ `LENGTH l'' = LENGTH ls1`
            by ( qunabbrev_tac `ls1` \\ fs[] )
            \\ metis_tac[] )
          \\ first_x_assum(qspec_then`LENGTH l''`mp_tac)
          \\ simp[Abbr `vars`] \\ strip_tac
          \\ match_mp_tac(GEN_ALL memory_rel_zero_space)
          \\ qexists_tac `x.space`
          \\ drule0 memory_rel_tl \\ match_mp_tac memory_rel_rearrange
          \\ simp[join_env_def,MEM_MAP,PULL_EXISTS,MEM_FILTER,MEM_toAList,EXISTS_PROD,lookup_inter_alt]
          \\ rw[] \\ rw[] \\ metis_tac[])
   >> `F` suffices_by rw[]
   >> pop_assum mp_tac
   >> fs[cut_state_opt_def]
   >> drule0 (#1(EQ_IMP_RULE cut_state_eq_some))
   >> strip_tac
   >> clean_tac
   >> simp[wordSemTheory.cut_env_def]
   >> rw[SUBSET_DEF,domain_lookup]
   >> fs[dataSemTheory.cut_env_def]
   >> clean_tac >> fs[]
   >> Cases_on`x=0` >- metis_tac[]
   >> qmatch_assum_abbrev_tac`lookup x ss = SOME _`
   >> `x ∈ domain ss` by metis_tac[domain_lookup]
   >> qunabbrev_tac`ss`
   >> imp_res_tac domain_adjust_set_EVEN
   >> `∃z. x = adjust_var z`
   by (
       simp[adjust_var_def]
       \\ fs[EVEN_EXISTS]
       \\ Cases_on`m` \\ fs[ADD1,LEFT_ADD_DISTRIB] )
   >> rveq
   >> fs[lookup_adjust_var_adjust_set_SOME_UNIT]
   >> last_x_assum(qspec_then`z`mp_tac)
   >> simp[lookup_inter]
   >> fs[IS_SOME_EXISTS]
   >> disch_then match_mp_tac
   >> BasicProvers.CASE_TAC
   >> fs[SUBSET_DEF,domain_lookup]
   >> res_tac >> fs[]
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
     (q = SOME NotEnoughSpace ==> r.ffi = t.ffi) /\
     (q <> SOME NotEnoughSpace ==> r.ffi = t.ffi /\ q = SOME(FinalFFI f))
Proof
  (* (* new proof *) *)
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ fs[do_app] \\ clean_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2] \\ clean_tac
  \\ fs [bvlSemTheory.Unit_def] \\ rveq
  \\ fs [GSYM bvlSemTheory.Unit_def] \\ rveq
  \\ imp_res_tac get_vars_2_imp
  \\ fs[state_rel_thm,set_var_def]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP )
  \\ strip_tac
  \\ fs[get_vars_def]
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ rpt_drule0 memory_rel_ByteArray_IMP
  \\ drule0 memory_rel_tl \\ strip_tac
  \\ rpt_drule0 memory_rel_ByteArray_IMP
  \\ pop_assum kall_tac
  \\ ntac 2 strip_tac \\ clean_tac
  \\ simp[assign_def,list_Seq_def] \\ eval_tac
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (Word _)`
     (fn thm => rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ simp[]
  \\ rename1`_ ∧ ffi_name = ""`
  \\ Cases_on`ffi_name = ""`
  >- (
    fs[wordSemTheory.evaluate_def]
    \\ ntac 2 strip_tac
    \\ simp[Unit_def,wordSemTheory.word_exp_def]
    \\ rveq
    \\ qhdtm_x_assum`call_FFI`mp_tac
    \\ simp[ffiTheory.call_FFI_def])
  \\ pop_assum (SUBST_ALL_TAC o EQF_INTRO)
  \\ rewrite_tac[]
  \\ eval_tac
  \\ qpat_abbrev_tac`tt = t with locals := _`
  \\ `get_var (adjust_var e1) tt = get_var (adjust_var e1) t`
  by fs[Abbr`tt`,wordSemTheory.get_var_def,lookup_insert]
  \\ `get_var (adjust_var e2) tt = get_var (adjust_var e2) t`
  by fs[Abbr`tt`,wordSemTheory.get_var_def,lookup_insert]
  \\ rfs[]
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
  \\ qpat_x_assum `get_var _ _ = SOME (WORD _)`
     (fn thm=> rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ `ttt.store = t.store` by simp[Abbr`ttt`]
  \\ simp[]
  \\ eval_tac
  \\ qpat_abbrev_tac`tttt = t with locals := _`
  \\ `get_var (adjust_var e1) tttt = get_var (adjust_var e1) t`
  by fs[Abbr`tttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ `get_var (adjust_var e2) tttt = get_var (adjust_var e2) t`
  by fs[Abbr`tttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ rfs[]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (WORD _)`
     (fn thm=> rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ `tttt.store = t.store` by simp[Abbr`tttt`]
  \\ simp[]
  \\ simp[]
  \\ qpat_abbrev_tac`ttttt = t with locals := _`
  \\ `get_var (adjust_var e1) ttttt = get_var (adjust_var e1) t`
  by fs[Abbr`ttttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ `get_var (adjust_var e2) tttt = get_var (adjust_var e2) t`
  by fs[Abbr`ttttt`,wordSemTheory.get_var_def,lookup_insert]
  \\ qpat_x_assum`¬_` kall_tac
  \\ rfs[]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ qpat_x_assum `get_var _ _ = SOME (WORD _)`
     (fn thm=> rpt_drule0 get_var_get_real_addr_lemma >> assume_tac thm)
  \\ `ttttt.store = t.store` by simp[Abbr`ttttt`]
  \\ simp[]
  \\ simp[wordSemTheory.get_var_def,lookup_insert]
  \\ qmatch_goalsub_abbrev_tac`read_bytearray aa len g`
  \\ qmatch_asmsub_rename_tac`LENGTH ls + 3`
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
  \\ qispl_then[`l''`,`LENGTH l''`,`aa2`]mp_tac IMP_read_bytearray_GENLIST
  \\ impl_tac >- simp[]
  \\ `len2 = LENGTH l''`
  by (
    simp[Abbr`len2`]
    \\ rfs[good_dimindex_def] \\ rfs[shift_def]
    \\ simp[bytes_in_word_def,GSYM word_add_n2w]
    \\ simp[dimword_def] )
  \\ fs[]
  \\ rpt strip_tac
  \\ simp[Unit_def]
  \\ eval_tac
  \\ simp[lookup_insert]
  \\ fs[wordSemTheory.cut_env_def] \\ clean_tac
  \\ simp[lookup_inter,lookup_insert,lookup_adjust_var_adjust_set]
  \\ IF_CASES_TAC
     >- (fs[adjust_set_def,lookup_fromAList,cut_state_opt_def,cut_state_def,cut_env_def]
         >> Cases_on `domain x' ⊆ domain s.locals` >> fs[]
         >> fs[domain_fromAList,MAP_MAP_o,o_DEF,pairTheory.ELIM_UNCURRY,adjust_var_def,
               lookup_insert,lookup_inter,lookup_fromAList]
         >> fs[Q.prove(`!(n:num). 2 * n + 2 ≠ 7`, intLib.COOPER_TAC),
               Q.prove(`!(n:num). 2 * n + 2 ≠ 5`, intLib.COOPER_TAC),
               Q.prove(`!(n:num). 2 * n + 2 ≠ 3`, intLib.COOPER_TAC),
               Q.prove(`!(n:num). 2 * n + 2 ≠ 1`, intLib.COOPER_TAC)]
         >> `!(n:num). 2 * n + 2 ≠ 7` by intLib.COOPER_TAC
         >> fs[]
         >> unabbrev_all_tac >> fs[state_component_equality])
   >> `F` suffices_by rw[]
   >> pop_assum mp_tac
   >> fs[cut_state_opt_def]
   >> drule0 (#1(EQ_IMP_RULE cut_state_eq_some))
   >> strip_tac
   >> clean_tac
   >> simp[wordSemTheory.cut_env_def]
   >> rw[SUBSET_DEF,domain_lookup]
   >> fs[dataSemTheory.cut_env_def]
   >> clean_tac >> fs[]
   >> Cases_on`x=0` >- metis_tac[]
   >> qmatch_assum_abbrev_tac`lookup x ss = SOME _`
   >> `x ∈ domain ss` by metis_tac[domain_lookup]
   >> qunabbrev_tac`ss`
   >> imp_res_tac domain_adjust_set_EVEN
   >> `∃z. x = adjust_var z`
   by (
       simp[adjust_var_def]
       \\ fs[EVEN_EXISTS]
       \\ Cases_on`m` \\ fs[ADD1,LEFT_ADD_DISTRIB] )
   >> rveq
   >> fs[lookup_adjust_var_adjust_set_SOME_UNIT]
   >> last_x_assum(qspec_then`z`mp_tac)
   >> simp[lookup_inter]
   >> fs[IS_SOME_EXISTS]
   >> disch_then match_mp_tac
   >> BasicProvers.CASE_TAC
   >> fs[SUBSET_DEF,domain_lookup]
   >> res_tac >> fs[]
QED

Theorem assign_thm:
   ^assign_thm_goal
Proof
  Cases_on `op = AllocGlobal` \\ fs []
  THEN1 (fs [do_app] \\ every_case_tac \\ fs [])
  \\ Cases_on `?i. op = Global i` \\ fs []
  THEN1 (fs [do_app] \\ every_case_tac \\ fs [])
  \\ Cases_on `?i. op = SetGlobal i` \\ fs []
  THEN1 (fs [do_app] \\ every_case_tac \\ fs [])
  \\ Cases_on `op = Greater` \\ fs []
  THEN1 (fs [do_app] \\ every_case_tac \\ fs [])
  \\ Cases_on `op = GreaterEq` \\ fs []
  THEN1 (fs [do_app] \\ every_case_tac \\ fs [])
  \\ map_every (fn th =>
         (Cases_on `^(th |> concl |> dest_imp |> #1)` THEN1 (fs []
             \\ match_mp_tac th \\ fs [])))
      (DB.match ["-"] ``_ ==> ^assign_thm_goal`` |> map (#1 o #2))
  \\ fs [] \\ strip_tac
  \\ Cases_on`op = CopyByte T` >- (
    fs[do_app_def,do_space_def,do_app_aux_def]
    \\ every_case_tac \\ fs[] )
  \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ qsuff_tac `assign c n l dest op args names_opt = (GiveUp,l)` \\ fs []
  \\ `?f. f () = op` by (qexists_tac `K op` \\ fs []) (* here for debugging only *)
  \\ Cases_on `op` \\ fs [assign_def]
  \\ rpt (PURE_CASE_TAC \\ fs [])
  \\ qhdtm_x_assum`do_app`mp_tac \\ EVAL_TAC
QED

val _ = export_theory();
