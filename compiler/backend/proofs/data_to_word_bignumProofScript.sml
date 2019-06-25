(*
  Part of the correctness proof for data_to_word
*)
open preamble dataSemTheory dataPropsTheory
     copying_gcTheory int_bitwiseTheory finite_mapTheory
     data_to_word_memoryProofTheory data_to_word_gcProofTheory
     data_to_wordTheory wordPropsTheory labPropsTheory
     set_sepTheory semanticsPropsTheory word_to_wordProofTheory
     helperLib alignmentTheory blastLib word_bignumTheory
     wordLangTheory word_bignumProofTheory gen_gc_partialTheory
     gc_sharedTheory word_gcFunctionsTheory;
local open gen_gcTheory in end

val _ = new_theory "data_to_word_bignumProof";

val _ = set_grammar_ancestry
  ["dataSem", "wordSem", "data_to_word",
   "data_to_word_memoryProof", "data_to_word_gcProof", "word_bignumProof",
   "labProps" (* good_dimindex *)
  ];

val _ = temp_bring_to_front_overload"cut_env"{Name="cut_env",Thy="wordSem"};

val _ = hide "next";

val _ = temp_overload_on("FALSE_CONST",``Const (n2w 2:'a word)``)
val _ = temp_overload_on("TRUE_CONST",``Const (n2w 18:'a word)``)

val clean_tac = rpt var_eq_tac \\ rpt (qpat_x_assum `T` kall_tac)
fun rpt_drule th = drule (th |> GEN_ALL) \\ rpt (disch_then drule \\ fs [])

val state_rel_def = data_to_word_gcProofTheory.state_rel_def
val code_rel_def = data_to_word_gcProofTheory.code_rel_def

val eval_tac = fs [wordSemTheory.evaluate_def,
  wordSemTheory.word_exp_def, wordSemTheory.set_var_def,
  set_var_def, wordSemTheory.the_words_def,
  wordSemTheory.mem_load_def,wordLangTheory.word_op_def,
  wordLangTheory.word_sh_def]

val eq_eval = save_thm("eq_eval",
  LIST_CONJ [wordSemTheory.evaluate_def,wordSemTheory.get_var_def,
             lookup_insert,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,
             wordSemTheory.word_exp_def,wordSemTheory.set_var_def,
             wordSemTheory.call_env_def,fromList2_def,wordSemTheory.mem_load_def,
             wordSemTheory.bad_dest_args_def,wordSemTheory.get_vars_def,
             wordSemTheory.find_code_def,wordSemTheory.add_ret_loc_def,
             list_insert_def,wordSemTheory.dec_clock_def,wordSemTheory.the_words_def,
             wordLangTheory.word_op_def]);

Theorem word_list_IMP_store_list:
   !xs a frame m dm.
      (word_list a xs * frame) (fun2set (m,dm)) ==>
      store_list a xs m dm = SOME m
Proof
  Induct \\ fs [store_list_def,word_list_def]
  \\ rw [] \\ SEP_R_TAC
  \\ `(a =+ h) m = m` by
    (fs [FUN_EQ_THM,APPLY_UPDATE_THM] \\ rw [] \\ SEP_R_TAC \\ fs [])
  \\ fs [] \\ first_x_assum match_mp_tac
  \\ qexists_tac `frame * one (a,h)` \\ fs [AC STAR_COMM STAR_ASSOC]
QED

Theorem word_exp_set_var_ShiftVar_lemma:
   word_exp t (ShiftVar sow v n) =
    case lookup v t.locals of
    | SOME (Word w) =>
        OPTION_MAP Word
          (case sow of Lsl => SOME (w << n)
                     | Lsr => SOME (w >>> n)
                     | Asr => SOME (w >> n)
                     | Ror => SOME (word_ror w n))
    | _ => FAIL (word_exp t (ShiftVar sow v n)) "lookup failed"
Proof
  Cases_on `lookup v t.locals` \\ fs [] \\ rw [FAIL_DEF]
  \\ fs [ShiftVar_def]
  \\ IF_CASES_TAC \\ fs []
  THEN1
   (Cases_on `n < dimindex (:'a)` \\ fs []
    THEN1
     (Cases_on `n = 0` \\ fs []
      \\ eval_tac \\ every_case_tac \\ fs [])
    \\ eval_tac \\ every_case_tac \\ fs [] \\ eval_tac
    \\ qspec_then `n` assume_tac (MATCH_MP MOD_LESS DIMINDEX_GT_0)
    \\ simp [])
  \\ IF_CASES_TAC \\ fs []
  THEN1 (eval_tac \\ every_case_tac \\ fs [])
  \\ IF_CASES_TAC \\ fs []
  THEN1
   (drule word_asr_dimindex
    \\ IF_CASES_TAC \\ eval_tac
    \\ every_case_tac \\ eval_tac)
  \\ eval_tac \\ every_case_tac \\ fs [] \\ eval_tac
QED

Theorem i2mw_small_int_IMP_0:
   (∀v1. i2mw v ≠ (F,[v1:'a word])) /\ (∀v1. i2mw v ≠ (T,[v1:'a word])) /\
    small_int (:α) v /\ good_dimindex (:'a) ==> v = 0
Proof
  CCONTR_TAC \\ fs [] \\ Cases_on `v` \\ fs []
  \\ fs [multiwordTheory.i2mw_def,small_int_def]
  \\ qpat_x_assum `!x._` mp_tac \\ fs []
  \\ once_rewrite_tac [multiwordTheory.n2mw_def]
  \\ once_rewrite_tac [multiwordTheory.n2mw_def]
  \\ rw []
  \\ fs [good_dimindex_def,dimword_def]
  \\ fs [good_dimindex_def,dimword_def] \\ rfs [DIV_EQ_X]
  \\ intLib.COOPER_TAC
QED

Theorem state_rel_Number_small_int:
   state_rel c r1 r2 s t [x] locs /\ small_int (:'a) i ==>
    state_rel c r1 r2 s t [(Number i,Word (Smallnum i:'a word))] locs
Proof
  fs [state_rel_thm] \\ rw[]
  \\ match_mp_tac IMP_memory_rel_Number \\ fs []
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
  \\ fs []
QED

Theorem heap_lookup_Unused_Bignum:
   heap_lookup a (Unused k::hb) = SOME (Bignum j) <=>
    k+1 <= a /\
    heap_lookup (a - (k+1)) hb = SOME (Bignum j)
Proof
  fs [heap_lookup_def,el_length_def]
  \\ rw [] \\ fs [Bignum_def]
  \\ pairarg_tac \\ fs []
QED

Theorem push_env_insert_0:
   push_env (insert 0 x LN) NONE t =
    t with <| stack := StackFrame [(0,x)] NONE :: t.stack ;
              permute := \n. t.permute (n+1) |>
Proof
  fs [wordSemTheory.push_env_def]
  \\ fs [wordSemTheory.env_to_list_def]
  \\ EVAL_TAC \\ rw [] \\ fs []
  \\ fs [BIJ_DEF,INJ_DEF]
QED

Theorem mc_header_i2mw_eq_0w:
   2 * LENGTH (SND (i2mw i):'a word list) + 1 < dimword (:'a) ==>
    (mc_header (i2mw i:bool # 'a word list) = 0w:'a word <=> i = 0)
Proof
  Cases_on `i = 0`
  \\ fs [multiwordTheory.i2mw_def,mc_multiwordTheory.mc_header_def]
  \\ rw [] \\ fs [word_add_n2w] THEN1 EVAL_TAC
  \\ fs [LENGTH_NIL]
  \\ once_rewrite_tac [multiwordTheory.n2mw_def]
  \\ rw [] \\ intLib.COOPER_TAC
QED

Theorem MustTerminate_limit_eq:
   good_dimindex (:'a) ==>
    ?k. MustTerminate_limit (:α) =
        10 * dimword (:'a) * dimword (:'a) +
        10 * dimword (:'a) + 100 + k
Proof
  rewrite_tac [GSYM LESS_EQ_EXISTS]
  \\ fs [wordSemTheory.MustTerminate_limit_def] \\ rw []
  \\ match_mp_tac LESS_EQ_TRANS
  \\ qexists_tac `dimword (:α) ** dimword (:α)`
  \\ fs []
  \\ match_mp_tac LESS_EQ_TRANS
  \\ qexists_tac `12 * (dimword (:α))²`
  \\ `10 * dimword (:'a) <= (dimword (:α))² /\
      100 <= (dimword (:α))²` by
    (fs [dimword_def,good_dimindex_def] \\ NO_TAC)
  \\ fs []
  \\ match_mp_tac LESS_EQ_TRANS
  \\ qexists_tac `(dimword (:α)) * (dimword (:α))²` \\ fs []
  \\ fs [dimword_def,good_dimindex_def]
QED

Theorem SND_i2mw_NIL:
   SND (i2mw i) = [] <=> i = 0
Proof
  Cases_on `i` \\ fs []
  \\ fs [multiwordTheory.i2mw_def]
  \\ once_rewrite_tac [multiwordTheory.n2mw_def]
  \\ rw [] \\ intLib.COOPER_TAC
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

val get_iop_def = Define `
  get_iop (n:num) =
    if n = 0 then multiword$Add else
    if n = 1 then multiword$Sub else
    if n = 4 then multiword$Mul else
    if n = 5 then multiword$Div else
                  multiword$Mod`;

val int_op_def = Define `
  int_op op_index i j =
    if op_index = 0n then SOME (i + j) else
    if op_index = 1 then SOME (i - j) else
    if op_index = 4 then SOME (i * j) else
    if op_index = 5 /\ j <> 0 then SOME (i / j) else
    if op_index = 6 /\ j <> 0 then SOME (i % j) else NONE`

Theorem get_sign_word_lemma:
   good_dimindex (:α) ⇒ (1w && x ⋙ 4) = if word_bit 4 x then 1w else 0w:'a word
Proof
  rw [] \\ fs [fcpTheory.CART_EQ,word_and_def,word_lsr_def,fcpTheory.FCP_BETA,
         good_dimindex_def,word_index]
  \\ rw [] \\ Cases_on `i = 0` \\ fs [word_bit_def]
QED

val if_eq_b2w = prove(
  ``(if b then 1w else 0w) = b2w b``,
  Cases_on `b` \\ EVAL_TAC);

Theorem LongDiv1_thm:
   !k n1 n2 m i1 i2 (t2:('a,'c,'ffi) wordSem$state)
        r1 r2 m1 is1 c:data_to_word$config.
      single_div_loop (n2w k,[n1;n2],m,[i1;i2]) = (m1,is1) /\
      lookup LongDiv1_location t2.code = SOME (7,LongDiv1_code c) /\
      lookup 0 t2.locals = SOME (Loc r1 r2) /\
      lookup 2 t2.locals = SOME (Word (n2w k)) /\
      lookup 4 t2.locals = SOME (Word n2) /\
      lookup 6 t2.locals = SOME (Word n1) /\
      lookup 8 t2.locals = SOME (Word m) /\
      lookup 10 t2.locals = SOME (Word i1) /\
      lookup 12 t2.locals = SOME (Word i2) /\
      k < dimword (:'a) /\ k < t2.clock /\ good_dimindex (:'a) /\ ~c.has_longdiv ==>
      ?j1 j2.
        is1 = [j1;j2] /\
        evaluate (LongDiv1_code c,t2) = (SOME (Result (Loc r1 r2) (Word m1)),
          t2 with <| clock := t2.clock - k;
                     locals := LN;
                     store := t2.store |+ (Temp 28w,Word (HD is1)) |>)
Proof
  Induct THEN1
   (fs [Once multiwordTheory.single_div_loop_def] \\ rw []
    \\ rewrite_tac [LongDiv1_code_def]
    \\ fs [eq_eval,wordSemTheory.set_store_def]
    \\ fs [wordSemTheory.state_component_equality])
  \\ once_rewrite_tac [multiwordTheory.single_div_loop_def]
  \\ rpt strip_tac \\ fs []
  \\ fs [multiwordTheory.mw_shift_def]
  \\ fs [ADD1,GSYM word_add_n2w]
  \\ qpat_x_assum `_ = (m1,is1)` mp_tac
  \\ once_rewrite_tac [multiwordTheory.mw_cmp_def] \\ fs []
  \\ once_rewrite_tac [multiwordTheory.mw_cmp_def] \\ fs []
  \\ once_rewrite_tac [multiwordTheory.mw_cmp_def] \\ fs []
  \\ qabbrev_tac `n2' = n2 ⋙ 1`
  \\ qabbrev_tac `n1' = (n2 ≪ (dimindex (:α) − 1) ‖ n1 ⋙ 1)`
  \\ rewrite_tac [LongDiv1_code_def]
  \\ fs [eq_eval,word_add_n2w]
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs []
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [lookup_insert]
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ fs [lookup_insert]
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ fs [GSYM word_add_n2w]
  \\ Cases_on `i2 <+ n2'` \\ fs [WORD_LOWER_NOT_EQ] THEN1
   (strip_tac
    \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
    \\ qmatch_goalsub_abbrev_tac `evaluate (LongDiv1_code c,t3)`
    \\ first_x_assum drule
    \\ disch_then (qspecl_then [`t3`,`r1`,`r2`,`c`] mp_tac)
    \\ impl_tac THEN1 (unabbrev_all_tac \\ fs [lookup_insert])
    \\ strip_tac \\ fs []
    \\ unabbrev_all_tac \\ fs [wordSemTheory.state_component_equality])
  \\ Cases_on `i2 = n2' /\ i1 <+ n1'` \\ asm_rewrite_tac [] THEN1
   (fs [WORD_LOWER_NOT_EQ] \\ rveq \\ strip_tac
    \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
    \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
    \\ qmatch_goalsub_abbrev_tac `evaluate (LongDiv1_code c,t3)`
    \\ first_x_assum drule
    \\ disch_then (qspecl_then [`t3`,`r1`,`r2`,`c`] mp_tac)
    \\ impl_tac THEN1 (unabbrev_all_tac \\ fs [lookup_insert])
    \\ strip_tac \\ fs []
    \\ unabbrev_all_tac \\ fs [wordSemTheory.state_component_equality])
  \\ IF_CASES_TAC
  THEN1 (sg `F` \\ fs [] \\ pop_assum mp_tac \\ rfs [] \\ rfs [] \\ rw [])
  \\ pop_assum kall_tac
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval]
  \\ `i2 = n2' ==> ~(i1 <₊ n1')` by metis_tac []
  \\ simp [] \\ ntac 2 (pop_assum kall_tac)
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval]
  \\ fs [multiwordTheory.mw_sub_def,multiwordTheory.single_sub_def]
  \\ pairarg_tac \\ fs []
  \\ rename1 `_ = (is2,r)`
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval,wordSemTheory.inst_def]
  \\ fs [if_eq_b2w,GSYM word_add_n2w]
  \\ `i1 + ¬n1' + 1w = z /\ (dimword (:α) ≤ w2n i1 + (w2n (¬n1') + 1)) = c1` by
   (fs [multiwordTheory.single_add_def] \\ rveq
    \\ fs [multiwordTheory.b2w_def,multiwordTheory.b2n_def])
  \\ fs [] \\ ntac 2 (pop_assum kall_tac)
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval,wordSemTheory.inst_def]
  \\ fs [if_eq_b2w,GSYM word_add_n2w]
  \\ qmatch_goalsub_abbrev_tac `b2w new_c`
  \\ qmatch_goalsub_abbrev_tac `insert 12 (Word new_z)`
  \\ `z' = new_z /\ c1' = new_c` by
   (unabbrev_all_tac \\ pop_assum mp_tac
    \\ simp [multiwordTheory.single_add_def] \\ strip_tac \\ rveq
    \\ qpat_abbrev_tac `ppp = if b2w c1 = 0w then 0 else 1n`
    \\ qsuff_tac `ppp = b2n c1`
    THEN1 (fs [] \\ Cases_on `c1` \\ EVAL_TAC)
    \\ unabbrev_all_tac \\ Cases_on `c1` \\ EVAL_TAC \\ fs [] \\ NO_TAC)
  \\ fs [list_Seq_def,eq_eval]
  \\ qmatch_goalsub_abbrev_tac `evaluate (LongDiv1_code c,t3)`
  \\ strip_tac \\ first_x_assum drule
  \\ disch_then (qspecl_then [`t3`,`r1`,`r2`,`c`] mp_tac)
  \\ impl_tac THEN1 (unabbrev_all_tac \\ fs [lookup_insert])
  \\ strip_tac \\ fs []
  \\ unabbrev_all_tac \\ fs [wordSemTheory.state_component_equality]
QED

Theorem get_real_addr_lemma:
   shift_length c < dimindex (:'a) /\
    good_dimindex (:'a) /\
    get_var v (t:('a,'c,'ffi) wordSem$state) = SOME (Word ptr_w) /\
    get_real_addr c t.store ptr_w = SOME x ==>
    word_exp t (real_addr c v) = SOME (Word (x:'a word))
Proof
  fs [get_real_addr_def] \\ every_case_tac \\ fs []
  \\ fs [wordSemTheory.get_var_def,real_addr_def]
  \\ eval_tac \\ fs [] \\ rw []
  \\ eval_tac \\ fs [] \\ rw [] \\ fs []
  \\ fs [labPropsTheory.good_dimindex_def,dimword_def] \\ rw []
  \\ rfs [backend_commonTheory.word_shift_def] \\ fs []
QED

Theorem memory_rel_lookup:
   memory_rel c be refs s st m dm
      (join_env l1 (toAList (inter l2 (adjust_set l1))) ++ xs) ∧
    lookup n l1 = SOME x ∧ lookup (adjust_var n) l2 = SOME w ⇒
    memory_rel c be refs s st m dm
     ((x,w)::(join_env l1 (toAList (inter l2 (adjust_set l1))) ++ xs))
Proof
  fs [memory_rel_def] \\ rw [] \\ asm_exists_tac \\ fs []
  \\ rpt_drule (Q.INST [`ys`|->`[]`] word_ml_inv_lookup
        |> SIMP_RULE std_ss [APPEND])
QED

Theorem evaluate_AddNumSize:
   !src c l1 l2 s t locs i w.
      state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) [] locs /\
      get_var src s.locals = SOME (Number i) ==>
      evaluate (AddNumSize c src,set_var 1 (Word w) t) =
        (NONE,set_var 1 (Word (w +
           n2w (4 * LENGTH ((SND (i2mw i):'a word list))))) t)
Proof
  fs [AddNumSize_def] \\ rpt strip_tac
  \\ imp_res_tac state_rel_get_var_IMP
  \\ fs [state_rel_thm,get_var_def,wordSemTheory.get_var_def]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule (GEN_ALL memory_rel_lookup)
  \\ rpt (disch_then drule) \\ fs [] \\ strip_tac
  \\ imp_res_tac memory_rel_any_Number_IMP
  \\ rveq \\ fs [] \\ rveq \\ fs []
  \\ rename1 `_ = SOME (Word w4)`
  \\ Cases_on `w4 = 0w` THEN1
   (fs [eq_eval,EVAL ``0w ' 0``]
    \\ imp_res_tac memory_rel_Number_const_test
    \\ pop_assum (qspec_then `i` assume_tac) \\ rfs []
    \\ sg `i = 0` \\ fs [EVAL ``i2mw 0``]
    \\ fs [Smallnum_def,small_int_def,good_dimindex_def] \\ rfs [dimword_def]
    \\ Cases_on `i` \\ fs [] \\ rfs [dimword_def])
  \\ Cases_on `(w4 && 1w) = 0w` THEN1
   (fs [eq_eval]
    \\ imp_res_tac memory_rel_Number_const_test
    \\ pop_assum (qspec_then `i` assume_tac) \\ rfs []
    \\ fs [Smallnum_def]
    \\ sg `LENGTH (SND (i2mw i)) = 1` \\ fs []
    \\ fs [word_index_test]
    \\ fs [multiwordTheory.i2mw_def,Once multiwordTheory.n2mw_def] \\ rfs []
    \\ rveq \\ fs [] \\ fs [small_int_def]
    \\ fs [good_dimindex_def] \\ rfs [dimword_def]
    \\ Cases_on `i` \\ fs [dimword_def] \\ rfs []
    \\ once_rewrite_tac [multiwordTheory.n2mw_def]
    \\ fs [DIV_EQ_X]
    \\ rw [] \\ fs []
    \\ `F` by intLib.COOPER_TAC)
  \\ fs [eq_eval]
  \\ fs [word_index_test]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule (GEN_ALL memory_rel_Number_bignum_IMP_ALT) \\ fs []
  \\ strip_tac
  \\ `word_exp (t with locals := insert 1 (Word w) t.locals)
            (real_addr c (adjust_var src)) = SOME (Word a)` by
    (match_mp_tac (GEN_ALL get_real_addr_lemma)
     \\ fs [wordSemTheory.get_var_def,lookup_insert] \\ NO_TAC) \\ fs []
  \\ fs [word_sh_def,decode_length_def]
  \\ IF_CASES_TAC THEN1
   (rfs [memory_rel_def,heap_in_memory_store_def]
    \\ fs [good_dimindex_def]  \\ rfs [] \\ fs[])
  \\ pop_assum kall_tac \\ fs []
  \\ IF_CASES_TAC THEN1
   (fs [good_dimindex_def] \\ rfs [])
  \\ pop_assum kall_tac \\ fs []
  \\ fs [WORD_MUL_LSL,GSYM word_mul_n2w,multiwordTheory.i2mw_def]
QED

Theorem AnyHeader_thm:
   !t1 t2 t3 r.
      state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) [] locs /\
      get_var r s.locals = SOME (Number i) /\
      ALL_DISTINCT [t1;t2;t3] ==>
      ?a2 a3 temp.
        evaluate (AnyHeader c (adjust_var r) a t1 t2 t3,t) =
          (NONE, (set_store (Temp t1) (Word (mc_header (i2mw i)))
                 (set_store (Temp t2) (Word a2)
                 (set_store (Temp t3) (Word a3) (set_var 7 temp t))))) /\
        (i = 0i ==>
           small_int (:'a) 0i /\ i2mw i = (F,[]) /\
           a2 = 0w /\ a3 = 0w) /\
        (small_int (:'a) i /\ i <> 0 ==>
           i2mw i = (i < 0,[a3]) /\
           FLOOKUP t.store (if a then OtherHeap else NextFree) = SOME (Word a2)) /\
        (~small_int (:'a) i ==>
           ?w x. get_var (adjust_var r) t = SOME (Word w) /\
                 get_real_addr c t.store w = SOME x /\
                 a2 = x + bytes_in_word)
Proof
  rpt strip_tac
  \\ imp_res_tac state_rel_get_var_IMP
  \\ fs [state_rel_thm]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule memory_rel_get_var_IMP
  \\ fs [APPEND] \\ strip_tac
  \\ imp_res_tac memory_rel_any_Number_IMP
  \\ fs [] \\ fs [] \\ rveq \\ fs []
  \\ rename1 `w ' 0 ⇔ ¬small_int (:α) i`
  \\ `(w = 0w) <=> (i = 0)` by
   (rpt_drule memory_rel_Number_const_test
    \\ disch_then (qspec_then `i` mp_tac)
    \\ fs [] \\ Cases_on `w = 0w` \\ fs [EVAL ``0w ' 0``]
    \\ rw [] \\ fs [] \\ rpt strip_tac
    \\ fs [EVAL ``Smallnum 0``,EVAL ``small_int (:'a) 0``]
    \\ fs [small_int_def,Smallnum_def]
    \\ Cases_on `i` \\ fs []
    \\ rfs [good_dimindex_def,dimword_def]
    \\ rfs [good_dimindex_def,dimword_def])
  \\ Cases_on `i = 0` \\ fs []
  THEN1
   (fs [EVAL ``i2mw 0``] \\ fs [EVAL ``small_int (:α) 0``]
    \\ fs [EVAL ``mc_header (F,[])``,dimword_def]
    \\ `0n < 2 ** dimindex (:α) DIV 8` by fs [good_dimindex_def] \\ fs []
    \\ fs [AnyHeader_def]
    \\ fs [eq_eval,list_Seq_def,wordSemTheory.set_store_def,wordSemTheory.set_var_def]
    \\ fs [wordSemTheory.state_component_equality]
    \\ fs [GSYM fmap_EQ,FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ qexists_tac `Word 0w`
    \\ rw [] \\ fs [] \\ eq_tac \\ rw [] \\ fs [])
  \\ fs [word_bit,word_bit_test]
  \\ reverse (Cases_on `small_int (:'a) i`) \\ fs []
  THEN1
   (fs [AnyHeader_def,eq_eval]
    \\ fs [eq_eval,list_Seq_def,wordSemTheory.set_store_def]
    \\ rpt_drule memory_rel_Number_bignum_IMP_ALT
    \\ strip_tac
    \\ `word_exp t (real_addr c (adjust_var r)) = SOME (Word a)` by
     (match_mp_tac (GEN_ALL get_real_addr_lemma)
      \\ fs [wordSemTheory.get_var_def]) \\ fs []
    \\ fs [word_sh_def]
    \\ IF_CASES_TAC
    THEN1 (rfs [memory_rel_def,heap_in_memory_store_def]
           \\ rfs [good_dimindex_def])
    \\ pop_assum kall_tac
    \\ `~(1 ≥ dimindex (:α)) /\ ~(4 ≥ dimindex (:α))` by
          (fs [good_dimindex_def] \\ fs [good_dimindex_def])
    \\ fs []
    \\ qexists_tac `0w` \\ fs []
    \\ qexists_tac `Word a` \\ fs []
    \\ fs [wordSemTheory.state_component_equality]
    \\ fs [GSYM fmap_EQ,FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ rw [] \\ fs [] \\ TRY (eq_tac \\ rw [] \\ fs [])
    \\ fs [decode_length_def,mc_multiwordTheory.mc_header_def,
           multiwordTheory.i2mw_def,WORD_MUL_LSL,word_mul_n2w]
    \\ qpat_assum `_ <=> i < 0i` (fn th => rewrite_tac [GSYM th])
    \\ qpat_assum `good_dimindex (:α)` mp_tac
    \\ fs [get_sign_word_lemma])
  \\ fs [AnyHeader_def,eq_eval]
  \\ Q.MATCH_ASMSUB_RENAME_TAC `(Number i,Word w)::vars` \\ rveq
  \\ `memory_rel c t.be s.refs s.space t.store t.memory t.mdomain
         ((Number 0,Word (Smallnum 0))::(Number i,Word w)::vars)` by
   (match_mp_tac IMP_memory_rel_Number
    \\ fs [] \\ EVAL_TAC \\ fs [good_dimindex_def,dimword_def])
  \\ imp_res_tac memory_rel_swap
  \\ drule memory_rel_Number_cmp \\ fs [EVAL ``word_bit 0 (Smallnum 0)``]
  \\ fs [word_bit_test,EVAL ``Smallnum 0``]
  \\ strip_tac \\ fs []
  \\ IF_CASES_TAC \\ fs []
  THEN1
   (`i2mw i = (F,[w >>> 2])` by
      (fs [multiwordTheory.i2mw_def]
       \\ Cases_on `i` \\ fs [intLib.COOPER_PROVE ``Num (ABS (&n)) = n``]
       \\ once_rewrite_tac [multiwordTheory.n2mw_def] \\ fs []
       \\ `n < dimword (:α)` by
            (ntac 2 (rfs [good_dimindex_def,small_int_def,dimword_def]))
       \\ once_rewrite_tac [multiwordTheory.n2mw_def] \\ fs []
       \\ fs [DIV_EQ_X]
       \\ imp_res_tac memory_rel_Number_IMP \\ fs []
       \\ fs [Smallnum_def]
       \\ rewrite_tac [GSYM w2n_11,w2n_lsr]
       \\ fs [] \\ rfs [good_dimindex_def,small_int_def,dimword_def] \\ rfs[]
       \\ fs [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV])
    \\ fs [] \\ fs [eq_eval,list_Seq_def,wordSemTheory.set_store_def]
    \\ Cases_on `a` \\ fs [FLOOKUP_UPDATE,heap_in_memory_store_def,memory_rel_def]
    \\ fs [word_sh_def]
    \\ qexists_tac `Word 0w` \\ fs []
    \\ fs [wordSemTheory.state_component_equality]
    \\ fs [GSYM fmap_EQ,FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ rw [] \\ fs [] \\ TRY (eq_tac \\ rw [] \\ fs [])
    \\ EVAL_TAC \\ fs [n2w_mod])
  THEN1
   (`i2mw i = (T,[0w - (w >> 2)])` by
      (fs [multiwordTheory.i2mw_def]
       \\ Cases_on `i` \\ fs [intLib.COOPER_PROVE ``Num (ABS (-&n)) = n``]
       \\ once_rewrite_tac [multiwordTheory.n2mw_def] \\ fs []
       \\ `n < dimword (:α)` by
            (ntac 2 (rfs [good_dimindex_def,small_int_def,dimword_def]))
       \\ once_rewrite_tac [multiwordTheory.n2mw_def] \\ fs []
       \\ fs [DIV_EQ_X]
       \\ imp_res_tac memory_rel_Number_IMP \\ fs []
       \\ fs [small_int_def,Smallnum_def]
       \\ `-n2w (4 * n) = i2w (- & (4 * n))` by
            (fs [integer_wordTheory.i2w_def] \\ NO_TAC) \\ fs []
       \\ qspecl_then [`2`,`-&(4 * n)`] mp_tac (GSYM integer_wordTheory.i2w_DIV)
       \\ impl_tac THEN1
        (fs [wordsTheory.INT_MIN_def]
         \\ fs [EXP_SUB,X_LE_DIV,dimword_def]
         \\ rfs [good_dimindex_def])
       \\ fs [] \\ strip_tac
       \\ `-&(4 * n) / 4:int = - & n` by
        (rewrite_tac [MATCH_MP (GSYM integerTheory.INT_DIV_NEG)
                         (intLib.COOPER_PROVE ``0 <> 4i``)]
         \\ fs [integerTheory.INT_DIV_CALCULATE]
         \\ fs [integerTheory.INT_EQ_NEG]
         \\ match_mp_tac integerTheory.INT_DIV_UNIQUE
         \\ fs [] \\ qexists_tac `0` \\ fs []
         \\ fs [integerTheory.INT_MUL_CALCULATE])
       \\ fs [] \\ fs [integer_wordTheory.i2w_def]
       \\ rewrite_tac [GSYM WORD_NEG_MUL] \\ fs [])
    \\ fs [] \\ fs [eq_eval,list_Seq_def,wordSemTheory.set_store_def]
    \\ Cases_on `a` \\ fs [FLOOKUP_UPDATE,heap_in_memory_store_def,memory_rel_def]
    \\ fs [word_sh_def]
    \\ qexists_tac `Word 0w` \\ fs []
    \\ fs [wordSemTheory.state_component_equality]
    \\ fs [GSYM fmap_EQ,FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ rw [] \\ fs [] \\ TRY (eq_tac \\ rw [] \\ fs [])
    \\ EVAL_TAC \\ fs [n2w_mod])
QED

Theorem state_rel_set_store_Temp:
   state_rel c l1 l2 s (set_store (Temp tmp) w t) vs locs =
    state_rel c l1 l2 s t vs locs
Proof
  fs [state_rel_def,wordSemTheory.set_store_def]
  \\ rw [] \\ eq_tac \\ rw []
  \\ fs [heap_in_memory_store_def,PULL_EXISTS,FLOOKUP_UPDATE,
         FAPPLY_FUPDATE_THM,code_oracle_rel_def]
  \\ rpt (asm_exists_tac \\ fs []) \\ metis_tac []
QED

Theorem state_rel_IMP_num_size_limit:
   state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) [] locs /\
    get_var k s.locals = SOME (Number i) ==>
    LENGTH (SND (i2mw i):'a word list) < dimword (:'a) DIV 16
Proof
  rpt strip_tac
  \\ imp_res_tac state_rel_get_var_IMP
  \\ fs [state_rel_thm,get_var_def,wordSemTheory.get_var_def]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule (GEN_ALL memory_rel_lookup)
  \\ Cases_on `small_int (:'a) i`
  THEN1
   (rw [] \\ simp [multiwordTheory.i2mw_def]
    \\ once_rewrite_tac [multiwordTheory.n2mw_def]
    \\ once_rewrite_tac [multiwordTheory.n2mw_def]
    \\ fs [good_dimindex_def,dimword_def] \\ rfs [DIV_EQ_X]
    \\ rw [] \\ fs [] \\ rfs [small_int_def,dimword_def]
    \\ `F` by intLib.COOPER_TAC)
  \\ strip_tac
  \\ rpt_drule memory_rel_Number_bignum_IMP_ALT
  \\ fs [multiwordTheory.i2mw_def] \\ rw [] \\ fs []
  \\ fs [good_dimindex_def,dimword_def] \\ rfs [EXP_SUB]
QED

Theorem word_list_store_list:
   !xs a frame m dm.
      (word_list a xs * frame) (fun2set (m,dm)) ==>
      ?m2. (store_list a (REPLICATE (LENGTH xs) (Word 0w)) m dm = SOME m2) /\
           (word_list a (REPLICATE (LENGTH xs) (Word 0w)) * frame)
              (fun2set (m2,dm))
Proof
  Induct \\ fs [store_list_def,REPLICATE,word_list_def] \\ rw []
  \\ SEP_R_TAC \\ fs [] \\ SEP_W_TAC \\ SEP_F_TAC
  \\ strip_tac \\ fs [AC STAR_COMM STAR_ASSOC]
QED

Theorem MustTerminate_limit_SUB_2:
   good_dimindex (:'a) ==> dimword (:'a) <= MustTerminate_limit (:α) − 2
Proof
  fs [wordSemTheory.MustTerminate_limit_def]
  \\ qpat_abbrev_tac `m = (_:num) ** _`
  \\ qpat_abbrev_tac `n = (_:num) ** _`
  \\ rpt (pop_assum kall_tac)
  \\ fs [good_dimindex_def] \\ rw [] \\ fs [dimword_def]
QED

Theorem cut_env_fromList_sing:
   cut_env (fromList [()]) (insert 0 (Loc l1 l2) LN) =
    SOME (insert 0 (Loc l1 l2) LN)
Proof
  EVAL_TAC
QED

Theorem single_div_pre_IMP_single_div_full:
   single_div_pre x1 x2 y ==>
    single_div x1 x2 y = single_div_full x1 x2 y
Proof
  strip_tac
  \\ match_mp_tac (GSYM multiwordTheory.single_div_full_thm)
  \\ fs [mc_multiwordTheory.single_div_pre_def,multiwordTheory.mw2n_def]
  \\ Cases_on `y` \\ fs [] \\ rfs [DIV_LT_X]
QED

Theorem IMP_LESS_MustTerminate_limit[simp]:
   i < dimword (:α) ==>
    i < MustTerminate_limit (:α) − 1
Proof
  rewrite_tac [wordSemTheory.MustTerminate_limit_def] \\ decide_tac
QED

Theorem evaluate_LongDiv_code:
   !(t:('a,'c,'ffi) wordSem$state) l1 l2 c w x1 x2 y d1 m1.
      single_div_pre x1 x2 y /\
      single_div x1 x2 y = (d1,m1:'a word) /\
      lookup LongDiv1_location t.code = SOME (7,LongDiv1_code c) /\
      lookup 0 t.locals = SOME (Loc l1 l2) /\
      lookup 2 t.locals = SOME (Word x1) /\
      lookup 4 t.locals = SOME (Word x2) /\
      lookup 6 t.locals = SOME (Word y) /\
      dimword (:'a) < t.clock /\ good_dimindex (:'a) ==>
      ?ck.
        evaluate (LongDiv_code c,t) =
          (SOME (Result (Loc l1 l2) (Word d1)),
           t with <| clock := ck; locals := LN;
                     store := t.store |+ (Temp 28w,Word m1) |>)
Proof
  rpt strip_tac
  \\ Cases_on `c.has_longdiv` \\ simp []
  \\ fs [LongDiv_code_def,eq_eval,wordSemTheory.push_env_def]
  THEN1 (* has_longdiv case *)
   (once_rewrite_tac [list_Seq_def] \\ fs [eq_eval,wordSemTheory.inst_def]
    \\ reverse IF_CASES_TAC THEN1
     (sg `F` \\ pop_assum mp_tac \\ simp []
      \\ fs [mc_multiwordTheory.single_div_pre_def])
    \\ fs [list_Seq_def,eq_eval,wordSemTheory.set_store_def,lookup_insert]
    \\ fs [fromAList_def,wordSemTheory.state_component_equality]
    \\ fs [multiwordTheory.single_div_def])
  \\ `dimindex (:'a) + 5 < dimword (:'a)` by
        (fs [dimword_def,good_dimindex_def] \\ NO_TAC)
  \\ imp_res_tac IMP_LESS_MustTerminate_limit
  \\ qmatch_goalsub_abbrev_tac `evaluate (LongDiv1_code c,t2)`
  \\ rfs [single_div_pre_IMP_single_div_full]
  \\ fs [multiwordTheory.single_div_full_def]
  \\ Cases_on `(single_div_loop (n2w (dimindex (:α)),[0w; y],0w,[x2; x1]))`
  \\ fs [] \\ rveq
  \\ `lookup LongDiv1_location t2.code = SOME (7,LongDiv1_code c) /\
      lookup 0 t2.locals = SOME (Loc l1 l2)` by
    (qunabbrev_tac `t2` \\ fs [lookup_insert])
  \\ rpt_drule LongDiv1_thm
  \\ impl_tac THEN1 (qunabbrev_tac `t2` \\ EVAL_TAC \\ fs [])
  \\ strip_tac \\ fs []
  \\ qunabbrev_tac `t2` \\ fs []
  \\ fs [FLOOKUP_UPDATE,wordSemTheory.set_store_def,
         wordSemTheory.state_component_equality,fromAList_def]
QED

Theorem div_code_assum_thm:
   state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) [] locs ==>
    div_code_assum (:'ffi) (:'c) t.code
Proof
  fs [DivCode_def,div_code_assum_def,eq_eval] \\ rpt strip_tac
  \\ fs [state_rel_thm,code_rel_def,stubs_def]
  \\ fs [EVAL ``LongDiv_location``,div_location_def]
  \\ qpat_abbrev_tac `x = cut_env (LS ()) _`
  \\ `x = SOME (insert 0 ret_val LN)` by
   (unabbrev_all_tac \\ fs [wordSemTheory.cut_env_def,domain_lookup]
    \\ match_mp_tac (spt_eq_thm |> REWRITE_RULE [EQ_IMP_THM]
                       |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT2
                       |> DISCH_ALL |> MP_CANON |> GEN_ALL)
    \\ conj_tac THEN1 (rewrite_tac [wf_inter] \\ EVAL_TAC)
    \\ simp_tac std_ss [lookup_inter_alt,lookup_def,domain_lookup]
    \\ fs [lookup_insert,lookup_def] \\ NO_TAC)
  \\ fs [eq_eval,wordSemTheory.push_env_def]
  \\ `env_to_list (insert 0 ret_val LN) t1.permute =
        ([(0,ret_val)],\n. t1.permute (n+1))` by
   (fs [wordSemTheory.env_to_list_def,wordSemTheory.list_rearrange_def]
    \\ fs [EVAL ``(QSORT key_val_compare (toAList (insert 0 x LN)))``]
    \\ fs [EVAL ``count 1``] \\ rw []
    \\ fs [BIJ_DEF,SURJ_DEF]) \\ fs []
  \\ `dimindex (:'a) + 5 < dimword (:'a)` by
        (fs [dimword_def,good_dimindex_def] \\ NO_TAC)
  \\ qmatch_goalsub_abbrev_tac `evaluate (LongDiv_code c,t2)`
  \\ qspecl_then [`t2`,`n`,`l`,`c`] mp_tac evaluate_LongDiv_code
  \\ fs [Abbr `t2`,lookup_insert,multiwordTheory.single_div_def]
  \\ impl_tac THEN1 fs [wordSemTheory.MustTerminate_limit_def]
  \\ strip_tac \\ fs [] \\ pop_assum kall_tac
  \\ fs [wordSemTheory.pop_env_def,EVAL ``domain (fromAList [(0,ret_val)])``,
         FLOOKUP_UPDATE,wordSemTheory.set_store_def]
  \\ fs [fromAList_def,wordSemTheory.state_component_equality]
  \\ match_mp_tac (spt_eq_thm |> REWRITE_RULE [EQ_IMP_THM]
                     |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT2
                     |> DISCH_ALL |> MP_CANON |> GEN_ALL)
  \\ conj_tac THEN1 metis_tac [wf_def,wf_insert]
  \\ simp_tac std_ss [lookup_insert,lookup_def]
  \\ rpt strip_tac
  \\ rpt (IF_CASES_TAC \\ asm_rewrite_tac [])
  \\ rveq \\ qpat_x_assum `0 < 0n` mp_tac
  \\ simp_tac (srw_ss()) []
QED

Theorem IMP_bignum_code_rel:
   compile Bignum_location 1 1 (Bignum_location + 1,[])
             mc_iop_code = (xx1,xx2,xx3,xx4,xx5) /\
    state_rel c l1 l2 s t [] locs ==>
    code_rel (xx4,xx5) t.code
Proof
  fs [word_bignumProofTheory.code_rel_def,state_rel_def,code_rel_def,stubs_def]
  \\ rpt strip_tac
  \\ fs [generated_bignum_stubs_def] \\ rfs [] \\ fs [EVERY_MAP]
  \\ drule alistTheory.ALOOKUP_MEM \\ strip_tac
  \\ first_x_assum (drule o REWRITE_RULE [EVERY_MEM])
  \\ fs [] \\ strip_tac
  \\ imp_res_tac compile_NIL_IMP \\ fs []
  \\ asm_exists_tac \\ fs []
QED

Theorem TWO_LESS_MustTerminate_limit[simp]:
   2 < MustTerminate_limit (:α) /\
    ~(MustTerminate_limit (:α) <= 1)
Proof
  fs [wordSemTheory.MustTerminate_limit_def,dimword_def]
  \\ Cases_on `dimindex (:'a)` \\ fs [dimword_def,MULT_CLAUSES,EXP]
  \\ Cases_on `n` \\ fs [EXP] \\ Cases_on `2 ** n'` \\ fs []
QED

val Arith_location_def = Define `
  Arith_location index =
    if index = 0n then Add_location else
    if index = 1n then Sub_location else
    if index = 4n then Mul_location else
    if index = 5n then Div_location else
    if index = 6n then Mod_location else ARB`;

Theorem push_env_code:
   (push_env y NONE t).code = t.code
Proof
  fs [wordSemTheory.push_env_def] \\ pairarg_tac \\ fs []
QED

val Arith_code_def = Define `
  Arith_code index =
    Seq (Assign 6 (Const (n2w (4 * index))))
      (Call NONE (SOME AnyArith_location) [0; 2; 4; 6] NONE)`;

Theorem lookup_Arith_location:
   state_rel c l1 l2 x t [] locs /\ int_op index i1 i2 = SOME r ==>
    lookup (Arith_location index) t.code = SOME (3,Arith_code index)
Proof
  rw [] \\ drule lookup_RefByte_location
  \\ fs [int_op_def] \\ every_case_tac \\ fs []
  \\ fs [Arith_location_def] \\ rw [] \\ EVAL_TAC
QED

Theorem Replicate_code_thm:
   !n a r m1 a1 a2 a3 a4 a5.
      lookup Replicate_location r.code = SOME (5,Replicate_code) /\
      store_list (a + bytes_in_word) (REPLICATE n v)
        (r:('a,'c,'ffi) wordSem$state).memory r.mdomain = SOME m1 /\
      get_var a1 r = SOME (Loc l1 l2) /\
      get_var a2 r = SOME (Word a) /\
      get_var a3 r = SOME v /\
      get_var a4 r = SOME (Word (n2w (4 * n))) /\
      get_var a5 (r:('a,'c,'ffi) wordSem$state) = SOME ret_val /\
      4 * n < dimword (:'a) /\
      n < r.clock ==>
      evaluate (Call NONE (SOME Replicate_location) [a1;a2;a3;a4;a5] NONE,r) =
        (SOME (Result (Loc l1 l2) ret_val),
         r with <| memory := m1 ; clock := r.clock - n - 1; locals := LN |>)
Proof
  Induct \\ rw [] \\ simp [wordSemTheory.evaluate_def]
  \\ simp [wordSemTheory.get_vars_def,wordSemTheory.bad_dest_args_def,
        wordSemTheory.find_code_def,wordSemTheory.add_ret_loc_def]
  \\ rw [] \\ simp [Replicate_code_def]
  \\ simp [wordSemTheory.evaluate_def,wordSemTheory.call_env_def,
         wordSemTheory.get_var_def,word_exp_rw,fromList2_def,
         asmTheory.word_cmp_def,wordSemTheory.dec_clock_def]
  \\ fs [store_list_def,REPLICATE]
  THEN1 (rw [wordSemTheory.state_component_equality])
  \\ NTAC 3 (once_rewrite_tac [list_Seq_def])
  \\ simp [wordSemTheory.evaluate_def,wordSemTheory.call_env_def,
           wordSemTheory.get_var_def,word_exp_rw,fromList2_def,
           wordSemTheory.set_var_def,wordSemTheory.mem_store_def,
           asmTheory.word_cmp_def,wordSemTheory.dec_clock_def]
  \\ fs [list_Seq_def]
  \\ SEP_I_TAC "evaluate"
  \\ fs [wordSemTheory.call_env_def,
           wordSemTheory.get_var_def,word_exp_rw,fromList2_def,
           wordSemTheory.set_var_def,wordSemTheory.mem_store_def,
           asmTheory.word_cmp_def,wordSemTheory.dec_clock_def]
  \\ rfs [] \\ fs [MULT_CLAUSES,GSYM word_add_n2w] \\ fs [ADD1]
QED

Theorem Replicate_code_alt_thm:
   !n a r m1 a1 a2 a3 a4 a5 var.
      lookup Replicate_location r.code = SOME (5,Replicate_code) /\
      store_list (a + bytes_in_word) (REPLICATE n v)
        (r:('a,'c,'ffi) wordSem$state).memory r.mdomain = SOME m1 /\
      get_var a2 r = SOME (Word a) /\
      get_var a3 r = SOME v /\
      get_var a4 r = SOME (Word (n2w (4 * n))) /\
      get_var 0 (r:('a,'c,'ffi) wordSem$state) = SOME ret_val /\
      4 * n < dimword (:'a) /\
      n < r.clock ==>
      evaluate (Call (SOME (0,fromList [()],Skip,l1,l2))
                  (SOME Replicate_location) [a2;a3;a4;0] NONE,r) =
        (NONE,
         r with <| memory := m1 ; clock := r.clock - n - 1;
                   locals := insert 0 ret_val LN ;
                   permute := (\n. r.permute (n+1)) |>)
Proof
  rw [] \\ fs [wordSemTheory.evaluate_def]
  \\ simp [wordSemTheory.get_vars_def,wordSemTheory.bad_dest_args_def,
        wordSemTheory.find_code_def,wordSemTheory.add_ret_loc_def]
  \\ fs [EVAL ``sptree$fromList [()]``]
  \\ fs [wordSemTheory.cut_env_def,wordSemTheory.get_var_def,domain_lookup]
  \\ rw [] \\ simp [Replicate_code_def]
  \\ Cases_on `n`
  \\ simp [wordSemTheory.evaluate_def,wordSemTheory.call_env_def,
         wordSemTheory.get_var_def,word_exp_rw,fromList2_def,
         asmTheory.word_cmp_def,wordSemTheory.dec_clock_def]
  \\ fs [store_list_def,REPLICATE]
  \\ `inter r.locals (LS ()) = insert 0 ret_val LN` by
    (fs [spt_eq_thm,wf_insert,wf_def]
     \\ fs [lookup_inter,lookup_def,lookup_insert]
     \\ rw [] \\ every_case_tac \\ fs [])
  \\ `env_to_list (insert 0 ret_val LN) r.permute =
        ([(0,ret_val)],\n. r.permute (n+1))` by
   (fs [wordSemTheory.env_to_list_def,wordSemTheory.list_rearrange_def]
    \\ fs [EVAL ``(QSORT key_val_compare (toAList (insert 0 ret_val LN)))``]
    \\ fs [EVAL ``count 1``] \\ rw []
    \\ fs [BIJ_DEF,SURJ_DEF]) \\ fs []
  THEN1
   (fs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def]
    \\ fs [EVAL ``domain (fromAList [(0,ret_val)])``,wordSemTheory.set_var_def]
    \\ fs [fromAList_def,insert_shadow]
    \\ fs [wordSemTheory.state_component_equality])
  \\ NTAC 3 (once_rewrite_tac [list_Seq_def])
  \\ simp [wordSemTheory.evaluate_def,wordSemTheory.call_env_def,
           wordSemTheory.get_var_def,word_exp_rw,fromList2_def,
           wordSemTheory.set_var_def,wordSemTheory.mem_store_def,
           asmTheory.word_cmp_def,wordSemTheory.dec_clock_def]
  \\ fs [wordSemTheory.push_env_def]
  \\ fs [] \\ fs [lookup_insert]
  \\ fs [MULT_CLAUSES,GSYM word_add_n2w,list_Seq_def]
  \\ qmatch_goalsub_abbrev_tac`evaluate (Call NONE _ _ NONE,t5)`
  \\ qspecl_then [`n'`,`a + bytes_in_word`,`t5`] mp_tac Replicate_code_thm
  \\ disch_then (qspecl_then [`m1`,`0`,`2`,`4`,`6`,`8`] mp_tac)
  \\ impl_tac
  THEN1 (fs [wordSemTheory.get_var_def,lookup_insert,Abbr `t5`])
  \\ strip_tac \\ fs []
  \\ fs [wordSemTheory.pop_env_def,Abbr `t5`,
         EVAL ``domain (fromAList [(0,ret_val)])``]
  \\ fs [wordSemTheory.state_component_equality]
  \\ fs [fromAList_def,insert_shadow]
QED

val s = ``s:('c,'ffi)dataSem$state``

Theorem AnyArith_thm:
   ∀op_index i j v t s r2 r1 locs l2 l1 c.
     state_rel c l1 l2 ^s (t:('a,'c,'ffi) wordSem$state) [] locs /\
     get_vars [0;1;2] s.locals = SOME [Number i; Number j; Number (& op_index)] /\
     t.clock = MustTerminate_limit (:'a) - 2 /\ t.termdep <> 0 /\
     lookup 6 t.locals = SOME (Word (n2w (4 * op_index))) /\
     int_op op_index i j = SOME v ==>
     ?q r new_c.
       evaluate (AnyArith_code c,t) = (q,r) /\
       if q = SOME NotEnoughSpace then
         r.ffi = t.ffi
       else
         ?rv. q = SOME (Result (Loc l1 l2) rv) /\
              state_rel c r1 r2
                (s with <| locals := LN; clock := new_c; space := 0 |>) r
                [(Number v,rv)] locs
Proof
  rpt strip_tac \\ fs [AnyArith_code_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,wordSemTheory.word_exp_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ `get_var 1 s.locals = SOME (Number j) /\
      get_var 0 s.locals = SOME (Number i)` by
        fs [get_vars_SOME_IFF_data]
  \\ fs [wordSemTheory.evaluate_def,wordSemTheory.word_exp_def]
  \\ rpt_drule (GEN_ALL evaluate_AddNumSize)
  \\ disch_then kall_tac
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,wordSemTheory.word_exp_def]
  \\ pop_assum kall_tac
  \\ rpt_drule (GEN_ALL evaluate_AddNumSize)
  \\ disch_then kall_tac
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [eq_eval]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,wordSemTheory.word_exp_def]
  \\ fs [GSYM wordSemTheory.set_var_def]
  \\ Q.MATCH_GOALSUB_ABBREV_TAC `set_var 1 (Word w1)` \\ rveq
  \\ Q.MATCH_GOALSUB_ABBREV_TAC `evaluate (AllocVar _ _ _,t4)` \\ rveq
  \\ `state_rel c l1 l2 s t4 [] locs` by
   (unabbrev_all_tac
    \\ fs [wordSemTheory.set_var_def,state_rel_insert_1,state_rel_set_store_Temp]
    \\ NO_TAC)
  \\ `dataSem$cut_env (fromList [(); (); ()]) s.locals = SOME
         (fromList [Number i; Number j; Number (&op_index)])` by
   (fs [cut_env_def,SUBSET_DEF,domain_lookup,fromList_def,
        lookup_insert,lookup_def] \\ strip_tac \\ rw []
    \\ fs [get_vars_SOME_IFF_data,get_var_def]
    \\ fs [spt_eq_thm,wf_insert,wf_def,wf_inter]
    \\ fs [lookup_inter_alt,lookup_insert]
    \\ rw [lookup_def] \\ NO_TAC)
  \\ `get_var 1 t4 = SOME (Word w1)` by
   (unabbrev_all_tac \\ fs [wordSemTheory.get_var_def,
      lookup_insert,wordSemTheory.set_store_def,eq_eval] \\ NO_TAC)
  \\ pairarg_tac \\ fs []
  \\ `2 ** c.len_size < dimword (:α) DIV 8` by
   (fs [state_rel_thm,memory_rel_def,heap_in_memory_store_def]
    \\ fs [good_dimindex_def] \\ rfs [dimword_def]
    \\ rewrite_tac [MATCH_MP EXP_BASE_LT_MONO (DECIDE ``1<2n``),
         GSYM (EVAL ``2n**29``),GSYM (EVAL ``2n**61``)] \\ fs [])
  \\ rpt_drule AllocVar_thm
  \\ strip_tac \\ Cases_on `res = SOME NotEnoughSpace` \\ fs []
  THEN1 (fs [state_rel_def]) \\ fs []
  \\ qabbrev_tac `il = LENGTH ((SND (i2mw i)):'a word list)`
  \\ qabbrev_tac `jl = LENGTH ((SND (i2mw j)):'a word list)`
  \\ `w2n w1 DIV 4 + 1 = il + jl + 2` by
   (fs [word_add_n2w]
    \\ qsuff_tac `4 * il + (4 * jl) + 4 < dimword (:'a)`
    THEN1
     (qunabbrev_tac `w1` \\ fs []
      \\ qspecl_then [`4`,`il + jl + 1`] mp_tac MULT_DIV \\ fs [])
    \\ fs [get_vars_SOME_IFF_data]
    \\ imp_res_tac state_rel_IMP_num_size_limit \\ rfs []
    \\ fs [state_rel_def,good_dimindex_def] \\ rfs [dimword_def] \\ NO_TAC)
  \\ fs []
  \\ qabbrev_tac `s0 = (s with
          <|locals := fromList [Number i; Number j; Number (&op_index)];
            space := il + (jl + 2)|>)`
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ rpt_drule AnyHeader_thm
  \\ disch_then (qspecl_then [`i`,`F`,`0w`,`31w`,`12w`,`0`] mp_tac)
  \\ impl_tac THEN1
   (unabbrev_all_tac \\ fs [get_vars_SOME_IFF_data]
    \\ fs [fromList_def,get_var_def,lookup_insert])
  \\ fs [adjust_var_def] \\ strip_tac \\ fs []
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ qpat_abbrev_tac `s8 = set_store _ _ _`
  \\ `state_rel c l1 l2 s0 s8 [] locs` by
      (unabbrev_all_tac \\ fs [state_rel_set_store_Temp,state_rel_insert_7] \\ NO_TAC)
  \\ rpt_drule AnyHeader_thm
  \\ disch_then (qspecl_then [`j`,`T`,`1w`,`30w`,`11w`,`1`] mp_tac)
  \\ impl_tac THEN1
   (fs [get_vars_SOME_IFF_data,Abbr`s0`]
    \\ fs [fromList_def,get_var_def,lookup_insert])
  \\ fs [adjust_var_def] \\ strip_tac \\ fs []
  \\ qpat_abbrev_tac `s9 = set_store _ _ _`
  \\ `state_rel c l1 l2 s0 s9 [] locs` by
      (unabbrev_all_tac \\ fs [state_rel_set_store_Temp,
         wordSemTheory.set_var_def,state_rel_insert_7] \\ NO_TAC)
  \\ qunabbrev_tac `s8`
  \\ pop_assum mp_tac
  \\ simp [Once state_rel_thm,memory_rel_def]
  \\ fs [heap_in_memory_store_def]
  \\ strip_tac
  \\ `unused_space_inv a (sp+sp1) heap` by fs [word_ml_inv_def,abs_ml_inv_def]
  \\ fs [unused_space_inv_def]
  \\ `?k. sp + sp1 = il + jl + 2 + k` by
      (qexists_tac `(sp + sp1 - (il + jl + 2))`
       \\ unabbrev_all_tac \\ fs [] \\ NO_TAC)
  \\ fs []
  \\ rpt_drule heap_lookup_SPLIT
  \\ strip_tac
  \\ qpat_x_assum `(word_heap curr heap c * _) _` mp_tac
  \\ asm_rewrite_tac []
  \\ pop_assum (fn th => fs [th])
  \\ pop_assum (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def])
  \\ rveq
  \\ fs [word_heap_def,word_heap_APPEND,word_el_def]
  \\ `(il + (jl + (k + 2))) = 1 + (il + jl + 1) + k` by fs []
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ once_rewrite_tac [word_list_exists_ADD]
  \\ once_rewrite_tac [word_list_exists_ADD]
  \\ simp [Once word_list_exists_def]
  \\ simp [Once word_list_exists_def]
  \\ fs [SEP_CLAUSES,SEP_EXISTS_THM]
  \\ simp_tac (std_ss++sep_cond_ss) [cond_STAR]
  \\ strip_tac
  \\ `?x1. xs = [x1]` by
       (Cases_on `xs` \\ fs [] \\ Cases_on `t'` \\ fs [] \\ NO_TAC)
  \\ rveq \\ fs []
  \\ rename1 `LENGTH xs = il + (jl + 1)`
  \\ fs [word_list_def,SEP_CLAUSES]
  \\ `limit <> 0` by
   (fs [abs_ml_inv_def,heap_ok_def,word_ml_inv_def]
    \\ rveq \\ fs [Abbr`heap`]
    \\ fs [heap_length_APPEND]
    \\ fs [heap_length_def,el_length_def] \\ NO_TAC)
  \\ fs [word_heap_non_empty_limit]
  \\ fs [SEP_CLAUSES,SEP_EXISTS_THM]
  \\ `FLOOKUP s9.store (Temp 11w) = SOME (Word a3') /\
      FLOOKUP s9.store (Temp 12w) = SOME (Word a3) /\
      FLOOKUP s9.store (Temp 29w) = SOME (Word w1) /\
      FLOOKUP s9.store (Temp 31w) = SOME (Word a2) /\
      FLOOKUP s9.store (Temp 30w) = SOME (Word a2')` by
        (fs [Abbr`s9`,wordSemTheory.set_store_def,FLOOKUP_UPDATE,
           wordSemTheory.set_var_def,Abbr `t4`] \\ NO_TAC)
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ fs [wordSemTheory.mem_store_def]
  \\ SEP_R_TAC \\ fs []
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ fs [wordSemTheory.mem_store_def]
  \\ SEP_R_TAC \\ fs []
  \\ ntac 5 (once_rewrite_tac [list_Seq_def] \\ fs [eq_eval])
  \\ simp [wordSemTheory.set_store_def]
  \\ once_rewrite_tac [list_Seq_def] \\ fs []
  \\ once_rewrite_tac [eq_eval]
  \\ qpat_abbrev_tac `m5 = (_ =+ _) _`
  \\ fs [lookup_insert]
  \\ `lookup 6 s9.locals = SOME (Word (n2w (4 * op_index)))` by
   (`lookup 6 s9.locals = lookup 6 s1.locals` by
     (qunabbrev_tac `s9` \\ fs [lookup_insert,wordSemTheory.set_store_def])
    \\ asm_rewrite_tac []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ qpat_x_assum `state_rel c l1 l2 s0 s1 [] locs` mp_tac
    \\ rewrite_tac [state_rel_thm] \\ fs [] \\ strip_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ rpt_drule memory_rel_get_vars_IMP
    \\ `get_var 2 s0.locals = SOME (Number (& op_index))` by
         (qunabbrev_tac `s0` \\ EVAL_TAC \\ NO_TAC)
    \\ rpt_drule state_rel_get_var_IMP
    \\ simp [wordSemTheory.set_store_def,wordSemTheory.get_var_def,
             EVAL ``adjust_var 2``,lookup_insert]
    \\ strip_tac
    \\ disch_then (qspecl_then [`[Number (&op_index)]`,`[w]`,`[2]`] mp_tac)
    \\ fs [EVAL ``MAP adjust_var [2]``]
    \\ fs [get_vars_def,wordSemTheory.get_vars_def,wordSemTheory.get_var_def]
    \\ strip_tac
    \\ `small_int (:α) (&op_index)` by
     (qpat_x_assum `good_dimindex (:'a)` mp_tac
      \\ qpat_x_assum `int_op _ _ _ = _` mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ fs [good_dimindex_def,int_op_def]
      \\ every_case_tac \\ fs []
      \\ rw [] \\ fs [small_int_def,dimword_def] \\ NO_TAC)
    \\ rpt_drule (memory_rel_Number_IMP |> ONCE_REWRITE_RULE [CONJ_ASSOC]
                    |> ONCE_REWRITE_RULE [CONJ_COMM])
    \\ fs [Smallnum_def] \\ NO_TAC)
  \\ fs [lookup_insert]
  \\ fs [word_sh_def]
  \\ Q.MATCH_GOALSUB_ABBREV_TAC `evaluate (_,t9)` \\ rveq
  \\ qabbrev_tac `dm = s9.mdomain`
  \\ qabbrev_tac `m = s9.memory`
  \\ qpat_x_assum `_ (fun2set (m,dm))` mp_tac
  \\ fs [el_length_def]
  \\ qpat_abbrev_tac `hb_heap = word_list_exists _ k`
  \\ qpat_abbrev_tac `hb_heap1 = word_heap _ hb c`
  \\ qpat_abbrev_tac `other_heap = word_heap _ (heap_expand _) c`
  \\ strip_tac
  \\ `(word_list
          (curr + bytes_in_word + bytes_in_word * n2w (heap_length ha))
          xs * (word_heap curr ha c *
        one (curr + bytes_in_word * n2w (heap_length ha),Word a3) *
        hb_heap * hb_heap1 * one (other,Word a3') * other_heap))
         (fun2set (m5,dm))` by
    (fs [Abbr`m5`] \\ SEP_W_TAC \\ fs [AC STAR_COMM STAR_ASSOC] \\ NO_TAC)
  \\ drule word_list_store_list
  \\ strip_tac \\ fs []
  \\ qspecl_then [`Word 0w`,`Loc l1 l2`,`1`,`AnyArith_location`,`LENGTH xs`,
       `curr + bytes_in_word * n2w (heap_length ha)`,`t9`,`m2`,
       `2`,`3`,`1`] mp_tac
         (GEN_ALL Replicate_code_alt_thm |> SIMP_RULE std_ss [])
  \\ impl_tac THEN1
    (fs [Abbr `t9`,wordSemTheory.get_var_def,lookup_insert] \\ rfs []
     \\ qunabbrev_tac `w1` \\ fs [word_mul_n2w,word_add_n2w]
     \\ conj_tac THEN1
       (unabbrev_all_tac
        \\ fs [wordSemTheory.set_store_def,code_rel_def,stubs_def] \\ rfs [])
     \\ `s0.clock = t.clock` by
       (unabbrev_all_tac
        \\ fs [wordSemTheory.set_store_def,code_rel_def,stubs_def,state_rel_def])
     \\ simp []
     \\ drule MustTerminate_limit_SUB_2 \\ fs []
     \\ `il + (jl + 1) < dimword (:α) DIV 8` by
          (imp_res_tac LESS_TRANS \\ fs [] \\ NO_TAC)
     \\ qpat_assum `good_dimindex _` mp_tac
     \\ ntac 2 (pop_assum mp_tac)
     \\ rpt (pop_assum kall_tac)
     \\ rw [good_dimindex_def,dimword_def] \\ fs [dimword_def]
     \\ rfs [] \\ fs [])
  \\ strip_tac \\ simp []
  \\ pop_assum kall_tac
  \\ `t9.code = t.code /\ t9.termdep = t.termdep /\
      t9.mdomain = t.mdomain /\ t9.be = t.be` by
   (imp_res_tac wordSemTheory.evaluate_clock
    \\ unabbrev_all_tac
    \\ fs [wordSemTheory.set_store_def]
    \\ imp_res_tac evaluate_consts \\ fs [])
  \\ `FLOOKUP t9.store (Temp 29w) = SOME
        (Word (curr + bytes_in_word * n2w (heap_length ha)))` by
     (qunabbrev_tac `t9` \\ fs [wordSemTheory.set_store_def,FLOOKUP_UPDATE]
      \\ qunabbrev_tac `s9` \\ fs [wordSemTheory.set_store_def,FLOOKUP_UPDATE])
  \\ once_rewrite_tac [list_Seq_def]
  \\ simp [eq_eval,cut_env_fromList_sing]
  \\ once_rewrite_tac [list_Seq_def]
  \\ simp [eq_eval,cut_env_fromList_sing,wordSemTheory.set_store_def]
  \\ `code_rel c s.code t.code` by (fs [state_rel_def] \\ NO_TAC)
  \\ pop_assum mp_tac
  \\ rewrite_tac [code_rel_def,stubs_def,generated_bignum_stubs_def,LET_THM]
  \\ Cases_on `compile Bignum_location 1 1 (Bignum_location + 1,[]) mc_iop_code`
  \\ PairCases_on `r`
  \\ simp_tac (srw_ss())[APPEND,EVERY_DEF,EVAL ``domain (fromList [()]) = ∅``]
  \\ strip_tac
  \\ `il + (jl + 1) < dimword (:α) DIV 8` by fs []
  \\ IF_CASES_TAC THEN1
   (sg `F`
    \\ unabbrev_all_tac \\ fs [wordSemTheory.set_store_def]
    \\ rfs []
    \\ fs [DECIDE ``m + 1 = n + (k + 2:num) <=> m = n + k + 1``]
    \\ `s.clock = t.clock` by fs [state_rel_def] \\ rfs []
    \\ `LENGTH (SND (i2mw i):'a word list) +
       (LENGTH (SND (i2mw j):'a word list) + 1) < dimword (:α) DIV 8`
            by (imp_res_tac LESS_TRANS \\ fs [] \\ NO_TAC)
    \\ fs []
    \\ qpat_x_assum `_ <= _:num` mp_tac \\ simp[GSYM NOT_LESS]
    \\ fs [X_LT_DIV]
    \\ match_mp_tac LESS_TRANS
    \\ qexists_tac `2 * dimword (:'a)` \\ fs []
    \\ fs [wordSemTheory.MustTerminate_limit_def]
    \\ fs [dimword_def]
    \\ match_mp_tac (DECIDE ``n < k ==> n < k + l:num``)
    \\ rewrite_tac [prove(``n ** 2 = n * n:num``,fs []),ZERO_LESS_MULT]
    \\ fs [])
  \\ `t9.mdomain = dm` by
        (qunabbrev_tac `dm` \\ qunabbrev_tac `t9` \\ fs [])
  \\ Q.MATCH_GOALSUB_ABBREV_TAC `evaluate (Seq q (Return 0 0),t3)` \\ rveq
  \\ qabbrev_tac `my_frame = word_heap curr ha c *
         one (curr + bytes_in_word * n2w (heap_length ha),Word a3) *
         hb_heap * hb_heap1 * one (other,Word a3') * other_heap`
  \\ qspecl_then [`i`,`j`,`1`,`my_frame`,`REPLICATE (LENGTH xs) 0w`,`t3`,
          `Loc AnyArith_location 2`,`Bignum_location`,`t3.clock`,
          `get_iop op_index`] mp_tac
       (evaluate_mc_iop |> INST_TYPE [``:'d``|->``:'ffi``])
  \\ asm_rewrite_tac [] \\ simp_tac std_ss [AND_IMP_INTRO]
  \\ impl_tac THEN1
   (simp [LENGTH_REPLICATE]
    \\ simp_tac (srw_ss()) [word_bignumProofTheory.state_rel_def,GSYM CONJ_ASSOC]
    \\ simp [mc_multiwordTheory.mc_div_max_def,LENGTH_REPLICATE]
    \\ fs [X_LT_DIV]
    \\ `get_iop op_index ≠ Lt ∧
        get_iop op_index ≠ Eq ∧
        get_iop op_index ≠ Dec /\
        (get_iop op_index = Div ∨ get_iop op_index = Mod ⇒ j ≠ 0)` by
     (qpat_x_assum `int_op op_index i j = SOME v` mp_tac
      \\ rpt (pop_assum kall_tac) \\ fs []
      \\ fs [int_op_def]
      \\ every_case_tac \\ fs [] \\ EVAL_TAC \\ NO_TAC)
    \\ fs [] \\ `t3.code = t.code /\ t3.termdep = t.termdep` by
     (qunabbrev_tac `t3` \\ fs [wordSemTheory.push_env_def]
      \\ pairarg_tac \\ fs [] \\ NO_TAC) \\ fs []
    \\ `div_code_assum (:'ffi) (:'c) t.code` by metis_tac [div_code_assum_thm]
    \\ `get_var 0 t3 = SOME (Loc AnyArith_location 2)` by
          (qunabbrev_tac `t3` \\ fs [wordSemTheory.get_var_def] \\ NO_TAC)
    \\ simp []
    \\ imp_res_tac state_rel_imp_clock
    \\ `s9.clock = s1.clock` by
         (simp [Abbr`s9`,wordSemTheory.set_store_def] \\ NO_TAC)
    \\ `t3.clock = t9.clock − (il + (jl + 3))` by
         (simp [Abbr`t3`,wordSemTheory.set_store_def] \\ NO_TAC)
    \\ `t9.clock = s9.clock` by
         (simp [Abbr`t9`,wordSemTheory.set_store_def] \\ NO_TAC)
    \\ `s0.clock = s.clock` by
         (simp [Abbr`s0`,wordSemTheory.set_store_def] \\ fs [] \\ NO_TAC)
    \\ fs []
    \\ rewrite_tac [CONJ_ASSOC]
    \\ reverse conj_tac THEN1
     (match_mp_tac LESS_EQ_TRANS
      \\ qexists_tac `MustTerminate_limit (:α) - dimword (:'a) - dimword (:'a) - 5`
      \\ fs [LEFT_ADD_DISTRIB]
      \\ `il * jl <= dimword (:'a) * dimword (:'a)` by
           (match_mp_tac LESS_MONO_MULT2 \\ fs [])
      \\ `il * dimword (:α) <= dimword (:'a) * dimword (:'a)` by
           (match_mp_tac LESS_MONO_MULT2 \\ fs [])
      \\ `?k. MustTerminate_limit (:α) =
              10 * dimword (:'a) * dimword (:'a) +
              10 * dimword (:'a) + 100 + k` by metis_tac [MustTerminate_limit_eq]
      \\ qmatch_asmsub_abbrev_tac `_ * _ ≤ dd`
      \\ qmatch_goalsub_abbrev_tac `2 * ij`
      \\ `il < dimword (:'a) /\ jl < dimword (:'a)` by fs []
      \\ `dimindex (:'a) < dimword (:'a)` by
            (fs [good_dimindex_def] \\ simp [dimword_def])
      \\ fs [] \\ NO_TAC)
    \\ fs [SND_i2mw_NIL]
    \\ reverse conj_tac THEN1 (match_mp_tac mc_header_i2mw_eq_0w \\ fs [])
    \\ reverse conj_tac THEN1 (match_mp_tac mc_header_i2mw_eq_0w \\ fs [])
    \\ reverse conj_tac THEN1 metis_tac []
    \\ `t3.store = t9.store |+ (Temp 29w,
           Word (curr + bytes_in_word + bytes_in_word * n2w (heap_length ha))) /\
        t3.memory = m2 /\ t3.mdomain = t9.mdomain` by
     (qunabbrev_tac `t3` \\ simp_tac (srw_ss()) [wordSemTheory.push_env_def]
      \\ rw [] \\ pairarg_tac \\ asm_rewrite_tac []
      \\ simp_tac (srw_ss()) [] \\ asm_rewrite_tac [] \\ NO_TAC)
    \\ reverse conj_tac THEN1 (imp_res_tac IMP_bignum_code_rel \\ NO_TAC)
    \\ reverse conj_tac THEN1
     (qpat_x_assum `int_op op_index i j = SOME v` mp_tac
      \\ qpat_x_assum `good_dimindex (:'a)` mp_tac
      \\ asm_rewrite_tac [FLOOKUP_UPDATE]
      \\ rewrite_tac [FLOOKUP_DEF,FDOM_FEMPTY,NOT_IN_EMPTY]
      \\ qunabbrev_tac `t9`
      \\ qunabbrev_tac `s9`
      \\ simp_tac (srw_ss()) [wordSemTheory.set_store_def]
      \\ rpt (pop_assum kall_tac)
      \\ fs [FAPPLY_FUPDATE_THM]
      \\ rw [] \\ fs []
      \\ Cases_on `a = 0` \\ fs []
      \\ Cases_on `a = 1` \\ fs []
      \\ rveq \\ fs []
      \\ fs [int_op_def] \\ every_case_tac \\ fs []
      \\ rewrite_tac [GSYM w2n_11,w2n_lsr,w2n_n2w]
      \\ fs [good_dimindex_def,dimword_def]
      \\ EVAL_TAC \\ fs [dimword_def])
    \\ `FLOOKUP t9.store TempIn1 = SOME (Word a2) /\
        FLOOKUP t9.store TempIn2 = SOME (Word a2')` by
     (qunabbrev_tac `t9` \\ fs [wordSemTheory.set_store_def,FLOOKUP_UPDATE,
         EVAL ``TempOut``,EVAL ``TempIn1``,EVAL ``TempIn2``]
      \\ qunabbrev_tac `s9` \\ fs [wordSemTheory.set_store_def,FLOOKUP_UPDATE])
    \\ asm_rewrite_tac [FLOOKUP_UPDATE]
    \\ simp_tac (srw_ss()) [array_rel_def,APPLY_UPDATE_THM,GSYM PULL_EXISTS,
          EVAL ``TempOut``,EVAL ``TempIn1``,EVAL ``TempIn2``]
    \\ reverse (rpt strip_tac)
    \\ qpat_x_assum `_ (fun2set (m2,dm))` mp_tac
    THEN1 (fs [map_replicate])
    THEN1
     (Cases_on `j = 0` THEN1
       (qunabbrev_tac `jl` \\ fs [EVAL ``i2mw 0``]
        \\ fs [word_list_def,SEP_CLAUSES,map_replicate]
        \\ strip_tac \\ asm_exists_tac \\ fs [])
      \\ Cases_on `small_int (:'a) j` \\ fs [] THEN1
       (qunabbrev_tac `my_frame`
        \\ qunabbrev_tac `t9`
        \\ qunabbrev_tac `s9` \\ fs []
        \\ fs [EVAL ``TempIn2``,EVAL ``TempIn1``,
               wordSemTheory.set_store_def,FLOOKUP_UPDATE]
        \\ rveq \\ fs [word_list_def,SEP_CLAUSES]
        \\ strip_tac
        \\ qexists_tac `word_heap curr ha c *
             one (curr + bytes_in_word * n2w (heap_length ha),Word a3) *
             hb_heap * hb_heap1 * other_heap`
        \\ pop_assum mp_tac
        \\ simp_tac std_ss [AC STAR_COMM STAR_ASSOC,map_replicate])
      \\ simp_tac std_ss [map_replicate]
      \\ qmatch_goalsub_rename_tac `repl_list * my_frame`
      \\ fs [wordSemTheory.set_store_def,lookup_insert] \\ rveq
      \\ qpat_x_assum `lookup 4 s1.locals = SOME (Word w)` assume_tac
      \\ `get_real_addr c s1.store w = SOME x` by
            fs [get_real_addr_def,FLOOKUP_UPDATE]
      \\ qpat_x_assum `word_ml_inv _ _ _ _ _` assume_tac
      \\ `lookup 4 s9.locals = SOME (Word w)` by
        (qunabbrev_tac `s9`
         \\ simp_tac (srw_ss()) [wordSemTheory.set_store_def,lookup_insert]
         \\ asm_rewrite_tac [])
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ rpt_drule word_ml_inv_get_var_IMP
      \\ disch_then (qspecl_then [`Number j`,`1`,`Word w`] mp_tac)
      \\ impl_tac THEN1
       (asm_rewrite_tac [EVAL ``adjust_var 0``,EVAL ``adjust_var 1``,
               wordSemTheory.get_var_def,get_var_def]
        \\ qunabbrev_tac `s0` \\ EVAL_TAC)
      \\ qmatch_goalsub_rename_tac `((Number j,Word w)::vars)`
      \\ asm_simp_tac (srw_ss()) [word_ml_inv_def,abs_ml_inv_def,
             bc_stack_ref_inv_def,PULL_EXISTS,v_inv_def,word_addr_def]
      \\ rpt strip_tac \\ rveq
      \\ `curr + bytes_in_word * n2w ptr = x` by
       (rpt_drule get_real_addr_get_addr
        \\ qpat_x_assum `get_real_addr _ _ _ = _` mp_tac
        \\ `FLOOKUP s1.store CurrHeap = SOME (Word curr)` by
         (unabbrev_all_tac \\ simp_tac (srw_ss()) []
          \\ fs [wordSemTheory.set_store_def,FLOOKUP_UPDATE])
        \\ asm_simp_tac (srw_ss()) [get_real_addr_def]
        \\ rpt strip_tac \\ fs [])
      \\ rveq
      \\ qunabbrev_tac `my_frame`
      \\ qunabbrev_tac `hb_heap1`
      \\ qunabbrev_tac `heap`
      \\ full_simp_tac std_ss [APPEND]
      \\ fs [heap_lookup_APPEND]
      \\ Cases_on `ptr < heap_length ha` \\ full_simp_tac std_ss []
      THEN1
       (drule heap_lookup_SPLIT
        \\ strip_tac \\ rveq
        \\ qpat_x_assum `_ (fun2set _)` mp_tac
        \\ simp_tac std_ss [word_heap_APPEND,word_heap_def,word_el_def,
              Bignum_def,LET_THM]
        \\ pairarg_tac
        \\ asm_simp_tac std_ss [word_el_def,word_payload_def,LET_THM,word_list_def]
        \\ strip_tac \\ fs []
        \\ qmatch_goalsub_rename_tac `a * repl_list`
        \\ qabbrev_tac `b = repl_list`
        \\ full_simp_tac std_ss [AC STAR_COMM STAR_ASSOC]
        \\ asm_exists_tac \\ asm_rewrite_tac [])
      \\ full_simp_tac std_ss [heap_lookup_Unused_Bignum]
      THEN1
       (drule heap_lookup_SPLIT
        \\ strip_tac \\ rveq
        \\ qpat_x_assum `_ (fun2set _)` mp_tac
        \\ simp_tac std_ss [word_heap_APPEND,word_heap_def,word_el_def,
              Bignum_def,LET_THM]
        \\ pairarg_tac
        \\ asm_simp_tac std_ss [word_el_def,word_payload_def,LET_THM,word_list_def]
        \\ `ptr = heap_length ha' + heap_length ha + (il + (jl + (k + 2)))`
              by decide_tac \\ rveq \\ fs []
        \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
        \\ strip_tac \\ fs []
        \\ qmatch_goalsub_rename_tac `a * repl_list`
        \\ qabbrev_tac `b = repl_list`
        \\ full_simp_tac std_ss [AC STAR_COMM STAR_ASSOC]
        \\ asm_exists_tac \\ asm_rewrite_tac []))
    THEN1
     (Cases_on `i = 0` THEN1
       (qunabbrev_tac `il` \\ fs [EVAL ``i2mw 0``]
        \\ fs [word_list_def,SEP_CLAUSES,map_replicate]
        \\ strip_tac \\ asm_exists_tac \\ fs [])
      \\ Cases_on `small_int (:'a) i` \\ fs [] THEN1
       (qunabbrev_tac `my_frame`
        \\ qunabbrev_tac `t9`
        \\ qunabbrev_tac `s9` \\ fs []
        \\ fs [EVAL ``TempIn2``,EVAL ``TempIn1``,
               wordSemTheory.set_store_def,FLOOKUP_UPDATE]
        \\ rveq \\ fs [word_list_def,SEP_CLAUSES]
        \\ strip_tac
        \\ qexists_tac `word_heap curr ha c *
             one (other,Word a3') * hb_heap * hb_heap1 * other_heap`
        \\ pop_assum mp_tac
        \\ simp_tac std_ss [AC STAR_COMM STAR_ASSOC,map_replicate])
      \\ simp_tac std_ss [map_replicate]
      \\ qmatch_goalsub_rename_tac `repl_list * my_frame`
      \\ fs [wordSemTheory.set_store_def,lookup_insert] \\ rveq
      \\ qpat_x_assum `lookup 2 s1.locals = SOME (Word w)` assume_tac
      \\ `get_real_addr c s1.store w = SOME x` by
            fs [get_real_addr_def,FLOOKUP_UPDATE]
      \\ qpat_x_assum `word_ml_inv _ _ _ _ _` assume_tac
      \\ `lookup 2 s9.locals = SOME (Word w)` by
        (qunabbrev_tac `s9`
         \\ simp_tac (srw_ss()) [wordSemTheory.set_store_def,lookup_insert]
         \\ asm_rewrite_tac [])
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ rpt_drule word_ml_inv_get_var_IMP
      \\ disch_then (qspecl_then [`Number i`,`0`,`Word w`] mp_tac)
      \\ impl_tac THEN1
       (asm_rewrite_tac [EVAL ``adjust_var 0``,EVAL ``adjust_var 1``,
               wordSemTheory.get_var_def,get_var_def]
        \\ qunabbrev_tac `s0` \\ EVAL_TAC)
      \\ qmatch_goalsub_rename_tac `((Number i,Word w)::vars)`
      \\ asm_simp_tac (srw_ss()) [word_ml_inv_def,abs_ml_inv_def,
             bc_stack_ref_inv_def,PULL_EXISTS,v_inv_def,word_addr_def]
      \\ rpt strip_tac \\ rveq
      \\ `curr + bytes_in_word * n2w ptr = x` by
       (rpt_drule get_real_addr_get_addr
        \\ qpat_x_assum `get_real_addr _ _ _ = _` mp_tac
        \\ `FLOOKUP s1.store CurrHeap = SOME (Word curr)` by
         (unabbrev_all_tac \\ simp_tac (srw_ss()) []
          \\ fs [wordSemTheory.set_store_def,FLOOKUP_UPDATE])
        \\ asm_simp_tac (srw_ss()) [get_real_addr_def]
        \\ rpt strip_tac \\ fs [])
      \\ rveq
      \\ qunabbrev_tac `my_frame`
      \\ qunabbrev_tac `hb_heap1`
      \\ qunabbrev_tac `heap`
      \\ full_simp_tac std_ss [APPEND]
      \\ fs [heap_lookup_APPEND]
      \\ Cases_on `ptr < heap_length ha` \\ full_simp_tac std_ss []
      THEN1
       (drule heap_lookup_SPLIT
        \\ strip_tac \\ rveq
        \\ qpat_x_assum `_ (fun2set _)` mp_tac
        \\ simp_tac std_ss [word_heap_APPEND,word_heap_def,word_el_def,
              Bignum_def,LET_THM]
        \\ pairarg_tac
        \\ asm_simp_tac std_ss [word_el_def,word_payload_def,LET_THM,word_list_def]
        \\ strip_tac \\ fs []
        \\ qmatch_goalsub_rename_tac `a * repl_list`
        \\ qabbrev_tac `b = repl_list`
        \\ full_simp_tac std_ss [AC STAR_COMM STAR_ASSOC]
        \\ asm_exists_tac \\ asm_rewrite_tac [])
      \\ full_simp_tac std_ss [heap_lookup_Unused_Bignum]
      THEN1
       (drule heap_lookup_SPLIT
        \\ strip_tac \\ rveq
        \\ qpat_x_assum `_ (fun2set _)` mp_tac
        \\ simp_tac std_ss [word_heap_APPEND,word_heap_def,word_el_def,
              Bignum_def,LET_THM]
        \\ pairarg_tac
        \\ asm_simp_tac std_ss [word_el_def,word_payload_def,LET_THM,word_list_def]
        \\ `ptr = heap_length ha' + heap_length ha + (il + (jl + (k + 2)))`
              by decide_tac \\ rveq \\ fs []
        \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
        \\ strip_tac \\ fs []
        \\ qmatch_goalsub_rename_tac `a * repl_list`
        \\ qabbrev_tac `b = repl_list`
        \\ full_simp_tac std_ss [AC STAR_COMM STAR_ASSOC]
        \\ asm_exists_tac \\ asm_rewrite_tac [])))
  \\ strip_tac \\ simp []
  \\ rewrite_tac [eq_eval]
  \\ fs [wordSemTheory.get_var_def,push_env_insert_0]
  \\ simp [Abbr `t3`,wordSemTheory.pop_env_def,
       EVAL ``domain (fromAList [(0,x)])``]
  \\ simp_tac std_ss [fromAList_def]
  \\ `int_op (get_iop op_index) i j = v` by
   (qpat_x_assum `_ = SOME v` mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ fs [int_op_def] \\ rw [] \\ EVAL_TAC)
  \\ full_simp_tac std_ss [] \\ pop_assum kall_tac
  \\ `FLOOKUP t2.store (Temp 10w) = SOME (Word (mc_header (i2mw v)))` by
   (qpat_x_assum `state_rel _ _ _ _ _` mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ rewrite_tac [word_bignumProofTheory.state_rel_def]
    \\ rpt strip_tac
    \\ qpat_x_assum `∀a v. _ ==> _` mp_tac
    \\ simp_tac (srw_ss()) [FLOOKUP_UPDATE] \\ NO_TAC)
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval,insert_shadow]
  \\ `(mc_header (i2mw v) = 0w:'a word <=> v = 0) /\
      (mc_header (i2mw v) = 2w:'a word <=> ?v1. i2mw v = (F,[v1:'a word])) /\
      (mc_header (i2mw v) = 3w:'a word <=> ?v1. i2mw v = (T,[v1:'a word]))` by
   (fs [LENGTH_REPLICATE]
    \\ qpat_x_assum `LENGTH _ + LENGTH _ = _` (fn th => fs[GSYM th])
    \\ fs [multiwordTheory.i2mw_def]
    \\ Cases_on `v` \\ fs [mc_multiwordTheory.mc_header_def]
    \\ fs [X_LT_DIV,word_add_n2w]
    \\ once_rewrite_tac [multiwordTheory.n2mw_def]
    \\ rw [] \\ simp_tac std_ss [GSYM LENGTH_NIL] \\ intLib.COOPER_TAC)
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ `t2.be = s1.be` by
   (imp_res_tac evaluate_consts
    \\ rfs [] \\ unabbrev_all_tac
    \\ fs [wordSemTheory.set_store_def] \\ asm_rewrite_tac []
    \\ qpat_x_assum `state_rel _ _ _ _ _` mp_tac
    \\ rewrite_tac [word_bignumProofTheory.state_rel_def]
    \\ simp_tac (srw_ss()) [])
  \\ `FLOOKUP t2.store CurrHeap = FLOOKUP s9.store CurrHeap /\
      FLOOKUP t2.store OtherHeap = FLOOKUP s9.store OtherHeap /\
      FLOOKUP t2.store NextFree = FLOOKUP s9.store NextFree /\
      FLOOKUP t2.store EndOfHeap = FLOOKUP s9.store EndOfHeap /\
      FLOOKUP t2.store Globals = FLOOKUP s9.store Globals` by
   (qunabbrev_tac `s9` \\ qunabbrev_tac `t9`
    \\ qpat_x_assum `state_rel _ _ _ _ _` mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ fs [wordSemTheory.set_store_def]
    \\ rewrite_tac [word_bignumProofTheory.state_rel_def]
    \\ rpt strip_tac \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [FLOOKUP_UPDATE])
  \\ `Globals ∈ FDOM t2.store` by
       (pop_assum mp_tac \\ fs [FLOOKUP_DEF])
  \\ `∃new_c.
        state_rel c r1 r2
          (s with <|locals := LN; clock := new_c; space := il + jl + 2|>)
          (t2 with <|locals := LN; stack := t9.stack|>)
             [(Number 0,Word 0w)] locs` by
   (qmatch_asmsub_abbrev_tac `clock_write new_clock_val`
    \\ qexists_tac `new_clock_val`
    \\ fs [Abbr `s9`,wordSemTheory.set_store_def]
    \\ simp_tac (srw_ss()) [state_rel_thm] \\ asm_rewrite_tac []
    \\ simp_tac (srw_ss()) [EVAL ``join_env LN []``]
    \\ qunabbrev_tac `t9` \\ asm_simp_tac (srw_ss()) [lookup_def]
    \\ qpat_x_assum `state_rel _ _ _ _ _` mp_tac
    \\ rewrite_tac [word_bignumProofTheory.state_rel_def]
    \\ simp_tac (srw_ss()) [FLOOKUP_UPDATE,TempOut_def]
    \\ qunabbrev_tac `s0` \\ full_simp_tac (srw_ss()) []
    \\ rpt strip_tac
    THEN1
     (qpat_x_assum `code_oracle_rel _ s_compile s_compile_oracle t_store t_compile
                      t_compile_oracle t_code_buffer t_data_buffer` mp_tac
      \\ simp [code_oracle_rel_def,FLOOKUP_UPDATE])
    \\ rewrite_tac [GSYM (EVAL ``Smallnum 0``)]
    \\ match_mp_tac IMP_memory_rel_Number
    \\ imp_res_tac small_int_0
    \\ asm_rewrite_tac []
    \\ asm_simp_tac std_ss [memory_rel_def]
    \\ qexists_tac `heap`
    \\ qexists_tac `limit`
    \\ qexists_tac `heap_length ha`
    \\ qexists_tac `sp`
    \\ qexists_tac `sp1`
    \\ qexists_tac `gens`
    \\ reverse (rpt strip_tac)
    THEN1 (simp [])
    THEN1 asm_simp_tac std_ss []
    THEN1
     (qpat_x_assum `word_ml_inv _ _ _ _ _` mp_tac
      \\ match_mp_tac word_ml_inv_rearrange
      \\ fs [] \\ rpt strip_tac \\ asm_rewrite_tac []
      \\ full_simp_tac (srw_ss()) [FAPPLY_FUPDATE_THM,FLOOKUP_UPDATE]
      \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF]
      \\ first_x_assum (qspec_then `Globals` mp_tac)
      \\ asm_simp_tac (srw_ss()) [FLOOKUP_DEF] \\ rfs [])
    \\ asm_simp_tac std_ss [heap_in_memory_store_def]
    \\ simp_tac (srw_ss()) [AC ADD_COMM ADD_ASSOC] \\ asm_rewrite_tac []
    \\ full_simp_tac (srw_ss()) [FLOOKUP_UPDATE]
    \\ full_simp_tac std_ss [array_rel_def]
    \\ qpat_x_assum `_ (fun2set _)` mp_tac
    \\ rpt (qpat_x_assum `_ (fun2set _)` kall_tac)
    \\ full_simp_tac (srw_ss()) [APPLY_UPDATE_THM] \\ rveq
    \\ asm_simp_tac (srw_ss()) [word_heap_non_empty_limit]
    \\ qunabbrev_tac `my_frame`
    \\ qunabbrev_tac `heap`
    \\ simp_tac std_ss [word_heap_APPEND,word_heap_def,heap_length_APPEND,
         SEP_CLAUSES,word_el_def]
    \\ simp_tac std_ss [EVAL ``heap_length [Unused k]``]
    \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ simp_tac std_ss [word_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ simp_tac (std_ss++sep_cond_ss) [cond_STAR]
    \\ qunabbrev_tac `hb_heap`
    \\ simp_tac std_ss [word_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ simp_tac (std_ss++sep_cond_ss) [cond_STAR]
    \\ strip_tac \\ rename1 `LENGTH leftover = k` \\ rveq
    \\ fs [GSYM WORD_LEFT_ADD_DISTRIB,word_add_n2w]
    \\ fs [WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w]
    \\ qexists_tac `Word a3'`
    \\ qexists_tac `Word a3 :: MAP Word (SND (i2mw v)) ++ MAP Word zs1 ++ leftover`
    \\ conj_tac THEN1 fs [LENGTH_REPLICATE,ADD1]
    \\ full_simp_tac std_ss [APPEND_ASSOC,APPEND]
    \\ qpat_abbrev_tac `ts = MAP Word (SND (i2mw v)) ++ MAP Word zs1`
    \\ fs [LENGTH_REPLICATE,ADD1,word_list_def,word_list_APPEND]
    \\ `LENGTH ts = il + (jl + 1)` by (qunabbrev_tac `ts` \\ fs [])
    \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ fs [AC STAR_ASSOC STAR_COMM] \\ NO_TAC)
  \\ IF_CASES_TAC \\ simp [] (* v = 0 *)
  THEN1
   (rveq \\ full_simp_tac std_ss []
    \\ drule state_rel_with_clock_0
    \\ simp_tac (srw_ss()) [] \\ strip_tac
    \\ asm_exists_tac \\ asm_rewrite_tac [])
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ `FLOOKUP t2.store NextFree =
        SOME (Word (curr + bytes_in_word * n2w (heap_length ha))) /\
      curr + bytes_in_word + bytes_in_word * n2w (heap_length ha) ∈
         t2.mdomain /\
      t2.memory (curr + bytes_in_word +
         bytes_in_word * n2w (heap_length ha)) = Word (HD (SND (i2mw v)))` by
   (fs [GSYM TempOut_def]
    \\ qpat_x_assum `v <> 0` mp_tac
    \\ asm_rewrite_tac []
    \\ qpat_x_assum `state_rel _ _ _ _ _` mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ rewrite_tac [word_bignumProofTheory.state_rel_def]
    \\ strip_tac
    \\ qpat_x_assum `array_rel _ _ _ _ _ _ _` mp_tac
    \\ qpat_x_assum `_ = _` mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ fs [array_rel_def,APPLY_UPDATE_THM,FLOOKUP_UPDATE]
    \\ rpt (disch_then strip_assume_tac)
    \\ `?x xs. SND (i2mw v):'a word list = x::xs` by
     (fs [multiwordTheory.i2mw_def]
      \\ once_rewrite_tac [multiwordTheory.n2mw_def]
      \\ rw [] \\ intLib.COOPER_TAC)
    \\ fs [word_list_def] \\ SEP_R_TAC \\ fs [] \\ NO_TAC)
  \\ simp []
  \\ qpat_abbrev_tac `if_stmt = wordLang$If _ _ _ _ _`
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ Cases_on `small_int (:'a) v`
  THEN1
   (qunabbrev_tac `if_stmt` \\ fs [eq_eval]
    \\ IF_CASES_TAC THEN1
     (fs [word_sh_def,lookup_insert]
      \\ `v1 >>> (dimindex (:α) - 3) = 0w /\
          v1 << 2 = Smallnum v` by
       (ntac 2 (pop_assum mp_tac)
        \\ qpat_x_assum `good_dimindex (:'a)` mp_tac
        \\ rpt (pop_assum kall_tac)
        \\ fs [multiwordTheory.i2mw_def]
        \\ Cases_on `v` \\ fs [EVAL ``n2mw 0``]
        \\ once_rewrite_tac [multiwordTheory.n2mw_def]
        \\ IF_CASES_TAC \\ fs []
        \\ once_rewrite_tac [multiwordTheory.n2mw_def]
        \\ IF_CASES_TAC \\ fs [] \\ rw []
        \\ `Num (ABS (&n)) = n` by intLib.COOPER_TAC
        \\ fs [DIV_EQ_X,Smallnum_def,WORD_MUL_LSL,word_mul_n2w]
        \\ rewrite_tac [GSYM w2n_11,w2n_lsr]
        \\ fs [] \\ fs [DIV_EQ_X]
        \\ rfs [good_dimindex_def,small_int_def,dimword_def]
        \\ rfs [good_dimindex_def,small_int_def,dimword_def])
      \\ fs []
      \\ drule state_rel_with_clock_0
      \\ simp_tac (srw_ss()) [] \\ strip_tac
      \\ rpt_drule state_rel_Number_small_int
      \\ strip_tac \\ asm_exists_tac \\ asm_rewrite_tac [])
    \\ IF_CASES_TAC THEN1
     (fs [word_sh_def,lookup_insert]
      \\ `(v1 + -1w) >>> (dimindex (:α) - 3) = 0w /\
          -1w * v1 << 2 = Smallnum v` by
       (ntac 3 (pop_assum mp_tac)
        \\ qpat_x_assum `good_dimindex (:'a)` mp_tac
        \\ rpt (pop_assum kall_tac)
        \\ fs [multiwordTheory.i2mw_def]
        \\ Cases_on `v` \\ fs [EVAL ``n2mw 0``]
        \\ `Num (ABS (-&n)) = n` by intLib.COOPER_TAC \\ fs []
        \\ once_rewrite_tac [multiwordTheory.n2mw_def]
        \\ IF_CASES_TAC \\ fs []
        \\ once_rewrite_tac [multiwordTheory.n2mw_def]
        \\ IF_CASES_TAC \\ fs [] \\ rw []
        \\ fs [DIV_EQ_X,Smallnum_def,WORD_MUL_LSL,word_mul_n2w]
        \\ rewrite_tac [GSYM (SIMP_CONV (srw_ss()) [] ``-w:'a word``)]
        \\ Cases_on `n` \\ fs [ADD1,GSYM word_add_n2w]
        \\ rewrite_tac [GSYM w2n_11,w2n_lsr]
        \\ fs [] \\ fs [DIV_EQ_X]
        \\ rfs [good_dimindex_def,small_int_def,dimword_def]
        \\ rfs [good_dimindex_def,small_int_def,dimword_def])
      \\ fs []
      \\ drule state_rel_with_clock_0
      \\ simp_tac (srw_ss()) [] \\ strip_tac
      \\ rpt_drule state_rel_Number_small_int
      \\ strip_tac \\ asm_exists_tac \\ asm_rewrite_tac [])
    \\ sg `F` \\ fs []
    \\ rpt_drule i2mw_small_int_IMP_0)
  \\ qmatch_goalsub_abbrev_tac `evaluate (if_stmt,t8)`
  \\ `?w. evaluate (if_stmt,t8) = (NONE, set_var 5 w t8)` by
   (qunabbrev_tac `t8` \\ qunabbrev_tac `if_stmt`
    \\ simp [eq_eval,word_sh_def]
    \\ IF_CASES_TAC \\ simp [] THEN1
     (full_simp_tac std_ss [HD]
      \\ reverse IF_CASES_TAC \\ full_simp_tac std_ss []
      \\ simp_tac (srw_ss()) [wordSemTheory.state_component_equality]
      THEN1 metis_tac []
      \\ ntac 3 (pop_assum mp_tac)
      \\ qpat_x_assum `good_dimindex _` mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ fs [multiwordTheory.i2mw_def]
      \\ once_rewrite_tac [multiwordTheory.n2mw_def]
      \\ rw [] \\ rewrite_tac [GSYM w2n_11,w2n_lsr]
      \\ Cases_on `v`
      \\ fs [small_int_def,good_dimindex_def,dimword_def,multiwordTheory.n2mw_NIL]
      \\ fs [DIV_EQ_X] \\ rfs []
      \\ fs [intLib.COOPER_PROVE ``Num (ABS (&n)) = n``])
    \\ IF_CASES_TAC \\ fs [] THEN1
     (full_simp_tac std_ss [HD]
      \\ reverse IF_CASES_TAC \\ full_simp_tac std_ss []
      \\ simp_tac (srw_ss()) [wordSemTheory.state_component_equality]
      THEN1 metis_tac []
      \\ ntac 4 (pop_assum mp_tac)
      \\ qpat_x_assum `good_dimindex _` mp_tac
      \\ qpat_x_assum `v <> 0` mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ Cases_on `v`
      \\ fs [multiwordTheory.i2mw_def] \\ rfs []
      \\ once_rewrite_tac [multiwordTheory.n2mw_def]
      \\ rw [] \\ rewrite_tac [GSYM w2n_11,w2n_lsr]
      \\ fs [intLib.COOPER_PROVE ``Num (ABS (-&n)) = n``,n2w_mod]
      \\ Cases_on `n` \\ fs [GSYM word_add_n2w,ADD1]
      \\ fs [small_int_def,good_dimindex_def,dimword_def,multiwordTheory.n2mw_NIL]
      \\ fs [DIV_EQ_X] \\ rfs [])
    \\ simp_tac (srw_ss()) [wordSemTheory.state_component_equality]
    \\ metis_tac [])
  \\ asm_rewrite_tac [] \\ pop_assum kall_tac
  \\ simp_tac (srw_ss()) [wordSemTheory.set_var_def,Abbr `t8`]
  \\ qunabbrev_tac `if_stmt`
  \\ qpat_x_assum `SOME _ = _` (assume_tac o GSYM)
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ simp [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ simp [eq_eval]
  \\ qpat_x_assum `word_bignumProof$state_rel _ _ _ _ _` mp_tac
  \\ full_simp_tac std_ss [array_rel_def,word_bignumProofTheory.state_rel_def]
  \\ simp_tac (srw_ss()) [FLOOKUP_UPDATE,TempOut_def,APPLY_UPDATE_THM]
  \\ asm_simp_tac std_ss []
  \\ strip_tac
  \\ qpat_x_assum `!a v. _` kall_tac \\ fs [] \\ rveq
  \\ qpat_x_assum `_ (fun2set _)` mp_tac
  \\ rpt (qpat_x_assum `_ (fun2set _)` kall_tac)
  \\ qunabbrev_tac `my_frame`
  \\ strip_tac
  \\ once_rewrite_tac [list_Seq_def]
  \\ simp [eq_eval,wordSemTheory.mem_store_def]
  \\ SEP_R_TAC \\ simp_tac (srw_ss()) []
  \\ qmatch_goalsub_abbrev_tac `next_addr =+ Word new_header`
  \\ qabbrev_tac `m22 = t2.memory`
  \\ qabbrev_tac `dm22 = t2.mdomain`
  \\ SEP_W_TAC \\ qpat_x_assum `_ (fun2set _)` mp_tac
  \\ rpt (qpat_x_assum `_ (fun2set _)` kall_tac)
  \\ strip_tac
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ simp [eq_eval]
  \\ qmatch_goalsub_abbrev_tac `insert 1 (Word new_ret_val)`
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma] \\ simp [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval,wordSemTheory.set_store_def]
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval]
  \\ simp [state_rel_thm,lookup_def,EVAL ``join_env LN []``,FAPPLY_FUPDATE_THM]
  \\ rewrite_tac [CONJ_ASSOC]
  \\ qpat_x_assum `state_rel c r1 r2 _ _ _ _` mp_tac
  \\ fs [state_rel_thm,EVAL ``join_env LN []``]
  \\ strip_tac
  \\ rpt_drule IMP_memory_rel_bignum_alt
  \\ fs [Bignum_def]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ simp_tac (srw_ss()) []
  \\ `mc_header (i2mw v:bool # 'a word list) >>> 1 =
      n2w (LENGTH (SND (i2mw v):'a word list))` by
   (rewrite_tac [GSYM w2n_11,w2n_lsr,multiwordTheory.i2mw_def,SND,
          mc_multiwordTheory.mc_header_def] \\ rw [word_add_n2w]
    \\ `(2 * LENGTH (n2mw (Num (ABS v)):'a word list) + 1) < dimword (:α)` by
          fs [LENGTH_REPLICATE,X_LT_DIV,multiwordTheory.i2mw_def]
    \\ simp [DIV_MULT |> ONCE_REWRITE_RULE [MULT_COMM]]
    \\ simp [MULT_DIV |> ONCE_REWRITE_RULE [MULT_COMM]] \\ NO_TAC)
  \\ disch_then (qspecl_then [`SND (i2mw v):'a word list`,`new_header`] mp_tac)
  \\ impl_tac THEN1
   (fs [LENGTH_REPLICATE]
    \\ full_simp_tac std_ss [encode_header_def,multiwordTheory.i2mw_def]
    \\ qunabbrev_tac `new_header`
    \\ fs [make_header_def]
    \\ qmatch_goalsub_abbrev_tac `mc_header hh`
    \\ `(mc_header hh ≪ 4 && 1w ≪ 4) = (b2w (v < 0) ≪ 4):'a word` by
     (rewrite_tac [LSL_BITWISE] \\ AP_THM_TAC \\ AP_TERM_TAC
      \\ qunabbrev_tac `hh`
      \\ simp_tac std_ss [mc_multiwordTheory.mc_header_AND_1]
      \\ Cases_on `v < 0i` \\ asm_rewrite_tac [] \\ EVAL_TAC \\ NO_TAC)
    \\ asm_rewrite_tac []
    \\ reverse conj_tac THEN1 simp [WORD_MUL_LSL]
    \\ rpt strip_tac THEN1
     (match_mp_tac LESS_LESS_EQ_TRANS
      \\ qexists_tac `2 ** 3` \\ simp []
      \\ qpat_x_assum `good_dimindex _` mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ Cases_on `v < 0i` \\ simp [] \\ EVAL_TAC
      \\ rw [] \\ fs [dimword_def])
    THEN1
     (qpat_x_assum `good_dimindex _` mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ Cases_on `v < 0i` \\ simp [] \\ EVAL_TAC
      \\ rw [] \\ fs [dimword_def])
    \\ match_mp_tac LESS_EQ_LESS_TRANS
    \\ qexists_tac `2 ** c.len_size` \\ fs [])
  \\ fs [store_list_def] \\ strip_tac
  \\ `(next_addr =+ Word new_header) m22 = m1` by
   (`next_addr + bytes_in_word =
     curr + bytes_in_word + bytes_in_word * n2w (heap_length ha)` by
      (qunabbrev_tac `next_addr` \\ simp [])
    \\ full_simp_tac std_ss [word_list_APPEND,GSYM STAR_ASSOC]
    \\ drule word_list_IMP_store_list \\ fs [])
  \\ fs [] \\ pop_assum kall_tac
  \\ fs [shift_lsl]
  \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ pop_assum mp_tac
  \\ qpat_abbrev_tac `other_new_ret = make_ptr _ _ _ _`
  \\ `other_new_ret = Word new_ret_val` by
   (qunabbrev_tac `other_new_ret`
    \\ qunabbrev_tac `new_ret_val`
    \\ fs [make_ptr_def])
  \\ fs [] \\ pop_assum kall_tac
  \\ strip_tac
  \\ drule memory_rel_zero_space
  \\ match_mp_tac memory_rel_rearrange
  \\ rpt (pop_assum kall_tac)
  \\ fs [] \\ rw [] \\ fs []
QED

Theorem MAP_FST_EQ_IMP_IS_SOME_ALOOKUP:
   !xs ys.
      MAP FST xs = MAP FST ys ==>
      IS_SOME (ALOOKUP xs n) = IS_SOME (ALOOKUP ys n)
Proof
  Induct \\ fs [] \\ Cases \\ Cases_on `ys` \\ fs []
  \\ Cases_on `h` \\ fs [] \\ rw []
QED

Theorem eval_Call_Arith:
   !index r.
      state_rel c l1 l2 ^s (t:('a,'c,'ffi) wordSem$state) [] locs /\
      names_opt ≠ NONE /\ 1 < t.termdep /\
      get_vars [a1; a2] x.locals = SOME [Number i1; Number i2] /\
      cut_state_opt names_opt s = SOME x /\
      int_op index i1 i2 = SOME r ==>
      ∃q r'.
        (λ(res,s1).
           if res = NONE then
             evaluate (list_Seq [Move 2 [(adjust_var dest,1)]],s1)
           else (res,s1))
          (evaluate
            (MustTerminate
              (Call (SOME (1,adjust_set (get_names names_opt),Skip,n,l))
                (SOME (Arith_location index))
                [adjust_var a1; adjust_var a2] NONE),t)) = (q,r') ∧
        (q = SOME NotEnoughSpace ⇒ r'.ffi = s.ffi) ∧
        (q ≠ SOME NotEnoughSpace ⇒
         state_rel c l1 l2
           (x with
            <|locals := insert dest (Number r) x.locals; space := 0|>)
           r' [] locs ∧ q = NONE)
Proof
  rpt strip_tac \\ drule (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ imp_res_tac state_rel_cut_IMP
  \\ Cases_on `names_opt` \\ fs []
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ `get_vars [a1; a2] s.locals = SOME [Number i1; Number i2]` by
   (fs [cut_state_opt_def,cut_state_def,cut_env_def]
    \\ every_case_tac \\ fs [get_vars_def,get_var_def]
    \\ every_case_tac \\ fs [get_vars_def,get_var_def]
    \\ fs [] \\ rveq \\ fs [lookup_inter_alt] \\ NO_TAC)
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac \\ fs [] \\ clean_tac
  \\ rename1 `get_vars [adjust_var a1; adjust_var a2] t = SOME [x1; x2]`
  \\ imp_res_tac get_vars_2_IMP
  \\ fs [wordSemTheory.get_vars_def]
  \\ rpt_drule lookup_Arith_location \\ fs [get_names_def]
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
  \\ fs [wordSemTheory.dec_clock_def]
  \\ fs [Arith_code_def]
  \\ drule lookup_RefByte_location \\ fs [get_names_def]
  \\ fs [wordSemTheory.evaluate_def,list_Seq_def,word_exp_rw,push_env_code,
         wordSemTheory.find_code_def,wordSemTheory.set_var_def]
  \\ fs [wordSemTheory.add_ret_loc_def,wordSemTheory.find_code_def]
  \\ fs [wordSemTheory.bad_dest_args_def,wordSemTheory.get_vars_def,fromList2_def,
         wordSemTheory.get_var_def,lookup_insert,
         wordSemTheory.call_env_def,push_env_code]
  \\ disch_then kall_tac
  \\ Q.MATCH_GOALSUB_ABBREV_TAC `evaluate (AnyArith_code c,t4)` \\ rveq
  \\ `state_rel c l1 l2 (s1 with clock := MustTerminate_limit(:'a)-1)
        (t with <| clock := MustTerminate_limit(:'a)-1; termdep := t.termdep - 1 |>)
          [] locs` by (fs [state_rel_def] \\ asm_exists_tac \\ fs [] \\ NO_TAC)

  \\ rpt_drule state_rel_call_env_push_env \\ fs []
  \\ `dataSem$get_vars [a1; a2] s.locals = SOME [Number i1; Number i2]` by
    (fs [dataSemTheory.get_vars_def] \\ every_case_tac \\ fs [cut_env_def]
     \\ clean_tac \\ fs [lookup_inter_alt,get_var_def] \\ NO_TAC)
  \\ `s1.locals = x` by (unabbrev_all_tac \\ fs []) \\ fs []
  \\ disch_then drule \\ fs []
  \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def]
  \\ `dataSem$cut_env x' s1.locals = SOME s1.locals` by
   (unabbrev_all_tac \\ fs []
    \\ fs [cut_env_def] \\ clean_tac
    \\ fs [domain_inter] \\ fs [lookup_inter_alt] \\ NO_TAC)
  \\ fs [] \\ rfs []
  \\ disch_then drule \\ fs []
  \\ disch_then (qspecl_then [`n`,`l`,`NONE`] mp_tac) \\ fs []
  \\ strip_tac
  \\ `index < 7` by (fs [int_op_def] \\ every_case_tac \\ fs [] \\ NO_TAC)
  \\ `index < dimword (:'a) DIV 16` by
        (fs [labPropsTheory.good_dimindex_def,dimword_def,state_rel_def] \\ NO_TAC)
  \\ rpt_drule state_rel_IMP_Number_arg
  \\ strip_tac
  \\ rpt_drule AnyArith_thm
  \\ simp [Once call_env_def,wordSemTheory.dec_clock_def,do_app_def,
           get_vars_def,get_var_def,lookup_insert,fromList_def,push_env_termdep,
           do_space_def,dataLangTheory.op_space_reset_def,fromList2_def,
           bviSemTheory.do_app_def,(*do_app,*)call_env_def,wordSemTheory.call_env_def]
  \\ disch_then (qspecl_then [`l2`,`l1`] strip_assume_tac)
  \\ qmatch_assum_abbrev_tac `evaluate (AnyArith_code c,t5) = _`
  \\ `t5 = t4` by
   (unabbrev_all_tac \\ fs [wordSemTheory.call_env_def,
       wordSemTheory.push_env_def,wordSemTheory.dec_clock_def]
    \\ pairarg_tac \\ fs [] \\ NO_TAC)
  \\ fs [] \\ Cases_on `q = SOME NotEnoughSpace` THEN1 fs [] \\ fs []
  \\ rpt_drule state_rel_pop_env_IMP
  \\ simp [push_env_def,call_env_def,pop_env_def,dataSemTheory.dec_clock_def]
  \\ strip_tac \\ fs [] \\ clean_tac
  \\ `domain t2.locals = domain y` by
   (qspecl_then [`AnyArith_code c`,`t4`] mp_tac
         (wordPropsTheory.evaluate_stack_swap
            |> INST_TYPE [``:'b``|->``:'c``,``:'c``|->``:'ffi``])
    \\ fs [] \\ fs [wordSemTheory.pop_env_def,wordSemTheory.dec_clock_def]
    \\ Cases_on `r''.stack` \\ fs [] \\ Cases_on `h` \\ fs []
    \\ rename1 `r2.stack = StackFrame ns opt::t'`
    \\ unabbrev_all_tac
    \\ fs [wordSemTheory.call_env_def,wordSemTheory.push_env_def]
    \\ pairarg_tac \\ Cases_on `opt`
    \\ fs [wordPropsTheory.s_key_eq_def,
          wordPropsTheory.s_frame_key_eq_def]
    \\ rw [] \\ drule env_to_list_lookup_equiv
    \\ fs [EXTENSION,domain_lookup,lookup_fromAList]
    \\ fs[GSYM IS_SOME_EXISTS]
    \\ imp_res_tac MAP_FST_EQ_IMP_IS_SOME_ALOOKUP \\ metis_tac [])
  \\ pop_assum mp_tac
  \\ pop_assum mp_tac
  \\ simp [state_rel_def]
  \\ fs [dataSemTheory.call_env_def,alist_insert_def,push_env_def,
         dataSemTheory.set_var_def,wordSemTheory.set_vars_def]
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
    \\ drule env_to_list_lookup_equiv
    \\ fs[contains_loc_def])
  \\ conj_tac THEN1 (fs [lookup_insert,adjust_var_11] \\ rw [])
  \\ asm_exists_tac \\ fs []
  \\ fs [inter_insert_ODD_adjust_set]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac word_ml_inv_insert \\ fs [flat_def]
  \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac word_ml_inv_rearrange)
  \\ fs[MEM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
QED

val _ = export_theory();
