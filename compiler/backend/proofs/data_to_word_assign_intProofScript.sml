(*
  Part of the correctness proof for data_to_word: assign for IntOp
*)
Theory data_to_word_assign_intProof
Libs
  preamble helperLib blastLib
Ancestors
  wordSem
  backend_common (* for word_add_carry *)
  data_to_word_memoryProof data_to_word_gcProof dataSem
  wordSem[qualified] data_to_word int_bitwise dataProps
  data_to_word_bignumProof wordProps While set_sep
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

Theorem inst_IDiv_Smallnum[local]:
  good_dimindex (:'a) /\ small_int (dimindex (:'a)) i /\
  small_int (dimindex (:'a)) j /\ j <> 0 /\
  wordSem$get_vars [ra;rb] (s:('a,'c,'ffi) wordSem$state) =
    SOME [Word (Smallnum i);Word (Smallnum j)] ==>
  wordSem$inst (Arith (IDiv rq rr ra rb)) s =
    SOME (wordSem$set_var rq (Word (i2w (i quot j)))
      (wordSem$set_var rr (Word (Smallnum (i rem j))) s))
Proof
  strip_tac
  \\ `w2i (Smallnum i : 'a word) = 2 * i` by simp [small_int_w2i_Smallnum]
  \\ `w2i (Smallnum j : 'a word) = 2 * j` by simp [small_int_w2i_Smallnum]
  \\ simp [wordSemTheory.inst_def, LET_THM, tagged_quot_rem, small_int_quot_w2i]
  \\ simp [Smallnum_i2w]
QED

Theorem evaluate_SmallDivMod[local]:
  good_dimindex (:'a) /\ small_int (dimindex (:'a)) i /\
  small_int (dimindex (:'a)) j /\ j <> 0 /\
  wordSem$get_var (adjust_var v1) (s:('a,'c,'ffi) wordSem$state) =
    SOME (Word (Smallnum i)) /\
  wordSem$get_var (adjust_var v2) s = SOME (Word (Smallnum j)) ==>
  let r = i rem j;
      t = wordSem$set_var 1 (Word (i2w (i quot j)))
            (wordSem$set_var 3 (Word (Smallnum r)) s);
      tx = wordSem$set_var 5 (Word ((Smallnum r : 'a word) ?? Smallnum j)) t
  in wordSem$evaluate (SmallDivMod is_mod v1 v2,s) =
    (NONE,if r = 0 then t
          else if (r < 0) <> (j < 0) then
            if is_mod then wordSem$set_var 3 (Word (Smallnum (i % j))) tx
            else wordSem$set_var 1 (Word (i2w (i / j))) tx
          else tx)
Proof
  strip_tac
  \\ `wordSem$get_vars [adjust_var v1;adjust_var v2] s =
      SOME [Word (Smallnum i);Word (Smallnum j)]` by
    simp [wordSemTheory.get_vars_def]
  \\ drule_all inst_IDiv_Smallnum
  \\ strip_tac
  \\ `small_int (dimindex (:'a)) (i rem j)` by metis_tac [small_int_rem]
  \\ `w2i (Smallnum (i rem j) : 'a word) = 2 * (i rem j)` by
    simp [small_int_w2i_Smallnum]
  \\ `((Smallnum (i rem j) : 'a word) = 0w) <=> (i rem j = 0)` by (
    PURE_REWRITE_TAC [GSYM integer_wordTheory.w2i_eq_0]
    \\ asm_rewrite_tac []
    \\ intLib.COOPER_TAC)
  \\ `adjust_var v2 <> 1 /\ adjust_var v2 <> 3 /\ adjust_var v2 <> 5` by (
    simp [adjust_var_def]
    \\ decide_tac)
  \\ simp [LET_THM, SmallDivMod_def, list_Seq_def, Once wordSemTheory.evaluate_def]
  \\ simp [``wordSem$evaluate (Inst ii,ss)``
           |> REWRITE_CONV [wordSemTheory.evaluate_def]]
  \\ simp [Once wordSemTheory.evaluate_def, wordSemTheory.get_var_imm_def,
           get_var_set_var, asmTheory.word_cmp_def, integer_wordTheory.i2w_0]
  \\ Cases_on `i rem j = 0`
  >- simp [Once wordSemTheory.evaluate_def]
  \\ simp []
  \\ simp [Once wordSemTheory.evaluate_def,
           ``wordSem$evaluate (Assign dst exp,ss)``
           |> REWRITE_CONV [wordSemTheory.evaluate_def]]
  \\ simp [Once wordSemTheory.word_exp_def,
           ``wordSem$word_exp ss (Var reg)``
           |> REWRITE_CONV [wordSemTheory.word_exp_def], get_var_set_var,
           wordSemTheory.the_words_def, wordSemTheory.word_op_def]
  \\ simp [Once wordSemTheory.evaluate_def, wordSemTheory.get_var_imm_def,
           get_var_set_var, integer_wordTheory.i2w_0,
           small_int_Smallnum_xor_sign, EQ_SYM_EQ]
  \\ reverse (Cases_on `(i rem j < 0) <> (j < 0)`)
  >- (
    fs [EQ_SYM_EQ]
    \\ simp [Once wordSemTheory.evaluate_def])
  \\ qpat_x_assum `(i rem j < 0) <> (j < 0)`
    (assume_tac o ONCE_REWRITE_RULE [EQ_SYM_EQ])
  \\ simp []
  \\ `i / j = i quot j - 1 /\ i % j = i rem j + j` by (
    mp_tac (Q.INST [`a` |-> `i`, `b` |-> `j`] signed_floor_divmod)
    \\ simp [LET_THM, EQ_SYM_EQ])
  \\ Cases_on `is_mod`
  \\ simp []
  \\ simp [Once wordSemTheory.evaluate_def, Once wordSemTheory.word_exp_def,
           ``wordSem$word_exp ss (Var reg)``
           |> REWRITE_CONV [wordSemTheory.word_exp_def],
           ``wordSem$word_exp ss (Const ww)``
           |> REWRITE_CONV [wordSemTheory.word_exp_def], get_var_set_var,
           wordSemTheory.the_words_def, wordSemTheory.word_op_def]
  \\ simp [Smallnum_i2w, integer_wordTheory.i2w_pos, integer_wordTheory.word_i2w_add,
           integerTheory.INT_LDISTRIB, integerTheory.INT_ADD_COMM]
  \\ PURE_REWRITE_TAC [GSYM integer_wordTheory.i2w_minus_1,
                       integer_wordTheory.word_i2w_add, integerTheory.int_sub]
  \\ REFL_TAC
QED

Theorem evaluate_SmallDivMod_results[local]:
  good_dimindex (:'a) /\ small_int (dimindex (:'a)) i /\
  small_int (dimindex (:'a)) j /\ j <> 0 /\
  wordSem$get_var (adjust_var v1) (s:('a,'c,'ffi) wordSem$state) =
    SOME (Word (Smallnum i)) /\
  wordSem$get_var (adjust_var v2) s = SOME (Word (Smallnum j)) ==>
  let r = i rem j;
      locals = if r = 0 then s.locals
               else insert 5 (Word ((Smallnum r : 'a word) ?? Smallnum j)) s.locals
  in wordSem$evaluate (SmallDivMod is_mod v1 v2,s) =
    (NONE,s with locals :=
      insert 1 (Word (i2w (if is_mod then i quot j else i / j)))
        (insert 3 (Word (Smallnum (if is_mod then i % j else i rem j))) locals))
Proof
  strip_tac
  \\ mp_tac (Q.INST [`a` |-> `i`, `b` |-> `j`] signed_floor_divmod)
  \\ simp [LET_THM]
  \\ strip_tac
  \\ mp_tac (SPEC_ALL evaluate_SmallDivMod)
  \\ asm_rewrite_tac []
  \\ simp [LET_THM]
  \\ strip_tac
  \\ asm_rewrite_tac []
  \\ Cases_on `i rem j = 0`
  \\ Cases_on `(i rem j < 0) <> (j < 0)`
  \\ Cases_on `is_mod`
  \\ simp [wordSemTheory.set_var_def, insert_shadow, insert_swap]
QED

Theorem evaluate_SmallnumDivLoop_step[local]:
  good_dimindex (:'a) /\ n < dimword (:'a) /\ d < dimword (:'a) /\
  2 * r + n DIV 2 ** (dimindex (:'a) - 1) < dimword (:'a) /\
  wordSem$get_var 1 (t:('a,'c,'ffi) wordSem$state) = SOME (Word (n2w q)) /\
  wordSem$get_var 3 t = SOME (Word (n2w r)) /\
  wordSem$get_var 5 t = SOME (Word (n2w n)) /\
  wordSem$get_var 7 t = SOME (Word (n2w d)) ==>
  let trial = 2 * r + n DIV 2 ** (dimindex (:'a) - 1) in
  wordSem$evaluate (SmallnumDivLoop (dimindex (:'a)) (SUC k),t) =
  wordSem$evaluate (SmallnumDivLoop (dimindex (:'a)) k,
    t with locals :=
      insert 1 (Word (n2w (2 * q + if trial < d then 0 else 1)))
        (insert 3 (Word (n2w (if trial < d then trial else trial - d)))
          (insert 5 (Word (n2w (2 * n))) t.locals)))
Proof
  strip_tac
  \\ `n DIV 2 ** (dimindex (:'a) - 1) < dimword (:'a)` by decide_tac
  \\ `((n2w n : 'a word) >>> (dimindex (:'a) - 1)) =
      n2w (n DIV 2 ** (dimindex (:'a) - 1))` by (
    once_rewrite_tac [GSYM w2n_11]
    \\ asm_simp_tac std_ss [w2n_lsr,w2n_n2w,LESS_MOD])
  \\ simp_tac std_ss [LET_THM]
  \\ once_rewrite_tac [SmallnumDivLoop_def]
  \\ fs [wordSemTheory.get_var_def]
  \\ simp [list_Seq_def,eq_eval]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
  \\ simp [eq_eval,WORD_MUL_LSL,word_mul_n2w,word_add_n2w,WORD_LO]
  \\ Cases_on `2 * r + n DIV 2 ** (dimindex (:'a) - 1) < d`
  \\ simp [insert_swap,insert_shadow,integer_wordTheory.i2w_pos,word_add_n2w]
  \\ `d <= 2 * r + n DIV 2 ** (dimindex (:'a) - 1)` by decide_tac
  \\ asm_simp_tac pure_ss
       [n2w_sub,word_sub_def,WORD_NEG_LMUL,WORD_MULT_CLAUSES,WORD_ADD_COMM]
  \\ pure_rewrite_tac [GSYM WORD_NEG_MUL]
  \\ REFL_TAC
QED

Theorem evaluate_SmallnumDivLoop[local]:
  !k q r n d (t:('a,'c,'ffi) wordSem$state).
    good_dimindex (:'a) /\ k <= dimindex (:'a) /\
    n < dimword (:'a) /\ 0 < d /\ d < dimword (:'a) /\ r < d /\
    r * 2 ** k + n DIV 2 ** (dimindex (:'a) - k) < dimword (:'a) /\
    wordSem$get_var 1 t = SOME (Word (n2w q)) /\
    wordSem$get_var 3 t = SOME (Word (n2w r)) /\
    wordSem$get_var 5 t = SOME (Word (n2w n)) /\
    wordSem$get_var 7 t = SOME (Word (n2w d)) ==>
    let total = r * 2 ** k + n DIV 2 ** (dimindex (:'a) - k) in
    ?locals.
      wordSem$evaluate (SmallnumDivLoop (dimindex (:'a)) k,t) =
        (NONE,t with locals := locals) /\
      lookup 1 locals = SOME (Word (n2w (q * 2 ** k + total DIV d))) /\
      lookup 3 locals = SOME (Word (n2w (total MOD d))) /\
      !reg. EVEN reg ==> lookup reg locals = lookup reg t.locals
Proof
  Induct \\ rpt gen_tac \\ strip_tac
  >- (
    simp_tac std_ss [LET_THM]
    \\ qexists_tac `t.locals`
    \\ fs [SmallnumDivLoop_def,Once wordSemTheory.evaluate_def,
           GSYM dimword_def,LESS_DIV_EQ_ZERO,LESS_MOD,wordSemTheory.get_var_def])
  \\ `dimword (:'a) = 2 * (2 ** (dimindex (:'a) - SUC k) * 2 ** k)` by (
    simp_tac pure_ss [dimword_def,GSYM EXP_ADD,GSYM (CONJUNCT2 EXP)]
    \\ AP_TERM_TAC \\ decide_tac)
  \\ `2 ** (dimindex (:'a) - 1) = 2 ** (dimindex (:'a) - SUC k) * 2 ** k` by (
    pure_rewrite_tac [GSYM EXP_ADD]
    \\ AP_TERM_TAC \\ decide_tac)
  \\ `2 ** (dimindex (:'a) - k) = 2 * 2 ** (dimindex (:'a) - SUC k)` by (
    pure_rewrite_tac [GSYM (CONJUNCT2 EXP)]
    \\ AP_TERM_TAC \\ decide_tac)
  \\ qspecl_then [`n`,`d`,`r`,`2 ** (dimindex (:'a) - SUC k)`,`2 ** k`]
       mp_tac smallnum_div_step
  \\ impl_tac >- fs [EXP]
  \\ qpat_x_assum `dimword (:'a) = _` (fn th => pure_rewrite_tac [GSYM th])
  \\ qpat_x_assum `2 ** (_ - 1) = _` (fn th => pure_rewrite_tac [GSYM th])
  \\ qpat_x_assum `2 ** _ = 2 * _` (fn th => pure_rewrite_tac [GSYM th])
  \\ simp_tac std_ss [LET_THM] \\ strip_tac
  \\ mp_tac (SPEC_ALL evaluate_SmallnumDivLoop_step)
  \\ asm_rewrite_tac [] \\ simp_tac std_ss [LET_THM] \\ disch_tac
  \\ qabbrev_tac `trial = 2 * r + n DIV 2 ** (dimindex (:'a) - 1)`
  \\ qabbrev_tac `shifted = 2 * n MOD dimword (:'a)`
  \\ qabbrev_tac `pending =
       trial MOD d * 2 ** k + shifted DIV 2 ** (dimindex (:'a) - k)`
  \\ qspecl_then [`trial`,`d`] mp_tac smallnum_div_digit
  \\ impl_tac >- simp []
  \\ disch_then (fn th =>
       pure_rewrite_tac [GSYM (CONJUNCT1 th),GSYM (CONJUNCT2 th)])
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,next_state)`
  \\ `k <= dimindex (:'a)` by decide_tac
  \\ qpat_x_assum `!q r n d t. _`
       (qspecl_then [`2 * q + trial DIV d`,`trial MOD d`,`shifted`,`d`,`next_state`]
         mp_tac)
  \\ impl_tac
  >- fs [Abbr `next_state`,Abbr `shifted`,Abbr `pending`,
         wordSemTheory.get_var_def,lookup_insert,n2w_mod]
  \\ simp_tac std_ss [LET_THM] \\ strip_tac
  \\ qmatch_asmsub_rename_tac `lookup 1 result_locals = _`
  \\ qexists_tac `result_locals`
  \\ qpat_x_assum `Abbrev (pending = _)` (fn th =>
       RULE_ASSUM_TAC (PURE_REWRITE_RULE
         [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]))
  \\ pure_rewrite_tac [EXP]
  \\ asm_simp_tac std_ss []
  \\ simp_tac std_ss
       [RIGHT_ADD_DISTRIB,AC MULT_ASSOC MULT_COMM,AC ADD_ASSOC ADD_COMM]
  \\ simp [Abbr `next_state`,lookup_insert]
  \\ rw [] \\ gvs []
QED

Theorem evaluate_SmallnumUnsignedDiv[local]:
  good_dimindex (:'a) /\ arch_width_bits c.arch_width = dimindex (:'a) /\
  n < dimword (:'a) DIV 2 /\ 0 < d /\ d < dimword (:'a) DIV 2 /\
  wordSem$get_var 5 (t:('a,'c,'ffi) wordSem$state) = SOME (Word (n2w n)) /\
  wordSem$get_var 7 t = SOME (Word (n2w d)) ==>
  ?locals.
    wordSem$evaluate (SmallnumUnsignedDiv c,t) = (NONE,t with locals := locals) /\
    lookup 1 locals = SOME (Word (n2w (n DIV d))) /\
    lookup 3 locals = SOME (Word (n2w (n MOD d))) /\
    !reg. EVEN reg ==> lookup reg locals = lookup reg t.locals
Proof
  strip_tac
  \\ `n < dimword (:'a) /\ d < dimword (:'a)` by (
    qsuff_tac `dimword (:'a) DIV 2 <= dimword (:'a)` >- decide_tac
    \\ simp [DIV_LESS_EQ])
  \\ `n DIV d < dimword (:'a)` by (
    qsuff_tac `n DIV d <= n` >- decide_tac
    \\ simp [DIV_LESS_EQ])
  \\ drule DIVISION \\ disch_then (qspec_then `n` strip_assume_tac)
  \\ Cases_on `c.has_div`
  >- (
    `d <> 0 /\ n DIV d * d < dimword (:'a) /\ n DIV d * d <= n /\
     n - n DIV d * d = n MOD d` by decide_tac
    \\ qpat_x_assum `n = _` kall_tac
    \\ `n < INT_MIN (:'a) /\ d < INT_MIN (:'a)` by
         fs [dimword_IS_TWICE_INT_MIN,MULT_DIV_2]
    \\ `~word_msb (n2w n : 'a word) /\ ~word_msb (n2w d : 'a word)` by
         simp [word_msb_n2w_numeric]
    \\ qexists_tac `insert 3 (Word (-1w * n2w (n DIV d * d) + n2w n))
         (insert 9 (Word 0w) (insert 1 (Word (n2w (n DIV d))) t.locals))`
    \\ fs [SmallnumUnsignedDiv_def,list_Seq_def,eq_eval,wordSemTheory.inst_def,
           wordsTheory.word_quot_def,word_div_def,n2w_11,LESS_DIV_EQ_ZERO,
           insert_swap,insert_shadow]
    \\ conj_tac
    >- (
      qspecl_then [`n`,`d * (n DIV d)`] mp_tac n2w_sub
      \\ asm_simp_tac pure_ss [word_sub_def,GSYM WORD_NEG_MUL]
      \\ simp_tac std_ss [EQ_SYM_EQ])
    \\ rw [] \\ gvs [])
  \\ Cases_on `c.has_longdiv`
  >- (
    `d <> 0` by decide_tac
    \\ qpat_x_assum `n = _` kall_tac
    \\ qexists_tac `insert 1 (Word (n2w (n DIV d)))
         (insert 3 (Word (n2w (n MOD d))) t.locals)`
    \\ fs [SmallnumUnsignedDiv_def,list_Seq_def,eq_eval,wordSemTheory.inst_def,
           n2w_11,insert_shadow,insert_swap]
    \\ simp [integer_wordTheory.i2w_pos]
    \\ rw [] \\ gvs [])
  \\ qpat_x_assum `n = _` kall_tac
  \\ qabbrev_tac `division_start =
       t with locals := insert 3 (Word 0w) (insert 1 (Word 0w) t.locals)`
  \\ qspecl_then [`dimindex (:'a)`,`0`,`0`,`n`,`d`,`division_start`]
       mp_tac evaluate_SmallnumDivLoop
  \\ impl_tac
  >- fs [Abbr `division_start`,wordSemTheory.get_var_def,lookup_insert]
  \\ simp_tac (srw_ss ()) [LET_THM]
  \\ disch_then (qx_choose_then `result_locals` strip_assume_tac)
  \\ qexists_tac `result_locals`
  \\ fs [SmallnumUnsignedDiv_def,list_Seq_def,eq_eval,Abbr `division_start`,
         integer_wordTheory.i2w_pos]
  \\ rw [] \\ gvs []
QED

val _ = augment_srw_ss [rewrites [integer_wordTheory.i2w_pos,
                                  integer_wordTheory.i2w_w2i, i2w_neg, i2w_sub1,
    data_to_word_memoryProofTheory.compiler_all_ones_i2w,
  data_to_wordTheory.get_lowerbits_def,data_to_wordTheory.make_ptr_def,
  data_to_wordTheory.make_cons_ptr_def]]

Theorem evaluate_Seq_NONE[local]:
  wordSem$evaluate (p,(t:('a,'c,'ffi) wordSem$state)) = (NONE,s) ==>
  !q. wordSem$evaluate (Seq p q,t) = wordSem$evaluate (q,s)
Proof
  strip_tac \\ gen_tac \\ simp [Once wordSemTheory.evaluate_def]
QED

Theorem evaluate_SmallnumAbs[local]:
  good_dimindex (:'a) /\ small_int (dimindex (:'a)) i /\
  wordSem$get_var in_reg (t:('a,'c,'ffi) wordSem$state) =
    SOME (Word (Smallnum i)) ==>
  wordSem$evaluate
    (If Less in_reg (Imm 0)
      (Assign out_reg (Op Sub [Const 0; ShiftVar (dimindex (:'a)) Asr in_reg 1]))
      (Assign out_reg (ShiftVar (dimindex (:'a)) Asr in_reg 1)),t) =
    (NONE,t with locals := insert out_reg (Word (n2w (Num (ABS i)))) t.locals)
Proof
  strip_tac \\ drule_all small_int_Smallnum_asr \\ strip_tac
  \\ fs [wordSemTheory.get_var_def]
  \\ simp [eq_eval,GSYM word_msb_neg,small_int_Smallnum_msb]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
  \\ simp []
  \\ pure_rewrite_tac [GSYM WORD_NEG_MUL]
  \\ Cases_on `i` \\ simp []
  \\ simp_tac pure_ss [GSYM WORD_NEG_MUL,WORD_NEG_NEG]
  \\ REFL_TAC
QED

Theorem evaluate_SmallnumDivMod[local]:
  good_dimindex (:'a) /\ arch_width_bits c.arch_width = dimindex (:'a) /\
  small_int (dimindex (:'a)) i /\ small_int (dimindex (:'a)) j /\ j <> 0 /\
  wordSem$get_var 2 (t:('a,'c,'ffi) wordSem$state) = SOME (Word (Smallnum i)) /\
  wordSem$get_var 4 t = SOME (Word (Smallnum j)) ==>
  ?locals.
    wordSem$evaluate (SmallnumDivMod c,t) = (NONE,t with locals := locals) /\
    lookup 1 locals = SOME (Word (Smallnum (i / j))) /\
    lookup 3 locals = SOME (Word (Smallnum (i % j))) /\
    !reg. EVEN reg ==> lookup reg locals = lookup reg t.locals
Proof
  strip_tac
  \\ `Num (ABS i) < dimword (:'a) DIV 2 /\
      Num (ABS j) < dimword (:'a) DIV 2 /\ 0 < Num (ABS j)` by (
    Cases_on `i` \\ Cases_on `j`
    \\ fs [good_dimindex_def,small_int_def,dimword_def]
    \\ rfs [] \\ decide_tac)
  \\ mp_tac (Q.INST [`in_reg` |-> `2`,`out_reg` |-> `5`]
       evaluate_SmallnumAbs)
  \\ asm_rewrite_tac [] \\ disch_tac
  \\ qabbrev_tac `division_abs_left =
       t with locals := insert 5 (Word (n2w (Num (ABS i)))) t.locals`
  \\ mp_tac (Q.INST [`i` |-> `j`,`in_reg` |-> `4`,
       `out_reg` |-> `7`,`t` |-> `division_abs_left`] evaluate_SmallnumAbs)
  \\ impl_tac
  >- fs [Abbr `division_abs_left`,wordSemTheory.get_var_def,lookup_insert]
  \\ disch_tac
  \\ qabbrev_tac `division_start = division_abs_left with locals :=
       insert 7 (Word (n2w (Num (ABS j)))) division_abs_left.locals`
  \\ mp_tac (Q.INST [`n` |-> `Num (ABS i)`,`d` |-> `Num (ABS j)`,
       `t` |-> `division_start`] evaluate_SmallnumUnsignedDiv)
  \\ impl_tac
  >- fs [Abbr `division_start`,Abbr `division_abs_left`,
         wordSemTheory.get_var_def,lookup_insert]
  \\ disch_then (qx_choose_then `unsigned_locals` strip_assume_tac)
  \\ qabbrev_tac `division_unsigned = division_start with locals := unsigned_locals`
  \\ `i quot j = (if (i < 0) <> (j < 0)
       then -&(Num (ABS i) DIV Num (ABS j))
       else &(Num (ABS i) DIV Num (ABS j)))` by (
    Cases_on `i` \\ Cases_on `j` \\ gvs [integerTheory.INT_QUOT_CALCULATE])
  \\ `i rem j = (if i < 0 then -&(Num (ABS i) MOD Num (ABS j))
       else &(Num (ABS i) MOD Num (ABS j)))` by (
    Cases_on `i` \\ Cases_on `j` \\ gvs [integerTheory.INT_REM_CALCULATE])
  \\ `wordSem$get_var 2 division_unsigned = SOME (Word (Smallnum i)) /\
      wordSem$get_var 4 division_unsigned = SOME (Word (Smallnum j))` by
       fs [Abbr `division_unsigned`,Abbr `division_start`,Abbr `division_abs_left`,
           wordSemTheory.get_var_def,lookup_insert]
  \\ qpat_assum `evaluate (If _ _ _ _ (Assign 5 _),_) = _`
       (assume_tac o MATCH_MP evaluate_Seq_NONE)
  \\ qpat_assum `evaluate (If _ _ _ _ (Assign 7 _),_) = _`
       (assume_tac o MATCH_MP evaluate_Seq_NONE)
  \\ qpat_assum `evaluate (SmallnumUnsignedDiv _,_) = _`
       (assume_tac o MATCH_MP evaluate_Seq_NONE)
  \\ asm_simp_tac std_ss [SmallnumDivMod_def,list_Seq_def]
  \\ once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ asm_simp_tac std_ss [LET_THM]
  \\ rpt (qpat_x_assum `!q. evaluate (Seq _ q,_) = _` kall_tac)
  \\ rpt (qpat_x_assum `evaluate (If _ _ _ _ _,_) = _` kall_tac)
  \\ qpat_x_assum `evaluate (SmallnumUnsignedDiv _,_) = _` kall_tac
  \\ fs [eq_eval,Abbr `division_unsigned`,GSYM word_msb_neg,small_int_Smallnum_msb]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
  \\ simp [eq_eval,GSYM word_msb_neg,small_int_Smallnum_msb]
  \\ `small_int (dimindex (:'a)) (i rem j)` by (
    irule small_int_rem \\ rpt conj_tac \\ first_assum ACCEPT_TAC)
  \\ `w2i (Smallnum (i rem j) : 'a word) = 2 * (i rem j)` by (
    qpat_x_assum `i rem j = _` kall_tac
    \\ simp [small_int_w2i_Smallnum])
  \\ `((Smallnum (i rem j) : 'a word) = 0w) <=> i rem j = 0` by (
    PURE_REWRITE_TAC [GSYM integer_wordTheory.w2i_eq_0]
    \\ asm_rewrite_tac [] \\ intLib.COOPER_TAC)
  \\ mp_tac (Q.INST [`i` |-> `i`,`j` |-> `j`] small_int_Smallnum_xor_sign)
  \\ impl_tac >- (rpt conj_tac \\ first_assum ACCEPT_TAC)
  \\ simp_tac std_ss [asmTheory.word_cmp_def,GSYM word_msb_neg] \\ disch_tac
  \\ mp_tac (Q.INST [`i` |-> `i rem j`,`j` |-> `j`] small_int_Smallnum_xor_sign)
  \\ impl_tac >- (rpt conj_tac \\ first_assum ACCEPT_TAC)
  \\ simp_tac std_ss [asmTheory.word_cmp_def,GSYM word_msb_neg] \\ disch_tac
  \\ mp_tac (Q.INST [`a` |-> `i`,`b` |-> `j`] signed_floor_divmod)
  \\ impl_tac >- asm_rewrite_tac []
  \\ simp_tac std_ss [LET_THM] \\ strip_tac
  \\ `!n. (n2w n : 'a word) << 1 = Smallnum (&n)` by
       simp [Smallnum_i2w,WORD_MUL_LSL,integerTheory.INT_MUL,
             integer_wordTheory.i2w_pos,word_mul_n2w]
  \\ sg `(if i < 0 then
       ((NONE : 'a wordSem$result option),division_start with locals :=
         insert 3 (Word (-1w * ((n2w (Num (ABS i) MOD Num (ABS j))) << 1)))
           (insert 3 (Word ((n2w (Num (ABS i) MOD Num (ABS j))) << 1))
             unsigned_locals))
       else (NONE,division_start with locals :=
         insert 3 (Word ((n2w (Num (ABS i) MOD Num (ABS j))) << 1))
           unsigned_locals)) =
       (NONE,division_start with locals :=
         insert 3 (Word (Smallnum (i rem j))) unsigned_locals)`
  >- (
    Cases_on `i < 0`
    \\ asm_simp_tac std_ss [insert_shadow,Smallnum_i2w,WORD_MUL_LSL,
         integerTheory.INT_MUL,integerTheory.INT_MUL_RNEG,i2w_neg,
         integer_wordTheory.i2w_pos,word_mul_n2w]
    \\ pure_rewrite_tac [GSYM WORD_NEG_MUL,GSYM WORD_NEG_RMUL]
    \\ simp_tac std_ss [word_mul_n2w])
  \\ qpat_x_assum `(if i < 0 then _ else _) = _`
       (PURE_REWRITE_TAC o single)
  \\ qpat_x_assum `i rem j = _` kall_tac
  \\ simp [eq_eval,GSYM word_msb_neg]
  \\ `word_msb (Smallnum j ?? Smallnum (i rem j) : 'a word) <=>
       ((i rem j < 0) <> (j < 0))` by (
    once_rewrite_tac [WORD_XOR_COMM] \\ first_assum ACCEPT_TAC)
  \\ Cases_on `(i < 0) <> (j < 0)`
  \\ simp [eq_eval,GSYM word_msb_neg]
  >- (
    Cases_on `i rem j = 0` \\ simp [eq_eval]
    >- (
      simp [eq_eval,Abbr `division_start`,Abbr `division_abs_left`]
      \\ rw [] \\ gvs []
      \\ simp_tac std_ss [Smallnum_i2w,WORD_MUL_LSL,
           integerTheory.INT_MUL_RNEG,integerTheory.INT_MUL,i2w_neg,
           integer_wordTheory.i2w_pos,word_mul_n2w]
      \\ pure_rewrite_tac [GSYM WORD_NEG_MUL,GSYM WORD_NEG_RMUL]
      \\ simp_tac std_ss [word_mul_n2w])
    \\ Cases_on `(i rem j < 0) <> (j < 0)`
    \\ simp [eq_eval,Abbr `division_start`,Abbr `division_abs_left`]
    \\ rw [] \\ gvs []
    >- (
      simp_tac std_ss [Smallnum_i2w,WORD_MUL_LSL,
           integerTheory.INT_SUB_LDISTRIB,integerTheory.INT_MUL_RNEG,
           integerTheory.INT_MUL,GSYM word_i2w_sub,i2w_neg,
           integer_wordTheory.i2w_pos,word_sub_def]
      \\ pure_rewrite_tac [GSYM WORD_NEG_MUL,GSYM WORD_NEG_RMUL]
      \\ simp_tac std_ss [word_mul_n2w,WORD_ADD_COMM])
    >- simp_tac std_ss [Smallnum_i2w,integerTheory.INT_LDISTRIB,
         integer_wordTheory.word_i2w_add,integerTheory.INT_ADD_COMM]
    \\ simp_tac std_ss [Smallnum_i2w,WORD_MUL_LSL,
         integerTheory.INT_MUL_RNEG,integerTheory.INT_MUL,i2w_neg,
         integer_wordTheory.i2w_pos,word_mul_n2w]
    \\ pure_rewrite_tac [GSYM WORD_NEG_MUL,GSYM WORD_NEG_RMUL]
    \\ simp_tac std_ss [word_mul_n2w])
  \\ Cases_on `i rem j = 0`
  \\ Cases_on `(i rem j < 0) <> (j < 0)`
  \\ simp [eq_eval,Abbr `division_start`,Abbr `division_abs_left`]
  \\ rw [] \\ gvs []
  >- (
    simp_tac std_ss [Smallnum_i2w,WORD_MUL_LSL,
         integerTheory.INT_SUB_LDISTRIB,integerTheory.INT_MUL,
         GSYM word_i2w_sub,integer_wordTheory.i2w_pos,word_sub_def]
    \\ pure_rewrite_tac [GSYM WORD_NEG_MUL,GSYM WORD_NEG_RMUL]
    \\ simp_tac std_ss [word_mul_n2w])
  \\ simp_tac std_ss [Smallnum_i2w,integerTheory.INT_LDISTRIB,
       integer_wordTheory.word_i2w_add,integerTheory.INT_ADD_COMM]
QED

Theorem evaluate_SmallnumDivMod_code[local]:
  good_dimindex (:'a) /\ arch_width_bits c.arch_width = dimindex (:'a) /\
  ~c.has_idiv /\ small_int (dimindex (:'a)) i /\
  small_int (dimindex (:'a)) j /\ j <> 0 /\
  wordSem$get_var 0 (t:('a,'c,'ffi) wordSem$state) = SOME (Loc secn l) /\
  wordSem$get_var 2 t = SOME (Word (Smallnum i)) /\
  wordSem$get_var 4 t = SOME (Word (Smallnum j)) ==>
  wordSem$evaluate (SmallnumDivMod_code c,t) =
    (SOME (Result (Loc secn l) [Word (Smallnum (i / j)); Word (Smallnum (i % j))]),
     t with <| locals := LN; locals_size := SOME 0 |>)
Proof
  strip_tac
  \\ drule_all evaluate_SmallnumDivMod
  \\ disch_then (qx_choose_then `division_locals` strip_assume_tac)
  \\ qpat_assum `evaluate (SmallnumDivMod _,_) = _`
       (assume_tac o MATCH_MP evaluate_Seq_NONE)
  \\ simp [SmallnumDivMod_code_def]
  \\ fs [eq_eval,wordSemTheory.get_vars_def,wordSemTheory.flush_state_def]
QED

Theorem evaluate_SmallnumDivCall[local]:
  good_dimindex (:'a) /\ arch_width_bits c.arch_width = dimindex (:'a) /\
  ~c.has_idiv /\ t.termdep <> 0 /\
  small_int (dimindex (:'a)) i /\ small_int (dimindex (:'a)) j /\ j <> 0 /\
  wordSem$get_vars [adjust_var v1;adjust_var v2]
    (t:('a,'c,'ffi) wordSem$state) =
      SOME [Word (Smallnum i);Word (Smallnum j)] /\
  lookup SmallnumDivMod_location t.code = SOME (3,SmallnumDivMod_code c,md) /\
  cut_envs (adjust_sets names) t.locals = SOME (env1,env2) /\
  env_to_list env2 t.permute = (saved_locals,next_permute) ==>
  let saved_stack = StackFrame t.locals_size (toAList env1) saved_locals NONE::t.stack;
      restored = t with <|
        locals := union (fromAList saved_locals) (fromAList (toAList env1));
        permute := next_permute;
        stack_max := OPTION_MAP2 MAX
          (OPTION_MAP2 MAX t.stack_max (stack_size saved_stack))
          (OPTION_MAP2 $+ (stack_size saved_stack)
            (lookup SmallnumDivMod_location t.stack_size)) |>;
      results = [Word (Smallnum (i / j));Word (Smallnum (i % j))]
  in
    wordSem$evaluate (SmallnumDivCall is_mod secn l dest (SOME names) v1 v2,t) =
      (NONE,wordSem$set_var (adjust_var dest)
        (Word (Smallnum (if is_mod then i % j else i / j)))
        (wordSem$set_vars [1;3] results restored))
Proof
  strip_tac
  \\ simp [LET_THM,SmallnumDivCall_def,list_Seq_def,eq_eval,get_names_def,
       domain_adjust_sets,wordSemTheory.push_env_def]
  \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def,AllCaseEqs()]
  \\ simp [wordSemTheory.MustTerminate_limit_def]
  \\ qmatch_goalsub_abbrev_tac
       `evaluate (SmallnumDivMod_code c,division_call)`
  \\ mp_tac (Q.INST [`t` |-> `division_call`] evaluate_SmallnumDivMod_code)
  \\ impl_tac
  >- simp [Abbr `division_call`,wordSemTheory.get_var_def,lookup_insert]
  \\ disch_tac
  \\ simp [Abbr `division_call`,wordSemTheory.pop_env_def]
  \\ drule env_to_list_lookup_equiv \\ strip_tac
  \\ `domain (fromAList saved_locals) = domain env2` by
       simp [EXTENSION,domain_lookup,lookup_fromAList]
  \\ simp [domain_union,domain_fromAList_toAList,UNION_COMM,
       wordSemTheory.set_vars_def,alist_insert_def]
  \\ Cases_on `is_mod`
  \\ simp [lookup_insert,alist_insert_def,wordSemTheory.state_component_equality]
QED

Theorem evaluate_SmallnumDiv[local]:
  c.has_idiv /\
  good_dimindex (:'a) /\ arch_width_bits c.arch_width = dimindex (:'a) /\
  small_int (dimindex (:'a)) i /\ small_int (dimindex (:'a)) j /\ j <> 0 /\
  wordSem$get_var (adjust_var v1) (t:('a,'c,'ffi) wordSem$state) =
    SOME (Word (Smallnum i)) /\
  wordSem$get_var (adjust_var v2) t = SOME (Word (Smallnum j)) ==>
  ?locals.
    wordSem$evaluate (SmallnumDiv c is_mod secn l dest names v1 v2,t) =
      (NONE,t with locals := locals) /\
    lookup (adjust_var dest) locals =
      SOME (Word (Smallnum (if is_mod then i % j else i / j))) /\
    !reg. EVEN reg /\ reg <> adjust_var dest ==>
      lookup reg locals = lookup reg t.locals
Proof
  strip_tac
  \\ mp_tac (Q.INST [`s` |-> `t`] evaluate_SmallDivMod_results)
  \\ asm_rewrite_tac [] \\ simp_tac std_ss [LET_THM] \\ disch_tac
  \\ qmatch_asmsub_abbrev_tac
       `evaluate (SmallDivMod is_mod v1 v2,t) = (NONE,division_native)`
  \\ `(i2w (i / j) : 'a word) << 1 = Smallnum (i / j)` by (
    PURE_REWRITE_TAC [Smallnum_i2w,WORD_MUL_LSL]
    \\ CONV_TAC numLib.REDUCE_CONV
    \\ once_rewrite_tac [GSYM integer_wordTheory.i2w_pos]
    \\ PURE_REWRITE_TAC [integer_wordTheory.word_i2w_mul]
    \\ REFL_TAC)
  \\ qexists_tac `insert (adjust_var dest)
       (Word (Smallnum (if is_mod then i % j else i / j))) division_native.locals`
  \\ Cases_on `is_mod`
  \\ simp [SmallnumDiv_def,eq_eval]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
  \\ fs [Abbr `division_native`,lookup_insert]
  \\ rw [lookup_insert] \\ gvs []
  \\ rw [] \\ gvs []
QED

Theorem evaluate_SmallnumMul[local]:
  good_dimindex (:'a) /\ arch_width_bits c.arch_width = dimindex (:'a) /\
  small_int (dimindex (:'a)) i /\ small_int (dimindex (:'a)) j /\
  wordSem$get_var (adjust_var v1) (t:('a,'c,'ffi) wordSem$state) =
    SOME (Word (Smallnum i)) /\
  wordSem$get_var (adjust_var v2) t = SOME (Word (Smallnum j)) ==>
  ?locals.
    wordSem$evaluate (SmallnumMul c dest v1 v2,t) =
      (NONE,t with locals := locals) /\
    lookup (adjust_var dest) locals = SOME (Word (Smallnum (i * j))) /\
    !reg. EVEN reg /\ reg <> adjust_var dest ==>
      lookup reg locals = lookup reg t.locals
Proof
  strip_tac
  \\ mp_tac (Q.INST [`i` |-> `i`,`j` |-> `j`] small_int_Smallnum_imul)
  \\ impl_tac >- (rpt conj_tac \\ first_assum ACCEPT_TAC)
  \\ strip_tac
  \\ fs [wordSemTheory.get_var_def]
  \\ Cases_on `c.has_imul`
  \\ simp [SmallnumMul_def,list_Seq_def,eq_eval]
  \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
  \\ simp [eq_eval,wordSemTheory.inst_def]
  \\ simp [GSYM word_mul_n2w,WORD_MULT_COMM]
  \\ rw [] \\ gvs []
QED

Theorem evaluate_assign_Smallnum[local]:
  ((smallop = SmallDiv \/ smallop = SmallMod) ==> c.has_idiv) /\
  good_dimindex (:'a) /\ arch_width_bits c.arch_width = dimindex (:'a) /\
  small_int (dimindex (:'a)) i /\ small_int (dimindex (:'a)) j /\
  smallnum_app smallop i j = SOME result /\
  wordSem$get_var (adjust_var v1) (t:('a,'c,'ffi) wordSem$state) =
    SOME (Word (Smallnum i)) /\
  wordSem$get_var (adjust_var v2) t = SOME (Word (Smallnum j)) ==>
  ?locals.
    wordSem$evaluate (FST (assign_Smallnum c secn smallop l dest names v1 v2),t) =
      (NONE,t with locals := locals) /\
    lookup (adjust_var dest) locals = SOME (Word
      (case result of INL n => Smallnum n | INR b => if b then 2w else 0w)) /\
    !reg. EVEN reg /\ reg <> adjust_var dest ==>
      lookup reg locals = lookup reg t.locals
Proof
  strip_tac
  \\ `(2 * i < 2 * j <=> i < j) /\
       (2 * j < 2 * i <=> j < i) /\ (2 * i = 2 * j <=> i = j)` by intLib.COOPER_TAC
  \\ Cases_on `smallop`
  \\ gvs [backendPropsTheory.smallnum_app_def,assign_Smallnum_def,AllCaseEqs()]
  >~ [`evaluate (SmallnumMul _ _ _ _,_)`]
  >- (
    irule evaluate_SmallnumMul \\ simp [])
  >~ [`evaluate (SmallnumDiv _ F _ _ _ _ _ _,_)`]
  >- (
    irule (evaluate_SmallnumDiv |> Q.INST [`is_mod` |-> `F`] |> SIMP_RULE std_ss [])
    \\ simp [])
  >~ [`evaluate (SmallnumDiv _ T _ _ _ _ _ _,_)`]
  >- (
    irule (evaluate_SmallnumDiv |> Q.INST [`is_mod` |-> `T`] |> SIMP_RULE std_ss [])
    \\ simp [])
  \\ fs [wordSemTheory.get_var_def]
  \\ simp [SmallnumCompare_def,eq_eval]
  >~ [`Smallnum _ + Smallnum _ = Smallnum _`]
  >- (
    simp [Smallnum_i2w,integer_wordTheory.word_i2w_add,integerTheory.INT_LDISTRIB])
  >~ [`Smallnum _ + -1w * Smallnum _ = Smallnum _`]
  >- (
    simp [Smallnum_i2w,integer_wordTheory.MULT_MINUS_ONE,
          integer_wordTheory.word_i2w_add,integerTheory.int_sub,
          integerTheory.INT_SUB_LDISTRIB,integerTheory.INT_LDISTRIB,
          integerTheory.INT_MUL_RNEG])
  \\ `w2i (Smallnum i : 'a word) = 2 * i /\
       w2i (Smallnum j : 'a word) = 2 * j` by simp [small_int_w2i_Smallnum]
  \\ once_rewrite_tac [GSYM integer_wordTheory.w2i_11]
  \\ simp [integer_wordTheory.WORD_LTi,small_int_w2i_Smallnum]
  \\ simp [integerTheory.INT_NOT_LT,integerTheory.int_ge,integerTheory.int_gt]
  \\ IF_CASES_TAC \\ simp []
  \\ rw [lookup_insert]
  \\ qpat_x_assum `Smallnum i = Smallnum j`
       (mp_tac o AP_TERM ``w2i : 'a word -> int``)
  \\ asm_rewrite_tac [] \\ intLib.COOPER_TAC
QED

val _ = numLib.prefer_num ();

fun drule0 th =
  first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))

val _ = hide "next";
val _ = hide "el";
val shift_def = backend_commonTheory.word_shift_def
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

val _ = augment_srw_ss [rewrites [arch_bytes_word]];
val eval_tac = imp_res_tac state_rel_arch_width
  \\ imp_res_tac memory_rel_arch_width \\ eval_tac
  \\ fs [GSYM word_mul_n2w];

Theorem SmallnumDivCall_state_rel[local]:
  state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) NONE locs /\
  ~c.has_idiv /\ t.termdep <> 0 /\
  small_int (dimindex (:'a)) i /\ small_int (dimindex (:'a)) j /\ j <> 0 /\
  small_int (dimindex (:'a)) (if is_mod then i % j else i / j) /\
  wordSem$get_vars [adjust_var v1;adjust_var v2] t =
    SOME [Word (Smallnum i);Word (Smallnum j)] /\
  dataSem$cut_env names s.locals = SOME retained_locals /\
  stack_consumed s.stack_frame_sizes s.limits op vs =
    lookup SmallnumDivMod_location s.stack_frame_sizes ==>
  ?r.
    wordSem$evaluate (SmallnumDivCall is_mod secn l dest (SOME names) v1 v2,t) =
      (NONE,r) /\
    state_rel c l1 l2
      (dataSem$set_var dest (Number (if is_mod then i % j else i / j))
        (do_stack op vs (s with locals := retained_locals))) r NONE locs
Proof
  strip_tac
  \\ drule state_rel_arch_width \\ disch_tac
  \\ drule_all data_to_word_gcProofTheory.cut_env_IMP_cut_env
  \\ disch_then (qx_choose_then `saved_word_locals` assume_tac)
  \\ drule_all state_rel_cut_env_cut_env \\ disch_tac
  \\ drule cut_env_IMP_cut_envs
  \\ disch_then (qx_choosel_then [`saved_fixed`,`saved_live`] strip_assume_tac)
  \\ `?stub_metadata. lookup SmallnumDivMod_location t.code =
       SOME (3,SmallnumDivMod_code c,stub_metadata)` by
       fs [state_rel_thm,code_rel_def,stubs_md_def,stubs_def,MAP_MAP_o,o_DEF]
  \\ namedCases_on `env_to_list saved_live t.permute` ["saved_list next_permute"]
  \\ `good_dimindex (:'a)` by fs [state_rel_thm]
  \\ drule_all evaluate_SmallnumDivCall
  \\ disch_then (qspecl_then [`secn`,`l`,`is_mod`,`dest`] assume_tac)
  \\ fs [LET_THM]
  \\ `wf saved_fixed /\ wf saved_live` by
       gvs [wordSemTheory.cut_envs_def,wordSemTheory.cut_names_def,
            AllCaseEqs(),wf_inter]
  \\ drule env_to_list_lookup_equiv \\ strip_tac
  \\ `fromAList saved_list = saved_live` by
       simp [spt_eq_thm,wf_fromAList,lookup_fromAList]
  \\ qpat_assum `state_rel c l1 l2 (s with locals := _) _ NONE locs`
       (assume_tac o REWRITE_RULE [state_rel_thm])
  \\ fs [state_rel_thm,dataSemTheory.set_var_def,dataSemTheory.do_stack_def,
       wordSemTheory.set_var_def,wordSemTheory.set_vars_def,alist_insert_def,
       fromAList_toAList,lookup_insert,stack_size_eq]
  \\ conj_tac
  >- (
    qx_gen_tac `local_index` \\ Cases_on `local_index = dest`
    \\ simp [adjust_var_11])
  \\ conj_tac >- simp [option_le_max_right,option_add_comm]
  \\ `stack_size t.stack = size_of_stack s.stack` by (
    irule stack_rel_IMP_size_of_stack \\ first_assum (irule_at Any))
  \\ conj_tac
  >- (
    simp [option_le_max,option_le_max_right,option_add_comm,option_le_add]
    \\ disj2_tac
    \\ irule (ONCE_REWRITE_RULE [option_add_comm] option_le_add))
  \\ simp [inter_insert_ODD_adjust_set]
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
  \\ irule memory_rel_insert \\ rewrite_tac [APPEND]
  \\ irule IMP_memory_rel_Number
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
QED

Theorem SmallnumDiv_state_rel[local]:
  state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) NONE locs /\
  t.termdep <> 0 /\
  small_int (dimindex (:'a)) i /\ small_int (dimindex (:'a)) j /\ j <> 0 /\
  k = (if is_mod then i % j else i / j) /\ small_int (dimindex (:'a)) k /\
  wordSem$get_vars [adjust_var v1;adjust_var v2] t =
    SOME [Word (Smallnum i);Word (Smallnum j)] /\
  dataSem$cut_env names s.locals = SOME retained_locals /\
  stack_consumed s.stack_frame_sizes s.limits op vs =
    lookup SmallnumDivMod_location s.stack_frame_sizes ==>
  ?r.
    wordSem$evaluate (SmallnumDiv c is_mod secn l dest (SOME names) v1 v2,t) =
      (NONE,r) /\
    state_rel c l1 l2
      (dataSem$set_var dest (Number k)
        (do_stack op vs (s with locals := retained_locals))) r NONE locs
Proof
  strip_tac \\ rveq
  \\ Cases_on `c.has_idiv`
  >- (
    drule state_rel_arch_width \\ disch_tac
    \\ drule_all state_rel_cut_env \\ disch_tac
    \\ `good_dimindex (:'a)` by fs [state_rel_thm]
    \\ qmatch_asmsub_rename_tac `cut_env kept_names s.locals = SOME retained_locals`
    \\ mp_tac (Q.INST [`names` |-> `SOME kept_names`] evaluate_SmallnumDiv)
    \\ impl_tac
    >- fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def,AllCaseEqs()]
    \\ disch_then (qx_choose_then `result_locals` strip_assume_tac)
    \\ `inter result_locals
          (adjust_set (insert dest (Number (if is_mod then i % j else i / j))
            retained_locals)) =
         inter (insert (adjust_var dest)
           (Word (Smallnum (if is_mod then i % j else i / j))) t.locals)
          (adjust_set (insert dest (Number (if is_mod then i % j else i / j))
            retained_locals))` by (
      simp [wf_inter,spt_eq_thm,lookup_inter_alt]
      \\ rw [lookup_insert]
      \\ imp_res_tac domain_adjust_set_EVEN \\ fs [])
    \\ qpat_assum `state_rel c l1 l2 (s with locals := _) t NONE locs`
         (assume_tac o REWRITE_RULE [state_rel_thm])
    \\ simp [state_rel_thm,dataSemTheory.set_var_def,dataSemTheory.do_stack_def,
         lookup_insert,option_le_max_right]
    \\ fs []
    \\ conj_tac
    >- (
      qx_gen_tac `local_index` \\ Cases_on `local_index = dest`
      \\ asm_simp_tac std_ss [EVEN_adjust_var,adjust_var_11,IS_SOME_DEF])
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ irule memory_rel_insert \\ rewrite_tac [APPEND]
    \\ irule IMP_memory_rel_Number
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND])
  \\ simp [SmallnumDiv_def]
  \\ irule SmallnumDivCall_state_rel \\ simp []
QED

Theorem assign_Smallnum:
  (? smallop. op = IntOp (Smallnum smallop)) ==> ^assign_thm_goal
Proof
  disch_then (qx_choose_then `smallop` assume_tac)
  \\ rpt strip_tac
  \\ Cases_on `smallop = SmallDiv \/ smallop = SmallMod`
  >- (
    `?is_mod. smallop = if is_mod then SmallMod else SmallDiv` by (
      Cases_on `smallop = SmallMod`
      >- (qexists_tac `T` \\ simp [])
      \\ qexists_tac `F` \\ fs [])
    \\ qpat_x_assum `smallop = SmallDiv \/ smallop = SmallMod` kall_tac
    \\ qpat_x_assum `smallop = if _ then _ else _` SUBST_ALL_TAC
    \\ `?retained_names. names_opt = SOME retained_names` by (
      Cases_on `is_mod`
      \\ gvs [dataLangTheory.op_requires_names_def,
           GSYM IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS])
    \\ qpat_x_assum `names_opt = SOME _` SUBST_ALL_TAC
    \\ `?retained_locals.
         dataSem$cut_env retained_names s.locals = SOME retained_locals /\
         x = s with locals := retained_locals` by
         gvs [dataSemTheory.cut_state_opt_def,dataSemTheory.cut_state_def,AllCaseEqs()]
    \\ qpat_x_assum `x = s with locals := _` SUBST_ALL_TAC
    \\ qpat_x_assum `op = IntOp _` SUBST_ALL_TAC
    \\ drule state_rel_arch_width \\ disch_tac
    \\ `!left right.
         smallnum_app (if is_mod then SmallMod else SmallDiv) left right =
         if right = 0 then NONE
         else SOME (INL (if is_mod then left % right else left / right))` by (
      Cases_on `is_mod` \\ simp [backendPropsTheory.smallnum_app_def])
    \\ qpat_x_assum `!left right. smallnum_app _ left right = _` (fn th =>
         gvs [th,dataSemTheory.do_app_def,dataSemTheory.do_space_def,
           data_spaceTheory.op_space_req_def,dataLangTheory.op_space_reset_def,
           dataSemTheory.do_app_aux_def,oneline do_int_app_def,
           backendPropsTheory.bounded_smallnum_app_def,AllCaseEqs()])
    \\ qmatch_asmsub_rename_tac
         `get_vars args s.locals = SOME (Number left::Number right::_)`
    \\ drule_all state_rel_get_vars_IMP
    \\ disch_then (qx_choose_then `word_args` strip_assume_tac)
    \\ qpat_assum `state_rel c l1 l2 s t NONE locs`
         (assume_tac o REWRITE_RULE [state_rel_thm])
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ full_simp_tac std_ss [APPEND]
    \\ drule_all memory_rel_get_vars_IMP \\ strip_tac
    \\ imp_res_tac get_vars_IMP_LENGTH
    \\ fs [LENGTH_EQ_2,LENGTH_EQ_3]
    \\ gvs []
    \\ qmatch_asmsub_rename_tac
         `memory_rel _ _ _ _ _ _ _ _ ((Number left,left_word)::
            (Number right,right_word)::_)`
    \\ qpat_assum `memory_rel _ _ _ _ _ _ _ _ ((Number left,_)::_)`
         (assume_tac o MATCH_MP memory_rel_tail)
    \\ qpat_assum `memory_rel _ _ _ _ _ _ _ _ ((Number right,_)::_)`
         (assume_tac o MATCH_MP memory_rel_tail)
    \\ qmatch_goalsub_abbrev_tac `set_var dest (Number arith_result) _`
    \\ `small_int (dimindex (:'a)) left /\ small_int (dimindex (:'a)) right /\
         small_int (dimindex (:'a)) arith_result` by (
      fs [Abbr `arith_result`]
      \\ metis_tac [index_in_bounds_NONE_small_int,
                    memory_rel_index_in_bounds_small_int])
    \\ `left_word = Word (Smallnum left) /\ right_word = Word (Smallnum right)` by
         metis_tac [memory_rel_Number_IMP]
    \\ gvs [get_vars_SOME_IFF,get_vars_SOME_IFF_data,Abbr `arith_result`]
    \\ simp [data_to_wordTheory.assign_def,assign_Smallnum_def]
    \\ qexists_tac `NONE` \\ simp []
    \\ irule SmallnumDiv_state_rel
    \\ simp [PULL_EXISTS] \\ qexistsl_tac [`left`, `right`]
    \\ simp [stack_consumed_def,allowed_op_def,wordSemTheory.get_vars_def,
         wordSemTheory.get_var_def])
  \\ gvs [dataLangTheory.op_requires_names_def,dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule state_rel_arch_width \\ strip_tac
  \\ gvs [do_app,oneline do_int_app_def,AllCaseEqs()]
  \\ qmatch_asmsub_rename_tac
       `bounded_smallnum_app _ smallop left right = SOME _`
  \\ drule_all state_rel_get_vars_IMP
  \\ disch_then (qx_choose_then `word_args` strip_assume_tac)
  \\ qpat_assum `state_rel c l1 l2 s t NONE locs`
       (assume_tac o REWRITE_RULE [state_rel_thm])
  \\ fs [allowed_op_def]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule_all memory_rel_get_vars_IMP \\ strip_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ fs [LENGTH_EQ_2,LENGTH_EQ_3]
  \\ gvs []
  \\ qmatch_asmsub_rename_tac
       `memory_rel _ _ _ _ _ _ _ _ ((Number left,left_word)::
          (Number right,right_word)::_)`
  \\ qpat_assum `memory_rel _ _ _ _ _ _ _ _ ((Number left,_)::_)`
       (assume_tac o MATCH_MP memory_rel_tail)
  \\ qpat_assum `memory_rel _ _ _ _ _ _ _ _ ((Number right,_)::_)`
       (assume_tac o MATCH_MP memory_rel_tail)
  \\ gvs [backendPropsTheory.bounded_smallnum_app_def,AllCaseEqs()]
  \\ `small_int (dimindex (:'a)) left /\ small_int (dimindex (:'a)) right` by
       metis_tac [index_in_bounds_NONE_small_int,memory_rel_index_in_bounds_small_int]
  \\ `left_word = Word (Smallnum left) /\ right_word = Word (Smallnum right)` by
       metis_tac [memory_rel_Number_IMP]
  \\ gvs [get_vars_SOME_IFF,get_vars_SOME_IFF_data]
  \\ qmatch_goalsub_rename_tac
       `assign c n l dest _ (first_arg::second_arg::_) NONE`
  \\ qmatch_asmsub_abbrev_tac `smallnum_app smallop left right = SOME small_result`
  \\ mp_tac (Q.INST [`i` |-> `left`,`j` |-> `right`,`result` |-> `small_result`,
       `v1` |-> `first_arg`,`v2` |-> `second_arg`,
       `secn` |-> `n`,`names` |-> `NONE`] evaluate_assign_Smallnum)
  \\ (impl_tac >- simp [wordSemTheory.get_var_def])
  \\ disch_then (qx_choose_then `result_locals` strip_assume_tac)
  \\ fs [data_to_wordTheory.assign_def,Abbr `small_result`]
  \\ qmatch_goalsub_abbrev_tac `set_var dest result_value _`
  \\ qmatch_asmsub_abbrev_tac
       `lookup (adjust_var dest) result_locals = SOME result_word`
  \\ `inter result_locals (adjust_set (insert dest result_value s.locals)) =
       inter (insert (adjust_var dest) result_word t.locals)
         (adjust_set (insert dest result_value s.locals))` by (
    simp [wf_inter,spt_eq_thm,lookup_inter_alt]
    \\ rw [lookup_insert]
    \\ imp_res_tac domain_adjust_set_EVEN \\ fs [])
  \\ simp [Once state_rel_thm,dataSemTheory.set_var_def,lookup_insert,
           option_le_max_right]
  \\ (conj_tac >- (
    qx_gen_tac `local_index` \\ Cases_on `local_index = dest`
    \\ asm_simp_tac std_ss [EVEN_adjust_var,adjust_var_11,IS_SOME_DEF]))
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ irule memory_rel_insert
  \\ simp [Abbr `result_value`,Abbr `result_word`]
  >- (
    irule IMP_memory_rel_Number \\ simp []
    \\ asm_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ irule index_in_bounds_NONE_small_int \\ simp [])
  >- (
    irule memory_rel_Boolv
    \\ asm_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ simp [])
  >- (
    irule IMP_memory_rel_Number \\ simp []
    \\ asm_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ metis_tac [memory_rel_index_in_bounds_small_int])
  \\ irule memory_rel_Boolv
  \\ asm_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ simp []
QED

val _=augment_srw_ss[rewrites[i2w_int_or,i2w_mod_pow2,compiler_ptr_bits_i2w]];

val _ = augment_srw_ss [rewrites [arch_width_eq32, arch_bytes_scaled_word]];

val _ = augment_srw_ss [rewrites [compiler_tag_mask_i2w]];

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

Theorem memory_rel_small_int:
  memory_rel c be ts refs sp st m dm ((Number i,Word(w:'a word))::vars) ∧
  word_bit 0 w ∧ good_dimindex (:α) ⇒
  ~small_int (dimindex (:'a)) i
Proof
  rw [] \\ CCONTR_TAC \\ fs []
  \\ ((first_assum o mp_then (Pos last) mp_tac) memory_rel_Number_IMP)
  \\ fs [] \\ CCONTR_TAC \\ rveq \\ fs []
  \\ fs [word_bit_test,Smallnum_bits]
QED

Theorem small_int_Smallnum_add:
  good_dimindex(:'a) /\ small_int (dimindex (:'a))(i1 + i2)  ==>
  Smallnum i1 + (Smallnum i2):'a word = Smallnum(i1 + i2)
Proof
 rw[Smallnum_i2w,good_dimindex_def,small_int_def,
    integer_wordTheory.word_i2w_add,integerTheory.INT_LDISTRIB]
QED

Theorem small_int_INT_MIN_MAX:
  good_dimindex(:'a) /\ small_int (dimindex (:'a)) i ==>
  (INT_MIN (:'a) <= 2 * i /\ 2 * i <= INT_MAX (:'a))
Proof
 rw[small_int_def,good_dimindex_def,INT_MIN_def,INT_MAX_def]
 \\ rfs [dimword_def]
 \\ rw[] \\ intLib.COOPER_TAC
QED

Theorem small_int_w2i_Smallnum_add:
  good_dimindex(:'a) /\
  small_int (dimindex (:'a)) (i1 + i2) /\
  small_int (dimindex (:'a)) i1 /\
  small_int (dimindex (:'a)) i2 ==>
  w2i(Smallnum i1 + (Smallnum i2):'a word) = w2i(Smallnum i1:'a word) + w2i(Smallnum i2:'a word)
Proof
 rw[] >>
 rw[small_int_Smallnum_add,Smallnum_i2w] >>
 imp_res_tac small_int_INT_MIN_MAX >>
 simp[integer_wordTheory.w2i_i2w,integerTheory.INT_LDISTRIB]
QED

Theorem state_rel_IMP_arch_64_bit:
  state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) xs locs ==>
  (s.limits.arch_64_bit = (dimindex (:'a) = 64))
Proof
  fs [state_rel_def,limits_inv_def]
QED

Theorem assign_Add:
  op = IntOp Add ==> ^assign_thm_goal
Proof
  rpt strip_tac
  \\ gvs []
  \\ `names_opt <> NONE` by (qpat_x_assum `_ ⇎ _` mp_tac \\ EVAL_TAC)
  \\ Cases_on `names_opt` \\ fs []
  \\ drule_all state_rel_cut_state_opt_SOME \\ strip_tac
  \\ drule state_rel_IMP_arch_64_bit \\ strip_tac
  \\ fs [do_app,oneline do_int_app_def] \\ gvs [AllCaseEqs()]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [get_var_def]
  \\ qpat_x_assum `state_rel c l1 l2 s t NONE locs` (fn th => NTAC 2 (mp_tac th))
  \\ strip_tac
  \\ simp_tac std_ss [Once state_rel_thm] \\ strip_tac \\ fs [] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac \\ fs []
  \\ gvs [LENGTH_EQ_2]
  \\ rpt_drule0 memory_rel_Number_IMP_Word_2
  \\ strip_tac \\ clean_tac
  \\ rpt_drule0 memory_rel_Add \\ fs [] \\ strip_tac
  \\ fs [assign_def,arg2_def,assign_Add_def]
  \\ imp_res_tac get_vars_2_imp
  \\ fs [Once list_Seq_def] \\ eval_tac \\ fs [wordSemTheory.inst_def]
  \\ fs [Once list_Seq_def]
  \\ eval_tac \\ fs [lookup_insert,wordSemTheory.get_var_def]
  \\ qabbrev_tac `mt = MustTerminate`
  \\ fs [Once list_Seq_def]
  \\ eval_tac \\ fs [lookup_insert,wordSemTheory.get_var_def,
                     wordSemTheory.get_var_imm_def]
  \\ fs [word_cmp_Test_1,word_bit_or,word_bit_if_1_0]
  \\ IF_CASES_TAC THEN1
   (fs [list_Seq_def,state_rel_thm] \\ eval_tac
    \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def,lookup_insert,
           wordSemTheory.set_vars_def,wordSemTheory.set_var_def,alist_insert_def]
    \\ conj_tac >- (rw [] \\ fs [adjust_var_11] \\ res_tac \\ fs [])
    \\ conj_tac
    >- (irule option_le_trans \\ qexists_tac `x.stack_max`
        \\ fs [option_le_max_right])
    \\ fs [lookup_insert,adjust_var_NEQ,adjust_var_11]
    \\ fs [inter_insert_ODD_adjust_set]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ `get_var a1' s.locals = SOME (Number n1) /\
        get_var a2' s.locals = SOME (Number n2)` by
         (qpat_x_assum `get_vars [a1'; a2'] s.locals = _` mp_tac
          \\ simp [get_vars_def, get_var_def, AllCaseEqs()])
    \\ `small_int (dimindex (:'a)) n1` by
         (qpat_x_assum `memory_rel _ _ _ _ _ _ _ _
            ((Number n1,Word w1)::(Number n2,Word w2)::_)` assume_tac
          \\ drule_all memory_rel_any_Number_IMP \\ strip_tac
          \\ rfs [word_bit_def] \\ fs [word_bit_def])
    \\ `small_int (dimindex (:'a)) n2` by
         (qpat_x_assum `memory_rel _ _ _ _ _ _ _ _
            ((Number n1,Word w1)::(Number n2,Word w2)::_)` assume_tac
          \\ drule memory_rel_swap \\ strip_tac
          \\ drule_all memory_rel_any_Number_IMP \\ strip_tac
          \\ rfs [word_bit_def] \\ fs [word_bit_def])
    \\ `small_int (dimindex (:'a)) (n1 + n2)` by
         (qpat_x_assum `memory_rel _ _ _ _ _ _ _ _
            ((Number (n1 + n2),Word (w1 + w2))::_)` assume_tac
          \\ drule_all memory_rel_any_Number_IMP \\ strip_tac
          \\ gvs [WORD_ADD_BIT0, word_bit_def])
    \\ `w1 = Smallnum n1` by
         (qpat_x_assum `memory_rel _ _ _ _ _ _ _ _
            ((Number n1,Word w1)::(Number n2,Word w2)::_)` assume_tac
          \\ pop_assum (mp_then (Pos last) mp_tac memory_rel_Number_IMP)
          \\ impl_tac >- fs [] \\ simp [])
    \\ `w2 = Smallnum n2` by
         (qpat_x_assum `memory_rel _ _ _ _ _ _ _ _
            ((Number n1,Word w1)::(Number n2,Word w2)::_)` assume_tac
          \\ drule memory_rel_swap \\ strip_tac
          \\ pop_assum (mp_then (Pos last) mp_tac memory_rel_Number_IMP)
          \\ impl_tac >- fs [] \\ simp [])
    \\ `w1 + w2 = Smallnum (n1 + n2)` by
         (asm_rewrite_tac [] \\ irule small_int_Smallnum_add \\ fs [])
    \\ asm_rewrite_tac []
    \\ irule IMP_memory_rel_Number \\ simp []
    \\ qpat_x_assum `memory_rel c t.be (THE x.tstamps) x.refs x.space t.store
            t.memory t.mdomain
            (join_env x.locals (toAList (inter t.locals (adjust_set x.locals))) ++
             [(the_global x.global,t.store⟨Globals⟩)] ++ flat x.stack t.stack)`
         (fn th => irule (MATCH_MP memory_rel_zero_space th)))
  \\ `~(small_int (dimindex (:'a)) n1 ∧ small_int (dimindex (:'a)) n2 ∧ small_int (dimindex (:'a)) (n1 + n2))` by
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
  \\ `state_rel c l1 l2 s t4 NONE locs` by fs [Abbr`t4`,state_rel_insert_3_1]
  \\ drule (GEN_ALL eval_Call_Add)
  \\ disch_then (qspecl_then [`x`,`SOME x'`,`n`,`l`,`n2`,`n1`,`dest`,`a2'`,`a1'`] mp_tac)
  \\ impl_tac >- (simp [Abbr`t4`] \\ fs [])
  \\ disch_then (strip_assume_tac o SPEC_ALL) \\ simp []
  \\ qpat_x_assum `let max = _ in _` (strip_assume_tac o CONV_RULE (DEPTH_CONV let_CONV))
  \\ unabbrev_all_tac
  \\ `x.limits = s.limits` by (imp_res_tac cut_state_opt_SOME_eq \\ gvs [])
  \\ `x.stack = s.stack /\ x.stack_max = s.stack_max /\
      x.stack_frame_sizes = s.stack_frame_sizes /\ x.locals_size = s.locals_size` by
       (imp_res_tac cut_state_opt_SOME_eq \\ gvs [])
  \\ imp_res_tac data_to_word_gcProofTheory.stack_rel_IMP_size_of_stack
  \\ reverse (Cases_on `q = SOME NotEnoughSpace`) \\ simp[]
  >- (first_x_assum drule \\ simp [state_rel_thm] \\ strip_tac
      \\ qpat_x_assum `option_le r'.stack_max _` mp_tac
      \\ qpat_x_assum `stack_size t.stack = _` mp_tac
      \\ rpt (qpat_x_assum `t.locals_size = _` mp_tac)
      \\ rpt (qpat_x_assum `t.stack_size = _` mp_tac)
      \\ simp [AC option_add_comm option_add_assoc])
  \\ conj_tac
  >- (qpat_x_assum `option_le r'.stack_max _` mp_tac
      \\ qpat_x_assum `stack_size t.stack = _` mp_tac
      \\ rpt (qpat_x_assum `t.locals_size = _` mp_tac)
      \\ rpt (qpat_x_assum `t.stack_size = _` mp_tac)
      \\ simp [AC option_add_comm option_add_assoc])
  \\ strip_tac \\ disj1_tac \\ CCONTR_TAC
  \\ `s.limits.arch_64_bit = (dimindex (:'a) = 64)` by fs []
  \\ `s.limits.length_limit = c.len_size` by fs [limits_inv_def]
  \\ `space_consumed x (IntOp Add) [Number n1; Number n2] =
       2 * bignum_size (dimindex (:α) = 64) n1 +
       2 * bignum_size (dimindex (:α) = 64) n2` by
       (`x.limits.arch_64_bit = (dimindex (:'a) = 64)` by fs []
        \\ asm_simp_tac (srw_ss()) [space_consumed_def, small_num_small_int]
        \\ simp [LET_THM])
  \\ `bignum_size (dimindex (:α) = 64) n1 + bignum_size (dimindex (:α) = 64) n2 <=
        2 ** s.limits.length_limit /\
      size_of_heap_args [Number n1; Number n2] x +
        space_consumed x (IntOp Add) [Number n1; Number n2] <= s.limits.heap_limit` by
       (qpat_x_assum `~(_ \/ _)` mp_tac \\ fs [])
  \\ `bignum_size s.limits.arch_64_bit n1 + bignum_size s.limits.arch_64_bit n2 <=
        2 ** c.len_size` by
       (qpat_x_assum `s.limits.arch_64_bit ⇔ _` (fn th => rewrite_tac [th])
        \\ qpat_x_assum `s.limits.length_limit = c.len_size` (fn th => rewrite_tac [GSYM th])
        \\ first_x_assum ACCEPT_TAC)
  \\ ‘no_thunks_in_refs x.refs’ by fs []
  \\ ‘no_thunks_in_refs s.refs’ by
   (qpat_x_assum ‘cut_state_opt _ _ = _’ mp_tac
    \\ simp [cut_state_opt_def] \\ strip_tac
    \\ imp_res_tac cut_state_refs_same \\ gvs [])
  \\ res_tac
  \\ qpat_x_assum `s.limits.heap_limit < _` mp_tac
  \\ qpat_x_assum `size_of_heap_args _ _ + space_consumed _ _ _ <= _` mp_tac
  \\ qpat_x_assum `space_consumed _ _ _ = _` (fn th => rewrite_tac [th])
  \\ qpat_x_assum `s.limits.arch_64_bit ⇔ _` (fn th => rewrite_tac [th])
  \\ DECIDE_TAC
QED

Theorem small_int_w2i_Smallnum_sub:
  good_dimindex(:'a) /\ small_int (dimindex (:'a))(i1 - i2) /\ small_int (dimindex (:'a)) i1 /\ small_int (dimindex (:'a)) i2 ==>
  w2i(Smallnum i1 - (Smallnum i2):'a word) = w2i(Smallnum i1:'a word) - w2i(Smallnum i2:'a word)
Proof
  rw[] >>
  rw[small_int_Smallnum_sub,Smallnum_i2w] >>
  imp_res_tac small_int_INT_MIN_MAX >>
  drule integer_wordTheory.w2i_i2w >>
  strip_tac >> fs [] >>
  `i2w (2 * i1) + -1w * i2w (2 * i2) = i2w (2 * (i1 - i2))` by (
    rw [integerTheory.INT_SUB_LDISTRIB] >>
    rewrite_tac [GSYM word_i2w_sub] >>
    fs []) >>
  simp[] >>
  simp[integer_wordTheory.w2i_i2w,integerTheory.INT_LDISTRIB, integerTheory.INT_SUB_LDISTRIB]
QED

Theorem word_bit_0_sub_lemma[local]:
  !w1 w2:'a word. ~word_bit 0 w1 /\ ~word_bit 0 w2 ==> ~word_bit 0 (w1 + -1w * w2)
Proof
  rw [wordsTheory.word_bit_def, wordsTheory.WORD_ADD_BIT0]
  \\ `word_bit 0 (-1w * w2) <=> word_bit 0 w2` by
       (rw [GSYM wordsTheory.WORD_NEG_MUL, wordsTheory.WORD_NEG, wordsTheory.WORD_ADD_BIT0,
            wordsTheory.word_1comp_def, fcpTheory.FCP_BETA, wordsTheory.word_bit_def]
        \\ `(1w:'a word) ' 0` by simp [wordsTheory.word_index, DIMINDEX_GT_0] \\ fs [])
  \\ fs [wordsTheory.word_bit_def]
QED

Theorem assign_Sub:
  op = IntOp Sub ==> ^assign_thm_goal
Proof
  rpt strip_tac
  \\ gvs []
  \\ `names_opt <> NONE` by (qpat_x_assum `_ ⇎ _` mp_tac \\ EVAL_TAC)
  \\ Cases_on `names_opt` \\ fs []
  \\ drule_all state_rel_cut_state_opt_SOME \\ strip_tac
  \\ drule state_rel_IMP_arch_64_bit \\ strip_tac
  \\ fs [do_app,oneline do_int_app_def] \\ gvs [AllCaseEqs()]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [get_var_def]
  \\ qpat_x_assum `state_rel c l1 l2 s t NONE locs` (fn th => NTAC 2 (mp_tac th))
  \\ strip_tac
  \\ simp_tac std_ss [Once state_rel_thm] \\ strip_tac \\ fs [] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac \\ fs []
  \\ gvs [LENGTH_EQ_2]
  \\ rpt_drule0 memory_rel_Number_IMP_Word_2
  \\ strip_tac \\ clean_tac
  \\ rpt_drule0 memory_rel_Sub \\ fs [] \\ strip_tac
  \\ qmatch_asmsub_rename_tac `(Number n1,Word w1)::(Number n2,Word w2)::_`
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
    \\ conj_tac >- (rw [] \\ fs [adjust_var_11] \\ res_tac \\ fs [])
    \\ conj_tac
    >- (irule option_le_trans \\ qexists_tac `x.stack_max`
        \\ fs [option_le_max_right])
    \\ fs [lookup_insert,adjust_var_NEQ,adjust_var_11]
    \\ fs [inter_insert_ODD_adjust_set]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ `get_var a1' s.locals = SOME (Number n1) /\
        get_var a2' s.locals = SOME (Number n2)` by
         (qpat_x_assum `get_vars [a1'; a2'] s.locals = _` mp_tac
          \\ simp [get_vars_def, get_var_def, AllCaseEqs()])
    \\ `small_int (dimindex (:'a)) n1` by
         (qpat_x_assum `memory_rel _ _ _ _ _ _ _ _
            ((Number n1,Word w1)::(Number n2,Word w2)::_)` assume_tac
          \\ drule_all memory_rel_any_Number_IMP \\ strip_tac
          \\ rfs [word_bit_def] \\ fs [word_bit_def])
    \\ `small_int (dimindex (:'a)) n2` by
         (qpat_x_assum `memory_rel _ _ _ _ _ _ _ _
            ((Number n1,Word w1)::(Number n2,Word w2)::_)` assume_tac
          \\ drule memory_rel_swap \\ strip_tac
          \\ drule_all memory_rel_any_Number_IMP \\ strip_tac
          \\ rfs [word_bit_def] \\ fs [word_bit_def])
    \\ `w1 = Smallnum n1` by
         (qpat_x_assum `memory_rel _ _ _ _ _ _ _ _
            ((Number n1,Word w1)::(Number n2,Word w2)::_)` assume_tac
          \\ pop_assum (mp_then (Pos last) mp_tac memory_rel_Number_IMP)
          \\ impl_tac >- fs [] \\ simp [])
    \\ `w2 = Smallnum n2` by
         (qpat_x_assum `memory_rel _ _ _ _ _ _ _ _
            ((Number n1,Word w1)::(Number n2,Word w2)::_)` assume_tac
          \\ drule memory_rel_swap \\ strip_tac
          \\ pop_assum (mp_then (Pos last) mp_tac memory_rel_Number_IMP)
          \\ impl_tac >- fs [] \\ simp [])
    \\ `~word_bit 0 (w1 + -1w * w2)` by (irule word_bit_0_sub_lemma \\ fs [])
    \\ `small_int (dimindex (:'a)) (n1 - n2)` by
         (qpat_x_assum `memory_rel _ _ _ _ _ _ _ _
            ((Number (n1 - n2),Word (w1 + -1w * w2))::_)` assume_tac
          \\ drule_all memory_rel_any_Number_IMP \\ strip_tac
          \\ fs [wordsTheory.word_bit_def])
    \\ `w1 + -1w * w2 = Smallnum (n1 - n2)` by
         (asm_rewrite_tac [GSYM wordsTheory.WORD_NEG_MUL, GSYM wordsTheory.word_sub_def]
          \\ irule small_int_Smallnum_sub \\ fs [])
    \\ asm_rewrite_tac []
    \\ irule IMP_memory_rel_Number \\ simp []
    \\ qpat_x_assum `memory_rel c t.be (THE x.tstamps) x.refs x.space t.store
            t.memory t.mdomain
            (join_env x.locals (toAList (inter t.locals (adjust_set x.locals))) ++
             [(the_global x.global,t.store⟨Globals⟩)] ++ flat x.stack t.stack)`
         (fn th => irule (MATCH_MP memory_rel_zero_space th)))
  \\ `~(small_int (dimindex (:'a)) n1 ∧ small_int (dimindex (:'a)) n2 ∧ small_int (dimindex (:'a)) (n1 - n2))` by
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
  \\ `state_rel c l1 l2 s t4 NONE locs` by fs [Abbr`t4`,state_rel_insert_3_1]
  \\ drule (GEN_ALL eval_Call_Sub)
  \\ disch_then (qspecl_then [`x`,`SOME x'`,`n`,`l`,`n2`,`n1`,`dest`,`a2'`,`a1'`] mp_tac)
  \\ impl_tac >- (simp [Abbr`t4`] \\ fs [])
  \\ disch_then (strip_assume_tac o SPEC_ALL) \\ simp []
  \\ qpat_x_assum `let max = _ in _` (strip_assume_tac o CONV_RULE (DEPTH_CONV let_CONV))
  \\ unabbrev_all_tac
  \\ `x.limits = s.limits` by (imp_res_tac cut_state_opt_SOME_eq \\ gvs [])
  \\ `x.stack = s.stack /\ x.stack_max = s.stack_max /\
      x.stack_frame_sizes = s.stack_frame_sizes /\ x.locals_size = s.locals_size` by
       (imp_res_tac cut_state_opt_SOME_eq \\ gvs [])
  \\ imp_res_tac data_to_word_gcProofTheory.stack_rel_IMP_size_of_stack
  \\ reverse (Cases_on `q = SOME NotEnoughSpace`) \\ simp[]
  >- (first_x_assum drule \\ simp [state_rel_thm] \\ strip_tac
      \\ qpat_x_assum `option_le r'.stack_max _` mp_tac
      \\ qpat_x_assum `stack_size t.stack = _` mp_tac
      \\ rpt (qpat_x_assum `t.locals_size = _` mp_tac)
      \\ rpt (qpat_x_assum `t.stack_size = _` mp_tac)
      \\ simp [AC option_add_comm option_add_assoc])
  \\ conj_tac
  >- (qpat_x_assum `option_le r'.stack_max _` mp_tac
      \\ qpat_x_assum `stack_size t.stack = _` mp_tac
      \\ rpt (qpat_x_assum `t.locals_size = _` mp_tac)
      \\ rpt (qpat_x_assum `t.stack_size = _` mp_tac)
      \\ simp [AC option_add_comm option_add_assoc])
  \\ strip_tac \\ disj1_tac \\ CCONTR_TAC
  \\ `s.limits.arch_64_bit = (dimindex (:'a) = 64)` by fs []
  \\ `s.limits.length_limit = c.len_size` by fs [limits_inv_def]
  \\ `space_consumed x (IntOp Sub) [Number n1; Number n2] =
       2 * bignum_size (dimindex (:α) = 64) n1 +
       2 * bignum_size (dimindex (:α) = 64) n2` by
       (`x.limits.arch_64_bit = (dimindex (:'a) = 64)` by fs []
        \\ asm_simp_tac (srw_ss()) [space_consumed_def, small_num_small_int]
        \\ simp [LET_THM])
  \\ `bignum_size (dimindex (:α) = 64) n1 + bignum_size (dimindex (:α) = 64) n2 <=
        2 ** s.limits.length_limit /\
      size_of_heap_args [Number n1; Number n2] x +
        space_consumed x (IntOp Sub) [Number n1; Number n2] <= s.limits.heap_limit` by
       (qpat_x_assum `~(_ \/ _)` mp_tac \\ fs [])
  \\ `bignum_size s.limits.arch_64_bit n1 + bignum_size s.limits.arch_64_bit n2 <=
        2 ** c.len_size` by
       (qpat_x_assum `s.limits.arch_64_bit ⇔ _` (fn th => rewrite_tac [th])
        \\ qpat_x_assum `s.limits.length_limit = c.len_size` (fn th => rewrite_tac [GSYM th])
        \\ first_x_assum ACCEPT_TAC)
  \\ ‘no_thunks_in_refs x.refs’ by fs []
  \\ ‘no_thunks_in_refs s.refs’ by
   (qpat_x_assum ‘cut_state_opt _ _ = _’ mp_tac
    \\ simp [cut_state_opt_def] \\ strip_tac
    \\ imp_res_tac cut_state_refs_same \\ gvs [])
  \\ res_tac
  \\ qpat_x_assum `s.limits.heap_limit < _` mp_tac
  \\ qpat_x_assum `size_of_heap_args _ _ + space_consumed _ _ _ <= _` mp_tac
  \\ qpat_x_assum `space_consumed _ _ _ = _` (fn th => rewrite_tac [th])
  \\ qpat_x_assum `s.limits.arch_64_bit ⇔ _` (fn th => rewrite_tac [th])
  \\ DECIDE_TAC
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
  rpt strip_tac \\ gvs []
  \\ `names_opt <> NONE` by (qpat_x_assum `_ ⇎ _` mp_tac \\ EVAL_TAC)
  \\ Cases_on `names_opt` \\ fs []
  \\ drule_all state_rel_cut_state_opt_SOME \\ strip_tac
  \\ drule state_rel_IMP_arch_64_bit \\ strip_tac
  \\ fs [do_app,oneline do_int_app_def] \\ gvs [AllCaseEqs()]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [get_var_def]
  \\ qpat_x_assum `state_rel c l1 l2 s t NONE locs` (fn th => NTAC 2 (mp_tac th))
  \\ strip_tac
  \\ simp_tac std_ss [Once state_rel_thm] \\ strip_tac \\ fs [] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac \\ fs []
  \\ gvs [LENGTH_EQ_2]
  \\ rpt_drule0 memory_rel_Number_IMP_Word_2
  \\ strip_tac \\ clean_tac
  \\ qmatch_asmsub_rename_tac `(Number n1,Word w1)::(Number n2,Word w2)::_`
  \\ fs [assign_def]
  \\ fs [get_vars_SOME_IFF,get_vars_SOME_IFF_data]
  \\ rveq \\ fs []
  \\ Cases_on `c.has_imul`
  >- (
    simp []
    \\ once_rewrite_tac [list_Seq_def]
    \\ fs [eq_eval]
    \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
    \\ fs []
    \\ once_rewrite_tac [list_Seq_def]
    \\ fs [eq_eval, wordSemTheory.inst_def]
    \\ once_rewrite_tac [list_Seq_def]
    \\ fs [eq_eval]
    \\ qabbrev_tac `mt = MustTerminate`
    \\ once_rewrite_tac [list_Seq_def]
    \\ fs [eq_eval, wordSemTheory.get_var_imm_def, word_cmp_Test_1,
           word_bit_or, word_bit_if_1_0]
    \\ IF_CASES_TAC
    >- (
      fs []
      \\ `small_int (dimindex (:'a)) n1` by (
        drule_all memory_rel_any_Number_IMP
        \\ strip_tac
        \\ fs [word_bit_def])
      \\ `memory_rel c t.be (THE s.tstamps) s.refs s.space t.store t.memory t.mdomain
          ((Number n2,Word w2)::
           (join_env s.locals (toAList (inter t.locals (adjust_set s.locals))) ++
            [(the_global s.global,t.store ' Globals)] ++ flat s.stack t.stack))`
      by (
        qpat_x_assum `memory_rel _ _ _ _ _ _ _ _ ((Number n1,Word w1)::_)`
          (assume_tac o MATCH_MP memory_rel_tail)
        \\ asm_rewrite_tac [])
      \\ `small_int (dimindex (:'a)) n2` by (
        drule_all memory_rel_any_Number_IMP
        \\ strip_tac
        \\ fs [word_bit_def])
      \\ imp_res_tac memory_rel_Number_IMP
      \\ gvs []
      \\ mp_tac (Q.INST [`i` |-> `n1`, `j` |-> `n2`] small_int_Smallnum_imul)
      \\ asm_rewrite_tac []
      \\ strip_tac
      \\ fs [WORD_MULT_COMM]
      \\ simp [list_Seq_def, eq_eval, wordSemTheory.set_vars_def, alist_insert_def]
      \\ fs [state_rel_thm, lookup_insert, adjust_var_11, inter_insert_ODD_adjust_set]
      \\ conj_tac
      >- (
        rw []
        \\ fs [adjust_var_11]
        \\ res_tac
        \\ fs [])
      \\ conj_tac
      >- (
        irule option_le_trans
        \\ qexists_tac `x.stack_max`
        \\ fs [option_le_max_right])
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ match_mp_tac IMP_memory_rel_Number \\ fs []
      \\ imp_res_tac memory_rel_zero_space \\ fs [])
    \\ `~(small_int (dimindex (:'a)) n1 /\ small_int (dimindex (:'a)) n2 /\
       small_int (dimindex (:'a)) (n1 * n2))`
    by (
      CCONTR_TAC
      \\ qpat_x_assum `~~(small_int _ n1 /\ small_int _ n2 /\ small_int _ (n1 * n2))`
           (strip_assume_tac o REWRITE_RULE [NOT_CLAUSES])
      \\ qpat_assum `memory_rel _ _ _ _ _ _ _ _ ((Number n1,Word w1)::_)`
           (assume_tac o MATCH_MP memory_rel_tail)
      \\ imp_res_tac memory_rel_Number_IMP
      \\ fs [word_bit_def, Smallnum_0]
      \\ rveq
      \\ mp_tac (Q.INST [`i` |-> `n1`, `j` |-> `n2`] small_int_Smallnum_imul)
      \\ simp [WORD_MULT_COMM])
    \\ unabbrev_all_tac
    \\ simp [stack_consumed_def, OPTION_MAP2_NONE, miscTheory.the_def, list_Seq_def]
    \\ qmatch_goalsub_abbrev_tac `evaluate (_,t4)`
    \\ `state_rel c l1 l2 s t4 NONE locs` by
         simp [Abbr`t4`, insert_shadow, state_rel_insert_3_1]
    \\ qmatch_goalsub_rename_tac
         `Call _ (SOME Mul_location) [adjust_var left_arg; adjust_var right_arg] _`
    \\ qmatch_asmsub_rename_tac `cut_state_opt (SOME retained_names) s = SOME x`
    \\ drule (GEN_ALL eval_Call_Mul)
    \\ disch_then (qspecl_then
         [`x`, `SOME retained_names`, `n`, `l`, `n2`, `n1`, `dest`, `right_arg`, `left_arg`]
         mp_tac)
    \\ `~(small_int (dimindex (:'a)) n1 /\ 0 <= n1 /\
          small_int (dimindex (:'a)) n2 /\ 0 <= n2 /\
          small_int (dimindex (:'a)) (n1 * n2))`
    by (
      qpat_assum `~(small_int _ n1 /\ small_int _ n2 /\ small_int _ (n1 * n2))` mp_tac
      \\ tautLib.TAUT_TAC)
    \\ impl_tac
    >- (
      simp [Abbr`t4`]
      \\ simp [get_vars_def]
      \\ fs [get_var_def])
    \\ disch_then (strip_assume_tac o SPEC_ALL)
    \\ qmatch_asmsub_rename_tac `_ = (call_result,call_state)`
    \\ simp []
    \\ qpat_x_assum `let max = _ in _`
         (strip_assume_tac o CONV_RULE (DEPTH_CONV let_CONV))
    \\ qpat_x_assum `_ = (call_result,call_state)` mp_tac
    \\ simp [list_Seq_def]
    \\ disch_then kall_tac
    \\ unabbrev_all_tac
    \\ `x.limits = s.limits` by (
      imp_res_tac cut_state_opt_SOME_eq
      \\ gvs [])
    \\ `x.stack = s.stack /\ x.stack_max = s.stack_max /\
        x.stack_frame_sizes = s.stack_frame_sizes /\ x.locals_size = s.locals_size`
    by (
      imp_res_tac cut_state_opt_SOME_eq
      \\ gvs [])
    \\ imp_res_tac data_to_word_gcProofTheory.stack_rel_IMP_size_of_stack
    \\ reverse (Cases_on `call_result = SOME NotEnoughSpace`)
    \\ simp []
    >- (
      qpat_x_assum `call_result <> SOME NotEnoughSpace ==> _` mp_tac
      \\ simp [state_rel_thm, AC option_add_comm option_add_assoc]
      \\ strip_tac
      \\ fs [])
    \\ conj_tac
    >- (
      qpat_x_assum `option_le call_state.stack_max _` mp_tac
      \\ simp [AC option_add_comm option_add_assoc])
    \\ `space_consumed x (IntOp Mult) [Number n1; Number n2] =
        2 * bignum_size (dimindex (:'a) = 64) n1 +
        2 * bignum_size (dimindex (:'a) = 64) n2` by
         simp [space_consumed_def, small_num_small_int, LET_THM]
    \\ `x.refs = s.refs` by (
      imp_res_tac cut_state_opt_SOME_eq
      \\ gvs [])
    \\ `s.limits.arch_64_bit = (dimindex (:'a) = 64)` by fs []
    \\ `s.limits.length_limit = c.len_size` by fs [limits_inv_def]
    \\ strip_tac
    \\ disj1_tac
    \\ qpat_assum `call_result = SOME NotEnoughSpace ==> _`
         (fn th => qpat_assum `call_result = SOME NotEnoughSpace`
           (fn result => assume_tac (CONJUNCT2 (MATCH_MP th result))))
    \\ qpat_assum
         `~(small_int _ n1 /\ 0 <= n1 /\ small_int _ n2 /\ 0 <= n2 /\
            small_int _ (n1 * n2))`
         (assume_tac o REWRITE_RULE [DE_MORGAN_THM])
    \\ qpat_x_assum `c.gc_kind <> None /\ no_thunks_in_refs s.refs ==> _` mp_tac
    \\ asm_rewrite_tac []
    \\ decide_tac)
  \\ fs []
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval,wordSemTheory.inst_def]
  \\ `n2w (w2n w2 * w2n w1) = FST (single_mul w2 w1 0w) /\
      n2w (w2n w2 * w2n w1 DIV dimword (:α)) =
        SND (single_mul w2 w1 0w)` by
    (fs [multiwordTheory.single_mul_def,GSYM word_mul_n2w] \\ NO_TAC) \\ fs []
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ simp [Once word_exp_ShiftVar_bits] \\ fs [eq_eval]
  \\ rewrite_tac [list_Seq_def]
  \\ once_rewrite_tac [``list_Seq [MustTerminate x]``
       |> REWRITE_CONV [list_Seq_def] |> GSYM]
  \\ once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ fs [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def,lookup_insert,
         asmTheory.word_cmp_def]
  \\ IF_CASES_TAC \\ fs []
  >- (fs [eq_eval,wordSemTheory.set_vars_def,alist_insert_def]
  \\ fs [dataSemTheory.call_env_def,alist_insert_def,push_env_def,
         dataSemTheory.set_var_def,wordSemTheory.set_vars_def]
  \\ fs [state_rel_thm,lookup_insert,adjust_var_11]
  \\ conj_tac >- (rw [] \\ fs [adjust_var_11] \\ res_tac \\ fs [])
  \\ conj_tac
  >- (irule option_le_trans \\ qexists_tac `x.stack_max`
      \\ fs [option_le_max_right])
  \\ fs [inter_insert_ODD_adjust_set]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ qpat_x_assum `memory_rel _ _ _ _ _ _ _ _
       ((Number n1,Word w1)::(Number n2,Word w2)::_)` assume_tac
  \\ drule memory_rel_swap \\ strip_tac
  \\ first_x_assum (mp_then (Pos hd) mp_tac (memory_rel_Number_single_mul
       |> SIMP_RULE std_ss [LET_THM,AND_IMP_INTRO]
       |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)
       |> SIMP_RULE std_ss [LET_THM,AND_IMP_INTRO]))
  \\ simp []
  \\ disch_then assume_tac
  \\ `x.refs = s.refs /\ x.tstamps = s.tstamps /\ x.global = s.global /\
      x.stack = s.stack` by
       (imp_res_tac cut_state_opt_SOME_eq \\ asm_rewrite_tac [] \\ simp [])
  \\ PURE_ONCE_REWRITE_TAC [Q.SPECL [`n1`,`n2`] integerTheory.INT_MUL_COMM]
  \\ asm_rewrite_tac []
  \\ qpat_x_assum `memory_rel c t.be (THE s.tstamps) s.refs s.space t.store
        t.memory t.mdomain ((Number (n2 * n1),Word _)::_)`
       (fn th => mp_tac (MATCH_MP memory_rel_zero_space th))
  \\ match_mp_tac memory_rel_rearrange
  \\ rw [] \\ fs [MEM_APPEND]
  \\ disj2_tac \\ disj1_tac
  \\ `x.locals = mk_wf (inter s.locals x')` by
       (imp_res_tac cut_state_opt_SOME_eq \\ fs [])
  \\ qpat_x_assum `MEM x'' (join_env x.locals _)` mp_tac
  \\ asm_rewrite_tac []
  \\ simp [join_env_def, MEM_MAP, MEM_FILTER, MEM_toAList, EXISTS_PROD, PULL_EXISTS,
           lookup_inter_alt, lookup_mk_wf]
  \\ rw []
  \\ `(p_1 - 2) DIV 2 ∈ domain x' /\ (p_1 - 2) DIV 2 ∈ domain s.locals` by
       (qpat_x_assum `p_1 ∈ domain (adjust_set (inter s.locals x'))` mp_tac
        \\ simp [domain_lookup, lookup_adjust_set, AllCaseEqs(), lookup_inter_alt]
        \\ rw [] \\ fs [domain_lookup])
  \\ disj1_tac \\ qexists_tac `p_1`
  \\ simp [lookup_adjust_set, domain_lookup, lookup_inter_alt]
  \\ fs [EVEN_ODD])
  \\ `~(small_int (dimindex (:'a)) n1 /\ small_int (dimindex (:'a)) n2 /\ 0 <= n1 /\ 0 <= n2 /\
        small_int (dimindex (:'a)) (n1 * n2))` by
   (CCONTR_TAC \\ fs []
    \\ `~word_bit 0 w1` by (spose_not_then strip_assume_tac
                            \\ imp_res_tac memory_rel_small_int)
    \\ drule memory_rel_swap \\ strip_tac
    \\ `~word_bit 0 w2` by (spose_not_then strip_assume_tac
                            \\ imp_res_tac memory_rel_small_int)
    \\ first_x_assum (mp_then (Pos last) mp_tac (GEN_ALL memory_rel_Number_IMP))
    \\ first_x_assum (mp_then (Pos last) mp_tac (GEN_ALL memory_rel_Number_IMP))
    \\ rpt strip_tac \\ rfs [] \\ fs []
    \\ dxrule NONNEG_INT \\ dxrule NONNEG_INT \\ rpt strip_tac \\ fs []
    \\ fs [multiwordTheory.single_mul_def]
    \\ fs [GSYM word_bit_test_0]
    \\ fs [WORD_LEFT_AND_OVER_OR]
    \\ fs [DIV_MOD_MOD_DIV, w2n_mul_less]
    \\ fs [DIV_EQ_X, NOT_LESS]
    \\ Cases_on `Smallnum (&j) = 0w` >- fs [dimword_def]
    \\ Cases_on `Smallnum (&j') = 0w` >- fs [dimword_def]
    \\ rfs[w2n_lsr] \\ fs [Smallnum_def,small_int_def, X_LT_DIV] \\ fs [small_int_def]
    \\ qpat_x_assum `dimword (:α) <= _` mp_tac \\ simp [GSYM NOT_LESS]
    \\ fs [good_dimindex_def, dimword_def] \\ rfs [] \\ fs [quad_times_div_half_double])
  \\ simp [stack_consumed_def,OPTION_MAP2_NONE,miscTheory.the_def,list_Seq_def]
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,t4)`
  \\ `state_rel c l1 l2 s t4 NONE locs` by
        (fs [Abbr`t4`,state_rel_thm,lookup_insert] \\ rfs [inter_insert_ODD_adjust_set_alt])
  \\ drule (GEN_ALL eval_Call_Mul)
  \\ disch_then (qspecl_then [`x`,`SOME x'`,`n`,`l`,`n2`,`n1`,`dest`,`a2'`,`a1'`] mp_tac)
  \\ impl_tac >- (simp [Abbr`t4`] \\ simp [get_vars_def] \\ fs [get_var_def])
  \\ disch_then (strip_assume_tac o SPEC_ALL) \\ simp []
  \\ qpat_x_assum `let max = _ in _` (strip_assume_tac o CONV_RULE (DEPTH_CONV let_CONV))
  \\ qpat_x_assum `_ = (_,_)` mp_tac
  \\ simp [list_Seq_def] \\ disch_then kall_tac
  \\ unabbrev_all_tac
  \\ `x.limits = s.limits` by (imp_res_tac cut_state_opt_SOME_eq \\ gvs [])
  \\ `x.stack = s.stack /\ x.stack_max = s.stack_max /\
      x.stack_frame_sizes = s.stack_frame_sizes /\ x.locals_size = s.locals_size` by
       (imp_res_tac cut_state_opt_SOME_eq \\ gvs [])
  \\ imp_res_tac data_to_word_gcProofTheory.stack_rel_IMP_size_of_stack
  \\ reverse (Cases_on `q = SOME NotEnoughSpace`) \\ simp[]
  >- (IF_CASES_TAC THEN1 (rfs [] \\ fs [])
      \\ first_x_assum drule \\ simp [state_rel_thm]
      \\ strip_tac
      \\ qpat_x_assum `option_le _ _` mp_tac \\ simp []
      \\ qpat_x_assum `option_le _ _` mp_tac \\ simp []
      \\ simp [AC option_add_comm option_add_assoc])
  \\ IF_CASES_TAC THEN1 (rfs [] \\ fs [])
  \\ conj_tac
  >- (qpat_x_assum `option_le r'.stack_max _` mp_tac
      \\ qpat_x_assum `stack_size t.stack = _` mp_tac
      \\ rpt (qpat_x_assum `t.locals_size = _` mp_tac)
      \\ rpt (qpat_x_assum `t.stack_size = _` mp_tac)
      \\ simp [AC option_add_comm option_add_assoc])
  \\ strip_tac \\ disj1_tac \\ CCONTR_TAC
  \\ `s.limits.arch_64_bit = (dimindex (:'a) = 64)` by fs []
  \\ `s.limits.length_limit = c.len_size` by fs [limits_inv_def]
  \\ `space_consumed x (IntOp Mult) [Number n1; Number n2] =
       2 * bignum_size (dimindex (:α) = 64) n1 +
       2 * bignum_size (dimindex (:α) = 64) n2` by
       (`x.limits.arch_64_bit = (dimindex (:'a) = 64)` by fs []
        \\ `~(small_int (dimindex (:α)) n1 ∧ 0 ≤ n1 ∧ small_int (dimindex (:α)) n2 ∧ 0 ≤ n2 ∧
              small_int (dimindex (:α)) (n1 * n2))` by metis_tac []
        \\ asm_simp_tac (srw_ss()) [space_consumed_def, small_num_small_int]
        \\ simp [LET_THM])
  \\ `bignum_size (dimindex (:α) = 64) n1 + bignum_size (dimindex (:α) = 64) n2 <=
        2 ** s.limits.length_limit /\
      size_of_heap_args [Number n1; Number n2] x +
        space_consumed x (IntOp Mult) [Number n1; Number n2] <= s.limits.heap_limit` by
       (qpat_x_assum `~(_ \/ _)` mp_tac \\ fs [])
  \\ `bignum_size s.limits.arch_64_bit n1 + bignum_size s.limits.arch_64_bit n2 <=
        2 ** c.len_size` by
       (qpat_x_assum `s.limits.arch_64_bit ⇔ _` (fn th => rewrite_tac [th])
        \\ qpat_x_assum `s.limits.length_limit = c.len_size` (fn th => rewrite_tac [GSYM th])
        \\ first_x_assum ACCEPT_TAC)
  \\ ‘no_thunks_in_refs x.refs’ by fs []
  \\ ‘no_thunks_in_refs s.refs’ by
   (qpat_x_assum ‘cut_state_opt _ _ = _’ mp_tac
    \\ simp [cut_state_opt_def] \\ strip_tac
    \\ imp_res_tac cut_state_refs_same \\ gvs [])
  \\ res_tac
  \\ qpat_x_assum `s.limits.heap_limit < _` mp_tac
  \\ qpat_x_assum `size_of_heap_args _ _ + space_consumed _ _ _ <= _` mp_tac
  \\ qpat_x_assum `space_consumed _ _ _ = _` (fn th => rewrite_tac [th])
  \\ qpat_x_assum `s.limits.arch_64_bit ⇔ _` (fn th => rewrite_tac [th])
  \\ DECIDE_TAC
QED

Theorem word_bit_lsr_dimindex_1:
   word_bit 0 ((w1 ⋙ (dimindex (:'a) − 1)):'a word) <=> word_msb w1
Proof
  fs [word_bit_def,word_lsr_def,fcpTheory.FCP_BETA,word_msb_def]
QED

Theorem state_rel_Number_IMP:
   state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) NONE locs /\
    get_var a1 s.locals = SOME (Number i1) /\
    lookup (adjust_var a1) t.locals = SOME v1 ==>
    ?w1. (v1 = Word w1) /\
         (~(word_bit 0 w1) <=> small_int (dimindex (:'a)) i1) /\
         (~(word_msb w1) /\ ~(word_bit 0 w1) ==> 0 <= i1 /\ w1 = n2w (2 * Num i1))
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

Theorem state_rel_Number_Smallnum[local]:
  state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) NONE locs /\
  get_var v s.locals = SOME (Number i) /\
  lookup (adjust_var v) t.locals = SOME value /\
  small_int (dimindex (:'a)) i ==>
  value = Word (Smallnum i)
Proof
  fs [state_rel_thm]
  \\ rw []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]
  \\ drule0 (GEN_ALL memory_rel_get_var_IMP)
  \\ disch_then (qspec_then `v` mp_tac)
  \\ fs [get_var_def, wordSemTheory.get_var_def]
  \\ rw []
  \\ drule_all memory_rel_Number_IMP
  \\ simp []
QED

Theorem evaluate_If_Less_0[local]:
  wordSem$get_var 1 (s:('a,'c,'ffi) wordSem$state) = SOME (Word w) ==>
  wordSem$evaluate (if native then If Less 1 (Imm 0) negative positive else negative,s) =
  wordSem$evaluate (if native /\ ~word_msb w then positive else negative,s)
Proof
  strip_tac
  \\ Cases_on `native`
  \\ simp [Once wordSemTheory.evaluate_def, wordSemTheory.get_var_imm_def,
           asmTheory.word_cmp_def, GSYM word_msb_neg]
  \\ Cases_on `word_msb w`
  \\ simp []
QED

Theorem assign_Div:
  op = IntOp Div ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ imp_res_tac state_rel_arch_width
  \\ gvs []
  \\ `names_opt <> NONE` by (qpat_x_assum `_ ⇎ _` mp_tac \\ EVAL_TAC)
  \\ Cases_on `names_opt` \\ fs []
  \\ drule_all state_rel_cut_state_opt_SOME \\ strip_tac
  \\ drule state_rel_IMP_arch_64_bit \\ strip_tac
  \\ fs [do_app,oneline do_int_app_def] \\ gvs [AllCaseEqs()]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [get_var_def]
  \\ qmatch_asmsub_rename_tac `get_vars args s.locals = SOME [Number i1; Number i2]`
  \\ fs [assign_def]
  \\ fs [get_vars_SOME_IFF]
  \\ fs [get_vars_SOME_IFF_data]
  \\ gvs [LENGTH_EQ_2]
  \\ fs [get_vars_SOME_IFF, get_vars_SOME_IFF_data]
  \\ Cases_on `c.has_idiv`
  >- (
    simp []
    \\ qmatch_goalsub_rename_tac `SmallDivMod F left_arg right_arg`
    \\ qmatch_asmsub_rename_tac `cut_state_opt (SOME retained_names) s = SOME x`
    \\ fs [wordSemTheory.get_var_def]
    \\ `?left_word. lookup (adjust_var left_arg) t.locals = SOME (Word left_word) /\
         (~word_bit 0 left_word <=> small_int (dimindex (:'a)) i1) /\
         (~word_msb left_word /\ ~word_bit 0 left_word ==>
         0 <= i1 /\ left_word = n2w (2 * Num i1))` by
         metis_tac [state_rel_Number_IMP]
    \\ `?right_word. lookup (adjust_var right_arg) t.locals = SOME (Word right_word) /\
         (~word_bit 0 right_word <=> small_int (dimindex (:'a)) i2) /\
         (~word_msb right_word /\ ~word_bit 0 right_word ==>
          0 <= i2 /\ right_word = n2w (2 * Num i2))`
    by (
      drule_all (Q.INST [`a1` |-> `right_arg`, `i1` |-> `i2`]
                   state_rel_Number_IMP)
      \\ disch_then (qx_choose_then `right_word` strip_assume_tac)
      \\ qexists_tac `right_word`
      \\ simp [])
    \\ gvs []
    \\ once_rewrite_tac [list_Seq_def]
    \\ fs [eq_eval]
    \\ qabbrev_tac `mt = MustTerminate`
    \\ once_rewrite_tac [list_Seq_def]
    \\ fs [eq_eval, wordSemTheory.get_var_imm_def, word_cmp_Test_1, word_bit_or]
    \\ Cases_on `small_int (dimindex (:'a)) i1 /\ small_int (dimindex (:'a)) i2`
    >- (
      fs []
      \\ `left_word = Smallnum i1` by (
        mp_tac (Q.INST [`v` |-> `left_arg`, `i` |-> `i1`,
                        `value` |-> `Word left_word`] state_rel_Number_Smallnum)
        \\ simp [])
      \\ `right_word = Smallnum i2` by (
        mp_tac (Q.INST [`v` |-> `right_arg`, `i` |-> `i2`,
                        `value` |-> `Word right_word`] state_rel_Number_Smallnum)
        \\ simp [])
      \\ gvs []
      \\ `good_dimindex (:'a)` by fs [state_rel_thm]
      \\ `word_msb ((Smallnum i1 : 'a word) || Smallnum i2) =
          (word_msb (Smallnum i1 : 'a word) \/ word_msb (Smallnum i2 : 'a word))` by
        simp [word_msb_def, word_or_def, fcpTheory.FCP_BETA]
      \\ qabbrev_tac `tag_state = t with locals :=
          insert 1 (Word (Smallnum i1 || Smallnum i2)) t.locals`
      \\ `wordSem$get_var 1 tag_state =
          SOME (Word ((Smallnum i1:'a word) || Smallnum i2))` by
        simp [Abbr`tag_state`, wordSemTheory.get_var_def, lookup_insert]
      \\ qpat_assum `wordSem$get_var 1 tag_state = SOME (Word _)`
        (fn th => once_rewrite_tac [MATCH_MP evaluate_If_Less_0 th])
      \\ simp [small_int_Smallnum_msb, integerTheory.INT_NOT_LT]
      \\ Cases_on `(c.has_div \/ c.has_longdiv) /\ 0 <= i1 /\ 0 <= i2`
      >- (
        simp []
        \\ qpat_x_assum `(c.has_div \/ c.has_longdiv) /\ 0 <= i1 /\ 0 <= i2`
          (strip_assume_tac o CONJUNCT2)
        \\ `?num_left. i1 = &num_left` by (Cases_on `i1` \\ fs [])
        \\ `?num_right. i2 = &num_right` by (Cases_on `i2` \\ fs [])
        \\ gvs []
        \\ `~word_msb (Smallnum (&num_left) : 'a word) /\
            ~word_msb (Smallnum (&num_right) : 'a word)` by
          simp [small_int_Smallnum_msb]
        \\ `2 * num_left < dimword (:'a) /\ 2 * num_right < dimword (:'a)` by
          fs [small_int_def, GSYM dimword_def, X_LT_DIV]
        \\ `n2w (2 * num_right) <> (0w:'a word)` by fs []
        \\ `small_int (dimindex (:'a)) (&(num_left DIV num_right))` by (
          fs [small_int_def]
          \\ irule LESS_EQ_LESS_TRANS
          \\ qexists_tac `num_left`
          \\ simp [DIV_LESS_EQ])
        \\ unabbrev_all_tac
        \\ Cases_on `c.has_div`
        >- (
          `(n2w (2 * num_left) / n2w (2 * num_right) : 'a word) << 1 =
            Smallnum (&(num_left DIV num_right))` by (
            fs [wordsTheory.word_quot_def, word_div_def, Smallnum_def]
            \\ fs [WORD_MUL_LSL, word_mul_n2w, GSYM DIV_DIV_DIV_MULT,
                   MULT_DIV |> ONCE_REWRITE_RULE [MULT_COMM]])
          \\ simp [list_Seq_def, eq_eval, wordSemTheory.inst_def, Smallnum_def,
                   lookup_insert, adjust_var_11]
          \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
          \\ simp [eq_eval, wordSemTheory.set_vars_def, alist_insert_def, insert_shadow]
          \\ gvs [state_rel_thm, lookup_insert, adjust_var_11,
                  inter_insert_ODD_adjust_set, dataSemTheory.set_var_def]
          \\ conj_tac
          >- (
            rw []
            \\ res_tac
            \\ fs [])
          \\ conj_tac
          >- (
            irule option_le_trans
            \\ qexists_tac `x.stack_max`
            \\ fs [option_le_max_right])
          \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
          \\ match_mp_tac memory_rel_insert \\ fs []
          \\ match_mp_tac IMP_memory_rel_Number \\ fs []
          \\ imp_res_tac memory_rel_zero_space \\ fs [])
        \\ `2 * num_left DIV (2 * num_right) < dimword (:'a)` by (
          irule LESS_EQ_LESS_TRANS
          \\ qexists_tac `2 * num_left`
          \\ simp [DIV_LESS_EQ])
        \\ `(n2w (2 * num_left DIV (2 * num_right)) : 'a word) << 1 =
            Smallnum (&(num_left DIV num_right))` by (
          fs [wordsTheory.word_quot_def, word_div_def, Smallnum_def]
          \\ fs [WORD_MUL_LSL, word_mul_n2w, GSYM DIV_DIV_DIV_MULT,
                 MULT_DIV |> ONCE_REWRITE_RULE [MULT_COMM]])
        \\ simp [list_Seq_def, eq_eval, wordSemTheory.inst_def, Smallnum_def,
                 lookup_insert, adjust_var_11]
        \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
        \\ simp [eq_eval, wordSemTheory.set_vars_def, alist_insert_def, insert_shadow]
        \\ gvs [state_rel_thm, lookup_insert, adjust_var_11,
                inter_insert_ODD_adjust_set, dataSemTheory.set_var_def]
        \\ conj_tac
        >- (
          rw []
          \\ res_tac
          \\ fs [])
        \\ conj_tac
        >- (
          irule option_le_trans
          \\ qexists_tac `x.stack_max`
          \\ fs [option_le_max_right])
        \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
        \\ match_mp_tac memory_rel_insert \\ fs []
        \\ match_mp_tac IMP_memory_rel_Number \\ fs []
        \\ imp_res_tac memory_rel_zero_space \\ fs [])
      \\ simp []
      \\ once_rewrite_tac [list_Seq_def]
      \\ mp_tac (Q.INST [`i` |-> `i1`, `j` |-> `i2`,
                        `v1` |-> `left_arg`, `v2` |-> `right_arg`,
                        `is_mod` |-> `F`, `s` |-> `tag_state`]
                        evaluate_SmallDivMod_results)
      \\ simp [Abbr`tag_state`, wordSemTheory.get_var_def, lookup_insert, adjust_var_11]
      \\ strip_tac
      \\ asm_rewrite_tac []
      \\ simp [eq_eval]
      \\ once_rewrite_tac [list_Seq_def]
      \\ simp [eq_eval]
      \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
      \\ simp [list_Seq_def, eq_eval, wordSemTheory.get_var_imm_def, asmTheory.word_cmp_def]
      \\ mp_tac (Q.INST [`bits` |-> `dimindex (:'a)`, `a` |-> `i1`, `b` |-> `i2`]
                        small_int_div_bounds)
      \\ simp []
      \\ strip_tac
      \\ mp_tac (Q.INST [`q` |-> `i1 / i2`] small_int_quotient_check)
      \\ simp []
      \\ strip_tac
      \\ once_rewrite_tac [word_exp_set_var_ShiftVar_lemma]
      \\ simp [insert_swap, insert_shadow, COND_RAND]
      \\ Cases_on `small_int (dimindex (:'a)) (i1 / i2)`
      >- (
        `(i2w (i1 / i2) : 'a word) << 1 = Smallnum (i1 / i2)` by (
          PURE_REWRITE_TAC [Smallnum_i2w, WORD_MUL_LSL]
          \\ CONV_TAC numLib.REDUCE_CONV
          \\ once_rewrite_tac [GSYM integer_wordTheory.i2w_pos]
          \\ PURE_REWRITE_TAC [integer_wordTheory.word_i2w_mul]
          \\ REFL_TAC)
        \\ qpat_x_assum `~((c.has_div \/ c.has_longdiv) /\ 0 <= i1 /\ 0 <= i2)` kall_tac
        \\ simp [wordSemTheory.set_vars_def, alist_insert_def]
        \\ gvs [state_rel_thm, lookup_insert, adjust_var_11,
                inter_insert_ODD_adjust_set, dataSemTheory.set_var_def]
        \\ conj_tac
        >- (
          rw []
          \\ res_tac
          \\ fs [])
        \\ conj_tac
        >- (
          irule option_le_trans
          \\ qexists_tac `x.stack_max`
          \\ fs [option_le_max_right])
        \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
        \\ match_mp_tac memory_rel_insert \\ fs []
        \\ match_mp_tac IMP_memory_rel_Number \\ fs []
        \\ imp_res_tac memory_rel_zero_space \\ fs [])
      \\ simp []
      \\ qpat_x_assum `~((c.has_div \/ c.has_longdiv) /\ 0 <= i1 /\ 0 <= i2)` kall_tac
      \\ unabbrev_all_tac
      \\ simp [stack_consumed_def, small_num_small_int, OPTION_MAP2_NONE, miscTheory.the_def]
      \\ qmatch_goalsub_abbrev_tac `evaluate (MustTerminate _,call_input)`
      \\ `state_rel c l1 l2 s call_input NONE locs` by
        gvs [Abbr`call_input`, state_rel_thm, lookup_insert, adjust_var_11,
             inter_insert_ODD_adjust_set_alt]
      \\ drule (GEN_ALL eval_Call_Div)
      \\ disch_then (qspecl_then
        [`x`, `SOME retained_names`, `n`, `l + 1`, `i2`, `i1`, `dest`, `right_arg`, `left_arg`]
        mp_tac)
      \\ impl_tac
      >- (
        simp [Abbr`call_input`, get_vars_def]
        \\ fs [get_var_def])
      \\ disch_then (strip_assume_tac o SPEC_ALL)
      \\ qmatch_asmsub_rename_tac `_ = (call_result,call_state)`
      \\ simp [small_num_small_int]
      \\ qpat_x_assum `let max = _ in _`
        (strip_assume_tac o CONV_RULE (DEPTH_CONV let_CONV))
      \\ qpat_x_assum `_ = (call_result,call_state)` mp_tac
      \\ simp [list_Seq_def, eq_eval]
      \\ disch_then kall_tac
      \\ unabbrev_all_tac
      \\ `x.limits = s.limits` by (
        imp_res_tac cut_state_opt_SOME_eq
        \\ gvs [])
      \\ `x.stack = s.stack /\ x.stack_max = s.stack_max /\
          x.stack_frame_sizes = s.stack_frame_sizes /\ x.locals_size = s.locals_size`
      by (
        imp_res_tac cut_state_opt_SOME_eq
        \\ gvs [])
      \\ qpat_assum `state_rel c l1 l2 s t NONE locs`
        (strip_assume_tac o REWRITE_RULE [state_rel_thm])
      \\ imp_res_tac data_to_word_gcProofTheory.stack_rel_IMP_size_of_stack
      \\ reverse (Cases_on `call_result = SOME NotEnoughSpace`)
      \\ simp []
      >- (
        qpat_x_assum `call_result <> SOME NotEnoughSpace ==> _` mp_tac
        \\ simp [state_rel_thm, dataSemTheory.set_var_def,
                 AC option_add_comm option_add_assoc]
        \\ strip_tac
        \\ fs [])
      \\ conj_tac
      >- (
        qpat_x_assum `option_le call_state.stack_max _` mp_tac
        \\ simp [AC option_add_comm option_add_assoc])
      \\ `space_consumed x (IntOp Div) [Number i1; Number i2] =
          2 * bignum_size (dimindex (:'a) = 64) i1 +
          2 * bignum_size (dimindex (:'a) = 64) i2` by
        simp [space_consumed_def, small_num_small_int, LET_THM]
      \\ `x.refs = s.refs` by (
        imp_res_tac cut_state_opt_SOME_eq
        \\ gvs [])
      \\ `s.limits.arch_64_bit = (dimindex (:'a) = 64)` by fs []
      \\ `s.limits.length_limit = c.len_size` by fs [limits_inv_def]
      \\ strip_tac
      \\ disj1_tac
      \\ qpat_assum `call_result = SOME NotEnoughSpace ==> _`
        (fn th => qpat_assum `call_result = SOME NotEnoughSpace`
          (fn result => assume_tac (CONJUNCT2 (MATCH_MP th result))))
      \\ qpat_x_assum `c.gc_kind <> None /\ no_thunks_in_refs s.refs ==> _` mp_tac
      \\ asm_rewrite_tac []
      \\ decide_tac)
    \\ simp []
    \\ `~(small_int (dimindex (:'a)) i1 /\ 0 <= i1 /\
          small_int (dimindex (:'a)) i2 /\ 0 <= i2 /\
          small_int (dimindex (:'a)) (i1 / i2))`
    by (
      qpat_assum `~(small_int _ i1 /\ small_int _ i2)` mp_tac
      \\ tautLib.TAUT_TAC)
    \\ unabbrev_all_tac
    \\ simp [stack_consumed_def, OPTION_MAP2_NONE, miscTheory.the_def]
    \\ qmatch_goalsub_abbrev_tac `evaluate (MustTerminate _,call_input)`
    \\ `state_rel c l1 l2 s call_input NONE locs` by
      simp [Abbr`call_input`, state_rel_insert_1]
    \\ drule (GEN_ALL eval_Call_Div)
    \\ disch_then (qspecl_then
      [`x`, `SOME retained_names`, `n`, `l`, `i2`, `i1`, `dest`, `right_arg`, `left_arg`]
      mp_tac)
    \\ impl_tac
    >- (
      simp [Abbr`call_input`, get_vars_def]
      \\ fs [get_var_def])
    \\ disch_then (strip_assume_tac o SPEC_ALL)
    \\ qmatch_asmsub_rename_tac `_ = (call_result,call_state)`
    \\ simp [small_num_small_int]
    \\ qpat_x_assum `let max = _ in _`
      (strip_assume_tac o CONV_RULE (DEPTH_CONV let_CONV))
    \\ qpat_x_assum `_ = (call_result,call_state)` mp_tac
    \\ simp []
    \\ disch_then kall_tac
    \\ unabbrev_all_tac
    \\ `x.limits = s.limits` by (
      imp_res_tac cut_state_opt_SOME_eq
      \\ gvs [])
    \\ `x.stack = s.stack /\ x.stack_max = s.stack_max /\
        x.stack_frame_sizes = s.stack_frame_sizes /\ x.locals_size = s.locals_size`
    by (
      imp_res_tac cut_state_opt_SOME_eq
      \\ gvs [])
    \\ qpat_assum `state_rel c l1 l2 s t NONE locs`
      (strip_assume_tac o REWRITE_RULE [state_rel_thm])
    \\ imp_res_tac data_to_word_gcProofTheory.stack_rel_IMP_size_of_stack
    \\ reverse (Cases_on `call_result = SOME NotEnoughSpace`)
    \\ simp []
    >- (
      qpat_x_assum `call_result <> SOME NotEnoughSpace ==> _` mp_tac
      \\ simp [state_rel_thm, dataSemTheory.set_var_def,
               AC option_add_comm option_add_assoc]
      \\ strip_tac
      \\ fs [])
    \\ conj_tac
    >- (
      qpat_x_assum `option_le call_state.stack_max _` mp_tac
      \\ simp [AC option_add_comm option_add_assoc])
    \\ `space_consumed x (IntOp Div) [Number i1; Number i2] =
        2 * bignum_size (dimindex (:'a) = 64) i1 +
        2 * bignum_size (dimindex (:'a) = 64) i2` by
      simp [space_consumed_def, small_num_small_int, LET_THM]
    \\ `x.refs = s.refs` by (
      imp_res_tac cut_state_opt_SOME_eq
      \\ gvs [])
    \\ `s.limits.arch_64_bit = (dimindex (:'a) = 64)` by fs []
    \\ `s.limits.length_limit = c.len_size` by fs [limits_inv_def]
    \\ strip_tac
    \\ disj1_tac
    \\ qpat_assum `call_result = SOME NotEnoughSpace ==> _`
      (fn th => qpat_assum `call_result = SOME NotEnoughSpace`
        (fn result => assume_tac (CONJUNCT2 (MATCH_MP th result))))
    \\ qpat_assum
      `~(small_int _ i1 /\ 0 <= i1 /\ small_int _ i2 /\ 0 <= i2 /\
         small_int _ (i1 / i2))`
      (assume_tac o REWRITE_RULE [DE_MORGAN_THM])
    \\ qpat_x_assum `c.gc_kind <> None /\ no_thunks_in_refs s.refs ==> _` mp_tac
    \\ asm_rewrite_tac []
    \\ decide_tac)
  \\ qmatch_asmsub_rename_tac `cut_state_opt (SOME retained_names) s = SOME x`
  \\ qmatch_asmsub_rename_tac
       `dataSem$get_var left_arg s.locals = SOME (Number i1)`
  \\ qmatch_asmsub_rename_tac
       `dataSem$get_var right_arg s.locals = SOME (Number i2)`
  \\ qmatch_asmsub_rename_tac
       `wordSem$get_var (adjust_var left_arg) t = SOME left_value`
  \\ qmatch_asmsub_rename_tac
       `wordSem$get_var (adjust_var right_arg) t = SOME right_value`
  \\ fs []
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ fs [wordSemTheory.get_var_def]
  \\ `?left_word. left_value = Word left_word /\
        (~(word_bit 0 left_word) <=> small_int (dimindex (:'a)) i1) /\
        (~(word_msb left_word) /\ ~(word_bit 0 left_word) ==> 0 <= i1 /\ left_word = n2w (2 * Num i1))` by
          (metis_tac [state_rel_Number_IMP])
  \\ `?right_word. right_value = Word right_word /\
        (~(word_bit 0 right_word) <=> small_int (dimindex (:'a)) i2) /\
        (~(word_msb right_word) /\ ~(word_bit 0 right_word) ==> 0 <= i2 /\ right_word = n2w (2 * Num i2))` by
          (metis_tac [state_rel_Number_IMP])
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ simp [Once word_exp_ShiftVar_bits] \\ fs [eq_eval]
  \\ simp [word_bit_test_0]
  \\ IF_CASES_TAC
  >- (
    qmatch_goalsub_rename_tac
      `SmallnumDivCall F n (l+1) dest (SOME kept_names) left_arg right_arg`
    \\ fs [word_bit_or,word_bit_lsr_dimindex_1]
    \\ `?num_left. i1 = &num_left` by (Cases_on `i1` \\ fs [])
    \\ `?num_right. i2 = &num_right` by (Cases_on `i2` \\ fs [])
    \\ gvs []
    \\ `small_int (dimindex (:'a)) (&(num_left DIV num_right))` by (
      fs [small_int_def]
      \\ irule LESS_EQ_LESS_TRANS \\ qexists_tac `num_left`
      \\ simp [DIV_LESS_EQ])
    \\ `?retained_locals.
         dataSem$cut_env kept_names s.locals = SOME retained_locals /\
         x = s with locals := retained_locals` by
         gvs [dataSemTheory.cut_state_opt_def,dataSemTheory.cut_state_def,AllCaseEqs()]
    \\ qpat_x_assum `x = s with locals := _` SUBST_ALL_TAC
    \\ qmatch_goalsub_abbrev_tac
         `evaluate (SmallnumDivCall _ _ _ _ _ _ _,call_input)`
    \\ `state_rel c l1 l2 (s with space := 0) call_input NONE locs` by (
      irule state_rel_with_clock_0
      \\ simp [Abbr `call_input`,insert_shadow,state_rel_insert_1])
    \\ `good_dimindex (:'a)` by fs [state_rel_thm]
    \\ mp_tac (Q.INST [`s` |-> `s with space := 0`,`t` |-> `call_input`,
         `is_mod` |-> `F`,`i` |-> `&num_left`,`j` |-> `&num_right`,
         `names` |-> `kept_names`,`v1` |-> `left_arg`,`v2` |-> `right_arg`,
         `secn` |-> `n`,`l` |-> `l+1`,`op` |-> `IntOp Div`,
         `vs` |-> `[Number (&num_left);Number (&num_right)]`]
         SmallnumDivCall_state_rel)
    \\ impl_tac
    >- fs [Abbr `call_input`,wordSemTheory.get_vars_def,wordSemTheory.get_var_def,
         lookup_insert,Smallnum_def,stack_consumed_def,small_num_small_int,allowed_op_def]
    \\ disch_then (qx_choose_then `result_state` strip_assume_tac)
    \\ qexists_tac `NONE` \\ qexists_tac `result_state` \\ simp []
    \\ qpat_x_assum `state_rel _ _ _ _ result_state NONE _` mp_tac
    \\ simp [state_rel_thm,dataSemTheory.set_var_def,dataSemTheory.do_stack_def])
  \\ `get_vars [left_arg;right_arg] s.locals = SOME [Number i1; Number i2]` by fs [get_vars_def]
  \\ `get_vars (MAP adjust_var [left_arg;right_arg]) t = SOME [Word left_word; Word right_word]` by
        fs [wordSemTheory.get_vars_def, wordSemTheory.get_var_def]
  \\ qpat_x_assum `state_rel c l1 l2 s t NONE locs` (fn th => NTAC 2 (mp_tac th))
  \\ strip_tac
  \\ simp_tac std_ss [Once state_rel_thm] \\ strip_tac \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac \\ fs []
  \\ drule state_rel_IMP_arch_64_bit \\ strip_tac
  \\ `~(small_int (dimindex (:'a)) i1 ∧ small_int (dimindex (:'a)) i2 ∧ 0 <= i1 /\ 0 <= i2 /\
        small_int (dimindex (:'a)) (i1 / i2))` by
   (CCONTR_TAC \\ fs []
    \\ `~word_bit 0 left_word` by (
      spose_not_then strip_assume_tac
      \\ imp_res_tac memory_rel_small_int)
    \\ fs []
    \\ drule memory_rel_swap
    \\ strip_tac
    \\ `~word_bit 0 right_word` by (
      spose_not_then strip_assume_tac
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
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,t4)`
  \\ `state_rel c l1 l2 s t4 NONE locs` by
        fs [Abbr`t4`,insert_shadow,state_rel_insert_1]
  \\ drule (GEN_ALL eval_Call_Div)
  \\ disch_then (qspecl_then [`x`,`SOME retained_names`,`n`,`l`,`i2`,`i1`,`dest`,`right_arg`,`left_arg`] mp_tac)
  \\ impl_tac >- (simp [Abbr`t4`] \\ fs [])
  \\ disch_then (strip_assume_tac o SPEC_ALL)
  \\ qmatch_asmsub_rename_tac `_ = (call_result,call_state)`
  \\ simp []
  \\ qpat_x_assum `let max = _ in _` (strip_assume_tac o CONV_RULE (DEPTH_CONV let_CONV))
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ qpat_x_assum `_ = (_,_)` mp_tac
  \\ simp [list_Seq_def] \\ disch_then kall_tac
  \\ unabbrev_all_tac
  \\ `x.limits = s.limits` by (imp_res_tac cut_state_opt_SOME_eq \\ gvs [])
  \\ `x.stack = s.stack /\ x.stack_max = s.stack_max /\
      x.stack_frame_sizes = s.stack_frame_sizes /\ x.locals_size = s.locals_size` by
       (imp_res_tac cut_state_opt_SOME_eq \\ gvs [])
  \\ imp_res_tac data_to_word_gcProofTheory.stack_rel_IMP_size_of_stack
  \\ reverse (Cases_on `call_result = SOME NotEnoughSpace`) \\ simp[]
  >- (
    `~(small_int (dimindex (:α)) i1 ∧ 0 ≤ i1 ∧ small_int (dimindex (:α)) i2 ∧ 0 ≤ i2 ∧
      small_int (dimindex (:α)) (i1 / i2))` by metis_tac []
    \\ asm_simp_tac std_ss []
    \\ first_x_assum drule
    \\ simp [state_rel_thm, dataSemTheory.set_var_def] \\ strip_tac
    \\ qpat_x_assum `option_le call_state.stack_max _` mp_tac
    \\ qpat_x_assum `stack_size t.stack = _` mp_tac
    \\ rpt (qpat_x_assum `t.locals_size = _` mp_tac)
    \\ rpt (qpat_x_assum `t.stack_size = _` mp_tac)
    \\ simp [AC option_add_comm option_add_assoc])
  \\ conj_tac
  >- (
    `~(small_int (dimindex (:α)) i1 ∧ 0 ≤ i1 ∧ small_int (dimindex (:α)) i2 ∧ 0 ≤ i2 ∧
      small_int (dimindex (:α)) (i1 / i2))` by metis_tac []
    \\ asm_simp_tac std_ss []
    \\ qpat_x_assum `option_le call_state.stack_max _` mp_tac
    \\ qpat_x_assum `stack_size t.stack = _` mp_tac
    \\ rpt (qpat_x_assum `t.locals_size = _` mp_tac)
    \\ rpt (qpat_x_assum `t.stack_size = _` mp_tac)
    \\ simp [AC option_add_comm option_add_assoc])
  \\ strip_tac \\ disj1_tac \\ CCONTR_TAC
  \\ `s.limits.arch_64_bit = (dimindex (:'a) = 64)` by fs []
  \\ `s.limits.length_limit = c.len_size` by fs [limits_inv_def]
  \\ `space_consumed x (IntOp Div) [Number i1; Number i2] =
       2 * bignum_size (dimindex (:α) = 64) i1 +
       2 * bignum_size (dimindex (:α) = 64) i2` by
       (`x.limits.arch_64_bit = (dimindex (:'a) = 64)` by fs []
        \\ `~(small_int (dimindex (:α)) i1 ∧ 0 ≤ i1 ∧ small_int (dimindex (:α)) i2 ∧ 0 ≤ i2 ∧
              small_int (dimindex (:α)) (i1 / i2))` by metis_tac []
        \\ asm_simp_tac (srw_ss()) [space_consumed_def, small_num_small_int]
        \\ simp [LET_THM])
  \\ `bignum_size (dimindex (:α) = 64) i1 + bignum_size (dimindex (:α) = 64) i2 <=
        2 ** s.limits.length_limit /\
      size_of_heap_args [Number i1; Number i2] x +
        space_consumed x (IntOp Div) [Number i1; Number i2] <= s.limits.heap_limit` by
       (qpat_x_assum `~(_ \/ _)` mp_tac \\ fs [])
  \\ `bignum_size s.limits.arch_64_bit i1 + bignum_size s.limits.arch_64_bit i2 <=
        2 ** c.len_size` by
       (qpat_x_assum `s.limits.arch_64_bit ⇔ _` (fn th => rewrite_tac [th])
        \\ qpat_x_assum `s.limits.length_limit = c.len_size` (fn th => rewrite_tac [GSYM th])
        \\ first_x_assum ACCEPT_TAC)
  \\ ‘no_thunks_in_refs x.refs’ by fs []
  \\ ‘no_thunks_in_refs s.refs’ by
    (qpat_x_assum ‘cut_state_opt _ _ = _’ mp_tac
    \\ simp [cut_state_opt_def] \\ strip_tac
    \\ imp_res_tac cut_state_refs_same \\ gvs [])
  \\ res_tac
  \\ qpat_x_assum `s.limits.heap_limit < _` mp_tac
  \\ qpat_x_assum `size_of_heap_args _ _ + space_consumed _ _ _ <= _` mp_tac
  \\ qpat_x_assum `space_consumed _ _ _ = _` (fn th => rewrite_tac [th])
  \\ qpat_x_assum `s.limits.arch_64_bit ⇔ _` (fn th => rewrite_tac [th])
  \\ DECIDE_TAC
QED

Theorem assign_Mod:
  op = (IntOp Mod) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ imp_res_tac state_rel_arch_width
  \\ gvs []
  \\ `names_opt <> NONE` by (qpat_x_assum `_ ⇎ _` mp_tac \\ EVAL_TAC)
  \\ Cases_on `names_opt` \\ fs []
  \\ drule_all state_rel_cut_state_opt_SOME \\ strip_tac
  \\ drule state_rel_IMP_arch_64_bit \\ strip_tac
  \\ fs [do_app,oneline do_int_app_def] \\ gvs [AllCaseEqs()]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [get_var_def]
  \\ qmatch_asmsub_rename_tac `get_vars args s.locals = SOME [Number i1; Number i2]`
  \\ fs [assign_def]
  \\ fs [get_vars_SOME_IFF]
  \\ fs [get_vars_SOME_IFF_data]
  \\ gvs [LENGTH_EQ_2]
  \\ fs [get_vars_SOME_IFF, get_vars_SOME_IFF_data]
  \\ Cases_on `c.has_idiv`
  >- (
    simp []
    \\ qmatch_goalsub_rename_tac `SmallDivMod T left_arg right_arg`
    \\ qmatch_asmsub_rename_tac `cut_state_opt (SOME retained_names) s = SOME x`
    \\ fs [wordSemTheory.get_var_def]
    \\ `?left_word. lookup (adjust_var left_arg) t.locals = SOME (Word left_word) /\
         (~word_bit 0 left_word <=> small_int (dimindex (:'a)) i1) /\
         (~word_msb left_word /\ ~word_bit 0 left_word ==>
         0 <= i1 /\ left_word = n2w (2 * Num i1))` by
         metis_tac [state_rel_Number_IMP]
    \\ `?right_word. lookup (adjust_var right_arg) t.locals = SOME (Word right_word) /\
         (~word_bit 0 right_word <=> small_int (dimindex (:'a)) i2) /\
         (~word_msb right_word /\ ~word_bit 0 right_word ==>
          0 <= i2 /\ right_word = n2w (2 * Num i2))`
    by (
      drule_all (Q.INST [`a1` |-> `right_arg`, `i1` |-> `i2`]
                   state_rel_Number_IMP)
      \\ disch_then (qx_choose_then `right_word` strip_assume_tac)
      \\ qexists_tac `right_word`
      \\ simp [])
    \\ gvs []
    \\ once_rewrite_tac [list_Seq_def]
    \\ fs [eq_eval]
    \\ qabbrev_tac `mt = MustTerminate`
    \\ once_rewrite_tac [list_Seq_def]
    \\ fs [eq_eval, wordSemTheory.get_var_imm_def, word_cmp_Test_1, word_bit_or]
    \\ Cases_on `small_int (dimindex (:'a)) i1 /\ small_int (dimindex (:'a)) i2`
    >- (
      fs []
      \\ `left_word = Smallnum i1` by (
        mp_tac (Q.INST [`v` |-> `left_arg`, `i` |-> `i1`,
                        `value` |-> `Word left_word`] state_rel_Number_Smallnum)
        \\ simp [])
      \\ `right_word = Smallnum i2` by (
        mp_tac (Q.INST [`v` |-> `right_arg`, `i` |-> `i2`,
                        `value` |-> `Word right_word`] state_rel_Number_Smallnum)
        \\ simp [])
      \\ gvs []
      \\ `good_dimindex (:'a)` by fs [state_rel_thm]
      \\ `word_msb ((Smallnum i1 : 'a word) || Smallnum i2) =
          (word_msb (Smallnum i1 : 'a word) \/ word_msb (Smallnum i2 : 'a word))` by
        simp [word_msb_def, word_or_def, fcpTheory.FCP_BETA]
      \\ qabbrev_tac `tag_state = t with locals :=
          insert 1 (Word (Smallnum i1 || Smallnum i2)) t.locals`
      \\ `wordSem$get_var 1 tag_state =
          SOME (Word ((Smallnum i1:'a word) || Smallnum i2))` by
        simp [Abbr`tag_state`, wordSemTheory.get_var_def, lookup_insert]
      \\ once_rewrite_tac [list_Seq_def]
      \\ simp [eq_eval]
      \\ qpat_assum `wordSem$get_var 1 tag_state = SOME (Word _)`
        (fn th => once_rewrite_tac [MATCH_MP evaluate_If_Less_0 th])
      \\ simp [small_int_Smallnum_msb, integerTheory.INT_NOT_LT]
      \\ Cases_on `c.has_longdiv /\ 0 <= i1 /\ 0 <= i2`
      >- (
        simp []
        \\ qpat_x_assum `c.has_longdiv /\ 0 <= i1 /\ 0 <= i2` strip_assume_tac
        \\ `?num_left. i1 = &num_left` by (Cases_on `i1` \\ fs [])
        \\ `?num_right. i2 = &num_right` by (Cases_on `i2` \\ fs [])
        \\ gvs []
        \\ `2 * num_left < dimword (:'a) /\ 2 * num_right < dimword (:'a)` by
          fs [small_int_def, GSYM dimword_def, X_LT_DIV]
        \\ `n2w (2 * num_right) <> (0w:'a word)` by fs []
        \\ `2 * num_left DIV (2 * num_right) < dimword (:'a)` by (
          irule LESS_EQ_LESS_TRANS
          \\ qexists_tac `2 * num_left`
          \\ simp [DIV_LESS_EQ])
        \\ `small_int (dimindex (:'a)) (&(num_left MOD num_right))` by (
          mp_tac (Q.INST [`bits` |-> `dimindex (:'a)`,
                          `a` |-> `&num_left`, `b` |-> `&num_right`] small_int_mod)
          \\ simp [])
        \\ `(n2w (2 * num_left MOD (2 * num_right)):'a word) =
            Smallnum (&(num_left MOD num_right))` by
          simp [Smallnum_def, MOD_COMMON_FACTOR]
        \\ unabbrev_all_tac
        \\ simp [list_Seq_def, eq_eval, wordSemTheory.inst_def, Smallnum_def,
                 lookup_insert, adjust_var_11, wordSemTheory.set_vars_def,
                 alist_insert_def, insert_shadow]
        \\ gvs [state_rel_thm, lookup_insert, adjust_var_11,
                 inter_insert_ODD_adjust_set, dataSemTheory.set_var_def]
        \\ conj_tac
        >- (
          rw []
          \\ res_tac
          \\ fs [])
        \\ conj_tac
        >- (
          irule option_le_trans
          \\ qexists_tac `x.stack_max`
          \\ fs [option_le_max_right])
        \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
        \\ match_mp_tac memory_rel_insert \\ fs []
        \\ irule (Q.INST [`i` |-> `&(num_left MOD num_right)`] IMP_memory_rel_Number
                  |> SIMP_RULE (srw_ss()) [Smallnum_def])
        \\ simp []
        \\ imp_res_tac memory_rel_zero_space \\ fs [])
      \\ simp []
      \\ mp_tac (Q.INST [`i` |-> `i1`, `j` |-> `i2`,
                        `v1` |-> `left_arg`, `v2` |-> `right_arg`,
                        `is_mod` |-> `T`, `s` |-> `tag_state`]
                        evaluate_SmallDivMod_results)
      \\ simp [Abbr`tag_state`, wordSemTheory.get_var_def, lookup_insert, adjust_var_11]
      \\ strip_tac
      \\ asm_rewrite_tac []
      \\ simp [list_Seq_def, eq_eval, wordSemTheory.set_vars_def, alist_insert_def,
               lookup_insert, adjust_var_11, insert_shadow]
      \\ `small_int (dimindex (:'a)) (i1 % i2)` by
        (irule small_int_mod \\ simp [])
      \\ qpat_x_assum `~(c.has_longdiv /\ 0 <= i1 /\ 0 <= i2)` kall_tac
      \\ gvs [state_rel_thm, lookup_insert, adjust_var_11,
               inter_insert_ODD_adjust_set, inter_insert_ODD_adjust_set_alt,
               dataSemTheory.set_var_def, COND_RAND]
      \\ simp [COND_RATOR, inter_insert_ODD_adjust_set,
                inter_insert_ODD_adjust_set_alt, lookup_insert, adjust_var_11]
      \\ conj_tac
      >- (
        rw []
        \\ res_tac
        \\ fs [])
      \\ conj_tac
      >- (
        irule option_le_trans
        \\ qexists_tac `x.stack_max`
        \\ fs [option_le_max_right])
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ match_mp_tac IMP_memory_rel_Number \\ fs []
      \\ imp_res_tac memory_rel_zero_space \\ fs [])
    \\ simp []
    \\ once_rewrite_tac [list_Seq_def]
    \\ simp [eq_eval]
    \\ `~(small_int (dimindex (:'a)) i1 /\ 0 <= i1 /\
          small_int (dimindex (:'a)) i2 /\ 0 <= i2 /\
          small_int (dimindex (:'a)) (i1 % i2))`
    by (
      qpat_assum `~(small_int _ i1 /\ small_int _ i2)` mp_tac
      \\ tautLib.TAUT_TAC)
    \\ unabbrev_all_tac
    \\ simp [stack_consumed_def, OPTION_MAP2_NONE, miscTheory.the_def]
    \\ qmatch_goalsub_abbrev_tac `evaluate (MustTerminate _,call_input)`
    \\ `state_rel c l1 l2 s call_input NONE locs` by
      simp [Abbr`call_input`, state_rel_insert_1]
    \\ drule (GEN_ALL eval_Call_Mod)
    \\ disch_then (qspecl_then
      [`x`, `SOME retained_names`, `n`, `l`, `i2`, `i1`, `dest`, `right_arg`, `left_arg`]
      mp_tac)
    \\ impl_tac
    >- (
      simp [Abbr`call_input`, get_vars_def]
      \\ fs [get_var_def])
    \\ disch_then (strip_assume_tac o SPEC_ALL)
    \\ qmatch_asmsub_rename_tac `_ = (call_result,call_state)`
    \\ simp [small_num_small_int]
    \\ qpat_x_assum `let max = _ in _`
      (strip_assume_tac o CONV_RULE (DEPTH_CONV let_CONV))
    \\ qpat_x_assum `_ = (call_result,call_state)` mp_tac
    \\ simp [list_Seq_def, eq_eval]
    \\ disch_then kall_tac
    \\ unabbrev_all_tac
    \\ `x.limits = s.limits` by (
      imp_res_tac cut_state_opt_SOME_eq
      \\ gvs [])
    \\ `x.stack = s.stack /\ x.stack_max = s.stack_max /\
        x.stack_frame_sizes = s.stack_frame_sizes /\ x.locals_size = s.locals_size`
    by (
      imp_res_tac cut_state_opt_SOME_eq
      \\ gvs [])
    \\ qpat_assum `state_rel c l1 l2 s t NONE locs`
      (strip_assume_tac o REWRITE_RULE [state_rel_thm])
    \\ imp_res_tac data_to_word_gcProofTheory.stack_rel_IMP_size_of_stack
    \\ reverse (Cases_on `call_result = SOME NotEnoughSpace`)
    \\ simp []
    >- (
      qpat_x_assum `call_result <> SOME NotEnoughSpace ==> _` mp_tac
      \\ simp [state_rel_thm, dataSemTheory.set_var_def,
               AC option_add_comm option_add_assoc]
      \\ strip_tac
      \\ fs [])
    \\ conj_tac
    >- (
      qpat_x_assum `option_le call_state.stack_max _` mp_tac
      \\ simp [AC option_add_comm option_add_assoc])
    \\ `space_consumed x (IntOp Mod) [Number i1; Number i2] =
        2 * bignum_size (dimindex (:'a) = 64) i1 +
        2 * bignum_size (dimindex (:'a) = 64) i2` by
      simp [space_consumed_def, small_num_small_int, LET_THM]
    \\ `x.refs = s.refs` by (
      imp_res_tac cut_state_opt_SOME_eq
      \\ gvs [])
    \\ `s.limits.arch_64_bit = (dimindex (:'a) = 64)` by fs []
    \\ `s.limits.length_limit = c.len_size` by fs [limits_inv_def]
    \\ strip_tac
    \\ disj1_tac
    \\ qpat_assum `call_result = SOME NotEnoughSpace ==> _`
      (fn th => qpat_assum `call_result = SOME NotEnoughSpace`
        (fn result => assume_tac (CONJUNCT2 (MATCH_MP th result))))
    \\ qpat_assum
      `~(small_int _ i1 /\ 0 <= i1 /\ small_int _ i2 /\ 0 <= i2 /\
         small_int _ (i1 % i2))`
      (assume_tac o REWRITE_RULE [DE_MORGAN_THM])
    \\ qpat_x_assum `c.gc_kind <> None /\ no_thunks_in_refs s.refs ==> _` mp_tac
    \\ asm_rewrite_tac []
    \\ decide_tac)
  \\ qmatch_asmsub_rename_tac `cut_state_opt (SOME retained_names) s = SOME x`
  \\ qmatch_asmsub_rename_tac
       `dataSem$get_var left_arg s.locals = SOME (Number i1)`
  \\ qmatch_asmsub_rename_tac
       `dataSem$get_var right_arg s.locals = SOME (Number i2)`
  \\ qmatch_asmsub_rename_tac
       `wordSem$get_var (adjust_var left_arg) t = SOME left_value`
  \\ qmatch_asmsub_rename_tac
       `wordSem$get_var (adjust_var right_arg) t = SOME right_value`
  \\ fs []
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ fs [wordSemTheory.get_var_def]
  \\ `?left_word. left_value = Word left_word /\
        (~(word_bit 0 left_word) <=> small_int (dimindex (:'a)) i1) /\
        (~(word_msb left_word) /\ ~(word_bit 0 left_word) ==> 0 <= i1 /\ left_word = n2w (2 * Num i1))` by
          (metis_tac [state_rel_Number_IMP])
  \\ `?right_word. right_value = Word right_word /\
        (~(word_bit 0 right_word) <=> small_int (dimindex (:'a)) i2) /\
        (~(word_msb right_word) /\ ~(word_bit 0 right_word) ==> 0 <= i2 /\ right_word = n2w (2 * Num i2))` by
          (metis_tac [state_rel_Number_IMP])
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ fs [eq_eval]
  \\ simp [Once word_exp_ShiftVar_bits] \\ fs [eq_eval]
  \\ simp [word_bit_test_0]
  \\ IF_CASES_TAC
  >- (
    qmatch_goalsub_rename_tac
      `SmallnumDivCall T n (l+1) dest (SOME kept_names) left_arg right_arg`
    \\ fs [word_bit_or,word_bit_lsr_dimindex_1]
    \\ `?num_left. i1 = &num_left` by (Cases_on `i1` \\ fs [])
    \\ `?num_right. i2 = &num_right` by (Cases_on `i2` \\ fs [])
    \\ gvs []
    \\ `small_int (dimindex (:'a)) (&(num_left MOD num_right))` by (
      fs [small_int_def]
      \\ irule LESS_EQ_LESS_TRANS \\ qexists_tac `num_left`
      \\ simp [MOD_LESS_EQ])
    \\ `?retained_locals.
         dataSem$cut_env kept_names s.locals = SOME retained_locals /\
         x = s with locals := retained_locals` by
         gvs [dataSemTheory.cut_state_opt_def,dataSemTheory.cut_state_def,AllCaseEqs()]
    \\ qpat_x_assum `x = s with locals := _` SUBST_ALL_TAC
    \\ qmatch_goalsub_abbrev_tac
         `evaluate (SmallnumDivCall _ _ _ _ _ _ _,call_input)`
    \\ `state_rel c l1 l2 (s with space := 0) call_input NONE locs` by (
      irule state_rel_with_clock_0
      \\ simp [Abbr `call_input`,insert_shadow,state_rel_insert_1])
    \\ `good_dimindex (:'a)` by fs [state_rel_thm]
    \\ mp_tac (Q.INST [`s` |-> `s with space := 0`,`t` |-> `call_input`,
         `is_mod` |-> `T`,`i` |-> `&num_left`,`j` |-> `&num_right`,
         `names` |-> `kept_names`,`v1` |-> `left_arg`,`v2` |-> `right_arg`,
         `secn` |-> `n`,`l` |-> `l+1`,`op` |-> `IntOp Mod`,
         `vs` |-> `[Number (&num_left);Number (&num_right)]`]
         SmallnumDivCall_state_rel)
    \\ impl_tac
    >- fs [Abbr `call_input`,wordSemTheory.get_vars_def,wordSemTheory.get_var_def,
         lookup_insert,Smallnum_def,stack_consumed_def,small_num_small_int,allowed_op_def]
    \\ disch_then (qx_choose_then `result_state` strip_assume_tac)
    \\ qexists_tac `NONE` \\ qexists_tac `result_state` \\ simp []
    \\ qpat_x_assum `state_rel _ _ _ _ result_state NONE _` mp_tac
    \\ simp [state_rel_thm,dataSemTheory.set_var_def,dataSemTheory.do_stack_def])
  \\ `get_vars [left_arg;right_arg] s.locals = SOME [Number i1; Number i2]` by fs [get_vars_def]
  \\ `get_vars (MAP adjust_var [left_arg;right_arg]) t = SOME [Word left_word; Word right_word]` by
        fs [wordSemTheory.get_vars_def, wordSemTheory.get_var_def]
  \\ qpat_x_assum `state_rel c l1 l2 s t NONE locs` (fn th => NTAC 2 (mp_tac th))
  \\ strip_tac
  \\ simp_tac std_ss [Once state_rel_thm] \\ strip_tac \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac \\ fs []
  \\ drule state_rel_IMP_arch_64_bit \\ strip_tac
  \\ `~(small_int (dimindex (:'a)) i1 ∧ small_int (dimindex (:'a)) i2 ∧ 0 <= i1 /\ 0 <= i2 /\
        small_int (dimindex (:'a)) (i1 % i2))` by
   (CCONTR_TAC \\ fs []
    \\ `~word_bit 0 left_word` by (
      spose_not_then strip_assume_tac
      \\ imp_res_tac memory_rel_small_int)
    \\ fs []
    \\ drule memory_rel_swap
    \\ strip_tac
    \\ `~word_bit 0 right_word` by (
      spose_not_then strip_assume_tac
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
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,t4)`
  \\ `state_rel c l1 l2 s t4 NONE locs` by
        fs [Abbr`t4`,insert_shadow,state_rel_insert_1]
  \\ drule (GEN_ALL eval_Call_Mod)
  \\ disch_then (qspecl_then [`x`,`SOME retained_names`,`n`,`l`,`i2`,`i1`,`dest`,`right_arg`,`left_arg`] mp_tac)
  \\ impl_tac >- (simp [Abbr`t4`] \\ fs [])
  \\ disch_then (strip_assume_tac o SPEC_ALL)
  \\ qmatch_asmsub_rename_tac `_ = (call_result,call_state)`
  \\ simp []
  \\ qpat_x_assum `let max = _ in _` (strip_assume_tac o CONV_RULE (DEPTH_CONV let_CONV))
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ qpat_x_assum `_ = (_,_)` mp_tac
  \\ simp [list_Seq_def] \\ disch_then kall_tac
  \\ unabbrev_all_tac
  \\ `x.limits = s.limits` by (imp_res_tac cut_state_opt_SOME_eq \\ gvs [])
  \\ `x.stack = s.stack /\ x.stack_max = s.stack_max /\
      x.stack_frame_sizes = s.stack_frame_sizes /\ x.locals_size = s.locals_size` by
       (imp_res_tac cut_state_opt_SOME_eq \\ gvs [])
  \\ imp_res_tac data_to_word_gcProofTheory.stack_rel_IMP_size_of_stack
  \\ reverse (Cases_on `call_result = SOME NotEnoughSpace`) \\ simp[]
  >- (
    `~(small_int (dimindex (:α)) i1 ∧ 0 ≤ i1 ∧ small_int (dimindex (:α)) i2 ∧ 0 ≤ i2 ∧
      small_int (dimindex (:α)) (i1 % i2))` by metis_tac []
    \\ asm_simp_tac std_ss []
    \\ first_x_assum drule
    \\ simp [state_rel_thm, dataSemTheory.set_var_def] \\ strip_tac
    \\ qpat_x_assum `option_le call_state.stack_max _` mp_tac
    \\ qpat_x_assum `stack_size t.stack = _` mp_tac
    \\ rpt (qpat_x_assum `t.locals_size = _` mp_tac)
    \\ rpt (qpat_x_assum `t.stack_size = _` mp_tac)
    \\ simp [AC option_add_comm option_add_assoc])
  \\ conj_tac
  >- (
    `~(small_int (dimindex (:α)) i1 ∧ 0 ≤ i1 ∧ small_int (dimindex (:α)) i2 ∧ 0 ≤ i2 ∧
      small_int (dimindex (:α)) (i1 % i2))` by metis_tac []
    \\ asm_simp_tac std_ss []
    \\ qpat_x_assum `option_le call_state.stack_max _` mp_tac
    \\ qpat_x_assum `stack_size t.stack = _` mp_tac
    \\ rpt (qpat_x_assum `t.locals_size = _` mp_tac)
    \\ rpt (qpat_x_assum `t.stack_size = _` mp_tac)
    \\ simp [AC option_add_comm option_add_assoc])
  \\ strip_tac \\ disj1_tac \\ CCONTR_TAC
  \\ `s.limits.arch_64_bit = (dimindex (:'a) = 64)` by fs []
  \\ `s.limits.length_limit = c.len_size` by fs [limits_inv_def]
  \\ `space_consumed x (IntOp Mod) [Number i1; Number i2] =
       2 * bignum_size (dimindex (:α) = 64) i1 +
       2 * bignum_size (dimindex (:α) = 64) i2` by
       (`x.limits.arch_64_bit = (dimindex (:'a) = 64)` by fs []
        \\ `~(small_int (dimindex (:α)) i1 ∧ 0 ≤ i1 ∧ small_int (dimindex (:α)) i2 ∧ 0 ≤ i2 ∧
              small_int (dimindex (:α)) (i1 % i2))` by metis_tac []
        \\ asm_simp_tac (srw_ss()) [space_consumed_def, small_num_small_int]
        \\ simp [LET_THM])
  \\ `bignum_size (dimindex (:α) = 64) i1 + bignum_size (dimindex (:α) = 64) i2 <=
        2 ** s.limits.length_limit /\
      size_of_heap_args [Number i1; Number i2] x +
        space_consumed x (IntOp Mod) [Number i1; Number i2] <= s.limits.heap_limit` by
       (qpat_x_assum `~(_ \/ _)` mp_tac \\ fs [])
  \\ `bignum_size s.limits.arch_64_bit i1 + bignum_size s.limits.arch_64_bit i2 <=
        2 ** c.len_size` by
       (qpat_x_assum `s.limits.arch_64_bit ⇔ _` (fn th => rewrite_tac [th])
        \\ qpat_x_assum `s.limits.length_limit = c.len_size` (fn th => rewrite_tac [GSYM th])
        \\ first_x_assum ACCEPT_TAC)
  \\ ‘no_thunks_in_refs x.refs’ by fs []
  \\ ‘no_thunks_in_refs s.refs’ by
    (qpat_x_assum ‘cut_state_opt _ _ = _’ mp_tac
    \\ simp [cut_state_opt_def] \\ strip_tac
    \\ imp_res_tac cut_state_refs_same \\ gvs [])
  \\ res_tac
  \\ qpat_x_assum `s.limits.heap_limit < _` mp_tac
  \\ qpat_x_assum `size_of_heap_args _ _ + space_consumed _ _ _ <= _` mp_tac
  \\ qpat_x_assum `space_consumed _ _ _ = _` (fn th => rewrite_tac [th])
  \\ qpat_x_assum `s.limits.arch_64_bit ⇔ _` (fn th => rewrite_tac [th])
  \\ DECIDE_TAC
QED

Theorem assign_LessConstSmall:
   assign c secn l dest (IntOp (LessConstSmall i)) args names =
      case args of
      | [v1] => (If Less (adjust_var v1) (Imm (&(2 * i)))
                  (Assign (adjust_var dest) TRUE_CONST)
                  (Assign (adjust_var dest) FALSE_CONST),l)
      | _ => (Skip:wordLang$prog,l)
Proof
  fs [assign_def] \\ every_case_tac \\ fs []
QED

Theorem assign_LessSmallConst[allow_rebind]:
  (∃i. op = IntOp (LessConstSmall i)) ==> ^assign_thm_goal
Proof
  rpt strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ gvs [do_app,AllCaseEqs(),allowed_op_def,oneline do_int_app_def]
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
  \\ `?k. i' = &k` by (Cases_on `i'` \\ fs [] \\ NO_TAC) \\ rveq \\ fs []
  \\ `small_int (dimindex (:'a)) (&k)` by
       (fs [small_int_def,good_dimindex_def,dimword_def] \\ NO_TAC)
  \\ imp_res_tac memory_rel_Number_IMP \\ fs [] \\ rveq \\ fs []
  \\ fs [assign_LessConstSmall]
  \\ fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF]
  \\ fs [eq_eval,WORD_LO_word_0,adjust_var_11]
  \\ fs [Smallnum_def]
  \\ `n2w (2 * k) < (n2w (2 * i):'a word) <=> k < i` by
    (fs [word_lt_n2w,bitTheory.BIT_def,bitTheory.BITS_THM]
     \\ fs [good_dimindex_def,LESS_DIV_EQ_ZERO,dimword_def] \\ NO_TAC)
  \\ fs []
  \\ qpat_abbrev_tac `bool_res <=> k < i`
  \\ Cases_on `bool_res`
  \\ fs [state_rel_thm] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
  \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
  \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [])
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
    (?md. lookup Compare1_location t.code = SOME (4,Compare1_code c,md)) /\
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
  rw [] \\ imp_res_tac memory_rel_arch_width \\ drule0 memory_rel_Number_cmp
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
  \\ `shift (dimindex (:'a)) <> 0 /\ shift (dimindex (:'a)) < dimindex (:'a)` by
    (fs [good_dimindex_def,shift_def])
  \\ ‘(dimindex (:α) − c.len_size) MOD dimword (:α) = (dimindex (:α) − c.len_size)
      ∧ (shift (dimindex (:α)) MOD dimword (:α)) = shift (dimindex (:α))
      ∧ (dimindex (:α) − c.len_size) < dimindex (:α)’
    by fs [good_dimindex_def, dimword_def, shift_def]
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
    \\ qpat_abbrev_tac `t1 = (_:('a,'c,'ffi) wordSem$state) with locals := _`
    \\ drule0 Compare1_code_thm
    \\ fs [GSYM decode_length_def]
    \\ disch_then (qspecl_then [`c`,`t1`] mp_tac)
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

Theorem assign_Less:
  op = IntOp Less ==> ^assign_thm_goal
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
  \\ rpt_drule0 memory_rel_Number_cmp
  \\ strip_tac \\ fs [] \\ rveq
  \\ fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF]
  \\ fs [wordSemTheory.get_var_def]
  \\ fs [assign_def,arg2_def,assign_Less_def,list_Seq_def] \\ eval_tac
  \\ fs [lookup_insert,wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def,
         word_cmp_Test_1,word_bit_or]
  \\ IF_CASES_TAC THEN1
   (fs [lookup_insert,state_rel_thm]
    \\ fs [wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def]
    \\ IF_CASES_TAC \\ fs [lookup_insert,inter_insert_ODD_adjust_set]
    \\ (conj_tac >- (fs [lookup_insert,adjust_var_11] \\ rw []))
    \\ (conj_tac >- rfs[option_le_max_right])
    \\ (conj_tac >- rfs[option_le_max_right])
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
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
  \\ `(?md. lookup Compare_location t.code = SOME (3,Compare_code c,md))` by
       fs [state_rel_def,code_rel_def,stubs_md_def,stubs_def,MAP_MAP_o,o_DEF]
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
  \\ fs [lookup_insert]
  \\ rw [] \\ fs []
  \\ unabbrev_all_tac
  \\ fs [wordSemTheory.pop_env_def,wordSemTheory.call_env_def,
         wordSemTheory.push_env_def,wordSemTheory.dec_clock_def]
  \\ pairarg_tac \\ fs [] \\ rveq \\ fs []
  \\ fs[CaseEq "bool",CaseEq"prod",CaseEq"option",CaseEq"list",CaseEq"stack_frame",
        FST_EQ_EQUIV,ELIM_UNCURRY] >> rveq >> fs[lookup_insert]
  \\ rfs[wordSemTheory.set_vars_def,alist_insert_def]
  \\ simp [word_cmp_Less_word_cmp_res]
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
  \\ qpat_x_assum ‘state_rel c l1 l2 x t NONE locs’ $ ASSUME_NAMED_TAC "state_rel_t"
  \\ LABEL_X_ASSUM "with_locals" assume_tac
  \\ gvs [state_rel_thm]
  \\ qmatch_goalsub_abbrev_tac ‘Boolv (n1 < n2)’
  \\ Cases_on ‘n1 < n2’ \\ gvs [lookup_insert, inter_insert_ODD_adjust_set]
  \\ ( (* two subgoals *)
    conj_tac >- rw []
    \\ conj_tac >-
        (rfs[option_le_max_right,option_le_max,stack_size_eq2,wordSemTheory.stack_size_frame_def,
             AC option_add_comm option_add_assoc])
    \\ conj_tac >-
        (match_mp_tac option_le_trans \\ goal_assum drule \\
         rpt(qpat_x_assum `option_le _.stack_max _.stack_max` mp_tac) \\
         simp[] \\
         imp_res_tac stack_rel_IMP_size_of_stack \\
         rpt (qpat_x_assum `stack_size _ = size_of_stack _` mp_tac) \\
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
    \\ rpt (match_mp_tac memory_rel_Boolv_T)
    \\ rpt (match_mp_tac memory_rel_Boolv_F) \\ fs [])
QED

Theorem assign_LessEq:
  op = IntOp LessEq ==> ^assign_thm_goal
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
  \\ rpt_drule0 memory_rel_Number_cmp
  \\ strip_tac \\ fs [] \\ rveq
  \\ fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF]
  \\ fs [wordSemTheory.get_var_def]
  \\ fs [assign_def,arg2_def,assign_LessEq_def,list_Seq_def] \\ eval_tac
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
  \\ `(?md. lookup Compare_location t.code = SOME (3,Compare_code c,md))` by
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
  \\ fs [lookup_insert]
  \\ rw [] \\ fs []
  \\ unabbrev_all_tac
  \\ fs [wordSemTheory.pop_env_def,wordSemTheory.call_env_def,
         wordSemTheory.push_env_def,wordSemTheory.dec_clock_def]
  \\ pairarg_tac \\ fs [] \\ rveq \\ fs []
  \\ fs[CaseEq "bool",CaseEq"prod",CaseEq"option",CaseEq"list",CaseEq"stack_frame",
        FST_EQ_EQUIV,ELIM_UNCURRY] >> rveq >> fs[lookup_insert]
  \\ rfs[wordSemTheory.set_vars_def,alist_insert_def]
  \\ simp [word_cmp_NotLess_word_cmp_res]
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
  \\ qpat_x_assum ‘state_rel c l1 l2 x t NONE locs’ $ ASSUME_NAMED_TAC "state_rel_t"
  \\ LABEL_X_ASSUM "with_locals" assume_tac
  \\ gvs [state_rel_thm]
  \\ qmatch_goalsub_abbrev_tac ‘Boolv (n1 ≤ n2)’
  \\ Cases_on ‘n1 ≤ n2’ \\ gvs [lookup_insert, inter_insert_ODD_adjust_set]
  \\ (
    conj_tac >- rw []
    \\ conj_tac >-
        (rfs[option_le_max_right,option_le_max,stack_size_eq2,wordSemTheory.stack_size_frame_def,
             AC option_add_comm option_add_assoc])
    \\ conj_tac >-
        (match_mp_tac option_le_trans \\ goal_assum drule \\
         rpt(qpat_x_assum `option_le _.stack_max _.stack_max` mp_tac) \\
         simp[] \\
         imp_res_tac stack_rel_IMP_size_of_stack \\
         rpt (qpat_x_assum `stack_size _ = size_of_stack _` mp_tac) \\
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
    \\ rpt (match_mp_tac memory_rel_Boolv_T)
    \\ rpt (match_mp_tac memory_rel_Boolv_F) \\ fs [])
QED

val _ = augment_srw_ss [rewrites [compiler_Smallnum_i2w]];

Theorem assign_Const:
  (∃i. op = IntOp (Const i)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ imp_res_tac state_rel_arch_width
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ gvs [do_app,AllCaseEqs(),allowed_op_def]
  \\ Cases_on ‘i’
  \\ fs [assign_def,eq_eval,wordSemTheory.get_store_def]
  \\ fs [state_rel_def,wordSemTheory.set_var_def,set_var_def,
        lookup_insert,adjust_var_11,oneline do_int_app_def,AllCaseEqs()]
  \\ rw [] \\ fs []
  \\ fs[option_le_max_right]
  \\ asm_exists_tac \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac word_ml_inv_insert \\ fs []
  \\ TRY (match_mp_tac word_ml_inv_zero) \\ fs []
  \\ TRY (match_mp_tac word_ml_inv_num) \\ fs []
  \\ PURE_REWRITE_TAC [integerTheory.INT_MUL_RNEG,GSYM integerTheory.INT_MUL]
  \\ fs []
  \\ TRY (match_mp_tac word_ml_inv_neg_num) \\ fs []
QED

Theorem join_lemma[local] =
  METIS_PROVE [] “(b1 ⇒ x) ∧ (b2 ⇒ x) ⇒ (b1 ∨ b2 ⇒ x)”;

Theorem imp_assign[local] =
  DB.match ["-"] “_ ==> ^assign_thm_goal” |> map (#1 o #2)
  |> end_itlist (fn x => fn y => MATCH_MP join_lemma (CONJ x y));

Theorem assign_IntOp:
  (∃i. op = IntOp i) ⇒ ^assign_thm_goal
Proof
  strip_tac \\ strip_tac
  \\ Cases_on `op = IntOp Greater`
  >- (fs [do_app] \\ every_case_tac \\ fs [])
  \\ Cases_on `op = IntOp GreaterEq`
  >- (fs [do_app] \\ every_case_tac \\ fs [])
  \\ irule imp_assign
  \\ asm_rewrite_tac []
  \\ rpt $ first_assum $ irule_at Any
  \\ gvs [] \\ Cases_on ‘i’ \\ gvs []
QED

