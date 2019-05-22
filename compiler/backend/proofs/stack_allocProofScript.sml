(*
  Correctness proof for stack_alloc
*)

open preamble stack_allocTheory
     stackLangTheory stackSemTheory stackPropsTheory
     word_gcFunctionsTheory
local open blastLib wordSemTheory in end

val _ = new_theory"stack_allocProof";
val _ = (max_print_depth := 18);

val word_shift_def = backend_commonTheory.word_shift_def
val theWord_def = wordSemTheory.theWord_def;
val isWord_def = wordSemTheory.isWord_def;
val is_fwd_ptr_def = wordSemTheory.is_fwd_ptr_def;

val _ = set_grammar_ancestry["stack_alloc", "stackLang", "stackSem", "stackProps",
  "word_gcFunctions" (* for memcpy *)
];
val _ = temp_overload_on("good_dimindex", ``labProps$good_dimindex``);
val _ = temp_bring_to_front_overload"compile"{Thy="stack_alloc",Name="compile"};

(* TODO: move and join with stack_remove *)

Theorem lsl_lsr:
   w2n ((n:'a word)) * 2 ** a < dimword (:'a) ⇒ n << a >>> a = n
Proof
  Cases_on`n` \\ simp[]
  \\ qmatch_assum_rename_tac`n < dimword _`
  \\ srw_tac[][]
  \\ REWRITE_TAC[GSYM wordsTheory.w2n_11]
  \\ REWRITE_TAC[wordsTheory.w2n_lsr]
  \\ simp[]
  \\ simp[word_lsl_n2w]
  \\ srw_tac[][]
  >- (
    simp[ZERO_DIV]
    \\ Cases_on`n`
    \\ full_simp_tac(srw_ss())[dimword_def]
    \\ full_simp_tac(srw_ss())[bitTheory.LT_TWOEXP]
    \\ full_simp_tac(srw_ss())[bitTheory.LOG2_def]
    \\ qmatch_asmsub_rename_tac`SUC n * 2 ** a`
    \\ qspecl_then[`a`,`2`,`SUC n`]mp_tac logrootTheory.LOG_EXP
    \\ simp[] )
  \\ simp[MULT_DIV]
QED

Theorem bytes_in_word_word_shift:
   good_dimindex(:'a) ∧ w2n (bytes_in_word:'a word) * w2n n < dimword(:'a) ⇒
   (bytes_in_word:'a word * n) >>> word_shift (:'a) = n
Proof
  EVAL_TAC \\ srw_tac[][] \\ pop_assum mp_tac
  \\ blastLib.BBLAST_TAC \\ simp[]
  \\ blastLib.BBLAST_TAC \\ srw_tac[][]
  \\ match_mp_tac lsl_lsr
  \\ simp[]
  \\ Cases_on`n`\\full_simp_tac(srw_ss())[word_lsl_n2w]
  \\ full_simp_tac(srw_ss())[dimword_def]
QED

(* ---- *)

val get_var_imm_case = Q.prove(
  `get_var_imm ri s =
    case ri of
    | Reg n => get_var n s
    | Imm w => SOME (Word w)`,
  Cases_on `ri` \\ full_simp_tac(srw_ss())[get_var_imm_def]);

val prog_comp_lemma = Q.prove(
  `prog_comp = \(n,p). (n,FST (comp n (next_lab p 1) p))`,
  full_simp_tac(srw_ss())[FUN_EQ_THM,FORALL_PROD,prog_comp_def]);

Theorem FST_prog_comp[simp]:
   FST (prog_comp pp) = FST pp
Proof
  Cases_on`pp` \\ EVAL_TAC
QED

val lookup_IMP_lookup_compile = Q.prove(
  `lookup dest s.code = SOME x /\ dest ≠ gc_stub_location ==>
    ?m1 n1. lookup dest (fromAList (compile c (toAList s.code))) =
            SOME (FST (comp m1 n1 x))`,
  full_simp_tac(srw_ss())[lookup_fromAList,compile_def] \\ srw_tac[][ALOOKUP_APPEND]
  \\ `ALOOKUP (stubs c) dest = NONE` by
    (full_simp_tac(srw_ss())[stubs_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ decide_tac) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[prog_comp_lemma] \\ full_simp_tac(srw_ss())[ALOOKUP_MAP_2,ALOOKUP_toAList]
  \\ metis_tac []);

val map_bitmap_APPEND = Q.prove(
  `!x q stack p0 p1.
      filter_bitmap x stack = SOME (p0,p1) /\
      LENGTH q = LENGTH p0 ==>
      map_bitmap x (q ++ q') stack =
      case map_bitmap x q stack of
      | NONE => NONE
      | SOME (hd,ts,ws) => SOME (hd,ts++q',ws)`,
  Induct \\ full_simp_tac(srw_ss())[map_bitmap_def]
  \\ reverse (Cases \\ Cases_on `stack`)
  \\ full_simp_tac(srw_ss())[map_bitmap_def,filter_bitmap_def]
  THEN1 (srw_tac[][] \\ rpt (CASE_TAC \\ full_simp_tac(srw_ss())[]))
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ Cases \\ full_simp_tac(srw_ss())[map_bitmap_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]);

Theorem filter_bitmap_map_bitmap:
   !x t q xs xs1 z ys ys1.
      filter_bitmap x t = SOME (xs,xs1) /\
      LENGTH q = LENGTH xs /\
      map_bitmap x q t = SOME (ys,z,ys1) ==>
      z = [] /\ ys1 = xs1
Proof
  Induct
  THEN1 ( fs[filter_bitmap_def,map_bitmap_def] )
  \\ Cases_on `t` \\ Cases_on `q` \\ Cases
  \\ rewrite_tac [filter_bitmap_def] \\ simp_tac std_ss [map_bitmap_def]
  THEN1
   (Cases_on `xs` \\ simp_tac std_ss [map_bitmap_def,LENGTH,ADD1]
    \\ CASE_TAC \\ rename1 `_ = SOME y` \\ PairCases_on `y`
    \\ simp_tac (srw_ss()) [map_bitmap_def,LENGTH,ADD1]
    \\ ntac 2 strip_tac \\ first_x_assum drule
    \\ disch_then (qspec_then `[]` mp_tac) \\ full_simp_tac(srw_ss())[])
  THEN1
   (CASE_TAC \\ rename1 `_ = SOME y` \\ PairCases_on `y`
    \\ simp_tac (srw_ss()) [map_bitmap_def,LENGTH,ADD1]
    \\ CASE_TAC \\ rename1 `_ = SOME y` \\ PairCases_on `y`
    \\ simp_tac (srw_ss()) [map_bitmap_def,LENGTH,ADD1]
    \\ metis_tac [])
  \\ CASE_TAC \\ rename1 `_ = SOME y` \\ PairCases_on `y`
  \\ simp_tac (srw_ss()) []
  \\ rpt gen_tac \\ strip_tac
  \\ first_x_assum match_mp_tac
  \\ qexists_tac `t'` \\ full_simp_tac(srw_ss())[]
  \\ qexists_tac `h'::t` \\ full_simp_tac(srw_ss())[]
QED

val get_bits_def = Define `
  get_bits w = GENLIST (\i. w ' i) (bit_length w − 1)`

Theorem bit_length_thm:
   !w. ((w >>> bit_length w) = 0w) /\ !n. n < bit_length w ==> (w >>> n) <> 0w
Proof
  HO_MATCH_MP_TAC bit_length_ind \\ srw_tac[][]
  \\ once_rewrite_tac [bit_length_def]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
  \\ Cases_on `w = 0w` \\ full_simp_tac(srw_ss())[EVAL ``bit_length 0w``]
  \\ Cases_on `n` \\ full_simp_tac(srw_ss())[]
  \\ ntac 2 (pop_assum mp_tac)
  \\ once_rewrite_tac [bit_length_def]
  \\ full_simp_tac(srw_ss())[ADD1] \\ srw_tac[][]
QED

val word_lsr_dimindex = Q.prove(
  `(w:'a word) >>> dimindex (:'a) = 0w`,
  full_simp_tac(srw_ss())[]);

Theorem bit_length_LESS_EQ_dimindex:
   bit_length (w:'a word) <= dimindex (:'a)
Proof
  CCONTR_TAC \\ full_simp_tac(srw_ss())[GSYM NOT_LESS]
  \\ imp_res_tac bit_length_thm
  \\ full_simp_tac(srw_ss())[word_lsr_dimindex]
QED

Theorem shift_to_zero_word_msb:
   (w:'a word) >>> n = 0w /\ word_msb w ==> dimindex (:'a) <= n
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss] []
  \\ CCONTR_TAC
  \\ qpat_x_assum `!xx.bb` mp_tac
  \\ fs [GSYM NOT_LESS]
  \\ qexists_tac `dimindex (:α) - 1 - n`
  \\ simp []
QED

val word_msb_IMP_bit_length = Q.prove(
  `!h. word_msb (h:'a word) ==> (bit_length h = dimindex (:'a))`,
  srw_tac[][] \\ imp_res_tac shift_to_zero_word_msb \\ CCONTR_TAC
  \\ imp_res_tac (DECIDE ``n<>m ==> n < m \/ m < n:num``)
  \\ qspec_then `h` mp_tac bit_length_thm
  \\ strip_tac \\ res_tac \\ full_simp_tac(srw_ss())[word_lsr_dimindex]
  \\ decide_tac);

val get_bits_intro = Q.prove(
  `word_msb (h:'a word) ==>
    GENLIST (\i. h ' i) (dimindex (:'a) - 1) = get_bits h`,
  full_simp_tac(srw_ss())[get_bits_def,word_msb_IMP_bit_length]);

val filter_bitmap_APPEND = Q.prove(
  `!xs stack ys.
      filter_bitmap (xs ++ ys) stack =
      case filter_bitmap xs stack of
      | NONE => NONE
      | SOME (zs,rs) =>
        case filter_bitmap ys rs of
        | NONE => NONE
        | SOME (zs2,rs) => SOME (zs ++ zs2,rs)`,
  Induct \\ Cases_on `stack` \\ full_simp_tac(srw_ss())[filter_bitmap_def]
  THEN1 (srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  THEN1 (srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ Cases \\ full_simp_tac(srw_ss())[filter_bitmap_def] \\ srw_tac[][]
  \\ rpt (CASE_TAC \\ full_simp_tac(srw_ss())[]));

Theorem bit_length_minus_1:
   w <> 0w ==> bit_length w − 1 = bit_length (w >>> 1)
Proof
  simp [Once bit_length_def]
QED

Theorem bit_length_eq_1:
   bit_length w = 1 <=> w = 1w
Proof
  Cases_on `w = 1w` \\ full_simp_tac(srw_ss())[] THEN1 (EVAL_TAC \\ full_simp_tac(srw_ss())[])
  \\ once_rewrite_tac [bit_length_def] \\ srw_tac[][]
  \\ once_rewrite_tac [bit_length_def] \\ srw_tac[][]
  \\ pop_assum mp_tac
  \\ simp_tac std_ss [GSYM w2n_11,w2n_lsr]
  \\ Cases_on `w` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `n` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `n'` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[DIV_EQ_X] \\ decide_tac
QED

Theorem word_and_one_eq_0_iff:
   !w. ((w && 1w) = 0w) <=> ~(w ' 0)
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss] [wordsTheory.word_index]
QED

val split_num_forall_to_10 = Q.prove(
  `($! P) <=> P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5 /\
               P 6 /\ P 7 /\ P 8 /\ P 9 /\ !x. 9 < x ==> P (x:num)`,
  full_simp_tac(srw_ss())[GSYM (RAND_CONV ETA_CONV ``!x. P x``)]
  \\ eq_tac \\ srw_tac[][]
  \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
  \\ ntac 5 (Cases_on `n` \\ full_simp_tac(srw_ss())[] \\ Cases_on `n'` \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[ADD1,GSYM ADD_ASSOC]
  \\ pop_assum match_mp_tac \\ decide_tac);

val nine_less = DECIDE
  ``9 < n ==> n <> 0 /\ n <> 1 /\ n <> 2 /\ n <> 3 /\ n <> 4 /\
              n <> 5 /\ n <> 6 /\ n <> 7 /\ n <> 8 /\ n <> 9n``

Theorem word_shift_not_0:
   word_shift (:'a) <> 0
Proof
  srw_tac[][word_shift_def] \\ full_simp_tac(srw_ss())[]
QED

Theorem select_lower_lemma:
   (n -- 0) w = ((w:'a word) << (dimindex(:'a)-n-1)) >>> (dimindex(:'a)-n-1)
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [wordsTheory.word_index]
  \\ Cases_on `i + (dimindex (:α) - n - 1) < dimindex (:α)`
  \\ fs []
QED

Theorem select_eq_select_0:
   k <= n ==> (n -- k) w = (n - k -- 0) (w >>> k)
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss] [] \\ eq_tac \\ rw []
QED

val is_fwd_ptr_iff = Q.prove(
  `!w. is_fwd_ptr w <=> ?v. w = Word v /\ (v && 3w) = 0w`,
  Cases \\ full_simp_tac(srw_ss())[wordSemTheory.is_fwd_ptr_def]);

val isWord_thm = Q.prove(
  `!w. isWord w = ?v. w = Word v`,
  Cases \\ full_simp_tac(srw_ss())[wordSemTheory.isWord_def]);

val lower_2w_eq = Q.prove(
  `!w:'a word. good_dimindex (:'a) ==> (w <+ 2w <=> w = 0w \/ w = 1w)`,
  Cases \\ fs [labPropsTheory.good_dimindex_def,WORD_LO,dimword_def]
  \\ rw [] \\ rw []);

val EL_LENGTH_ADD_LEMMA = Q.prove(
  `EL (LENGTH init + LENGTH old) (init ++ old ++ [x] ++ st1) = x`,
  mp_tac (EL_LENGTH_APPEND |> Q.SPECL [`[x] ++ st1`,`init++old`])
  \\ fs []);

val LUPDATE_LENGTH_ADD_LEMMA = Q.prove(
  `LUPDATE w (LENGTH init + LENGTH old) (init ++ old ++ [x] ++ st1) =
       init ++ old ++ [w] ++ st1`,
  mp_tac (LUPDATE_LENGTH |> Q.SPECL [`init++old`]) \\ fs []);

Theorem word_msb_IFF_lsr_EQ_0:
   word_msb h <=> (h >>> (dimindex (:'a) - 1) <> 0w:'a word)
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss] []
QED

Theorem map_bitmap_IMP_LENGTH:
   !x wl stack xs ys.
      map_bitmap x wl stack = SOME (xs,ys) ==>
      LENGTH xs = LENGTH x
Proof
  recInduct map_bitmap_ind \\ fs [map_bitmap_def]
  \\ rw [] \\ res_tac \\ fs []
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
QED

Theorem filter_bitmap_IMP_LENGTH:
   !x stack q r.
      filter_bitmap x stack = SOME (q,r) ==>
      LENGTH stack = LENGTH x + LENGTH r
Proof
  recInduct filter_bitmap_ind \\ fs [filter_bitmap_def]
  \\ rw [] \\ res_tac \\ fs []
  \\ every_case_tac \\ fs []
QED

val EL_LENGTH_ADD_LEMMA = Q.prove(
  `!n xs y ys. LENGTH xs = n ==> EL n (xs ++ y::ys) = y`,
  fs [EL_LENGTH_APPEND]);

Theorem bytes_in_word_word_shift_n2w:
   good_dimindex (:α) ∧ (dimindex(:'a) DIV 8) * n < dimword (:α) ⇒
    (bytes_in_word * n2w n) ⋙ word_shift (:α) = (n2w n):'a word
Proof
  strip_tac \\ match_mp_tac bytes_in_word_word_shift
  \\ fs [bytes_in_word_def]
  \\ `(dimindex (:α) DIV 8) < dimword (:α) /\ n < dimword (:α)` by
       (rfs [labPropsTheory.good_dimindex_def,dimword_def] \\ rfs [])
  \\ fs []
QED

val tac = simp [list_Seq_def,evaluate_def,inst_def,word_exp_def,get_var_def,
       wordLangTheory.word_op_def,mem_load_def,assign_def,set_var_def,
       FLOOKUP_UPDATE,mem_store_def,dec_clock_def,get_var_imm_def,
       asmTheory.word_cmp_def,
       labSemTheory.word_cmp_def,GREATER_EQ,GSYM NOT_LESS,FUPDATE_LIST,
       wordLangTheory.word_sh_def,word_shift_not_0,FLOOKUP_UPDATE]

val tac1 = simp [Once list_Seq_def, evaluate_def,inst_def,word_exp_def,get_var_def,
       wordLangTheory.word_op_def,mem_load_def,assign_def,set_var_def,
       FLOOKUP_UPDATE,mem_store_def,dec_clock_def,get_var_imm_def,
       asmTheory.word_cmp_def,set_store_def,
       labSemTheory.word_cmp_def,GREATER_EQ,GSYM NOT_LESS,FUPDATE_LIST,
       wordLangTheory.word_sh_def,word_shift_not_0,FLOOKUP_UPDATE]


fun abbrev_under_exists tm tac =
  (fn state => (`?^(tm). ^(hd (fst (hd (fst (tac state)))))` by
        (fs [markerTheory.Abbrev_def] \\ NO_TAC)) state)

val memcpy_code_thm = Q.prove(
  `!n a b m dm b1 m1 (s:('a,'c,'b)stackSem$state).
      memcpy ((n2w n):'a word) a b m dm = (b1:'a word,m1,T) /\
      n < dimword (:'a) /\
      s.memory = m /\ s.mdomain = dm /\
      get_var 0 s = SOME (Word (n2w n)) /\
      1 IN FDOM s.regs /\
      get_var 2 s = SOME (Word a) /\
      get_var 3 s = SOME (Word b) ==>
      ?r1.
        evaluate (memcpy_code,s with clock := s.clock + n) =
          (NONE,s with <| memory := m1;
                          regs := s.regs |++ [(0,Word 0w);
                                              (1,r1);
                                              (2,Word (a + n2w n * bytes_in_word));
                                              (3,Word b1)] |>)`,
  Induct THEN1
   (simp [Once memcpy_def]
    \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[memcpy_code_def,
            evaluate_def,get_var_def,get_var_imm_def]
    \\ full_simp_tac(srw_ss())[EVAL ``word_cmp NotEqual 0w 0w``]
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10] \\ full_simp_tac(srw_ss())[nine_less])
  \\ simp [Once memcpy_def]
  \\ rpt gen_tac \\ strip_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[ADD1,GSYM word_add_n2w]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[] \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ simp [memcpy_code_def,evaluate_def,get_var_def,get_var_imm_def]
  \\ full_simp_tac(srw_ss())[labSemTheory.word_cmp_def,asmTheory.word_cmp_def,word_add_n2w,get_var_def]
  \\ tac
  \\ qpat_abbrev_tac `s3 = s with <| regs := _ ; memory := _; clock := _ |>`
  \\ `memcpy ((n2w n):'a word) (a + bytes_in_word) (b + bytes_in_word)
         (s3 with clock := s3.clock - n).memory
         (s3 with clock := s3.clock - n).mdomain = (b1,m1,T)` by
       (unabbrev_all_tac \\ full_simp_tac(srw_ss())[])
  \\ first_x_assum drule \\ full_simp_tac(srw_ss())[]
  \\ impl_tac THEN1
    (unabbrev_all_tac \\ full_simp_tac(srw_ss())[FLOOKUP_UPDATE,GSYM word_add_n2w] \\ decide_tac)
  \\ strip_tac
  \\ `s3 with clock := s3.clock - n + n = s3` by
   (unabbrev_all_tac \\ full_simp_tac(srw_ss())[state_component_equality] \\ decide_tac)
  \\ full_simp_tac(srw_ss())[memcpy_code_def,list_Seq_def,STOP_def]
  \\ unabbrev_all_tac
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
         FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10] \\ full_simp_tac(srw_ss())[nine_less]
  \\ full_simp_tac(srw_ss())[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])

Theorem memcpy_code_thm:
   !w a b m dm b1 m1 (s:('a,'c,'b)stackSem$state).
      memcpy (w:'a word) a b m dm = (b1:'a word,m1,T) /\
      s.memory = m /\ s.mdomain = dm /\
      get_var 0 s = SOME (Word w) /\
      1 IN FDOM s.regs /\
      get_var 2 s = SOME (Word a) /\
      get_var 3 s = SOME (Word b) ==>
      ?r1.
        evaluate (memcpy_code,s with clock := s.clock + w2n w) =
          (NONE,s with <| memory := m1;
                          regs := s.regs |++ [(0,Word 0w);
                                              (1,r1);
                                              (2,Word (a + w * bytes_in_word));
                                              (3,Word b1)] |>)
Proof
  Cases \\ full_simp_tac(srw_ss())[]
  \\ pop_assum mp_tac \\ qspec_tac (`n`,`n`)
  \\ full_simp_tac(srw_ss())[PULL_FORALL] \\ rpt strip_tac
  \\ match_mp_tac (memcpy_code_thm |> SIMP_RULE (srw_ss()) [])
  \\ metis_tac []
QED

(* gc_kind = Simple *)

val word_gc_fun_lemma =
  word_gc_fun_def
  |> SPEC_ALL
  |> DISCH ``conf.gc_kind = Simple``
  |> SIMP_RULE std_ss [TypeBase.case_def_of ``:gc_kind`` ]
  |> SIMP_RULE std_ss [word_full_gc_def]
  |> SIMP_RULE std_ss [Once LET_THM]
  |> SIMP_RULE std_ss [Once LET_THM]
  |> SIMP_RULE std_ss [Once LET_THM]
  |> SIMP_RULE std_ss [Once LET_THM]
  |> SIMP_RULE std_ss [Once LET_THM,word_gc_move_roots_def]

val word_gc_fun_thm = Q.prove(
  `conf.gc_kind = Simple ==>
   word_gc_fun conf (roots,m,dm,s) =
      let (w1,i1:'a word,pa1,m1,c1) =
            word_gc_move conf
              (s ' Globals,0w,theWord (s ' OtherHeap),
               theWord (s ' CurrHeap),m,dm) in
      let (ws2,i2,pa2,m2,c2) =
            word_gc_move_roots conf
              (roots,i1,pa1,theWord (s ' CurrHeap),m1,dm) in
      let (i1,pa1,m1,c2) =
            word_gc_move_loop (dimword (:'a)) conf
              (theWord (s ' OtherHeap),i2,pa2,
               theWord (s ' CurrHeap),m2,dm,c1 /\ c2) in
      let s1 =
            s |++
            [(CurrHeap,Word (theWord (s ' OtherHeap)));
             (OtherHeap,Word (theWord (s ' CurrHeap)));
             (NextFree,Word pa1);
             (TriggerGC,
              Word
                (theWord (s ' OtherHeap) +
                 theWord (s ' HeapLength)));
             (EndOfHeap,
              Word
                (theWord (s ' OtherHeap) +
                 theWord (s ' HeapLength)));
             (Globals,w1)]
      in
        if word_gc_fun_assum conf s /\ c2 then SOME (ws2,m1,s1) else NONE`,
  full_simp_tac(srw_ss())[word_gc_fun_lemma,LET_THM]
  \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[])
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]);

val gc_lemma = gc_def
  |> SPEC_ALL
  |> DISCH ``s.gc_fun = word_gc_fun conf``
  |> SIMP_RULE std_ss [] |> UNDISCH
  |> DISCH ``conf.gc_kind = Simple``
  |> SIMP_RULE std_ss [word_gc_fun_thm] |> DISCH_ALL

val word_gc_move_roots_bitmaps_def = Define `
  word_gc_move_roots_bitmaps conf (stack,bitmaps,i1,pa1,curr,m,dm) =
    case enc_stack bitmaps stack of
    | NONE => (ARB,ARB,ARB,ARB,F)
    | SOME wl_list =>
        let (wl,i2,pa2,m2,c2) =
            word_gc_move_roots conf (wl_list,i1,pa1,curr,m,dm) in
          case dec_stack bitmaps wl stack of
          | NONE => (ARB,ARB,ARB,ARB,F)
          | SOME stack => (stack,i2,pa2,m2,c2)`

Theorem word_gc_move_loop_F:
   !k conf pb i pa old m dm i1 pa1 m1 c1.
      word_gc_move_loop k conf (pb,i,pa,old,m,dm,F) = (i1,pa1,m1,c1) ==> ~c1
Proof
  Induct \\ once_rewrite_tac [word_gc_move_loop_def] \\ fs [] \\ rw []
  \\ pairarg_tac \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ pairarg_tac \\ fs []
QED

Theorem word_gc_move_loop_ok:
   word_gc_move_loop k conf (pb,i,pa,old,m,dm,c) = (i1,pa1,m1,c1) ==> c1 ==> c
Proof
  Cases_on `c` \\ fs [] \\ rw [] \\ imp_res_tac word_gc_move_loop_F \\ fs []
QED

val gc_thm = Q.prove(
  `s.gc_fun = word_gc_fun conf /\ conf.gc_kind = Simple ==>
   gc (s:('a,'c,'b)stackSem$state) =
   if LENGTH s.stack < s.stack_space then NONE else
     let unused = TAKE s.stack_space s.stack in
     let stack = DROP s.stack_space s.stack in
     let (w1,i1,pa1,m1,c1) =
              word_gc_move conf
                (s.store ' Globals,0w,
                 theWord (s.store ' OtherHeap),
                 theWord (s.store ' CurrHeap),s.memory,s.mdomain) in
     let (stack,i2,pa2,m2,c2) =
           word_gc_move_roots_bitmaps conf
             (stack,s.bitmaps,i1,pa1,
              theWord (s.store ' CurrHeap),m1,s.mdomain) in
     let (i1,pa1,m1,c2) =
           word_gc_move_loop (dimword(:'a)) conf
             (theWord (s.store ' OtherHeap),i2,pa2,
              theWord (s.store ' CurrHeap),m2,s.mdomain,
              c1 ∧ c2) in
     let s1 =
           s.store |++
           [(CurrHeap,Word (theWord (s.store ' OtherHeap)));
            (OtherHeap,Word (theWord (s.store ' CurrHeap)));
            (NextFree,Word pa1);
            (TriggerGC,
             Word
               (theWord (s.store ' OtherHeap) +
                theWord (s.store ' HeapLength)));
            (EndOfHeap,
             Word
               (theWord (s.store ' OtherHeap) +
                theWord (s.store ' HeapLength)));
            (Globals,w1)] in
       if word_gc_fun_assum conf s.store /\ c2 then SOME (s with
                       <|stack := unused ++ stack; store := s1;
                         regs := FEMPTY; memory := m1|>) else NONE`,
  strip_tac \\ drule gc_lemma
  \\ disch_then (fn th => full_simp_tac(srw_ss())[th])
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[LET_THM,word_gc_move_roots_bitmaps_def]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  THEN1
   (rpt (pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[])
    \\ imp_res_tac word_gc_move_loop_F \\ fs [])
  \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[]
          \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[])
  \\ Cases_on `dec_stack s.bitmaps ws2 (DROP s.stack_space s.stack)`
  THEN1
   (full_simp_tac(srw_ss())[] \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac word_gc_move_loop_F \\ full_simp_tac(srw_ss())[]
    \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[] \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]);

val word_gc_move_bitmaps_def = Define `
  word_gc_move_bitmaps conf (w,stack,bitmaps,i1,pa1,curr,m,dm) =
    case full_read_bitmap bitmaps w of
    | NONE => NONE
    | SOME bs =>
      case filter_bitmap bs stack of
      | NONE => NONE
      | SOME (ts,ws) =>
        let (wl,i2,pa2,m2,c2) =
                word_gc_move_roots conf (ts,i1,pa1,curr,m,dm) in
          case map_bitmap bs wl stack of
          | NONE => NONE
          | SOME (hd,ts1,ws') =>
              SOME (hd,ws,i2,pa2,m2,c2)`

val word_gc_move_roots_APPEND = Q.prove(
  `!xs ys i1 pa1 m.
      word_gc_move_roots conf (xs++ys,i1,pa1,curr,m,dm) =
        let (ws1,i1,pa1,m1,c1) = word_gc_move_roots conf (xs,i1,pa1,curr,m,dm) in
        let (ws2,i2,pa2,m2,c2) = word_gc_move_roots conf (ys,i1,pa1,curr,m1,dm) in
          (ws1++ws2,i2,pa2,m2,c1 /\ c2)`,
  Induct \\ full_simp_tac(srw_ss())[word_gc_move_roots_def,LET_THM]
  \\ srw_tac[][] \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ rveq \\ fs[]
  \\ EQ_TAC \\ fs[] \\ rw[]);

Theorem word_gc_move_roots_IMP_LENGTH:
   !xs r0 r1 curr r2 dm ys i2 pa2 m2 c conf.
      word_gc_move_roots conf (xs,r0,r1,curr,r2,dm) = (ys,i2,pa2,m2,c) ==>
      LENGTH ys = LENGTH xs
Proof
  Induct \\ full_simp_tac(srw_ss())[word_gc_move_roots_def,LET_THM] \\ srw_tac[][]
  \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[] \\ res_tac
QED

val word_gc_move_roots_bitmaps = Q.prove(
  `!stack i1 pa1 m stack2 i2 pa2 m2.
      (word_gc_move_roots_bitmaps conf (stack,bitmaps,i1,pa1,curr,m,dm) =
        (stack2,i2,pa2,m2,T)) ==>
      word_gc_move_roots_bitmaps conf (stack,bitmaps,i1,pa1,curr,m,dm) =
      case stack of
      | [] => (ARB,ARB,ARB,ARB,F)
      | (w::ws) =>
        if w = Word 0w then (stack,i1,pa1,m,ws = []) else
          case word_gc_move_bitmaps conf (w,ws,bitmaps,i1,pa1,curr,m,dm) of
          | NONE => (ARB,ARB,ARB,ARB,F)
          | SOME (new,stack,i2,pa2,m2,c2) =>
              let (stack,i,pa,m,c3) =
                word_gc_move_roots_bitmaps conf (stack,bitmaps,i2,pa2,curr,m2,dm) in
                  (w::new++stack,i,pa,m,c2 /\ c3)`,
  Cases THEN1 (full_simp_tac(srw_ss())[word_gc_move_roots_bitmaps_def,
                 enc_stack_def])
  \\ rpt strip_tac \\ pop_assum mp_tac \\ full_simp_tac(srw_ss())[]
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  THEN1 (full_simp_tac(srw_ss())[word_gc_move_roots_bitmaps_def,enc_stack_def]
         \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[word_gc_move_roots_def,LET_THM,dec_stack_def])
  \\ full_simp_tac(srw_ss())[word_gc_move_roots_bitmaps_def,word_gc_move_bitmaps_def,enc_stack_def]
  \\ Cases_on `full_read_bitmap bitmaps h` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `filter_bitmap x t` \\ full_simp_tac(srw_ss())[]
  \\ rename1 `_ = SOME filter_res` \\ PairCases_on `filter_res` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `enc_stack bitmaps filter_res1` \\ full_simp_tac(srw_ss())[]
  \\ rename1 `_ = SOME enc_rest` \\ full_simp_tac(srw_ss())[word_gc_move_roots_APPEND]
  \\ simp [Once LET_DEF]
  \\ Cases_on `word_gc_move_roots conf (filter_res0,i1,pa1,curr,m,dm)` \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `r` \\ full_simp_tac(srw_ss())[dec_stack_def]
  \\ Cases_on `word_gc_move_roots conf (enc_rest,r0,r1,curr,r2,dm)` \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `r` \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ rename1 `_ = SOME map_rest` \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `map_rest` \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac word_gc_move_roots_IMP_LENGTH \\ full_simp_tac(srw_ss())[]
  \\ drule (GEN_ALL map_bitmap_APPEND) \\ full_simp_tac(srw_ss())[]
  \\ disch_then (mp_tac o SPEC_ALL) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[] \\ pop_assum kall_tac
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ rename1 `_ = SOME z` \\ full_simp_tac(srw_ss())[] \\ PairCases_on `z` \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac word_gc_move_roots_IMP_LENGTH \\ full_simp_tac(srw_ss())[]
  \\ drule filter_bitmap_map_bitmap
  \\ disch_then drule \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]);

val word_gc_move_bitmap_def = Define `
  word_gc_move_bitmap conf (w,stack,i1,pa1,curr,m,dm) =
    let bs = get_bits w in
      case filter_bitmap bs stack of
      | NONE => NONE
      | SOME (ts,ws) =>
         let (wl,i2,pa2,m2,c2) = word_gc_move_roots conf (ts,i1,pa1,curr,m,dm) in
           case map_bitmap bs wl stack of
           | NONE => NONE
           | SOME (hd,v2) => SOME (hd,ws,i2,pa2,m2,c2)`

val map_bitmap_APPEND_APPEND = Q.prove(
  `!vs1 stack x0 x1 ws2 vs2 ws1.
      filter_bitmap vs1 stack = SOME (x0,x1) /\
      LENGTH x0 = LENGTH ws1 ==>
      map_bitmap (vs1 ++ vs2) (ws1 ++ ws2) stack =
      case map_bitmap vs1 ws1 stack of
      | NONE => NONE
      | SOME (ts1,ts2,ts3) =>
        case map_bitmap vs2 ws2 ts3 of
        | NONE => NONE
        | SOME (us1,us2,us3) => SOME (ts1++us1,ts2++us2,us3)`,
  Induct \\ full_simp_tac(srw_ss())[map_bitmap_def] THEN1
   (Cases \\ full_simp_tac(srw_ss())[filter_bitmap_def]
    \\ once_rewrite_tac [EQ_SYM_EQ] \\ full_simp_tac(srw_ss())[LENGTH_NIL]
    \\ srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ Cases_on `stack` \\ full_simp_tac(srw_ss())[filter_bitmap_def]
  \\ reverse Cases \\ full_simp_tac(srw_ss())[filter_bitmap_def,map_bitmap_def]
  THEN1 (srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `ws1` \\ full_simp_tac(srw_ss())[LENGTH,map_bitmap_def]
  \\ srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  |> SIMP_RULE std_ss [];

val word_gc_move_bitmaps_Loc =
  ``word_gc_move_bitmaps conf (Loc l1 l2,stack,bitmaps,i1,pa1,curr,m,dm)``
  |> SIMP_CONV std_ss [word_gc_move_bitmaps_def,full_read_bitmap_def];

val word_gc_move_bitmaps_unroll = Q.prove(
  `word_gc_move_bitmaps conf (Word w,stack,bitmaps,i1,pa1,curr,m,dm) = SOME x /\
    LENGTH bitmaps < dimword (:'a) - 1 /\ good_dimindex (:'a) ==>
    word_gc_move_bitmaps conf (Word w,stack,bitmaps,i1,pa1,curr,m,dm) =
    case DROP (w2n (w - 1w:'a word)) bitmaps of
    | [] => NONE
    | (y::ys) =>
      case word_gc_move_bitmap conf (y,stack,i1,pa1,curr,m,dm) of
      | NONE => NONE
      | SOME (hd,ws,i2,pa2,m2,c2) =>
          if ~(word_msb y) then SOME (hd,ws,i2,pa2,m2,c2) else
            case word_gc_move_bitmaps conf (Word (w+1w),ws,bitmaps,i2,pa2,curr,m2,dm) of
            | NONE => NONE
            | SOME (hd3,ws3,i3,pa3,m3,c3) =>
                SOME (hd++hd3,ws3,i3,pa3,m3,c2 /\ c3)`,
  full_simp_tac(srw_ss())[word_gc_move_bitmaps_def,full_read_bitmap_def]
  \\ Cases_on `w = 0w` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `DROP (w2n (w + -1w)) bitmaps`
  \\ full_simp_tac(srw_ss())[read_bitmap_def]
  \\ reverse (Cases_on `word_msb h`)
  THEN1
   (full_simp_tac(srw_ss())[word_gc_move_bitmap_def,get_bits_def,LET_THM]
    \\ CASE_TAC \\ rename1 `_ = SOME y` \\ PairCases_on `y`
    \\ full_simp_tac(srw_ss())[]
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ CASE_TAC \\ rename1 `_ = SOME y` \\ PairCases_on `y`
    \\ full_simp_tac(srw_ss())[]
    \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[] \\ Cases_on `read_bitmap t`
  \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ rename1 `_ = SOME y`
  \\ PairCases_on `y` \\ full_simp_tac(srw_ss())[LET_THM]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ rename1 `_ = SOME z`
  \\ PairCases_on `z` \\ full_simp_tac(srw_ss())[LET_THM]
  \\ full_simp_tac(srw_ss())[word_gc_move_bitmap_def,LET_THM] \\ rev_full_simp_tac(srw_ss())[get_bits_intro]
  \\ strip_tac \\ rpt var_eq_tac
  \\ IF_CASES_TAC THEN1
   (sg `F`
    \\ full_simp_tac(srw_ss())[wordsLib.WORD_DECIDE ``w+1w=0w <=> (w = -1w)``]
    \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[labPropsTheory.good_dimindex_def]
    \\ full_simp_tac(srw_ss())[word_2comp_def] \\ full_simp_tac(srw_ss())[dimword_def]
    \\ imp_res_tac DROP_IMP_LESS_LENGTH \\ decide_tac)
  \\ `DROP (w2n w) bitmaps = t` by
   (`w2n w = SUC (w2n (w + -1w))` suffices_by
      metis_tac [DROP_EQ_CONS_IMP_DROP_SUC]
    \\ Cases_on `w` \\ full_simp_tac(srw_ss())[word_add_n2w]
    \\ `~(n < 1) /\ n - 1 < dimword (:'a)` by decide_tac
    \\ full_simp_tac std_ss [GSYM word_sub_def,addressTheory.word_arith_lemma2]
    \\ full_simp_tac(srw_ss())[] \\ decide_tac) \\ full_simp_tac(srw_ss())[] \\ pop_assum kall_tac
  \\ full_simp_tac(srw_ss())[filter_bitmap_APPEND]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `x` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `filter_bitmap x' x1` \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `x` \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[word_gc_move_roots_APPEND,LET_THM]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ qpat_x_assum `filter_bitmap (get_bits h) stack = SOME (x0,x1)` assume_tac
  \\ drule (map_bitmap_APPEND_APPEND |> GEN_ALL)
  \\ `LENGTH x0 = LENGTH wl'` by (imp_res_tac word_gc_move_roots_IMP_LENGTH \\ full_simp_tac(srw_ss())[])
  \\ disch_then drule
  \\ disch_then (qspecl_then [`ws2`,`x'`] mp_tac)
  \\ strip_tac \\ full_simp_tac(srw_ss())[] \\ pop_assum kall_tac
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `x` \\ full_simp_tac(srw_ss())[]
  \\ drule filter_bitmap_map_bitmap
  \\ once_rewrite_tac [EQ_SYM_EQ] \\ disch_then drule
  \\ once_rewrite_tac [EQ_SYM_EQ] \\ disch_then drule
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `x` \\ full_simp_tac(srw_ss())[]);

val word_gc_move_bitmap_unroll = Q.prove(
  `word_gc_move_bitmap conf (w,stack,i1,pa1,curr,m,dm) =
    if w = 0w:'a word then SOME ([],stack,i1,pa1,m,T) else
    if w = 1w then SOME ([],stack,i1,pa1,m,T) else
      case stack of
      | [] => NONE
      | (x::xs) =>
        if (w && 1w) = 0w then
          case word_gc_move_bitmap conf (w >>> 1,xs,i1,pa1,curr,m,dm) of
          | NONE => NONE
          | SOME (new,stack,i1,pa1,m,c) => SOME (x::new,stack,i1,pa1,m,c)
        else
          let (x1,i1,pa1,m1,c1) = word_gc_move conf (x,i1,pa1,curr,m,dm) in
          case word_gc_move_bitmap conf (w >>> 1,xs,i1,pa1,curr,m1,dm) of
          | NONE => NONE
          | SOME (new,stack,i1,pa1,m,c) => SOME (x1::new,stack,i1,pa1,m,c1 /\ c)`,
  simp [word_and_one_eq_0_iff]
  \\ simp [Once word_gc_move_bitmap_def,get_bits_def]
  \\ IF_CASES_TAC
  \\ full_simp_tac(srw_ss())[EVAL ``bit_length 0w``,filter_bitmap_def,
         map_bitmap_def,word_gc_move_roots_def]
  \\ IF_CASES_TAC
  \\ full_simp_tac(srw_ss())[EVAL ``bit_length 1w``,filter_bitmap_def,
         map_bitmap_def,word_gc_move_roots_def]
  \\ simp [bit_length_minus_1]
  \\ full_simp_tac(srw_ss())[GSYM bit_length_eq_1]
  \\ pop_assum (fn th => mp_tac (ONCE_REWRITE_RULE [bit_length_def] th))
  \\ full_simp_tac(srw_ss())[] \\ strip_tac
  \\ Cases_on `bit_length (w >>> 1)` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[GENLIST_CONS,o_DEF,ADD1,filter_bitmap_def]
  \\ Cases_on `stack` \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[filter_bitmap_def]
  \\ `get_bits (w >>> 1) = GENLIST (\x. w ' (x + 1)) n` by
   (full_simp_tac(srw_ss())[get_bits_def,GENLIST_FUN_EQ] \\ srw_tac[][]
    \\ `n + 1 <= dimindex (:'a)` by metis_tac [bit_length_LESS_EQ_dimindex]
    \\ `x < dimindex (:'a)` by decide_tac
    \\ full_simp_tac(srw_ss())[word_lsr_def,fcpTheory.FCP_BETA]
    \\ eq_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ decide_tac)
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[filter_bitmap_def,map_bitmap_def]
  THEN1
   (full_simp_tac(srw_ss())[word_gc_move_bitmap_def,LET_THM]
    \\ ntac 2 (CASE_TAC \\ full_simp_tac(srw_ss())[])
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ rpt (CASE_TAC \\ full_simp_tac(srw_ss())[]))
  \\ full_simp_tac(srw_ss())[word_gc_move_bitmap_def,LET_THM]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] THEN1 (pairarg_tac \\ full_simp_tac(srw_ss())[])
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[word_gc_move_roots_def,LET_THM]
  \\ ntac 3 (pairarg_tac \\ full_simp_tac(srw_ss())[]) \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[map_bitmap_def]
  \\ rpt (CASE_TAC \\ full_simp_tac(srw_ss())[]));

Theorem word_gc_move_code_thm:
   word_gc_move conf (w,i,pa,old,m,dm) = (w1,i1,pa1,m1,T) /\
    shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
    2 < dimindex (:'a) /\ conf.len_size <> 0 /\
    (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
    FLOOKUP (s:('a,'c,'b)stackSem$state).store CurrHeap = SOME (Word old) /\ s.use_store /\
    s.memory = m /\ s.mdomain = dm /\
    0 IN FDOM s.regs /\
    1 IN FDOM s.regs /\
    2 IN FDOM s.regs /\
    get_var 3 s = SOME (Word pa) /\
    get_var 4 s = SOME (Word (i:'a word)) /\
    get_var 5 s = SOME w /\
    6 IN FDOM s.regs ==>
    ?ck r0 r1 r2 r6.
      evaluate (word_gc_move_code conf,s with clock := s.clock + ck) =
        (NONE,s with <| memory := m1;
                        regs := s.regs |++ [(0,r0);
                                            (1,r1);
                                            (2,r2);
                                            (3,Word pa1);
                                            (4,Word i1);
                                            (5,w1);
                                            (6,r6)] |>)
Proof
  reverse (Cases_on `w`) \\ full_simp_tac(srw_ss())[word_gc_move_def] THEN1
   (srw_tac[][word_gc_move_code_def,evaluate_def]
    \\ full_simp_tac(srw_ss())[get_var_def] \\ tac
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less])
  \\ full_simp_tac(srw_ss())[get_var_def,word_gc_move_code_def,evaluate_def] \\ tac
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[] THEN1
   (tac \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac `0` \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less])
  \\ IF_CASES_TAC
  THEN1
   (full_simp_tac(srw_ss())[ptr_to_addr_def] \\ tac
    \\ strip_tac \\ rpt var_eq_tac \\ tac
    \\ full_simp_tac(srw_ss())[is_fwd_ptr_iff] \\ tac
    \\ full_simp_tac(srw_ss())[clear_top_inst_def,evaluate_def] \\ tac
    \\ qexists_tac `0` \\ full_simp_tac(srw_ss())[theWord_def]
    \\ full_simp_tac(srw_ss())[update_addr_def,select_lower_lemma]
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less])
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[ptr_to_addr_def,isWord_thm]
  \\ strip_tac \\ rpt var_eq_tac \\ tac
  \\ full_simp_tac(srw_ss())[is_fwd_ptr_def,theWord_def,clear_top_inst_def] \\ tac
  \\ qabbrev_tac `len = decode_length conf v`
  \\ full_simp_tac(srw_ss())[GSYM select_lower_lemma]
  \\ qexists_tac `w2n (len + 1w)`
  \\ drule memcpy_code_thm
  \\ qpat_abbrev_tac `s3 = s with <| regs := _ ; clock := _ |>`
  \\ disch_then (qspec_then `s3 with clock := s.clock` mp_tac)
  \\ full_simp_tac(srw_ss())[]
  \\ `s3 with clock := s.clock + w2n (len + 1w) = s3` by
       (unabbrev_all_tac \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC] \\ NO_TAC)
  \\ full_simp_tac(srw_ss())[] \\ impl_tac THEN1
    (unabbrev_all_tac \\ full_simp_tac(srw_ss())[get_var_def] \\ tac
     \\ fs [decode_length_def])
  \\ strip_tac \\ full_simp_tac(srw_ss())[FUPDATE_LIST]
  \\ unabbrev_all_tac \\ full_simp_tac(srw_ss())[] \\ tac
  \\ fs [LET_THM,decode_length_def]
  \\ fs [] \\ tac \\ rpt var_eq_tac
  \\ full_simp_tac(srw_ss())[] \\ tac
  \\ full_simp_tac(srw_ss())[select_lower_lemma,
        DECIDE ``n<>0 ==> m-(n-1)-1=m-n:num``]
  \\ tac \\ full_simp_tac(srw_ss())[] \\ tac
  \\ full_simp_tac(srw_ss())[update_addr_def]
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
         FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less]
  \\ `shift_length conf <> 0` by (EVAL_TAC \\ decide_tac)
  \\ full_simp_tac(srw_ss())[select_lower_lemma,
        DECIDE ``n<>0 ==> m-(n-1)-1=m-n:num``]
QED

Theorem word_gc_move_list_code_thm:
   !l a (s:('a,'c,'b)stackSem$state) pa1 pa old m1 m i1 i dm conf a1.
      word_gc_move_list conf (a:'a word,l,i,pa,old,m,dm) = (a1,i1,pa1,m1,T) /\
      shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ conf.len_size <> 0 /\
      (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
      FLOOKUP s.store CurrHeap = SOME (Word old) /\ s.use_store /\
      s.memory = m /\ s.mdomain = dm /\
       0 IN FDOM s.regs /\
      1 IN FDOM s.regs /\
      2 IN FDOM s.regs /\
      get_var 3 s = SOME (Word pa) /\
      get_var 4 s = SOME (Word (i:'a word)) /\
      5 IN FDOM s.regs ==>
      6 IN FDOM s.regs ==>
      get_var 7 s = SOME (Word l) /\
      get_var 8 s = SOME (Word a) ==>
      ?ck r0 r1 r2 r5 r6.
        evaluate (word_gc_move_list_code conf,s with clock := s.clock + ck) =
          (NONE,s with <| memory := m1;
                          regs := s.regs |++ [(0,r0);
                                              (1,r1);
                                              (2,r2);
                                              (3,Word pa1);
                                              (4,Word i1);
                                              (5,r5);
                                              (6,r6);
                                              (7,Word 0w);
                                              (8,Word a1)] |>)
Proof
  Cases \\ Induct_on `n` \\ simp [] THEN1
   (fs [Once word_gc_move_list_def] \\ rw []
    \\ qexists_tac `0`
    \\ fs [word_gc_move_list_code_def,get_var_def] \\ tac
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less])
  \\ once_rewrite_tac [word_gc_move_list_def] \\ simp [LET_THM]
  \\ rpt strip_tac \\ simp [LET_THM]
  \\ qpat_x_assum `_ = (a1,i1,pa1,m1,T)` mp_tac
  \\ `n2w (SUC n) + -1w = n2w n` by fs [ADD1,GSYM word_add_n2w]
  \\ pairarg_tac \\ simp []
  \\ pairarg_tac \\ simp []
  \\ strip_tac
  \\ rpt var_eq_tac
  \\ `n < dimword (:'a)` by decide_tac
  \\ first_x_assum drule
  \\ disch_then drule
  \\ fs [] \\ strip_tac
  \\ rpt var_eq_tac \\ fs []
  \\ simp [word_gc_move_list_code_def,evaluate_def]
  \\ fs [GSYM word_gc_move_list_code_def,get_var_def,get_var_imm_def]
  \\ tac
  \\ drule (word_gc_move_code_thm |> GEN_ALL)
  \\ fs [ADD1,GSYM word_add_n2w]
  \\ `FLOOKUP ((s:('a,'c,'b)stackSem$state) with
           <|regs := s.regs |+ (5,s.memory a) |+ (7,Word (n2w n)) |>).store
       CurrHeap  = SOME (Word old)` by fs []
  \\ disch_then drule \\ fs [get_var_def] \\ tac \\ strip_tac
  \\ fs []
  \\ first_x_assum (qspec_then `s with
        <|regs :=
            s.regs |+ (5,s.memory a) |+ (7,Word (n2w n)) |+ (0,r0) |+
            (1,r1) |+ (2,r2) |+ (3,Word pa1') |+ (4,Word i1') |+
            (5,w1) |+ (6,r6) |+ (8,Word (a + bytes_in_word));
          memory := (a =+ w1) m1' |>` mp_tac)
  \\ rpt (impl_tac THEN1 (fs [] \\ tac)) \\ fs []
  \\ strip_tac \\ fs []
  \\ qexists_tac `ck+ck'+1` \\ fs []
  \\ pop_assum mp_tac
  \\ drule (evaluate_add_clock |> GEN_ALL)
  \\ disch_then (qspec_then `ck'+1` strip_assume_tac)
  \\ fs [AC ADD_COMM ADD_ASSOC] \\ tac
  \\ strip_tac
  \\ drule (evaluate_add_clock |> GEN_ALL)
  \\ disch_then (qspec_then `ck` strip_assume_tac)
  \\ fs [AC ADD_COMM ADD_ASSOC] \\ tac
  \\ fs [STOP_def]
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
         FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less]
QED

val word_gc_move_loop_code_thm = Q.prove(
  `!k pb1 i1 pa1 old1 m1 dm1 c1 i2 pa2 m2 (s:('a,'c,'b)stackSem$state).
      word_gc_move_loop k conf (pb1,i1,pa1,old1,m1,dm1,c1) = (i2,pa2,m2,T) /\
      shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ conf.len_size <> 0 /\
      conf.len_size + 2 < dimindex (:'a) /\
      (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
      FLOOKUP s.store CurrHeap = SOME (Word old1) /\ s.use_store /\
      s.memory = m1 /\ s.mdomain = dm1 /\
      0 IN FDOM s.regs /\
      1 IN FDOM s.regs /\
      2 IN FDOM s.regs /\
      get_var 3 s = SOME (Word pa1) /\
      get_var 4 s = SOME (Word (i1:'a word)) /\
      5 IN FDOM s.regs ==>
      6 IN FDOM s.regs ==>
      7 IN FDOM s.regs ==>
      get_var 8 s = SOME (Word pb1) /\ c1 ==>
      ?ck r0 r1 r2 r5 r6 r7.
        evaluate (word_gc_move_loop_code conf,s with clock := s.clock + ck) =
          (NONE,s with <| memory := m2;
                          regs := s.regs |++ [(0,r0);
                                              (1,r1);
                                              (2,r2);
                                              (3,Word pa2);
                                              (4,Word i2);
                                              (5,r5);
                                              (6,r6);
                                              (7,r7);
                                              (8,Word pa2)] |>)`,
  strip_tac \\ completeInduct_on `k` \\ rpt strip_tac
  \\ qpat_x_assum `word_gc_move_loop _ _ _ = _` mp_tac
  \\ once_rewrite_tac [word_gc_move_loop_def]
  \\ IF_CASES_TAC THEN1
   (fs [] \\ rw [] \\ fs [] \\ rpt var_eq_tac
    \\ fs [word_gc_move_loop_code_def,get_var_def] \\ tac
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less])
  \\ IF_CASES_TAC \\ fs []
  \\ `k-1 < k` by decide_tac
  \\ first_x_assum drule \\ ntac 2 (pop_assum kall_tac) \\ strip_tac
  \\ rpt var_eq_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ Cases_on `word_bit 2 (theWord (s.memory pb1))`
  \\ fs [word_bit_test] THEN1
   (strip_tac
    \\ drule word_gc_move_loop_ok \\ fs [] \\ strip_tac \\ fs []
    \\ asm_simp_tac std_ss[word_gc_move_loop_code_def,evaluate_def]
    \\ asm_simp_tac std_ss[GSYM word_gc_move_loop_code_def,STOP_def]
    \\ fs [get_var_def,isWord_thm,clear_top_inst_def] \\ tac
    \\ rev_full_simp_tac(srw_ss())
         [decode_length_def,LET_THM] \\ rpt var_eq_tac
    \\ full_simp_tac(srw_ss())[theWord_def] \\ tac
    \\ rev_full_simp_tac(srw_ss())[select_lower_lemma,
         DECIDE ``n<>0 ==> m-(n-1)-1=m-n:num``,theWord_def]
    \\ qabbrev_tac `ww = bytes_in_word *
          (v ⋙ (dimindex (:α) − conf.len_size) + 1w)`
    \\ qabbrev_tac `s5 = s with
        <|regs := s.regs |+ (7,Word v) |+
                            (7,Word ww) |+ (8,Word (pb1 + ww)) |>`
    \\ `s.memory = s5.memory /\ s.mdomain = s5.mdomain` by
         (unabbrev_all_tac \\ fs [])
    \\ fs [] \\ first_x_assum drule \\ fs []
    \\ fs [AND_IMP_INTRO] \\ impl_tac
    THEN1 (unabbrev_all_tac \\ fs [FLOOKUP_UPDATE])
    \\ strip_tac \\ qexists_tac `ck + 1` \\ fs []
    \\ qunabbrev_tac `s5` \\ fs []
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less])
  \\ strip_tac
  \\ drule word_gc_move_loop_ok \\ fs [] \\ strip_tac \\ fs []
  \\ asm_simp_tac std_ss[word_gc_move_loop_code_def,evaluate_def]
  \\ asm_simp_tac std_ss[GSYM word_gc_move_loop_code_def,STOP_def]
  \\ rev_full_simp_tac(srw_ss())[] \\ rpt var_eq_tac
  \\ fs [get_var_def,isWord_thm,clear_top_inst_def] \\ tac
  \\ full_simp_tac(srw_ss())[theWord_def] \\ tac
  \\ rev_full_simp_tac(srw_ss())[select_lower_lemma,
       DECIDE ``n<>0 ==> m-(n-1)-1=m-n:num``,theWord_def]
  \\ rev_full_simp_tac(srw_ss())
         [decode_length_def,LET_THM] \\ rpt var_eq_tac
  \\ qabbrev_tac `s5 = s with
        <|regs :=
            s.regs |+ (7,Word v) |+
            (7,Word (v ⋙ (dimindex (:'a) − conf.len_size))) |+
            (8,Word (pb1 + bytes_in_word)) |>`
  \\ drule word_gc_move_list_code_thm
  \\ disch_then (qspec_then `s5` mp_tac)
  \\ fs [AND_IMP_INTRO] \\ impl_tac
  THEN1 (unabbrev_all_tac \\ fs [FLOOKUP_UPDATE,get_var_def])
  \\ strip_tac \\ fs [GSYM CONJ_ASSOC]
  \\ pop_assum mp_tac
  \\ qpat_abbrev_tac `s6 = s5 with <|regs := _ ; memory := _ |>`
  \\ `s.mdomain = s6.mdomain /\ m1 = s6.memory` by (unabbrev_all_tac \\ fs [])
  \\ qpat_x_assum `Abbrev _` assume_tac
  \\ fs [] \\ qpat_x_assum `_ = _` kall_tac
  \\ first_x_assum drule \\ impl_tac
  THEN1 (unabbrev_all_tac \\ fs [FUPDATE_LIST,FLOOKUP_UPDATE])
  \\ rpt strip_tac \\ qexists_tac `ck + ck' + 1`
  \\ drule (evaluate_add_clock |> GEN_ALL)
  \\ disch_then (qspec_then `ck'+1` mp_tac) \\ fs []
  \\ qunabbrev_tac `s5` \\ fs [] \\ strip_tac
  \\ qunabbrev_tac `s6`
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
         FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less]);

Theorem word_gc_move_bitmap_code_thm:
   !w stack (s:('a,'c,'b)stackSem$state) i pa curr m dm new stack1 a1 i1 pa1 m1 old.
      word_gc_move_bitmap conf (w,stack,i,pa,curr,m,dm) =
        SOME (new,stack1,i1,pa1,m1,T) /\
      shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ conf.len_size <> 0 /\ good_dimindex (:'a) /\
      (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
      FLOOKUP s.store CurrHeap = SOME (Word curr) /\ s.use_store /\
      s.memory = m /\ s.mdomain = dm /\ s.use_stack /\
      0 IN FDOM s.regs /\
      1 IN FDOM s.regs /\
      2 IN FDOM s.regs /\
      get_var 3 s = SOME (Word pa) /\
      get_var 4 s = SOME (Word (i:'a word)) /\
      5 IN FDOM s.regs /\
      6 IN FDOM s.regs /\
      get_var 7 s = SOME (Word w) /\
      get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
      s.stack = init ++ old ++ stack /\
      s.stack_space = LENGTH init /\
      (dimindex (:'a) DIV 8) * LENGTH s.stack < dimword (:'a) ==>
      ?ck r0 r1 r2 r5 r6 r7.
        evaluate (word_gc_move_bitmap_code conf,s with clock := s.clock + ck) =
          (NONE,s with <| memory := m1;
                          stack := init ++ old ++ new ++ stack1;
                          regs := s.regs |++ [(0,r0);
                                              (1,r1);
                                              (2,r2);
                                              (3,Word pa1);
                                              (4,Word i1);
                                              (5,r5);
                                              (6,r6);
                                              (7,r7);
                      (8,Word (bytes_in_word * n2w (LENGTH (old ++ new))))] |>)
Proof
  recInduct bit_length_ind \\ rpt strip_tac \\ fs []
  \\ qpat_x_assum `word_gc_move_bitmap _ _ = _` mp_tac
  \\ once_rewrite_tac [word_gc_move_bitmap_unroll]
  \\ Cases_on `w = 0w` \\ fs [] THEN1
   (strip_tac \\ rpt var_eq_tac
    \\ fs [word_gc_move_bitmap_code_def,get_var_def] \\ tac
    \\ fs [lower_2w_eq]
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less])
  \\ Cases_on `w = 1w` \\ fs [] THEN1
   (strip_tac \\ rpt var_eq_tac
    \\ fs [word_gc_move_bitmap_code_def,get_var_def] \\ tac
    \\ fs [lower_2w_eq]
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less])
  \\ Cases_on `stack` \\ fs []
  \\ IF_CASES_TAC THEN1
   (every_case_tac \\ strip_tac \\ rpt var_eq_tac
    \\ rename1 `_ = SOME (new1,st1,i1,pa1,m1,T)`
    \\ simp_tac std_ss [word_gc_move_bitmap_code_def,get_var_def,evaluate_def]
    \\ simp_tac std_ss [GSYM word_gc_move_bitmap_code_def]
    \\ fs [get_var_def,get_var_imm_def] \\ tac
    \\ fs [lower_2w_eq,STOP_def]
    \\ qabbrev_tac `s2 = s with
           <|regs := s.regs |+ (7,Word (w ⋙ 1))
              |+ (8,Word (bytes_in_word + bytes_in_word * n2w (LENGTH old))) |>`
    \\ `s.memory = s2.memory /\ s.mdomain = s2.mdomain` by
          (unabbrev_all_tac \\ fs []) \\ fs []
    \\ first_x_assum drule
    \\ disch_then (qspec_then `old ++ [h]` mp_tac)
    \\ impl_tac
    THEN1 (unabbrev_all_tac
         \\ fs [FLOOKUP_UPDATE,word_add_n2w]
         \\ rfs [WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w])
    \\ strip_tac \\ unabbrev_all_tac \\ fs []
    \\ qexists_tac `ck + 1` \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND,ADD1]
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less] \\ fs [])
  \\ pairarg_tac \\ fs []
  \\ every_case_tac \\ strip_tac \\ rpt var_eq_tac
  \\ rename1 `_ = SOME (new1,st1,i1,pa1,m1,T)`
  \\ simp_tac std_ss [word_gc_move_bitmap_code_def,get_var_def,evaluate_def]
  \\ simp_tac std_ss [GSYM word_gc_move_bitmap_code_def]
  \\ fs [get_var_def,get_var_imm_def] \\ tac
  \\ fs [lower_2w_eq,STOP_def]
  \\ `w2n (((bytes_in_word:'a word) * n2w (LENGTH old)) ⋙ word_shift (:α)) =
         LENGTH old` by
   (`(dimindex (:α) DIV 8) * LENGTH old < dimword (:α)` by rfs [RIGHT_ADD_DISTRIB]
    \\ drule (bytes_in_word_word_shift_n2w |> GEN_ALL)
    \\ disch_then drule \\ fs [] \\ rw []
    \\ rfs [labPropsTheory.good_dimindex_def,dimword_def] \\ rfs [])
  \\ fs [] \\ reverse CASE_TAC THEN1
    (sg `F` \\ fs []
     \\ pop_assum mp_tac \\ fs [] \\ AP_TERM_TAC
     \\ match_mp_tac (bytes_in_word_word_shift_n2w |> GEN_ALL) \\ fs []
     \\ rfs [labPropsTheory.good_dimindex_def,dimword_def] \\ rfs [])
  \\ fs [] \\ tac \\ fs [EL_LENGTH_ADD_LEMMA]
  \\ qabbrev_tac `s4 = s with <|regs := s.regs |+ (5,h) |+ (7,Word (w ⋙ 1)) |>`
  \\ `s.memory = s4.memory /\ s.mdomain = s4.mdomain` by
           (unabbrev_all_tac \\ fs []) \\ fs []
  \\ drule (word_gc_move_code_thm |> GEN_ALL |> SIMP_RULE std_ss [])
  \\ impl_tac THEN1 (unabbrev_all_tac \\ fs [get_var_def,FLOOKUP_UPDATE])
  \\ strip_tac
  \\ qabbrev_tac `s5 = s with
        <|regs :=
            s.regs |+ (5,h) |+ (7,Word (w ⋙ 1)) |+ (0,r0) |+ (1,r1) |+
            (2,r2) |+ (3,Word pa1') |+ (4,Word i1') |+ (5,x1) |+ (6,r6) |+
            (8,Word (bytes_in_word + bytes_in_word * n2w (LENGTH old)));
          stack := init ++ old ++ [x1] ++ t; memory := m1' |>`
  \\ `m1' = s5.memory /\ s4.mdomain = s5.mdomain` by
           (unabbrev_all_tac \\ fs []) \\ fs []
  \\ first_x_assum drule
  \\ disch_then (qspec_then `old ++ [x1]` mp_tac)
  \\ impl_tac THEN1
   (unabbrev_all_tac \\ tac
    \\ fs [RIGHT_ADD_DISTRIB,word_add_n2w,word_mul_n2w,bytes_in_word_def]
    \\ rfs [labPropsTheory.good_dimindex_def,dimword_def] \\ rfs [])
  \\ strip_tac \\ pop_assum mp_tac
  \\ drule (GEN_ALL evaluate_add_clock) \\ fs []
  \\ disch_then (qspec_then `ck' + 1` mp_tac)
  \\ rpt strip_tac \\ fs []
  \\ qexists_tac `ck+ck'+1` \\ fs []
  \\ unabbrev_all_tac \\ fs [] \\ tac
  \\ fs [LUPDATE_LENGTH_ADD_LEMMA,ADD1]
  \\ fs [EL_APPEND_EQN]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND,ADD1]
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less]
  \\ fs [FAPPLY_FUPDATE_THM,LUPDATE_APPEND,LUPDATE_def]
  \\ pop_assum mp_tac \\ fs []
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less]
QED

Theorem word_gc_move_bitmaps_LENGTH:
   word_gc_move_bitmaps conf (w,stack,bitmaps,i,pa,curr,m,dm) =
       SOME (xs,stack1,i1,pa1,m1,T) ==>
    LENGTH stack = LENGTH xs + LENGTH stack1
Proof
  fs [word_gc_move_bitmaps_def]
  \\ every_case_tac \\ fs [] \\ pairarg_tac \\ fs []
  \\ every_case_tac \\ fs [] \\ rw []
  \\ imp_res_tac map_bitmap_IMP_LENGTH \\ fs []
  \\ imp_res_tac filter_bitmap_IMP_LENGTH \\ fs []
QED

Theorem word_gc_move_bitmaps_code_thm:
   !w bitmaps z stack (s:('a,'c,'b)stackSem$state) i pa curr m dm new
         stack1 a1 i1 pa1 m1 old.
      word_gc_move_bitmaps conf (Word w,stack,bitmaps,i,pa,curr,m,dm) =
        SOME (new,stack1,i1,pa1,m1,T) /\
      LENGTH bitmaps < dimword (:'a) − 1 ∧ good_dimindex (:'a) /\
      shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ conf.len_size <> 0 /\ good_dimindex (:'a) /\
      (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
      FLOOKUP s.store CurrHeap = SOME (Word curr) /\ s.use_store /\
      s.memory = m /\ s.mdomain = dm /\ s.bitmaps = bitmaps /\ s.use_stack /\
      get_var 0 s = SOME (Word z) /\ z <> 0w /\
      1 IN FDOM s.regs /\
      2 IN FDOM s.regs /\
      get_var 3 s = SOME (Word pa) /\
      get_var 4 s = SOME (Word (i:'a word)) /\
      5 IN FDOM s.regs /\
      6 IN FDOM s.regs /\
      7 IN FDOM s.regs /\
      get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
      get_var 9 s = SOME (Word (w - 1w)) /\
      s.stack = init ++ old ++ stack /\
      s.stack_space = LENGTH init /\
      (dimindex (:'a) DIV 8) * LENGTH s.stack < dimword (:'a) ==>
      ?ck r0 r1 r2 r5 r6 r7 r9.
        evaluate (word_gc_move_bitmaps_code conf,s with clock := s.clock + ck) =
          (NONE,s with <| memory := m1;
                          stack := init ++ old ++ new ++ stack1;
                          clock := s.clock;
                          regs := s.regs |++ [(0,r0);
                                              (1,r1);
                                              (2,r2);
                                              (3,Word pa1);
                                              (4,Word i1);
                                              (5,r5);
                                              (6,r6);
                                              (7,r7);
                      (8,Word (bytes_in_word * n2w (LENGTH (old ++ new))));
                                              (9,r9)] |>)
Proof
  ntac 2 strip_tac \\ completeInduct_on `LENGTH bitmaps - w2n (w - 1w)`
  \\ rpt strip_tac \\ fs [] \\ rpt var_eq_tac \\ fs [PULL_FORALL]
  \\ qpat_x_assum `word_gc_move_bitmaps _ _ = _`
        (fn th => assume_tac th \\ mp_tac th)
  \\ drule (GEN_ALL word_gc_move_bitmaps_unroll) \\ fs []
  \\ CASE_TAC \\ fs []
  \\ Cases_on `word_gc_move_bitmap conf (h,stack,i,pa,curr,s.memory,s.mdomain)`
  \\ fs [] \\ PairCases_on `x` \\ fs [] \\ strip_tac
  \\ `x5` by (every_case_tac \\ fs []) \\ var_eq_tac
  \\ simp_tac std_ss [word_gc_move_bitmaps_code_def,get_var_def,evaluate_def]
  \\ simp_tac std_ss [GSYM word_gc_move_bitmaps_code_def]
  \\ fs [get_var_def,get_var_imm_def] \\ tac
  \\ imp_res_tac DROP_IMP_LESS_LENGTH \\ fs []
  \\ qabbrev_tac `s2 = s with
           <|regs := s.regs |+ (7,Word (EL (w2n (w + -1w)) s.bitmaps)) |>`
  \\ imp_res_tac DROP_IMP_EL \\ fs []
  \\ `s.memory = s2.memory /\ s.mdomain = s2.mdomain` by (unabbrev_all_tac \\ fs [])
  \\ fs []
  \\ drule (word_gc_move_bitmap_code_thm |> GEN_ALL |> SIMP_RULE std_ss [])
  \\ disch_then (qspecl_then [`init`,`old`] mp_tac)
  \\ impl_tac
  THEN1 (unabbrev_all_tac \\ rfs [get_var_def] \\ tac \\ fs [FLOOKUP_DEF])
  \\ strip_tac \\ drule (GEN_ALL evaluate_add_clock)
  \\ reverse (Cases_on `word_msb h`) \\ fs []
  \\ fs [word_msb_IFF_lsr_EQ_0] THEN1
   (disch_then (qspec_then `1` assume_tac)
    \\ qexists_tac `ck+1` \\ unabbrev_all_tac \\ fs [STOP_def] \\ tac
    \\ fs [word_gc_move_bitmaps_code_def] \\ tac
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
             FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less] \\ fs [])
  \\ strip_tac
  \\ Cases_on `word_gc_move_bitmaps conf
       (Word (w + 1w),x1,s.bitmaps,x2,x3,curr,x4,s2.mdomain)` \\ fs []
  \\ rename1 `_ = SOME y` \\ PairCases_on `y` \\ fs []
  \\ rpt var_eq_tac
  \\ qabbrev_tac `s5 = s with
     <|regs :=
         s.regs |+ (7,Word (EL (w2n (w + -1w)) s.bitmaps)) |+ (0,r0) |+
         (1,r1) |+ (2,r2) |+ (3,Word x3) |+ (4,Word x2) |+ (5,r5) |+
         (6,r6) |+ (7,r7) |+
         (8,Word (bytes_in_word * n2w (LENGTH old + LENGTH x0))) |+
         (0,Word (EL (w2n (w + -1w)) s.bitmaps)) |+ (9,Word w) |+
         (0,Word (EL (w2n (w + -1w)) s.bitmaps ⋙ (dimindex (:α) − 1)));
       stack := init ++ old ++ x0 ++ x1; memory := x4 |>`
  \\ `LENGTH s5.bitmaps <
      LENGTH s.bitmaps + w2n ((w+1w) + -1w) − w2n (w + -1w)` by
   (unabbrev_all_tac \\ fs [] \\ Cases_on `w` \\ fs []
    \\ fs [word_add_n2w] \\ Cases_on `n` \\ fs []
    \\ fs [GSYM word_add_n2w,ADD1,w2n_minus1] \\ NO_TAC)
  \\ first_x_assum drule \\ fs []
  \\ `x4 = s5.memory /\ s.mdomain = s5.mdomain /\ s.bitmaps = s5.bitmaps` by
       (unabbrev_all_tac \\ fs []) \\ fs []
  \\ disch_then drule
  \\ ntac 3 (pop_assum (fn th => fs [GSYM th]))
  \\ disch_then (qspecl_then [`EL (w2n (w + -1w))
         s5.bitmaps ⋙ (dimindex (:α) - 1)`,`old ++ x0`] mp_tac)
  \\ fs [AND_IMP_INTRO]
  \\ impl_tac THEN1
   (unabbrev_all_tac \\ fs [] \\ tac
    \\ rfs [RIGHT_ADD_DISTRIB]
    \\ imp_res_tac word_gc_move_bitmaps_LENGTH \\ fs [])
  \\ strip_tac
  \\ first_x_assum (qspec_then `ck'+1` assume_tac)
  \\ qexists_tac `ck+ck'+1` \\ fs []
  \\ unabbrev_all_tac \\ fs [] \\ tac
  \\ fs [STOP_def] \\ tac \\ fs []
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less] \\ fs []
QED

Theorem word_gc_move_roots_bitmaps_code_thm:
   !bitmaps (s:('a,'c,'b)stackSem$state) i pa curr m dm new
         stack1 a1 i1 pa1 m1 old.
      word_gc_move_roots_bitmaps conf (stack,bitmaps,i,pa,curr,m,dm) =
        (stack1,i1,pa1,m1,T) /\
      LENGTH bitmaps < dimword (:'a) - 1 /\ good_dimindex (:'a) /\
      shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ conf.len_size <> 0 /\ good_dimindex (:'a) /\
      (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
      FLOOKUP s.store CurrHeap = SOME (Word curr) /\ s.use_store /\
      s.memory = m /\ s.mdomain = dm /\ s.bitmaps = bitmaps /\ s.use_stack /\
      0 IN FDOM s.regs /\
      1 IN FDOM s.regs /\
      2 IN FDOM s.regs /\
      get_var 3 s = SOME (Word pa) /\
      get_var 4 s = SOME (Word (i:'a word)) /\
      5 IN FDOM s.regs /\
      6 IN FDOM s.regs /\
      7 IN FDOM s.regs /\
      get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
      get_var 9 s = SOME (HD stack) /\
      s.stack = init ++ old ++ stack /\
      s.stack_space = LENGTH init /\
      (dimindex (:'a) DIV 8) * LENGTH s.stack < dimword (:'a) ==>
      ?ck r0 r1 r2 r5 r6 r7 r8 r9.
        evaluate (word_gc_move_roots_bitmaps_code conf,
            s with clock := s.clock + ck) =
          (NONE,s with <| memory := m1;
                          stack := init ++ old ++ stack1;
                          clock := s.clock;
                          regs := s.regs |++ [(0,r0);
                                              (1,r1);
                                              (2,r2);
                                              (3,Word pa1);
                                              (4,Word i1);
                                              (5,r5);
                                              (6,r6);
                                              (7,r7);
                                              (8,r8);
                                              (9,Word 0w)] |>)
Proof
  completeInduct_on `LENGTH stack`
  \\ rpt strip_tac \\ fs [PULL_FORALL]
  \\ rpt var_eq_tac \\ fs []
  \\ qpat_x_assum `word_gc_move_roots_bitmaps _ _ = _`
        (fn th => assume_tac th \\ mp_tac th)
  \\ drule (GEN_ALL word_gc_move_roots_bitmaps) \\ fs []
  \\ Cases_on `stack` \\ fs []
  \\ rename1 `word_gc_move_roots_bitmaps conf (hd::stack,_) = _`
  \\ Cases_on `hd = Word 0w` \\ fs [] THEN1
   (rpt strip_tac \\ rpt var_eq_tac \\ fs []
    \\ simp_tac std_ss [word_gc_move_roots_bitmaps_code_def,get_var_def]
    \\ fs [get_var_def,get_var_imm_def] \\ tac
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less] \\ fs [])
  \\ Cases_on `word_gc_move_bitmaps conf
       (hd,stack,s.bitmaps,i,pa,curr,s.memory,s.mdomain)` \\ fs []
  \\ PairCases_on `x` \\ fs []
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ fs []
  \\ rpt var_eq_tac \\ fs []
  \\ simp_tac std_ss [word_gc_move_roots_bitmaps_code_def,evaluate_def]
  \\ simp_tac std_ss [GSYM word_gc_move_roots_bitmaps_code_def,get_var_def]
  \\ fs [get_var_def,get_var_imm_def] \\ tac
  \\ reverse (Cases_on `hd`) \\ fs []
  THEN1 (fs[word_gc_move_roots_bitmaps_def,enc_stack_def,full_read_bitmap_def])
  \\ tac
  \\ qabbrev_tac `s2 = s with
      <| clock := s.clock ;
         regs := s.regs |+ (0,Word c) |+ (9,Word (c + -1w)) |+
         (8, Word (bytes_in_word + bytes_in_word * n2w (LENGTH old))) |>`
  \\ `s.memory = s2.memory /\ s.mdomain = s2.mdomain /\ s.bitmaps = s2.bitmaps` by
        (unabbrev_all_tac \\ fs []) \\ fs []
  \\ drule (word_gc_move_bitmaps_code_thm |> SIMP_RULE std_ss [])
  \\ ntac 3 (pop_assum (fn th => fs [GSYM th]))
  \\ disch_then (qspecl_then [`c`,`old ++ [Word c]`] mp_tac)
  \\ impl_tac THEN1
   (unabbrev_all_tac \\ rpt strip_tac
    \\ fs [RIGHT_ADD_DISTRIB]
    \\ rfs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ fs [get_var_def] \\ tac)
  \\ strip_tac \\ fs []
  \\ unabbrev_all_tac \\ fs [] \\ tac
  \\ `(bytes_in_word * n2w (LENGTH old + (LENGTH x0 + 1))) ⋙ word_shift (:α) =
      n2w (LENGTH old + (LENGTH x0 + 1)):'a word` by
   (match_mp_tac bytes_in_word_word_shift_n2w
    \\ imp_res_tac word_gc_move_bitmaps_LENGTH
    \\ rfs [RIGHT_ADD_DISTRIB] \\ fs []) \\ fs []
  \\ `(LENGTH old + (LENGTH x0 + 1)) < dimword (:α)` by
   (imp_res_tac word_gc_move_bitmaps_LENGTH
    \\ rfs [RIGHT_ADD_DISTRIB] \\ fs []
    \\ rfs [labPropsTheory.good_dimindex_def] \\ rfs [] \\ fs[]) \\ fs []
  \\ `0 < LENGTH x1` by
   (Cases_on `x1` \\ fs [word_gc_move_roots_bitmaps_def,enc_stack_def])
  \\ fs [STOP_def] \\ Cases_on `x1` \\ fs []
  \\ `EL (LENGTH init + (LENGTH old + (LENGTH x0 + 1)))
                (init ++ old ++ [Word c] ++ x0 ++ h::t) = h` by
         (match_mp_tac EL_LENGTH_ADD_LEMMA \\ fs []) \\ fs []
  \\ qabbrev_tac `s8 = s with
       <|regs :=
         s.regs |+ (0,Word c) |+ (9,Word (c + -1w)) |+
         (8,Word (bytes_in_word + bytes_in_word * n2w (LENGTH old))) |+
         (0,r0) |+ (1,r1) |+ (2,r2) |+ (3,Word x3) |+ (4,Word x2) |+
         (5,r5) |+ (6,r6) |+ (7,r7) |+
         (8,Word (bytes_in_word * n2w (LENGTH old + (LENGTH x0 + 1)))) |+
         (9,h); stack := init ++ old ++ [Word c] ++ x0 ++ h::t ;
         memory := x4 |>`
  \\ `LENGTH (h::t) < SUC (LENGTH stack)` by
   (imp_res_tac word_gc_move_bitmaps_LENGTH
    \\ rfs [RIGHT_ADD_DISTRIB] \\ fs [])
  \\ first_x_assum drule
  \\ `x4 = s8.memory /\ s.mdomain = s8.mdomain /\ s.bitmaps = s8.bitmaps` by
        (unabbrev_all_tac \\ fs [] \\ NO_TAC) \\ fs []
  \\ disch_then drule
  \\ ntac 3 (pop_assum (fn th => fs [GSYM th]))
  \\ disch_then (qspec_then `old ++ Word c::x0` mp_tac)
  \\ impl_tac THEN1
   (unabbrev_all_tac \\ fs [] \\ tac \\ fs [ADD1,RIGHT_ADD_DISTRIB]
    \\ rfs [] \\ imp_res_tac word_gc_move_bitmaps_LENGTH
    \\ rfs [RIGHT_ADD_DISTRIB] \\ fs []
    \\ rfs [labPropsTheory.good_dimindex_def] \\ rfs [] \\ fs[])
  \\ strip_tac \\ unabbrev_all_tac \\ fs []
  \\ qexists_tac `ck + ck' + 1` \\ fs []
  \\ pop_assum mp_tac
  \\ drule (evaluate_add_clock |> GEN_ALL)
  \\ disch_then (qspec_then `ck' + 1` assume_tac)
  \\ fs [] \\ tac \\ rpt strip_tac
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less] \\ fs []
QED

Theorem alloc_correct_lemma_Simple:
   alloc w (s:('a,'c,'b)stackSem$state) = (r,t) /\ r <> SOME Error /\
    s.gc_fun = word_gc_fun conf /\ conf.gc_kind = Simple /\
    LENGTH s.bitmaps < dimword (:'a) - 1 /\
    LENGTH s.stack * (dimindex (:'a) DIV 8) < dimword (:'a) /\
    FLOOKUP l 0 = SOME ret /\
    FLOOKUP l 1 = SOME (Word w) ==>
    ?ck l2.
      evaluate
        (word_gc_code conf,
         s with
           <| use_store := T; use_stack := T; use_alloc := F;
              clock := s.clock + ck; regs := l; gc_fun := anything;
              code := fromAList (compile c (toAList s.code))|>) =
        (r,
         t with
           <| use_store := T; use_stack := T; use_alloc := F;
              code := fromAList (compile c (toAList s.code));
              regs := l2; gc_fun := anything |>) /\
       (r <> NONE ==> r = SOME (Halt (Word 1w))) /\
       t.regs SUBMAP l2 /\
       (r = NONE ==> FLOOKUP l2 0 = SOME ret)
Proof
  Cases_on `conf.gc_kind = Simple` \\ fs []
  \\ Cases_on `s.gc_fun = word_gc_fun conf` \\ fs [] \\ fs [alloc_def]
  \\ `(set_store AllocSize (Word w) s).gc_fun = word_gc_fun conf` by
        (fs [set_store_def] \\ NO_TAC)
  \\ drule gc_thm
  \\ fs [] \\ disch_then kall_tac
  \\ fs [set_store_def] \\ IF_CASES_TAC THEN1 (fs [] \\ rw [] \\ fs [])
  \\ fs [FAPPLY_FUPDATE_THM]
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ reverse IF_CASES_TAC THEN1 rw [] \\ fs []
  \\ fs [FLOOKUP_UPDATE,FUPDATE_LIST,has_space_def]
  \\ rpt var_eq_tac \\ strip_tac \\ fs [NOT_LESS]
  \\ `{Globals; CurrHeap; OtherHeap; HeapLength} SUBSET FDOM s.store /\
      isWord (s.store ' OtherHeap) /\
      isWord (s.store ' CurrHeap) /\
      isWord (s.store ' HeapLength) /\
      good_dimindex (:'a) /\
      conf.len_size + 2 < dimindex (:'a) /\
      shift_length conf < dimindex (:'a) /\
      conf.len_size <> 0` by
        (fs [word_gc_fun_assum_def,set_store_def,FAPPLY_FUPDATE_THM] \\ NO_TAC)
  \\ `word_shift (:'a) < dimindex (:'a) /\ 2 < dimindex (:'a) /\
      !w:'a word. w ≪ word_shift (:'a) = w * bytes_in_word` by
   (fs [word_shift_def,bytes_in_word_def,labPropsTheory.good_dimindex_def]
    \\ fs [WORD_MUL_LSL] \\ NO_TAC)
  \\ fs [isWord_thm] \\ fs [theWord_def]
  \\ rename1 `s.store ' OtherHeap = Word other`
  \\ rename1 `s.store ' CurrHeap = Word curr`
  \\ rename1 `s.store ' HeapLength = Word len`
  \\ fs [word_gc_code_def,list_Seq_def] \\ tac
  \\ fs [set_store_def,FLOOKUP_UPDATE] \\ tac
  \\ fs [FLOOKUP_DEF] \\ rfs []
  \\ imp_res_tac word_gc_move_loop_ok
  \\ fs [] \\ rpt var_eq_tac \\ fs []
  \\ abbrev_under_exists ``s3:('a,'c,'b)stackSem$state``
   (qexists_tac `0` \\ fs []
    \\ qpat_abbrev_tac `(s3:('a,'c,'b)stackSem$state) = _`)
  \\ drule (GEN_ALL word_gc_move_code_thm)
  \\ disch_then (qspec_then `s3` mp_tac)
  \\ impl_tac THEN1
   (unabbrev_all_tac \\ fs [] \\ tac
    \\ fs [FAPPLY_FUPDATE_THM,FLOOKUP_DEF])
  \\ strip_tac \\ fs []
  \\ `s.stack_space < LENGTH s.stack` by
   (CCONTR_TAC \\ fs [NOT_LESS]
    \\ imp_res_tac DROP_LENGTH_TOO_LONG
    \\ fs [word_gc_move_roots_bitmaps_def,enc_stack_def] \\ NO_TAC)
  \\ abbrev_under_exists ``s4:('a,'c,'b)stackSem$state``
   (qexists_tac `ck` \\ fs []
    \\ unabbrev_all_tac \\ fs [] \\ tac
    \\ fs [FAPPLY_FUPDATE_THM]
    \\ qpat_abbrev_tac `(s4:('a,'c,'b)stackSem$state) = _`)
  \\ qpat_x_assum `word_gc_move_roots_bitmaps _ _ = _` assume_tac
  \\ drule LESS_EQ_LENGTH
  \\ strip_tac \\ fs []
  \\ `DROP s.stack_space (ys1 ++ ys2) = ys2` by
       metis_tac [DROP_LENGTH_APPEND] \\ fs []
  \\ drule (GEN_ALL word_gc_move_roots_bitmaps_code_thm
           |> REWRITE_RULE [GSYM AND_IMP_INTRO])
  \\ fs [AND_IMP_INTRO]
  \\ disch_then (qspecl_then [`ys1`,`s4`,`[]`] mp_tac)
  \\ impl_tac THEN1
    (fs [] \\ unabbrev_all_tac \\ fs [get_var_def,FLOOKUP_UPDATE]
     \\ fs [FLOOKUP_DEF] \\ Cases_on `ys2` \\ fs []
     \\ metis_tac [EL_LENGTH_APPEND,NULL,HD])
  \\ strip_tac \\ fs [FAPPLY_FUPDATE_THM]
  \\ pop_assum mp_tac
  \\ drule (GEN_ALL evaluate_add_clock)
  \\ disch_then (qspec_then `ck'` mp_tac)
  \\ fs [] \\ rpt strip_tac
  \\ abbrev_under_exists ``s5:('a,'c,'b)stackSem$state``
   (qexists_tac `ck+ck'` \\ fs []
    \\ unabbrev_all_tac \\ fs [] \\ tac
    \\ fs [FAPPLY_FUPDATE_THM]
    \\ qpat_abbrev_tac `(s5:('a,'c,'b)stackSem$state) = _`)
  \\ drule (GEN_ALL word_gc_move_loop_code_thm
           |> REWRITE_RULE [GSYM AND_IMP_INTRO])
  \\ fs [AND_IMP_INTRO]
  \\ disch_then (qspec_then `s5` mp_tac)
  \\ impl_tac THEN1
    (fs [] \\ unabbrev_all_tac \\ fs [get_var_def,FLOOKUP_UPDATE]
     \\ fs [FLOOKUP_DEF,FDOM_FUPDATE,FUPDATE_LIST,FAPPLY_FUPDATE_THM])
  \\ strip_tac \\ pop_assum mp_tac
  \\ drule (GEN_ALL evaluate_add_clock)
  \\ disch_then (qspec_then `ck''` mp_tac)
  \\ qpat_x_assum `evaluate _ = _` kall_tac
  \\ drule (GEN_ALL evaluate_add_clock)
  \\ disch_then (qspec_then `ck''` mp_tac)
  \\ rpt strip_tac \\ fs []
  \\ qexists_tac `ck+ck'+ck''` \\ fs []
  \\ unabbrev_all_tac \\ fs [] \\ tac
  \\ fs [FAPPLY_FUPDATE_THM,FUPDATE_LIST]
  \\ fs [labSemTheory.word_cmp_def]
  \\ IF_CASES_TAC \\ fs [WORD_LO,GSYM NOT_LESS]
  \\ fs [empty_env_def,state_component_equality]
  \\ rpt var_eq_tac \\ fs []
  \\ fs [FAPPLY_FUPDATE_THM,FUPDATE_LIST]
  \\ rpt (qpat_x_assum `evaluate _ = _` kall_tac)
  \\ qpat_x_assum `_ = t.store` (fn th => fs [GSYM th])
  \\ `TAKE t.stack_space (ys1 ++ ys2) = ys1` by metis_tac [TAKE_LENGTH_APPEND]
  \\ fs [fmap_EXT,EXTENSION]
  \\ rw [] \\ fs [FAPPLY_FUPDATE_THM]
  \\ fs [SUBMAP_DEF] \\ rw [] \\ fs [] \\ eq_tac \\ strip_tac \\ fs []
QED

(* gc_kind = Generational *)

val kind = ``Generational gen_sizes``

val word_gc_fun_lemma =
  word_gc_fun_def
  |> SPEC_ALL
  |> DISCH ``conf.gc_kind = ^kind``
  |> SIMP_RULE std_ss [TypeBase.case_def_of ``:gc_kind`` ]
  |> SIMP_RULE std_ss [word_gen_gc_def]
  |> SIMP_RULE std_ss [Once LET_THM]
  |> SIMP_RULE std_ss [Once LET_THM]
  |> SIMP_RULE std_ss [Once LET_THM]
  |> SIMP_RULE std_ss [Once LET_THM]
  |> SIMP_RULE std_ss [Once LET_THM,word_gen_gc_move_roots_def]

val word_gc_fun_thm = Q.prove(
  `conf.gc_kind = ^kind ==>
   word_gc_fun conf (roots,m,dm,s) =
     if ¬word_gc_fun_assum conf s then NONE else
     if word_gen_gc_can_do_partial gen_sizes s then
       (λ(roots1,i1,pa1,m1,c2).
          if c2 /\ theWord (s ' AllocSize) ≤₊ -1w * pa1 + theWord (s ' EndOfHeap)
                /\ theWord (s ' AllocSize) ≤₊ new_trig
                     (theWord (s ' EndOfHeap) - pa1)
                     (theWord (s ' AllocSize)) gen_sizes then
            SOME
              (TL roots1,m1,
               s |++
               [(CurrHeap,Word (theWord (s ' CurrHeap)));
                (OtherHeap,Word (theWord (s ' OtherHeap)));
                (NextFree,Word pa1);
                (GenStart,Word (pa1 + -1w * theWord (s ' CurrHeap)));
                (TriggerGC,Word (pa1 + new_trig (theWord (s ' EndOfHeap) - pa1)
                                         (theWord (s ' AllocSize)) gen_sizes));
                (Globals,HD roots1);
                (Temp 0w,Word 0w); (Temp 1w,Word 0w)])
          else NONE)
         ((λ(roots,i,pa,m,c1).
             (λ(b1,m,c2). (roots,i,b1,m,c1 ∧ c2))
               (memcpy
                  ((pa + -1w * theWord (s ' OtherHeap)) ⋙ shift (:α))
                  (theWord (s ' OtherHeap))
                  (theWord (s ' CurrHeap) + theWord (s ' GenStart)) m
                  dm))
            ((λ(roots,i,pa,m,c1).
                (λ(i,pa,m,c2).
                   (λ(i,pa,m,c3). (roots,i,pa,m,c2 ∧ c3))
                     (word_gen_gc_partial_move_data conf (dimword (:α))
                        (theWord (s ' OtherHeap),i,pa,
                         theWord (s ' CurrHeap),m,dm,
                         theWord (s ' GenStart),
                         -1w * theWord (s ' CurrHeap) +
                         theWord (s ' EndOfHeap))))
                  (word_gen_gc_partial_move_ref_list (dimword (:α)) conf
                     (theWord (s ' EndOfHeap),i,pa,
                      theWord (s ' CurrHeap),m,dm,c1,
                      theWord (s ' GenStart),
                      -1w * theWord (s ' CurrHeap) +
                      theWord (s ' EndOfHeap),
                      theWord (s ' CurrHeap) +
                      theWord (s ' HeapLength))))
               (word_gen_gc_partial_move_roots conf
                  (s ' Globals::roots,
                   theWord (s ' GenStart) ⋙ shift (:α),
                   theWord (s ' OtherHeap),theWord (s ' CurrHeap),m,dm,
                   theWord (s ' GenStart),
                   -1w * theWord (s ' CurrHeap) +
                   theWord (s ' EndOfHeap)))))
     else
      (let new_end = theWord (s ' OtherHeap) + theWord (s ' HeapLength) in
       let len = theWord (s ' HeapLength) ⋙ shift (:α) in
       let (w1,i1,pa1,ib',pb',m1,c1) =
              word_gen_gc_move conf
                (s ' Globals,0w,theWord (s ' OtherHeap),
                 len,new_end,theWord (s ' CurrHeap),m,dm) in
       let (ws2,i2,pa2,ib2,pb2:'a word,m2,c2) =
              word_gen_gc_move_roots conf
                (roots,i1,pa1,ib',pb',
                 theWord (s ' CurrHeap),m1,dm) in
       let (i3,pa3,ib3,pb3,m3,c3) =
             word_gen_gc_move_loop conf (w2n len)
               (theWord (s ' OtherHeap),i2,pa2,ib2,pb2,new_end,
                theWord (s ' CurrHeap),m2,dm) in
       let a = theWord (s ' AllocSize) in
       let s1 =
             s |++
             [(CurrHeap,Word (theWord (s ' OtherHeap)));
              (OtherHeap,Word (theWord (s ' CurrHeap)));
              (NextFree,Word pa3);
              (GenStart,Word (pa3 − theWord (s ' OtherHeap)));
              (TriggerGC,Word (pa3 + new_trig (pb3 - pa3) a gen_sizes));
              (EndOfHeap,Word pb3); (Globals,w1);
              (Temp 0w,Word 0w);
              (Temp 1w,Word 0w);
              (Temp 2w,Word 0w);
              (Temp 3w,Word 0w);
              (Temp 4w,Word 0w);
              (Temp 5w,Word 0w);
              (Temp 6w,Word 0w)]
       in
         if word_gc_fun_assum conf s /\ c1 /\ c2 /\ c3
         then SOME (ws2,m3,s1)
         else NONE)`,
  strip_tac
  \\ drule word_gc_fun_lemma
  \\ disch_then (fn th => rewrite_tac [th])
  \\ full_simp_tac(srw_ss())[LET_THM]
  \\ Cases_on `word_gc_fun_assum conf s` \\ fs []
  \\ Cases_on `word_gen_gc_can_do_partial gen_sizes s` \\ fs []
  THEN1 (fs [word_gen_gc_partial_full_def,word_gen_gc_partial_def]
         \\ fs [word_gc_fun_assum_def,isWord_thm,theWord_def])
  \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]);

val gc_lemma = gc_def
  |> SPEC_ALL
  |> DISCH ``s.gc_fun = word_gc_fun conf``
  |> SIMP_RULE std_ss [] |> UNDISCH
  |> DISCH ``conf.gc_kind = ^kind``
  |> SIMP_RULE std_ss [word_gc_fun_thm] |> DISCH_ALL

val word_gen_gc_move_roots_bitmaps_def = Define `
  word_gen_gc_move_roots_bitmaps conf (stack,bitmaps,i1,pa1,ib1,pb1,curr,m,dm) =
    case enc_stack bitmaps stack of
    | NONE => (ARB,ARB,ARB,ARB,ARB,ARB,F)
    | SOME wl_list =>
        let (wl,i2,pa2,ib2,pb2,m2,c2) =
            word_gen_gc_move_roots conf (wl_list,i1,pa1,ib1,pb1,curr,m,dm) in
          case dec_stack bitmaps wl stack of
          | NONE => (ARB,ARB,ARB,ARB,ARB,ARB,F)
          | SOME stack => (stack,i2,pa2,ib2,pb2,m2,c2)`

val word_gen_gc_partial_move_roots_bitmaps_def = Define `
  word_gen_gc_partial_move_roots_bitmaps conf (stack,bitmaps,i1,pa1,curr,m,dm,gs,rs) =
    case enc_stack bitmaps stack of
    | NONE => (ARB,ARB,ARB,ARB,F)
    | SOME wl_list =>
        let (wl,i2,pa2,m2,c2) =
            word_gen_gc_partial_move_roots conf (wl_list,i1,pa1,curr,m,dm,gs,rs) in
          case dec_stack bitmaps wl stack of
          | NONE => (ARB,ARB,ARB,ARB,F)
          | SOME stack => (stack,i2,pa2,m2,c2)`

val word_gen_gc_partial_move_ref_list_ok = prove(
  ``!k rs re pb pa old m i gs dm conf c i1 pa1 m1.
      word_gen_gc_partial_move_ref_list k conf
       (pb,i,pa,old,m,dm,c,gs,rs,re) = (i1,pa1,m1,T) ==> c``,
  Induct
  THEN1 (once_rewrite_tac [word_gen_gc_partial_move_ref_list_def]
         \\ fs [] \\ rw [])
  \\ once_rewrite_tac [word_gen_gc_partial_move_ref_list_def]
  \\ simp_tac std_ss [ADD1]
  \\ rpt gen_tac \\ IF_CASES_TAC
  \\ simp_tac std_ss [ADD1,LET_THM]
  \\ pairarg_tac
  \\ res_tac
  \\ asm_rewrite_tac [] \\ simp_tac std_ss []
  \\ strip_tac \\ res_tac);

val gc_thm = Q.prove(
  `s.gc_fun = word_gc_fun conf /\ conf.gc_kind = ^kind ==>
   gc (s:('a,'c,'b)stackSem$state) =
   if LENGTH s.stack < s.stack_space then NONE else
     if ¬word_gc_fun_assum conf s.store then NONE else
     if word_gen_gc_can_do_partial gen_sizes s.store then
      (let unused = TAKE s.stack_space s.stack in
       let stack = DROP s.stack_space s.stack in
       let gs = theWord (s.store ' GenStart) in
       let other = theWord (s.store ' OtherHeap) in
       let curr = theWord (s.store ' CurrHeap) in
       let endh = theWord (s.store ' EndOfHeap) in
       let (w1,i1,pa1,m1,c1) = word_gen_gc_partial_move conf
              (s.store ' Globals,gs ⋙ shift (:α), other,curr,
               s.memory,s.mdomain,gs, endh - curr) in
       let (ws2,i1,pa1,m1,c2) = word_gen_gc_partial_move_roots_bitmaps conf
              (stack,s.bitmaps,i1,pa1,curr,m1,s.mdomain,gs,endh - curr) in
       let (i1,pa1,m1,c3) =
              word_gen_gc_partial_move_ref_list (dimword (:α)) conf
               (endh,i1,pa1,curr,m1,s.mdomain,c1 ∧ c2,gs,
                endh - curr, curr +theWord (s.store ' HeapLength)) in
       let (i1,pa1,m1,c4) = word_gen_gc_partial_move_data conf (dimword (:α))
               (other,i1,pa1,curr,m1,s.mdomain,gs, endh - curr) in
       let (b1,m1,c5) = memcpy ((pa1 - other) ⋙ shift (:α)) other (curr + gs) m1
                         s.mdomain in
       let s1 = s.store |++
                [(CurrHeap,Word curr);
                 (OtherHeap,Word other);
                 (NextFree,Word b1);
                 (GenStart,Word (b1 - curr));
                 (TriggerGC,Word (b1 + new_trig
                    (theWord (s.store ' EndOfHeap) - b1)
                    (theWord (s.store ' AllocSize)) gen_sizes));
                 (Globals,w1);
                 (Temp 0w,Word 0w);
                 (Temp 1w,Word 0w)] in
       let c6 = ((theWord (s.store ' AllocSize) ≤₊
                  theWord (s.store ' EndOfHeap) - b1) /\
                 (theWord (s.store ' AllocSize) ≤₊ new_trig
                    (theWord (s.store ' EndOfHeap) - b1)
                    (theWord (s.store ' AllocSize)) gen_sizes)) in
         if word_gc_fun_assum conf s.store /\ c3 /\ c4 /\ c5 /\ c6
         then SOME (s with
              <| stack := unused ++ ws2; store := s1;
                 regs := FEMPTY; memory := m1|>) else NONE)
     else
      (let unused = TAKE s.stack_space s.stack in
       let stack = DROP s.stack_space s.stack in
       let new_end = theWord (s.store ' OtherHeap) + theWord (s.store ' HeapLength) in
       let len = theWord (s.store ' HeapLength) ⋙ shift (:α) in
       let (w1,i1,pa1,ib',pb',m1,c1) =
                word_gen_gc_move conf
                  (s.store ' Globals,0w,theWord (s.store ' OtherHeap),
                   len,new_end,theWord (s.store ' CurrHeap),s.memory,s.mdomain) in
       let (ws2,i2,pa2,ib2,pb2:'a word,m2,c2) =
                word_gen_gc_move_roots_bitmaps conf
                  (stack,s.bitmaps,i1,pa1,ib',pb',
                   theWord (s.store ' CurrHeap),m1,s.mdomain) in
       let (i3,pa3,ib3,pb3,m3,c3) =
               word_gen_gc_move_loop conf (w2n len)
                 (theWord (s.store ' OtherHeap),i2,pa2,ib2,pb2,new_end,
                  theWord (s.store ' CurrHeap),m2,s.mdomain) in
       let s1 =
               s.store |++
               [(CurrHeap,Word (theWord (s.store ' OtherHeap)));
                (OtherHeap,Word (theWord (s.store ' CurrHeap)));
                (NextFree,Word pa3);
                (GenStart,Word (pa3 + -1w * theWord (s.store ' OtherHeap)));
                (TriggerGC,Word (pa3 + new_trig
                   (pb3 - pa3) (theWord (s.store ' AllocSize)) gen_sizes));
                (EndOfHeap,Word pb3);
                (Globals,w1);
                (Temp 0w, Word 0w);
                (Temp 1w, Word 0w);
                (Temp 2w, Word 0w);
                (Temp 3w, Word 0w);
                (Temp 4w, Word 0w);
                (Temp 5w, Word 0w);
                (Temp 6w, Word 0w)]
       in
         if word_gc_fun_assum conf s.store /\ c1 /\ c2 /\ c3 then SOME (s with
              <| stack := unused ++ ws2; store := s1;
                 regs := FEMPTY; memory := m3|>) else NONE)`,
  strip_tac \\ drule gc_lemma \\ fs []
  \\ disch_then (fn th => full_simp_tac(srw_ss())[th])
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  \\ reverse (Cases_on `word_gc_fun_assum conf s.store`) \\ fs []
  THEN1 (TOP_CASE_TAC \\ fs [] \\ fs [word_gc_fun_def])
  \\ Cases_on `word_gen_gc_can_do_partial gen_sizes s.store` \\ fs []
  THEN1
   (full_simp_tac(srw_ss())[LET_THM,word_gen_gc_partial_move_roots_bitmaps_def]
    \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
    THEN1 (rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
           \\ CCONTR_TAC \\ fs [] \\ rveq \\ fs []
           \\ imp_res_tac word_gen_gc_partial_move_ref_list_ok \\ fs [])
    \\ fs [UNDISCH word_gc_fun_thm,word_gen_gc_partial_move_roots_def]
    \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
    \\ ntac 6 (rpt (CASE_TAC \\ fs []) \\ rveq \\ fs [])
    \\ CCONTR_TAC \\ fs [] \\ rveq \\ fs []
    \\ every_case_tac \\ fs [] \\ rveq \\ fs []
    \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac word_gen_gc_partial_move_ref_list_ok \\ fs []
    \\ fs [] \\ rveq \\ fs [])
  \\ full_simp_tac(srw_ss())[LET_THM,word_gen_gc_move_roots_bitmaps_def]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  THEN1 (rpt (pairarg_tac \\ full_simp_tac(srw_ss())[]))
  \\ fs [UNDISCH word_gc_fun_thm]
  \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
  \\ rpt (CASE_TAC \\ fs []) \\ rveq \\ fs []
  \\ every_case_tac \\ fs [] \\ rveq);

val word_gen_gc_move_bitmaps_def = Define `
  word_gen_gc_move_bitmaps conf (w,stack,bitmaps,i1,pa1,ib1,pb1,curr,m,dm) =
    case full_read_bitmap bitmaps w of
    | NONE => NONE
    | SOME bs =>
      case filter_bitmap bs stack of
      | NONE => NONE
      | SOME (ts,ws) =>
        let (wl,i2,pa2,ib2,pb2,m2,c2) =
                word_gen_gc_move_roots conf (ts,i1,pa1,ib1,pb1,curr,m,dm) in
          case map_bitmap bs wl stack of
          | NONE => NONE
          | SOME (hd,ts1,ws') =>
              SOME (hd,ws,i2,pa2,ib2,pb2,m2,c2)`

val word_gen_gc_partial_move_bitmaps_def = Define `
  word_gen_gc_partial_move_bitmaps conf (w,stack,bitmaps,i1,pa1,curr,m,dm,gs,rs) =
    case full_read_bitmap bitmaps w of
    | NONE => NONE
    | SOME bs =>
      case filter_bitmap bs stack of
      | NONE => NONE
      | SOME (ts,ws) =>
        let (wl,i2,pa2,m2,c2) =
                word_gen_gc_partial_move_roots conf (ts,i1,pa1,curr,m,dm,gs,rs) in
          case map_bitmap bs wl stack of
          | NONE => NONE
          | SOME (hd,ts1,ws') =>
              SOME (hd,ws,i2,pa2,m2,c2)`

val word_gen_gc_move_roots_APPEND = Q.prove(
  `!xs ys i1 pa1 ib1 pb1 m.
      word_gen_gc_move_roots conf (xs++ys,i1,pa1,ib1,pb1,curr,m,dm) =
        let (ws1,i1,pa1,ib1,pb1,m1,c1) =
          word_gen_gc_move_roots conf (xs,i1,pa1,ib1,pb1,curr,m,dm) in
        let (ws2,i2,pa2,ib2,pb2,m2,c2) =
          word_gen_gc_move_roots conf (ys,i1,pa1,ib1,pb1,curr,m1,dm) in
            (ws1++ws2,i2,pa2,ib2,pb2,m2,c1 /\ c2)`,
  Induct \\ full_simp_tac(srw_ss())[word_gen_gc_move_roots_def,LET_THM]
  \\ srw_tac[][] \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ rveq \\ fs[] \\ EQ_TAC \\ fs[] \\ rw[]);

val word_gen_gc_partial_move_roots_APPEND = Q.prove(
  `!xs ys i1 pa1 ib1 pb1 m.
      word_gen_gc_partial_move_roots conf (xs++ys,i1,pa1,curr,m,dm,gs,rs) =
        let (ws1,i1,pa1,m1,c1) =
          word_gen_gc_partial_move_roots conf (xs,i1,pa1,curr,m,dm,gs,rs) in
        let (ws2,i2,pa2,m2,c2) =
          word_gen_gc_partial_move_roots conf (ys,i1,pa1,curr,m1,dm,gs,rs) in
            (ws1++ws2,i2,pa2,m2,c1 /\ c2)`,
  Induct \\ full_simp_tac(srw_ss())[word_gen_gc_partial_move_roots_def,LET_THM]
  \\ srw_tac[][] \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ rveq \\ fs[] \\ EQ_TAC \\ fs[] \\ rw[]);

Theorem word_gen_gc_move_roots_IMP_LENGTH:
   !xs r0 r1 r3 r4 curr r2 dm ys i2 pa2 m2 c conf ib2 pb2.
      word_gen_gc_move_roots conf (xs,r0,r1,r3,r4,curr,r2,dm) =
         (ys,i2,pa2,ib2,pb2,m2,c) ==>
      LENGTH ys = LENGTH xs
Proof
  Induct \\ full_simp_tac(srw_ss())[word_gen_gc_move_roots_def,LET_THM]
  \\ srw_tac[][]
  \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[] \\ res_tac
QED

Theorem word_gen_gc_partial_move_roots_IMP_LENGTH:
   !xs r0 r1 r3 r4 curr r2 dm ys i2 pa2 m2 c conf.
      word_gen_gc_partial_move_roots conf (xs,r0,r1,curr,r2,dm,r3,r4) =
         (ys,i2,pa2,m2,c) ==>
      LENGTH ys = LENGTH xs
Proof
  Induct \\ full_simp_tac(srw_ss())[word_gen_gc_partial_move_roots_def,LET_THM]
  \\ srw_tac[][]
  \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[] \\ res_tac
QED

val word_gen_gc_move_roots_bitmaps = Q.prove(
  `!stack i1 pa1 m stack2 i2 pa2 m2.
      (word_gen_gc_move_roots_bitmaps conf (stack,bitmaps,i1,pa1,ib1,pb1,curr,m,dm) =
        (stack2,i2,pa2,ib2,pb2,m2,T)) ==>
      word_gen_gc_move_roots_bitmaps conf (stack,bitmaps,i1,pa1,ib1,pb1,curr,m,dm) =
      case stack of
      | [] => (ARB,ARB,ARB,ARB,ARB,ARB,F)
      | (w::ws) =>
        if w = Word 0w then (stack,i1,pa1,ib1,pb1,m,ws = []) else
          case word_gen_gc_move_bitmaps conf (w,ws,bitmaps,i1,pa1,ib1,pb1,curr,m,dm) of
          | NONE => (ARB,ARB,ARB,ARB,ARB,ARB,F)
          | SOME (new,stack,i2,pa2,ib2,pb2,m2,c2) =>
              let (stack,i,pa,ib1,pb1,m,c3) =
                word_gen_gc_move_roots_bitmaps conf
                  (stack,bitmaps,i2,pa2,ib2,pb2,curr,m2,dm) in
                    (w::new++stack,i,pa,ib1,pb1,m,c2 /\ c3)`,
  Cases THEN1 (full_simp_tac(srw_ss())[word_gen_gc_move_roots_bitmaps_def,
                 enc_stack_def])
  \\ rpt strip_tac \\ pop_assum mp_tac \\ full_simp_tac(srw_ss())[]
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  THEN1 (full_simp_tac(srw_ss())[word_gen_gc_move_roots_bitmaps_def,enc_stack_def]
         \\ IF_CASES_TAC
         \\ full_simp_tac(srw_ss())[word_gen_gc_move_roots_def,LET_THM,dec_stack_def])
  \\ full_simp_tac(srw_ss())[word_gen_gc_move_roots_bitmaps_def,
        word_gen_gc_move_bitmaps_def,enc_stack_def]
  \\ Cases_on `full_read_bitmap bitmaps h` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `filter_bitmap x t` \\ full_simp_tac(srw_ss())[]
  \\ rename1 `_ = SOME filter_res` \\ PairCases_on `filter_res` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `enc_stack bitmaps filter_res1` \\ full_simp_tac(srw_ss())[]
  \\ rename1 `_ = SOME enc_rest` \\ full_simp_tac(srw_ss())[word_gen_gc_move_roots_APPEND]
  \\ simp [Once LET_DEF]
  \\ Cases_on `word_gen_gc_move_roots conf (filter_res0,i1,pa1,ib1,pb1,curr,m,dm)` \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `r` \\ full_simp_tac(srw_ss())[dec_stack_def]
  \\ Cases_on `word_gen_gc_move_roots conf (enc_rest,r0,r1,r2,r3,curr,r4,dm)` \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `r` \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ rename1 `_ = SOME map_rest` \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `map_rest` \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac word_gen_gc_move_roots_IMP_LENGTH \\ full_simp_tac(srw_ss())[]
  \\ drule (GEN_ALL map_bitmap_APPEND) \\ full_simp_tac(srw_ss())[]
  \\ disch_then (mp_tac o SPEC_ALL) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[] \\ pop_assum kall_tac
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ rename1 `_ = SOME z` \\ full_simp_tac(srw_ss())[] \\ PairCases_on `z` \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac word_gen_gc_move_roots_IMP_LENGTH \\ full_simp_tac(srw_ss())[]
  \\ drule filter_bitmap_map_bitmap
  \\ disch_then drule \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]);

val word_gen_gc_partial_move_roots_bitmaps = Q.prove(
  `!stack i1 pa1 m stack2 i2 pa2 m2.
      (word_gen_gc_partial_move_roots_bitmaps conf
        (stack,bitmaps,i1,pa1,curr,m,dm,gs,rs) =
          (stack2,i2,pa2,m2,T)) ==>
      word_gen_gc_partial_move_roots_bitmaps conf
        (stack,bitmaps,i1,pa1,curr,m,dm,gs,rs) =
      case stack of
      | [] => (ARB,ARB,ARB,ARB,F)
      | (w::ws) =>
        if w = Word 0w then (stack,i1,pa1,m,ws = []) else
          case word_gen_gc_partial_move_bitmaps conf (w,ws,bitmaps,i1,pa1,curr,m,dm,gs,rs) of
          | NONE => (ARB,ARB,ARB,ARB,F)
          | SOME (new,stack,i2,pa2,m2,c2) =>
              let (stack,i,pa,m,c3) =
                word_gen_gc_partial_move_roots_bitmaps conf
                  (stack,bitmaps,i2,pa2,curr,m2,dm,gs,rs) in
                    (w::new++stack,i,pa,m,c2 /\ c3)`,
  Cases THEN1 (full_simp_tac(srw_ss())[word_gen_gc_partial_move_roots_bitmaps_def,
                 enc_stack_def])
  \\ rpt strip_tac \\ pop_assum mp_tac \\ full_simp_tac(srw_ss())[]
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  THEN1 (full_simp_tac(srw_ss())[word_gen_gc_partial_move_roots_bitmaps_def,enc_stack_def]
         \\ IF_CASES_TAC
         \\ full_simp_tac(srw_ss())[word_gen_gc_partial_move_roots_def,LET_THM,dec_stack_def])
  \\ full_simp_tac(srw_ss())[word_gen_gc_partial_move_roots_bitmaps_def,
        word_gen_gc_partial_move_bitmaps_def,enc_stack_def]
  \\ Cases_on `full_read_bitmap bitmaps h` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `filter_bitmap x t` \\ full_simp_tac(srw_ss())[]
  \\ rename1 `_ = SOME filter_res` \\ PairCases_on `filter_res` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `enc_stack bitmaps filter_res1` \\ full_simp_tac(srw_ss())[]
  \\ rename1 `_ = SOME enc_rest` \\ full_simp_tac(srw_ss())[word_gen_gc_partial_move_roots_APPEND]
  \\ simp [Once LET_DEF]
  \\ Cases_on `word_gen_gc_partial_move_roots conf (filter_res0,i1,pa1,curr,m,dm,gs,rs)` \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `r` \\ full_simp_tac(srw_ss())[dec_stack_def]
  \\ Cases_on `word_gen_gc_partial_move_roots conf (enc_rest,r0,r1,curr,r2,dm,gs,rs)` \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `r` \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ rename1 `_ = SOME map_rest` \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `map_rest` \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac word_gen_gc_partial_move_roots_IMP_LENGTH \\ full_simp_tac(srw_ss())[]
  \\ drule (GEN_ALL map_bitmap_APPEND) \\ full_simp_tac(srw_ss())[]
  \\ disch_then (mp_tac o SPEC_ALL) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[] \\ pop_assum kall_tac
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ rename1 `_ = SOME z` \\ full_simp_tac(srw_ss())[] \\ PairCases_on `z` \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac word_gen_gc_partial_move_roots_IMP_LENGTH \\ full_simp_tac(srw_ss())[]
  \\ drule filter_bitmap_map_bitmap
  \\ disch_then drule \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]);

val word_gen_gc_move_bitmap_def = Define `
  word_gen_gc_move_bitmap conf (w,stack,i1,pa1,ib1,pb1,curr,m,dm) =
    let bs = get_bits w in
      case filter_bitmap bs stack of
      | NONE => NONE
      | SOME (ts,ws) =>
         let (wl,i2,pa2,ib2,pb2,m2,c2) =
           word_gen_gc_move_roots conf (ts,i1,pa1,ib1,pb1,curr,m,dm) in
           case map_bitmap bs wl stack of
           | NONE => NONE
           | SOME (hd,v2) => SOME (hd,ws,i2,pa2,ib2,pb2,m2,c2)`

val word_gen_gc_partial_move_bitmap_def = Define `
  word_gen_gc_partial_move_bitmap conf (w,stack,i1,pa1,curr,m,dm,gs,rs) =
    let bs = get_bits w in
      case filter_bitmap bs stack of
      | NONE => NONE
      | SOME (ts,ws) =>
         let (wl,i2,pa2,m2,c2) =
           word_gen_gc_partial_move_roots conf (ts,i1,pa1,curr,m,dm,gs,rs) in
           case map_bitmap bs wl stack of
           | NONE => NONE
           | SOME (hd,v2) => SOME (hd,ws,i2,pa2,m2,c2)`

val map_bitmap_APPEND_APPEND = Q.prove(
  `!vs1 stack x0 x1 ws2 vs2 ws1.
      filter_bitmap vs1 stack = SOME (x0,x1) /\
      LENGTH x0 = LENGTH ws1 ==>
      map_bitmap (vs1 ++ vs2) (ws1 ++ ws2) stack =
      case map_bitmap vs1 ws1 stack of
      | NONE => NONE
      | SOME (ts1,ts2,ts3) =>
        case map_bitmap vs2 ws2 ts3 of
        | NONE => NONE
        | SOME (us1,us2,us3) => SOME (ts1++us1,ts2++us2,us3)`,
  Induct \\ full_simp_tac(srw_ss())[map_bitmap_def] THEN1
   (Cases \\ full_simp_tac(srw_ss())[filter_bitmap_def]
    \\ once_rewrite_tac [EQ_SYM_EQ] \\ full_simp_tac(srw_ss())[LENGTH_NIL]
    \\ srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ Cases_on `stack` \\ full_simp_tac(srw_ss())[filter_bitmap_def]
  \\ reverse Cases \\ full_simp_tac(srw_ss())[filter_bitmap_def,map_bitmap_def]
  THEN1 (srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `ws1` \\ full_simp_tac(srw_ss())[LENGTH,map_bitmap_def]
  \\ srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  |> SIMP_RULE std_ss [];

val word_gen_gc_move_bitmaps_Loc =
  ``word_gen_gc_move_bitmaps conf (Loc l1 l2,stack,bitmaps,i1,pa1,ib1,pb1,curr,m,dm)``
  |> SIMP_CONV std_ss [word_gen_gc_move_bitmaps_def,full_read_bitmap_def];

val word_gen_gc_partial_move_bitmaps_Loc =
  ``word_gen_gc_partial_move_bitmaps conf (Loc l1 l2,stack,bitmaps,i1,pa1,curr,m,dm,gs,rs)``
  |> SIMP_CONV std_ss [word_gen_gc_partial_move_bitmaps_def,full_read_bitmap_def];

val word_gen_gc_move_bitmaps_unroll = Q.prove(
  `word_gen_gc_move_bitmaps conf (Word w,stack,bitmaps,i1,pa1,ib1,pb1,curr,m,dm) = SOME x /\
    LENGTH bitmaps < dimword (:'a) - 1 /\ good_dimindex (:'a) ==>
    word_gen_gc_move_bitmaps conf (Word w,stack,bitmaps,i1,pa1,ib1,pb1,curr,m,dm) =
    case DROP (w2n (w - 1w:'a word)) bitmaps of
    | [] => NONE
    | (y::ys) =>
      case word_gen_gc_move_bitmap conf (y,stack,i1,pa1,ib1,pb1,curr,m,dm) of
      | NONE => NONE
      | SOME (hd,ws,i2,pa2,ib2,pb2,m2,c2) =>
          if ~(word_msb y) then SOME (hd,ws,i2,pa2,ib2,pb2,m2,c2) else
            case word_gen_gc_move_bitmaps conf (Word (w+1w),ws,bitmaps,i2,pa2,ib2,pb2,curr,m2,dm) of
            | NONE => NONE
            | SOME (hd3,ws3,i3,pa3,ib3,pb3,m3,c3) =>
                SOME (hd++hd3,ws3,i3,pa3,ib3,pb3,m3,c2 /\ c3)`,
  full_simp_tac(srw_ss())[word_gen_gc_move_bitmaps_def,full_read_bitmap_def]
  \\ Cases_on `w = 0w` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `DROP (w2n (w + -1w)) bitmaps`
  \\ full_simp_tac(srw_ss())[read_bitmap_def]
  \\ reverse (Cases_on `word_msb h`)
  THEN1
   (full_simp_tac(srw_ss())[word_gen_gc_move_bitmap_def,get_bits_def,LET_THM]
    \\ CASE_TAC \\ rename1 `_ = SOME y` \\ PairCases_on `y`
    \\ full_simp_tac(srw_ss())[]
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ CASE_TAC \\ rename1 `_ = SOME y` \\ PairCases_on `y`
    \\ full_simp_tac(srw_ss())[]
    \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[] \\ Cases_on `read_bitmap t`
  \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ rename1 `_ = SOME y`
  \\ PairCases_on `y` \\ full_simp_tac(srw_ss())[LET_THM]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ rename1 `_ = SOME z`
  \\ PairCases_on `z` \\ full_simp_tac(srw_ss())[LET_THM]
  \\ full_simp_tac(srw_ss())[word_gen_gc_move_bitmap_def,LET_THM] \\ rev_full_simp_tac(srw_ss())[get_bits_intro]
  \\ strip_tac \\ rpt var_eq_tac
  \\ IF_CASES_TAC THEN1
   (sg `F`
    \\ full_simp_tac(srw_ss())[wordsLib.WORD_DECIDE ``w+1w=0w <=> (w = -1w)``]
    \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[labPropsTheory.good_dimindex_def]
    \\ full_simp_tac(srw_ss())[word_2comp_def] \\ full_simp_tac(srw_ss())[dimword_def]
    \\ imp_res_tac DROP_IMP_LESS_LENGTH \\ decide_tac)
  \\ `DROP (w2n w) bitmaps = t` by
   (`w2n w = SUC (w2n (w + -1w))` suffices_by
      metis_tac [DROP_EQ_CONS_IMP_DROP_SUC]
    \\ Cases_on `w` \\ full_simp_tac(srw_ss())[word_add_n2w]
    \\ `~(n < 1) /\ n - 1 < dimword (:'a)` by decide_tac
    \\ full_simp_tac std_ss [GSYM word_sub_def,addressTheory.word_arith_lemma2]
    \\ full_simp_tac(srw_ss())[] \\ decide_tac) \\ full_simp_tac(srw_ss())[] \\ pop_assum kall_tac
  \\ full_simp_tac(srw_ss())[filter_bitmap_APPEND]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `x` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `filter_bitmap x' x1` \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `x` \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[word_gen_gc_move_roots_APPEND,LET_THM]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ qpat_x_assum `filter_bitmap (get_bits h) stack = SOME (x0,x1)` assume_tac
  \\ drule (map_bitmap_APPEND_APPEND |> GEN_ALL)
  \\ `LENGTH x0 = LENGTH wl'` by (imp_res_tac word_gen_gc_move_roots_IMP_LENGTH \\ full_simp_tac(srw_ss())[])
  \\ disch_then drule
  \\ disch_then (qspecl_then [`ws2`,`x'`] mp_tac)
  \\ strip_tac \\ full_simp_tac(srw_ss())[] \\ pop_assum kall_tac
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `x` \\ full_simp_tac(srw_ss())[]
  \\ drule filter_bitmap_map_bitmap
  \\ once_rewrite_tac [EQ_SYM_EQ] \\ disch_then drule
  \\ once_rewrite_tac [EQ_SYM_EQ] \\ disch_then drule
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `x` \\ full_simp_tac(srw_ss())[]);

val word_gen_gc_partial_move_bitmaps_unroll = Q.prove(
  `word_gen_gc_partial_move_bitmaps conf
      (Word w,stack,bitmaps,i1,pa1,curr,m,dm,gs,rs) = SOME x /\
    LENGTH bitmaps < dimword (:'a) - 1 /\ good_dimindex (:'a) ==>
    word_gen_gc_partial_move_bitmaps conf
      (Word w,stack,bitmaps,i1,pa1,curr,m,dm,gs,rs) =
    case DROP (w2n (w - 1w:'a word)) bitmaps of
    | [] => NONE
    | (y::ys) =>
      case word_gen_gc_partial_move_bitmap conf (y,stack,i1,pa1,curr,m,dm,gs,rs) of
      | NONE => NONE
      | SOME (hd,ws,i2,pa2,m2,c2) =>
          if ~(word_msb y) then SOME (hd,ws,i2,pa2,m2,c2) else
            case word_gen_gc_partial_move_bitmaps conf
                   (Word (w+1w),ws,bitmaps,i2,pa2,curr,m2,dm,gs,rs) of
            | NONE => NONE
            | SOME (hd3,ws3,i3,pa3,m3,c3) =>
                SOME (hd++hd3,ws3,i3,pa3,m3,c2 /\ c3)`,
  full_simp_tac(srw_ss())[word_gen_gc_partial_move_bitmaps_def,full_read_bitmap_def]
  \\ Cases_on `w = 0w` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `DROP (w2n (w + -1w)) bitmaps`
  \\ full_simp_tac(srw_ss())[read_bitmap_def]
  \\ reverse (Cases_on `word_msb h`)
  THEN1
   (full_simp_tac(srw_ss())[word_gen_gc_partial_move_bitmap_def,get_bits_def,LET_THM]
    \\ CASE_TAC \\ rename1 `_ = SOME y` \\ PairCases_on `y`
    \\ full_simp_tac(srw_ss())[]
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ CASE_TAC \\ rename1 `_ = SOME y` \\ PairCases_on `y`
    \\ full_simp_tac(srw_ss())[]
    \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[] \\ Cases_on `read_bitmap t`
  \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ rename1 `_ = SOME y`
  \\ PairCases_on `y` \\ full_simp_tac(srw_ss())[LET_THM]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ rename1 `_ = SOME z`
  \\ PairCases_on `z` \\ full_simp_tac(srw_ss())[LET_THM]
  \\ full_simp_tac(srw_ss())[word_gen_gc_partial_move_bitmap_def,LET_THM] \\ rev_full_simp_tac(srw_ss())[get_bits_intro]
  \\ strip_tac \\ rpt var_eq_tac
  \\ IF_CASES_TAC THEN1
   (sg `F`
    \\ full_simp_tac(srw_ss())[wordsLib.WORD_DECIDE ``w+1w=0w <=> (w = -1w)``]
    \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[labPropsTheory.good_dimindex_def]
    \\ full_simp_tac(srw_ss())[word_2comp_def] \\ full_simp_tac(srw_ss())[dimword_def]
    \\ imp_res_tac DROP_IMP_LESS_LENGTH \\ decide_tac)
  \\ `DROP (w2n w) bitmaps = t` by
   (`w2n w = SUC (w2n (w + -1w))` suffices_by
      metis_tac [DROP_EQ_CONS_IMP_DROP_SUC]
    \\ Cases_on `w` \\ full_simp_tac(srw_ss())[word_add_n2w]
    \\ `~(n < 1) /\ n - 1 < dimword (:'a)` by decide_tac
    \\ full_simp_tac std_ss [GSYM word_sub_def,addressTheory.word_arith_lemma2]
    \\ full_simp_tac(srw_ss())[] \\ decide_tac) \\ full_simp_tac(srw_ss())[] \\ pop_assum kall_tac
  \\ full_simp_tac(srw_ss())[filter_bitmap_APPEND]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `x` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `filter_bitmap x' x1` \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `x` \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[word_gen_gc_partial_move_roots_APPEND,LET_THM]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ qpat_x_assum `filter_bitmap (get_bits h) stack = SOME (x0,x1)` assume_tac
  \\ drule (map_bitmap_APPEND_APPEND |> GEN_ALL)
  \\ `LENGTH x0 = LENGTH wl'` by (imp_res_tac word_gen_gc_partial_move_roots_IMP_LENGTH \\ full_simp_tac(srw_ss())[])
  \\ disch_then drule
  \\ disch_then (qspecl_then [`ws2`,`x'`] mp_tac)
  \\ strip_tac \\ full_simp_tac(srw_ss())[] \\ pop_assum kall_tac
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `x` \\ full_simp_tac(srw_ss())[]
  \\ drule filter_bitmap_map_bitmap
  \\ once_rewrite_tac [EQ_SYM_EQ] \\ disch_then drule
  \\ once_rewrite_tac [EQ_SYM_EQ] \\ disch_then drule
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `x` \\ full_simp_tac(srw_ss())[]);

val word_gen_gc_move_bitmap_unroll = Q.prove(
  `word_gen_gc_move_bitmap conf (w,stack,i1,pa1,ib1,pb1,curr,m,dm) =
    if w = 0w:'a word then SOME ([],stack,i1,pa1,ib1,pb1,m,T) else
    if w = 1w then SOME ([],stack,i1,pa1,ib1,pb1,m,T) else
      case stack of
      | [] => NONE
      | (x::xs) =>
        if (w && 1w) = 0w then
          case word_gen_gc_move_bitmap conf (w >>> 1,xs,i1,pa1,ib1,pb1,curr,m,dm) of
          | NONE => NONE
          | SOME (new,stack,i1,pa1,ib1,pb1,m,c) =>
              SOME (x::new,stack,i1,pa1,ib1,pb1,m,c)
        else
          let (x1,i1,pa1,ib1,pb1,m1,c1) =
            word_gen_gc_move conf (x,i1,pa1,ib1,pb1,curr,m,dm) in
          case word_gen_gc_move_bitmap conf (w >>> 1,xs,i1,pa1,ib1,pb1,curr,m1,dm) of
          | NONE => NONE
          | SOME (new,stack,i1,pa1,ib1,pb1,m,c) =>
              SOME (x1::new,stack,i1,pa1,ib1,pb1,m,c1 /\ c)`,
  simp [word_and_one_eq_0_iff]
  \\ simp [Once word_gen_gc_move_bitmap_def,get_bits_def]
  \\ IF_CASES_TAC
  \\ full_simp_tac(srw_ss())[EVAL ``bit_length 0w``,filter_bitmap_def,
         map_bitmap_def,word_gen_gc_move_roots_def]
  \\ IF_CASES_TAC
  \\ full_simp_tac(srw_ss())[EVAL ``bit_length 1w``,filter_bitmap_def,
         map_bitmap_def,word_gen_gc_move_roots_def]
  \\ simp [bit_length_minus_1]
  \\ full_simp_tac(srw_ss())[GSYM bit_length_eq_1]
  \\ pop_assum (fn th => mp_tac (ONCE_REWRITE_RULE [bit_length_def] th))
  \\ full_simp_tac(srw_ss())[] \\ strip_tac
  \\ Cases_on `bit_length (w >>> 1)` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[GENLIST_CONS,o_DEF,ADD1,filter_bitmap_def]
  \\ Cases_on `stack` \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[filter_bitmap_def]
  \\ `get_bits (w >>> 1) = GENLIST (\x. w ' (x + 1)) n` by
   (full_simp_tac(srw_ss())[get_bits_def,GENLIST_FUN_EQ] \\ srw_tac[][]
    \\ `n + 1 <= dimindex (:'a)` by metis_tac [bit_length_LESS_EQ_dimindex]
    \\ `x < dimindex (:'a)` by decide_tac
    \\ full_simp_tac(srw_ss())[word_lsr_def,fcpTheory.FCP_BETA]
    \\ eq_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ decide_tac)
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[filter_bitmap_def,map_bitmap_def]
  THEN1
   (full_simp_tac(srw_ss())[word_gen_gc_move_bitmap_def,LET_THM]
    \\ ntac 2 (CASE_TAC \\ full_simp_tac(srw_ss())[])
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ rpt (CASE_TAC \\ full_simp_tac(srw_ss())[]))
  \\ full_simp_tac(srw_ss())[word_gen_gc_move_bitmap_def,LET_THM]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] THEN1 (pairarg_tac \\ full_simp_tac(srw_ss())[])
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[word_gen_gc_move_roots_def,LET_THM]
  \\ ntac 3 (pairarg_tac \\ full_simp_tac(srw_ss())[]) \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[map_bitmap_def]
  \\ rpt (CASE_TAC \\ full_simp_tac(srw_ss())[]));

val word_gen_gc_partial_move_bitmap_unroll = Q.prove(
  `word_gen_gc_partial_move_bitmap conf (w,stack,i1,pa1,curr,m,dm,gs,rs) =
    if w = 0w:'a word then SOME ([],stack,i1,pa1,m,T) else
    if w = 1w then SOME ([],stack,i1,pa1,m,T) else
      case stack of
      | [] => NONE
      | (x::xs) =>
        if (w && 1w) = 0w then
          case word_gen_gc_partial_move_bitmap conf
                 (w >>> 1,xs,i1,pa1,curr,m,dm,gs,rs) of
          | NONE => NONE
          | SOME (new,stack,i1,pa1,m,c) =>
              SOME (x::new,stack,i1,pa1,m,c)
        else
          let (x1,i1,pa1,m1,c1) =
            word_gen_gc_partial_move conf (x,i1,pa1,curr,m,dm,gs,rs) in
          case word_gen_gc_partial_move_bitmap conf
                 (w >>> 1,xs,i1,pa1,curr,m1,dm,gs,rs) of
          | NONE => NONE
          | SOME (new,stack,i1,pa1,m,c) =>
              SOME (x1::new,stack,i1,pa1,m,c1 /\ c)`,
  simp [word_and_one_eq_0_iff]
  \\ simp [Once word_gen_gc_partial_move_bitmap_def,get_bits_def]
  \\ IF_CASES_TAC
  \\ full_simp_tac(srw_ss())[EVAL ``bit_length 0w``,filter_bitmap_def,
         map_bitmap_def,word_gen_gc_partial_move_roots_def]
  \\ IF_CASES_TAC
  \\ full_simp_tac(srw_ss())[EVAL ``bit_length 1w``,filter_bitmap_def,
         map_bitmap_def,word_gen_gc_partial_move_roots_def]
  \\ simp [bit_length_minus_1]
  \\ full_simp_tac(srw_ss())[GSYM bit_length_eq_1]
  \\ pop_assum (fn th => mp_tac (ONCE_REWRITE_RULE [bit_length_def] th))
  \\ full_simp_tac(srw_ss())[] \\ strip_tac
  \\ Cases_on `bit_length (w >>> 1)` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[GENLIST_CONS,o_DEF,ADD1,filter_bitmap_def]
  \\ Cases_on `stack` \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[filter_bitmap_def]
  \\ `get_bits (w >>> 1) = GENLIST (\x. w ' (x + 1)) n` by
   (full_simp_tac(srw_ss())[get_bits_def,GENLIST_FUN_EQ] \\ srw_tac[][]
    \\ `n + 1 <= dimindex (:'a)` by metis_tac [bit_length_LESS_EQ_dimindex]
    \\ `x < dimindex (:'a)` by decide_tac
    \\ full_simp_tac(srw_ss())[word_lsr_def,fcpTheory.FCP_BETA]
    \\ eq_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ decide_tac)
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[filter_bitmap_def,map_bitmap_def]
  THEN1
   (full_simp_tac(srw_ss())[word_gen_gc_partial_move_bitmap_def,LET_THM]
    \\ ntac 2 (CASE_TAC \\ full_simp_tac(srw_ss())[])
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ rpt (CASE_TAC \\ full_simp_tac(srw_ss())[]))
  \\ full_simp_tac(srw_ss())[word_gen_gc_partial_move_bitmap_def,LET_THM]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] THEN1 (pairarg_tac \\ full_simp_tac(srw_ss())[])
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[word_gen_gc_partial_move_roots_def,LET_THM]
  \\ ntac 3 (pairarg_tac \\ full_simp_tac(srw_ss())[]) \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[map_bitmap_def]
  \\ rpt (CASE_TAC \\ full_simp_tac(srw_ss())[]));

Theorem word_gen_gc_move_code_thm:
   word_gen_gc_move conf (w,i,pa,ib,pb,old,m,dm) = (w1,i1,pa1,ib1,pb1,m1,T) /\
    shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
    2 < dimindex (:'a) /\ conf.len_size <> 0 /\
    (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
    FLOOKUP s.store CurrHeap = SOME (Word old) /\ s.use_store /\
    (s:('a,'c,'b)stackSem$state).memory = m /\ s.mdomain = dm /\
    0 IN FDOM s.regs /\
    1 IN FDOM s.regs /\
    2 IN FDOM s.regs /\
    get_var 3 s = SOME (Word pa) /\
    get_var 4 s = SOME (Word (i:'a word)) /\
    get_var 5 s = SOME w /\
    (Temp 0w) IN FDOM s.store /\
    (Temp 1w) IN FDOM s.store /\
    FLOOKUP s.store (Temp 2w) = SOME (Word pb) /\
    FLOOKUP s.store (Temp 3w) = SOME (Word ib) /\
    1 IN FDOM s.regs /\
    2 IN FDOM s.regs /\
    6 IN FDOM s.regs ==>
    ?ck r0 r1 r2 r6 t0 t1.
      evaluate (word_gen_gc_move_code conf,s with clock := s.clock + ck) =
        (NONE,s with <| memory := m1;
                        store := s.store |++ [(Temp 0w, t0);
                                              (Temp 1w, t1);
                                              (Temp 2w, Word pb1);
                                              (Temp 3w, Word ib1)];
                        regs := s.regs |++ [(0,r0);
                                            (1,r1);
                                            (2,r2);
                                            (3,Word pa1);
                                            (4,Word i1);
                                            (5,w1);
                                            (6,r6)] |>)
Proof
  reverse (Cases_on `w`) \\ full_simp_tac(srw_ss())[word_gen_gc_move_def] THEN1
   (srw_tac[][word_gen_gc_move_code_def,evaluate_def]
    \\ full_simp_tac(srw_ss())[get_var_def] \\ tac
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less]
    \\ qexists_tac `s.store ' (Temp 0w)`
    \\ qexists_tac `s.store ' (Temp 1w)`
    \\ rw [] \\ fs [] \\ eq_tac \\ rw [] \\ fs [])
  \\ full_simp_tac(srw_ss())[get_var_def,word_gen_gc_move_code_def,evaluate_def]
  \\ tac1
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[] THEN1
   (tac \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac `0` \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less]
    \\ qexists_tac `s.store ' (Temp 0w)`
    \\ qexists_tac `s.store ' (Temp 1w)`
    \\ rw [] \\ fs [] \\ eq_tac \\ rw [] \\ fs [])
  \\ IF_CASES_TAC
  THEN1
   (full_simp_tac(srw_ss())[ptr_to_addr_def] \\ tac
    \\ strip_tac \\ rpt var_eq_tac \\ tac
    \\ full_simp_tac(srw_ss())[is_fwd_ptr_iff] \\ tac
    \\ full_simp_tac(srw_ss())[clear_top_inst_def,evaluate_def] \\ tac
    \\ qexists_tac `0` \\ full_simp_tac(srw_ss())[theWord_def]
    \\ full_simp_tac(srw_ss())[update_addr_def,select_lower_lemma]
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less]
    \\ qexists_tac `s.store ' (Temp 0w)`
    \\ qexists_tac `s.store ' (Temp 1w)`
    \\ rw [] \\ fs [] \\ eq_tac \\ rw [] \\ fs [])
  \\ IF_CASES_TAC THEN1
   (pairarg_tac \\ full_simp_tac(srw_ss())[ptr_to_addr_def,isWord_thm]
    \\ strip_tac \\ rpt var_eq_tac \\ fs [theWord_def]
    \\ ntac 6 tac1
    \\ fs [is_fwd_ptr_def,is_ref_header_def,theWord_def]
    \\ ntac 19 tac1
    \\ qabbrev_tac `len = decode_length conf v`
    \\ full_simp_tac(srw_ss())[GSYM select_lower_lemma]
    \\ qexists_tac `w2n (len + 1w)`
    \\ qmatch_goalsub_abbrev_tac `evaluate (_,s3)`
    \\ drule memcpy_code_thm
    \\ disch_then (qspec_then `s3 with clock := s.clock` mp_tac)
    \\ full_simp_tac(srw_ss())[]
    \\ `s3 with clock := s.clock + w2n (len + 1w) = s3` by
         (unabbrev_all_tac
          \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC] \\ NO_TAC)
    \\ full_simp_tac(srw_ss())[] \\ impl_tac THEN1
      (unabbrev_all_tac \\ full_simp_tac(srw_ss())[get_var_def] \\ tac
       \\ fs [decode_length_def])
    \\ strip_tac \\ full_simp_tac(srw_ss())[FUPDATE_LIST]
    \\ tac1 \\ qunabbrev_tac `s3` \\ fs []
    \\ tac1 \\ full_simp_tac(srw_ss())[] \\ tac1
    \\ pop_assum kall_tac
    \\ fs [LET_THM,decode_length_def]
    \\ fs [] \\ tac \\ rpt var_eq_tac
    \\ full_simp_tac(srw_ss())[clear_top_inst_def] \\ tac
    \\ full_simp_tac(srw_ss())[select_lower_lemma,
          DECIDE ``n<>0 ==> m-(n-1)-1=m-n:num``]
    \\ tac \\ full_simp_tac(srw_ss())[] \\ tac
    \\ full_simp_tac(srw_ss())[update_addr_def]
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less]
    \\ `shift_length conf <> 0` by (EVAL_TAC \\ decide_tac)
    \\ full_simp_tac(srw_ss())[select_lower_lemma,
          DECIDE ``n<>0 ==> m-(n-1)-1=m-n:num``]
    \\ qexists_tac `Word pa`
    \\ qexists_tac `Word i` \\ fs [])
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[ptr_to_addr_def,isWord_thm]
  \\ strip_tac \\ rpt var_eq_tac
  \\ ntac 6 tac1
  \\ fs [is_fwd_ptr_def,is_ref_header_def,theWord_def]
  \\ ntac 9 tac1
  \\ qabbrev_tac `len = decode_length conf v`
  \\ full_simp_tac(srw_ss())[GSYM select_lower_lemma]
  \\ qexists_tac `w2n (len + 1w)`
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,s3)`
  \\ drule memcpy_code_thm
  \\ disch_then (qspec_then `s3 with clock := s.clock` mp_tac)
  \\ full_simp_tac(srw_ss())[]
  \\ `s3 with clock := s.clock + w2n (len + 1w) = s3` by
       (unabbrev_all_tac \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC] \\ NO_TAC)
  \\ full_simp_tac(srw_ss())[] \\ impl_tac THEN1
    (unabbrev_all_tac \\ full_simp_tac(srw_ss())[get_var_def] \\ tac
     \\ fs [decode_length_def])
  \\ strip_tac \\ full_simp_tac(srw_ss())[FUPDATE_LIST]
  \\ tac1 \\ qunabbrev_tac `s3` \\ fs []
  \\ tac1 \\ full_simp_tac(srw_ss())[] \\ tac1
  \\ fs [LET_THM,decode_length_def]
  \\ fs [] \\ tac \\ rpt var_eq_tac
  \\ full_simp_tac(srw_ss())[clear_top_inst_def] \\ tac
  \\ full_simp_tac(srw_ss())[select_lower_lemma,
        DECIDE ``n<>0 ==> m-(n-1)-1=m-n:num``]
  \\ tac \\ full_simp_tac(srw_ss())[] \\ tac
  \\ full_simp_tac(srw_ss())[update_addr_def]
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
         FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less]
  \\ `shift_length conf <> 0` by (EVAL_TAC \\ decide_tac)
  \\ full_simp_tac(srw_ss())[select_lower_lemma,
        DECIDE ``n<>0 ==> m-(n-1)-1=m-n:num``]
  \\ qexists_tac `s.store ' (Temp 0w)`
  \\ qexists_tac `s.store ' (Temp 1w)`
  \\ rw [] \\ fs [] \\ eq_tac \\ rw [] \\ fs []
QED

Theorem word_gen_gc_partial_move_code_thm:
   word_gen_gc_partial_move conf (w,i,pa,old,m,dm,gs,rs) = (w1,i1,pa1,m1,T) /\
    shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
    2 < dimindex (:'a) /\ conf.len_size <> 0 /\
    (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
    FLOOKUP s.store CurrHeap = SOME (Word old) /\ (s:('a,'c,'b)stackSem$state).use_store /\
    s.memory = m /\ s.mdomain = dm /\ good_dimindex (:'a) /\
    0 IN FDOM s.regs /\
    1 IN FDOM s.regs /\
    2 IN FDOM s.regs /\
    get_var 3 s = SOME (Word pa) /\
    get_var 4 s = SOME (Word (i:'a word)) /\
    get_var 5 s = SOME w /\
    FLOOKUP s.store (Temp 0w) = SOME (Word gs) /\
    FLOOKUP s.store (Temp 1w) = SOME (Word rs) /\
    1 IN FDOM s.regs /\
    2 IN FDOM s.regs /\
    6 IN FDOM s.regs ==>
    ?ck r0 r1 r2 r6.
      evaluate (word_gen_gc_partial_move_code conf,s with clock := s.clock + ck) =
        (NONE,s with <| memory := m1;
                        regs := s.regs |++ [(0,r0);
                                            (1,r1);
                                            (2,r2);
                                            (3,Word pa1);
                                            (4,Word i1);
                                            (5,w1);
                                            (6,r6)] |>)
Proof
  reverse (Cases_on `w`)
  \\ full_simp_tac(srw_ss())[word_gen_gc_partial_move_def] THEN1
   (srw_tac[][word_gen_gc_partial_move_code_def,evaluate_def]
    \\ full_simp_tac(srw_ss())[get_var_def] \\ tac
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less])
  \\ full_simp_tac(srw_ss())[get_var_def,
       word_gen_gc_partial_move_code_def,evaluate_def]
  \\ tac1
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[] THEN1
   (tac \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac `0` \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less])
  \\ simp [Once ptr_to_addr_def]
  \\ simp [Once ptr_to_addr_def]
  \\ Cases_on `good_dimindex (:'a)` \\ fs []
  \\ drule (GEN_ALL bytes_in_word_mul_eq_shift
               |> GSYM) \\ fs [] \\ strip_tac
  \\ Cases_on `c ⋙ shift_length conf ≪ shift (:α) <₊ gs`
  THEN1
   (rfs [] \\ fs [] \\ strip_tac \\ rveq
    \\ ntac 5 tac1
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less])
  \\ Cases_on `rs ≤₊ c ⋙ shift_length conf ≪ shift (:α)`
  THEN1
   (rfs [] \\ fs [] \\ strip_tac \\ rveq
    \\ ntac 5 tac1
    \\ fs [GSYM WORD_NOT_LOWER]
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less])
  \\ asm_simp_tac std_ss []
  \\ ntac 9 tac1
  \\ rev_full_simp_tac (srw_ss()) [GSYM WORD_NOT_LOWER]
  \\ IF_CASES_TAC
  THEN1
   (full_simp_tac(srw_ss())[ptr_to_addr_def] \\ tac1
    \\ strip_tac \\ rpt var_eq_tac
    \\ full_simp_tac(srw_ss())[is_fwd_ptr_iff] \\ tac
    \\ full_simp_tac(srw_ss())[clear_top_inst_def,evaluate_def] \\ tac
    \\ qexists_tac `0` \\ full_simp_tac(srw_ss())[theWord_def]
    \\ full_simp_tac(srw_ss())[update_addr_def,select_lower_lemma]
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less])
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[ptr_to_addr_def,isWord_thm]
  \\ strip_tac \\ rpt var_eq_tac
  \\ ntac 6 tac1
  \\ fs [is_fwd_ptr_def,is_ref_header_def,theWord_def]
  \\ ntac 4 tac1
  \\ qabbrev_tac `len = decode_length conf v`
  \\ full_simp_tac(srw_ss())[GSYM select_lower_lemma]
  \\ qexists_tac `w2n (len + 1w)`
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,s3)`
  \\ drule memcpy_code_thm
  \\ disch_then (qspec_then `s3 with clock := s.clock` mp_tac)
  \\ full_simp_tac(srw_ss())[]
  \\ `s3 with clock := s.clock + w2n (len + 1w) = s3` by
       (unabbrev_all_tac \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC] \\ NO_TAC)
  \\ full_simp_tac(srw_ss())[] \\ impl_tac THEN1
    (unabbrev_all_tac \\ full_simp_tac(srw_ss())[get_var_def] \\ tac
     \\ fs [decode_length_def])
  \\ strip_tac \\ full_simp_tac(srw_ss())[FUPDATE_LIST]
  \\ tac1 \\ qunabbrev_tac `s3` \\ fs []
  \\ tac1 \\ full_simp_tac(srw_ss())[] \\ tac1
  \\ fs [LET_THM,decode_length_def]
  \\ fs [] \\ tac \\ rpt var_eq_tac
  \\ full_simp_tac(srw_ss())[clear_top_inst_def] \\ tac
  \\ full_simp_tac(srw_ss())[select_lower_lemma,
        DECIDE ``n<>0 ==> m-(n-1)-1=m-n:num``]
  \\ tac \\ full_simp_tac(srw_ss())[] \\ tac
  \\ full_simp_tac(srw_ss())[update_addr_def]
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
         FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less]
  \\ `shift_length conf <> 0` by (EVAL_TAC \\ decide_tac)
  \\ full_simp_tac(srw_ss())[select_lower_lemma,
        DECIDE ``n<>0 ==> m-(n-1)-1=m-n:num``]
QED

Theorem word_gen_gc_move_bitmap_code_thm:
   !w stack (s:('a,'c,'b)stackSem$state) i pa ib pb curr m dm new stack1
    a1 i1 pa1 ib1 pb1 m1 old.
      word_gen_gc_move_bitmap conf (w,stack,i,pa,ib,pb,curr,m,dm) =
        SOME (new,stack1,i1,pa1,ib1,pb1,m1,T) /\
      shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ conf.len_size <> 0 /\ good_dimindex (:'a) /\
      (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
      FLOOKUP s.store CurrHeap = SOME (Word curr) /\ s.use_store /\
      s.memory = m /\ s.mdomain = dm /\ s.use_stack /\
      0 IN FDOM s.regs /\
      1 IN FDOM s.regs /\
      2 IN FDOM s.regs /\
      get_var 3 s = SOME (Word pa) /\
      get_var 4 s = SOME (Word (i:'a word)) /\
      5 IN FDOM s.regs /\
      6 IN FDOM s.regs /\
      get_var 7 s = SOME (Word w) /\
      get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
      Temp 0w IN FDOM s.store /\
      Temp 1w IN FDOM s.store /\
      FLOOKUP s.store (Temp 2w) = SOME (Word pb) /\
      FLOOKUP s.store (Temp 3w) = SOME (Word ib) /\
      s.stack = init ++ old ++ stack /\
      s.stack_space = LENGTH init /\
      (dimindex (:'a) DIV 8) * LENGTH s.stack < dimword (:'a) ==>
      ?ck r0 r1 r2 r5 r6 r7 t0 t1.
        evaluate (word_gen_gc_move_bitmap_code conf,s with clock := s.clock + ck) =
          (NONE,s with <| memory := m1;
                          stack := init ++ old ++ new ++ stack1;
                          store :=
                            s.store |++
                            [(Temp 0w,t0); (Temp 1w,t1); (Temp 2w,Word pb1);
                             (Temp 3w,Word ib1)];
                          regs := s.regs |++ [(0,r0);
                                              (1,r1);
                                              (2,r2);
                                              (3,Word pa1);
                                              (4,Word i1);
                                              (5,r5);
                                              (6,r6);
                                              (7,r7);
                      (8,Word (bytes_in_word * n2w (LENGTH (old ++ new))))] |>)
Proof
  recInduct bit_length_ind \\ rpt strip_tac \\ fs []
  \\ qpat_x_assum `word_gen_gc_move_bitmap _ _ = _` mp_tac
  \\ once_rewrite_tac [word_gen_gc_move_bitmap_unroll]
  \\ Cases_on `w = 0w` \\ fs [] THEN1
   (strip_tac \\ rpt var_eq_tac
    \\ fs [word_gen_gc_move_bitmap_code_def,get_var_def] \\ tac
    \\ fs [lower_2w_eq]
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less]
    \\ qexists_tac `s.store ' (Temp 0w)`
    \\ qexists_tac `s.store ' (Temp 1w)`
    \\ rw [] \\ fs [] \\ eq_tac \\ rw [] \\ fs [])
  \\ Cases_on `w = 1w` \\ fs [] THEN1
   (strip_tac \\ rpt var_eq_tac
    \\ fs [word_gen_gc_move_bitmap_code_def,get_var_def] \\ tac
    \\ fs [lower_2w_eq]
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less]
    \\ qexists_tac `s.store ' (Temp 0w)`
    \\ qexists_tac `s.store ' (Temp 1w)`
    \\ rw [] \\ fs [] \\ eq_tac \\ rw [] \\ fs [])
  \\ Cases_on `stack` \\ fs []
  \\ IF_CASES_TAC THEN1
   (every_case_tac \\ strip_tac \\ rpt var_eq_tac
    \\ rename1 `_ = SOME (new1,st1,i1,pa1,ib1,pb1,m1,T)`
    \\ simp_tac std_ss [word_gen_gc_move_bitmap_code_def,get_var_def,evaluate_def]
    \\ simp_tac std_ss [GSYM word_gen_gc_move_bitmap_code_def]
    \\ fs [get_var_def,get_var_imm_def] \\ tac
    \\ fs [lower_2w_eq,STOP_def]
    \\ qabbrev_tac `s2 = s with
           <|regs := s.regs |+ (7,Word (w ⋙ 1))
              |+ (8,Word (bytes_in_word + bytes_in_word * n2w (LENGTH old))) |>`
    \\ `s.memory = s2.memory /\ s.mdomain = s2.mdomain` by
          (unabbrev_all_tac \\ fs []) \\ fs []
    \\ first_x_assum drule
    \\ disch_then (qspec_then `old ++ [h]` mp_tac)
    \\ impl_tac
    THEN1 (unabbrev_all_tac
         \\ fs [FLOOKUP_UPDATE,word_add_n2w]
         \\ rfs [WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w])
    \\ strip_tac \\ unabbrev_all_tac \\ fs []
    \\ qexists_tac `ck + 1` \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND,ADD1]
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less] \\ fs []
    \\ qexists_tac `t0`
    \\ qexists_tac `t1`
    \\ rw [] \\ fs [] \\ eq_tac \\ rw [] \\ fs [])
  \\ pairarg_tac \\ fs []
  \\ every_case_tac \\ strip_tac \\ rpt var_eq_tac
  \\ rename1 `_ = SOME (new1,st1,i1,pa1,ib1,pb1,m1,T)`
  \\ simp_tac std_ss [word_gen_gc_move_bitmap_code_def,get_var_def,evaluate_def]
  \\ simp_tac std_ss [GSYM word_gen_gc_move_bitmap_code_def]
  \\ fs [get_var_def,get_var_imm_def] \\ tac
  \\ fs [lower_2w_eq,STOP_def]
  \\ `w2n (((bytes_in_word:'a word) * n2w (LENGTH old)) ⋙ word_shift (:α)) =
         LENGTH old` by
   (`(dimindex (:α) DIV 8) * LENGTH old < dimword (:α)` by rfs [RIGHT_ADD_DISTRIB]
    \\ drule (bytes_in_word_word_shift_n2w |> GEN_ALL)
    \\ disch_then drule \\ fs [] \\ rw []
    \\ rfs [labPropsTheory.good_dimindex_def,dimword_def] \\ rfs [])
  \\ fs [] \\ reverse CASE_TAC THEN1
    (sg `F` \\ fs []
     \\ pop_assum mp_tac \\ fs [] \\ AP_TERM_TAC
     \\ match_mp_tac (bytes_in_word_word_shift_n2w |> GEN_ALL) \\ fs []
     \\ rfs [labPropsTheory.good_dimindex_def,dimword_def] \\ rfs [])
  \\ fs [] \\ tac \\ fs [EL_LENGTH_ADD_LEMMA]
  \\ qabbrev_tac `s4 = s with <|regs := s.regs |+ (5,h) |+ (7,Word (w ⋙ 1)) |>`
  \\ `s.memory = s4.memory /\ s.mdomain = s4.mdomain` by
           (unabbrev_all_tac \\ fs []) \\ fs []
  \\ qpat_abbrev_tac `ee = EL _ _`
  \\ `ee = h` by
   (unabbrev_all_tac
    \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ simp_tac std_ss [APPEND_ASSOC,GSYM LENGTH_APPEND]
    \\ simp_tac std_ss [Q.SPEC `h::t` EL_LENGTH_APPEND
         |> SIMP_RULE (srw_ss()) []] \\ NO_TAC)
  \\ drule (word_gen_gc_move_code_thm |> GEN_ALL |> SIMP_RULE std_ss [])
  \\ impl_tac THEN1 (unabbrev_all_tac \\ fs [get_var_def,FLOOKUP_UPDATE])
  \\ strip_tac \\ fs []
  \\ qabbrev_tac `s5 = s with
        <|regs :=
            s.regs |+ (5,h) |+ (7,Word (w ⋙ 1)) |+ (0,r0) |+ (1,r1) |+
            (2,r2) |+ (3,Word pa1') |+ (4,Word i1') |+ (5,x1) |+ (6,r6) |+
            (8,Word (bytes_in_word + bytes_in_word * n2w (LENGTH old)));
          stack := init ++ old ++ [x1] ++ t;
          store :=
            s4.store |++
            [(Temp 0w,t0); (Temp 1w,t1); (Temp 2w,Word pb1');
             (Temp 3w,Word ib1')]; memory := m1' |>`
  \\ `m1' = s5.memory /\ s4.mdomain = s5.mdomain` by
           (unabbrev_all_tac \\ fs []) \\ fs []
  \\ first_x_assum drule
  \\ disch_then (qspec_then `old ++ [x1]` mp_tac)
  \\ impl_tac THEN1
   (unabbrev_all_tac \\ tac
    \\ fs [RIGHT_ADD_DISTRIB,word_add_n2w,word_mul_n2w,bytes_in_word_def]
    \\ rfs [labPropsTheory.good_dimindex_def,dimword_def] \\ rfs [])
  \\ strip_tac \\ pop_assum mp_tac
  \\ drule (GEN_ALL evaluate_add_clock) \\ fs []
  \\ disch_then (qspec_then `ck' + 1` mp_tac)
  \\ rpt strip_tac \\ fs []
  \\ qexists_tac `ck+ck'+1` \\ fs []
  \\ unabbrev_all_tac \\ fs [] \\ tac
  \\ fs [LUPDATE_LENGTH_ADD_LEMMA,ADD1]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND,ADD1]
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less] \\ fs []
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less] \\ fs []
  \\ qexists_tac `t0'` \\ qexists_tac `t1'`
  \\ rw [] \\ fs [] \\ eq_tac \\ rw [] \\ fs []
QED

Theorem word_gen_gc_partial_move_bitmap_code_thm:
   !w stack (s:('a,'c,'b)stackSem$state) i pa curr m dm new stack1 a1 i1 pa1 m1 old.
      word_gen_gc_partial_move_bitmap conf (w,stack,i,pa,curr,m,dm,gs,rs) =
        SOME (new,stack1,i1,pa1,m1,T) /\
      shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ conf.len_size <> 0 /\ good_dimindex (:'a) /\
      (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
      FLOOKUP s.store CurrHeap = SOME (Word curr) /\ s.use_store /\
      s.memory = m /\ s.mdomain = dm /\ s.use_stack /\
      0 IN FDOM s.regs /\
      1 IN FDOM s.regs /\
      2 IN FDOM s.regs /\
      get_var 3 s = SOME (Word pa) /\
      get_var 4 s = SOME (Word (i:'a word)) /\
      5 IN FDOM s.regs /\
      6 IN FDOM s.regs /\
      get_var 7 s = SOME (Word w) /\
      get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
      FLOOKUP s.store (Temp 0w) = SOME (Word gs) /\
      FLOOKUP s.store (Temp 1w) = SOME (Word rs) /\
      s.stack = init ++ old ++ stack /\
      s.stack_space = LENGTH init /\
      (dimindex (:'a) DIV 8) * LENGTH s.stack < dimword (:'a) ==>
      ?ck r0 r1 r2 r5 r6 r7.
        evaluate (word_gen_gc_partial_move_bitmap_code conf,
          s with clock := s.clock + ck) =
          (NONE,s with <| memory := m1;
                          stack := init ++ old ++ new ++ stack1;
                          regs := s.regs |++ [(0,r0);
                                              (1,r1);
                                              (2,r2);
                                              (3,Word pa1);
                                              (4,Word i1);
                                              (5,r5);
                                              (6,r6);
                                              (7,r7);
                      (8,Word (bytes_in_word * n2w (LENGTH (old ++ new))))] |>)
Proof
  recInduct bit_length_ind \\ rpt strip_tac \\ fs []
  \\ qpat_x_assum `word_gen_gc_partial_move_bitmap _ _ = _` mp_tac
  \\ once_rewrite_tac [word_gen_gc_partial_move_bitmap_unroll]
  \\ Cases_on `w = 0w` \\ fs [] THEN1
   (strip_tac \\ rpt var_eq_tac
    \\ fs [word_gen_gc_partial_move_bitmap_code_def,get_var_def] \\ tac
    \\ fs [lower_2w_eq]
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less])
  \\ Cases_on `w = 1w` \\ fs [] THEN1
   (strip_tac \\ rpt var_eq_tac
    \\ fs [word_gen_gc_partial_move_bitmap_code_def,get_var_def] \\ tac
    \\ fs [lower_2w_eq]
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less])
  \\ Cases_on `stack` \\ fs []
  \\ IF_CASES_TAC THEN1
   (every_case_tac \\ strip_tac \\ rpt var_eq_tac
    \\ rename1 `_ = SOME (new1,st1,i1,pa1,m1,T)`
    \\ simp_tac std_ss [word_gen_gc_partial_move_bitmap_code_def,get_var_def,evaluate_def]
    \\ simp_tac std_ss [GSYM word_gen_gc_partial_move_bitmap_code_def]
    \\ fs [get_var_def,get_var_imm_def] \\ tac
    \\ fs [lower_2w_eq,STOP_def]
    \\ qabbrev_tac `s2 = s with
           <|regs := s.regs |+ (7,Word (w ⋙ 1))
              |+ (8,Word (bytes_in_word + bytes_in_word * n2w (LENGTH old))) |>`
    \\ `s.memory = s2.memory /\ s.mdomain = s2.mdomain` by
          (unabbrev_all_tac \\ fs []) \\ fs []
    \\ first_x_assum drule
    \\ disch_then (qspec_then `old ++ [h]` mp_tac)
    \\ impl_tac
    THEN1 (unabbrev_all_tac
         \\ fs [FLOOKUP_UPDATE,word_add_n2w]
         \\ rfs [WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w])
    \\ strip_tac \\ unabbrev_all_tac \\ fs []
    \\ qexists_tac `ck + 1` \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND,ADD1]
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less] \\ fs [])
  \\ pairarg_tac \\ fs []
  \\ every_case_tac \\ strip_tac \\ rpt var_eq_tac
  \\ rename1 `_ = SOME (new1,st1,i1,pa1,m1,T)`
  \\ simp_tac std_ss [word_gen_gc_partial_move_bitmap_code_def,
       get_var_def,evaluate_def]
  \\ simp_tac std_ss [GSYM word_gen_gc_partial_move_bitmap_code_def]
  \\ fs [get_var_def,get_var_imm_def] \\ tac
  \\ fs [lower_2w_eq,STOP_def]
  \\ `w2n (((bytes_in_word:'a word) * n2w (LENGTH old)) ⋙ word_shift (:α)) =
         LENGTH old` by
   (`(dimindex (:α) DIV 8) * LENGTH old < dimword (:α)` by rfs [RIGHT_ADD_DISTRIB]
    \\ drule (bytes_in_word_word_shift_n2w |> GEN_ALL)
    \\ disch_then drule \\ fs [] \\ rw []
    \\ rfs [labPropsTheory.good_dimindex_def,dimword_def] \\ rfs [])
  \\ fs [] \\ reverse CASE_TAC THEN1
    (sg `F` \\ fs []
     \\ pop_assum mp_tac \\ fs [] \\ AP_TERM_TAC
     \\ match_mp_tac (bytes_in_word_word_shift_n2w |> GEN_ALL) \\ fs []
     \\ rfs [labPropsTheory.good_dimindex_def,dimword_def] \\ rfs [])
  \\ qpat_abbrev_tac `ee = EL _ _`
  \\ `ee = h` by
   (unabbrev_all_tac
    \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ simp_tac std_ss [APPEND_ASSOC,GSYM LENGTH_APPEND]
    \\ simp_tac std_ss [Q.SPEC `h::t` EL_LENGTH_APPEND
         |> SIMP_RULE (srw_ss()) []] \\ NO_TAC)
  \\ fs [] \\ tac \\ fs [EL_LENGTH_ADD_LEMMA]
  \\ qabbrev_tac `s4 = s with <|regs := s.regs |+ (5,h) |+ (7,Word (w ⋙ 1)) |>`
  \\ `s.memory = s4.memory /\ s.mdomain = s4.mdomain` by
           (unabbrev_all_tac \\ fs []) \\ fs []
  \\ drule (word_gen_gc_partial_move_code_thm |> GEN_ALL |> SIMP_RULE std_ss [])
  \\ impl_tac THEN1 (unabbrev_all_tac \\ fs [get_var_def,FLOOKUP_UPDATE])
  \\ strip_tac
  \\ qabbrev_tac `s5 = s with
        <|regs :=
            s.regs |+ (5,h) |+ (7,Word (w ⋙ 1)) |+ (0,r0) |+ (1,r1) |+
            (2,r2) |+ (3,Word pa1') |+ (4,Word i1') |+ (5,x1) |+ (6,r6) |+
            (8,Word (bytes_in_word + bytes_in_word * n2w (LENGTH old)));
          stack := init ++ old ++ [x1] ++ t; memory := m1' |>`
  \\ `m1' = s5.memory /\ s4.mdomain = s5.mdomain` by
           (unabbrev_all_tac \\ fs []) \\ fs []
  \\ first_x_assum drule
  \\ disch_then (qspec_then `old ++ [x1]` mp_tac)
  \\ impl_tac THEN1
   (unabbrev_all_tac \\ tac
    \\ fs [RIGHT_ADD_DISTRIB,word_add_n2w,word_mul_n2w,bytes_in_word_def]
    \\ rfs [labPropsTheory.good_dimindex_def,dimword_def] \\ rfs [])
  \\ strip_tac \\ pop_assum mp_tac
  \\ drule (GEN_ALL evaluate_add_clock) \\ fs []
  \\ disch_then (qspec_then `ck' + 1` mp_tac)
  \\ rpt strip_tac \\ fs []
  \\ qexists_tac `ck+ck'+1` \\ fs []
  \\ unabbrev_all_tac \\ fs [] \\ tac
  \\ fs [LUPDATE_LENGTH_ADD_LEMMA,ADD1]
  \\ fs [EL_APPEND_EQN]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND,ADD1]
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less]
  \\ fs [FAPPLY_FUPDATE_THM,LUPDATE_APPEND,LUPDATE_def]
  \\ pop_assum mp_tac \\ fs []
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less]
QED

Theorem word_gen_gc_move_bitmaps_LENGTH:
   word_gen_gc_move_bitmaps conf (w,stack,bitmaps,i,pa,ib,pb,curr,m,dm) =
       SOME (xs,stack1,i1,pa1,ib1,pb1,m1,T) ==>
    LENGTH stack = LENGTH xs + LENGTH stack1
Proof
  fs [word_gen_gc_move_bitmaps_def]
  \\ every_case_tac \\ fs [] \\ pairarg_tac \\ fs []
  \\ every_case_tac \\ fs [] \\ rw []
  \\ imp_res_tac map_bitmap_IMP_LENGTH \\ fs []
  \\ imp_res_tac filter_bitmap_IMP_LENGTH \\ fs []
QED

Theorem word_gen_gc_partial_move_bitmaps_LENGTH:
   word_gen_gc_partial_move_bitmaps conf (w,stack,bitmaps,i,pa,curr,m,dm,gs,rs) =
       SOME (xs,stack1,i1,pa1,m1,T) ==>
    LENGTH stack = LENGTH xs + LENGTH stack1
Proof
  fs [word_gen_gc_partial_move_bitmaps_def]
  \\ every_case_tac \\ fs [] \\ pairarg_tac \\ fs []
  \\ every_case_tac \\ fs [] \\ rw []
  \\ imp_res_tac map_bitmap_IMP_LENGTH \\ fs []
  \\ imp_res_tac filter_bitmap_IMP_LENGTH \\ fs []
QED

Theorem word_gen_gc_move_bitmaps_code_thm:
   !w bitmaps z stack (s:('a,'c,'b)stackSem$state) i pa ib pb curr m dm new
         stack1 a1 i1 pa1 ib1 pb1 m1 old.
      word_gen_gc_move_bitmaps conf (Word w,stack,bitmaps,i,pa,ib,pb,curr,m,dm) =
        SOME (new,stack1,i1,pa1,ib1,pb1,m1,T) /\
      LENGTH bitmaps < dimword (:'a) − 1 ∧ good_dimindex (:'a) /\
      shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ conf.len_size <> 0 /\ good_dimindex (:'a) /\
      (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
      FLOOKUP s.store CurrHeap = SOME (Word curr) /\ s.use_store /\
      s.memory = m /\ s.mdomain = dm /\ s.bitmaps = bitmaps /\ s.use_stack /\
      get_var 0 s = SOME (Word z) /\ z <> 0w /\
      1 IN FDOM s.regs /\
      2 IN FDOM s.regs /\
      get_var 3 s = SOME (Word pa) /\
      get_var 4 s = SOME (Word (i:'a word)) /\
      5 IN FDOM s.regs /\
      6 IN FDOM s.regs /\
      7 IN FDOM s.regs /\
      get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
      get_var 9 s = SOME (Word (w - 1w)) /\
      Temp 0w IN FDOM s.store /\
      Temp 1w IN FDOM s.store /\
      FLOOKUP s.store (Temp 2w) = SOME (Word pb) /\
      FLOOKUP s.store (Temp 3w) = SOME (Word ib) /\
      s.stack = init ++ old ++ stack /\
      s.stack_space = LENGTH init /\
      (dimindex (:'a) DIV 8) * LENGTH s.stack < dimword (:'a) ==>
      ?ck r0 r1 r2 r5 r6 r7 r9 t0 t1.
        evaluate (word_gen_gc_move_bitmaps_code conf,s with clock := s.clock + ck) =
          (NONE,s with <| memory := m1;
                          stack := init ++ old ++ new ++ stack1;
                          clock := s.clock;
                          store :=
                            s.store |++
                            [(Temp 0w,t0); (Temp 1w,t1); (Temp 2w,Word pb1);
                             (Temp 3w,Word ib1)];
                          regs := s.regs |++ [(0,r0);
                                              (1,r1);
                                              (2,r2);
                                              (3,Word pa1);
                                              (4,Word i1);
                                              (5,r5);
                                              (6,r6);
                                              (7,r7);
                      (8,Word (bytes_in_word * n2w (LENGTH (old ++ new))));
                                              (9,r9)] |>)
Proof
  ntac 2 strip_tac \\ completeInduct_on `LENGTH bitmaps - w2n (w - 1w)`
  \\ rpt strip_tac \\ fs [] \\ rpt var_eq_tac \\ fs [PULL_FORALL]
  \\ qpat_x_assum `word_gen_gc_move_bitmaps _ _ = _`
        (fn th => assume_tac th \\ mp_tac th)
  \\ drule (GEN_ALL word_gen_gc_move_bitmaps_unroll) \\ fs []
  \\ CASE_TAC \\ fs []
  \\ Cases_on `word_gen_gc_move_bitmap conf
                  (h,stack,i,pa,ib,pb,curr,s.memory,s.mdomain)`
  \\ fs [] \\ PairCases_on `x` \\ fs [] \\ strip_tac
  \\ `x7` by (every_case_tac \\ fs []) \\ var_eq_tac
  \\ simp_tac std_ss [word_gen_gc_move_bitmaps_code_def,get_var_def,evaluate_def]
  \\ simp_tac std_ss [GSYM word_gen_gc_move_bitmaps_code_def]
  \\ fs [get_var_def,get_var_imm_def] \\ tac
  \\ imp_res_tac DROP_IMP_LESS_LENGTH \\ fs []
  \\ qabbrev_tac `s2 = s with
           <|regs := s.regs |+ (7,Word (EL (w2n (w + -1w)) s.bitmaps)) |>`
  \\ imp_res_tac DROP_IMP_EL \\ fs []
  \\ `s.memory = s2.memory /\ s.mdomain = s2.mdomain` by (unabbrev_all_tac \\ fs [])
  \\ fs []
  \\ drule (word_gen_gc_move_bitmap_code_thm |> GEN_ALL |> SIMP_RULE std_ss [])
  \\ disch_then (qspecl_then [`init`,`old`] mp_tac)
  \\ impl_tac
  THEN1 (unabbrev_all_tac \\ rfs [get_var_def] \\ tac \\ fs [FLOOKUP_DEF])
  \\ strip_tac \\ drule (GEN_ALL evaluate_add_clock)
  \\ reverse (Cases_on `word_msb h`) \\ fs []
  \\ fs [word_msb_IFF_lsr_EQ_0] THEN1
   (disch_then (qspec_then `1` assume_tac)
    \\ qexists_tac `ck+1` \\ unabbrev_all_tac \\ fs [STOP_def] \\ tac
    \\ fs [word_gen_gc_move_bitmaps_code_def] \\ tac
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
             FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less] \\ fs []
    \\ qexists_tac `t0` \\ qexists_tac `t1` \\ rw [] \\ fs [] \\ rw [])
  \\ strip_tac
  \\ Cases_on `word_gen_gc_move_bitmaps conf
       (Word (w + 1w),x1,s.bitmaps,x2,x3,x4,x5,curr,x6,s2.mdomain)` \\ fs []
  \\ rename1 `_ = SOME y` \\ PairCases_on `y` \\ fs []
  \\ rpt var_eq_tac
  \\ qabbrev_tac `s5 = s with
     <|regs :=
         s.regs |+ (7,Word (EL (w2n (w + -1w)) s.bitmaps)) |+ (0,r0) |+
         (1,r1) |+ (2,r2) |+ (3,Word x3) |+ (4,Word x2) |+ (5,r5) |+
         (6,r6) |+ (7,r7) |+
         (8,Word (bytes_in_word * n2w (LENGTH old + LENGTH x0))) |+
         (0,Word (EL (w2n (w + -1w)) s.bitmaps)) |+ (9,Word w) |+
         (0,Word (EL (w2n (w + -1w)) s.bitmaps ⋙ (dimindex (:α) − 1)));
       store :=
         s.store |+ (Temp 0w,t0) |+ (Temp 1w,t1) |+
           (Temp 2w,Word x5) |+ (Temp 3w,Word x4);
       stack := init ++ old ++ x0 ++ x1; memory := x6 |>`
  \\ `LENGTH s5.bitmaps <
      LENGTH s.bitmaps + w2n ((w+1w) + -1w) − w2n (w + -1w)` by
   (unabbrev_all_tac \\ fs [] \\ Cases_on `w` \\ fs []
    \\ fs [word_add_n2w] \\ Cases_on `n` \\ fs []
    \\ fs [GSYM word_add_n2w,ADD1,w2n_minus1] \\ NO_TAC)
  \\ first_x_assum drule \\ fs []
  \\ `x6 = s5.memory /\ s.mdomain = s5.mdomain /\ s.bitmaps = s5.bitmaps` by
       (unabbrev_all_tac \\ fs []) \\ fs []
  \\ disch_then drule
  \\ ntac 3 (pop_assum (fn th => fs [GSYM th]))
  \\ disch_then (qspecl_then [`EL (w2n (w + -1w))
         s5.bitmaps ⋙ (dimindex (:α) - 1)`,`old ++ x0`] mp_tac)
  \\ fs [AND_IMP_INTRO]
  \\ impl_tac THEN1
   (unabbrev_all_tac \\ fs [] \\ tac
    \\ rfs [RIGHT_ADD_DISTRIB]
    \\ imp_res_tac word_gen_gc_move_bitmaps_LENGTH \\ fs [])
  \\ strip_tac
  \\ first_x_assum (qspec_then `ck'+1` assume_tac)
  \\ qexists_tac `ck+ck'+1` \\ fs []
  \\ unabbrev_all_tac \\ fs [] \\ tac
  \\ fs [STOP_def] \\ tac \\ fs []
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less] \\ fs []
  \\ qexists_tac `t0'`
  \\ qexists_tac `t1'`
  \\ rw [] \\ fs [] \\ rw [] \\ fs []
  \\ eq_tac \\ rw[] \\ fs []
QED

Theorem word_gen_gc_partial_move_bitmaps_code_thm:
   !w bitmaps z stack (s:('a,'c,'b)stackSem$state) i pa ib pb curr m dm new
         stack1 a1 i1 pa1 ib1 pb1 m1 old.
      word_gen_gc_partial_move_bitmaps conf
          (Word w,stack,bitmaps,i,pa,curr,m,dm,gs,rs) =
        SOME (new,stack1,i1,pa1,m1,T) /\
      LENGTH bitmaps < dimword (:'a) − 1 ∧ good_dimindex (:'a) /\
      shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ conf.len_size <> 0 /\ good_dimindex (:'a) /\
      (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
      FLOOKUP s.store CurrHeap = SOME (Word curr) /\ s.use_store /\
      s.memory = m /\ s.mdomain = dm /\ s.bitmaps = bitmaps /\ s.use_stack /\
      get_var 0 s = SOME (Word z) /\ z <> 0w /\
      1 IN FDOM s.regs /\
      2 IN FDOM s.regs /\
      get_var 3 s = SOME (Word pa) /\
      get_var 4 s = SOME (Word (i:'a word)) /\
      5 IN FDOM s.regs /\
      6 IN FDOM s.regs /\
      7 IN FDOM s.regs /\
      get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
      get_var 9 s = SOME (Word (w - 1w)) /\
      FLOOKUP s.store (Temp 0w) = SOME (Word gs) /\
      FLOOKUP s.store (Temp 1w) = SOME (Word rs) /\
      s.stack = init ++ old ++ stack /\
      s.stack_space = LENGTH init /\
      (dimindex (:'a) DIV 8) * LENGTH s.stack < dimword (:'a) ==>
      ?ck r0 r1 r2 r5 r6 r7 r9 t0 t1.
        evaluate (word_gen_gc_partial_move_bitmaps_code conf,s with clock := s.clock + ck) =
          (NONE,s with <| memory := m1;
                          stack := init ++ old ++ new ++ stack1;
                          clock := s.clock;
                          regs := s.regs |++ [(0,r0);
                                              (1,r1);
                                              (2,r2);
                                              (3,Word pa1);
                                              (4,Word i1);
                                              (5,r5);
                                              (6,r6);
                                              (7,r7);
                      (8,Word (bytes_in_word * n2w (LENGTH (old ++ new))));
                                              (9,r9)] |>)
Proof
  ntac 2 strip_tac \\ completeInduct_on `LENGTH bitmaps - w2n (w - 1w)`
  \\ rpt strip_tac \\ fs [] \\ rpt var_eq_tac \\ fs [PULL_FORALL]
  \\ qpat_x_assum `word_gen_gc_partial_move_bitmaps _ _ = _`
        (fn th => assume_tac th \\ mp_tac th)
  \\ drule (GEN_ALL word_gen_gc_partial_move_bitmaps_unroll) \\ fs []
  \\ CASE_TAC \\ fs []
  \\ Cases_on `word_gen_gc_partial_move_bitmap conf
                  (h,stack,i,pa,curr,s.memory,s.mdomain,gs,rs)`
  \\ fs [] \\ PairCases_on `x` \\ fs [] \\ strip_tac
  \\ `x5` by (every_case_tac \\ fs []) \\ var_eq_tac
  \\ simp_tac std_ss [word_gen_gc_partial_move_bitmaps_code_def,get_var_def,evaluate_def]
  \\ simp_tac std_ss [GSYM word_gen_gc_partial_move_bitmaps_code_def]
  \\ fs [get_var_def,get_var_imm_def] \\ tac
  \\ imp_res_tac DROP_IMP_LESS_LENGTH \\ fs []
  \\ qabbrev_tac `s2 = s with
           <|regs := s.regs |+ (7,Word (EL (w2n (w + -1w)) s.bitmaps)) |>`
  \\ imp_res_tac DROP_IMP_EL \\ fs []
  \\ `s.memory = s2.memory /\ s.mdomain = s2.mdomain` by (unabbrev_all_tac \\ fs [])
  \\ fs []
  \\ drule (word_gen_gc_partial_move_bitmap_code_thm |> GEN_ALL |> SIMP_RULE std_ss [])
  \\ disch_then (qspecl_then [`init`,`old`] mp_tac)
  \\ impl_tac
  THEN1 (unabbrev_all_tac \\ rfs [get_var_def] \\ tac \\ fs [FLOOKUP_DEF])
  \\ strip_tac \\ drule (GEN_ALL evaluate_add_clock)
  \\ reverse (Cases_on `word_msb h`) \\ fs []
  \\ fs [word_msb_IFF_lsr_EQ_0] THEN1
   (disch_then (qspec_then `1` assume_tac)
    \\ qexists_tac `ck+1` \\ unabbrev_all_tac \\ fs [STOP_def] \\ tac
    \\ fs [word_gen_gc_partial_move_bitmaps_code_def] \\ tac
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
             FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less] \\ fs []
    \\ qexists_tac `t0` \\ qexists_tac `t1` \\ rw [] \\ fs [] \\ rw [])
  \\ strip_tac
  \\ Cases_on `word_gen_gc_partial_move_bitmaps conf
       (Word (w + 1w),x1,s.bitmaps,x2,x3,curr,x4,s2.mdomain,gs,rs)` \\ fs []
  \\ rename1 `_ = SOME y` \\ PairCases_on `y` \\ fs []
  \\ rpt var_eq_tac
  \\ qabbrev_tac `s5 = s with
     <|regs :=
         s.regs |+ (7,Word (EL (w2n (w + -1w)) s.bitmaps)) |+ (0,r0) |+
         (1,r1) |+ (2,r2) |+ (3,Word x3) |+ (4,Word x2) |+ (5,r5) |+
         (6,r6) |+ (7,r7) |+
         (8,Word (bytes_in_word * n2w (LENGTH old + LENGTH x0))) |+
         (0,Word (EL (w2n (w + -1w)) s.bitmaps)) |+ (9,Word w) |+
         (0,Word (EL (w2n (w + -1w)) s.bitmaps ⋙ (dimindex (:α) − 1)));
       stack := init ++ old ++ x0 ++ x1; memory := x4 |>`
  \\ `LENGTH s5.bitmaps <
      LENGTH s.bitmaps + w2n ((w+1w) + -1w) − w2n (w + -1w)` by
   (unabbrev_all_tac \\ fs [] \\ Cases_on `w` \\ fs []
    \\ fs [word_add_n2w] \\ Cases_on `n` \\ fs []
    \\ fs [GSYM word_add_n2w,ADD1,w2n_minus1] \\ NO_TAC)
  \\ first_x_assum drule \\ fs []
  \\ `x4 = s5.memory /\ s.mdomain = s5.mdomain /\ s.bitmaps = s5.bitmaps` by
       (unabbrev_all_tac \\ fs []) \\ fs []
  \\ disch_then drule
  \\ ntac 3 (pop_assum (fn th => fs [GSYM th]))
  \\ disch_then (qspecl_then [`EL (w2n (w + -1w))
         s5.bitmaps ⋙ (dimindex (:α) - 1)`,`old ++ x0`] mp_tac)
  \\ fs [AND_IMP_INTRO]
  \\ impl_tac THEN1
   (unabbrev_all_tac \\ fs [] \\ tac
    \\ rfs [RIGHT_ADD_DISTRIB]
    \\ imp_res_tac word_gen_gc_partial_move_bitmaps_LENGTH \\ fs [])
  \\ strip_tac
  \\ first_x_assum (qspec_then `ck'+1` assume_tac)
  \\ qexists_tac `ck+ck'+1` \\ fs []
  \\ unabbrev_all_tac \\ fs [] \\ tac
  \\ fs [STOP_def] \\ tac \\ fs []
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less] \\ fs []
QED

Theorem word_gen_gc_move_roots_bitmaps_code_thm:
   !bitmaps (s:('a,'c,'b)stackSem$state) i pa ib pb curr m dm new
         stack1 a1 i1 pa1 ib1 pb1 m1 old.
      word_gen_gc_move_roots_bitmaps conf (stack,bitmaps,i,pa,ib,pb,curr,m,dm) =
        (stack1,i1,pa1,ib1,pb1,m1,T) /\
      LENGTH bitmaps < dimword (:'a) - 1 /\ good_dimindex (:'a) /\
      shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ conf.len_size <> 0 /\ good_dimindex (:'a) /\
      (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
      FLOOKUP s.store CurrHeap = SOME (Word curr) /\ s.use_store /\
      s.memory = m /\ s.mdomain = dm /\ s.bitmaps = bitmaps /\ s.use_stack /\
      0 IN FDOM s.regs /\
      1 IN FDOM s.regs /\
      2 IN FDOM s.regs /\
      get_var 3 s = SOME (Word pa) /\
      get_var 4 s = SOME (Word (i:'a word)) /\
      5 IN FDOM s.regs /\
      6 IN FDOM s.regs /\
      7 IN FDOM s.regs /\
      get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
      get_var 9 s = SOME (HD stack) /\
      Temp 0w IN FDOM s.store /\
      Temp 1w IN FDOM s.store /\
      FLOOKUP s.store (Temp 2w) = SOME (Word pb) /\
      FLOOKUP s.store (Temp 3w) = SOME (Word ib) /\
      s.stack = init ++ old ++ stack /\
      s.stack_space = LENGTH init /\
      (dimindex (:'a) DIV 8) * LENGTH s.stack < dimword (:'a) ==>
      ?ck r0 r1 r2 r5 r6 r7 r8 r9 t0 t1.
        evaluate (word_gen_gc_move_roots_bitmaps_code conf,
            s with clock := s.clock + ck) =
          (NONE,s with <| memory := m1;
                          stack := init ++ old ++ stack1;
                          clock := s.clock;
                          store :=
                            s.store |++
                            [(Temp 0w,t0); (Temp 1w,t1); (Temp 2w,Word pb1);
                             (Temp 3w,Word ib1)];
                          regs := s.regs |++ [(0,r0);
                                              (1,r1);
                                              (2,r2);
                                              (3,Word pa1);
                                              (4,Word i1);
                                              (5,r5);
                                              (6,r6);
                                              (7,r7);
                                              (8,r8);
                                              (9,Word 0w)] |>)
Proof
  completeInduct_on `LENGTH stack`
  \\ rpt strip_tac \\ fs [PULL_FORALL]
  \\ rpt var_eq_tac \\ fs []
  \\ qpat_x_assum `word_gen_gc_move_roots_bitmaps _ _ = _`
        (fn th => assume_tac th \\ mp_tac th)
  \\ drule (GEN_ALL word_gen_gc_move_roots_bitmaps) \\ fs []
  \\ Cases_on `stack` \\ fs []
  \\ rename1 `word_gen_gc_move_roots_bitmaps conf (hd::stack,_) = _`
  \\ Cases_on `hd = Word 0w` \\ fs [] THEN1
   (rpt strip_tac \\ rpt var_eq_tac \\ fs []
    \\ simp_tac std_ss [word_gen_gc_move_roots_bitmaps_code_def,get_var_def]
    \\ fs [get_var_def,get_var_imm_def] \\ tac
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less] \\ fs []
    \\ qexists_tac `s.store ' (Temp 0w)`
    \\ qexists_tac `s.store ' (Temp 1w)`
    \\ rw [] \\ eq_tac \\ rw [] \\ fs [])
  \\ Cases_on `word_gen_gc_move_bitmaps conf
       (hd,stack,s.bitmaps,i,pa,ib,pb,curr,s.memory,s.mdomain)` \\ fs []
  \\ PairCases_on `x` \\ fs []
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ fs []
  \\ rpt var_eq_tac \\ fs []
  \\ simp_tac std_ss [word_gen_gc_move_roots_bitmaps_code_def,evaluate_def]
  \\ simp_tac std_ss [GSYM word_gen_gc_move_roots_bitmaps_code_def,get_var_def]
  \\ fs [get_var_def,get_var_imm_def] \\ tac
  \\ reverse (Cases_on `hd`) \\ fs []
  THEN1 (fs[word_gen_gc_move_roots_bitmaps_def,enc_stack_def,full_read_bitmap_def])
  \\ tac
  \\ qabbrev_tac `s2 = s with
      <| clock := s.clock ;
         regs := s.regs |+ (0,Word c) |+ (9,Word (c + -1w)) |+
         (8, Word (bytes_in_word + bytes_in_word * n2w (LENGTH old))) |>`
  \\ `s.memory = s2.memory /\ s.mdomain = s2.mdomain /\ s.bitmaps = s2.bitmaps` by
        (unabbrev_all_tac \\ fs []) \\ fs []
  \\ drule (word_gen_gc_move_bitmaps_code_thm |> SIMP_RULE std_ss [])
  \\ ntac 3 (pop_assum (fn th => fs [GSYM th]))
  \\ disch_then (qspecl_then [`c`,`old ++ [Word c]`] mp_tac)
  \\ impl_tac THEN1
   (unabbrev_all_tac \\ rpt strip_tac
    \\ fs [RIGHT_ADD_DISTRIB]
    \\ rfs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ fs [get_var_def] \\ tac)
  \\ strip_tac \\ fs []
  \\ unabbrev_all_tac \\ fs [] \\ tac
  \\ `(bytes_in_word * n2w (LENGTH old + (LENGTH x0 + 1))) ⋙ word_shift (:α) =
      n2w (LENGTH old + (LENGTH x0 + 1)):'a word` by
   (match_mp_tac bytes_in_word_word_shift_n2w
    \\ imp_res_tac word_gen_gc_move_bitmaps_LENGTH
    \\ rfs [RIGHT_ADD_DISTRIB] \\ fs []) \\ fs []
  \\ `(LENGTH old + (LENGTH x0 + 1)) < dimword (:α)` by
   (imp_res_tac word_gen_gc_move_bitmaps_LENGTH
    \\ rfs [RIGHT_ADD_DISTRIB] \\ fs []
    \\ rfs [labPropsTheory.good_dimindex_def] \\ rfs [] \\ fs[]) \\ fs []
  \\ `0 < LENGTH x1` by
   (Cases_on `x1` \\ fs [word_gen_gc_move_roots_bitmaps_def,enc_stack_def])
  \\ fs [STOP_def] \\ Cases_on `x1` \\ fs []
  \\ `EL (LENGTH init + (LENGTH old + (LENGTH x0 + 1)))
                (init ++ old ++ [Word c] ++ x0 ++ h::t) = h` by
         (match_mp_tac EL_LENGTH_ADD_LEMMA \\ fs []) \\ fs []
  \\ qabbrev_tac `s8 = s with
       <|regs :=
         s.regs |+ (0,Word c) |+ (9,Word (c + -1w)) |+
         (8,Word (bytes_in_word + bytes_in_word * n2w (LENGTH old))) |+
         (0,r0) |+ (1,r1) |+ (2,r2) |+ (3,Word x3) |+ (4,Word x2) |+
         (5,r5) |+ (6,r6) |+ (7,r7) |+
         (8,Word (bytes_in_word * n2w (LENGTH old + (LENGTH x0 + 1)))) |+
         (9,h); stack := init ++ old ++ [Word c] ++ x0 ++ h::t ;
          store :=
            s.store |++
            [(Temp 0w,t0); (Temp 1w,t1); (Temp 2w,Word x5);
             (Temp 3w,Word x4)];
         memory := x6 |>`
  \\ `LENGTH (h::t) < SUC (LENGTH stack)` by
   (imp_res_tac word_gen_gc_move_bitmaps_LENGTH
    \\ rfs [RIGHT_ADD_DISTRIB] \\ fs [])
  \\ first_x_assum drule
  \\ `x6 = s8.memory /\ s.mdomain = s8.mdomain /\ s.bitmaps = s8.bitmaps` by
        (unabbrev_all_tac \\ fs [] \\ NO_TAC) \\ fs []
  \\ disch_then drule
  \\ ntac 3 (pop_assum (fn th => fs [GSYM th]))
  \\ disch_then (qspec_then `old ++ Word c::x0` mp_tac)
  \\ impl_tac THEN1
   (unabbrev_all_tac \\ fs [] \\ tac \\ fs [ADD1,RIGHT_ADD_DISTRIB]
    \\ rfs [] \\ imp_res_tac word_gen_gc_move_bitmaps_LENGTH
    \\ rfs [RIGHT_ADD_DISTRIB] \\ fs []
    \\ rfs [labPropsTheory.good_dimindex_def] \\ rfs [] \\ fs[])
  \\ strip_tac \\ unabbrev_all_tac \\ fs []
  \\ qexists_tac `ck + ck' + 1` \\ fs []
  \\ pop_assum mp_tac
  \\ drule (evaluate_add_clock |> GEN_ALL)
  \\ disch_then (qspec_then `ck' + 1` assume_tac)
  \\ fs [] \\ tac \\ rpt strip_tac
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less] \\ fs []
  \\ qexists_tac `t0'` \\ qexists_tac `t1'`
  \\ rw [] \\ fs [] \\ eq_tac \\ rw [] \\ fs []
QED

Theorem word_gen_gc_partial_move_roots_bitmaps_code_thm:
   !bitmaps (s:('a,'c,'b)stackSem$state) i pa curr m dm new
         stack1 a1 i1 pa1 m1 old.
      word_gen_gc_partial_move_roots_bitmaps conf (stack,bitmaps,i,pa,curr,m,dm,gs,rs) =
        (stack1,i1,pa1,m1,T) /\
      LENGTH bitmaps < dimword (:'a) - 1 /\ good_dimindex (:'a) /\
      shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ conf.len_size <> 0 /\ good_dimindex (:'a) /\
      (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
      FLOOKUP s.store CurrHeap = SOME (Word curr) /\ s.use_store /\
      s.memory = m /\ s.mdomain = dm /\ s.bitmaps = bitmaps /\ s.use_stack /\
      0 IN FDOM s.regs /\
      1 IN FDOM s.regs /\
      2 IN FDOM s.regs /\
      get_var 3 s = SOME (Word pa) /\
      get_var 4 s = SOME (Word (i:'a word)) /\
      5 IN FDOM s.regs /\
      6 IN FDOM s.regs /\
      7 IN FDOM s.regs /\
      get_var 8 s = SOME (Word (bytes_in_word * n2w (LENGTH old))) /\
      get_var 9 s = SOME (HD stack) /\
      FLOOKUP s.store (Temp 0w) = SOME (Word gs) /\
      FLOOKUP s.store (Temp 1w) = SOME (Word rs) /\
      s.stack = init ++ old ++ stack /\
      s.stack_space = LENGTH init /\
      (dimindex (:'a) DIV 8) * LENGTH s.stack < dimword (:'a) ==>
      ?ck r0 r1 r2 r5 r6 r7 r8 r9.
        evaluate (word_gen_gc_partial_move_roots_bitmaps_code conf,
            s with clock := s.clock + ck) =
          (NONE,s with <| memory := m1;
                          stack := init ++ old ++ stack1;
                          clock := s.clock;
                          regs := s.regs |++ [(0,r0);
                                              (1,r1);
                                              (2,r2);
                                              (3,Word pa1);
                                              (4,Word i1);
                                              (5,r5);
                                              (6,r6);
                                              (7,r7);
                                              (8,r8);
                                              (9,Word 0w)] |>)
Proof
  completeInduct_on `LENGTH stack`
  \\ rpt strip_tac \\ fs [PULL_FORALL]
  \\ rpt var_eq_tac \\ fs []
  \\ qpat_x_assum `word_gen_gc_partial_move_roots_bitmaps _ _ = _`
        (fn th => assume_tac th \\ mp_tac th)
  \\ drule (GEN_ALL word_gen_gc_partial_move_roots_bitmaps) \\ fs []
  \\ Cases_on `stack` \\ fs []
  \\ rename1 `word_gen_gc_partial_move_roots_bitmaps conf (hd::stack,_) = _`
  \\ Cases_on `hd = Word 0w` \\ fs [] THEN1
   (rpt strip_tac \\ rpt var_eq_tac \\ fs []
    \\ simp_tac std_ss [word_gen_gc_partial_move_roots_bitmaps_code_def,get_var_def]
    \\ fs [get_var_def,get_var_imm_def] \\ tac
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less] \\ fs [])
  \\ Cases_on `word_gen_gc_partial_move_bitmaps conf
       (hd,stack,s.bitmaps,i,pa,curr,s.memory,s.mdomain,gs,rs)` \\ fs []
  \\ PairCases_on `x` \\ fs []
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ fs []
  \\ rpt var_eq_tac \\ fs []
  \\ simp_tac std_ss [word_gen_gc_partial_move_roots_bitmaps_code_def,evaluate_def]
  \\ simp_tac std_ss [GSYM word_gen_gc_partial_move_roots_bitmaps_code_def,get_var_def]
  \\ fs [get_var_def,get_var_imm_def] \\ tac
  \\ reverse (Cases_on `hd`) \\ fs []
  THEN1 (fs[word_gen_gc_partial_move_roots_bitmaps_def,enc_stack_def,full_read_bitmap_def])
  \\ tac
  \\ qabbrev_tac `s2 = s with
      <| clock := s.clock ;
         regs := s.regs |+ (0,Word c) |+ (9,Word (c + -1w)) |+
         (8, Word (bytes_in_word + bytes_in_word * n2w (LENGTH old))) |>`
  \\ `s.memory = s2.memory /\ s.mdomain = s2.mdomain /\ s.bitmaps = s2.bitmaps` by
        (unabbrev_all_tac \\ fs []) \\ fs []
  \\ drule (word_gen_gc_partial_move_bitmaps_code_thm |> SIMP_RULE std_ss [])
  \\ ntac 3 (pop_assum (fn th => fs [GSYM th]))
  \\ disch_then (qspecl_then [`c`,`old ++ [Word c]`] mp_tac)
  \\ impl_tac THEN1
   (unabbrev_all_tac \\ rpt strip_tac
    \\ fs [RIGHT_ADD_DISTRIB]
    \\ rfs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ fs [get_var_def] \\ tac)
  \\ strip_tac \\ fs []
  \\ unabbrev_all_tac \\ fs [] \\ tac
  \\ `(bytes_in_word * n2w (LENGTH old + (LENGTH x0 + 1))) ⋙ word_shift (:α) =
      n2w (LENGTH old + (LENGTH x0 + 1)):'a word` by
   (match_mp_tac bytes_in_word_word_shift_n2w
    \\ imp_res_tac word_gen_gc_partial_move_bitmaps_LENGTH
    \\ rfs [RIGHT_ADD_DISTRIB] \\ fs []) \\ fs []
  \\ `(LENGTH old + (LENGTH x0 + 1)) < dimword (:α)` by
   (imp_res_tac word_gen_gc_partial_move_bitmaps_LENGTH
    \\ rfs [RIGHT_ADD_DISTRIB] \\ fs []
    \\ rfs [labPropsTheory.good_dimindex_def] \\ rfs [] \\ fs[]) \\ fs []
  \\ `0 < LENGTH x1` by
   (Cases_on `x1` \\ fs [word_gen_gc_partial_move_roots_bitmaps_def,enc_stack_def])
  \\ fs [STOP_def] \\ Cases_on `x1` \\ fs []
  \\ `EL (LENGTH init + (LENGTH old + (LENGTH x0 + 1)))
                (init ++ old ++ [Word c] ++ x0 ++ h::t) = h` by
         (match_mp_tac EL_LENGTH_ADD_LEMMA \\ fs []) \\ fs []
  \\ qabbrev_tac `s8 = s with
       <|regs :=
         s.regs |+ (0,Word c) |+ (9,Word (c + -1w)) |+
         (8,Word (bytes_in_word + bytes_in_word * n2w (LENGTH old))) |+
         (0,r0) |+ (1,r1) |+ (2,r2) |+ (3,Word x3) |+ (4,Word x2) |+
         (5,r5) |+ (6,r6) |+ (7,r7) |+
         (8,Word (bytes_in_word * n2w (LENGTH old + (LENGTH x0 + 1)))) |+
         (9,h); stack := init ++ old ++ [Word c] ++ x0 ++ h::t ;
         memory := x4 |>`
  \\ `LENGTH (h::t) < SUC (LENGTH stack)` by
   (imp_res_tac word_gen_gc_partial_move_bitmaps_LENGTH
    \\ rfs [RIGHT_ADD_DISTRIB] \\ fs [])
  \\ first_x_assum drule
  \\ `x4 = s8.memory /\ s.mdomain = s8.mdomain /\ s.bitmaps = s8.bitmaps` by
        (unabbrev_all_tac \\ fs [] \\ NO_TAC) \\ fs []
  \\ disch_then drule
  \\ ntac 3 (pop_assum (fn th => fs [GSYM th]))
  \\ disch_then (qspec_then `old ++ Word c::x0` mp_tac)
  \\ impl_tac THEN1
   (unabbrev_all_tac \\ fs [] \\ tac \\ fs [ADD1,RIGHT_ADD_DISTRIB]
    \\ rfs [] \\ imp_res_tac word_gen_gc_partial_move_bitmaps_LENGTH
    \\ rfs [RIGHT_ADD_DISTRIB] \\ fs []
    \\ rfs [labPropsTheory.good_dimindex_def] \\ rfs [] \\ fs[])
  \\ strip_tac \\ unabbrev_all_tac \\ fs []
  \\ qexists_tac `ck + ck' + 1` \\ fs []
  \\ pop_assum mp_tac
  \\ drule (evaluate_add_clock |> GEN_ALL)
  \\ disch_then (qspec_then `ck' + 1` assume_tac)
  \\ fs [] \\ tac \\ rpt strip_tac
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less] \\ fs []
QED

Theorem word_gen_gc_move_list_code_thm:
   !l a (s:('a,'c,'b)stackSem$state) pa1 pa old m1 m i1 i dm conf a1 ib ib1 pb pb1.
      word_gen_gc_move_list conf (a:'a word,l,i,pa,ib,pb,old,m,dm) =
         (a1,i1,pa1,ib1,pb1,m1,T) /\
      shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ conf.len_size <> 0 /\
      (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
      FLOOKUP s.store CurrHeap = SOME (Word old) /\ s.use_store /\
      s.memory = m /\ s.mdomain = dm /\
      Temp 0w IN FDOM s.store /\
      Temp 1w IN FDOM s.store /\
      FLOOKUP s.store (Temp 2w) = SOME (Word pb) /\
      FLOOKUP s.store (Temp 3w) = SOME (Word ib) /\
      0 IN FDOM s.regs /\
      1 IN FDOM s.regs /\
      2 IN FDOM s.regs /\
      get_var 3 s = SOME (Word pa) /\
      get_var 4 s = SOME (Word (i:'a word)) /\
      5 IN FDOM s.regs ==>
      6 IN FDOM s.regs ==>
      get_var 7 s = SOME (Word l) /\
      get_var 8 s = SOME (Word a) ==>
      ?ck r0 r1 r2 r5 r6 t0 t1.
        evaluate (word_gen_gc_move_list_code conf,s with clock := s.clock + ck) =
          (NONE,s with <| memory := m1;
                          store :=
                            s.store |++
                            [(Temp 0w,t0); (Temp 1w,t1); (Temp 2w,Word pb1);
                             (Temp 3w,Word ib1)];
                          regs := s.regs |++ [(0,r0);
                                              (1,r1);
                                              (2,r2);
                                              (3,Word pa1);
                                              (4,Word i1);
                                              (5,r5);
                                              (6,r6);
                                              (7,Word 0w);
                                              (8,Word a1)] |>)
Proof
  Cases \\ Induct_on `n` \\ simp [] THEN1
   (fs [Once word_gen_gc_move_list_def] \\ rw []
    \\ qexists_tac `0`
    \\ fs [word_gen_gc_move_list_code_def,get_var_def] \\ tac
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less]
    \\ qexists_tac `s.store ' (Temp 0w)`
    \\ qexists_tac `s.store ' (Temp 1w)`
    \\ rw [] \\ eq_tac \\ rw[] \\ fs [])
  \\ once_rewrite_tac [word_gen_gc_move_list_def] \\ simp [LET_THM]
  \\ rpt strip_tac \\ simp [LET_THM]
  \\ qpat_x_assum `_ = (a1,i1,pa1,ib1,pb1,m1,T)` mp_tac
  \\ `n2w (SUC n) + -1w = n2w n` by fs [ADD1,GSYM word_add_n2w]
  \\ pairarg_tac \\ simp []
  \\ pairarg_tac \\ simp []
  \\ strip_tac
  \\ rpt var_eq_tac
  \\ `n < dimword (:'a)` by decide_tac
  \\ first_x_assum drule
  \\ disch_then drule
  \\ fs [] \\ strip_tac
  \\ rpt var_eq_tac \\ fs []
  \\ simp [word_gen_gc_move_list_code_def,evaluate_def]
  \\ fs [GSYM word_gen_gc_move_list_code_def,get_var_def,get_var_imm_def]
  \\ tac
  \\ drule (word_gen_gc_move_code_thm |> GEN_ALL)
  \\ fs [ADD1,GSYM word_add_n2w]
  \\ `FLOOKUP ((s:('a,'c,'b)stackSem$state) with
           <|regs := s.regs |+ (5,s.memory a) |+ (7,Word (n2w n)) |>).store
       CurrHeap  = SOME (Word old)` by fs []
  \\ disch_then drule \\ fs [get_var_def] \\ tac \\ strip_tac
  \\ fs []
  \\ first_x_assum (qspec_then `s with
        <|regs :=
            s.regs |+ (5,s.memory a) |+ (7,Word (n2w n)) |+ (0,r0) |+
            (1,r1) |+ (2,r2) |+ (3,Word pa1') |+ (4,Word i1') |+
            (5,w1) |+ (6,r6) |+ (8,Word (a + bytes_in_word));
          store :=
            s.store |+ (Temp 0w,t0) |+ (Temp 1w,t1) |+
            (Temp 2w,Word pb') |+ (Temp 3w,Word ib');
          memory := (a =+ w1) m1' |>` mp_tac)
  \\ rpt (impl_tac THEN1 (fs [] \\ tac)) \\ fs []
  \\ strip_tac \\ fs []
  \\ qexists_tac `ck+ck'+1` \\ fs []
  \\ pop_assum mp_tac
  \\ drule (evaluate_add_clock |> GEN_ALL)
  \\ disch_then (qspec_then `ck'+1` strip_assume_tac)
  \\ fs [AC ADD_COMM ADD_ASSOC] \\ tac
  \\ strip_tac
  \\ drule (evaluate_add_clock |> GEN_ALL)
  \\ disch_then (qspec_then `ck` strip_assume_tac)
  \\ fs [AC ADD_COMM ADD_ASSOC] \\ tac
  \\ fs [STOP_def]
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
         FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less]
  \\ qexists_tac `t0'` \\ qexists_tac `t1'`
  \\ rw [] \\ eq_tac \\ rw [] \\ fs []
QED

Theorem word_gen_gc_partial_move_list_code_thm:
   !l a (s:('a,'c,'b)stackSem$state) pa1 pa old m1 m i1 i dm conf a1 gs rs.
      word_gen_gc_partial_move_list conf (a:'a word,l,i,pa,old,m,dm,gs,rs) =
         (a1,i1,pa1,m1,T) /\
      shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ conf.len_size <> 0 /\
      (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
      FLOOKUP s.store CurrHeap = SOME (Word old) /\ s.use_store /\
      s.memory = m /\ s.mdomain = dm /\ good_dimindex (:'a) /\
      FLOOKUP s.store (Temp 0w) = SOME (Word gs) /\
      FLOOKUP s.store (Temp 1w) = SOME (Word rs) /\
      0 IN FDOM s.regs /\
      1 IN FDOM s.regs /\
      2 IN FDOM s.regs /\
      get_var 3 s = SOME (Word pa) /\
      get_var 4 s = SOME (Word (i:'a word)) /\
      5 IN FDOM s.regs ==>
      6 IN FDOM s.regs ==>
      get_var 7 s = SOME (Word l) /\
      get_var 8 s = SOME (Word a) ==>
      ?ck r0 r1 r2 r5 r6.
        evaluate (word_gen_gc_partial_move_list_code conf,s with clock := s.clock + ck) =
          (NONE,s with <| memory := m1;
                          regs := s.regs |++ [(0,r0);
                                              (1,r1);
                                              (2,r2);
                                              (3,Word pa1);
                                              (4,Word i1);
                                              (5,r5);
                                              (6,r6);
                                              (7,Word 0w);
                                              (8,Word a1)] |>)
Proof
  Cases \\ Induct_on `n` \\ simp [] THEN1
   (fs [Once word_gen_gc_partial_move_list_def] \\ rw []
    \\ qexists_tac `0`
    \\ fs [word_gen_gc_partial_move_list_code_def,get_var_def] \\ tac
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less])
  \\ once_rewrite_tac [word_gen_gc_partial_move_list_def] \\ simp [LET_THM]
  \\ rpt strip_tac \\ simp [LET_THM]
  \\ qpat_x_assum `_ = (a1,i1,pa1,m1,T)` mp_tac
  \\ `n2w (SUC n) + -1w = n2w n` by fs [ADD1,GSYM word_add_n2w]
  \\ pairarg_tac \\ simp []
  \\ pairarg_tac \\ simp []
  \\ strip_tac
  \\ rpt var_eq_tac
  \\ `n < dimword (:'a)` by decide_tac
  \\ first_x_assum drule
  \\ disch_then drule
  \\ fs [] \\ strip_tac
  \\ rpt var_eq_tac \\ fs []
  \\ simp [word_gen_gc_partial_move_list_code_def,evaluate_def]
  \\ fs [GSYM word_gen_gc_partial_move_list_code_def,get_var_def,get_var_imm_def]
  \\ tac
  \\ drule (word_gen_gc_partial_move_code_thm |> GEN_ALL)
  \\ fs [ADD1,GSYM word_add_n2w]
  \\ `FLOOKUP ((s:('a,'c,'b)stackSem$state) with
           <|regs := s.regs |+ (5,s.memory a) |+ (7,Word (n2w n)) |>).store
       CurrHeap  = SOME (Word old)` by fs []
  \\ disch_then drule \\ fs [get_var_def] \\ tac \\ strip_tac
  \\ fs []
  \\ first_x_assum (qspec_then `s with
        <|regs :=
            s.regs |+ (5,s.memory a) |+ (7,Word (n2w n)) |+ (0,r0) |+
            (1,r1) |+ (2,r2) |+ (3,Word pa1') |+ (4,Word i1') |+
            (5,w1) |+ (6,r6) |+ (8,Word (a + bytes_in_word));
          memory := (a =+ w1) m1' |>` mp_tac)
  \\ rpt (impl_tac THEN1 (fs [] \\ tac)) \\ fs []
  \\ strip_tac \\ fs []
  \\ qexists_tac `ck+ck'+1` \\ fs []
  \\ pop_assum mp_tac
  \\ drule (evaluate_add_clock |> GEN_ALL)
  \\ disch_then (qspec_then `ck'+1` strip_assume_tac)
  \\ fs [AC ADD_COMM ADD_ASSOC] \\ tac
  \\ strip_tac
  \\ drule (evaluate_add_clock |> GEN_ALL)
  \\ disch_then (qspec_then `ck` strip_assume_tac)
  \\ fs [AC ADD_COMM ADD_ASSOC] \\ tac
  \\ fs [STOP_def]
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
         FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less]
QED

val word_gen_gc_partial_move_ref_list_code_thm = Q.prove(
  `!k r2a1 r1a1 r2a2 i1 pa1 ib1 pb1 old1 m1 dm1 c1 i2 pa2 ib2 pb2 m2 (s:('a,'c,'b)stackSem$state).
      word_gen_gc_partial_move_ref_list k conf (r1a1,i1,pa1,old1,m1,dm1,T,gs,rs,r2a1) =
        (i2,pa2,m2,T) /\
      shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ conf.len_size <> 0 /\
      conf.len_size + 2 < dimindex (:'a) /\ good_dimindex (:α) /\
      (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
      FLOOKUP s.store CurrHeap = SOME (Word old1) /\ s.use_store /\
      s.memory = m1 /\ s.mdomain = dm1 /\
      FLOOKUP s.store (Temp 0w) = SOME (Word gs) /\
      FLOOKUP s.store (Temp 1w) = SOME (Word rs) /\
      0 IN FDOM s.regs /\
      1 IN FDOM s.regs /\
      2 IN FDOM s.regs /\
      get_var 3 s = SOME (Word pa1) /\
      get_var 4 s = SOME (Word (i1:'a word)) /\
      5 IN FDOM s.regs /\
      6 IN FDOM s.regs /\
      7 IN FDOM s.regs /\
      get_var 8 s = SOME (Word r1a1) /\
      get_var 9 s = SOME (Word r2a1) ==>
      ?ck r0 r1 r2 r5 r6 r7 r8 r9.
        evaluate (word_gen_gc_partial_move_ref_list_code conf,s with clock := s.clock + ck) =
          (NONE,s with <| memory := m2;
                          regs := s.regs |++ [(0,r0);
                                              (1,r1);
                                              (2,r2);
                                              (3,Word pa2);
                                              (4,Word i2);
                                              (5,r5);
                                              (6,r6);
                                              (7,r7);
                                              (8,r8);
                                              (9,r9)] |>)`,
  strip_tac \\ completeInduct_on `k` \\ rpt strip_tac
  \\ qpat_x_assum `word_gen_gc_partial_move_ref_list _ _ _ = _` mp_tac
  \\ once_rewrite_tac [word_gen_gc_partial_move_ref_list_def]
  \\ IF_CASES_TAC THEN1
   (fs [] \\ rw [] \\ fs [] \\ rpt var_eq_tac
    \\ fs [word_gen_gc_partial_move_ref_list_code_def,get_var_def] \\ tac
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less])
  \\ IF_CASES_TAC \\ fs []
  \\ `k-1 < k` by decide_tac
  \\ first_x_assum drule \\ ntac 2 (pop_assum kall_tac) \\ strip_tac
  \\ rpt var_eq_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ strip_tac \\ rveq \\ fs []
  \\ asm_simp_tac std_ss[word_gen_gc_partial_move_ref_list_code_def,evaluate_def]
  \\ asm_simp_tac std_ss[GSYM word_gen_gc_partial_move_ref_list_code_def,STOP_def]
  \\ rev_full_simp_tac(srw_ss())[] \\ rpt var_eq_tac
  \\ fs [get_var_def,isWord_thm,clear_top_inst_def] \\ tac
  \\ full_simp_tac(srw_ss())[theWord_def] \\ tac
  \\ rev_full_simp_tac(srw_ss())[select_lower_lemma,
       DECIDE ``n<>0 ==> m-(n-1)-1=m-n:num``,theWord_def]
  \\ rev_full_simp_tac(srw_ss())
         [decode_length_def,LET_THM] \\ rpt var_eq_tac
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs [] \\ tac
  \\ imp_res_tac word_gen_gc_partial_move_ref_list_ok \\ tac \\ rveq \\ tac
  \\ qabbrev_tac `s5 = s with
        <|regs :=
            s.regs |+
            (7,Word (v ⋙ (dimindex (:'a) − conf.len_size))) |+
            (8,Word (r1a1 + bytes_in_word)) |>`
  \\ drule word_gen_gc_partial_move_list_code_thm
  \\ disch_then (qspec_then `s5` mp_tac)
  \\ fs [AND_IMP_INTRO] \\ impl_tac
  THEN1 (unabbrev_all_tac \\ fs [FLOOKUP_UPDATE,get_var_def,theWord_def]
         \\ fs [get_var_def,FLOOKUP_DEF])
  \\ strip_tac \\ fs [GSYM CONJ_ASSOC]
  \\ pop_assum mp_tac
  \\ qpat_abbrev_tac `s6 = s5 with <|regs := _ ; memory := _ |>`
  \\ `s.mdomain = s6.mdomain /\ m1 = s6.memory` by (unabbrev_all_tac \\ fs [])
  \\ fs [] (* \\ qpat_x_assum `_ = _` kall_tac *)
  \\ first_x_assum drule \\ impl_tac
  THEN1 (unabbrev_all_tac \\ fs [FUPDATE_LIST,FLOOKUP_UPDATE])
  \\ rpt strip_tac \\ qexists_tac `ck + ck' + 1`
  \\ drule (evaluate_add_clock |> GEN_ALL)
  \\ disch_then (qspec_then `ck'+1` mp_tac) \\ fs []
  \\ qunabbrev_tac `s5` \\ fs [] \\ strip_tac
  \\ qunabbrev_tac `s6`
  \\ fs [theWord_def,FLOOKUP_UPDATE,FUPDATE_LIST]
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
         FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less]);

val word_gen_gc_move_data_code_thm = Q.prove(
  `!k ha1 i1 pa1 ib1 pb1 old1 m1 dm1 c1 i2 pa2 ib2 pb2 m2 (s:('a,'c,'b)stackSem$state).
      word_gen_gc_move_data conf k (ha1,i1,pa1,ib1,pb1,old1,m1,dm1) =
        (i2,pa2,ib2,pb2,m2,T) /\
      shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ conf.len_size <> 0 /\
      conf.len_size + 2 < dimindex (:'a) /\
      (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
      FLOOKUP s.store CurrHeap = SOME (Word old1) /\ s.use_store /\
      s.memory = m1 /\ s.mdomain = dm1 /\
      Temp 0w IN FDOM s.store /\
      Temp 1w IN FDOM s.store /\
      FLOOKUP s.store (Temp 2w) = SOME (Word pb1) /\
      FLOOKUP s.store (Temp 3w) = SOME (Word ib1) /\
      0 IN FDOM s.regs /\
      1 IN FDOM s.regs /\
      2 IN FDOM s.regs /\
      get_var 3 s = SOME (Word pa1) /\
      get_var 4 s = SOME (Word (i1:'a word)) /\
      5 IN FDOM s.regs ==>
      6 IN FDOM s.regs ==>
      7 IN FDOM s.regs ==>
      get_var 8 s = SOME (Word ha1) /\ c1 ==>
      ?ck r0 r1 r2 r5 r6 r7 t0 t1.
        evaluate (word_gen_gc_move_data_code conf,s with clock := s.clock + ck) =
          (NONE,s with <| memory := m2;
                          store :=
                            s.store |++
                            [(Temp 0w,t0); (Temp 1w,t1); (Temp 2w,Word pb2);
                             (Temp 3w,Word ib2)];
                          regs := s.regs |++ [(0,r0);
                                              (1,r1);
                                              (2,r2);
                                              (3,Word pa2);
                                              (4,Word i2);
                                              (5,r5);
                                              (6,r6);
                                              (7,r7);
                                              (8,Word pa2)] |>)`,
  strip_tac \\ completeInduct_on `k` \\ rpt strip_tac
  \\ qpat_x_assum `word_gen_gc_move_data _ _ _ = _` mp_tac
  \\ once_rewrite_tac [word_gen_gc_move_data_def]
  \\ IF_CASES_TAC THEN1
   (fs [] \\ rw [] \\ fs [] \\ rpt var_eq_tac
    \\ fs [word_gen_gc_move_data_code_def,get_var_def] \\ tac
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less]
    \\ qexists_tac `s.store ' (Temp 0w)`
    \\ qexists_tac `s.store ' (Temp 1w)`
    \\ rw [] \\ eq_tac \\ rw[] \\ fs [])
  \\ IF_CASES_TAC \\ fs []
  \\ `k-1 < k` by decide_tac
  \\ first_x_assum drule \\ ntac 2 (pop_assum kall_tac) \\ strip_tac
  \\ rpt var_eq_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ Cases_on `word_bit 2 (theWord (s.memory ha1))`
  \\ fs [word_bit_test] THEN1
   (rpt strip_tac \\ fs [] \\ fs [] \\ rveq
    \\ asm_simp_tac std_ss[word_gen_gc_move_data_code_def,evaluate_def]
    \\ asm_simp_tac std_ss[GSYM word_gen_gc_move_data_code_def,STOP_def]
    \\ fs [get_var_def,isWord_thm,clear_top_inst_def] \\ tac
    \\ rev_full_simp_tac(srw_ss())
         [decode_length_def,LET_THM] \\ rpt var_eq_tac
    \\ full_simp_tac(srw_ss())[theWord_def] \\ tac
    \\ rev_full_simp_tac(srw_ss())[select_lower_lemma,
         DECIDE ``n<>0 ==> m-(n-1)-1=m-n:num``,theWord_def]
    \\ qabbrev_tac `ww = bytes_in_word *
          (v ⋙ (dimindex (:α) − conf.len_size) + 1w)`
    \\ qabbrev_tac `s5 = s with
        <|regs := s.regs |+ (7,Word v) |+
                            (7,Word ww) |+ (8,Word (ha1 + ww)) |>`
    \\ `s.memory = s5.memory /\ s.mdomain = s5.mdomain` by
         (unabbrev_all_tac \\ fs [])
    \\ fs [] \\ first_x_assum drule \\ fs []
    \\ fs [AND_IMP_INTRO] \\ impl_tac
    THEN1 (unabbrev_all_tac \\ fs [FLOOKUP_UPDATE])
    \\ strip_tac \\ qexists_tac `ck + 1` \\ fs []
    \\ qunabbrev_tac `s5` \\ fs []
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less]
    \\ qexists_tac `t0` \\ qexists_tac `t1`
    \\ rw [] \\ eq_tac \\ rw[] \\ fs [])
  \\ rpt strip_tac
  \\ asm_simp_tac std_ss[word_gen_gc_move_data_code_def,evaluate_def]
  \\ asm_simp_tac std_ss[GSYM word_gen_gc_move_data_code_def,STOP_def]
  \\ rev_full_simp_tac(srw_ss())[] \\ rpt var_eq_tac
  \\ fs [get_var_def,isWord_thm,clear_top_inst_def] \\ tac
  \\ full_simp_tac(srw_ss())[theWord_def] \\ tac
  \\ rev_full_simp_tac(srw_ss())[select_lower_lemma,
       DECIDE ``n<>0 ==> m-(n-1)-1=m-n:num``,theWord_def]
  \\ rev_full_simp_tac(srw_ss())
         [decode_length_def,LET_THM] \\ rpt var_eq_tac
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs [] \\ tac
  \\ qabbrev_tac `s5 = s with
        <|regs :=
            s.regs |+ (7,Word v) |+
            (7,Word (v ⋙ (dimindex (:'a) − conf.len_size))) |+
            (8,Word (ha1 + bytes_in_word)) |>`
  \\ drule word_gen_gc_move_list_code_thm
  \\ disch_then (qspec_then `s5` mp_tac)
  \\ fs [AND_IMP_INTRO] \\ impl_tac
  THEN1 (unabbrev_all_tac \\ fs [FLOOKUP_UPDATE,get_var_def,theWord_def])
  \\ strip_tac \\ fs [GSYM CONJ_ASSOC]
  \\ pop_assum mp_tac
  \\ qpat_abbrev_tac `s6 = s5 with <|regs := _ ; store := _ ; memory := _ |>`
  \\ `s.mdomain = s6.mdomain /\ m'' = s6.memory` by (unabbrev_all_tac \\ fs [])
  \\ qpat_x_assum `Abbrev _` assume_tac
  \\ fs [] \\ qpat_x_assum `_ = _` kall_tac
  \\ first_x_assum drule \\ impl_tac
  THEN1 (unabbrev_all_tac \\ fs [FUPDATE_LIST,FLOOKUP_UPDATE])
  \\ rpt strip_tac \\ qexists_tac `ck + ck' + 1`
  \\ drule (evaluate_add_clock |> GEN_ALL)
  \\ disch_then (qspec_then `ck'+1` mp_tac) \\ fs []
  \\ qunabbrev_tac `s5` \\ fs [] \\ strip_tac
  \\ qunabbrev_tac `s6`
  \\ fs [theWord_def]
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
         FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less]
  \\ qexists_tac `t0'` \\ qexists_tac `t1'`
  \\ rw [] \\ eq_tac \\ rw[] \\ fs []);

val word_gen_gc_partial_move_data_code_thm = Q.prove(
  `!k ha1 i1 pa1 old1 m1 dm1 c1 i2 pa2 m2 (s:('a,'c,'b)stackSem$state).
      word_gen_gc_partial_move_data conf k (ha1,i1,pa1,old1,m1,dm1,gs,rs) =
        (i2,pa2,m2,T) /\
      shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ conf.len_size <> 0 /\
      conf.len_size + 2 < dimindex (:'a) /\
      (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
      FLOOKUP s.store CurrHeap = SOME (Word old1) /\ s.use_store /\
      s.memory = m1 /\ s.mdomain = dm1 /\ good_dimindex (:'a) /\
      FLOOKUP s.store (Temp 0w) = SOME (Word gs) /\
      FLOOKUP s.store (Temp 1w) = SOME (Word rs) /\
      0 IN FDOM s.regs /\
      1 IN FDOM s.regs /\
      2 IN FDOM s.regs /\
      get_var 3 s = SOME (Word pa1) /\
      get_var 4 s = SOME (Word (i1:'a word)) /\
      5 IN FDOM s.regs ==>
      6 IN FDOM s.regs ==>
      7 IN FDOM s.regs ==>
      get_var 8 s = SOME (Word ha1) /\ c1 ==>
      ?ck r0 r1 r2 r5 r6 r7 t0 t1.
        evaluate (word_gen_gc_partial_move_data_code conf,s with clock := s.clock + ck) =
          (NONE,s with <| memory := m2;
                          regs := s.regs |++ [(0,r0);
                                              (1,r1);
                                              (2,r2);
                                              (3,Word pa2);
                                              (4,Word i2);
                                              (5,r5);
                                              (6,r6);
                                              (7,r7);
                                              (8,Word pa2)] |>)`,
  strip_tac \\ completeInduct_on `k` \\ rpt strip_tac
  \\ qpat_x_assum `word_gen_gc_partial_move_data _ _ _ = _` mp_tac
  \\ once_rewrite_tac [word_gen_gc_partial_move_data_def]
  \\ IF_CASES_TAC THEN1
   (fs [] \\ rw [] \\ fs [] \\ rpt var_eq_tac
    \\ fs [word_gen_gc_partial_move_data_code_def,get_var_def] \\ tac
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less])
  \\ IF_CASES_TAC \\ fs []
  \\ `k-1 < k` by decide_tac
  \\ first_x_assum drule \\ ntac 2 (pop_assum kall_tac) \\ strip_tac
  \\ rpt var_eq_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ Cases_on `word_bit 2 (theWord (s.memory ha1))`
  \\ fs [word_bit_test] THEN1
   (rpt strip_tac \\ fs [] \\ fs [] \\ rveq
    \\ asm_simp_tac std_ss[word_gen_gc_partial_move_data_code_def,evaluate_def]
    \\ asm_simp_tac std_ss[GSYM word_gen_gc_partial_move_data_code_def,STOP_def]
    \\ fs [get_var_def,isWord_thm,clear_top_inst_def] \\ tac
    \\ rev_full_simp_tac(srw_ss())
         [decode_length_def,LET_THM] \\ rpt var_eq_tac
    \\ full_simp_tac(srw_ss())[theWord_def] \\ tac
    \\ rev_full_simp_tac(srw_ss())[select_lower_lemma,
         DECIDE ``n<>0 ==> m-(n-1)-1=m-n:num``,theWord_def]
    \\ qabbrev_tac `ww = bytes_in_word *
          (v ⋙ (dimindex (:α) − conf.len_size) + 1w)`
    \\ qabbrev_tac `s5 = s with
        <|regs := s.regs |+ (7,Word v) |+
                            (7,Word ww) |+ (8,Word (ha1 + ww)) |>`
    \\ `s.memory = s5.memory /\ s.mdomain = s5.mdomain` by
         (unabbrev_all_tac \\ fs [])
    \\ fs [] \\ first_x_assum drule \\ fs []
    \\ fs [AND_IMP_INTRO] \\ impl_tac
    THEN1 (unabbrev_all_tac \\ fs [FLOOKUP_UPDATE])
    \\ strip_tac \\ qexists_tac `ck + 1` \\ fs []
    \\ qunabbrev_tac `s5` \\ fs []
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less])
  \\ rpt strip_tac
  \\ asm_simp_tac std_ss[word_gen_gc_partial_move_data_code_def,evaluate_def]
  \\ asm_simp_tac std_ss[GSYM word_gen_gc_partial_move_data_code_def,STOP_def]
  \\ rev_full_simp_tac(srw_ss())[] \\ rpt var_eq_tac
  \\ fs [get_var_def,isWord_thm,clear_top_inst_def] \\ tac
  \\ full_simp_tac(srw_ss())[theWord_def] \\ tac
  \\ rev_full_simp_tac(srw_ss())[select_lower_lemma,
       DECIDE ``n<>0 ==> m-(n-1)-1=m-n:num``,theWord_def]
  \\ rev_full_simp_tac(srw_ss())
         [decode_length_def,LET_THM] \\ rpt var_eq_tac
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs [] \\ tac
  \\ qabbrev_tac `s5 = s with
        <|regs :=
            s.regs |+ (7,Word v) |+
            (7,Word (v ⋙ (dimindex (:'a) − conf.len_size))) |+
            (8,Word (ha1 + bytes_in_word)) |>`
  \\ drule word_gen_gc_partial_move_list_code_thm
  \\ disch_then (qspec_then `s5` mp_tac)
  \\ fs [AND_IMP_INTRO] \\ impl_tac
  THEN1 (unabbrev_all_tac \\ fs [FLOOKUP_UPDATE,get_var_def,theWord_def])
  \\ strip_tac \\ fs [GSYM CONJ_ASSOC]
  \\ pop_assum mp_tac
  \\ qpat_abbrev_tac `s6 = s5 with <|regs := _ ; memory := _ |>`
  \\ `s.mdomain = s6.mdomain /\ m'' = s6.memory` by (unabbrev_all_tac \\ fs [])
  \\ qpat_x_assum `Abbrev _` assume_tac
  \\ fs [] \\ qpat_x_assum `_ = _` kall_tac
  \\ first_x_assum drule \\ impl_tac
  THEN1 (unabbrev_all_tac \\ fs [FUPDATE_LIST,FLOOKUP_UPDATE])
  \\ rpt strip_tac \\ qexists_tac `ck + ck' + 1`
  \\ drule (evaluate_add_clock |> GEN_ALL)
  \\ disch_then (qspec_then `ck'+1` mp_tac) \\ fs []
  \\ qunabbrev_tac `s5` \\ fs [] \\ strip_tac
  \\ qunabbrev_tac `s6`
  \\ fs [theWord_def]
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
         FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less]);

val word_gen_gc_move_refs_code_thm = Q.prove(
  `!k r2a1 r1a1 r2a2 i1 pa1 ib1 pb1 old1 m1 dm1 c1 i2 pa2 ib2 pb2 m2 (s:('a,'c,'b)stackSem$state).
      word_gen_gc_move_refs conf k (r2a1,r1a1,i1,pa1,ib1,pb1,old1,m1,dm1) =
        (r2a2,i2,pa2,ib2,pb2,m2,T) /\
      shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ conf.len_size <> 0 /\
      conf.len_size + 2 < dimindex (:'a) /\
      (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
      FLOOKUP s.store CurrHeap = SOME (Word old1) /\ s.use_store /\
      s.memory = m1 /\ s.mdomain = dm1 /\
      Temp 0w IN FDOM s.store /\
      Temp 1w IN FDOM s.store /\
      FLOOKUP s.store (Temp 2w) = SOME (Word pb1) /\
      FLOOKUP s.store (Temp 3w) = SOME (Word ib1) /\
      FLOOKUP s.store (Temp 4w) = SOME (Word r1a1) /\
      get_var 0 s = SOME (Word r1a1) /\
      1 IN FDOM s.regs /\
      2 IN FDOM s.regs /\
      get_var 3 s = SOME (Word pa1) /\
      get_var 4 s = SOME (Word (i1:'a word)) /\
      5 IN FDOM s.regs ==>
      6 IN FDOM s.regs ==>
      7 IN FDOM s.regs ==>
      get_var 8 s = SOME (Word r2a1) /\ c1 ==>
      ?ck r1 r2 r5 r6 r7 t0 t1.
        evaluate (word_gen_gc_move_refs_code conf,s with clock := s.clock + ck) =
          (NONE,s with <| memory := m2;
                          store :=
                            s.store |++
                            [(Temp 0w,t0); (Temp 1w,t1); (Temp 2w,Word pb2);
                             (Temp 3w,Word ib2)];
                          regs := s.regs |++ [(0,Word r1a1);
                                              (1,r1);
                                              (2,r2);
                                              (3,Word pa2);
                                              (4,Word i2);
                                              (5,r5);
                                              (6,r6);
                                              (7,r7);
                                              (8,Word r2a2)] |>)`,
  strip_tac \\ completeInduct_on `k` \\ rpt strip_tac
  \\ qpat_x_assum `word_gen_gc_move_refs _ _ _ = _` mp_tac
  \\ once_rewrite_tac [word_gen_gc_move_refs_def]
  \\ IF_CASES_TAC THEN1
   (fs [] \\ rw [] \\ fs [] \\ rpt var_eq_tac
    \\ fs [word_gen_gc_move_refs_code_def,get_var_def] \\ tac
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less]
    \\ qexists_tac `s.store ' (Temp 0w)`
    \\ qexists_tac `s.store ' (Temp 1w)`
    \\ rw [] \\ eq_tac \\ rw[] \\ fs [])
  \\ IF_CASES_TAC \\ fs []
  \\ `k-1 < k` by decide_tac
  \\ first_x_assum drule \\ ntac 2 (pop_assum kall_tac) \\ strip_tac
  \\ rpt var_eq_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ strip_tac \\ rveq \\ fs []
  \\ asm_simp_tac std_ss[word_gen_gc_move_refs_code_def,evaluate_def]
  \\ asm_simp_tac std_ss[GSYM word_gen_gc_move_refs_code_def,STOP_def]
  \\ rev_full_simp_tac(srw_ss())[] \\ rpt var_eq_tac
  \\ fs [get_var_def,isWord_thm,clear_top_inst_def] \\ tac
  \\ full_simp_tac(srw_ss())[theWord_def] \\ tac
  \\ rev_full_simp_tac(srw_ss())[select_lower_lemma,
       DECIDE ``n<>0 ==> m-(n-1)-1=m-n:num``,theWord_def]
  \\ rev_full_simp_tac(srw_ss())
         [decode_length_def,LET_THM] \\ rpt var_eq_tac
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs [] \\ tac
  \\ qabbrev_tac `s5 = s with
        <|regs :=
            s.regs |+ (7,Word v) |+
            (7,Word (v ⋙ (dimindex (:'a) − conf.len_size))) |+
            (8,Word (r2a1 + bytes_in_word)) |>`
  \\ drule word_gen_gc_move_list_code_thm
  \\ disch_then (qspec_then `s5` mp_tac)
  \\ fs [AND_IMP_INTRO] \\ impl_tac
  THEN1 (unabbrev_all_tac \\ fs [FLOOKUP_UPDATE,get_var_def,theWord_def]
         \\ fs [get_var_def,FLOOKUP_DEF])
  \\ strip_tac \\ fs [GSYM CONJ_ASSOC]
  \\ pop_assum mp_tac
  \\ qpat_abbrev_tac `s6 = s5 with <|regs := _ ; store := _ ; memory := _ |>`
  \\ qabbrev_tac `s7 = s6 with regs := s6.regs |+ (0,Word r1a1)`
  \\ `s.mdomain = s7.mdomain /\ m' = s7.memory` by (unabbrev_all_tac \\ fs [])
  \\ fs [] (* \\ qpat_x_assum `_ = _` kall_tac *)
  \\ first_x_assum drule \\ impl_tac
  THEN1 (unabbrev_all_tac \\ fs [FUPDATE_LIST,FLOOKUP_UPDATE])
  \\ rpt strip_tac \\ qexists_tac `ck + ck' + 1`
  \\ drule (evaluate_add_clock |> GEN_ALL)
  \\ disch_then (qspec_then `ck'+1` mp_tac) \\ fs []
  \\ qunabbrev_tac `s5` \\ fs [] \\ strip_tac
  \\ qunabbrev_tac `s6`
  \\ qunabbrev_tac `s7`
  \\ fs [theWord_def,FLOOKUP_UPDATE,FUPDATE_LIST]
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
         FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less]
  \\ qexists_tac `t0'` \\ qexists_tac `t1'`
  \\ rw [] \\ eq_tac \\ rw[] \\ fs []);

val word_gen_gc_move_loop_code_thm = Q.prove(
  `!k pax i pa ib pb pbx old m dm i1 pa1 ib1 pb1 m1 tt (s:('a,'c,'b)stackSem$state).
      word_gen_gc_move_loop conf k (pax,i,pa,ib,pb,pbx,old,m,dm) =
          (i1,pa1,ib1,pb1,m1,T) /\
      shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ conf.len_size <> 0 /\
      conf.len_size + 2 < dimindex (:'a) /\
      (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
      FLOOKUP s.store CurrHeap = SOME (Word old) /\ s.use_store /\
      s.memory = m /\ s.mdomain = dm /\
      (tt = 0w <=> pbx = pb /\ pax = pa) /\
      Temp 0w IN FDOM s.store /\
      Temp 1w IN FDOM s.store /\
      Temp 5w IN FDOM s.store /\
      Temp 6w IN FDOM s.store /\
      FLOOKUP s.store (Temp 2w) = SOME (Word pb) /\
      FLOOKUP s.store (Temp 3w) = SOME (Word ib) /\
      FLOOKUP s.store (Temp 4w) = SOME (Word pbx) /\
      0 IN FDOM s.regs /\
      get_var 1 s = SOME (Word pbx) /\
      get_var 2 s = SOME (Word pb) /\
      get_var 3 s = SOME (Word pa) /\
      get_var 4 s = SOME (Word (i:'a word)) /\
      get_var 7 s = SOME (Word tt) /\
      get_var 8 s = SOME (Word pax) /\
      5 IN FDOM s.regs /\
      6 IN FDOM s.regs /\ c1 ==>
      ?ck r0 r1 r2 r5 r6 r7 r8 t0 t1 t4 t5 t6.
        evaluate (word_gen_gc_move_loop_code conf,s with clock := s.clock + ck) =
          (NONE,s with <| memory := m1;
                          store :=
                            s.store |++
                            [(Temp 0w,t0); (Temp 1w,t1); (Temp 2w,Word pb1);
                             (Temp 3w,Word ib1);
                             (Temp 4w,t4); (Temp 5w, t5); (Temp 6w, t6)];
                          regs := s.regs |++ [(0,r0);
                                              (1,r1);
                                              (2,r2);
                                              (3,Word pa1);
                                              (4,Word i1);
                                              (5,r5);
                                              (6,r6);
                                              (7,r7);
                                              (8,r8)] |>)`,
  strip_tac \\ completeInduct_on `k` \\ rpt strip_tac
  \\ qpat_x_assum `word_gen_gc_move_loop _ _ _ = _` mp_tac
  \\ once_rewrite_tac [word_gen_gc_move_loop_def]
  \\ Cases_on `pbx = pb /\ pax = pa`
  THEN1
   (fs [] \\ strip_tac \\ rveq
    \\ fs [word_gen_gc_move_loop_code_def,get_var_def] \\ tac
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less]
    \\ qexists_tac `s.store ' (Temp 0w)`
    \\ qexists_tac `s.store ' (Temp 1w)`
    \\ qexists_tac `s.store ' (Temp 4w)`
    \\ qexists_tac `s.store ' (Temp 5w)`
    \\ qexists_tac `s.store ' (Temp 6w)`
    \\ rw [] \\ eq_tac \\ rw[] \\ fs [])
  \\ Cases_on `pbx = pb` \\ fs [] \\ rveq
  \\ rpt (pairarg_tac \\ fs []) \\ strip_tac \\ rveq \\ fs []
  \\ Cases_on `k = 0` \\ fs [] \\ rveq \\ fs [PULL_FORALL]
  THEN1
   (drule word_gen_gc_move_data_code_thm
    \\ disch_then (qspecl_then [`T`,`s`] mp_tac)
    \\ fs [AND_IMP_INTRO]
    \\ impl_tac THEN1 fs [FLOOKUP_DEF,get_var_def]
    \\ strip_tac
    \\ `k - 1 < k` by fs []
    \\ first_x_assum drule
    \\ qmatch_asmsub_abbrev_tac `(NONE,s2)`
    \\ qabbrev_tac `s3 = s2 with <| regs := s2.regs |++
             [(5,Word pb');(7,Word pb);(1,Word pb);(2,Word pb');(7,Word (pb-pb'))] |>`
    \\ `s.mdomain = s3.mdomain /\ m' = s3.memory /\ s2.use_store` by
          (unabbrev_all_tac \\ fs [] \\ NO_TAC)
    \\ fs [] \\ disch_then drule
    \\ disch_then (qspec_then `pb - pb'` mp_tac)
    \\ impl_tac
    THEN1
     (unabbrev_all_tac \\ fs [] \\ tac
      \\ once_rewrite_tac [GSYM wordsTheory.WORD_EQ_SUB_ZERO] \\ fs [])
    \\ strip_tac
    \\ pop_assum mp_tac
    \\ drule (evaluate_add_clock |> GEN_ALL)
    \\ disch_then (qspec_then `ck'+1` strip_assume_tac)
    \\ fs [] \\ strip_tac
    \\ drule (evaluate_add_clock |> GEN_ALL)
    \\ disch_then (qspec_then `1` strip_assume_tac)
    \\ fs [] \\ qexists_tac `ck+ck'+1` \\ fs []
    \\ simp [Once word_gen_gc_move_loop_code_def,get_var_def]
    \\ tac1 \\ fs [get_var_def]
    \\ full_simp_tac std_ss [GSYM word_gen_gc_move_loop_code_def]
    \\ fs [labSemTheory.word_cmp_def]
    \\ ntac 18 tac1
    \\ qunabbrev_tac `s2` \\ fs [] \\ tac1
    \\ qunabbrev_tac `s3`
    \\ fs [STOP_def,FUPDATE_LIST]
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less]
    \\ qexists_tac `t0'`
    \\ qexists_tac `t1'`
    \\ qexists_tac `t4`
    \\ qexists_tac `t5`
    \\ qexists_tac `t6`
    \\ rw [] \\ eq_tac \\ rw[] \\ fs [])
  \\ qabbrev_tac `s1 = s with <| regs := s.regs |+ (0,Word pbx) |+ (8,Word pb);
           store := s.store |+ (Temp 6w, Word pax) |+ (Temp 5w, Word pb) |>`
  \\ `s.mdomain = s1.mdomain /\ s.memory = s1.memory` by
        (unabbrev_all_tac \\ fs [] \\ NO_TAC) \\ fs []
  \\ drule word_gen_gc_move_refs_code_thm
  \\ disch_then (qspecl_then [`T`,`s1`] mp_tac)
  \\ fs [AND_IMP_INTRO]
  \\ impl_tac THEN1
   (rpt strip_tac \\ unabbrev_all_tac \\ tac\\ fs [get_var_def,FLOOKUP_DEF])
  \\ strip_tac \\ fs [FUPDATE_LIST]
  \\ qmatch_asmsub_abbrev_tac `(NONE,s2)`
  (*
  (* for debugging *)
  qexists_tac `ck`
  \\ simp [Once word_gen_gc_move_loop_code_def,get_var_def]
  \\ tac1 \\ rewrite_tac [GSYM word_gen_gc_move_loop_code_def]
  \\ tac1 \\ fs [get_var_def] \\ tac1
  \\ qunabbrev_tac `s1` \\ fs []
  \\ qunabbrev_tac `s2` \\ fs [] \\ tac1
  \\ ntac 20 tac1 *)
  \\ qabbrev_tac `s4 = s2 with <| regs :=
        s2.regs |+
         (7,Word pbx') |+
         (1,Word pb) |+
         (2,Word pb') |+
         (3,Word pa') |+
         (4,Word i') |+
         (7,Word (-1w * pb' + pbx')) |+
         (8,Word pax) |+
         (5,Word (-1w * pa' + pax)) |+
         (7,Word (-1w * pa' + pax ‖ -1w * pb' + pb)) ;
       store := s2.store |+ (Temp 4w,Word pb) |>`
  \\ `s1.mdomain = s4.mdomain /\ m' = s4.memory` by
        (unabbrev_all_tac \\ fs [] \\ NO_TAC) \\ fs []
  \\ `k - 1 < k` by fs [] \\ first_x_assum drule
  \\ disch_then drule
  \\ disch_then (qspec_then `(pb - pb') || (pax - pa')` mp_tac)
  \\ impl_tac THEN1
   (rpt strip_tac \\ TRY (unabbrev_all_tac \\ tac \\ fs [word_or_eq_0,get_var_def]
    \\ once_rewrite_tac [GSYM wordsTheory.WORD_EQ_SUB_ZERO] \\ fs [] \\ NO_TAC))
  \\ strip_tac \\ pop_assum mp_tac
  \\ drule (evaluate_add_clock |> GEN_ALL)
  \\ disch_then (qspec_then `ck'+1` strip_assume_tac) \\ fs []
  \\ rpt strip_tac
  \\ drule (evaluate_add_clock |> GEN_ALL)
  \\ disch_then (qspec_then `0` strip_assume_tac) \\ fs []
  \\ qexists_tac `ck + ck'+1`
  \\ simp [Once word_gen_gc_move_loop_code_def,get_var_def]
  \\ tac1 \\ fs [get_var_def] \\ ntac 12 tac1
  \\ qunabbrev_tac `s1` \\ fs [set_store_def]
  \\ unabbrev_all_tac \\ tac \\ fs [set_store_def] \\ tac
  \\ fs [STOP_def,word_gen_gc_move_loop_code_def,list_Seq_def]
  \\ fs [FUPDATE_LIST]
  \\ qmatch_goalsub_abbrev_tac `(While _ _ _ _,s7)`
  \\ qmatch_asmsub_abbrev_tac `(While _ _ _ _,s8)`
  \\ `s8 = s7` by
   (unabbrev_all_tac
    \\ fs [state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10]
    \\ full_simp_tac(srw_ss())[nine_less]
    \\ rpt strip_tac
    \\ TRY (rw [] \\ eq_tac \\ rw [] \\ fs [] \\ NO_TAC))
  \\ fs [] \\ fs [state_component_equality]
  \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
         FUN_EQ_THM,FAPPLY_FUPDATE_THM]
  \\ once_rewrite_tac [split_num_forall_to_10]
  \\ full_simp_tac(srw_ss())[nine_less]
  \\ qexists_tac `t0'`
  \\ qexists_tac `t1'`
  \\ qexists_tac `t4`
  \\ qexists_tac `t5`
  \\ qexists_tac `t6`
  \\ fs [] \\ rw [] \\ eq_tac \\ rw [] \\ fs []);

val word_sub_0_eq = prove(
  ``((-1w * w + v = 0w) <=> w = v) /\
    ((v + -1w * w = 0w) <=> w = v)``,
  once_rewrite_tac [GSYM wordsTheory.WORD_EQ_NEG]
  \\ once_rewrite_tac [GSYM wordsTheory.WORD_EQ_SUB_ZERO] \\ fs []);

Theorem good_dimindex_byte_aligned_eq:
   good_dimindex (:'a) ==>
    (byte_aligned (w:'a word) <=>
     ((w && (if dimindex (:'a) = 32 then 3w else 7w)) = 0w))
Proof
  rw [labPropsTheory.good_dimindex_def]
  \\ fs [alignmentTheory.byte_aligned_def,alignmentTheory.aligned_bitwise_and]
QED

val evaluate_SetNewTrigger = prove(
  ``evaluate (SetNewTrigger endh_reg ib_reg gen_sizes,s5) = (res,new_s) ==>
    !ib endh w.
      good_dimindex (:'a) /\ s5.use_store /\
      ALL_DISTINCT [1; 4; 7; ib_reg; endh_reg] /\
      FLOOKUP s5.regs ib_reg = SOME (Word ib) /\
      FLOOKUP s5.regs endh_reg = SOME (Word endh) /\
      FLOOKUP s5.store AllocSize = SOME (Word (w:'a word)) ==>
      ?r7 r1 r4.
        res = NONE /\
        new_s = s5 with <| regs := s5.regs |+ (1,r1) |+ (7,r7) |+ (4,r4);
                           store := s5.store |+ (TriggerGC,
                             Word ((ib + new_trig (endh - ib) w gen_sizes))) |>``,
  rw [] \\ qpat_x_assum `evaluate _ = _` mp_tac
  \\ rw [new_trig_def]
  \\ pop_assum mp_tac
  \\ fs [SetNewTrigger_def,list_Seq_def]
  THEN1
   (tac \\ fs [FLOOKUP_DEF,FAPPLY_FUPDATE_THM,WORD_LO,GSYM NOT_LESS,
               set_store_def,MIN_DEF]
    \\ rw [] \\ fs [state_component_equality]
    \\ fs [fmap_EXT,EXTENSION]
    \\ fs [GSYM PULL_EXISTS]
    \\ fs [FAPPLY_FUPDATE_THM] \\ metis_tac [])
  \\ tac \\ fs [FLOOKUP_DEF,FAPPLY_FUPDATE_THM,WORD_LO,GSYM NOT_LESS,
                set_store_def,MIN_DEF]
  THEN1
   (strip_tac \\ rveq \\ fs []
    \\ rw [] \\ fs [state_component_equality] \\ metis_tac [])
  \\ rfs [good_dimindex_byte_aligned_eq]
  \\ tac \\ fs [FLOOKUP_DEF,FAPPLY_FUPDATE_THM,WORD_LO,GSYM NOT_LESS,
                set_store_def,MIN_DEF]
  \\ rw [] \\ fs [state_component_equality]
  \\ fs [fmap_EXT,EXTENSION]
  \\ fs [GSYM PULL_EXISTS]
  \\ fs [FAPPLY_FUPDATE_THM] \\ metis_tac []);

Theorem alloc_correct_lemma_Generational:
   alloc w (s:('a,'c,'b)stackSem$state) = (r,t) /\ r <> SOME Error /\
    s.gc_fun = word_gc_fun conf /\ conf.gc_kind = ^kind /\
    LENGTH s.bitmaps < dimword (:'a) - 1 /\
    LENGTH s.stack * (dimindex (:'a) DIV 8) < dimword (:'a) /\
    FLOOKUP l 0 = SOME ret /\
    FLOOKUP l 1 = SOME (Word w) ==>
    ?ck l2.
      evaluate
        (word_gc_code conf,
         s with
           <| use_store := T; use_stack := T; use_alloc := F;
              clock := s.clock + ck; regs := l; gc_fun := anything;
              code := fromAList (compile c (toAList s.code))|>) =
        (r,
         t with
           <| use_store := T; use_stack := T; use_alloc := F;
              code := fromAList (compile c (toAList s.code));
              regs := l2; gc_fun := anything |>) /\
       (r <> NONE ==> r = SOME (Halt (Word 1w))) /\
       t.regs SUBMAP l2 /\
       (r = NONE ==> FLOOKUP l2 0 = SOME ret)
Proof
  qspec_tac (`gen_sizes`,`gen_sizes`)
  \\ Cases_on `?gen_sizes. conf.gc_kind = Generational gen_sizes` \\ fs []
  \\ Cases_on `s.gc_fun = word_gc_fun conf` \\ fs [] \\ fs [alloc_def]
  \\ `(set_store AllocSize (Word w) s).gc_fun = word_gc_fun conf` by
        (fs [set_store_def] \\ NO_TAC)
  \\ drule gc_thm
  \\ fs [] \\ disch_then kall_tac
  \\ fs [set_store_def] \\ IF_CASES_TAC THEN1 (fs [] \\ rw [] \\ fs [])
  \\ fs [FAPPLY_FUPDATE_THM]
  \\ IF_CASES_TAC THEN1 (fs [] \\ rw [] \\ fs [])
  \\ IF_CASES_TAC THEN1
   (rpt (pairarg_tac \\ fs [])
    \\ reverse IF_CASES_TAC THEN1 rw [] \\ fs []
    \\ fs [FLOOKUP_UPDATE,FUPDATE_LIST,has_space_def]
    \\ rpt var_eq_tac \\ strip_tac \\ fs [NOT_LESS]
    \\ `{Globals; CurrHeap; OtherHeap; HeapLength;
         TriggerGC; EndOfHeap} SUBSET FDOM s.store /\
        isWord (s.store ' OtherHeap) /\
        isWord (s.store ' CurrHeap) /\
        isWord (s.store ' HeapLength) /\
        isWord (s.store ' TriggerGC) /\
        isWord (s.store ' EndOfHeap) /\
        good_dimindex (:'a) /\
        conf.len_size + 2 < dimindex (:'a) /\
        shift_length conf < dimindex (:'a) /\
        conf.len_size <> 0` by
          (fs [word_gc_fun_assum_def,set_store_def,FAPPLY_FUPDATE_THM] \\ NO_TAC)
    \\ `word_shift (:'a) < dimindex (:'a) /\ 2 < dimindex (:'a) /\
        !w:'a word. w ≪ word_shift (:'a) = w * bytes_in_word` by
     (fs [word_shift_def,bytes_in_word_def,labPropsTheory.good_dimindex_def]
      \\ fs [WORD_MUL_LSL] \\ NO_TAC)
    \\ fs [isWord_thm] \\ fs [theWord_def]
    \\ rename1 `s.store ' OtherHeap = Word other`
    \\ rename1 `s.store ' CurrHeap = Word curr`
    \\ rename1 `s.store ' HeapLength = Word len`
    \\ rename1 `s.store ' TriggerGC = Word trig`
    \\ rename1 `s.store ' EndOfHeap = Word endh`
    \\ fs [word_gc_code_def]
    \\ `FLOOKUP s.store OtherHeap = SOME (Word other) /\
        FLOOKUP s.store CurrHeap = SOME (Word curr) /\
        FLOOKUP s.store HeapLength = SOME (Word len) /\
        FLOOKUP s.store TriggerGC = SOME (Word trig) /\
        FLOOKUP s.store EndOfHeap = SOME (Word endh)` by fs [FLOOKUP_DEF]
    \\ `!ck xs ys. evaluate
          (word_gc_partial_or_full gen_sizes xs ys,
           s with
           <|regs := l; gc_fun := anything; use_stack := T; use_store := T;
             use_alloc := F; clock := ck + s.clock;
             code := fromAList (compile c (toAList s.code))|>) =
             evaluate
          (list_Seq xs,
           s with
           <|regs := l |++ [(8,Word trig);(7,Word (endh - trig))];
             gc_fun := anything; use_stack := T; use_store := T;
             use_alloc := F; clock := ck + s.clock;
             code := fromAList (compile c (toAList s.code))|>)` by
     (fs [word_gc_partial_or_full_def] \\ Cases_on `gen_sizes` \\ fs []
      \\ fs [word_gen_gc_can_do_partial_def] \\ tac
      \\ fs [WORD_NOT_LOWER,FAPPLY_FUPDATE_THM,theWord_def] \\ NO_TAC)
    \\ asm_rewrite_tac [] \\ pop_assum kall_tac
    \\ `?gs. FLOOKUP s.store GenStart = SOME (Word gs)` by
      (fs [FLOOKUP_DEF,word_gc_fun_assum_def,set_store_def,
           FAPPLY_FUPDATE_THM,isWord_thm] \\ NO_TAC)
    \\ tac \\ fs [set_store_def] \\ tac
    \\ simp [FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
    \\ fs []
    \\ drule word_gen_gc_partial_move_ref_list_ok
    \\ strip_tac \\ rveq \\ fs []
    \\ abbrev_under_exists ``s3:('a,'c,'b)stackSem$state``
     (qexists_tac `0` \\ fs []
      \\ qpat_abbrev_tac `(s3:('a,'c,'b)stackSem$state) = _`)
    \\ drule (GEN_ALL word_gen_gc_partial_move_code_thm)
    \\ disch_then (qspec_then `s3` mp_tac)
    \\ impl_tac THEN1
     (unabbrev_all_tac \\ fs [] \\ tac
      \\ fs [FAPPLY_FUPDATE_THM,FLOOKUP_DEF,theWord_def])
    \\ strip_tac \\ fs []
    \\ `s.stack_space < LENGTH s.stack` by
     (CCONTR_TAC \\ fs [NOT_LESS]
      \\ imp_res_tac DROP_LENGTH_TOO_LONG
      \\ fs [word_gen_gc_partial_move_roots_bitmaps_def,enc_stack_def] \\ NO_TAC)
    \\ fs [] \\ tac
    \\ fs [FAPPLY_FUPDATE_THM,FLOOKUP_DEF,theWord_def]
    \\ abbrev_under_exists ``s4:('a,'c,'b)stackSem$state``
     (qexists_tac `ck` \\ fs []
      \\ unabbrev_all_tac \\ fs [] \\ tac
      \\ fs [FAPPLY_FUPDATE_THM,FLOOKUP_DEF] \\ tac
      \\ qpat_abbrev_tac `(s4:('a,'c,'b)stackSem$state) = _`)
    \\ qpat_x_assum `word_gen_gc_partial_move_roots_bitmaps _ _ = _` assume_tac
    \\ `s.stack_space <= LENGTH s.stack` by fs []
    \\ drule LESS_EQ_LENGTH
    \\ strip_tac \\ fs []
    \\ `DROP s.stack_space (ys1 ++ ys2) = ys2` by
         metis_tac [DROP_LENGTH_APPEND] \\ fs []
    \\ drule (GEN_ALL word_gen_gc_partial_move_roots_bitmaps_code_thm
             |> REWRITE_RULE [GSYM AND_IMP_INTRO])
    \\ fs [AND_IMP_INTRO]
    \\ disch_then (qspecl_then [`ys1`,`s4`,`[]`] mp_tac)
    \\ impl_tac THEN1
      (fs [] \\ unabbrev_all_tac \\ fs [get_var_def,FLOOKUP_UPDATE]
       \\ fs [FLOOKUP_DEF] \\ fs [EL_APPEND_EQN])
    \\ strip_tac \\ fs [FAPPLY_FUPDATE_THM]
    \\ pop_assum mp_tac
    \\ drule (GEN_ALL evaluate_add_clock)
    \\ disch_then (qspec_then `ck'` mp_tac)
    \\ fs [] \\ rpt strip_tac
    \\ abbrev_under_exists ``s5:('a,'c,'b)stackSem$state``
     (qexists_tac `ck+ck'` \\ fs []
      \\ unabbrev_all_tac \\ fs [] \\ tac
      \\ fs [FAPPLY_FUPDATE_THM,FLOOKUP_DEF] \\ tac
      \\ qpat_abbrev_tac `(s5:('a,'c,'b)stackSem$state) = _`)
    \\ drule (GEN_ALL word_gen_gc_partial_move_ref_list_code_thm
             |> REWRITE_RULE [GSYM AND_IMP_INTRO])
    \\ fs [AND_IMP_INTRO]
    \\ disch_then (qspecl_then [`s5`] mp_tac)
    \\ impl_tac THEN1
      (fs [] \\ unabbrev_all_tac \\ fs [get_var_def,FLOOKUP_UPDATE]
       \\ fs [FLOOKUP_DEF,FDOM_FUPDATE,FUPDATE_LIST,FAPPLY_FUPDATE_THM]
       \\ fs [word_or_eq_0])
    \\ strip_tac \\ pop_assum mp_tac
    \\ drule (GEN_ALL evaluate_add_clock)
    \\ disch_then (qspec_then `ck''` mp_tac)
    \\ qpat_x_assum `evaluate _ = _` kall_tac
    \\ drule (GEN_ALL evaluate_add_clock)
    \\ disch_then (qspec_then `ck''` mp_tac)
    \\ rpt strip_tac \\ fs []
    \\ abbrev_under_exists ``s6:('a,'c,'b)stackSem$state``
     (qexists_tac `ck+ck'+ck''` \\ fs []
      \\ unabbrev_all_tac \\ fs [] \\ tac
      \\ fs [FAPPLY_FUPDATE_THM,FLOOKUP_DEF] \\ tac
      \\ qpat_abbrev_tac `(s6:('a,'c,'b)stackSem$state) = _`)
    \\ drule (GEN_ALL word_gen_gc_partial_move_data_code_thm)
    \\ disch_then (qspecl_then [`T`,`s6`] mp_tac)
    \\ fs [AND_IMP_INTRO]
    \\ impl_tac THEN1
     (unabbrev_all_tac \\ fs [] \\ tac
      \\ fs [FAPPLY_FUPDATE_THM,FLOOKUP_DEF,theWord_def])
    \\ strip_tac \\ fs []
    \\ qmatch_asmsub_rename_tac `s6 with clock := ck3 + s6.clock`
    \\ pop_assum mp_tac
    \\ drule (GEN_ALL evaluate_add_clock)
    \\ disch_then (qspec_then `ck3` mp_tac)
    \\ qpat_x_assum `evaluate _ = _` kall_tac
    \\ drule (GEN_ALL evaluate_add_clock)
    \\ disch_then (qspec_then `ck3` mp_tac)
    \\ qpat_x_assum `evaluate _ = _` kall_tac
    \\ drule (GEN_ALL evaluate_add_clock)
    \\ disch_then (qspec_then `ck3` mp_tac)
    \\ fs []
    \\ qmatch_goalsub_rename_tac `ck0 + (ck1 + (ck2 + (ck3 + s3.clock)))`
    \\ rpt strip_tac
    \\ abbrev_under_exists ``s7:('a,'c,'b)stackSem$state``
     (qexists_tac `ck0+ck1+ck2+ck3` \\ fs []
      \\ unabbrev_all_tac \\ fs [] \\ tac
      \\ fs [FAPPLY_FUPDATE_THM,FLOOKUP_DEF,FUPDATE_LIST]
      \\ tac \\ rfs [] \\ tac
      \\ fs [FAPPLY_FUPDATE_THM,FLOOKUP_DEF,FUPDATE_LIST]
      \\ qpat_abbrev_tac `(s7:('a,'c,'b)stackSem$state) = _`)
    \\ drule (GEN_ALL memcpy_code_thm)
    \\ disch_then (qspecl_then [`s7`] mp_tac)
    \\ fs [AND_IMP_INTRO]
    \\ impl_tac THEN1
     (unabbrev_all_tac \\ fs [] \\ tac
      \\ fs [FAPPLY_FUPDATE_THM,FLOOKUP_DEF,theWord_def])
    \\ strip_tac \\ fs []
    \\ qmatch_asmsub_rename_tac `s7 with clock := s7.clock + ck4`
    \\ pop_assum mp_tac
    \\ drule (GEN_ALL evaluate_add_clock)
    \\ disch_then (qspec_then `ck4` mp_tac)
    \\ qpat_x_assum `evaluate _ = _` kall_tac
    \\ drule (GEN_ALL evaluate_add_clock)
    \\ disch_then (qspec_then `ck4` mp_tac)
    \\ qpat_x_assum `evaluate _ = _` kall_tac
    \\ drule (GEN_ALL evaluate_add_clock)
    \\ disch_then (qspec_then `ck4` mp_tac)
    \\ qpat_x_assum `evaluate _ = _` kall_tac
    \\ drule (GEN_ALL evaluate_add_clock)
    \\ disch_then (qspec_then `ck4` mp_tac)
    \\ rpt strip_tac
    \\ qexists_tac `ck0+ck1+ck2+ck3+ck4` \\ fs []
    \\ unabbrev_all_tac \\ fs [] \\ tac
    \\ fs [FAPPLY_FUPDATE_THM,FLOOKUP_DEF,FUPDATE_LIST]
    \\ tac \\ rfs [] \\ tac
    \\ fs [FAPPLY_FUPDATE_THM,FLOOKUP_DEF,FUPDATE_LIST]
    \\ qmatch_goalsub_abbrev_tac `evaluate (SetNewTrigger _ _ _,s5)`
    \\ Cases_on `evaluate (SetNewTrigger 8 3 gen_sizes,s5)`
    \\ drule (GEN_ALL evaluate_SetNewTrigger)
    \\ qunabbrev_tac `s5` \\ fs [FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
    \\ strip_tac \\ rveq
    \\ fs [FAPPLY_FUPDATE_THM,FLOOKUP_DEF,FUPDATE_LIST]
    \\ tac \\ rfs [] \\ tac
    \\ fs [FAPPLY_FUPDATE_THM,FLOOKUP_DEF,FUPDATE_LIST]
    \\ fs [labSemTheory.word_cmp_def,set_store_def]
    \\ rpt (qpat_x_assum `evaluate _ = _` kall_tac)
    \\ `w2n w ≤ w2n (-1w * b1 + endh)` by rfs [WORD_LS] \\ fs []
    \\ `¬(w2n (new_trig (-1w * b1 + endh) w gen_sizes) < w2n w)` by
          rfs [WORD_LS] \\ fs []
    \\ fs [WORD_LO,GSYM NOT_LESS,set_store_def] \\ tac
    \\ fs [FAPPLY_FUPDATE_THM,FUPDATE_LIST,FLOOKUP_DEF] \\ tac
    \\ fs [empty_env_def,state_component_equality]
    \\ rpt var_eq_tac \\ fs []
    \\ fs [FAPPLY_FUPDATE_THM,FUPDATE_LIST]
    \\ qpat_x_assum `_ = t.store` (fn th => fs [GSYM th])
    \\ `TAKE t.stack_space (ys1 ++ ys2) = ys1` by metis_tac [TAKE_LENGTH_APPEND]
    \\ fs [fmap_EXT,EXTENSION]
    \\ rw [] \\ fs [FAPPLY_FUPDATE_THM]
    \\ fs [SUBMAP_DEF] \\ rw [] \\ fs [] \\ eq_tac \\ strip_tac \\ fs [])
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ reverse IF_CASES_TAC THEN1 rw [] \\ fs []
  \\ fs [FLOOKUP_UPDATE,FUPDATE_LIST,has_space_def]
  \\ rpt var_eq_tac \\ strip_tac \\ fs [NOT_LESS]
  \\ `{Globals; CurrHeap; OtherHeap; HeapLength;
       TriggerGC; EndOfHeap} SUBSET FDOM s.store /\
      isWord (s.store ' OtherHeap) /\
      isWord (s.store ' CurrHeap) /\
      isWord (s.store ' HeapLength) /\
      isWord (s.store ' TriggerGC) /\
      isWord (s.store ' EndOfHeap) /\
      good_dimindex (:'a) /\
      conf.len_size + 2 < dimindex (:'a) /\
      shift_length conf < dimindex (:'a) /\
      conf.len_size <> 0` by
        (fs [word_gc_fun_assum_def,set_store_def,FAPPLY_FUPDATE_THM] \\ NO_TAC)
  \\ `word_shift (:'a) < dimindex (:'a) /\ 2 < dimindex (:'a) /\
      !w:'a word. w ≪ word_shift (:'a) = w * bytes_in_word` by
   (fs [word_shift_def,bytes_in_word_def,labPropsTheory.good_dimindex_def]
    \\ fs [WORD_MUL_LSL] \\ NO_TAC)
  \\ fs [isWord_thm] \\ fs [theWord_def]
  \\ rename1 `s.store ' OtherHeap = Word other`
  \\ rename1 `s.store ' CurrHeap = Word curr`
  \\ rename1 `s.store ' HeapLength = Word len`
  \\ rename1 `s.store ' TriggerGC = Word trig`
  \\ rename1 `s.store ' EndOfHeap = Word endh`
  \\ fs [word_gc_code_def]
  \\ `FLOOKUP s.store OtherHeap = SOME (Word other) /\
      FLOOKUP s.store CurrHeap = SOME (Word curr) /\
      FLOOKUP s.store HeapLength = SOME (Word len) /\
      FLOOKUP s.store TriggerGC = SOME (Word trig) /\
      FLOOKUP s.store EndOfHeap = SOME (Word endh)` by fs [FLOOKUP_DEF]
  \\ `!ck xs ys. evaluate
        (word_gc_partial_or_full gen_sizes xs ys,
         s with
         <|regs := l; gc_fun := anything; use_stack := T; use_store := T;
           use_alloc := F; clock := ck + s.clock;
           code := fromAList (compile c (toAList s.code))|>) =
           evaluate
        (list_Seq ys,
         s with
         <|regs := l |++ [(8,Word trig);(7,Word (endh - trig))];
           gc_fun := anything; use_stack := T; use_store := T;
           use_alloc := F; clock := ck + s.clock;
           code := fromAList (compile c (toAList s.code))|>)` by
   (fs [word_gc_partial_or_full_def] \\ Cases_on `gen_sizes` \\ fs []
    \\ tac THEN1 (Cases_on `ys` \\ tac)
    \\ fs [word_gen_gc_can_do_partial_def]
    \\ fs [WORD_NOT_LOWER,FAPPLY_FUPDATE_THM,theWord_def] \\ NO_TAC)
  \\ asm_rewrite_tac [] \\ pop_assum kall_tac
  \\ ntac 15 tac1
  \\ fs []
  \\ ntac 4 tac1
  \\ simp [FLOOKUP_DEF]
  \\ ntac 2 tac1
  \\ abbrev_under_exists ``s3:('a,'c,'b)stackSem$state``
   (qexists_tac `0` \\ fs []
    \\ qpat_abbrev_tac `(s3:('a,'c,'b)stackSem$state) = _`)
  \\ drule (GEN_ALL word_gen_gc_move_code_thm)
  \\ disch_then (qspec_then `s3` mp_tac)
  \\ impl_tac THEN1
   (unabbrev_all_tac \\ fs [] \\ tac
    \\ fs [FAPPLY_FUPDATE_THM,FLOOKUP_DEF])
  \\ strip_tac \\ fs []
  \\ `s.stack_space < LENGTH s.stack` by
   (CCONTR_TAC \\ fs [NOT_LESS]
    \\ imp_res_tac DROP_LENGTH_TOO_LONG
    \\ fs [word_gen_gc_move_roots_bitmaps_def,enc_stack_def] \\ NO_TAC)
  \\ ntac 3 tac1
  \\ abbrev_under_exists ``s4:('a,'c,'b)stackSem$state``
   (qexists_tac `ck` \\ fs []
    \\ unabbrev_all_tac \\ fs [] \\ tac
    \\ fs [FAPPLY_FUPDATE_THM,FLOOKUP_DEF] \\ tac
    \\ qpat_abbrev_tac `(s4:('a,'c,'b)stackSem$state) = _`)
  \\ qpat_x_assum `word_gen_gc_move_roots_bitmaps _ _ = _` assume_tac
  \\ drule LESS_EQ_LENGTH
  \\ strip_tac \\ fs []
  \\ `DROP s.stack_space (ys1 ++ ys2) = ys2` by
       metis_tac [DROP_LENGTH_APPEND] \\ fs []
  \\ drule (GEN_ALL word_gen_gc_move_roots_bitmaps_code_thm
           |> REWRITE_RULE [GSYM AND_IMP_INTRO])
  \\ fs [AND_IMP_INTRO]
  \\ disch_then (qspecl_then [`ys1`,`s4`,`[]`] mp_tac)
  \\ impl_tac THEN1
    (fs [] \\ unabbrev_all_tac \\ fs [get_var_def,FLOOKUP_UPDATE]
     \\ fs [FLOOKUP_DEF] \\ Cases_on `ys2` \\ fs []
     \\ metis_tac [EL_LENGTH_APPEND,NULL,HD])
  \\ strip_tac \\ fs [FAPPLY_FUPDATE_THM]
  \\ pop_assum mp_tac
  \\ drule (GEN_ALL evaluate_add_clock)
  \\ disch_then (qspec_then `ck'` mp_tac)
  \\ fs [] \\ rpt strip_tac
  \\ abbrev_under_exists ``s5:('a,'c,'b)stackSem$state``
   (qexists_tac `ck+ck'` \\ fs []
    \\ unabbrev_all_tac \\ fs [] \\ tac
    \\ fs [FAPPLY_FUPDATE_THM,FLOOKUP_DEF] \\ tac
    \\ qpat_abbrev_tac `(s5:('a,'c,'b)stackSem$state) = _`)
  \\ drule (GEN_ALL word_gen_gc_move_loop_code_thm
           |> REWRITE_RULE [GSYM AND_IMP_INTRO])
  \\ fs [AND_IMP_INTRO]
  \\ disch_then (qspecl_then [`(pb2 - (len+other)) || (pa2 - other)`,`s5`] mp_tac)
  \\ impl_tac THEN1
    (fs [] \\ unabbrev_all_tac \\ fs [get_var_def,FLOOKUP_UPDATE]
     \\ fs [FLOOKUP_DEF,FDOM_FUPDATE,FUPDATE_LIST,FAPPLY_FUPDATE_THM]
     \\ fs [word_or_eq_0]
     \\ rpt (pop_assum kall_tac) \\ fs [word_sub_0_eq])
  \\ strip_tac \\ pop_assum mp_tac
  \\ drule (GEN_ALL evaluate_add_clock)
  \\ disch_then (qspec_then `ck''` mp_tac)
  \\ qpat_x_assum `evaluate _ = _` kall_tac
  \\ drule (GEN_ALL evaluate_add_clock)
  \\ disch_then (qspec_then `ck''` mp_tac)
  \\ rpt strip_tac \\ fs []
  \\ qexists_tac `ck+ck'+ck''` \\ fs []
  \\ unabbrev_all_tac \\ fs [] \\ tac
  \\ fs [FAPPLY_FUPDATE_THM,FUPDATE_LIST,FLOOKUP_DEF,set_store_def] \\ tac
  \\ qmatch_goalsub_abbrev_tac `evaluate (SetNewTrigger 2 3 _,s5)`
  \\ Cases_on `evaluate (SetNewTrigger 2 3 gen_sizes,s5)`
  \\ drule evaluate_SetNewTrigger
  \\ qunabbrev_tac `s5` \\ fs [FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
  \\ strip_tac \\ rveq
  \\ fs [FAPPLY_FUPDATE_THM,FUPDATE_LIST,FLOOKUP_DEF,set_store_def] \\ tac
  \\ fs [labSemTheory.word_cmp_def,set_store_def]
  \\ IF_CASES_TAC \\ fs [WORD_LO,GSYM NOT_LESS,set_store_def] \\ tac
  \\ fs [FAPPLY_FUPDATE_THM,FUPDATE_LIST,FLOOKUP_DEF] \\ tac
  \\ fs [empty_env_def,state_component_equality]
  \\ rpt var_eq_tac \\ fs []
  \\ fs [FAPPLY_FUPDATE_THM,FUPDATE_LIST]
  \\ rpt (qpat_x_assum `evaluate _ = _` kall_tac)
  \\ qpat_x_assum `_ = t.store` (fn th => fs [GSYM th])
  \\ `TAKE t.stack_space (ys1 ++ ys2) = ys1` by metis_tac [TAKE_LENGTH_APPEND]
  \\ fs [fmap_EXT,EXTENSION]
  \\ rw [] \\ fs [FAPPLY_FUPDATE_THM]
  \\ fs [SUBMAP_DEF] \\ rw [] \\ fs [] \\ eq_tac \\ strip_tac \\ fs []
QED

(* gc_kind = None *)

val filter_bitmap_map_bitmap_IMP = prove(
  ``!x ws q r x' q' q'' r''.
      filter_bitmap x ws = SOME (q,r) /\
      map_bitmap x (q ++ x') ws = SOME (q',q'',r'') ==>
      q'' = x' /\ r = r'' /\ ws = q' ++ r``,
  Induct \\ fs [filter_bitmap_def,map_bitmap_def]
  \\ Cases \\ Cases
  \\ fs [filter_bitmap_def,map_bitmap_def]
  \\ every_case_tac \\ fs [map_bitmap_def]
  \\ rw [] \\ every_case_tac \\ fs [] \\ rveq \\ fs []
  \\ res_tac \\ rveq \\ fs []);

val enc_dec_stack = prove(
  ``!bs ys2 x1 x2.
      enc_stack bs ys2 = SOME x1 /\
      dec_stack bs x1 ys2 = SOME x2 ==>
      (ys2 = x2)``,
  ho_match_mp_tac enc_stack_ind
  \\ fs [enc_stack_def] \\ rw []
  \\ rw [] \\ fs [dec_stack_def]
  \\ ntac 2 (pop_assum mp_tac)
  \\ ntac 5 (TOP_CASE_TAC \\ fs [])
  \\ strip_tac \\ rveq
  \\ rpt (TOP_CASE_TAC \\ fs [])
  \\ strip_tac \\ rveq \\ fs []
  \\ drule filter_bitmap_map_bitmap_IMP
  \\ fs [] \\ strip_tac \\ rveq \\ fs []
  \\ pop_assum drule \\ fs [] \\ rw []
  \\ res_tac \\ rveq \\ fs []);

Theorem alloc_correct_lemma_None:
   alloc w (s:('a,'c,'b)stackSem$state) = (r,t) /\ r <> SOME Error /\
    s.gc_fun = word_gc_fun conf /\ conf.gc_kind = None /\
    LENGTH s.bitmaps < dimword (:'a) - 1 /\
    LENGTH s.stack * (dimindex (:'a) DIV 8) < dimword (:'a) /\
    FLOOKUP l 0 = SOME ret /\
    FLOOKUP l 1 = SOME (Word w) ==>
    ?ck l2.
      evaluate
        (word_gc_code conf,
         s with
           <| use_store := T; use_stack := T; use_alloc := F;
              clock := s.clock + ck; regs := l; gc_fun := anything;
              code := fromAList (compile c (toAList s.code))|>) =
        (r,
         t with
           <| use_store := T; use_stack := T; use_alloc := F;
              code := fromAList (compile c (toAList s.code));
              regs := l2; gc_fun := anything |>) /\
       (r <> NONE ==> r = SOME (Halt (Word 1w))) /\
       t.regs SUBMAP l2 /\
       (r = NONE ==> FLOOKUP l2 0 = SOME ret)
Proof
  Cases_on `conf.gc_kind = None` \\ fs []
  \\ fs [word_gc_fun_def,word_gc_code_def] \\ rw []
  \\ qpat_x_assum `alloc w s = (r,t)` mp_tac
  \\ fs [alloc_def,gc_def,set_store_def]
  \\ IF_CASES_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ pop_assum mp_tac
  \\ TOP_CASE_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ rveq \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ strip_tac \\ rveq
  \\ fs [FAPPLY_FUPDATE_THM,FLOOKUP_UPDATE,FUPDATE_LIST,has_space_def]
  \\ IF_CASES_TAC \\ strip_tac \\ fs [] \\ rveq \\ fs []
  \\ fs [list_Seq_def,evaluate_def,word_gc_fun_assum_def,
       list_Seq_def,evaluate_def,inst_def,word_exp_def,get_var_def,
       wordLangTheory.word_op_def,mem_load_def,assign_def,set_var_def,
       FLOOKUP_UPDATE,mem_store_def,dec_clock_def,get_var_imm_def,
       asmTheory.word_cmp_def,FAPPLY_FUPDATE_THM,
       labSemTheory.word_cmp_def,GREATER_EQ,GSYM NOT_LESS,FUPDATE_LIST,
       wordLangTheory.word_sh_def,word_shift_not_0,FLOOKUP_UPDATE]
  \\ fs [labSemTheory.word_cmp_def,FAPPLY_FUPDATE_THM,FLOOKUP_DEF,set_store_def]
  \\ fs [state_component_equality,FAPPLY_FUPDATE_THM]
  \\ Cases_on `s.store ' CurrHeap` \\ fs [isWord_def,theWord_def]
  \\ Cases_on `s.store ' NextFree` \\ fs [isWord_def,theWord_def]
  \\ Cases_on `s.store ' TriggerGC` \\ fs [isWord_def,theWord_def]
  \\ fs [empty_env_def,finite_mapTheory.SUBMAP_FEMPTY]
  \\ fs [NOT_LESS]
  \\ drule LESS_EQ_LENGTH
  \\ strip_tac \\ fs []
  \\ pop_assum (assume_tac o GSYM) \\ fs []
  \\ fs [TAKE_LENGTH_APPEND,DROP_LENGTH_APPEND]
  \\ imp_res_tac enc_dec_stack \\ fs []
QED

(* --- *)

Theorem alloc_correct_lemma:
   alloc w (s:('a,'c,'b)stackSem$state) = (r,t) /\ r <> SOME Error /\
    s.gc_fun = word_gc_fun conf /\
    LENGTH s.bitmaps < dimword (:'a) - 1 /\
    LENGTH s.stack * (dimindex (:'a) DIV 8) < dimword (:'a) /\
    FLOOKUP l 0 = SOME ret /\
    FLOOKUP l 1 = SOME (Word w) ==>
    ?ck l2.
      evaluate
        (word_gc_code conf,
         s with
           <| use_store := T; use_stack := T; use_alloc := F;
              clock := s.clock + ck; regs := l; gc_fun := anything;
              code := fromAList (compile c (toAList s.code))|>) =
        (r,
         t with
           <| use_store := T; use_stack := T; use_alloc := F;
              code := fromAList (compile c (toAList s.code));
              regs := l2; gc_fun := anything |>) /\
       (r <> NONE ==> r = SOME (Halt (Word 1w))) /\
       t.regs SUBMAP l2 /\
       (r = NONE ==> FLOOKUP l2 0 = SOME ret)
Proof
  Cases_on `conf.gc_kind`
  THEN1 metis_tac [alloc_correct_lemma_None]
  THEN1 metis_tac [alloc_correct_lemma_Simple]
  THEN1 metis_tac [alloc_correct_lemma_Generational]
QED

val alloc_correct = Q.prove(
  `alloc w (s:('a,'c,'b)stackSem$state) = (r,t) /\ r <> SOME Error /\
    s.gc_fun = word_gc_fun c /\
    LENGTH s.bitmaps < dimword (:'a) - 1 /\
    LENGTH s.stack * (dimindex (:'a) DIV 8) < dimword (:'a) /\
    FLOOKUP l 1 = SOME (Word w) ==>
    ?ck l2.
       evaluate
          (Call (SOME (Skip,0,n',m)) (INL gc_stub_location) NONE,
           s with
           <| use_store := T; use_stack := T; use_alloc := F;
              use_alloc := F; clock := s.clock + ck; regs := l; gc_fun := anything;
              code := fromAList (compile c (toAList s.code))|>) =
         (r,
          t with
           <| use_store := T; use_stack := T; use_alloc := F;
              use_alloc := F; code := fromAList (compile c (toAList s.code));
              regs := l2; gc_fun := anything|>) /\ t.regs SUBMAP l2`,
  `find_code (INL gc_stub_location) (l \\ 0) (fromAList (compile c (toAList s.code))) =
      SOME (Seq (word_gc_code c) (Return 0 0))` by
     simp[find_code_def,lookup_fromAList,compile_def,ALOOKUP_APPEND,stubs_def]
  \\ tac \\ fs [] \\ strip_tac
  \\ mp_tac (Q.GENL [`conf`,`l`,`ret`] alloc_correct_lemma) \\ fs []
  \\ disch_then (qspecl_then [`c`,`l |+ (0,Loc n' m)`] mp_tac)
  \\ fs [FLOOKUP_UPDATE] \\ strip_tac
  \\ qexists_tac `ck+1` \\ fs []
  \\ Cases_on `r` \\ fs [state_component_equality]);

val find_code_IMP_lookup = Q.prove(
  `find_code dest regs (s:'a num_map) = SOME x ==>
    ?k. lookup k s = SOME x /\
        (find_code dest regs = ((lookup k):'a num_map -> 'a option))`,
  Cases_on `dest` \\ full_simp_tac(srw_ss())[find_code_def,FUN_EQ_THM]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ metis_tac []);

Theorem alloc_length_stack:
   alloc c s = (r,t) /\ s.gc_fun = word_gc_fun conf /\
   (!w. r <> SOME (Halt w)) ==>
   LENGTH t.stack = LENGTH s.stack
Proof
  fs [alloc_def,gc_def,set_store_def] \\ rw [] \\ fs []
  \\ every_case_tac \\ fs []
  \\ rw [] \\ drule word_gc_fun_LENGTH \\ rw [] \\ fs [NOT_LESS]
  \\ drule LESS_EQ_LENGTH \\ strip_tac \\ fs []
  \\ pop_assum (fn th => fs [GSYM th]) \\ fs [DROP_LENGTH_APPEND]
  \\ metis_tac [dec_stack_length]
QED

Theorem find_code_regs_SUBMAP:
   r1 ⊑ r2 ∧
   find_code dest r1 c = SOME x ⇒
   find_code dest r2 c = SOME x
Proof
  Cases_on`dest` \\ EVAL_TAC \\ rw[]
  \\ imp_res_tac FLOOKUP_SUBMAP
  \\ every_case_tac \\ fs[] \\ res_tac \\ fs[]
  \\ rw[]
QED

Theorem get_labels_comp:
   !n p e. get_labels e SUBSET get_labels (FST (comp n p e))
Proof
  recInduct comp_ind \\ rw []
  \\ Cases_on `p` \\ fs []
  \\ once_rewrite_tac [comp_def] \\ fs []
  \\ every_case_tac \\ fs []
  \\ TRY pairarg_tac \\ fs [get_labels_def,SUBSET_DEF]
  \\ TRY pairarg_tac \\ fs [get_labels_def,SUBSET_DEF]
  \\ rw [] \\ fs []
QED

Theorem loc_check_compile:
   loc_check s.code (l1,l2) /\
    (!k prog. lookup k s.code = SOME prog ==> k ≠ gc_stub_location) ==>
    loc_check (fromAList (compile c (toAList s.code))) (l1,l2)
Proof
  fs [loc_check_def,domain_lookup] \\ rw [] \\ fs []
  \\ fs [compile_def,lookup_fromAList,ALOOKUP_def,stubs_def]
  THEN1
   (CASE_TAC \\ fs [ALOOKUP_MAP]
    \\ disj1_tac
    \\ `ALOOKUP (toAList s.code) l1 = SOME v` by fs [ALOOKUP_toAList]
    \\ pop_assum mp_tac
    \\ qspec_tac (`toAList s.code`,`xs`)
    \\ Induct \\ fs [FORALL_PROD,ALOOKUP_def]
    \\ rw [] \\ fs [prog_comp_def])
  \\ disj2_tac \\ qexists_tac `n`
  \\ CASE_TAC \\ fs []
  \\ `ALOOKUP (toAList s.code) n = SOME e` by fs [ALOOKUP_toAList]
  \\ pop_assum mp_tac
  \\ qspec_tac (`toAList s.code`,`xs`)
  \\ Induct \\ fs [FORALL_PROD,ALOOKUP_def,prog_comp_def]
  \\ rw [] \\ metis_tac [get_labels_comp,SUBSET_DEF]
QED

val SUBMAP_DOMSUB_both = Q.prove(`
  A SUBMAP B ⇒
  A \\ c SUBMAP B \\ c`,
  rw[GSYM SUBMAP_DOMSUB_gen]>>
  metis_tac[SUBMAP_TRANS,SUBMAP_DOMSUB]);

val SUBMAP_FUPDATE_both = Q.prove(`
  A SUBMAP B ⇒
  A |+ (n,v) SUBMAP B |+ (n,v)`,
  rw[]>>match_mp_tac SUBMAP_mono_FUPDATE >>
  fs[SUBMAP_DOMSUB_both]);

(* This proof is very slow! *)
val inst_correct = Q.prove(`
  inst (i:'a inst) (s:('a,'c,'b) stackSem$state) = SOME t ∧
  LENGTH s.stack * (dimindex (:α) DIV 8) < dimword (:α) ∧
  LENGTH s.data_buffer.buffer + (LENGTH s.bitmaps + s.data_buffer.space_left) < dimword (:'a) - 1 ∧
  s.regs SUBMAP regs ⇒
  ∃regs1.
  inst i (s with <|regs := regs;
          compile := compile_rest;
          compile_oracle := (I ## MAP prog_comp ## I) o s.compile_oracle;
          gc_fun := anything; use_stack := T;
          use_store := T; use_alloc := F;
          code := fromAList (compile c (toAList s.code))|>) =
    SOME (t with <|regs := regs1;
          compile := compile_rest;
          compile_oracle := (I ## MAP prog_comp ## I) o t.compile_oracle;
          gc_fun := anything; use_stack := T;
          use_store := T; use_alloc := F;
          code := fromAList (compile c (toAList t.code))|>) ∧
    t.regs SUBMAP regs1 ∧
    LENGTH t.stack * (dimindex (:α) DIV 8) < dimword (:α) ∧
    LENGTH t.data_buffer.buffer + (LENGTH t.bitmaps + t.data_buffer.space_left) < dimword (:'a) - 1`,
  Cases_on`i`>>fs[inst_def]
  >-
    (rw[]>>rfs[state_component_equality])
  >-
    (rw[assign_def,word_exp_def,set_var_def]>>rfs[state_component_equality]>>
    metis_tac[SUBMAP_FUPDATE_both])
  >-
    (TOP_CASE_TAC>>rw[]>>
    fs[assign_def,word_exp_def,wordLangTheory.word_op_def,get_vars_def,get_var_def]>>
    fs[case_eq_thms] \\ rw[] \\ fs[IS_SOME_EXISTS,case_eq_thms] \\
    imp_res_tac FLOOKUP_SUBMAP>>fs[] \\
    TRY(Cases_on`r`) \\ fs[case_eq_thms,IS_SOME_EXISTS,word_exp_def]>>
    imp_res_tac FLOOKUP_SUBMAP>>fs[] \\
    fs[set_var_def,state_component_equality]>>
    metis_tac[SUBMAP_FUPDATE_both])
  >-
    (TOP_CASE_TAC>>rw[]>>
    TOP_CASE_TAC>>rw[]>>
    fs[]>>qpat_x_assum`A=SOME t` mp_tac>>
    fs[assign_def,word_exp_def,wordLangTheory.word_op_def,get_vars_def,get_var_def,mem_load_def,mem_store_def]>>
    every_case_tac>>
    imp_res_tac FLOOKUP_SUBMAP>>fs[set_var_def,state_component_equality]>>
    rw[]>>fs[]>>
    metis_tac[SUBMAP_FUPDATE_both])
  >-
    (TOP_CASE_TAC>>rw[]>>
    fs[get_fp_var_def,set_fp_var_def,get_var_def]>>
    every_case_tac>>
    imp_res_tac FLOOKUP_SUBMAP>>fs[]>>
    fs[set_var_def,state_component_equality]>>
    metis_tac[SUBMAP_FUPDATE_both]));

Theorem comp_correct:
   !p (s:('a,'c,'b)stackSem$state) r t m n c regs.
     evaluate (p,s) = (r,t) /\ r <> SOME Error /\ alloc_arg p /\
     (!k prog. lookup k s.code = SOME prog ==> k ≠ gc_stub_location /\ alloc_arg prog) /\
     (∀n k p. MEM (k,p) (FST (SND (s.compile_oracle n))) ⇒ k ≠ gc_stub_location ∧ alloc_arg p) /\
     s.gc_fun = word_gc_fun c ∧
     LENGTH s.stack * (dimindex (:'a) DIV 8) < dimword (:'a) /\
     s.regs SUBMAP regs /\
     s.use_stack ∧ (* Necessary for the data buffer oracle *)
     (* Data buffer does not wrap around *)
     LENGTH s.bitmaps + LENGTH s.data_buffer.buffer + s.data_buffer.space_left < dimword(:'a) - 1 /\
     s.compile = (λc. compile_rest c o (MAP prog_comp))
     ==>
     ?ck regs1.
       evaluate (FST (comp n m p),
          s with <| use_store := T; use_stack := T; use_alloc := F;
                    clock := s.clock + ck; regs := regs; gc_fun := anything;
                    compile_oracle := (I ## MAP prog_comp ## I) o s.compile_oracle;
                    compile := compile_rest;
                    code := fromAList (stack_alloc$compile c (toAList s.code)) |>) =
         (r, t with
             <| use_store := T; use_stack := T; use_alloc := F;
                regs := regs1; gc_fun := anything;
                compile_oracle := (I ## MAP prog_comp ## I) o t.compile_oracle;
                compile := compile_rest;
                code := fromAList (stack_alloc$compile c (toAList t.code)) |>) /\
       t.regs SUBMAP regs1 ∧
       LENGTH t.bitmaps + LENGTH t.data_buffer.buffer + t.data_buffer.space_left < dimword(:'a) - 1 /\
       ((∀w. r ≠ SOME (Halt w)) ⇒ LENGTH t.stack * (dimindex (:'a) DIV 8) < dimword (:'a))
Proof
  recInduct evaluate_ind
  \\ conj_tac THEN1 (* Skip *)
   (full_simp_tac(srw_ss())[Once comp_def,evaluate_def]
    \\ srw_tac[][] \\ full_simp_tac(srw_ss())[state_component_equality])
  \\ conj_tac THEN1 (* Halt *)
   (rpt strip_tac \\ full_simp_tac(srw_ss())[Once comp_def,evaluate_def,get_var_def]
    \\ Cases_on `FLOOKUP s.regs v` \\ fs [] \\ rw []
    \\ fs [FLOOKUP_DEF,SUBMAP_DEF,empty_env_def]
    \\ srw_tac[][] \\ full_simp_tac(srw_ss())[state_component_equality])
  \\ conj_tac THEN1 (* Alloc *)
   (rpt strip_tac \\ full_simp_tac(srw_ss())[evaluate_def,get_var_def]
    \\ every_case_tac \\ fs []
    \\ full_simp_tac(srw_ss())[Once comp_def,get_var_def]
    \\ fs [alloc_arg_def] \\ rw []
    \\ rename1 `alloc w s = (r,t)`
    \\ qmatch_goalsub_abbrev_tac`f1 o f2`
    \\ `alloc w (s with <|compile := compile_rest; compile_oracle := f1 o f2|>) =
        (r,t with <|compile := compile_rest; compile_oracle := f1 o f2|>)`
    by (
      qhdtm_x_assum`alloc`mp_tac \\
      simp[alloc_def,set_store_def,gc_def] \\
      every_case_tac \\ fs[] \\ rw[] \\ fs[empty_env_def] )
    \\ drule (GEN_ALL alloc_correct) \\ fs []
    \\ `word_gc_fun c = word_gc_fun c` by fs []
    \\ disch_then drule
    \\ disch_then (qspecl_then [`n'`,`m`,`regs`,`anything`] mp_tac) \\ fs []
    \\ impl_tac THEN1 (fs [FLOOKUP_DEF,SUBMAP_DEF] \\ rfs [])
    \\ strip_tac \\ qexists_tac `ck` \\ fs []
    \\ fs [state_component_equality,Abbr`f2`]
    \\ metis_tac[alloc_length_stack,alloc_const])
  \\ conj_tac (* Inst *) >- (
    rpt strip_tac
    \\ fs[Once comp_def,evaluate_def]
    \\ qpat_x_assum `_ = (r,t)` mp_tac
    \\ TOP_CASE_TAC \\ fs[] \\ rw[]
    \\ qexists_tac `0` \\ simp[]
    \\ drule inst_correct
    \\ rw[]
    \\ qmatch_goalsub_abbrev_tac`inst i st`
    \\ qmatch_asmsub_abbrev_tac`inst i st' = _`
    \\ `st = st'` by
        (unabbrev_all_tac>>fs[state_component_equality])
    \\ HINT_EXISTS_TAC
    \\ simp[])
  \\ conj_tac (* Get *) >- (
    fs[Once comp_def,evaluate_def,get_var_def]
    \\ every_case_tac \\ fs[] \\ rw[] \\ fs[set_var_def]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ qpat_x_assum`_ = t.regs`(assume_tac o SYM) \\ fs[]
    \\ match_mp_tac SUBMAP_mono_FUPDATE
    \\ rw[GSYM SUBMAP_DOMSUB_gen]
    \\ metis_tac[SUBMAP_TRANS,SUBMAP_DOMSUB] )
  \\ conj_tac (* Set *) >- (
    fs[Once comp_def,evaluate_def,get_var_def,set_store_def]
    \\ every_case_tac \\ fs[] \\ rw[] \\ fs[set_var_def]
    \\ qpat_x_assum`_ = (_,_)`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[] \\ rw[]
    \\ imp_res_tac FLOOKUP_SUBMAP \\ fs[]
    \\ full_simp_tac(srw_ss())[state_component_equality] )
  \\ conj_tac (* Tick *) >- (
    rpt strip_tac
    \\ qexists_tac `0` \\ full_simp_tac(srw_ss())[Once comp_def,evaluate_def,dec_clock_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[set_var_def]
    \\ full_simp_tac(srw_ss())[state_component_equality,empty_env_def])
  \\ conj_tac (* Seq *) >- (
    rpt strip_tac
    \\ simp [Once comp_def,dec_clock_def] \\ full_simp_tac(srw_ss())[evaluate_def]
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ full_simp_tac(srw_ss())[alloc_arg_def,evaluate_def]
    \\ first_x_assum (qspecl_then[`m`,`n`,`c`,`regs`]mp_tac)
    \\ impl_tac
    THEN1 (fs[] \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[] \\ res_tac \\ fs[])
    \\ strip_tac \\ rev_full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `res`) \\ full_simp_tac(srw_ss())[]
    THEN1 (qexists_tac `ck` \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC,LET_DEF] \\ srw_tac[][]
           \\ qexists_tac`regs1`\\simp[])
    \\ first_x_assum (qspecl_then[`m'`,`n`,`c`,`regs1`]mp_tac)
    \\ impl_tac THEN1 (
      fs[] \\
      imp_res_tac evaluate_consts \\ fs[] \\
      qpat_x_assum`evaluate _ = (NONE,s1)`assume_tac \\
      drule evaluate_code_bitmaps \\
      disch_then(qx_choose_then`k`strip_assume_tac) \\
      simp[lookup_FOLDL_union] \\
      conj_tac >- (
        ntac 3 strip_tac \\
        imp_res_tac FOLDL_OPTION_CHOICE_EQ_SOME_IMP_MEM \\
        fs[] >- metis_tac[] \\
        fs[MAP_MAP_o,MAP_GENLIST,MEM_GENLIST,lookup_fromAList] \\
        pop_assum (assume_tac o SYM) \\
        imp_res_tac ALOOKUP_MEM \\
        metis_tac[] ) \\
      fs[shift_seq_def] \\
      metis_tac[] )
    \\ strip_tac \\ qhdtm_x_assum`evaluate`mp_tac
    \\ drule (GEN_ALL evaluate_add_clock) \\ simp []
    \\ disch_then (qspec_then `ck'`assume_tac) \\ strip_tac
    \\ qexists_tac `ck + ck'` \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
    \\ imp_res_tac evaluate_consts \\ full_simp_tac(srw_ss())[]
    \\ ONCE_REWRITE_TAC[CONJ_COMM]
    \\ asm_exists_tac \\ simp[])
  \\ conj_tac (* Return *) >- (
    rpt strip_tac
    \\ qexists_tac `0` \\ full_simp_tac(srw_ss())[Once comp_def,evaluate_def,get_var_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[get_var_def]
    \\ full_simp_tac(srw_ss())[state_component_equality,empty_env_def]
    \\ imp_res_tac FLOOKUP_SUBMAP \\ fs[] \\ rw[]
    \\ simp[state_component_equality] )
  \\ conj_tac (* Raise *) >- (
    rpt strip_tac
    \\ qexists_tac `0` \\ full_simp_tac(srw_ss())[Once comp_def,evaluate_def,get_var_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[get_var_def]
    \\ full_simp_tac(srw_ss())[state_component_equality,empty_env_def]
    \\ imp_res_tac FLOOKUP_SUBMAP \\ fs[] )
  \\ conj_tac (* If *) >- (
    rpt strip_tac
    \\ simp [Once comp_def] \\ full_simp_tac(srw_ss())[evaluate_def,get_var_def]
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[] \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ qpat_x_assum`_ = (r,_)`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ strip_tac
    \\ every_case_tac \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[evaluate_def,get_var_def,get_var_imm_case,alloc_arg_def]
    \\ rev_full_simp_tac(srw_ss())[]
    \\ imp_res_tac FLOOKUP_SUBMAP \\ fs[]
    THENL [first_x_assum (qspecl_then[`m`,`n`,`c`,`regs`]mp_tac),
           first_x_assum (qspecl_then[`m'`,`n`,`c`,`regs`]mp_tac)]
    \\ match_mp_tac IMP_IMP \\ conj_tac
    \\ TRY (srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
    \\ strip_tac \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]
    \\ qexists_tac `ck` \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
    \\ BasicProvers.CASE_TAC \\ fs[]
    \\ imp_res_tac FLOOKUP_SUBMAP \\ fs[]
    \\ simp[state_component_equality])
  \\ conj_tac (* While *) >- (
    rpt strip_tac
    \\ simp [Once comp_def] \\ full_simp_tac(srw_ss())[evaluate_def,get_var_def]
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ qpat_x_assum`_ = (r,_)`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ imp_res_tac FLOOKUP_SUBMAP
    \\ full_simp_tac(srw_ss())[evaluate_def,get_var_def,get_var_imm_case,alloc_arg_def]
    \\ strip_tac
    \\ BasicProvers.TOP_CASE_TAC
    >- (
      pop_assum mp_tac
      \\ BasicProvers.TOP_CASE_TAC \\ fs[]
      \\ imp_res_tac FLOOKUP_SUBMAP \\ fs[] )
    \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      pop_assum mp_tac
      \\ BasicProvers.TOP_CASE_TAC \\ fs[]
      \\ imp_res_tac FLOOKUP_SUBMAP \\ fs[] )
    \\ qmatch_assum_rename_tac`_ _ _ _ = SOME (Word w1)`
    \\ qpat_x_assum`_ = _ (Word w1)`mp_tac
    \\ qmatch_assum_rename_tac`_ _ _ _ = SOME (Word w2)`
    \\ strip_tac
    \\ `w1 = w2`
    by (
      every_case_tac \\ fs[]
      \\ imp_res_tac FLOOKUP_SUBMAP \\ fs[] \\ rw[]
      \\ rpt(first_x_assum(qspec_then`regs`mp_tac)\\simp[]) )
    \\ fs[]
    \\ reverse BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    >- simp[state_component_equality]
    \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
    \\ pairarg_tac \\ fs[]
    \\ first_x_assum (qspecl_then[`m`,`n`,`c`,`regs`]mp_tac)
    \\ impl_tac THEN1 (full_simp_tac(srw_ss())[] \\ rpt strip_tac \\ res_tac \\ full_simp_tac(srw_ss())[])
    \\ full_simp_tac(srw_ss())[] \\ strip_tac \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `res <> NONE` \\ full_simp_tac(srw_ss())[]
    THEN1 (rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
      \\ qexists_tac `ck` \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
      \\ fs[state_component_equality])
    \\ Cases_on `s1.clock = 0` \\ full_simp_tac(srw_ss())[]
    THEN1 (rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
      \\ qexists_tac `ck` \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC,empty_env_def]
      \\ fs[state_component_equality])
    \\ full_simp_tac(srw_ss())[STOP_def]
    \\ first_x_assum (qspecl_then[`m`,`n`,`c`,`regs1`]mp_tac)
    \\ impl_tac
    THEN1 (
      fs[alloc_arg_def,dec_clock_def] \\
      imp_res_tac evaluate_consts \\ fs[] \\
      qpat_x_assum`evaluate _ = (NONE,s1)`assume_tac \\
      drule evaluate_code_bitmaps \\
      disch_then(qx_choose_then`k`strip_assume_tac) \\
      simp[lookup_FOLDL_union] \\
      conj_tac >- (
        ntac 3 strip_tac \\
        imp_res_tac FOLDL_OPTION_CHOICE_EQ_SOME_IMP_MEM \\
        fs[] >- metis_tac[] \\
        fs[MAP_MAP_o,MAP_GENLIST,MEM_GENLIST,lookup_fromAList] \\
        pop_assum (assume_tac o SYM) \\
        imp_res_tac ALOOKUP_MEM \\
        metis_tac[] ) \\
      fs[shift_seq_def] \\
      metis_tac[])
    \\ once_rewrite_tac [comp_def] \\ full_simp_tac(srw_ss())[LET_THM]
    \\ strip_tac \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac `ck+ck'`
    \\ qhdtm_x_assum`evaluate` mp_tac
    \\ drule (GEN_ALL evaluate_add_clock) \\ full_simp_tac(srw_ss())[]
    \\ disch_then (qspec_then `ck'` assume_tac)
    \\ full_simp_tac(srw_ss())[dec_clock_def] \\ strip_tac
    \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
    \\ `ck' + (s1.clock - 1) = ck' + s1.clock - 1` by decide_tac \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac evaluate_consts \\ full_simp_tac(srw_ss())[]
    \\ fs[state_component_equality])
  \\ conj_tac (* JumpLower *) >- (
    rpt strip_tac
    \\ full_simp_tac(srw_ss())[evaluate_def,get_var_def] \\ simp [Once comp_def]
    \\ qpat_x_assum`_ = (r,_)`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ imp_res_tac FLOOKUP_SUBMAP \\ fs[]
    \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      rw[evaluate_def,get_var_def,state_component_equality] \\ fs[] )
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ fs[find_code_def]
    \\ res_tac
    \\ imp_res_tac lookup_IMP_lookup_compile
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      rw[evaluate_def,get_var_def,find_code_def]
      \\ first_x_assum(qspec_then`c`strip_assume_tac) \\ fs[]
      \\ qexists_tac`0` \\ fs[]
      \\ fs[state_component_equality,empty_env_def] )
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ rw[evaluate_def,get_var_def,find_code_def]
    \\ first_x_assum(qspec_then`c`strip_assume_tac) \\ fs[]
    \\ fs[PULL_FORALL,dec_clock_def]
    \\ first_x_assum (qspecl_then[`n1`,`m1`,`c`,`regs`]mp_tac)
    \\ match_mp_tac IMP_IMP \\ conj_tac
    \\ TRY (srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
    \\ strip_tac \\ full_simp_tac(srw_ss())[]
    \\ `ck + s.clock - 1 = ck + (s.clock - 1)` by decide_tac
    \\ qexists_tac `ck` \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
    \\ simp[state_component_equality])
  \\ conj_tac (* Call *) >- (
     rpt strip_tac
     \\ full_simp_tac(srw_ss())[evaluate_def]
     \\ Cases_on `ret` \\ full_simp_tac(srw_ss())[] THEN1
     (Cases_on `find_code dest s.regs s.code` \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac find_code_regs_SUBMAP
      \\ every_case_tac \\ full_simp_tac(srw_ss())[empty_env_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[alloc_arg_def] \\ simp [Once comp_def,evaluate_def]
      \\ drule find_code_IMP_lookup \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]
      \\ res_tac \\ imp_res_tac lookup_IMP_lookup_compile
      \\ pop_assum (strip_assume_tac o SPEC_ALL) \\ full_simp_tac(srw_ss())[]
      THEN1 (qexists_tac `0` \\ full_simp_tac(srw_ss())[empty_env_def,state_component_equality])
      THEN1 (qexists_tac `0` \\ full_simp_tac(srw_ss())[empty_env_def,state_component_equality])
      \\ full_simp_tac(srw_ss())[dec_clock_def]
      \\ first_x_assum (qspecl_then[`n1`,`m1`,`c`,`regs`]mp_tac)
      \\ match_mp_tac IMP_IMP \\ conj_tac
      \\ TRY (srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[] \\ NO_TAC) \\ strip_tac \\ full_simp_tac(srw_ss())[]
      \\ `ck + s.clock - 1 = ck + (s.clock - 1)` by decide_tac
      \\ qexists_tac `ck` \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
      \\ simp[state_component_equality])
    \\ qmatch_assum_rename_tac `alloc_arg (Call (SOME z) dest handler)`
    \\ PairCases_on `z` \\ full_simp_tac(srw_ss())[] \\ simp [Once comp_def] \\ full_simp_tac(srw_ss())[]
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `find_code dest (s.regs \\ z1) s.code` \\ full_simp_tac(srw_ss())[]
    \\ `s.regs \\ z1 ⊑ regs \\ z1`
    by (
      simp[GSYM SUBMAP_DOMSUB_gen]
      \\ metis_tac[SUBMAP_TRANS,SUBMAP_DOMSUB] )
    \\ drule (GEN_ALL(ONCE_REWRITE_RULE[CONJ_COMM] find_code_regs_SUBMAP))
    \\ disch_then drule \\ strip_tac
    \\ drule find_code_IMP_lookup \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
    \\ res_tac \\ imp_res_tac lookup_IMP_lookup_compile
    \\ pop_assum (qspec_then`c`strip_assume_tac) \\ full_simp_tac(srw_ss())[alloc_arg_def]
    \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] THEN1
     (srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ every_case_tac \\ full_simp_tac(srw_ss())[]
      \\ TRY pairarg_tac \\ full_simp_tac(srw_ss())[evaluate_def]
      \\ qexists_tac `0` \\ full_simp_tac(srw_ss())[]
      \\ fs[empty_env_def,state_component_equality])
    \\ Cases_on `evaluate (x,dec_clock (set_var z1 (Loc z2 z3) s))`
    \\ Cases_on `q` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ TRY (
      rename1`Exception` ORELSE
      rename1`Result` ORELSE (
      every_case_tac \\ full_simp_tac(srw_ss())[] \\ TRY pairarg_tac
      \\ full_simp_tac(srw_ss())[evaluate_def,dec_clock_def,set_var_def]
      \\ qpat_abbrev_tac`pp = (z1,_)`
      \\ first_x_assum (qspecl_then[`n1`,`m1`,`c`,`regs |+ pp`]mp_tac)
      \\ match_mp_tac IMP_IMP \\ conj_tac
      \\ TRY (srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[]
        \\ qunabbrev_tac`pp`
        \\ match_mp_tac SUBMAP_mono_FUPDATE
        \\ simp[] \\ NO_TAC)
      \\ strip_tac \\ full_simp_tac(srw_ss())[]
      \\ `ck + s.clock - 1 = s.clock - 1 + ck` by decide_tac
      \\ qexists_tac `ck` \\ full_simp_tac(srw_ss())[]
      \\ simp[state_component_equality]
      \\ NO_TAC))
    THEN1
     (Cases_on `w = Loc z2 z3` \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
      \\ last_x_assum (qspecl_then[`n1`,`m1`,`c`,`regs |+ (z1,Loc z2 z3) `]mp_tac)
      \\ impl_tac
      >- (
        imp_res_tac evaluate_consts \\ fs[]
        \\ fs[dec_clock_def,set_var_def]
        \\ conj_tac >- metis_tac[]
        \\ conj_tac >- metis_tac[]
        \\ match_mp_tac SUBMAP_mono_FUPDATE
        \\ simp[] )
      \\ strip_tac \\ fs[] \\ rfs[]
      \\ first_x_assum (qspecl_then[`m`,`n`,`c`,`regs1`]mp_tac)
      \\ impl_tac
      >- (
        imp_res_tac evaluate_consts \\ fs[] \\
        qmatch_goalsub_rename_tac`lookup _ s1.code` \\
        qpat_x_assum`_ = (_,s1)`assume_tac \\
        drule evaluate_code_bitmaps \\
        strip_tac \\ rveq \\ simp[] \\
        fs[shift_seq_def,lookup_FOLDL_union] \\
        conj_tac >- (
          ntac 3 strip_tac \\
          imp_res_tac FOLDL_OPTION_CHOICE_EQ_SOME_IMP_MEM \\
          fs[] >- metis_tac[] \\
          fs[MAP_MAP_o,MAP_GENLIST,MEM_GENLIST,lookup_fromAList] \\
          pop_assum (assume_tac o SYM) \\
          imp_res_tac ALOOKUP_MEM \\
          metis_tac[] ) \\
        metis_tac[])
      \\ strip_tac \\ fs[] \\ rw[]
      \\ Cases_on `handler` \\ full_simp_tac(srw_ss())[]
      \\ TRY (PairCases_on `x'` \\ fs[] \\ pairarg_tac \\ full_simp_tac(srw_ss())[])
      \\ full_simp_tac(srw_ss())[evaluate_def,dec_clock_def,set_var_def]
      \\ qhdtm_x_assum`evaluate`mp_tac
      \\ first_assum (mp_tac o Q.SPEC `ck'` o
             MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
             (evaluate_add_clock |> GEN_ALL))) \\ full_simp_tac(srw_ss())[]
      \\ srw_tac[][] \\ qexists_tac `ck' + ck` \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
      \\ `ck + (ck' + (s.clock - 1)) = ck + (ck' + s.clock) - 1` by decide_tac
      \\ full_simp_tac(srw_ss())[] \\ imp_res_tac evaluate_consts \\ full_simp_tac(srw_ss())[]
      \\ simp[state_component_equality])
    \\ Cases_on `handler` \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[evaluate_def,dec_clock_def,set_var_def]
    THEN1
     (first_x_assum (qspecl_then[`n1`,`m1`,`c`,`regs |+ (z1,Loc z2 z3)`]mp_tac)
      \\ impl_tac
      >- (
        imp_res_tac evaluate_consts \\ full_simp_tac(srw_ss())[]
        \\ conj_tac >- metis_tac[]
        \\ conj_tac >- metis_tac[]
        \\ srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[]
        \\ match_mp_tac SUBMAP_mono_FUPDATE
        \\ simp[]
        \\ NO_TAC) \\ srw_tac[][]
      \\ `ck + s.clock - 1 = s.clock - 1 + ck` by decide_tac
      \\ qexists_tac `ck` \\ full_simp_tac(srw_ss())[]
      \\ simp[state_component_equality])
    \\ PairCases_on `x'` \\ full_simp_tac(srw_ss())[]
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[evaluate_def,dec_clock_def,set_var_def]
    \\ Cases_on `w = Loc x'1 x'2` \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
    \\ last_x_assum (qspecl_then[`n1`,`m1`,`c`,`regs |+ (z1,Loc z2 z3)`]mp_tac)
    \\ impl_tac
    >- (
      imp_res_tac evaluate_consts \\ full_simp_tac(srw_ss())[]
      \\ conj_tac >- metis_tac[]
      \\ conj_tac >- metis_tac[]
      \\ match_mp_tac SUBMAP_mono_FUPDATE
      \\ simp[]
      \\ NO_TAC) \\ srw_tac[][] \\ rev_full_simp_tac(srw_ss())[]
    \\ first_x_assum (qspecl_then[`m'`,`n`,`c`,`regs1`]mp_tac)
    \\ impl_tac
    >- (
      imp_res_tac evaluate_consts \\ full_simp_tac(srw_ss())[] \\
      qmatch_goalsub_rename_tac`lookup _ s1.code` \\
      qpat_x_assum`_ = (_,s1)`assume_tac \\
      drule evaluate_code_bitmaps \\
      strip_tac \\ rveq \\ simp[] \\
      fs[shift_seq_def,lookup_FOLDL_union] \\
      conj_tac >- (
        ntac 3 strip_tac \\
        imp_res_tac FOLDL_OPTION_CHOICE_EQ_SOME_IMP_MEM \\
        fs[] >- metis_tac[] \\
        fs[MAP_MAP_o,MAP_GENLIST,MEM_GENLIST,lookup_fromAList] \\
        pop_assum (assume_tac o SYM) \\
        imp_res_tac ALOOKUP_MEM \\
        metis_tac[] ) \\
      metis_tac[])
    \\ srw_tac[][]
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ first_assum (mp_tac o Q.SPEC `ck'` o
             MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
             (evaluate_add_clock |> GEN_ALL))) \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ qexists_tac `ck+ck'` \\ full_simp_tac(srw_ss())[]
    \\ `ck + ck' + s.clock - 1 = s.clock - 1 + ck + ck'` by decide_tac \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac evaluate_consts \\ full_simp_tac(srw_ss())[]
    \\ simp[state_component_equality])
  (* Install *)
  \\ conj_tac >- (
    rw[] \\
    simp[Once comp_def] \\
    qhdtm_x_assum`evaluate`mp_tac \\
    simp[evaluate_def] \\
    simp[case_eq_thms] \\
    pairarg_tac \\ fs[] \\
    rw[] \\
    fs[get_var_def] \\
    imp_res_tac FLOOKUP_SUBMAP \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    Cases_on`progs` \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    qpat_x_assum`_ = (r,t)`mp_tac \\
    TOP_CASE_TAC \\ fs[prog_comp_lemma] \\
    simp[shift_seq_def] \\
    TOP_CASE_TAC>>fs[] >> rw[]>>
    fs[state_component_equality] \\
    CONJ_TAC>-
      fs[shift_seq_def,FUN_EQ_THM]>>
    CONJ_TAC>-(
      DEP_REWRITE_TAC[spt_eq_thm] \\
      simp[wf_union,wf_fromAList,lookup_union,lookup_fromAList] \\
      simp[compile_def,ALOOKUP_APPEND] \\
      gen_tac \\ CASE_TAC \\ fs[] \\
      simp[prog_comp_lemma] \\
      simp[ALOOKUP_MAP_2] \\
      simp[ALOOKUP_toAList,lookup_union] \\
      match_mp_tac EQ_SYM \\ CASE_TAC \\ fs[] \\
      simp[lookup_fromAList] >>
      fs[prog_comp_lemma]>>rw[])>>
    CONJ_TAC>-(
      fs[prog_comp_lemma]>>
      match_mp_tac SUBMAP_mono_FUPDATE \\
      simp[GSYM SUBMAP_DOMSUB_gen] \\
      metis_tac[SUBMAP_DOMSUB,SUBMAP_TRANS,SUBMAP_DRESTRICT_MONOTONE,
                SUBSET_REFL])>>
    fs[wordSemTheory.buffer_flush_def]>>rw[])
  (* CodeBufferWrite *)
  \\ conj_tac >- (
    rw[Once comp_def,evaluate_def,get_var_def] \\
    fs[case_eq_thms] \\ rw[] \\
    imp_res_tac FLOOKUP_SUBMAP \\ fs[] \\
    simp[state_component_equality] )
  (* DataBufferWrite *)
  \\ conj_tac >- (
    rw[Once comp_def,evaluate_def,get_var_def] \\
    fs[case_eq_thms] \\ rw[] \\
    imp_res_tac FLOOKUP_SUBMAP \\ fs[] \\
    simp[state_component_equality]\\
    fs[wordSemTheory.buffer_write_def] \\
    rw[])
  \\ conj_tac (* FFI *) >- (
    rpt strip_tac
    \\ qexists_tac `0` \\ full_simp_tac(srw_ss())[Once comp_def,evaluate_def,get_var_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[get_var_def]
    \\ imp_res_tac FLOOKUP_SUBMAP \\ fs[]
    \\ full_simp_tac(srw_ss())[state_component_equality,empty_env_def,LET_DEF]
    \\ fs[] \\ rw[]
    \\ simp[markerTheory.Abbrev_def]
    \\ fs[] \\ rveq \\ fs[]
    \\ qmatch_goalsub_abbrev_tac `a1 ⊑ _`
    \\ qpat_x_assum `_ = a1` (assume_tac o GSYM)
    \\ simp[]
    \\ match_mp_tac SUBMAP_DRESTRICT_MONOTONE
    \\ simp[])
  \\ rpt strip_tac
  \\ qexists_tac `0`
  \\ full_simp_tac(srw_ss())[Once comp_def,evaluate_def,get_var_def,set_var_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[get_var_def]
  \\ TRY (drule loc_check_compile \\ impl_tac >- metis_tac[] \\ fs []) \\ fs []
  \\ full_simp_tac(srw_ss())[state_component_equality,empty_env_def,LET_DEF]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[state_component_equality,empty_env_def,LET_DEF]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[get_var_def] \\ rw[]
  \\ imp_res_tac FLOOKUP_SUBMAP \\ fs[] \\ rw[markerTheory.Abbrev_def]
  \\ rw[state_component_equality]
  \\ match_mp_tac SUBMAP_mono_FUPDATE
  \\ rw[GSYM SUBMAP_DOMSUB_gen]
  \\ metis_tac[SUBMAP_TRANS,SUBMAP_DOMSUB]
QED

val comp_correct_thm =
  comp_correct |> SPEC_ALL
  |> Q.INST [`regs`|->`s.regs`]
  |> REWRITE_RULE [SUBMAP_REFL];

val with_same_regs_lemma = Q.prove(
  `s with <| regs := s.regs; compile := cc; compile_oracle := oracle; gc_fun := anything; use_stack := T; use_store := T; use_alloc := F; clock := k; code := c |> =
   s with <| compile := cc; compile_oracle := oracle; gc_fun := anything; use_stack := T; use_store := T; use_alloc := F; clock := k; code := c |>`,
  simp[state_component_equality])
val _ = augment_srw_ss[rewrites[with_same_regs_lemma]];

Theorem compile_semantics:
   (!k prog. lookup k s.code = SOME prog ==> k <> gc_stub_location /\ alloc_arg prog) /\
    (∀n k p.  MEM (k,p) (FST (SND (s.compile_oracle n))) ⇒ k ≠ gc_stub_location ∧ alloc_arg p) /\
   (s:('a,'c,'b)stackSem$state).gc_fun = (word_gc_fun c:α gc_fun_type) /\
   LENGTH s.bitmaps + LENGTH s.data_buffer.buffer + s.data_buffer.space_left < dimword (:α) − 1 ∧
   LENGTH s.stack * (dimindex (:'a) DIV 8) < dimword (:α) /\
   s.use_stack ∧
   s.compile = (λc. compile_rest c o (MAP prog_comp)) /\
   semantics start s <> Fail
   ==>
   semantics start (s with <|
                      code := fromAList (stack_alloc$compile c (toAList s.code));
                      gc_fun := anything;
                      compile := compile_rest;
                      compile_oracle := (I ## MAP prog_comp ## I) o s.compile_oracle;
                      use_store := T;
                      use_stack := T;
                      use_alloc := F |>) =
   semantics start s
Proof
  simp[GSYM AND_IMP_INTRO] >> ntac 6 strip_tac >>
  simp[semantics_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  DEEP_INTRO_TAC some_intro >> full_simp_tac(srw_ss())[] >>
  conj_tac >- (
    gen_tac >> ntac 2 strip_tac >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
      first_x_assum(qspec_then`k'`mp_tac)>>simp[]>>
      (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >>
      simp[] >>
      qmatch_assum_rename_tac`_ = (res,_)` >>
      Cases_on`res=SOME Error`>>simp[]>>
      drule comp_correct_thm >>
      simp[alloc_arg_def,RIGHT_FORALL_IMP_THM] >>
      impl_tac >- metis_tac[] >>
      simp[comp_def] >>
      strip_tac >>
      qpat_x_assum`_ ≠ SOME TimeOut`mp_tac >>
      (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >>
      strip_tac >>
      drule (Q.GEN`extra`evaluate_add_clock) >>
      disch_then(qspec_then`ck`mp_tac) >> full_simp_tac(srw_ss())[] >>
      fs[]) >>
    DEEP_INTRO_TAC some_intro >> full_simp_tac(srw_ss())[] >>
    conj_tac >- (
      srw_tac[][] >>
      Cases_on`r=TimeOut`>>full_simp_tac(srw_ss())[]>>
      qpat_x_assum `evaluate _ = (SOME r, t)` assume_tac >>
      dxrule comp_correct_thm >>
      simp[RIGHT_FORALL_IMP_THM] >>
      impl_tac >- (
        simp[alloc_arg_def] >>
        reverse conj_tac >- metis_tac[] >>
        CCONTR_TAC >> fs[]) >>
      strip_tac >>
      dxrule(GEN_ALL evaluate_add_clock) >>
      disch_then(qspec_then `k'` mp_tac) >>
      impl_tac >- (CCONTR_TAC >> fs[]) >>
      dxrule(GEN_ALL evaluate_add_clock) >>
      disch_then(qspec_then `ck + k` mp_tac) >>
      impl_tac >- (CCONTR_TAC >> fs[]) >>
      ntac 2 strip_tac >>
      fs[comp_def,state_component_equality] >>
      rveq >> rpt(PURE_FULL_CASE_TAC >> fs[])) >>
    drule comp_correct_thm >>
    simp[RIGHT_FORALL_IMP_THM] >>
    impl_tac >- (
      simp[alloc_arg_def] >>
      reverse conj_tac >- metis_tac[] >>
      rpt(first_x_assum(qspec_then`k`mp_tac)) >>
    srw_tac[][]) >>
    simp[comp_def] >>
    strip_tac >>
    asm_exists_tac >> simp[] >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[]) >>
  ntac 2 strip_tac >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
    first_x_assum(qspec_then`k`mp_tac)>>simp[]>>
    first_x_assum(qspec_then`k`mp_tac)>>
    (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >>
    simp[] >> strip_tac >> fs[] >>
    drule comp_correct_thm >>
    simp[alloc_arg_def,comp_def] >>
    conj_tac >- metis_tac[] >>
    srw_tac[][] >>
    qpat_x_assum`_ ≠ SOME TimeOut`mp_tac >>
    (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >> srw_tac[][] >>
    drule (GEN_ALL evaluate_add_clock) >>
    disch_then(qspec_then`ck`mp_tac)>>simp[]) >>
  DEEP_INTRO_TAC some_intro >> full_simp_tac(srw_ss())[] >>
  conj_tac >- (
    srw_tac[][] >>
    qpat_x_assum`∀k t. _`(qspec_then`k`mp_tac) >>
    (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >>
    simp[] >>
    last_x_assum mp_tac >>
    last_x_assum mp_tac >>
    last_x_assum(qspec_then`k`mp_tac) >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    drule comp_correct_thm >>
    simp[alloc_arg_def,comp_def] >>
    conj_tac >- metis_tac[] >>
    srw_tac[][] >>
    Cases_on`r=TimeOut`>>full_simp_tac(srw_ss())[] >>
    qhdtm_x_assum`evaluate`mp_tac >>
    drule (GEN_ALL evaluate_add_clock) >>
    disch_then(qspec_then`ck`mp_tac)>>simp[] ) >>
  srw_tac[][] >>
  qmatch_abbrev_tac`build_lprefix_lub l1 = build_lprefix_lub l2` >>
  `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
    suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_new_chain,unique_lprefix_lub] >>
  conj_asm1_tac >- (
    UNABBREV_ALL_TAC >>
    conj_tac >>
    Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
    REWRITE_TAC[IMAGE_COMPOSE] >>
    match_mp_tac prefix_chain_lprefix_chain >>
    simp[prefix_chain_def,PULL_EXISTS] >>
    qx_genl_tac[`k1`,`k2`] >>
    qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
    match_mp_tac(PROVE[]``((a ⇒ c) ∧ (b ⇒ d)) ⇒ (a ∨ b ⇒ c ∨ d)``) \\
    simp[LESS_EQ_EXISTS] \\
    conj_tac \\ strip_tac \\ rveq \\
    qmatch_goalsub_abbrev_tac`e,ss` \\
    Q.ISPECL_THEN[`p`,`e`,`ss`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono) \\
    simp[Abbr`ss`]) >>
  simp[equiv_lprefix_chain_thm] >>
  unabbrev_all_tac >> simp[PULL_EXISTS] >>
  ntac 2 (pop_assum kall_tac) >>
  simp[LNTH_fromList,PULL_EXISTS] >>
  simp[GSYM FORALL_AND_THM] >>
  rpt gen_tac >>
  (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >> full_simp_tac(srw_ss())[] >>
  (fn g => subterm (fn tm => Cases_on`^(assert (fn tm => has_pair_type tm andalso free_in tm (#2 g)) tm)`) (#2 g) g) >> full_simp_tac(srw_ss())[] >>
  drule comp_correct_thm >>
  simp[comp_def,RIGHT_FORALL_IMP_THM] >>
  impl_tac >- (
    simp[alloc_arg_def] >>
    reverse conj_tac >- metis_tac[] >>
    rpt(first_x_assum(qspec_then`k`mp_tac))>>srw_tac[][] ) >>
  strip_tac >>
  reverse conj_tac >- (
    srw_tac[][] >>
    qexists_tac`ck+k`>>simp[] ) >>
  srw_tac[][] >>
  qexists_tac`k`>>simp[] >>
  ntac 2 (qhdtm_x_assum`evaluate`mp_tac) >>
  qmatch_assum_abbrev_tac`evaluate (e,ss) = _` >>
  Q.ISPECL_THEN[`ck`,`e`,`ss`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono)>>
  simp[Abbr`ss`] >>
  ntac 3 strip_tac >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[IS_PREFIX_APPEND] >>
  simp[EL_APPEND1]
QED

(* TODO: does this have to initialize the data_buffer to empty? *)
val make_init_def = Define `
  make_init c code oracle s =
    s with <| code := code; use_alloc := T; use_stack := T; gc_fun := word_gc_fun c
            ; compile := λc. s.compile c o (MAP prog_comp)
            ; compile_oracle := oracle |>`;

Theorem prog_comp_lambda:
   prog_comp = λ(n,p). ^(rhs (concl (SPEC_ALL prog_comp_def)))
Proof
  srw_tac[][FUN_EQ_THM,prog_comp_def,LAMBDA_PROD,FORALL_PROD]
QED

Theorem make_init_semantics:
   (!k prog. ALOOKUP code k = SOME prog ==> k <> gc_stub_location /\ alloc_arg prog) /\
   (∀n k p.  MEM (k,p) (FST (SND (oracle n))) ⇒ k ≠ gc_stub_location ∧ alloc_arg p) /\
   s.use_stack ∧ s.use_store ∧ ~s.use_alloc /\ s.code = fromAList (compile c code) /\
   s.compile_oracle = (I ## MAP prog_comp ## I) o oracle /\
   LENGTH s.bitmaps + LENGTH s.data_buffer.buffer + s.data_buffer.space_left < dimword (:α) − 1 ∧
   LENGTH s.stack * (dimindex (:α) DIV 8) < dimword (:α) ∧
   ALL_DISTINCT (MAP FST code) /\
   semantics start (make_init c (fromAList code) oracle s) <> Fail ==>
   semantics start (s:('a,'c,'ffi) stackSem$state) =
   semantics start (make_init c (fromAList code) oracle s)
Proof
  srw_tac[][]
  \\ drule (CONV_RULE(LAND_CONV(move_conj_left(can dest_neg)))compile_semantics
            |> GEN_ALL)
  \\ disch_then (qspecl_then [`s.compile`,`c`,`s.gc_fun`] mp_tac)
  \\ full_simp_tac(srw_ss())[make_init_def,lookup_fromAList]
  \\ impl_tac THEN1 (srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[])
  \\ disch_then (assume_tac o GSYM)
  \\ full_simp_tac(srw_ss())[] \\ AP_TERM_TAC
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[spt_eq_thm,wf_fromAList,lookup_fromAList,compile_def]
  \\ srw_tac[][]
  \\ srw_tac[][ALOOKUP_APPEND] \\ BasicProvers.CASE_TAC
  \\ simp[prog_comp_lambda,ALOOKUP_MAP_2]
  \\ simp[ALOOKUP_toAList,lookup_fromAList]
QED

Theorem next_lab_EQ_MAX = Q.prove(`
  !q (n:num) aux. next_lab q aux = MAX aux (next_lab q 0)`,
  ho_match_mp_tac next_lab_ind>>Cases_on`q`>>rw[]>>
  once_rewrite_tac [next_lab_def]>>
  simp_tac (srw_ss()) [] >>
  every_case_tac >>
  simp_tac (srw_ss()) [] >>
  rpt (qpat_x_assum `!x. _` (mp_tac o SIMP_RULE std_ss [])) >>
  rpt strip_tac >>
  rpt (pop_assum (fn th => once_rewrite_tac [th])) >>
  fs [AC MAX_ASSOC MAX_COMM]) |> SIMP_RULE std_ss [];

val MAX_SIMP = prove(
  ``MAX n (MAX n m) = MAX n m``,
  fs [MAX_DEF]);

Theorem next_lab_thm:
   !p.
      next_lab (p:'a stackLang$prog) 1 =
      case p of
      | Seq p1 p2 => MAX (next_lab p1 1) (next_lab p2 1)
      | If _ _ _ p1 p2 => MAX (next_lab p1 1) (next_lab p2 1)
      | While _ _ _ p => next_lab p 1
      | Call NONE _ NONE => 1
      | Call NONE _ (SOME (_,_,l2)) => l2 + 1
      | Call (SOME (p,_,_,l2)) _ NONE => MAX (next_lab p 1) (l2 + 1)
      | Call (SOME (p,_,_,l2)) _ (SOME (p',_,l3)) =>
           MAX (MAX (next_lab p 1) (next_lab p' 1)) (MAX l2 l3 + 1)
      | _ => 1
Proof
  Induct \\ simp [Once next_lab_def] \\ fs []
  \\ once_rewrite_tac [next_lab_EQ_MAX]
  \\ once_rewrite_tac [next_lab_EQ_MAX]
  \\ once_rewrite_tac [next_lab_EQ_MAX]
  \\ fs [AC MAX_ASSOC MAX_COMM,MAX_SIMP]
  \\ every_case_tac \\ fs []
  \\ once_rewrite_tac [next_lab_EQ_MAX]
  \\ once_rewrite_tac [next_lab_EQ_MAX]
  \\ once_rewrite_tac [next_lab_EQ_MAX]
  \\ fs [AC MAX_ASSOC MAX_COMM,MAX_SIMP]
  \\ fs [MAX_DEF]
QED

Theorem extract_labels_next_lab:
    ∀p (aux:num) e.
    MEM e (extract_labels p) ⇒
    SND e < next_lab p 1
Proof
  ho_match_mp_tac next_lab_ind>>Cases_on`p`>>rw[]>>
  once_rewrite_tac [next_lab_thm]>>fs[extract_labels_def]>>
  fs[extract_labels_def]>>
  BasicProvers.EVERY_CASE_TAC>>fs []>>fs[MAX_DEF]
QED

Theorem stack_alloc_lab_pres:
    ∀n nl p aux.
  EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0) (extract_labels p) ∧
  ALL_DISTINCT (extract_labels p) ∧
  next_lab p 1 ≤ nl ⇒
  let (cp,nl') = comp n nl p in
  EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0) (extract_labels cp) ∧
  ALL_DISTINCT (extract_labels cp) ∧
  (∀lab. MEM lab (extract_labels cp) ⇒ MEM lab (extract_labels p) ∨ (nl ≤ SND lab ∧ SND lab < nl')) ∧
  nl ≤ nl'
Proof
  HO_MATCH_MP_TAC comp_ind>>Cases_on`p`>>rw[]>>
  once_rewrite_tac [comp_def]>>fs[extract_labels_def]
  >-
    (BasicProvers.EVERY_CASE_TAC>>fs[]>>rveq>>fs[extract_labels_def]>>
    rpt(pairarg_tac>>fs[])>>rveq>>fs[extract_labels_def]>>
    qpat_x_assum`A<=nl` mp_tac>>
    simp[Once next_lab_thm]>>
    strip_tac>>
    fs[ALL_DISTINCT_APPEND]
    >-
      (CCONTR_TAC>>fs[]>>
      res_tac>>fs[])
    >>
      `next_lab q 1 ≤ m'` by fs[]>>
      fs[]>>rfs[]>>
      `r < nl ∧ r' < nl` by
        fs[MAX_DEF]>>
      rw[]>>
      TRY(CCONTR_TAC>>fs[]>>
      res_tac>>fs[])
      >- metis_tac[]
      >>
        imp_res_tac extract_labels_next_lab>>fs[])
  >>
  TRY
  (rpt(pairarg_tac>>fs[])>>rveq>>fs[extract_labels_def]>>
  qpat_x_assum`A<=nl` mp_tac>>
  simp[Once next_lab_thm])>>
  (strip_tac>>
  fs[ALL_DISTINCT_APPEND]>>rw[]
  >-
    (CCONTR_TAC>>fs[]>>
    res_tac>>fs[]>- metis_tac[]>>
    imp_res_tac extract_labels_next_lab>>
    fs[])
  >>
    res_tac>>fs[])
QED

Theorem stack_alloc_comp_stack_asm_name:
    ∀n m p.
  stack_asm_name c p ∧ stack_asm_remove (c:'a asm_config) p ⇒
  let (p',m') = comp n m p in
  stack_asm_name c p' ∧ stack_asm_remove (c:'a asm_config) p'
Proof
  ho_match_mp_tac comp_ind>>Cases_on`p`>>rw[]>>
  simp[Once comp_def]
  >-
    (Cases_on`o'`>-
      fs[Once comp_def,stack_asm_name_def,stack_asm_remove_def]
    >>
    PairCases_on`x`>>SIMP_TAC std_ss [Once comp_def]>>fs[]>>
    FULL_CASE_TAC>>fs[]>>
    TRY(PairCases_on`x`)>>
    rpt(pairarg_tac>>fs[])>>rw[]>>
    fs[stack_asm_name_def,stack_asm_remove_def])
  >>
    rpt(pairarg_tac>>fs[])>>rw[]>>
    fs[stack_asm_name_def,stack_asm_remove_def]
QED

Theorem stack_alloc_stack_asm_convs:
    EVERY (λ(n,p). stack_asm_name c p) prog ∧
  EVERY (λ(n,p). (stack_asm_remove (c:'a asm_config) p)) prog ∧
  (* conf_ok is too strong, but we already have it anyway *)
  conf_ok (:'a) conf ∧
  addr_offset_ok c 0w ∧
  reg_name 10 c ∧ good_dimindex(:'a) ∧
  c.valid_imm (INL Add) 8w ∧
  c.valid_imm (INL Add) 4w ∧
  c.valid_imm (INL Add) 1w ∧
  c.valid_imm (INL Sub) 1w
  ⇒
  EVERY (λ(n,p). stack_asm_name c p) (compile conf prog) ∧
  EVERY (λ(n,p). stack_asm_remove c p) (compile conf prog)
Proof
  fs[compile_def]>>rw[]>>
    TRY (EVAL_TAC>>every_case_tac >>
         EVAL_TAC>>every_case_tac >>
         fs [] >> EVAL_TAC >>
     fs[reg_name_def, labPropsTheory.good_dimindex_def,
        asmTheory.offset_ok_def, data_to_wordTheory.conf_ok_def,
        data_to_wordTheory.shift_length_def]>>
     pairarg_tac>>fs[]>>NO_TAC)
  >>
  fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,prog_comp_def]>>
  rw[]>>res_tac>>
  drule stack_alloc_comp_stack_asm_name>>fs[]>>
  disch_then(qspecl_then[`p_1`,`next_lab p_2 1`] assume_tac)>>
  pairarg_tac>>fs[]
QED

Theorem stack_alloc_reg_bound:
   10 ≤ sp ∧
    EVERY (\p. reg_bound p sp)
       (MAP SND prog1) ==>
    EVERY (\p. reg_bound p sp)
       (MAP SND (compile dc prog1))
Proof
  fs[stack_allocTheory.compile_def]>>
  strip_tac>>CONJ_TAC
  >-
    (EVAL_TAC>>TOP_CASE_TAC>>EVAL_TAC>>fs[]>>
    IF_CASES_TAC>>EVAL_TAC>>fs[])
  >>
  pop_assum mp_tac>>
  qid_spec_tac`prog1`>>Induct>>
  fs[stack_allocTheory.prog_comp_def,FORALL_PROD]>>
  ntac 3 strip_tac>>fs[]>>
  qpat_x_assum`reg_bound p_2 sp` mp_tac>>
  qpat_x_assum`10 ≤ sp` mp_tac>>
  rpt (pop_assum kall_tac)>>
  (qpat_abbrev_tac`l = next_lab _ _`) >> pop_assum kall_tac>>
  qid_spec_tac `p_2` >>
  qid_spec_tac `l` >>
  qid_spec_tac `p_1` >>
  ho_match_mp_tac stack_allocTheory.comp_ind>>
  Cases_on`p_2`>>rw[]>>
  simp[Once stack_allocTheory.comp_def]>>
  fs[reg_bound_def]>>
  TRY(ONCE_REWRITE_TAC [stack_allocTheory.comp_def]>>
    Cases_on`o'`>>TRY(PairCases_on`x`)>>fs[reg_bound_def]>>
    BasicProvers.EVERY_CASE_TAC)>>
  rpt(pairarg_tac>>fs[reg_bound_def])
QED

Theorem stack_alloc_call_args:
   EVERY (λp. call_args p 1 2 3 4 0) (MAP SND prog1) ==>
   EVERY (λp. call_args p 1 2 3 4 0) (MAP SND (compile dc prog1))
Proof
  fs[stack_allocTheory.compile_def]>>
  strip_tac>>CONJ_TAC
  >-
    (EVAL_TAC>>TOP_CASE_TAC>>EVAL_TAC>>fs[]>>
    IF_CASES_TAC>>EVAL_TAC>>fs[])
  >>
  pop_assum mp_tac>>
  qid_spec_tac`prog1`>>Induct>>
  fs[stack_allocTheory.prog_comp_def,FORALL_PROD]>>
  ntac 3 strip_tac>>fs[]>>
  (qpat_abbrev_tac`l = next_lab _ _`) >> pop_assum kall_tac>>
  qpat_x_assum`call_args p_2 1 2 3 4 0` mp_tac>>
  rpt (pop_assum kall_tac)>>
  qid_spec_tac `p_2` >>
  qid_spec_tac `l` >>
  qid_spec_tac `p_1` >>
  ho_match_mp_tac stack_allocTheory.comp_ind>>
  Cases_on`p_2`>>rw[]>>
  simp[Once stack_allocTheory.comp_def]>>fs[call_args_def]>>
  TRY(ONCE_REWRITE_TAC [stack_allocTheory.comp_def]>>
    Cases_on`o'`>>TRY(PairCases_on`x`)>>fs[call_args_def]>>
    BasicProvers.EVERY_CASE_TAC)>>
  rpt(pairarg_tac>>fs[call_args_def])
QED

Theorem compile_has_fp_ops[simp]:
  compile (dconf with <| has_fp_ops := b1; has_fp_tern := b2 |>) code = compile dconf code
Proof
  fs [compile_def,stubs_def,word_gc_code_def]
  \\ every_case_tac \\ fs []
  \\ fs [data_to_wordTheory.small_shift_length_def,
         word_gc_move_code_def,
         word_gc_move_list_code_def,
         word_gc_move_loop_code_def,
         word_gc_move_roots_bitmaps_code_def,
         word_gc_move_bitmaps_code_def,
         word_gc_move_bitmap_code_def,
         word_gen_gc_move_code_def,
         word_gen_gc_move_list_code_def,
         word_gen_gc_move_roots_bitmaps_code_def,
         word_gen_gc_move_bitmaps_code_def,
         word_gen_gc_move_bitmap_code_def,
         word_gen_gc_move_data_code_def,
         word_gen_gc_move_refs_code_def,
         word_gen_gc_move_loop_code_def,
         word_gen_gc_partial_move_code_def,
         word_gen_gc_partial_move_list_code_def,
         word_gen_gc_partial_move_roots_bitmaps_code_def,
         word_gen_gc_partial_move_bitmaps_code_def,
         word_gen_gc_partial_move_bitmap_code_def,
         word_gen_gc_partial_move_data_code_def,
         word_gen_gc_partial_move_ref_list_code_def]
QED

val _ = export_theory();
