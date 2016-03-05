open preamble
     stack_allocTheory
     stackLangTheory
     stackSemTheory
     stackPropsTheory
     bvp_to_wordProofTheory

val _ = new_theory"stack_allocProof";

(* move and join with stack_remove *)

val lsl_lsr = Q.store_thm("lsl_lsr",
  `w2n ((n:'a word)) * 2 ** a < dimword (:'a) ⇒ n << a >>> a = n`,
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
  \\ simp[MULT_DIV]);

val bytes_in_word_word_shift = Q.store_thm("bytes_in_word_word_shift",
  `good_dimindex(:'a) ∧ w2n (bytes_in_word:'a word) * w2n n < dimword(:'a) ⇒
   (bytes_in_word:'a word * n) >>> word_shift (:'a) = n`,
  EVAL_TAC \\ srw_tac[][] \\ pop_assum mp_tac
  \\ blastLib.BBLAST_TAC \\ simp[]
  \\ blastLib.BBLAST_TAC \\ srw_tac[][]
  \\ match_mp_tac lsl_lsr
  \\ simp[]
  \\ Cases_on`n`\\full_simp_tac(srw_ss())[word_lsl_n2w]
  \\ full_simp_tac(srw_ss())[dimword_def]);

(* ---- *)

val good_syntax_def = Define `
  (good_syntax (Alloc v) <=> (v = 1)) /\
  (good_syntax ((Seq p1 p2):'a stackLang$prog) <=>
     good_syntax p1 /\ good_syntax p2) /\
  (good_syntax ((If c r ri p1 p2):'a stackLang$prog) <=>
     good_syntax p1 /\ good_syntax p2) /\
  (good_syntax (While c r ri p1) <=>
     good_syntax p1) /\
  (good_syntax (Call x1 _ x2) <=>
     (case x1 of | SOME (y,r,_,_) => good_syntax y | NONE => T) /\
     (case x2 of SOME (y,_,_) => good_syntax y | NONE => T)) /\
  (good_syntax _ <=> T)`

val get_var_imm_case = prove(
  ``get_var_imm ri s =
    case ri of
    | Reg n => get_var n s
    | Imm w => SOME (Word w)``,
  Cases_on `ri` \\ full_simp_tac(srw_ss())[get_var_imm_def]);

val prog_comp_lemma = prove(
  ``prog_comp = \(n,p). (n,FST (comp n (next_lab p) p))``,
  full_simp_tac(srw_ss())[FUN_EQ_THM,FORALL_PROD,prog_comp_def]);

val lookup_IMP_lookup_compile = prove(
  ``lookup dest s.code = SOME x /\ 30 <= dest ==>
    ?m1 n1. lookup dest (fromAList (compile c (toAList s.code))) =
            SOME (FST (comp m1 n1 x))``,
  full_simp_tac(srw_ss())[lookup_fromAList,compile_def] \\ srw_tac[][ALOOKUP_APPEND]
  \\ `ALOOKUP (stubs c) dest = NONE` by
    (full_simp_tac(srw_ss())[stubs_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ decide_tac) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[prog_comp_lemma] \\ full_simp_tac(srw_ss())[ALOOKUP_MAP_gen,ALOOKUP_toAList]
  \\ metis_tac []);

val word_gc_fun_lemma = word_gc_fun_def
  |> SIMP_RULE std_ss [word_full_gc_def]
  |> SIMP_RULE std_ss [Once LET_THM]
  |> SIMP_RULE std_ss [Once LET_THM]
  |> SIMP_RULE std_ss [Once LET_THM]
  |> SIMP_RULE std_ss [Once LET_THM]
  |> SIMP_RULE std_ss [Once LET_THM,word_gc_move_roots_def]

val word_gc_fun_thm = prove(
  ``word_gc_fun conf (roots,m,dm,s) =
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
             (EndOfHeap,
              Word
                (theWord (s ' OtherHeap) +
                 theWord (s ' HeapLength))); (Globals,w1)]
      in
        if c2 then SOME (ws2,m1,s1) else NONE``,
  full_simp_tac(srw_ss())[word_gc_fun_lemma,LET_THM]
  \\ rpt (split_pair_tac \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[])
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]);

val gc_lemma = gc_def
  |> SPEC_ALL
  |> DISCH ``s.gc_fun = word_gc_fun conf``
  |> SIMP_RULE std_ss [] |> UNDISCH
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

val word_gc_move_loop_F = store_thm("word_gc_move_loop_F",
  ``!k conf pb i pa old m dm i1 pa1 m1 c1.
      word_gc_move_loop k conf (pb,i,pa,old,m,dm,F) = (i1,pa1,m1,c1) ==> ~c1``,
  Induct \\ once_rewrite_tac [word_gc_move_loop_def] \\ fs [] \\ rw []
  \\ split_pair_tac \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ split_pair_tac \\ fs []);

val word_gc_move_loop_ok = store_thm("word_gc_move_loop_ok",
  ``word_gc_move_loop k conf (pb,i,pa,old,m,dm,c) = (i1,pa1,m1,c1) ==> c1 ==> c``,
  Cases_on `c` \\ fs [] \\ rw [] \\ imp_res_tac word_gc_move_loop_F \\ fs []);

val gc_thm = prove(
  ``s.gc_fun = word_gc_fun conf ⇒
   gc (s:('a,'b)stackSem$state) =
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
            (EndOfHeap,
             Word
               (theWord (s.store ' OtherHeap) +
                theWord (s.store ' HeapLength)));
            (Globals,w1)] in
       if c2 then SOME (s with
                       <|stack := unused ++ stack; store := s1;
                         regs := FEMPTY; memory := m1|>) else NONE``,
  strip_tac \\ drule gc_lemma
  \\ disch_then (fn th => full_simp_tac(srw_ss())[th])
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[LET_THM,word_gc_move_roots_bitmaps_def]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  THEN1
   (rpt (split_pair_tac \\ full_simp_tac(srw_ss())[]
    \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[])
    \\ imp_res_tac word_gc_move_loop_F)
  \\ rpt (split_pair_tac \\ full_simp_tac(srw_ss())[]
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

val word_gc_move_roots_APPEND = prove(
  ``!xs ys i1 pa1 m.
      word_gc_move_roots conf (xs++ys,i1,pa1,curr,m,dm) =
        let (ws1,i1,pa1,m1,c1) = word_gc_move_roots conf (xs,i1,pa1,curr,m,dm) in
        let (ws2,i2,pa2,m2,c2) = word_gc_move_roots conf (ys,i1,pa1,curr,m1,dm) in
          (ws1++ws2,i2,pa2,m2,c1 /\ c2)``,
  Induct \\ full_simp_tac(srw_ss())[word_gc_move_roots_def,LET_THM]
  \\ srw_tac[][] \\ split_pair_tac \\ full_simp_tac(srw_ss())[]
  \\ split_pair_tac \\ fs[]
  \\ split_pair_tac \\ fs[]
  \\ split_pair_tac \\ fs[]
  \\ EQ_TAC \\ fs[] \\ rw[]);

val map_bitmap_APPEND = prove(
  ``!x q stack p0 p1.
      filter_bitmap x stack = SOME (p0,p1) /\
      LENGTH q = LENGTH p0 ==>
      map_bitmap x (q ++ q') stack =
      case map_bitmap x q stack of
      | NONE => NONE
      | SOME (hd,ts,ws) => SOME (hd,ts++q',ws)``,
  Induct \\ full_simp_tac(srw_ss())[map_bitmap_def]
  \\ reverse (Cases \\ Cases_on `stack`)
  \\ full_simp_tac(srw_ss())[map_bitmap_def,filter_bitmap_def]
  THEN1 (srw_tac[][] \\ rpt (CASE_TAC \\ full_simp_tac(srw_ss())[]))
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ Cases \\ full_simp_tac(srw_ss())[map_bitmap_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]);

val word_gc_move_roots_IMP_LENGTH = store_thm("word_gc_move_roots_IMP_LENGTH",
  ``!xs r0 r1 curr r2 dm ys i2 pa2 m2 c conf.
      word_gc_move_roots conf (xs,r0,r1,curr,r2,dm) = (ys,i2,pa2,m2,c) ==>
      LENGTH ys = LENGTH xs``,
  Induct \\ full_simp_tac(srw_ss())[word_gc_move_roots_def,LET_THM] \\ srw_tac[][]
  \\ rpt (split_pair_tac \\ full_simp_tac(srw_ss())[])
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[] \\ res_tac);

val filter_bitmap_map_bitmap = store_thm("filter_bitmap_map_bitmap",
  ``!x t q xs xs1 z ys ys1.
      filter_bitmap x t = SOME (xs,xs1) /\
      LENGTH q = LENGTH xs /\
      map_bitmap x q t = SOME (ys,z,ys1) ==>
      z = [] /\ ys1 = xs1``,
  Induct
  THEN1 (Cases_on `q` \\ Cases_on `t`
         \\ full_simp_tac(srw_ss())[filter_bitmap_def,map_bitmap_def])
  \\ Cases_on `t` \\ Cases_on `q` \\ Cases
  \\ rewrite_tac [filter_bitmap_def] \\ simp_tac std_ss [map_bitmap_def]
  THEN1
   (Cases_on `xs` \\ simp_tac std_ss [map_bitmap_def,LENGTH,ADD1]
    \\ CASE_TAC \\ qcase_tac `_ = SOME y` \\ PairCases_on `y`
    \\ simp_tac (srw_ss()) [map_bitmap_def,LENGTH,ADD1]
    \\ ntac 2 strip_tac \\ first_x_assum drule
    \\ disch_then (qspec_then `[]` mp_tac) \\ full_simp_tac(srw_ss())[])
  THEN1
   (CASE_TAC \\ qcase_tac `_ = SOME y` \\ PairCases_on `y`
    \\ simp_tac (srw_ss()) [map_bitmap_def,LENGTH,ADD1]
    \\ CASE_TAC \\ qcase_tac `_ = SOME y` \\ PairCases_on `y`
    \\ simp_tac (srw_ss()) [map_bitmap_def,LENGTH,ADD1]
    \\ metis_tac [])
  \\ CASE_TAC \\ qcase_tac `_ = SOME y` \\ PairCases_on `y`
  \\ simp_tac (srw_ss()) []
  \\ rpt gen_tac \\ strip_tac
  \\ first_x_assum match_mp_tac
  \\ qexists_tac `t'` \\ full_simp_tac(srw_ss())[]
  \\ qexists_tac `h'::t` \\ full_simp_tac(srw_ss())[]);

val word_gc_move_roots_bitmaps = prove(
  ``!stack i1 pa1 m stack2 i2 pa2 m2.
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
                  (w::new++stack,i,pa,m,c2 /\ c3)``,
  Cases THEN1 (full_simp_tac(srw_ss())[word_gc_move_roots_bitmaps_def,
                 enc_stack_def])
  \\ rpt strip_tac \\ pop_assum mp_tac \\ full_simp_tac(srw_ss())[]
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  THEN1 (full_simp_tac(srw_ss())[word_gc_move_roots_bitmaps_def,enc_stack_def]
         \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[word_gc_move_roots_def,LET_THM,dec_stack_def])
  \\ full_simp_tac(srw_ss())[word_gc_move_roots_bitmaps_def,word_gc_move_bitmaps_def,enc_stack_def]
  \\ Cases_on `full_read_bitmap bitmaps h` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `filter_bitmap x t` \\ full_simp_tac(srw_ss())[]
  \\ qcase_tac `_ = SOME filter_res` \\ PairCases_on `filter_res` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `enc_stack bitmaps filter_res1` \\ full_simp_tac(srw_ss())[]
  \\ qcase_tac `_ = SOME enc_rest` \\ full_simp_tac(srw_ss())[word_gc_move_roots_APPEND]
  \\ simp [Once LET_DEF]
  \\ Cases_on `word_gc_move_roots conf (filter_res0,i1,pa1,curr,m,dm)` \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `r` \\ full_simp_tac(srw_ss())[dec_stack_def]
  \\ Cases_on `word_gc_move_roots conf (enc_rest,r0,r1,curr,r2,dm)` \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `r` \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ qcase_tac `_ = SOME map_rest` \\ full_simp_tac(srw_ss())[]
  \\ PairCases_on `map_rest` \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac word_gc_move_roots_IMP_LENGTH \\ full_simp_tac(srw_ss())[]
  \\ drule (GEN_ALL map_bitmap_APPEND) \\ full_simp_tac(srw_ss())[]
  \\ disch_then (mp_tac o SPEC_ALL) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[] \\ pop_assum kall_tac
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ qcase_tac `_ = SOME z` \\ full_simp_tac(srw_ss())[] \\ PairCases_on `z` \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac word_gc_move_roots_IMP_LENGTH \\ full_simp_tac(srw_ss())[]
  \\ drule filter_bitmap_map_bitmap
  \\ disch_then drule \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]);

val get_bits_def = Define `
  get_bits w = GENLIST (\i. w ' i) (bit_length w − 1)`

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

val bit_length_thm = store_thm("bit_length_thm",
  ``!w. ((w >>> bit_length w) = 0w) /\ !n. n < bit_length w ==> (w >>> n) <> 0w``,
  HO_MATCH_MP_TAC bit_length_ind \\ srw_tac[][]
  \\ once_rewrite_tac [bit_length_def]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
  \\ Cases_on `w = 0w` \\ full_simp_tac(srw_ss())[EVAL ``bit_length 0w``]
  \\ Cases_on `n` \\ full_simp_tac(srw_ss())[]
  \\ ntac 2 (pop_assum mp_tac)
  \\ once_rewrite_tac [bit_length_def]
  \\ full_simp_tac(srw_ss())[ADD1] \\ srw_tac[][]);

val word_lsr_dimindex = prove(
  ``(w:'a word) >>> dimindex (:'a) = 0w``,
  full_simp_tac(srw_ss())[]);

val bit_length_LESS_EQ_dimindex = store_thm("bit_length_LESS_EQ_dimindex",
  ``bit_length (w:'a word) <= dimindex (:'a)``,
  CCONTR_TAC \\ full_simp_tac(srw_ss())[GSYM NOT_LESS]
  \\ imp_res_tac bit_length_thm
  \\ full_simp_tac(srw_ss())[word_lsr_dimindex]);

val shift_to_zero_word_msb = store_thm("shift_to_zero_word_msb",
  ``(w:'a word) >>> n = 0w /\ word_msb w ==> dimindex (:'a) <= n``,
  srw_tac [wordsLib.WORD_BIT_EQ_ss] []
  \\ CCONTR_TAC
  \\ qpat_assum `!xx.bb` mp_tac
  \\ fs [GSYM NOT_LESS]
  \\ qexists_tac `dimindex (:α) - 1 - n`
  \\ simp [])

val word_msb_IMP_bit_length = prove(
  ``!h. word_msb (h:'a word) ==> (bit_length h = dimindex (:'a))``,
  srw_tac[][] \\ imp_res_tac shift_to_zero_word_msb \\ CCONTR_TAC
  \\ imp_res_tac (DECIDE ``n<>m ==> n < m \/ m < n:num``)
  \\ qspec_then `h` mp_tac bit_length_thm
  \\ strip_tac \\ res_tac \\ full_simp_tac(srw_ss())[word_lsr_dimindex]
  \\ decide_tac);

val get_bits_intro = prove(
  ``word_msb (h:'a word) ==>
    GENLIST (\i. h ' i) (dimindex (:'a) - 1) = get_bits h``,
  full_simp_tac(srw_ss())[get_bits_def,word_msb_IMP_bit_length]);

val DROP_IMP_LESS_LENGTH = prove(
  ``!xs n y ys. DROP n xs = y::ys ==> n < LENGTH xs``,
  Induct \\ full_simp_tac(srw_ss())[DROP_def] \\ srw_tac[][]
  \\ res_tac \\ decide_tac);

val DROP_EQ_CONS_IMP_DROP_SUC = prove(
  ``!xs n y ys. DROP n xs = y::ys ==> DROP (SUC n) xs = ys``,
  Induct \\ full_simp_tac(srw_ss())[DROP_def] \\ srw_tac[][]
  \\ res_tac \\ full_simp_tac(srw_ss())[ADD1]
  \\ `n - 1 + 1 = n` by decide_tac \\ full_simp_tac(srw_ss())[]);

val filter_bitmap_APPEND = prove(
  ``!xs stack ys.
      filter_bitmap (xs ++ ys) stack =
      case filter_bitmap xs stack of
      | NONE => NONE
      | SOME (zs,rs) =>
        case filter_bitmap ys rs of
        | NONE => NONE
        | SOME (zs2,rs) => SOME (zs ++ zs2,rs)``,
  Induct \\ Cases_on `stack` \\ full_simp_tac(srw_ss())[filter_bitmap_def]
  THEN1 (srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  THEN1 (srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ Cases \\ full_simp_tac(srw_ss())[filter_bitmap_def] \\ srw_tac[][]
  \\ rpt (CASE_TAC \\ full_simp_tac(srw_ss())[]));

val map_bitmap_APPEND_APPEND = prove(
  ``!vs1 stack x0 x1 ws2 vs2 ws1.
      filter_bitmap vs1 stack = SOME (x0,x1) /\
      LENGTH x0 = LENGTH ws1 ==>
      map_bitmap (vs1 ++ vs2) (ws1 ++ ws2) stack =
      case map_bitmap vs1 ws1 stack of
      | NONE => NONE
      | SOME (ts1,ts2,ts3) =>
        case map_bitmap vs2 ws2 ts3 of
        | NONE => NONE
        | SOME (us1,us2,us3) => SOME (ts1++us1,ts2++us2,us3)``,
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

val word_gc_move_bitmaps_unroll = prove(
  ``word_gc_move_bitmaps conf (Word w,stack,bitmaps,i1,pa1,curr,m,dm) = SOME x /\
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
                SOME (hd++hd3,ws3,i3,pa3,m3,c2 /\ c3)``,
  full_simp_tac(srw_ss())[word_gc_move_bitmaps_def,full_read_bitmap_def]
  \\ Cases_on `w = 0w` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `DROP (w2n (w + -1w)) bitmaps`
  \\ full_simp_tac(srw_ss())[read_bitmap_def]
  \\ reverse (Cases_on `word_msb h`)
  THEN1
   (full_simp_tac(srw_ss())[word_gc_move_bitmap_def,get_bits_def,LET_THM]
    \\ CASE_TAC \\ qcase_tac `_ = SOME y` \\ PairCases_on `y`
    \\ full_simp_tac(srw_ss())[]
    \\ split_pair_tac \\ full_simp_tac(srw_ss())[]
    \\ CASE_TAC \\ qcase_tac `_ = SOME y` \\ PairCases_on `y`
    \\ full_simp_tac(srw_ss())[]
    \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[] \\ Cases_on `read_bitmap t`
  \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ qcase_tac `_ = SOME y`
  \\ PairCases_on `y` \\ full_simp_tac(srw_ss())[LET_THM]
  \\ split_pair_tac \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ qcase_tac `_ = SOME z`
  \\ PairCases_on `z` \\ full_simp_tac(srw_ss())[LET_THM]
  \\ full_simp_tac(srw_ss())[word_gc_move_bitmap_def,LET_THM] \\ rev_full_simp_tac(srw_ss())[get_bits_intro]
  \\ strip_tac \\ rpt var_eq_tac
  \\ IF_CASES_TAC THEN1
   (`F` by all_tac
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
  \\ split_pair_tac \\ full_simp_tac(srw_ss())[]
  \\ split_pair_tac \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ qpat_assum `filter_bitmap (get_bits h) stack = SOME (x0,x1)` assume_tac
  \\ drule (map_bitmap_APPEND_APPEND |> GEN_ALL)
  \\ `LENGTH x0 = LENGTH ws1` by (imp_res_tac word_gc_move_roots_IMP_LENGTH \\ full_simp_tac(srw_ss())[])
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

val bit_length_minus_1 = store_thm("bit_length_minus_1",
  ``w <> 0w ==> bit_length w − 1 = bit_length (w >>> 1)``,
  simp [Once bit_length_def]);

val bit_length_eq_1 = store_thm("bit_length_eq_1",
  ``bit_length w = 1 <=> w = 1w``,
  Cases_on `w = 1w` \\ full_simp_tac(srw_ss())[] THEN1 (EVAL_TAC \\ full_simp_tac(srw_ss())[])
  \\ once_rewrite_tac [bit_length_def] \\ srw_tac[][]
  \\ once_rewrite_tac [bit_length_def] \\ srw_tac[][]
  \\ pop_assum mp_tac
  \\ simp_tac std_ss [GSYM w2n_11,w2n_lsr]
  \\ Cases_on `w` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `n` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `n'` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[DIV_EQ_X] \\ decide_tac);

val word_and_one_eq_0_iff = store_thm("word_and_one_eq_0_iff",
  ``!w. ((w && 1w) = 0w) <=> ~(w ' 0)``,
  srw_tac [wordsLib.WORD_BIT_EQ_ss] [wordsTheory.word_index])

val word_gc_move_bitmap_unroll = prove(
  ``word_gc_move_bitmap conf (w,stack,i1,pa1,curr,m,dm) =
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
          | SOME (new,stack,i1,pa1,m,c) => SOME (x1::new,stack,i1,pa1,m,c1 /\ c)``,
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
    \\ split_pair_tac \\ full_simp_tac(srw_ss())[]
    \\ rpt (CASE_TAC \\ full_simp_tac(srw_ss())[]))
  \\ full_simp_tac(srw_ss())[word_gc_move_bitmap_def,LET_THM]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] THEN1 (split_pair_tac \\ full_simp_tac(srw_ss())[])
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[word_gc_move_roots_def,LET_THM]
  \\ ntac 3 (split_pair_tac \\ full_simp_tac(srw_ss())[]) \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[map_bitmap_def]
  \\ rpt (CASE_TAC \\ full_simp_tac(srw_ss())[]));

val split_num_forall_to_10 = prove(
  ``($! P) <=> P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5 /\
               P 6 /\ P 7 /\ P 8 /\ P 9 /\ !x. 9 < x ==> P (x:num)``,
  full_simp_tac(srw_ss())[GSYM (RAND_CONV ETA_CONV ``!x. P x``)]
  \\ eq_tac \\ srw_tac[][]
  \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
  \\ ntac 5 (Cases_on `n` \\ full_simp_tac(srw_ss())[] \\ Cases_on `n'` \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[ADD1,GSYM ADD_ASSOC]
  \\ pop_assum match_mp_tac \\ decide_tac);

val nine_less = DECIDE
  ``9 < n ==> n <> 0 /\ n <> 1 /\ n <> 2 /\ n <> 3 /\ n <> 4 /\
              n <> 5 /\ n <> 6 /\ n <> 7 /\ n <> 8 /\ n <> 9n``

val word_shift_not_0 = store_thm("word_shift_not_0",
  ``word_shift (:'a) <> 0``,
  srw_tac[][stackLangTheory.word_shift_def] \\ full_simp_tac(srw_ss())[]);

val tac = simp [list_Seq_def,evaluate_def,inst_def,word_exp_def,get_var_def,
       wordLangTheory.word_op_def,mem_load_def,assign_def,set_var_def,
       FLOOKUP_UPDATE,mem_store_def,dec_clock_def,get_var_imm_def,
       asmSemTheory.word_cmp_def,wordLangTheory.num_exp_def,
       labSemTheory.word_cmp_def,GREATER_EQ,GSYM NOT_LESS,FUPDATE_LIST,
       wordSemTheory.word_sh_def,word_shift_not_0,FLOOKUP_UPDATE]

val memcpy_code_thm = prove(
  ``!n a b m dm b1 m1 s.
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
                                              (3,Word b1)] |>)``,
  Induct THEN1
   (simp [Once memcpy_def]
    \\ srw_tac[][] \\ full_simp_tac(srw_ss())[memcpy_code_def,evaluate_def,get_var_def,get_var_imm_def]
    \\ full_simp_tac(srw_ss())[EVAL ``word_cmp NotEqual 0w 0w``]
    \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ full_simp_tac(srw_ss())[FUPDATE_LIST,GSYM fmap_EQ,FLOOKUP_DEF,EXTENSION,
           FUN_EQ_THM,FAPPLY_FUPDATE_THM]
    \\ once_rewrite_tac [split_num_forall_to_10] \\ full_simp_tac(srw_ss())[nine_less])
  \\ simp [Once memcpy_def]
  \\ rpt gen_tac \\ strip_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[ADD1,GSYM word_add_n2w]
  \\ split_pair_tac \\ full_simp_tac(srw_ss())[] \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ simp [memcpy_code_def,evaluate_def,get_var_def,get_var_imm_def]
  \\ full_simp_tac(srw_ss())[labSemTheory.word_cmp_def,asmSemTheory.word_cmp_def,word_add_n2w,get_var_def]
  \\ tac
  \\ qpat_abbrev_tac `s3 = s with <| regs := _ ; memory := _; clock := _ |>`
  \\ `memcpy ((n2w n):'a word) (a + bytes_in_word) (b + bytes_in_word)
         (s3 with clock := s3.clock - n).memory
         (s3 with clock := s3.clock - n).mdomain = (b1,m1,T)` by
       (unabbrev_all_tac \\ full_simp_tac(srw_ss())[])
  \\ first_x_assum drule \\ full_simp_tac(srw_ss())[]
  \\ discharge_hyps THEN1
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

val memcpy_code_thm = store_thm("memcpy_code_thm",
  ``!w a b m dm b1 m1 s.
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
                                              (3,Word b1)] |>)``,
  Cases \\ full_simp_tac(srw_ss())[] \\ pop_assum mp_tac \\ qspec_tac (`n`,`n`) \\ full_simp_tac(srw_ss())[PULL_FORALL]
  \\ rpt strip_tac
  \\ match_mp_tac (memcpy_code_thm |> SIMP_RULE (srw_ss()) [])
  \\ metis_tac [])

val select_lower_lemma = store_thm("select_lower_lemma",
  ``(n -- 0) w = ((w:'a word) << (dimindex(:'a)-n-1)) >>> (dimindex(:'a)-n-1)``,
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [wordsTheory.word_index]
  \\ Cases_on `i + (dimindex (:α) - n - 1) < dimindex (:α)`
  \\ fs []
  )

val select_eq_select_0 = store_thm("select_eq_select_0",
  ``k <= n ==> (n -- k) w = (n - k -- 0) (w >>> k)``,
  srw_tac [wordsLib.WORD_BIT_EQ_ss] [] \\ eq_tac \\ rw [])

val is_fwd_ptr_iff = prove(
  ``!w. is_fwd_ptr w <=> ?v. w = Word v /\ (v && 3w) = 0w``,
  Cases \\ full_simp_tac(srw_ss())[is_fwd_ptr_def]);

val isWord_thm = prove(
  ``!w. isWord w = ?v. w = Word v``,
  Cases \\ full_simp_tac(srw_ss())[isWord_def]);

val word_gc_move_code_thm = store_thm("word_gc_move_code_thm",
  ``word_gc_move conf (w,i,pa,old,m,dm) = (w1,i1,pa1,m1,T) /\
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
                                            (6,r6)] |>)``,
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
  \\ split_pair_tac \\ full_simp_tac(srw_ss())[ptr_to_addr_def,isWord_thm]
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
  \\ full_simp_tac(srw_ss())[] \\ discharge_hyps THEN1
    (unabbrev_all_tac \\ full_simp_tac(srw_ss())[get_var_def] \\ tac
     \\ fs [bvp_to_wordPropsTheory.decode_length_def])
  \\ strip_tac \\ full_simp_tac(srw_ss())[FUPDATE_LIST]
  \\ unabbrev_all_tac \\ full_simp_tac(srw_ss())[] \\ tac
  \\ fs [LET_THM,bvp_to_wordPropsTheory.decode_length_def]
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
        DECIDE ``n<>0 ==> m-(n-1)-1=m-n:num``]);

val word_gc_move_list_code_thm = store_thm("word_gc_move_code_thm",
  ``!l a (s:('a,'b)stackSem$state) pa1 pa old m1 m i1 i dm conf a1.
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
                                              (8,Word a1)] |>)``,
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
  \\ qpat_assum `_ = (a1,i1,pa1,m1,T)` mp_tac
  \\ `n2w (SUC n) + -1w = n2w n` by fs [ADD1,GSYM word_add_n2w]
  \\ split_pair_tac \\ simp []
  \\ split_pair_tac \\ simp []
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
  \\ `FLOOKUP ((s:('a,'b)stackSem$state) with
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
  \\ rpt (discharge_hyps THEN1 (fs [] \\ tac)) \\ fs []
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
  \\ full_simp_tac(srw_ss())[nine_less])

val word_gc_move_loop_code_thm = prove(
  ``!k pb1 i1 pa1 old1 m1 dm1 c1 i2 pa2 m2 (s:('a,'b)stackSem$state).
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
                                              (8,Word pa2)] |>)``,
  strip_tac \\ completeInduct_on `k` \\ rpt strip_tac
  \\ qpat_assum `word_gc_move_loop _ _ _ = _` mp_tac
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
  \\ split_pair_tac \\ fs []
  \\ Cases_on `word_bit 3 (theWord (s.memory pb1))`
  \\ fs [word_bit_test] THEN1
   (strip_tac
    \\ drule word_gc_move_loop_ok \\ fs [] \\ strip_tac \\ fs []
    \\ asm_simp_tac std_ss[word_gc_move_loop_code_def,evaluate_def]
    \\ asm_simp_tac std_ss[GSYM word_gc_move_loop_code_def,STOP_def]
    \\ fs [get_var_def,isWord_thm,clear_top_inst_def] \\ tac
    \\ rev_full_simp_tac(srw_ss())
         [bvp_to_wordPropsTheory.decode_length_def,LET_THM] \\ rpt var_eq_tac
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
    \\ fs [AND_IMP_INTRO] \\ discharge_hyps
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
         [bvp_to_wordPropsTheory.decode_length_def,LET_THM] \\ rpt var_eq_tac
  \\ qabbrev_tac `s5 = s with
        <|regs :=
            s.regs |+ (7,Word v) |+
            (7,Word (v ⋙ (dimindex (:'a) − conf.len_size))) |+
            (8,Word (pb1 + bytes_in_word)) |>`
  \\ drule word_gc_move_list_code_thm
  \\ disch_then (qspec_then `s5` mp_tac)
  \\ fs [AND_IMP_INTRO] \\ discharge_hyps
  THEN1 (unabbrev_all_tac \\ fs [FLOOKUP_UPDATE,get_var_def])
  \\ strip_tac \\ fs [GSYM CONJ_ASSOC]
  \\ pop_assum mp_tac
  \\ qpat_abbrev_tac `s6 = s5 with <|regs := _ ; memory := _ |>`
  \\ `s.mdomain = s6.mdomain /\ m1 = s6.memory` by (unabbrev_all_tac \\ fs [])
  \\ qpat_assum `Abbrev _` assume_tac
  \\ fs [] \\ qpat_assum `_ = _` kall_tac
  \\ first_x_assum drule \\ discharge_hyps
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

val lower_2w_eq = prove(
  ``!w:'a word. good_dimindex (:'a) ==> (w <+ 2w <=> w = 0w \/ w = 1w)``,
  Cases \\ fs [labPropsTheory.good_dimindex_def,WORD_LO,dimword_def]
  \\ rw [] \\ rw []);

val EL_LENGTH_ADD_LEMMA = prove(
  ``EL (LENGTH init + LENGTH old) (init ++ old ++ [x] ++ st1) = x``,
  mp_tac (EL_LENGTH_APPEND |> Q.SPECL [`[x] ++ st1`,`init++old`])
  \\ fs []);

val LUPDATE_LENGTH_ADD_LEMMA = prove(
  ``LUPDATE w (LENGTH init + LENGTH old) (init ++ old ++ [x] ++ st1) =
       init ++ old ++ [w] ++ st1``,
  mp_tac (LUPDATE_LENGTH |> Q.SPECL [`init++old`]) \\ fs []);

val bytes_in_word_word_shift_n2w = store_thm("bytes_in_word_word_shift_n2w",
  ``good_dimindex (:α) ∧ (dimindex(:'a) DIV 8) * n < dimword (:α) ⇒
    (bytes_in_word * n2w n) ⋙ word_shift (:α) = (n2w n):'a word``,
  strip_tac \\ match_mp_tac bytes_in_word_word_shift
  \\ fs [bytes_in_word_def]
  \\ `(dimindex (:α) DIV 8) < dimword (:α) /\ n < dimword (:α)` by
       (rfs [labPropsTheory.good_dimindex_def,dimword_def] \\ rfs [])
  \\ fs []);

val word_gc_move_bitmap_code_thm = store_thm("word_gc_move_bitmap_code_thm",
  ``!w stack (s:('a,'b)stackSem$state) i pa curr m dm new stack1 a1 i1 pa1 m1 old.
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
                      (8,Word (bytes_in_word * n2w (LENGTH (old ++ new))))] |>)``,
  recInduct bit_length_ind \\ rpt strip_tac \\ fs []
  \\ qpat_assum `word_gc_move_bitmap _ _ = _` mp_tac
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
    \\ qcase_tac `_ = SOME (new1,st1,i1,pa1,m1,T)`
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
    \\ discharge_hyps
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
  \\ split_pair_tac \\ fs []
  \\ every_case_tac \\ strip_tac \\ rpt var_eq_tac
  \\ qcase_tac `_ = SOME (new1,st1,i1,pa1,m1,T)`
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
    (`F` by all_tac \\ fs []
     \\ pop_assum mp_tac \\ fs [] \\ AP_TERM_TAC
     \\ match_mp_tac (bytes_in_word_word_shift_n2w |> GEN_ALL) \\ fs []
     \\ rfs [labPropsTheory.good_dimindex_def,dimword_def] \\ rfs [])
  \\ fs [] \\ tac \\ fs [EL_LENGTH_ADD_LEMMA]
  \\ qabbrev_tac `s4 = s with <|regs := s.regs |+ (5,h) |+ (7,Word (w ⋙ 1)) |>`
  \\ `s.memory = s4.memory /\ s.mdomain = s4.mdomain` by
           (unabbrev_all_tac \\ fs []) \\ fs []
  \\ drule (word_gc_move_code_thm |> GEN_ALL |> SIMP_RULE std_ss [])
  \\ discharge_hyps THEN1 (unabbrev_all_tac \\ fs [get_var_def,FLOOKUP_UPDATE])
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
  \\ discharge_hyps THEN1
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
  \\ full_simp_tac(srw_ss())[nine_less] \\ fs [])

val DROP_IMP_EL = store_thm("DROP_IMP_EL",
  ``!xs n h t. DROP n xs = h::t ==> (EL n xs = h)``,
  Induct \\ fs [DROP_def] \\ Cases_on `n` \\ fs []);

val word_msb_IFF_lsr_EQ_0 = store_thm("word_msb_IFF_lsr_EQ_0",
  ``word_msb h <=> (h >>> (dimindex (:'a) - 1) <> 0w:'a word)``,
  srw_tac [wordsLib.WORD_BIT_EQ_ss] [])

val map_bitmap_IMP_LENGTH = store_thm("map_bitmap_IMP_LENGTH",
  ``!x wl stack xs ys.
      map_bitmap x wl stack = SOME (xs,ys) ==>
      LENGTH xs = LENGTH x``,
  recInduct map_bitmap_ind \\ fs [map_bitmap_def]
  \\ rw [] \\ res_tac \\ fs []
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []);

val filter_bitmap_IMP_LENGTH = store_thm("filter_bitmap_IMP_LENGTH",
  ``!x stack q r.
      filter_bitmap x stack = SOME (q,r) ==>
      LENGTH stack = LENGTH x + LENGTH r``,
  recInduct filter_bitmap_ind \\ fs [filter_bitmap_def]
  \\ rw [] \\ res_tac \\ fs []
  \\ every_case_tac \\ fs []);

val word_gc_move_bitmaps_LENGTH = store_thm("word_gc_move_bitmaps_LENGTH",
  ``word_gc_move_bitmaps conf (w,stack,bitmaps,i,pa,curr,m,dm) =
       SOME (xs,stack1,i1,pa1,m1,T) ==>
    LENGTH stack = LENGTH xs + LENGTH stack1``,
  fs [word_gc_move_bitmaps_def]
  \\ every_case_tac \\ fs [] \\ split_pair_tac \\ fs []
  \\ every_case_tac \\ fs [] \\ rw []
  \\ imp_res_tac map_bitmap_IMP_LENGTH \\ fs []
  \\ imp_res_tac filter_bitmap_IMP_LENGTH \\ fs []);

val word_gc_move_bitmaps_code_thm = store_thm("word_gc_move_bitmap_code_thm",
  ``!w bitmaps z stack (s:('a,'b)stackSem$state) i pa curr m dm new
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
                                              (9,r9)] |>)``,
  ntac 2 strip_tac \\ completeInduct_on `LENGTH bitmaps - w2n (w - 1w)`
  \\ rpt strip_tac \\ fs [] \\ rpt var_eq_tac \\ fs [PULL_FORALL]
  \\ qpat_assum `word_gc_move_bitmaps _ _ = _`
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
  \\ discharge_hyps
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
  \\ qcase_tac `_ = SOME y` \\ PairCases_on `y` \\ fs []
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
  \\ discharge_hyps THEN1
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
  \\ full_simp_tac(srw_ss())[nine_less] \\ fs [])

val EL_LENGTH_ADD_LEMMA = prove(
  ``!n xs y ys. LENGTH xs = n ==> EL n (xs ++ y::ys) = y``,
  fs [EL_LENGTH_APPEND]);

val word_gc_move_roots_bitmaps_code_thm =
        store_thm("word_gc_move_roots_bitmaps_code_thm",
  ``!bitmaps (s:('a,'b)stackSem$state) i pa curr m dm new
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
                                              (9,Word 0w)] |>)``,
  completeInduct_on `LENGTH stack`
  \\ rpt strip_tac \\ fs [PULL_FORALL]
  \\ rpt var_eq_tac \\ fs []
  \\ qpat_assum `word_gc_move_roots_bitmaps _ _ = _`
        (fn th => assume_tac th \\ mp_tac th)
  \\ drule (GEN_ALL word_gc_move_roots_bitmaps) \\ fs []
  \\ Cases_on `stack` \\ fs []
  \\ qcase_tac `word_gc_move_roots_bitmaps conf (hd::stack,_) = _`
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
  \\ split_pair_tac \\ fs []
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
  \\ discharge_hyps THEN1
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
  \\ discharge_hyps THEN1
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
  \\ full_simp_tac(srw_ss())[nine_less] \\ fs [])

fun abbrev_under_exists tm tac =
  (fn state => (`?^(tm). ^(hd (fst (hd (fst (tac state)))))` by
        (fs [markerTheory.Abbrev_def] \\ NO_TAC)) state)

val alloc_correct = store_thm("alloc_correct",
  ``alloc w (s:('a,'b)stackSem$state) = (r,t) /\ r <> SOME Error /\
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
              clock := s.clock + ck; regs := l;
              code := fromAList (compile c (toAList s.code))|>) =
        (r,
         t with
           <| use_store := T; use_stack := T; use_alloc := F;
              code := fromAList (compile c (toAList s.code));
              regs := l2 |>) /\
       (r = NONE ==> FLOOKUP l2 0 = SOME ret)``,
  Cases_on `s.gc_fun = word_gc_fun conf` \\ fs [] \\ fs [alloc_def]
  \\ `(set_store AllocSize (Word w) s).gc_fun = word_gc_fun conf` by
        (fs [set_store_def] \\ NO_TAC)
  \\ drule gc_thm \\ fs [] \\ disch_then kall_tac
  \\ fs [set_store_def] \\ IF_CASES_TAC THEN1 (fs [] \\ rw [] \\ fs [])
  \\ fs [FAPPLY_FUPDATE_THM]
  \\ `{Globals; CurrHeap; OtherHeap; HeapLength} SUBSET FDOM s.store /\
      isWord (s.store ' OtherHeap) /\
      isWord (s.store ' CurrHeap) /\
      isWord (s.store ' HeapLength) /\
      good_dimindex (:'a) /\
      conf.len_size + 2 < dimindex (:'a) /\
      shift_length conf < dimindex (:'a) /\
      conf.len_size <> 0` by cheat
  \\ `word_shift (:'a) < dimindex (:'a) /\ 2 < dimindex (:'a) /\
      !w:'a word. w ≪ word_shift (:'a) = w * bytes_in_word` by
   (fs [word_shift_def,bytes_in_word_def,labPropsTheory.good_dimindex_def]
    \\ fs [WORD_MUL_LSL] \\ NO_TAC)
  \\ fs [isWord_thm] \\ fs [theWord_def]
  \\ qcase_tac `s.store ' OtherHeap = Word other`
  \\ qcase_tac `s.store ' CurrHeap = Word curr`
  \\ qcase_tac `s.store ' HeapLength = Word len`
  \\ split_pair_tac \\ fs []
  \\ split_pair_tac \\ fs []
  \\ split_pair_tac \\ fs []
  \\ reverse IF_CASES_TAC \\ fs [] THEN1 rw []
  \\ fs [FLOOKUP_UPDATE,FUPDATE_LIST,has_space_def]
  \\ rpt var_eq_tac \\ strip_tac \\ fs [NOT_LESS]
  \\ fs [word_gc_code_def,list_Seq_def] \\ tac
  \\ fs [set_store_def,FLOOKUP_UPDATE] \\ tac
  \\ fs [FLOOKUP_DEF]
  \\ imp_res_tac word_gc_move_loop_ok
  \\ fs [] \\ rpt var_eq_tac \\ fs []
  \\ abbrev_under_exists ``s3:('a,'b)stackSem$state``
   (qexists_tac `0` \\ fs []
    \\ qpat_abbrev_tac `(s3:('a,'b)stackSem$state) = _`)
  \\ drule (GEN_ALL word_gc_move_code_thm)
  \\ disch_then (qspec_then `s3` mp_tac)
  \\ discharge_hyps THEN1
   (unabbrev_all_tac \\ fs [] \\ tac
    \\ fs [FAPPLY_FUPDATE_THM,FLOOKUP_DEF])
  \\ strip_tac \\ fs []
  \\ `s.stack_space < LENGTH s.stack` by
   (CCONTR_TAC \\ fs [NOT_LESS]
    \\ imp_res_tac DROP_LENGTH_TOO_LONG
    \\ fs [word_gc_move_roots_bitmaps_def,enc_stack_def] \\ NO_TAC)
  \\ abbrev_under_exists ``s4:('a,'b)stackSem$state``
   (qexists_tac `ck` \\ fs []
    \\ unabbrev_all_tac \\ fs [] \\ tac
    \\ fs [FAPPLY_FUPDATE_THM]
    \\ qpat_abbrev_tac `(s4:('a,'b)stackSem$state) = _`)
  \\ qpat_assum `word_gc_move_roots_bitmaps _ _ = _` assume_tac
  \\ drule bvp_to_wordPropsTheory.LESS_EQ_LENGTH
  \\ strip_tac \\ fs []
  \\ `DROP s.stack_space (ys1 ++ ys2) = ys2` by
       metis_tac [DROP_LENGTH_APPEND] \\ fs []
  \\ drule (GEN_ALL word_gc_move_roots_bitmaps_code_thm
           |> REWRITE_RULE [GSYM AND_IMP_INTRO])
  \\ fs [AND_IMP_INTRO]
  \\ disch_then (qspecl_then [`ys1`,`s4`,`[]`] mp_tac)
  \\ discharge_hyps THEN1
    (fs [] \\ unabbrev_all_tac \\ fs [get_var_def,FLOOKUP_UPDATE]
     \\ fs [FLOOKUP_DEF] \\ Cases_on `ys2` \\ fs []
     \\ metis_tac [EL_LENGTH_APPEND,NULL,HD])
  \\ strip_tac \\ fs [FAPPLY_FUPDATE_THM]
  \\ pop_assum mp_tac
  \\ drule (GEN_ALL evaluate_add_clock)
  \\ disch_then (qspec_then `ck'` mp_tac)
  \\ fs [] \\ rpt strip_tac
  \\ abbrev_under_exists ``s5:('a,'b)stackSem$state``
   (qexists_tac `ck+ck'` \\ fs []
    \\ unabbrev_all_tac \\ fs [] \\ tac
    \\ fs [FAPPLY_FUPDATE_THM]
    \\ qpat_abbrev_tac `(s5:('a,'b)stackSem$state) = _`)
  \\ drule (GEN_ALL word_gc_move_loop_code_thm
           |> REWRITE_RULE [GSYM AND_IMP_INTRO])
  \\ fs [AND_IMP_INTRO]
  \\ disch_then (qspec_then `s5` mp_tac)
  \\ discharge_hyps THEN1
    (fs [] \\ unabbrev_all_tac \\ fs [get_var_def,FLOOKUP_UPDATE]
     \\ fs [FLOOKUP_DEF,FDOM_FUPDATE,FUPDATE_LIST,FAPPLY_FUPDATE_THM])
  \\ strip_tac \\ pop_assum mp_tac
  \\ drule (GEN_ALL evaluate_add_clock)
  \\ disch_then (qspec_then `ck''` mp_tac)
  \\ qpat_assum `evaluate _ = _` kall_tac
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
  \\ rpt (qpat_assum `evaluate _ = _` kall_tac)
  \\ qpat_assum `_ = t.store` (fn th => fs [GSYM th])
  \\ `TAKE t.stack_space (ys1 ++ ys2) = ys1` by metis_tac [TAKE_LENGTH_APPEND]
  \\ fs [fmap_EXT,EXTENSION]
  \\ rw [] \\ fs [FAPPLY_FUPDATE_THM]
  \\ rw [] \\ fs [] \\ TRY (eq_tac \\ strip_tac \\ fs [])
  \\ cheat); (* stackLang semantics at end of alloc is wrong w.r.t. stack *)

val alloc_correct = prove(
  ``alloc w s = (r,t) /\ r <> SOME Error /\
    FLOOKUP s.regs 1 = SOME (Word w) ==>
    ?ck. evaluate
          (Call (SOME (Skip,0,n',m)) (INL 10) NONE,
           s with
           <|use_alloc := F; clock := s.clock + ck;
             code := fromAList (compile c (toAList s.code))|>) =
         (r,
          t with
           <|use_alloc := F; code := fromAList (compile c (toAList s.code))|>)``,
  simp[alloc_def,GSYM AND_IMP_INTRO]
  \\ BasicProvers.CASE_TAC \\ simp[]
  \\ BasicProvers.CASE_TAC \\ simp[]
  \\ BasicProvers.CASE_TAC \\ simp[]
  \\ simp[evaluate_def,find_code_def,lookup_fromAList,compile_def,ALOOKUP_APPEND]
  \\ simp[stubs_def]
  \\ cheat (* correctness of (unimplemented) stubs *));

val find_code_IMP_lookup = prove(
  ``find_code dest regs (s:'a num_map) = SOME x ==>
    ?k. lookup k s = SOME x /\
        (find_code dest regs = ((lookup k):'a num_map -> 'a option))``,
  Cases_on `dest` \\ full_simp_tac(srw_ss())[find_code_def,FUN_EQ_THM]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ metis_tac []);

val comp_correct = prove(
  ``!p s r t m n c.
      evaluate (p,s) = (r,t) /\ r <> SOME Error /\ good_syntax p /\
      (!k prog. lookup k s.code = SOME prog ==> 30 <= k /\ good_syntax prog) ==>
      ?ck.
        evaluate (FST (comp n m p),
           s with <| clock := s.clock + ck;
                     code := fromAList (stack_alloc$compile c (toAList s.code));
                     use_alloc := F |>) =
          (r, t with
              <| code := fromAList (stack_alloc$compile c (toAList s.code));
                 use_alloc := F |>)``,
  recInduct evaluate_ind \\ rpt strip_tac
  THEN1 (* Skip *)
   (full_simp_tac(srw_ss())[Once comp_def,evaluate_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[state_component_equality])
  THEN1 (* Halt *)
   (full_simp_tac(srw_ss())[Once comp_def,evaluate_def,get_var_def]
    \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[state_component_equality])
  THEN1 (* Alloc *)
   (full_simp_tac(srw_ss())[evaluate_def,get_var_def]
    \\ full_simp_tac(srw_ss())[Once comp_def,get_var_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[good_syntax_def] \\ srw_tac[][]
    \\ drule alloc_correct \\ full_simp_tac(srw_ss())[])
  THEN1 (* Inst *)
   (full_simp_tac(srw_ss())[Once comp_def] \\ full_simp_tac(srw_ss())[evaluate_def,inst_def]
    \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[assign_def,word_exp_def,set_var_def,mem_load_def,
         get_var_def,mem_store_def]
    \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[state_component_equality]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[markerTheory.Abbrev_def,LET_DEF,word_exp_def]
    \\ full_simp_tac(srw_ss())[state_component_equality] \\ srw_tac[][])
  THEN1 (* Get *)
   (full_simp_tac(srw_ss())[Once comp_def,evaluate_def,get_var_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[set_var_def]
    \\ full_simp_tac(srw_ss())[state_component_equality])
  THEN1 (* Set *)
   (full_simp_tac(srw_ss())[Once comp_def,evaluate_def,get_var_def,set_store_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[set_var_def]
    \\ full_simp_tac(srw_ss())[state_component_equality])
  THEN1 (* Tick *)
   (qexists_tac `0` \\ full_simp_tac(srw_ss())[Once comp_def,evaluate_def,dec_clock_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[set_var_def]
    \\ full_simp_tac(srw_ss())[state_component_equality,empty_env_def])
  THEN1 (* Seq *)
   (simp [Once comp_def,dec_clock_def] \\ full_simp_tac(srw_ss())[evaluate_def]
    \\ split_pair_tac \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ split_pair_tac \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ split_pair_tac \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ full_simp_tac(srw_ss())[good_syntax_def,evaluate_def]
    \\ first_x_assum (qspecl_then[`m`,`n`,`c`]mp_tac)
    \\ match_mp_tac IMP_IMP \\ conj_tac
    THEN1 (CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[] \\ res_tac)
    \\ strip_tac \\ rev_full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `res`) \\ full_simp_tac(srw_ss())[]
    THEN1 (qexists_tac `ck` \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC,LET_DEF] \\ srw_tac[][])
    \\ first_x_assum (qspecl_then[`m'`,`n`,`c`]mp_tac)
    \\ match_mp_tac IMP_IMP \\ conj_tac
    THEN1 (srw_tac[][] \\ imp_res_tac evaluate_consts \\ full_simp_tac(srw_ss())[] \\ res_tac \\ full_simp_tac(srw_ss())[])
    \\ strip_tac \\ pop_assum mp_tac
    \\ drule (GEN_ALL evaluate_add_clock) \\ simp []
    \\ disch_then (qspec_then `ck'`assume_tac) \\ strip_tac
    \\ qexists_tac `ck + ck'` \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
    \\ imp_res_tac evaluate_consts \\ full_simp_tac(srw_ss())[])
  THEN1 (* Return *)
   (qexists_tac `0` \\ full_simp_tac(srw_ss())[Once comp_def,evaluate_def,get_var_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[get_var_def]
    \\ full_simp_tac(srw_ss())[state_component_equality,empty_env_def])
  THEN1 (* Raise *)
   (qexists_tac `0` \\ full_simp_tac(srw_ss())[Once comp_def,evaluate_def,get_var_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[get_var_def]
    \\ full_simp_tac(srw_ss())[state_component_equality,empty_env_def])
  THEN1 (* If *)
   (simp [Once comp_def] \\ full_simp_tac(srw_ss())[evaluate_def,get_var_def]
    \\ split_pair_tac \\ full_simp_tac(srw_ss())[] \\ split_pair_tac \\ full_simp_tac(srw_ss())[]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[evaluate_def,get_var_def,get_var_imm_case,good_syntax_def]
    \\ rev_full_simp_tac(srw_ss())[]
    THENL [first_x_assum (qspecl_then[`m`,`n`,`c`]mp_tac),
           first_x_assum (qspecl_then[`m'`,`n`,`c`]mp_tac)]
    \\ match_mp_tac IMP_IMP \\ conj_tac
    \\ TRY (srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
    \\ strip_tac \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]
    \\ qexists_tac `ck` \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC])
  THEN1 (* While *)
   (simp [Once comp_def] \\ full_simp_tac(srw_ss())[evaluate_def,get_var_def]
    \\ split_pair_tac \\ full_simp_tac(srw_ss())[]
    \\ reverse every_case_tac \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[evaluate_def,get_var_def,get_var_imm_case,good_syntax_def]
    \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
    THEN1 (qexists_tac `0` \\ full_simp_tac(srw_ss())[state_component_equality])
    \\ full_simp_tac(srw_ss())[LET_THM] \\ split_pair_tac \\ full_simp_tac(srw_ss())[]
    \\ first_x_assum (qspecl_then[`m`,`n`,`c`]mp_tac)
    \\ discharge_hyps THEN1 (full_simp_tac(srw_ss())[] \\ rpt strip_tac \\ res_tac \\ full_simp_tac(srw_ss())[])
    \\ full_simp_tac(srw_ss())[] \\ strip_tac \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `res <> NONE` \\ full_simp_tac(srw_ss())[]
    THEN1 (rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
      \\ qexists_tac `ck` \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC])
    \\ Cases_on `s1.clock = 0` \\ full_simp_tac(srw_ss())[]
    THEN1 (rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
      \\ qexists_tac `ck` \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC,empty_env_def])
    \\ full_simp_tac(srw_ss())[STOP_def]
    \\ first_x_assum (qspecl_then[`m`,`n`,`c`]mp_tac)
    \\ discharge_hyps
    THEN1 (full_simp_tac(srw_ss())[good_syntax_def] \\ rpt strip_tac \\ res_tac \\ full_simp_tac(srw_ss())[]
           \\ imp_res_tac evaluate_consts \\ full_simp_tac(srw_ss())[] \\ res_tac)
    \\ once_rewrite_tac [comp_def] \\ full_simp_tac(srw_ss())[LET_THM]
    \\ strip_tac \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac `ck+ck'`
    \\ pop_assum mp_tac
    \\ drule (GEN_ALL evaluate_add_clock) \\ full_simp_tac(srw_ss())[]
    \\ disch_then (qspec_then `ck'` assume_tac)
    \\ full_simp_tac(srw_ss())[dec_clock_def] \\ strip_tac
    \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
    \\ `ck' + (s1.clock - 1) = ck' + s1.clock - 1` by decide_tac \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac evaluate_consts \\ full_simp_tac(srw_ss())[])
  THEN1 (* JumpLower *)
   (full_simp_tac(srw_ss())[evaluate_def,get_var_def] \\ simp [Once comp_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[good_syntax_def]
    \\ full_simp_tac(srw_ss())[evaluate_def,get_var_def] \\ full_simp_tac(srw_ss())[find_code_def]
    \\ full_simp_tac(srw_ss())[state_component_equality,empty_env_def] \\ res_tac
    \\ imp_res_tac lookup_IMP_lookup_compile
    \\ pop_assum (qspec_then `c` strip_assume_tac) \\ full_simp_tac(srw_ss())[]
    THEN1 (qexists_tac `0` \\ full_simp_tac(srw_ss())[state_component_equality,empty_env_def])
    \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[PULL_FORALL,dec_clock_def]
    \\ first_x_assum (qspecl_then[`m1`,`n1`,`c`]mp_tac)
    \\ match_mp_tac IMP_IMP \\ conj_tac
    \\ TRY (srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[] \\ NO_TAC) \\ strip_tac \\ full_simp_tac(srw_ss())[]
    \\ `ck + s.clock - 1 = ck + (s.clock - 1)` by decide_tac
    \\ qexists_tac `ck` \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC])
  THEN1 (* Call *)
   (full_simp_tac(srw_ss())[evaluate_def] \\ Cases_on `ret` \\ full_simp_tac(srw_ss())[] THEN1
     (Cases_on `find_code dest s.regs s.code` \\ full_simp_tac(srw_ss())[]
      \\ every_case_tac \\ full_simp_tac(srw_ss())[empty_env_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[good_syntax_def] \\ simp [Once comp_def,evaluate_def]
      \\ drule find_code_IMP_lookup \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]
      \\ res_tac \\ imp_res_tac lookup_IMP_lookup_compile
      \\ pop_assum (strip_assume_tac o SPEC_ALL) \\ full_simp_tac(srw_ss())[]
      THEN1 (qexists_tac `0` \\ full_simp_tac(srw_ss())[empty_env_def,state_component_equality])
      THEN1 (qexists_tac `0` \\ full_simp_tac(srw_ss())[empty_env_def,state_component_equality])
      \\ full_simp_tac(srw_ss())[dec_clock_def]
      \\ first_x_assum (qspecl_then[`n1`,`m1`,`c`]mp_tac)
      \\ match_mp_tac IMP_IMP \\ conj_tac
      \\ TRY (srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[] \\ NO_TAC) \\ strip_tac \\ full_simp_tac(srw_ss())[]
      \\ `ck + s.clock - 1 = ck + (s.clock - 1)` by decide_tac
      \\ qexists_tac `ck` \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC])
    \\ qmatch_assum_rename_tac `good_syntax (Call (SOME z) dest handler)`
    \\ PairCases_on `z` \\ full_simp_tac(srw_ss())[] \\ simp [Once comp_def] \\ full_simp_tac(srw_ss())[]
    \\ split_pair_tac \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `find_code dest (s.regs \\ z1) s.code` \\ full_simp_tac(srw_ss())[]
    \\ drule find_code_IMP_lookup \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
    \\ res_tac \\ imp_res_tac lookup_IMP_lookup_compile
    \\ pop_assum (qspec_then`c`strip_assume_tac) \\ full_simp_tac(srw_ss())[good_syntax_def]
    \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] THEN1
     (srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ every_case_tac \\ full_simp_tac(srw_ss())[]
      \\ TRY split_pair_tac \\ full_simp_tac(srw_ss())[evaluate_def]
      \\ qexists_tac `0` \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[empty_env_def,state_component_equality])
    \\ Cases_on `evaluate (x,dec_clock (set_var z1 (Loc z2 z3) s))`
    \\ Cases_on `q` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ TRY
     (every_case_tac \\ full_simp_tac(srw_ss())[] \\ TRY split_pair_tac
      \\ full_simp_tac(srw_ss())[evaluate_def,dec_clock_def,set_var_def]
      \\ first_x_assum (qspecl_then[`n1`,`m1`,`c`]mp_tac)
      \\ match_mp_tac IMP_IMP \\ conj_tac
      \\ TRY (srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[] \\ NO_TAC) \\ strip_tac \\ full_simp_tac(srw_ss())[]
      \\ `ck + s.clock - 1 = s.clock - 1 + ck` by decide_tac
      \\ qexists_tac `ck` \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
    THEN1
     (Cases_on `w = Loc z2 z3` \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
      \\ first_x_assum (qspecl_then[`m`,`n`,`c`]mp_tac)
      \\ match_mp_tac IMP_IMP \\ conj_tac
      \\ TRY (imp_res_tac evaluate_consts \\ full_simp_tac(srw_ss())[]
              \\ srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
      \\ strip_tac \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]
      \\ first_x_assum (qspecl_then[`n1`,`m1`,`c`]mp_tac)
      \\ match_mp_tac IMP_IMP \\ conj_tac
      \\ TRY (imp_res_tac evaluate_consts \\ full_simp_tac(srw_ss())[]
              \\ srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[] \\ NO_TAC) \\ srw_tac[][]
      \\ Cases_on `handler` \\ full_simp_tac(srw_ss())[]
      \\ TRY (PairCases_on `x'` \\ fs[] \\ split_pair_tac \\ full_simp_tac(srw_ss())[])
      \\ full_simp_tac(srw_ss())[evaluate_def,dec_clock_def,set_var_def]
      \\ first_assum (mp_tac o Q.SPEC `ck` o
             MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
             (evaluate_add_clock |> GEN_ALL))) \\ full_simp_tac(srw_ss())[]
      \\ srw_tac[][] \\ qexists_tac `ck' + ck` \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
      \\ `ck + (ck' + (s.clock - 1)) = ck + (ck' + s.clock) - 1` by decide_tac
      \\ full_simp_tac(srw_ss())[] \\ imp_res_tac evaluate_consts \\ full_simp_tac(srw_ss())[])
    \\ Cases_on `handler` \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[evaluate_def,dec_clock_def,set_var_def]
    THEN1
     (first_x_assum (qspecl_then[`n1`,`m1`,`c`]mp_tac)
      \\ match_mp_tac IMP_IMP \\ conj_tac
      \\ TRY (imp_res_tac evaluate_consts \\ full_simp_tac(srw_ss())[]
              \\ srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[] \\ NO_TAC) \\ srw_tac[][]
      \\ `ck + s.clock - 1 = s.clock - 1 + ck` by decide_tac
      \\ qexists_tac `ck` \\ full_simp_tac(srw_ss())[])
    \\ PairCases_on `x'` \\ full_simp_tac(srw_ss())[]
    \\ split_pair_tac \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[evaluate_def,dec_clock_def,set_var_def]
    \\ Cases_on `w = Loc x'1 x'2` \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
    \\ ntac 2 (pop_assum mp_tac)
    \\ first_x_assum (qspecl_then[`n1`,`m1`,`c`]mp_tac)
    \\ match_mp_tac IMP_IMP \\ conj_tac
    \\ TRY (imp_res_tac evaluate_consts \\ full_simp_tac(srw_ss())[]
            \\ srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[] \\ NO_TAC) \\ srw_tac[][] \\ rev_full_simp_tac(srw_ss())[]
    \\ first_x_assum (qspecl_then[`m'`,`n`,`c`]mp_tac)
    \\ match_mp_tac IMP_IMP \\ conj_tac
    \\ TRY (imp_res_tac evaluate_consts \\ full_simp_tac(srw_ss())[]
            \\ srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[] \\ NO_TAC) \\ srw_tac[][]
    \\ ntac 2 (pop_assum mp_tac)
    \\ first_assum (mp_tac o Q.SPEC `ck'` o
             MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
             (evaluate_add_clock |> GEN_ALL))) \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ qexists_tac `ck+ck'` \\ full_simp_tac(srw_ss())[]
    \\ `ck + ck' + s.clock - 1 = s.clock - 1 + ck + ck'` by decide_tac \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac evaluate_consts \\ full_simp_tac(srw_ss())[])
  THEN1 (* FFI *)
   (qexists_tac `0` \\ full_simp_tac(srw_ss())[Once comp_def,evaluate_def,get_var_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[get_var_def]
    \\ full_simp_tac(srw_ss())[state_component_equality,empty_env_def,LET_DEF])
  \\ qexists_tac `0` \\ full_simp_tac(srw_ss())[Once comp_def,evaluate_def,get_var_def,set_var_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[get_var_def]
  \\ full_simp_tac(srw_ss())[state_component_equality,empty_env_def,LET_DEF]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[state_component_equality,empty_env_def,LET_DEF]);

val compile_semantics = Q.store_thm("compile_semantics",
  `(!k prog. lookup k s.code = SOME prog ==> 30 ≤ k /\ good_syntax prog) /\
   semantics start s <> Fail
   ==>
   semantics start (s with <|
                      code := fromAList (stack_alloc$compile c (toAList s.code));
                      use_alloc := F |>) =
   semantics start s`,
  simp[GSYM AND_IMP_INTRO] >> strip_tac >>
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
      drule comp_correct >>
      simp[good_syntax_def,RIGHT_FORALL_IMP_THM] >>
      discharge_hyps >- metis_tac[] >>
      simp[comp_def] >>
      disch_then(qspec_then`c`strip_assume_tac) >>
      qpat_assum`_ ≠ SOME TimeOut`mp_tac >>
      (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >>
      strip_tac >>
      drule (Q.GEN`extra`evaluate_add_clock) >>
      disch_then(qspec_then`ck`mp_tac) >> full_simp_tac(srw_ss())[] >>
      strip_tac >> fsrw_tac[ARITH_ss][] >> srw_tac[][]) >>
    DEEP_INTRO_TAC some_intro >> full_simp_tac(srw_ss())[] >>
    conj_tac >- (
      srw_tac[][] >>
      Cases_on`r=TimeOut`>>full_simp_tac(srw_ss())[]>-(
        qmatch_assum_abbrev_tac`evaluate (e,ss) = (SOME TimeOut,_)` >>
        qspecl_then[`k'`,`e`,`ss`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono)>>
        simp[Abbr`ss`] >>
        (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >>
        simp[] >> strip_tac >>
        drule comp_correct >>
        simp[RIGHT_FORALL_IMP_THM] >>
        discharge_hyps >- (
          simp[Abbr`e`,good_syntax_def] >>
          reverse conj_tac >- metis_tac[] >>
          rpt(first_x_assum(qspec_then`k+k'`mp_tac))>>srw_tac[][] ) >>
        simp[Abbr`e`,comp_def] >>
        disch_then(qspec_then`c`strip_assume_tac) >>
        Cases_on`t'.ffi.final_event`>>full_simp_tac(srw_ss())[] >- (
          ntac 2 (rator_x_assum`evaluate`mp_tac) >>
          drule (GEN_ALL evaluate_add_clock) >>
          disch_then(qspec_then`ck+k`mp_tac) >>
          simp[] >>
          discharge_hyps >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
          simp[] >> ntac 3 strip_tac >>
          rveq >> full_simp_tac(srw_ss())[] >>
          `t'.ffi = r''.ffi` by full_simp_tac(srw_ss())[state_component_equality] >>
          full_simp_tac(srw_ss())[] >>
          Cases_on`t.ffi.final_event`>>full_simp_tac(srw_ss())[] >>
          rev_full_simp_tac(srw_ss())[] ) >>
        rator_x_assum`evaluate`mp_tac >>
        qmatch_assum_abbrev_tac`evaluate (e,ss) = (_,t')` >>
        qspecl_then[`ck+k`,`e`,`ss`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono)>>
        simp[Abbr`ss`] >>
        ntac 2 strip_tac >> full_simp_tac(srw_ss())[] >>
        Cases_on`t.ffi.final_event`>>full_simp_tac(srw_ss())[] >>
        rev_full_simp_tac(srw_ss())[] ) >>
      rator_x_assum`evaluate`mp_tac >>
      drule (GEN_ALL evaluate_add_clock) >>
      disch_then(qspec_then`k'`mp_tac) >>
      simp[] >> strip_tac >>
      drule comp_correct >>
      simp[RIGHT_FORALL_IMP_THM] >>
      discharge_hyps >- (
        simp[good_syntax_def] >>
        reverse conj_tac >- metis_tac[] >>
        rpt(first_x_assum(qspec_then`k+k'`mp_tac))>>srw_tac[][] ) >>
      simp[comp_def] >>
      disch_then(qspec_then`c`strip_assume_tac) >>
      strip_tac >>
      qmatch_assum_abbrev_tac`evaluate (e,ss) = _` >>
      qspecl_then[`ck+k`,`e`,`ss`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono)>>
      simp[Abbr`ss`] >> strip_tac >>
      Cases_on`t'.ffi.final_event`>>full_simp_tac(srw_ss())[]>>
      drule (GEN_ALL evaluate_add_clock) >>
      disch_then(qspec_then`ck+k`mp_tac) >>
      simp[] >>
      discharge_hyps >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
      strip_tac >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
      `t.ffi = t'.ffi` by full_simp_tac(srw_ss())[state_component_equality] >>
      BasicProvers.FULL_CASE_TAC >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] ) >>
    drule comp_correct >>
    simp[RIGHT_FORALL_IMP_THM] >>
    discharge_hyps >- (
      simp[good_syntax_def] >>
      reverse conj_tac >- metis_tac[] >>
      rpt(first_x_assum(qspec_then`k`mp_tac))>>srw_tac[][]) >>
    simp[comp_def] >>
    disch_then(qspec_then`c`strip_assume_tac) >>
    asm_exists_tac >> simp[] >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[]) >>
  strip_tac >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
    first_x_assum(qspec_then`k`mp_tac)>>simp[]>>
    first_x_assum(qspec_then`k`mp_tac)>>
    (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >>
    simp[] >>
    srw_tac[][] >> BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
    drule comp_correct >>
    simp[good_syntax_def,comp_def] >>
    qexists_tac`c`>>simp[] >>
    conj_tac >- metis_tac[] >>
    srw_tac[][] >>
    qpat_assum`_ ≠ SOME TimeOut`mp_tac >>
    (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >> srw_tac[][] >>
    drule (GEN_ALL evaluate_add_clock) >>
    disch_then(qspec_then`ck`mp_tac)>>simp[] ) >>
  DEEP_INTRO_TAC some_intro >> full_simp_tac(srw_ss())[] >>
  conj_tac >- (
    srw_tac[][] >>
    qpat_assum`∀k t. _`(qspec_then`k`mp_tac) >>
    (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >>
    simp[] >>
    last_x_assum mp_tac >>
    last_x_assum(qspec_then`k`mp_tac) >>
    srw_tac[][] >> BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
    drule comp_correct >>
    simp[good_syntax_def,comp_def] >>
    qexists_tac`c`>>simp[] >>
    conj_tac >- metis_tac[] >>
    srw_tac[][] >>
    Cases_on`r=TimeOut`>>full_simp_tac(srw_ss())[]>-(
      qmatch_assum_abbrev_tac`evaluate (e,ss) = (_,t)` >>
      qspecl_then[`ck`,`e`,`ss`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono)>>
      simp[Abbr`ss`] >>
      Cases_on`t.ffi.final_event`>>full_simp_tac(srw_ss())[] >>
      rpt strip_tac >> full_simp_tac(srw_ss())[] ) >>
    rator_x_assum`evaluate`mp_tac >>
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
    metis_tac[
      LESS_EQ_EXISTS,
      evaluate_add_clock_io_events_mono
        |> CONV_RULE(SWAP_FORALL_CONV)
        |> Q.SPEC`s with <| use_alloc := F; clock := k; code := c|>`
        |> SIMP_RULE(srw_ss())[],
      evaluate_add_clock_io_events_mono
        |> CONV_RULE(SWAP_FORALL_CONV)
        |> Q.SPEC`s with <| clock := k |>`
        |> SIMP_RULE(srw_ss())[]]) >>
  simp[equiv_lprefix_chain_thm] >>
  unabbrev_all_tac >> simp[PULL_EXISTS] >>
  ntac 2 (pop_assum kall_tac) >>
  simp[LNTH_fromList,PULL_EXISTS] >>
  simp[GSYM FORALL_AND_THM] >>
  rpt gen_tac >>
  (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >> full_simp_tac(srw_ss())[] >>
  (fn g => subterm (fn tm => Cases_on`^(assert (fn tm => has_pair_type tm andalso free_in tm (#2 g)) tm)`) (#2 g) g) >> full_simp_tac(srw_ss())[] >>
  drule comp_correct >>
  simp[comp_def,RIGHT_FORALL_IMP_THM] >>
  discharge_hyps >- (
    simp[good_syntax_def] >>
    reverse conj_tac >- metis_tac[] >>
    rpt(first_x_assum(qspec_then`k`mp_tac))>>srw_tac[][] ) >>
  disch_then(qspec_then`c`strip_assume_tac) >>
  reverse conj_tac >- (
    srw_tac[][] >>
    qexists_tac`ck+k`>>simp[] ) >>
  srw_tac[][] >>
  qexists_tac`k`>>simp[] >>
  ntac 2 (rator_x_assum`evaluate`mp_tac) >>
  qmatch_assum_abbrev_tac`evaluate (e,ss) = _` >>
  qspecl_then[`ck`,`e`,`ss`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono)>>
  simp[Abbr`ss`] >>
  ntac 3 strip_tac >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[IS_PREFIX_APPEND] >>
  simp[EL_APPEND1]);

val make_init_def = Define `
  make_init code s = s with <| code := code; use_alloc := T |>`;

val prog_comp_lambda = Q.store_thm("prog_comp_lambda",
  `prog_comp = λ(n,p). ^(rhs (concl (SPEC_ALL prog_comp_def)))`,
  srw_tac[][FUN_EQ_THM,prog_comp_def,LAMBDA_PROD,FORALL_PROD]);

val make_init_semantics = Q.store_thm("make_init_semantics",
  `(!k prog. ALOOKUP code k = SOME prog ==> 30 ≤ k /\ good_syntax prog) /\
   ~s.use_alloc /\ s.code = fromAList (compile c code) /\
   ALL_DISTINCT (MAP FST code) /\
   semantics start (make_init (fromAList code) s) <> Fail ==>
   semantics start s = semantics start (make_init (fromAList code) s)`,
  srw_tac[][] \\ drule (ONCE_REWRITE_RULE[CONJ_COMM]compile_semantics)
  \\ full_simp_tac(srw_ss())[make_init_def,lookup_fromAList]
  \\ discharge_hyps THEN1 (srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[])
  \\ disch_then (assume_tac o GSYM)
  \\ full_simp_tac(srw_ss())[] \\ AP_TERM_TAC
  \\ full_simp_tac(srw_ss())[state_component_equality]
  \\ full_simp_tac(srw_ss())[spt_eq_thm,wf_fromAList,lookup_fromAList,compile_def]
  \\ srw_tac[][]
  \\ srw_tac[][ALOOKUP_APPEND] \\ BasicProvers.CASE_TAC
  \\ simp[prog_comp_lambda,ALOOKUP_MAP_gen]
  \\ simp[ALOOKUP_toAList,lookup_fromAList]);

val _ = export_theory();
