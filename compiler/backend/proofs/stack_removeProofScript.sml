open preamble
     stack_removeTheory
     stackLangTheory
     stackSemTheory
     stackPropsTheory
     set_sepTheory
     semanticsPropsTheory
     helperLib
local open dep_rewrite blastLib in end

val _ = new_theory"stack_removeProof";

val word_shift_def = backend_commonTheory.word_shift_def
val _ = temp_overload_on ("num_stubs", ``stack_num_stubs``)

(* TODO: move *)

val aligned_or = Q.store_thm("aligned_or", (* TODO: move *)
  `aligned n (w || v) <=> aligned n w /\ aligned n v`,
  Cases_on `n = 0`
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [alignmentTheory.aligned_extract]
  \\ metis_tac [])

val aligned_w2n = Q.store_thm("aligned_w2n",
  `aligned k w <=> w2n (w:'a word) MOD 2 ** k = 0`,
  Cases_on `w`
  \\ fs [alignmentTheory.aligned_def,alignmentTheory.align_w2n]
  \\ `0n < 2 ** k` by simp []
  \\ drule DIVISION
  \\ disch_then (qspec_then `n` assume_tac)
  \\ `(n DIV 2 ** k * 2 ** k) < dimword (:α)` by decide_tac
  \\ asm_simp_tac std_ss [] \\ decide_tac);

val word_list_exists_thm = Q.store_thm("word_list_exists_thm",
  `(word_list_exists a 0 = emp) /\
    (word_list_exists a (SUC n) =
     SEP_EXISTS w. one (a,w) * word_list_exists (a + bytes_in_word) n)`,
  full_simp_tac(srw_ss())[word_list_exists_def,LENGTH_NIL,FUN_EQ_THM,ADD1,
          SEP_EXISTS_THM,cond_STAR,word_list_def,SEP_CLAUSES]
  \\ srw_tac[][] \\ eq_tac \\ srw_tac[][]
  THEN1
   (Cases_on `xs` \\ full_simp_tac(srw_ss())[ADD1]
    \\ full_simp_tac(srw_ss())[word_list_def]
    \\ qexists_tac `h` \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac `t` \\ full_simp_tac(srw_ss())[SEP_CLAUSES])
  \\ qexists_tac `w::xs`
  \\ full_simp_tac(srw_ss())[word_list_def,ADD1,STAR_ASSOC,cond_STAR]);

val word_list_exists_ADD = Q.store_thm("word_list_exists_ADD",
  `!m n a.
      word_list_exists a (m + n) =
      word_list_exists a m *
      word_list_exists (a + bytes_in_word * n2w m) n`,
  Induct \\ full_simp_tac(srw_ss())[word_list_exists_thm,SEP_CLAUSES,ADD_CLAUSES]
  \\ full_simp_tac(srw_ss())[STAR_ASSOC,ADD1,GSYM word_add_n2w,
       WORD_LEFT_ADD_DISTRIB]);

val word_list_APPEND = Q.store_thm("word_list_APPEND",
  `!xs ys a.
      word_list a (xs ++ ys) =
      word_list a xs * word_list (a + bytes_in_word * n2w (LENGTH xs)) ys`,
  Induct \\ full_simp_tac(srw_ss())[word_list_def,SEP_CLAUSES,STAR_ASSOC,ADD1,GSYM word_add_n2w]
  \\ full_simp_tac(srw_ss())[WORD_LEFT_ADD_DISTRIB]);

val LESS_LENGTH_IMP_APPEND = Q.store_thm("LESS_LENGTH_IMP_APPEND",
  `!xs n. n < LENGTH xs ==> ?ys zs. xs = ys ++ zs /\ LENGTH ys = n`,
  Induct \\ full_simp_tac(srw_ss())[] \\ Cases_on `n` \\ full_simp_tac(srw_ss())[LENGTH_NIL]
  \\ srw_tac[][] \\ res_tac \\ srw_tac[][]
  \\ pop_assum (fn th => simp [Once th])
  \\ qexists_tac `h::ys` \\ full_simp_tac(srw_ss())[]);

val call_FFI_LENGTH = Q.store_thm("call_FFI_LENGTH",
  `(call_FFI s i conf xs = (n,ys)) ==> (LENGTH ys = LENGTH xs)`,
  srw_tac[][ffiTheory.call_FFI_def]
  \\ every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]);

val n2w_lt = Q.store_thm("n2w_lt",
  `(0w:'a word) < n2w a ∧ (0w:'a word) < n2w b ∧
   a < dimword (:'a) ∧ b < dimword (:'a)
   ⇒
   ((n2w a:'a word) < (n2w b:'a word) ⇔ a < b)`,
  simp[word_lt_n2w]);

val n2w_le = Q.store_thm("n2w_le",
  `(0w:'a word) < n2w a ∧ (0w:'a word) < n2w b ∧
   a < dimword (:'a) ∧ b < dimword (:'a)
   ⇒
   ((n2w a:'a word) ≤ (n2w b:'a word) ⇔ a ≤ b)`,
  srw_tac[][WORD_LESS_OR_EQ,LESS_OR_EQ]
  \\ metis_tac[n2w_lt]);

val word_lt_0w = Q.store_thm("word_lt_0w",
  `2 * n < dimword (:'a) ⇒ ((0w:'a word) < n2w n ⇔ 0 < n)`,
  simp[WORD_LT]
  \\ Cases_on`0 < n` \\ simp[]
  \\ simp[word_msb_n2w_numeric]
  \\ simp[NOT_LESS_EQUAL]
  \\ simp[INT_MIN_def]
  \\ simp[dimword_def]
  \\ Cases_on`dimindex(:'a)`\\simp[]
  \\ simp[EXP]);

val word_sub_lt = Q.store_thm("word_sub_lt",
  `0w < n ∧ 0w < m ∧ n ≤ m ⇒ m - n < m`,
  rpt strip_tac
  \\ Cases_on`m`>>Cases_on`n`
  \\ qpat_x_assum`_ ≤ _`mp_tac
  \\ asm_simp_tac std_ss [n2w_le]
  \\ simp_tac std_ss [GSYM n2w_sub]
  \\ strip_tac
  \\ qmatch_assum_rename_tac`a:num ≤ b`
  \\ Cases_on`a=b`>-full_simp_tac(srw_ss())[]
  \\ `a < b` by simp[]
  \\ `0 < a` by (Cases_on`a`\\full_simp_tac(srw_ss())[]\\metis_tac[WORD_LESS_REFL])
  \\ `b - a < b` by simp[]
  \\ Cases_on`0w < n2w (b - a)`
  >- (
    dep_rewrite.DEP_ONCE_REWRITE_TAC[n2w_lt]
    \\ simp[])
  \\ full_simp_tac(srw_ss())[word_lt_n2w,LET_THM]);

val with_same_clock = Q.store_thm("with_same_clock[simp]",
  `x with clock := x.clock = x`,
  srw_tac[][state_component_equality]);

val set_var_set_var = Q.store_thm("set_var_set_var[simp]",
  `set_var x y (set_var x z w) = set_var x y w`,
  EVAL_TAC \\ srw_tac[][state_component_equality]);

val get_var_set_var_same = Q.store_thm("get_var_set_var_same[simp]",
  `get_var x (set_var x y z) = SOME y`,
  EVAL_TAC);

val get_var_set_var = Q.store_thm("get_var_set_var",
  `get_var x (set_var x' y z) = if x = x' then SOME y else get_var x z`,
  EVAL_TAC \\ srw_tac[][]);

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

val word_offset_eq = Q.store_thm("word_offset_eq",
  `word_offset n = bytes_in_word * n2w n`,
  full_simp_tac(srw_ss())[word_offset_def,word_mul_n2w,bytes_in_word_def]);

val memory_def = Define `
  memory m dm = \s. s = fun2set (m, dm)`;

val word_list_rev_def = Define `
  (word_list_rev a [] = emp) /\
  (word_list_rev a (x::xs) =
     one (a - bytes_in_word, x) * word_list_rev (a - bytes_in_word) xs)`;

val word_store_def = Define `
  word_store base store =
    word_list_rev base
      (MAP (\name. case FLOOKUP store name of
                   | NONE => Word 0w | SOME x => x) store_list)`

val code_rel_def = Define `
  code_rel jump off k code1 code2 <=>
    !n prog.
      lookup n code1 = SOME prog ==>
      reg_bound prog k /\
      lookup n code2 = SOME (comp jump off k prog)`

val is_SOME_Word_def = Define `
  (is_SOME_Word (SOME (Word w)) = T) /\
  (is_SOME_Word _ = F)`;

val the_SOME_Word_def = Define `
  (the_SOME_Word (SOME (Word w)) = w)`;

val state_rel_def = Define `
  state_rel jump off k (s1:('a,'ffi) stackSem$state) s2 <=>
    s1.use_stack /\ s1.use_store /\
    ~s2.use_stack /\ ~s2.use_store /\
    ~s2.use_alloc /\ ~s1.use_alloc /\
    s2.be = s1.be /\
    s2.gc_fun = s1.gc_fun /\
    s2.clock = s1.clock /\
    s2.ffi = s1.ffi /\
    s2.ffi_save_regs = s1.ffi_save_regs /\
    s2.fp_regs = s1.fp_regs /\
    good_dimindex (:'a) /\
    (!n.
       n < k ==>
       FLOOKUP s2.regs n = FLOOKUP s1.regs n) /\
    code_rel jump off k s1.code s2.code /\
    lookup stack_err_lab s2.code = SOME (halt_inst 2w) /\
    FLOOKUP s2.regs (k+2) = FLOOKUP s1.store CurrHeap /\
    {k;k+1;k+2} SUBSET s2.ffi_save_regs /\
    is_SOME_Word (FLOOKUP s1.store BitmapBase) /\
    s1.stack_space <= LENGTH s1.stack /\
    case FLOOKUP s2.regs (k+1) of
    | SOME (Word base) =>
      dimindex (:'a) DIV 8 * max_stack_alloc <= w2n base /\
      w2n base + w2n (bytes_in_word:'a word) * LENGTH s1.stack < dimword (:'a) /\
      FLOOKUP s2.regs k =
        SOME (Word (base + bytes_in_word * n2w s1.stack_space)) /\
      (memory s1.memory s1.mdomain *
       word_list (the_SOME_Word (FLOOKUP s1.store BitmapBase) << word_shift (:'a))
         (MAP Word s1.bitmaps) *
       word_store base s1.store *
       word_list base s1.stack)
        (fun2set (s2.memory,s2.mdomain))
    | _ => F`

val state_rel_get_var = Q.prove(
  `state_rel jump off k s t /\ n < k ==> (get_var n s = get_var n t)`,
  full_simp_tac(srw_ss())[state_rel_def,get_var_def]);

val state_rel_IMP = Q.prove(
  `state_rel jump off k s t1 ==>
    state_rel jump off k (dec_clock s) (dec_clock t1)`,
  srw_tac[][] \\ full_simp_tac(srw_ss())[state_rel_def,dec_clock_def,empty_env_def] \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[])

val state_rel_with_clock = Q.prove(
  `state_rel jump off k s t1 ==>
    state_rel jump off k (s with clock := c) (t1 with clock := c)`,
  srw_tac[][] \\ full_simp_tac(srw_ss())[state_rel_def,dec_clock_def,empty_env_def] \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[])

val find_code_lemma = Q.prove(
  `state_rel jump off k s t1 /\
    (case dest of INL v2 => T | INR i => i < k) /\
    find_code dest s.regs s.code = SOME x ==>
    find_code dest t1.regs t1.code = SOME (comp jump off k x) /\ reg_bound x k`,
  CASE_TAC \\ full_simp_tac(srw_ss())[find_code_def,state_rel_def,code_rel_def]
  \\ strip_tac \\ res_tac
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ res_tac);

val find_code_lemma2 = Q.prove(
  `state_rel jump off k s t1 /\
    (case dest of INL v2 => T | INR i => i < k) /\
    find_code dest (s.regs \\ x1) s.code = SOME x ==>
    find_code dest (t1.regs \\ x1) t1.code = SOME (comp jump off k x) /\ reg_bound x k`,
  CASE_TAC \\ full_simp_tac(srw_ss())[find_code_def,state_rel_def,code_rel_def]
  \\ strip_tac \\ res_tac
  \\ fs[DOMSUB_FLOOKUP_THM]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ res_tac
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ res_tac);

val state_rel_set_var = Q.store_thm("state_rel_set_var[simp]",
  `state_rel jump off k s t1 /\ v < k ==>
    state_rel jump off k (set_var v x s) (set_var v x t1)`,
  full_simp_tac(srw_ss())[state_rel_def,set_var_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[FLOOKUP_UPDATE]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[] \\ `F` by decide_tac);

val word_store_CurrHeap = Q.prove(
  `word_store base (s.store |+ (CurrHeap,x)) = word_store base s.store`,
  full_simp_tac(srw_ss())[word_store_def,store_list_def,FLOOKUP_UPDATE]);

val memory_fun2set_IMP_read = Q.prove(
  `(memory m d * p) (fun2set (m1,d1)) /\ a IN d ==>
    a IN d1 /\ m1 a = m a`,
  simp [Once STAR_def,set_sepTheory.SPLIT_EQ,memory_def]
  \\ full_simp_tac(srw_ss())[fun2set_def,SUBSET_DEF,PULL_EXISTS]);

val state_rel_read = Q.prove(
  `state_rel jump off k s t /\ a IN s.mdomain ==>
    a IN t.mdomain /\ (t.memory a = s.memory a)`,
  full_simp_tac(srw_ss())[state_rel_def] \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ strip_tac
  \\ full_simp_tac(srw_ss())[GSYM STAR_ASSOC] \\ metis_tac [memory_fun2set_IMP_read]);

val mem_load_byte_aux_IMP = Q.prove(
  `state_rel jump off k s t /\
    mem_load_byte_aux s.memory s.mdomain s.be a = SOME x ==>
    mem_load_byte_aux t.memory t.mdomain t.be a = SOME x`,
  full_simp_tac(srw_ss())[wordSemTheory.mem_load_byte_aux_def] \\ srw_tac[][]
  \\ `s.be = t.be` by full_simp_tac(srw_ss())[state_rel_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ imp_res_tac state_rel_read
  \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]);

val read_bytearray_IMP_read_bytearray = Q.prove(
  `!n a k s t x.
      state_rel jump off k s t /\
      read_bytearray a n (mem_load_byte_aux s.memory s.mdomain s.be) = SOME x ==>
      read_bytearray a n (mem_load_byte_aux t.memory t.mdomain t.be) = SOME x`,
  Induct \\ full_simp_tac(srw_ss())[read_bytearray_def]
  \\ srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ res_tac \\ srw_tac[][]
  \\ imp_res_tac mem_load_byte_aux_IMP \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]);

val write_bytearray_IGNORE_non_aligned = Q.prove(
  `!new_bytes a.
      (!x. b <> byte_align x) ==>
      write_bytearray a new_bytes m d be b = m b`,
  Induct \\ full_simp_tac(srw_ss())[wordSemTheory.write_bytearray_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[wordSemTheory.mem_store_byte_aux_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]);

val write_bytearray_IGNORE = Q.prove(
  `!new_bytes a x xx.
      d1 SUBSET d /\
      read_bytearray a (LENGTH new_bytes) (mem_load_byte_aux m1 d1 be) = SOME x /\ xx ∉ d1 ==>
      write_bytearray a new_bytes m d be xx = m xx`,
  Induct_on `new_bytes`
  \\ full_simp_tac(srw_ss())[wordSemTheory.write_bytearray_def,read_bytearray_def]
  \\ full_simp_tac(srw_ss())[wordSemTheory.mem_load_byte_aux_def]
  \\ full_simp_tac(srw_ss())[wordSemTheory.mem_store_byte_aux_def]
  \\ rpt gen_tac \\ every_case_tac
  \\ srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]);

val write_bytearray_EQ = Q.prove(
  `!new_bytes a m1 m y x.
      d1 SUBSET d /\ (!a. a IN d1 ==> m1 a = m a /\ a IN d) /\
      read_bytearray a (LENGTH new_bytes) (mem_load_byte_aux m1 d1 be) = SOME y /\ m1 x = m x ==>
      write_bytearray a new_bytes m1 d1 be x =
      write_bytearray a new_bytes m d be x`,
  Induct_on `new_bytes`
  \\ full_simp_tac(srw_ss())[wordSemTheory.write_bytearray_def,read_bytearray_def]
  \\ rpt gen_tac \\ ntac 2 BasicProvers.TOP_CASE_TAC \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[wordSemTheory.mem_store_byte_aux_def]
  \\ full_simp_tac(srw_ss())[wordSemTheory.mem_load_byte_aux_def]
  \\ Cases_on `m1 (byte_align a)` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ `byte_align a IN d` by full_simp_tac(srw_ss())[SUBSET_DEF] \\ full_simp_tac(srw_ss())[]
  \\ qpat_x_assum `xx ==> yy` mp_tac \\ impl_tac THEN1 (metis_tac [])
  \\ srw_tac[][]
  \\ `write_bytearray (a + 1w) new_bytes m1 d1 be (byte_align a) =
      write_bytearray (a + 1w) new_bytes m d be (byte_align a)` by
    (first_x_assum match_mp_tac \\ full_simp_tac(srw_ss())[] \\ res_tac \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[] \\ every_case_tac \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM] \\ srw_tac[][]);

val write_bytearray_lemma = Q.prove(
  `!new_bytes a m1 d1 be x p m d.
      (memory m1 d1 * p) (fun2set (m,d)) /\
      read_bytearray a (LENGTH new_bytes) (mem_load_byte_aux m1 d1 be) = SOME x ==>
      (memory (write_bytearray a new_bytes m1 d1 be) d1 * p)
        (fun2set (write_bytearray a new_bytes m d be,d))`,
  simp [STAR_def,set_sepTheory.SPLIT_EQ,memory_def]
  \\ full_simp_tac(srw_ss())[fun2set_def,SUBSET_DEF,PULL_EXISTS] \\ srw_tac[][]
  \\ `d1 SUBSET d` by full_simp_tac(srw_ss())[SUBSET_DEF]
  THEN1 (res_tac \\ full_simp_tac(srw_ss())[] \\ imp_res_tac write_bytearray_EQ \\ full_simp_tac(srw_ss())[])
  \\ qpat_x_assum `p xx` mp_tac
  \\ match_mp_tac (METIS_PROVE [] ``(x=y)==>x==>y``) \\ AP_TERM_TAC
  \\ full_simp_tac(srw_ss())[EXTENSION] \\ srw_tac[][] \\ EQ_TAC \\ srw_tac[][]
  \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ pop_assum mp_tac \\ full_simp_tac(srw_ss())[]
  \\ rename1 `xx IN d`
  \\ Cases_on `xx IN d1` \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac write_bytearray_IGNORE \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac write_bytearray_EQ \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[] \\ metis_tac [])

val state_rel_get_var_k = Q.store_thm("state_rel_get_var_k",
  `state_rel jump off k s t ⇒
   ∃c:α word.
   get_var (k+1) t = SOME (Word c) ∧
   dimindex (:α) DIV 8 * max_stack_alloc ≤ w2n c ∧
   w2n c + w2n (bytes_in_word:'a word) * LENGTH s.stack < dimword (:'a) ∧
   get_var k t = SOME (Word (c + bytes_in_word * n2w s.stack_space)) ∧
   (memory s.memory s.mdomain *
    word_list (the_SOME_Word (FLOOKUP s.store BitmapBase) << word_shift (:α)) (MAP Word s.bitmaps) *
    word_store c s.store * word_list c s.stack) (fun2set (t.memory,t.mdomain))`,
  srw_tac[][state_rel_def]
  \\ pop_assum mp_tac
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ simp[get_var_def]);

val evaluate_single_stack_alloc = Q.store_thm("evaluate_single_stack_alloc",
  `state_rel jump off k s t1 ∧
   ((r,s2) = if s.stack_space < n
    then (SOME (Halt (Word 2w)),empty_env s)
    else (NONE, s with stack_space := s.stack_space - n)) ∧
   n ≠ 0 ∧ n ≤ max_stack_alloc
   ⇒
   ∃ck t2.
     evaluate (single_stack_alloc jump k n,t1 with clock := t1.clock + ck) = (r,t2) ∧
     if s.stack_space < n then t2.ffi = s2.ffi else state_rel jump off k s2 t2`,
  simp[single_stack_alloc_def] \\
  Cases_on`jump` \\
  simp [evaluate_def,inst_def,assign_def,word_exp_def,
       wordLangTheory.word_op_def,GSYM get_var_def]
  \\ strip_tac
  \\ imp_res_tac state_rel_get_var_k
  \\ simp[get_var_imm_def,get_var_def]
  \\ full_simp_tac(srw_ss())[get_var_def,set_var_def,FLOOKUP_UPDATE]
  \\ simp[]
  \\ simp[labSemTheory.word_cmp_def,asmTheory.word_cmp_def]
  \\ qpat_abbrev_tac`cc = c + _ + _`
  \\ `cc <+ c ⇔ s.stack_space < n`
  by (
    simp[Abbr`cc`,word_offset_def,bytes_in_word_def,word_mul_n2w,word_add_n2w]
    \\ Cases_on`c` \\ full_simp_tac(srw_ss())[]
    \\ qpat_abbrev_tac`d = _ DIV 8`
    \\ REWRITE_TAC[
         wordsLib.WORD_DECIDE ``w + -1w * v + t = w + t - v``,
         word_add_n2w]
    \\ REWRITE_TAC[addressTheory.word_arith_lemma2]
    \\ qmatch_assum_rename_tac`m < dimword _`
    \\ IF_CASES_TAC \\ simp_tac bool_ss []
    >- (
      `m < (n - s.stack_space) * d` by decide_tac
      \\ reverse (Cases_on `s.stack_space < n`)
      >- (
        `n - s.stack_space = 0` by decide_tac
        \\ `m < 0 * d` by metis_tac[] \\ full_simp_tac(srw_ss())[] )
      \\ simp[]
      \\ `m + d * s.stack_space ≤ d * n` by decide_tac
      \\ asm_simp_tac std_ss [n2w_sub]
      \\ REWRITE_TAC[WORD_NEG_SUB]
      \\ asm_simp_tac std_ss [GSYM n2w_sub]
      \\ REWRITE_TAC[GSYM word_add_n2w]
      \\ REWRITE_TAC[GSYM WORD_SUB_SUB]
      \\ `d * s.stack_space ≤ d * n` by decide_tac
      \\ asm_simp_tac std_ss [GSYM n2w_sub]
      \\ REWRITE_TAC[GSYM LEFT_SUB_DISTRIB]
      \\ ONCE_REWRITE_TAC[MULT_COMM]
      \\ qmatch_abbrev_tac`n2w m - n2w a <+ _`
      \\ `d ≠ 0` by ( strip_tac \\ full_simp_tac(srw_ss())[Abbr`d`,Abbr`a`] )
      \\ `0 < m` by (full_simp_tac(srw_ss())[max_stack_alloc_def,Abbr`d`] \\ decide_tac)
      \\ `d * max_stack_alloc < d * (n - s.stack_space)` by decide_tac
      \\ `max_stack_alloc < n - s.stack_space` by metis_tac[LT_MULT_LCANCEL]
      \\ decide_tac)
    \\ `(n - s.stack_space) * d ≤ m` by decide_tac
    \\ qmatch_assum_abbrev_tac`a * d ≤ m`
    \\ simp[WORD_LO]
    \\ Cases_on`s.stack_space < n`
    >- (
      `s.stack_space ≤ n` by decide_tac
      \\ `s.stack_space * d ≤ n * d` by metis_tac[LESS_MONO_MULT]
      \\ asm_simp_tac std_ss [GSYM SUB_SUB]
      \\ REWRITE_TAC[GSYM RIGHT_SUB_DISTRIB]
      \\ simp[]
      \\ `d ≠ 0` by (strip_tac \\ full_simp_tac(srw_ss())[Abbr`d`,state_rel_def,labPropsTheory.good_dimindex_def] \\ rev_full_simp_tac(srw_ss())[])
      \\ conj_asm1_tac >- simp[]
      \\ full_simp_tac(srw_ss())[max_stack_alloc_def]
      \\ simp[] )
    \\ simp[]
    \\ simp[NOT_LESS]
    \\ `n ≤ s.stack_space` by decide_tac
    \\ simp[]
    \\ `d * n ≤ d * s.stack_space` by metis_tac[LESS_MONO_MULT,MULT_COMM]
    \\ asm_simp_tac std_ss [LESS_EQ_ADD_SUB]
    \\ REWRITE_TAC[GSYM LEFT_SUB_DISTRIB]
    \\ `m + d * (s.stack_space - n) < dimword (:'a)` suffices_by (simp [])
    \\ full_simp_tac(srw_ss())[LEFT_SUB_DISTRIB]
    \\ full_simp_tac(srw_ss())[state_rel_def,bytes_in_word_def]
    \\ `d < dimword (:α)` by (UNABBREV_ALL_TAC
           \\ full_simp_tac(srw_ss())[labPropsTheory.good_dimindex_def,dimword_def]) \\ full_simp_tac(srw_ss())[]
    \\ qpat_x_assum `s.stack_space <= LENGTH s.stack` assume_tac
    \\ drule LESS_EQUAL_ADD \\ strip_tac \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[LEFT_ADD_DISTRIB] \\ decide_tac)
  \\ simp[]
  >- (* jump = true *)
    (BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    >- (
      srw_tac[][find_code_def]
      \\ qhdtm_x_assum`state_rel`mp_tac
      \\ simp[Once state_rel_def]
      \\ strip_tac
      \\ simp[halt_inst_def,evaluate_def,inst_def,assign_def,word_exp_def,set_var_def,dec_clock_def,get_var_def,FLOOKUP_UPDATE]
      \\ qexists_tac`1`
      \\ simp[] )
    \\ rveq
    \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ simp[FLOOKUP_UPDATE]
    \\ conj_tac >- metis_tac[]
    \\ simp[Abbr`cc`]
    \\ simp[word_offset_def,bytes_in_word_def,word_mul_n2w,word_add_n2w]
    \\ ONCE_REWRITE_TAC[WORD_SUB_INTRO]
    \\ ONCE_REWRITE_TAC[GSYM WORD_ADD_SUB_SYM]
    \\ REWRITE_TAC[WORD_MULT_CLAUSES]
    \\ REWRITE_TAC[WORD_ADD_SUB_ASSOC]
    \\ dep_rewrite.DEP_REWRITE_TAC[GSYM n2w_sub]
    \\ simp[]
    \\ metis_tac[])
  >> (* jump = false *)
    (BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    >- (simp[evaluate_def,halt_inst_def,inst_def,assign_def,word_exp_def]>>
      fs[state_rel_def])
    \\ rveq
    \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ simp[FLOOKUP_UPDATE]
    \\ conj_tac >- metis_tac[]
    \\ simp[Abbr`cc`]
    \\ simp[word_offset_def,bytes_in_word_def,word_mul_n2w,word_add_n2w]
    \\ ONCE_REWRITE_TAC[WORD_SUB_INTRO]
    \\ ONCE_REWRITE_TAC[GSYM WORD_ADD_SUB_SYM]
    \\ REWRITE_TAC[WORD_MULT_CLAUSES]
    \\ REWRITE_TAC[WORD_ADD_SUB_ASSOC]
    \\ dep_rewrite.DEP_REWRITE_TAC[GSYM n2w_sub]
    \\ simp[]
    \\ metis_tac[]));

val evaluate_stack_alloc = Q.store_thm("evaluate_stack_alloc",
  `∀jump k n r s s2 t1.
   evaluate (StackAlloc n,s) = (r,s2) ∧ r ≠ SOME Error ∧
   state_rel jump off k s t1
   ⇒
   ∃ck t2.
     evaluate (stack_alloc jump k n,t1 with clock := ck + t1.clock) = (r,t2) ∧
     if ∀w. r ≠ SOME (Halt w) then state_rel jump off k s2 t2 else t2.ffi = s2.ffi`,
  ho_match_mp_tac stack_alloc_ind
  \\ srw_tac[][stackSemTheory.evaluate_def]
  \\ simp[Once stack_alloc_def]
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  >- (
    srw_tac[][evaluate_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[]
    \\ srw_tac[][] \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ metis_tac[])
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  >- (
    drule evaluate_single_stack_alloc
    \\ impl_tac
    >- ( srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[state_rel_def] )
    \\ simp[]
    \\ strip_tac
    \\ asm_exists_tac
    \\ every_case_tac \\ full_simp_tac(srw_ss())[]
    \\ rveq \\ full_simp_tac(srw_ss())[])
  \\ simp[evaluate_def]
  \\ drule (GEN_ALL evaluate_single_stack_alloc)
  \\ disch_then(qspec_then`max_stack_alloc`mp_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars["n"])))
  \\ simp[]
  \\ `max_stack_alloc ≠ 0` by EVAL_TAC
  \\ simp[]
  \\ srw_tac[][]
  >- (
    qexists_tac`ck`\\simp[]
    \\ `s.stack_space < n` by decide_tac
    \\ full_simp_tac(srw_ss())[]
    \\ `s.use_stack` by full_simp_tac(srw_ss())[state_rel_def]
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] )
  \\ `s.use_stack` by full_simp_tac(srw_ss())[state_rel_def]
  \\ full_simp_tac(srw_ss())[]
  \\ qabbrev_tac`s' =
        if s.stack_space < n then empty_env (s with stack_space := s.stack_space - max_stack_alloc)
        else s with stack_space := s.stack_space - n`
  \\ `∃ck'. ∃t2'.
        evaluate (stack_alloc jump k (n - max_stack_alloc), t2 with clock := ck' + t2.clock) =
          (r,t2') ∧
        if ∀w. r ≠ SOME (Halt w) then
          state_rel jump off k s' t2'
       else t2'.ffi = s'.ffi`
  by (
    first_x_assum match_mp_tac
    \\ simp[]
    \\ ONCE_REWRITE_TAC[CONJ_COMM]
    \\ asm_exists_tac
    \\ simp[]
    \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[Abbr`s'`] )
  \\ qhdtm_x_assum`evaluate`mp_tac
  \\ drule (GEN_ALL evaluate_add_clock)
  \\ disch_then(qspec_then`ck'`mp_tac)
  \\ simp[] \\ ntac 2 strip_tac
  \\ qexists_tac`ck+ck'`\\simp[]
  \\ qhdtm_x_assum`COND`mp_tac
  \\ simp[Abbr`s'`]
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  \\ rveq \\ simp[]);

val state_rel_mem_load_imp = Q.store_thm("state_rel_mem_load_imp",
  `state_rel jump off k s t ∧
   mem_load x s = SOME w ⇒
   mem_load x t = SOME w`,
  srw_tac[][state_rel_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[mem_load_def]
  \\ drule fun2set_STAR_IMP \\ strip_tac
  \\ drule fun2set_STAR_IMP \\ strip_tac
  \\ drule fun2set_STAR_IMP \\ strip_tac
  \\ full_simp_tac(srw_ss())[memory_def]
  \\ full_simp_tac(srw_ss())[fun2set_def,EXTENSION,PULL_EXISTS,EXISTS_PROD,FORALL_PROD]
  \\ metis_tac[]);

val state_rel_word_exp = Q.store_thm("state_rel_word_exp",
  `∀s e w.
   state_rel jump off k s t ∧
   reg_bound_exp e k ∧
   word_exp s e = SOME w ⇒
   word_exp t e = SOME w`,
  ho_match_mp_tac word_exp_ind
  \\ simp[word_exp_def]
  \\ srw_tac[][]
  \\ imp_res_tac state_rel_mem_load_imp
  \\ full_simp_tac(srw_ss())[state_rel_def]
  \\ TRY(
    qpat_x_assum`_ = SOME w`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ strip_tac \\ rveq)
  >- ( res_tac \\ simp[] )
  >- (
    full_simp_tac(srw_ss())[EVERY_MEM,MEM_MAP,PULL_EXISTS,IS_SOME_EXISTS]
    \\ metis_tac[] )
  >- (
    first_x_assum(CHANGED_TAC o SUBST1_TAC o GSYM)
    \\ AP_TERM_TAC
    \\ simp[MAP_EQ_f,MAP_MAP_o]
    \\ full_simp_tac(srw_ss())[EVERY_MEM,MEM_MAP,PULL_EXISTS,IS_SOME_EXISTS]
    \\ metis_tac[]));

val memory_write = Q.store_thm("memory_write",
  `x IN sd /\ x IN dm /\
  (memory sm sd * p) (fun2set (m,dm)) ==>
  (memory ((x =+ y) sm) sd * p) (fun2set ((x =+ y) m,dm))`,
  srw_tac[][STAR_def,memory_def]
  \\ qexists_tac`v` \\ simp[]
  \\ full_simp_tac(srw_ss())[SPLIT_def]
  \\ full_simp_tac(srw_ss())[EXTENSION,IN_DISJOINT,IN_fun2set,FORALL_PROD]
  \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
  \\ metis_tac[]);

val state_rel_mem_store = Q.store_thm("state_rel_mem_store",
  `state_rel jump off k s t ∧
   mem_store x y s = SOME s' ∧
   mem_store x y t = SOME t' ⇒
   state_rel jump off k s' t'`,
  full_simp_tac(srw_ss())[mem_store_def] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[state_rel_def]
  \\ conj_tac >- metis_tac[]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[GSYM STAR_ASSOC]
  \\ match_mp_tac memory_write
  \\ full_simp_tac(srw_ss())[]);

val state_rel_mem_store_byte_aux = Q.store_thm("state_rel_mem_store_byte_aux",
  `state_rel jump off k s t ∧ mem_store_byte_aux s.memory s.mdomain s.be a b = SOME z ⇒
   ∃y. mem_store_byte_aux t.memory t.mdomain t.be a b = SOME y ∧
       state_rel jump off k (s with memory := z) (t with memory := y)`,
  rw[state_rel_def,wordSemTheory.mem_store_byte_aux_def]
  \\ ntac 2 (pop_assum mp_tac)
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ strip_tac
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ strip_tac
  \\ fs[GSYM STAR_ASSOC]
  \\ drule (GEN_ALL memory_fun2set_IMP_read)
  \\ disch_then drule
  \\ strip_tac \\ simp[]
  \\ rveq
  \\ simp[CONJ_ASSOC]
  \\ conj_tac >- metis_tac[]
  \\ match_mp_tac memory_write
  \\ simp[]);

val state_rel_get_fp_var = Q.prove(`
  state_rel jump off k s t ⇒
  get_fp_var n s = get_fp_var n t`,
  fs[state_rel_def,get_fp_var_def]);

val state_rel_set_fp_var = Q.prove(`
  state_rel jump off k s t ⇒
  state_rel jump off k (set_fp_var n v s) (set_fp_var n v t)`,
  rw[state_rel_def,set_fp_var_def]>>rfs[]);

val state_rel_inst = Q.store_thm("state_rel_inst",
  `state_rel jump off k s t ∧
   reg_bound_inst i k ∧
   inst i s = SOME s'
   ⇒
   ∃t'.
     inst i t = SOME t' ∧
     state_rel jump off k s' t'`,
  simp[inst_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ full_simp_tac(srw_ss())[]
  \\ strip_tac
  \\ rveq \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[assign_def]
  >- (
    pop_assum mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ strip_tac
    \\ imp_res_tac state_rel_word_exp
    \\ first_x_assum(qspec_then`Const c`mp_tac)
    \\ simp_tac(srw_ss())[]
    \\ disch_then drule
    \\ simp_tac(srw_ss())[]
    \\ rveq \\ simp[])
  >- (
    reverse BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[] >>
    TRY
      (qmatch_goalsub_rename_tac`get_vars _ _`>>
      fs[get_vars_def]
      \\ every_case_tac \\ fs[]
      \\ imp_res_tac state_rel_get_var \\ fs[]
      \\ rw[] \\ fs[] )
    >- (
      drule state_rel_word_exp
      \\ qpat_x_assum`_ = SOME _`mp_tac
      \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
      \\ strip_tac
      \\ ONCE_REWRITE_TAC[CONJ_COMM]
      \\ disch_then drule
      \\ srw_tac[][] )
    \\ qpat_abbrev_tac`c ⇔ _ ∧ _`
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    >- (
      imp_res_tac state_rel_get_var
      \\ full_simp_tac(srw_ss())[get_var_def]
      \\ BasicProvers.CASE_TAC \\ full_simp_tac(srw_ss())[]
      \\ srw_tac[][] )
    \\ pop_assum mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ strip_tac
    \\ drule state_rel_word_exp
    \\ ONCE_REWRITE_TAC[CONJ_COMM]
    \\ disch_then drule
    \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ srw_tac[][] )
  >- (
    BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ pop_assum mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ drule state_rel_word_exp
    \\ ONCE_REWRITE_TAC[CONJ_COMM]
    \\ disch_then drule
    \\ simp[]
    \\ imp_res_tac mem_load_byte_aux_IMP \\ fs[]
    >> TRY (
      imp_res_tac state_rel_mem_load_imp
      \\ simp[] \\ srw_tac[][] \\ srw_tac[][] \\ NO_TAC)
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ TRY BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac state_rel_get_var
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ TRY (
      qmatch_assum_rename_tac`mem_store x y s = SOME s'`
      \\ `∃t'. mem_store x y t = SOME t'`
      by (
        full_simp_tac(srw_ss())[mem_store_def]
        \\ full_simp_tac(srw_ss())[state_rel_def]
        \\ every_case_tac \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[GSYM STAR_ASSOC]
        \\ drule (GEN_ALL memory_fun2set_IMP_read)
        \\ metis_tac[] )
      \\ simp[]
      \\ imp_res_tac state_rel_mem_store)
    \\ drule (GEN_ALL state_rel_mem_store_byte_aux)
    \\ disch_then drule
    \\ strip_tac \\ simp[])
  >>
    BasicProvers.TOP_CASE_TAC \\ fs[] \\ every_case_tac \\
    imp_res_tac state_rel_get_fp_var>>fs[]>>
    imp_res_tac state_rel_get_var >> fs[]>>
    rw[]>>fs[state_rel_set_var,state_rel_set_fp_var]>>
    rfs[]);

val stack_write = Q.store_thm("stack_write",
  `∀stack base p m d a v.
   (word_list base stack * p) (fun2set (m,d)) ∧ a < LENGTH stack ⇒
   (word_list base (LUPDATE v a stack) * p) (fun2set ((base + bytes_in_word * (n2w a) =+ v) m,d))`,
  Induct \\ simp[word_list_def] \\ srw_tac[][]
  \\ Cases_on`a`\\full_simp_tac(srw_ss())[LUPDATE_def]
  \\ full_simp_tac(srw_ss())[word_list_def] >- SEP_W_TAC
  \\ SEP_F_TAC
  \\ disch_then drule
  \\ simp[ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ srw_tac[star_ss][]);

val state_rel_stack_store = Q.store_thm("state_rel_stack_store",
  `state_rel jump off k s t ∧ st = s.stack ∧
   FLOOKUP t.regs k = SOME (Word b) ∧
   s.stack_space + n < LENGTH st ∧
   b + bytes_in_word * n2w n = a
   ⇒
   state_rel jump off k (s with stack := LUPDATE x (n + s.stack_space) st)
     (t with memory := (a =+ x) t.memory)`,
  simp[state_rel_def]
  \\ strip_tac
  \\ conj_tac >- metis_tac[]
  \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ rveq
  \\ REWRITE_TAC[GSYM WORD_LEFT_ADD_DISTRIB,GSYM WORD_ADD_ASSOC,word_add_n2w]
  \\ REWRITE_TAC[Once STAR_COMM]
  \\ REWRITE_TAC[Once ADD_COMM]
  \\ match_mp_tac stack_write
  \\ fsrw_tac[star_ss][AC ADD_COMM ADD_ASSOC]);

val lsl_word_shift = Q.store_thm("lsl_word_shift",
  `good_dimindex (:'a) ==>
    w ≪ word_shift (:α) = w * bytes_in_word:'a word`,
  srw_tac[][WORD_MUL_LSL,word_shift_def,bytes_in_word_def,
      labPropsTheory.good_dimindex_def]);

val get_labels_stack_free = Q.prove(
  `!k n. get_labels (stack_free k n) = {}`,
  recInduct stack_free_ind \\ rw []
  \\ once_rewrite_tac [stack_free_def] \\ rw []
  \\ fs [get_labels_def,single_stack_free_def]);

val get_labels_stack_alloc = Q.prove(
  `!jump k n. get_labels (stack_alloc jump k n) = {}`,
  recInduct stack_alloc_ind \\ rw []
  \\ once_rewrite_tac [stack_alloc_def] \\ rw []
  \\ fs [get_labels_def,single_stack_alloc_def]
  \\ IF_CASES_TAC \\ fs[get_labels_def,halt_inst_def]);

val get_labels_upshift = Q.prove(
  `!n n0. get_labels (upshift n n0) = {}`,
  recInduct upshift_ind \\ rw []
  \\ once_rewrite_tac [upshift_def] \\ rw []
  \\ fs [get_labels_def]);

val get_labels_downshift = Q.prove(
  `!n n0. get_labels (downshift n n0) = {}`,
  recInduct downshift_ind \\ rw []
  \\ once_rewrite_tac [downshift_def] \\ rw []
  \\ fs [get_labels_def]);

val get_labels_comp = Q.store_thm("get_labels_comp",
  `!jump off k e. get_labels (comp jump off k e) = get_labels e`,
  recInduct comp_ind \\ rw [] \\ Cases_on `p`
  \\ once_rewrite_tac [comp_def] \\ fs [get_labels_def] \\ rw []
  \\ fs [get_labels_def,list_Seq_def]
  \\ every_case_tac
  \\ fs [get_labels_stack_alloc,get_labels_stack_free,stack_store_def,stack_load_def,get_labels_def]
  \\ metis_tac[get_labels_upshift,get_labels_downshift])

val code_rel_loc_check = Q.store_thm("code_rel_loc_check",
  `code_rel jump off k c1 c2 /\ loc_check c1 (l1,l2) ==> loc_check c2 (l1,l2)`,
  fs [loc_check_def,code_rel_def,domain_lookup,PULL_EXISTS] \\ rw []
  \\ res_tac \\ fs [] \\ disj2_tac
  \\ asm_exists_tac \\ fs [get_labels_comp]);

val evaluate_single_stack_free = Q.store_thm("evaluate_single_stack_free",
  `state_rel jump off k s t1 ∧
   ((r,s2) = (NONE, s with stack_space := s.stack_space + n)) ∧
   ¬(LENGTH s.stack < s.stack_space + n) ∧
   n ≠ 0 ∧ n ≤ max_stack_alloc
   ⇒
   ∃ck t2.
     evaluate (single_stack_free k n,t1 with clock := t1.clock + ck) = (r,t2) ∧ state_rel jump off k s2 t2`,
  simp[single_stack_free_def,evaluate_def,inst_def,assign_def,word_exp_def,
       wordLangTheory.word_op_def,GSYM get_var_def]
  \\ strip_tac
  \\ imp_res_tac state_rel_get_var_k
  \\ simp[]
  \\ full_simp_tac(srw_ss())[get_var_def,set_var_def,FLOOKUP_UPDATE]
  \\ simp[]
  \\ simp[labSemTheory.word_cmp_def,asmTheory.word_cmp_def]
  \\ full_simp_tac(srw_ss())[state_rel_def]
  \\ simp[FLOOKUP_UPDATE]
  \\ rw[] >> TRY (metis_tac[])
  \\ simp[word_offset_def,bytes_in_word_def,word_mul_n2w,word_add_n2w]
  \\ simp[RIGHT_ADD_DISTRIB,GSYM word_add_n2w])

val evaluate_stack_free = Q.store_thm("evaluate_stack_free",
  `∀k n r s s2 t1.
   evaluate (StackFree n,s) = (r,s2) ∧ r ≠ SOME Error ∧
   state_rel jump off k s t1
   ⇒
   ∃ck t2.
     evaluate (stack_free k n,t1 with clock := ck + t1.clock) = (r,t2) ∧
     state_rel jump off k s2 t2`,
  ho_match_mp_tac stack_free_ind
  \\ srw_tac[][stackSemTheory.evaluate_def]
  \\ simp[Once stack_free_def]
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  >- (
    srw_tac[][evaluate_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[]
    \\ srw_tac[][] \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ metis_tac[])
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  >- (
    every_case_tac>>fs[]>>
    drule evaluate_single_stack_free>> rw[])
  \\ simp[evaluate_def]
  \\ drule (GEN_ALL evaluate_single_stack_free)
  \\ disch_then(qspec_then`max_stack_alloc`mp_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars["n"])))
  \\ simp[]>>
  qpat_assum`A=(r,s2)` mp_tac>>
  IF_CASES_TAC>>fs[]>>
  qpat_assum`A=(r,s2)` mp_tac>>
  IF_CASES_TAC>>fs[]>>
  impl_keep_tac >- EVAL_TAC>>
  strip_tac>>
  qabbrev_tac`s' = s with stack_space := max_stack_alloc + s.stack_space`>>
  `∃ck'. ∃t2'. evaluate (stack_free k (n - max_stack_alloc), t2 with clock := ck' + t2.clock) = (r,t2') ∧ state_rel jump off k s2 t2'`
  by (
    first_x_assum match_mp_tac >>
    qexists_tac`s'` >> simp[Abbr`s'`]>>rw[])
  \\ qhdtm_x_assum`evaluate`mp_tac
  \\ drule (GEN_ALL evaluate_add_clock)
  \\ disch_then(qspec_then`ck'`mp_tac)
  \\ rveq \\ fs[]
  \\ ntac 2 strip_tac
  \\ qexists_tac`ck+ck'`\\simp[]);

val evaluate_upshift = Q.prove(`
  ∀r n st w.
  FLOOKUP st.regs r = SOME (Word w) ⇒
  evaluate(upshift r n,st) = (NONE, st with regs := st.regs |+ (r,Word (w + word_offset n)))`,
  ho_match_mp_tac upshift_ind>>rw[]>>
  simp[Once upshift_def]>>IF_CASES_TAC>>
  simp[evaluate_def,inst_def,assign_def,word_exp_def,wordLangTheory.word_op_def,set_var_def]>>
  qpat_abbrev_tac`st' = st with regs := _`>>fs[]>>
  first_x_assum(qspecl_then[`st'`,`w+word_offset max_stack_alloc`] mp_tac)>>
  fs[Abbr`st'`,set_var_def,FLOOKUP_UPDATE]>>rw[]>>
  simp[evaluate_def,inst_def,assign_def,word_exp_def,FLOOKUP_UPDATE,wordLangTheory.word_op_def,set_var_def]>>
  simp[state_component_equality,FUPD11_SAME_KEY_AND_BASE,word_offset_def]>>
  FULL_SIMP_TAC std_ss [Once (GSYM WORD_ADD_ASSOC),word_add_n2w]>>
  FULL_SIMP_TAC std_ss [GSYM RIGHT_ADD_DISTRIB]>>
  simp[])

val evaluate_downshift = Q.prove(`
  ∀r n st w.
  FLOOKUP st.regs r = SOME (Word w) ⇒
  evaluate(downshift r n,st) = (NONE, st with regs := st.regs |+ (r,Word (w - word_offset n)))`,
  ho_match_mp_tac downshift_ind>>rw[]>>
  simp[Once downshift_def]>>IF_CASES_TAC>>
  simp[evaluate_def,inst_def,assign_def,word_exp_def,wordLangTheory.word_op_def,set_var_def]>>
  qpat_abbrev_tac`st' = st with regs := _`>>fs[]>>
  first_x_assum(qspecl_then[`st'`,`w - 1w * word_offset max_stack_alloc`] mp_tac)>>
  fs[Abbr`st'`,set_var_def,FLOOKUP_UPDATE]>>rw[]>>
  simp[evaluate_def,inst_def,assign_def,word_exp_def,FLOOKUP_UPDATE,wordLangTheory.word_op_def,set_var_def]>>
  simp[state_component_equality,FUPD11_SAME_KEY_AND_BASE,word_offset_def]>>
  FULL_SIMP_TAC std_ss [Once (GSYM WORD_ADD_ASSOC),word_add_n2w]>>
  simp[]>>
  FULL_SIMP_TAC std_ss [GSYM WORD_LEFT_ADD_DISTRIB]>>
  FULL_SIMP_TAC std_ss [Once (GSYM WORD_ADD_ASSOC),word_add_n2w]>>
  FULL_SIMP_TAC std_ss [GSYM RIGHT_ADD_DISTRIB]>>
  simp[])

val name_cases = prove(
  ``!name. name <> CurrHeap ==> MEM name store_list``,
  Cases_on `name` \\ fs [store_list_def]
  \\ CCONTR_TAC \\ fs [] \\ Cases_on `c`
  \\ full_simp_tac std_ss [n2w_11,EVAL ``dimword (:5)``]
  \\ ntac 16 (Cases_on `n` \\ full_simp_tac std_ss [ADD1]
              \\ Cases_on `n'` \\ full_simp_tac std_ss [ADD1,GSYM ADD_ASSOC])
  \\ pop_assum mp_tac \\ rpt (pop_assum kall_tac) \\ decide_tac);

(* Significantly faster than SEP_R_TAC *)
val mem_load_lemma = Q.prove(`
  MEM name store_list ∧
  FLOOKUP (s:('a,'b)state).store name = SOME x ∧
  (memory s.memory s.mdomain *
        word_list
          (the_SOME_Word (FLOOKUP s.store BitmapBase) ≪ word_shift (:α))
          (MAP Word s.bitmaps) * word_store c s.store *
        word_list c s.stack) (fun2set (t1.memory,(t1:('a,'b) state).mdomain)) ⇒
  mem_load (c+store_offset name) t1 = SOME x`,
  strip_tac >>
  drule fun2set_STAR_IMP>>
  pop_assum kall_tac >> strip_tac >> pop_assum kall_tac >>
  drule fun2set_STAR_IMP>>
  simp[Once CONJ_COMM]>>
  pop_assum kall_tac >> strip_tac >>  pop_assum kall_tac>>
  ntac 2 (pop_assum mp_tac)>>
  simp[store_offset_def,store_pos_def,word_offset_def,word_offset_def,INDEX_FIND_def
    ,word_store_def,GSYM word_mul_n2w, store_list_def
    ,word_list_rev_def,bytes_in_word_def] \\ rfs[] \\
  strip_tac>>
  ntac 43 (
  IF_CASES_TAC>>simp[Once one_fun2set]>>
  qmatch_abbrev_tac `P ∧ Q ∧ R ⇒ _`>>
  strip_tac
  >-
    simp[Abbr`P`,Abbr`Q`,mem_load_def]
  >>
  qpat_x_assum`P` kall_tac>> qpat_x_assum`Q` kall_tac>>
  qpat_x_assum`Abbrev (P ⇔ _)` kall_tac>>
  qpat_x_assum`Abbrev (Q ⇔ _)` kall_tac>>
  fs[Abbr`R`]>>
  pop_assum mp_tac)>>
  fs[store_list_def]);

(* basically the same thing, but without the read assumption *)
val mem_load_lemma2 = Q.prove(`
  MEM name store_list ∧
  (memory s.memory s.mdomain *
        word_list
          (the_SOME_Word (FLOOKUP s.store BitmapBase) ≪ word_shift (:α))
          (MAP Word s.bitmaps) * word_store c s.store *
        word_list c s.stack) (fun2set (t1.memory,(t1:('a,'b) state).mdomain)) ⇒
  c+store_offset name ∈ t1.mdomain`,
  strip_tac >>
  drule fun2set_STAR_IMP>>
  pop_assum kall_tac >> strip_tac >> pop_assum kall_tac >>
  drule fun2set_STAR_IMP>>
  simp[Once CONJ_COMM]>>
  pop_assum kall_tac >> strip_tac >>  pop_assum kall_tac>>
  pop_assum mp_tac>>
  simp[store_offset_def,store_pos_def,word_offset_def,word_offset_def,INDEX_FIND_def
    ,word_store_def,GSYM word_mul_n2w, store_list_def
    ,word_list_rev_def,bytes_in_word_def] \\ rfs[] \\
  ntac 43(
  IF_CASES_TAC>>simp[Once one_fun2set]>>
  qmatch_abbrev_tac `P ∧ Q ∧ R ⇒ _`>>
  strip_tac>>
  qpat_x_assum`P` kall_tac>> qpat_x_assum`Q` kall_tac>>
  qpat_x_assum`Abbrev (P ⇔ _)` kall_tac>>
  qpat_x_assum`Abbrev (Q ⇔ _)` kall_tac>>
  fs[Abbr`R`]>>
  pop_assum mp_tac)>>
  fs[store_list_def])

val assoc_lem = Q.prove(`
  (A:(('a -> bool) -> bool) * B) * C =
  (B * C) * A`,
  metis_tac[STAR_ASSOC,STAR_COMM])

val write_fun2set2 = write_fun2set |> SIMP_RULE std_ss [GSYM STAR_COMM]

val store_write_lemma = Q.prove(`
  MEM name store_list ∧
  (memory s.memory s.mdomain *
        word_list
          (the_SOME_Word (FLOOKUP s.store BitmapBase) ≪ word_shift (:α))
          (MAP Word s.bitmaps) * word_store c s.store *
        word_list c s.stack) (fun2set (m,d)) ⇒
  (memory s.memory s.mdomain *
 word_list
   (the_SOME_Word (FLOOKUP s.store BitmapBase) ≪ word_shift (:α))
   (MAP Word s.bitmaps) * word_store c (s.store |+ (name,x)) *
 word_list c s.stack) (fun2set ((c + store_offset name =+ x) m,d))`,
  strip_tac>>
  pop_assum mp_tac>>
  qmatch_goalsub_abbrev_tac`A * B * C`>>
  `A * B * C = B * (A * C)` by
    metis_tac[STAR_ASSOC,STAR_COMM]>>
  pop_assum SUBST_ALL_TAC>>
  qmatch_goalsub_abbrev_tac`A * B' * C`>>
  `A * B' * C = B' * (A * C)` by
    metis_tac[STAR_ASSOC,STAR_COMM]>>
  pop_assum SUBST_ALL_TAC>>
  qabbrev_tac`Z = (A*C)`>>
  fs[Abbr`B`,Abbr`B'`]>>
  simp[store_offset_def,store_pos_def,word_offset_def,word_offset_def,INDEX_FIND_def
      ,word_store_def,GSYM word_mul_n2w, store_list_def
      ,word_list_rev_def,bytes_in_word_def] \\ rfs[] \\
  simp[Once assoc_lem]>>strip_tac>>
  simp[Once assoc_lem]>>
  IF_CASES_TAC >> fs[]
  >-
    (rveq>>
    simp[FLOOKUP_UPDATE]>>
    match_mp_tac write_fun2set2>>
    qmatch_asmsub_abbrev_tac`(_* one(_,vv)) _`>>
    qexists_tac`vv`>>
    first_x_assum ACCEPT_TAC)
  >>
  ntac 42(
  qpat_x_assum` _ (fun2set _)` mp_tac>>
  simp[Once (GSYM STAR_ASSOC)]>>
  simp[Once assoc_lem]>>strip_tac>>
  simp[Once (GSYM STAR_ASSOC)]>>
  simp[Once assoc_lem]>>
  IF_CASES_TAC >> fs[]
  >-
    (rveq>>
    simp[FLOOKUP_UPDATE]>>
    match_mp_tac write_fun2set2>>
    qmatch_asmsub_abbrev_tac`(_* one(_,vv)) _`>>
    qexists_tac`vv`>>
    first_x_assum ACCEPT_TAC))>>
  fs[store_list_def]);

val comp_correct = Q.prove(
  `!p s1 r s2 t1 k off jump.
     evaluate (p,s1) = (r,s2) /\ r <> SOME Error /\
     state_rel jump off k s1 t1 /\ reg_bound p k ==>
     ?ck t2. evaluate (comp jump off k p,t1 with clock := ck + t1.clock) = (r,t2) /\
             (case r of
               | SOME (Halt _) => t2.ffi = s2.ffi
               | SOME TimeOut => t2.ffi = s2.ffi
               | _ =>  (state_rel jump off k s2 t2))`,
  recInduct evaluate_ind \\ rpt strip_tac
  THEN1 (full_simp_tac(srw_ss())[comp_def,evaluate_def] \\ rpt var_eq_tac \\ qexists_tac`0` \\ full_simp_tac(srw_ss())[])
  THEN1
   (full_simp_tac(srw_ss())[comp_def,evaluate_def,reg_bound_def]
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac`0`
    \\ BasicProvers.TOP_CASE_TAC \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[state_rel_def])
  THEN1 (full_simp_tac(srw_ss())[comp_def,evaluate_def] \\ full_simp_tac(srw_ss())[state_rel_def])
  THEN1 (
    full_simp_tac(srw_ss())[comp_def,evaluate_def]
    \\ last_x_assum mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ strip_tac \\ rveq
    \\ drule (GEN_ALL state_rel_inst)
    \\ full_simp_tac(srw_ss())[reg_bound_def]
    \\ disch_then drule
    \\ disch_then drule
    \\ strip_tac
    \\ simp[]
    \\ imp_res_tac inst_const
    \\ qexists_tac`0` \\ simp[]
    \\ metis_tac[with_same_clock])
  THEN1 (* Get *)
   (qexists_tac`0`
    \\ `s.use_store` by full_simp_tac(srw_ss())[state_rel_def]
    \\ full_simp_tac(srw_ss())[comp_def,evaluate_def,reg_bound_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[evaluate_def,inst_def,assign_def,word_exp_def,LET_DEF]
    THEN1 (`FLOOKUP t1.regs (k + 2) = SOME x` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[])
    \\ qpat_x_assum `state_rel jump off k s t1` mp_tac
    \\ simp [Once state_rel_def] \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ strip_tac
    \\ full_simp_tac(srw_ss())[wordLangTheory.word_op_def]
    \\ `mem_load (c + store_offset name) t1 = SOME x` by
     (drule name_cases>>
     strip_tac>>
     metis_tac[mem_load_lemma])
    \\ full_simp_tac(srw_ss())[] \\ res_tac
    \\ full_simp_tac(srw_ss())[] \\ match_mp_tac state_rel_set_var
    \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ full_simp_tac(srw_ss())[AC MULT_COMM MULT_ASSOC])
  THEN1 (* Set *)
   (qexists_tac`0`
    \\ `s.use_store` by full_simp_tac(srw_ss())[state_rel_def]
    \\ full_simp_tac(srw_ss())[comp_def,evaluate_def,reg_bound_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[evaluate_def,inst_def,assign_def,word_exp_def,LET_DEF,get_var_def]
    THEN1 (full_simp_tac(srw_ss())[state_rel_def,set_var_def,set_store_def,FLOOKUP_UPDATE]
           \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[word_store_def,word_store_CurrHeap]
           \\ srw_tac[][] \\ `F` by decide_tac \\ full_simp_tac(srw_ss())[])
    \\ qpat_x_assum `state_rel jump off k s t1` mp_tac
    \\ simp [Once state_rel_def] \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ strip_tac
    \\ full_simp_tac(srw_ss())[wordLangTheory.word_op_def,mem_store_def]
    \\ `c + store_offset name IN t1.mdomain` by
     (drule name_cases>>
     strip_tac>>
     metis_tac[mem_load_lemma2])
    \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[state_rel_def,set_store_def,FLOOKUP_UPDATE]
    \\ rev_full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[AC MULT_COMM MULT_ASSOC]
    \\ Q.ABBREV_TAC `m = t1.memory`
    \\ Q.ABBREV_TAC `d = t1.mdomain`
    \\ drule name_cases
    \\ metis_tac[store_write_lemma])
  THEN1 (* Tick *)
   (full_simp_tac(srw_ss())[comp_def,evaluate_def]
    \\ `s.clock = t1.clock` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac`0` \\ full_simp_tac(srw_ss())[]
    \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ imp_res_tac state_rel_IMP \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[state_rel_def])
  THEN1 (* Seq *)
   (full_simp_tac(srw_ss())[] \\ simp [Once comp_def]
    \\ full_simp_tac(srw_ss())[evaluate_def,reg_bound_def,LET_DEF]
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ reverse(Cases_on `res = NONE`) \\ full_simp_tac(srw_ss())[]
    >- (rpt var_eq_tac
      \\ first_x_assum drule >> simp[]
      \\ strip_tac >> full_simp_tac(srw_ss())[]
      \\ pop_assum mp_tac >> CASE_TAC
      \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[]
      \\ strip_tac
      \\ qexists_tac`ck`\\simp[])
    \\ first_x_assum drule >> simp[] >> strip_tac
    \\ first_x_assum drule \\ simp[] \\ strip_tac
    \\ ntac 2 (pop_assum mp_tac)
    \\ drule (GEN_ALL evaluate_add_clock)
    \\ disch_then(qspec_then`ck'`mp_tac)
    \\ simp[] \\ ntac 3 strip_tac
    \\ qexists_tac`ck+ck'`\\simp[])
  THEN1 (* Return *)
   (full_simp_tac(srw_ss())[comp_def,evaluate_def,reg_bound_def]
    \\ qexists_tac`0`
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[])
  THEN1 (* Raise *)
   (full_simp_tac(srw_ss())[comp_def,evaluate_def,reg_bound_def]
    \\ qexists_tac`0`
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[])
  THEN1 (* If *)
   (full_simp_tac(srw_ss())[] \\ simp [Once comp_def]
    \\ full_simp_tac(srw_ss())[evaluate_def,reg_bound_def]
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[]
    \\ qpat_x_assum`_ = (r,_)`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ strip_tac \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]
    \\ first_x_assum drule \\ simp[] \\ strip_tac
    \\ qexists_tac`ck` \\ simp[]
    \\ full_simp_tac(srw_ss())[get_var_def]
    \\ Cases_on `ri` \\ full_simp_tac(srw_ss())[get_var_imm_def]
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[])
  THEN1 (* While *)
   (qpat_x_assum `evaluate _ = _` mp_tac
    \\ simp [Once evaluate_def,get_var_def]
    \\ ntac 4 (BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[])
    \\ `get_var_imm ri s = get_var_imm ri t1 /\
        get_var r1 s = get_var r1 t1` by
     (Cases_on `ri` \\ full_simp_tac(srw_ss())[get_var_imm_def,reg_bound_def]
      \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[get_var_def])
    \\ reverse (BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[])
    THEN1
     (strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
      \\ qexists_tac `0`
      \\ simp [Once comp_def,evaluate_def]
      \\ full_simp_tac(srw_ss())[reg_bound_def,get_var_def])
    \\ strip_tac \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ rev_full_simp_tac(srw_ss())[get_var_def] \\ full_simp_tac(srw_ss())[]
    \\ qpat_x_assum `SOME (Word _) = _` (assume_tac o GSYM) \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `res <> NONE` \\ full_simp_tac(srw_ss())[]
    THEN1
     (rpt var_eq_tac \\ full_simp_tac(srw_ss())[] \\ simp [Once comp_def]
      \\ full_simp_tac(srw_ss())[evaluate_def,get_var_def,LET_THM]
      \\ rev_full_simp_tac(srw_ss())[] \\ first_x_assum drule \\ full_simp_tac(srw_ss())[reg_bound_def]
      \\ strip_tac \\ full_simp_tac(srw_ss())[]
      \\ qexists_tac `ck` \\ full_simp_tac(srw_ss())[])
    \\ Cases_on `s1.clock = 0` \\ full_simp_tac(srw_ss())[]
    THEN1
     (rpt var_eq_tac \\ full_simp_tac(srw_ss())[] \\ simp [Once comp_def]
      \\ full_simp_tac(srw_ss())[evaluate_def,get_var_def,LET_THM]
      \\ rev_full_simp_tac(srw_ss())[] \\ first_x_assum drule \\ full_simp_tac(srw_ss())[reg_bound_def]
      \\ strip_tac \\ full_simp_tac(srw_ss())[]
      \\ qexists_tac `ck` \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[state_rel_def])
    \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[] \\ simp [Once comp_def]
    \\ full_simp_tac(srw_ss())[evaluate_def,get_var_def,LET_THM] \\ full_simp_tac(srw_ss())[STOP_def]
    \\ first_x_assum drule \\ full_simp_tac(srw_ss())[reg_bound_def]
    \\ strip_tac \\ rev_full_simp_tac(srw_ss())[]
    \\ rename1 `state_rel jump off k s3 t3`
    \\ `state_rel jump off k (dec_clock s3) (dec_clock t3)` by
        (full_simp_tac(srw_ss())[state_rel_def,dec_clock_def] \\ rev_full_simp_tac(srw_ss())[] \\ NO_TAC)
    \\ first_x_assum drule \\ full_simp_tac(srw_ss())[]
    \\ strip_tac \\ full_simp_tac(srw_ss())[] \\ ntac 2 (pop_assum mp_tac)
    \\ drule (GEN_ALL evaluate_add_clock) \\ full_simp_tac(srw_ss())[]
    \\ disch_then (qspec_then `ck'` assume_tac)
    \\ simp [Once comp_def] \\ rpt strip_tac \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac `ck+ck'` \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
    \\ `t3.clock <> 0` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[dec_clock_def]
    \\ `ck' + (t3.clock - 1) = ck' + t3.clock - 1` by decide_tac \\ full_simp_tac(srw_ss())[])
  THEN1 (* JumpLower *)
   (simp [Once comp_def]
    \\ full_simp_tac(srw_ss())[reg_bound_def,evaluate_def]
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[find_code_def]
    \\ Cases_on `get_var r1 t1` \\ full_simp_tac(srw_ss())[] \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `get_var r2 t1` \\ full_simp_tac(srw_ss())[] \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `word_cmp Lower c c'`) \\ full_simp_tac(srw_ss())[] THEN1 (
      srw_tac[][] \\ qexists_tac`0`\\simp[])
    \\ Cases_on `lookup dest s.code` \\ full_simp_tac(srw_ss())[]
    \\ `lookup dest t1.code = SOME (comp jump off k x) /\
        reg_bound x k /\ s.clock = t1.clock` by
     (qpat_x_assum `bb ==> bbb` (K all_tac)
      \\ full_simp_tac(srw_ss())[state_rel_def,code_rel_def] \\ res_tac \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[])
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `t1.clock = 0` \\ full_simp_tac(srw_ss())[]
    THEN1 (srw_tac[][] \\ qexists_tac`t1.clock` \\ full_simp_tac(srw_ss())[state_rel_def,code_rel_def])
    \\ split_pair_case_tac \\ fs[]
    \\ Cases_on `v` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
    \\ `state_rel jump off k (dec_clock s) (dec_clock t1)` by metis_tac [state_rel_IMP]
    \\ res_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ qexists_tac`ck`
    \\ fsrw_tac[ARITH_ss][get_var_def,dec_clock_def]
    \\ rev_full_simp_tac(srw_ss()++ARITH_ss)[])
  THEN1 (* Call *)
   (Cases_on `ret` \\ full_simp_tac(srw_ss())[] THEN1
     (full_simp_tac(srw_ss())[evaluate_def]
      \\ Cases_on `find_code dest s.regs s.code` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `handler` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] THEN1
       (qexists_tac`0`
        \\ full_simp_tac(srw_ss())[evaluate_def,Once comp_def,reg_bound_def]
        \\ imp_res_tac find_code_lemma \\ full_simp_tac(srw_ss())[] \\ pop_assum (K all_tac)
        \\ full_simp_tac(srw_ss())[state_rel_def,code_rel_def])
      \\ Cases_on `evaluate (x,dec_clock s)` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `q` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
      \\ simp [evaluate_def,Once comp_def,reg_bound_def]
      \\ full_simp_tac(srw_ss())[reg_bound_def]
      \\ `find_code dest t1.regs t1.code = SOME (comp jump off k x) /\ reg_bound x k` by
           (match_mp_tac find_code_lemma \\ full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
      \\ `t1.clock <> 0` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[]
      \\ `state_rel jump off k (dec_clock s) (dec_clock t1)` by
       (full_simp_tac(srw_ss())[state_rel_def,dec_clock_def] \\ rev_full_simp_tac(srw_ss())[] \\ metis_tac [])
      \\ first_x_assum drule \\ full_simp_tac(srw_ss())[]
      \\ strip_tac \\ full_simp_tac(srw_ss())[]
      \\ qexists_tac`ck`
      \\ rev_full_simp_tac(srw_ss()++ARITH_ss)[dec_clock_def])
    \\ PairCases_on `x` \\ full_simp_tac(srw_ss())[reg_bound_def]
    \\ simp[Once comp_def]
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[Once evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ drule (GEN_ALL find_code_lemma2)
    \\ disch_then drule
    \\ disch_then drule
    \\ strip_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      strip_tac \\ rveq
      \\ simp[evaluate_def]
      \\ qexists_tac`0`\\simp[]
      \\ `t1.clock = 0` by fs[state_rel_def]
      \\ simp[] \\ fs[state_rel_def] )
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ simp[Once evaluate_def]
    \\ `t1.clock = s.clock` by fs[state_rel_def]
    \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ qmatch_assum_rename_tac`_ = (SOME res,_)`
    \\ Cases_on`res = TimeOut` \\ fs[]
    >- (
      strip_tac \\ rveq \\ fs[]
      \\ qmatch_asmsub_abbrev_tac`state_rel _ _ _ ss _`
      \\ (fn g => subterm (fn tm => (sg `state_rel jump off k ss (^tm with clock := s.clock - 1)`) g) (#2 g))
      >- (
        simp[Abbr`ss`,dec_clock_def]
        \\ match_mp_tac state_rel_with_clock
        \\ match_mp_tac state_rel_set_var
        \\ simp[] )
      \\ first_x_assum drule
      \\ simp[]
      \\ strip_tac
      \\ fs[dec_clock_def]
      \\ qexists_tac`ck'`\\simp[] )
    \\ Cases_on`∃w. res = Halt w` \\ fs[]
    >- (
      strip_tac \\ rveq \\ fs[]
      \\ qmatch_asmsub_abbrev_tac`state_rel _ _ _ ss _`
      \\ (fn g => subterm (fn tm => (sg `state_rel jump off k ss (^tm with clock := s.clock - 1)`) g) (#2 g))
      >- (
        simp[Abbr`ss`,dec_clock_def]
        \\ match_mp_tac state_rel_with_clock
        \\ match_mp_tac state_rel_set_var
        \\ simp[] )
      \\ first_x_assum drule
      \\ simp[]
      \\ strip_tac
      \\ fs[dec_clock_def]
      \\ qexists_tac`ck'`\\simp[] )
    \\ Cases_on`∃l. res = Result l` \\ fs[]
    >- (
      BasicProvers.TOP_CASE_TAC \\ fs[]
      \\ strip_tac \\ fs[] \\ rfs[]
      \\ qmatch_asmsub_abbrev_tac`state_rel _ _ _ (dec_clock sss) _`
      \\ qabbrev_tac`ss = dec_clock sss`
      \\ (fn g => subterm (fn tm => (sg `state_rel jump off k ss (^tm with clock := s.clock - 1)`) g) (#2 g))
      >- (
        simp[Abbr`ss`,dec_clock_def,Abbr`sss`]
        \\ match_mp_tac state_rel_with_clock
        \\ match_mp_tac state_rel_set_var
        \\ simp[] )
      \\ first_x_assum drule \\ simp[] \\ strip_tac
      \\ first_x_assum drule \\ simp[] \\ strip_tac
      \\ fs[dec_clock_def]
      \\ qhdtm_x_assum`evaluate`mp_tac
      \\ qmatch_goalsub_rename_tac`ck2 + t2.clock`
      \\ drule (GEN_ALL evaluate_add_clock)
      \\ disch_then(qspec_then`ck2`mp_tac)
      \\ simp[] \\ ntac 2 strip_tac
      \\ qexists_tac`ck' + ck2` \\  simp[] )
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      strip_tac \\ rveq
      \\ qmatch_asmsub_abbrev_tac`state_rel _ _ _ ss _`
      \\ (fn g => subterm (fn tm => (sg `state_rel jump off k ss (^tm with clock := s.clock - 1)`) g) (#2 g))
      >- (
        simp[Abbr`ss`,dec_clock_def]
        \\ match_mp_tac state_rel_with_clock
        \\ match_mp_tac state_rel_set_var
        \\ simp[] )
      \\ first_x_assum drule
      \\ simp[]
      \\ strip_tac
      \\ fs[dec_clock_def]
      \\ qexists_tac`ck'`\\simp[] )
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ strip_tac \\ fs[] \\ rfs[]
    \\ qmatch_asmsub_abbrev_tac`state_rel _ _ _ (dec_clock sss) _`
    \\ qabbrev_tac`ss = dec_clock sss`
    \\ (fn g => subterm (fn tm => (sg `state_rel jump off k ss (^tm with clock := s.clock - 1)`) g) (#2 g))
    >- (
      simp[Abbr`ss`,dec_clock_def,Abbr`sss`]
      \\ match_mp_tac state_rel_with_clock
      \\ match_mp_tac state_rel_set_var
      \\ simp[] )
    \\ first_x_assum drule \\ simp[] \\ strip_tac
    \\ first_x_assum drule \\ simp[] \\ strip_tac
    \\ fs[dec_clock_def]
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ qmatch_goalsub_rename_tac`ck2 + t2.clock`
    \\ drule (GEN_ALL evaluate_add_clock)
    \\ disch_then(qspec_then`ck2`mp_tac)
    \\ simp[] \\ ntac 2 strip_tac
    \\ qexists_tac`ck' + ck2` \\  simp[] )
  THEN1 (* FFI *)
   (simp [Once comp_def]
    \\ qexists_tac`0`
    \\ full_simp_tac(srw_ss())[reg_bound_def,evaluate_def]
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[]
    \\ qpat_x_assum `xxx = (r,s2)` mp_tac
    \\ rpt (BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[])
    \\ imp_res_tac read_bytearray_IMP_read_bytearray \\ full_simp_tac(srw_ss())[]
    \\ pop_assum kall_tac \\ srw_tac[][] \\ full_simp_tac(srw_ss())[LET_THM]
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ `t1.ffi = s.ffi` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[markerTheory.Abbrev_def] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_DRESTRICT]
    \\ rev_full_simp_tac(srw_ss())[] \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[GSYM STAR_ASSOC]
    \\ match_mp_tac write_bytearray_lemma \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac read_bytearray_LENGTH \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac call_FFI_LENGTH \\ full_simp_tac(srw_ss())[])
  THEN1 (* LocValue *)
   (full_simp_tac(srw_ss())[evaluate_def,Once comp_def] \\ srw_tac[][]
    \\ last_x_assum mp_tac \\ IF_CASES_TAC \\ rw[] \\ rw[]
    \\ reverse CASE_TAC
    THEN1 (fs [state_rel_def] \\ imp_res_tac code_rel_loc_check \\ fs [])
    \\ fs[state_rel_def,set_var_def,FLOOKUP_UPDATE,reg_bound_def]
    \\ `r <> k /\ r <> k+1 /\ r <> k+2` by decide_tac \\ full_simp_tac(srw_ss())[]
    \\ every_case_tac \\ rw[] \\ fs[] \\ res_tac \\ fs[] \\ rfs[])
  THEN1 (* StackAlloc *) (
    simp[comp_def]
    \\ drule evaluate_stack_alloc
    \\ simp[]
    \\ disch_then drule
    \\ strip_tac \\ simp[]
    \\ asm_exists_tac \\ simp[]
    \\ BasicProvers.CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[state_rel_def] )
  THEN1 (* StackFree *) (
    simp[comp_def]
    \\ drule evaluate_stack_free
    \\ simp[]
    \\ disch_then drule
    \\ strip_tac \\ simp[]
    \\ asm_exists_tac \\ simp[]
    \\ fs[evaluate_def]
    \\ every_case_tac \\ fs[])
  THEN1 (* StackLoad *) (
    simp[comp_def]
    \\ IF_CASES_TAC
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ strip_tac \\ rveq
    \\ simp[inst_def,assign_def,word_exp_def]
    \\ imp_res_tac state_rel_get_var_k
    \\ full_simp_tac(srw_ss())[get_var_def]
    \\ qexists_tac `0` \\ full_simp_tac(srw_ss())[]
    >-
      (simp[wordLangTheory.word_op_def]
      \\ simp[mem_load_def]
      \\ imp_res_tac LESS_LENGTH_IMP_APPEND
      \\ full_simp_tac(srw_ss())[word_list_APPEND,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
      \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th])
      \\ Cases_on `zs` \\ full_simp_tac(srw_ss())[word_list_def,word_offset_eq]
      \\ full_simp_tac(srw_ss())[EL_LENGTH_APPEND] \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[]
      \\ `set_var r h t1 with clock := t1.clock = set_var r h t1` by full_simp_tac(srw_ss())[set_var_def]
      \\ full_simp_tac(srw_ss())[] \\ match_mp_tac state_rel_set_var
      \\ full_simp_tac(srw_ss())[reg_bound_def])
    >>
      fs[stack_load_def,evaluate_def]>>
      qpat_abbrev_tac`t = (set_var r _ _) with clock:= _`>>
      `FLOOKUP t.regs r = SOME(Word (c + bytes_in_word * n2w s.stack_space))` by
        fs[Abbr`t`,set_var_def,FLOOKUP_UPDATE]>>
      drule evaluate_upshift>>
      disch_then (qspec_then `n` assume_tac)>>
      simp[inst_def,assign_def,word_exp_def,FLOOKUP_UPDATE,wordLangTheory.word_op_def]>>fs[Abbr`t`,set_var_def]>>
      simp[mem_load_def]
      \\ fsrw_tac[ARITH_ss][NOT_LESS]
      \\ imp_res_tac LESS_LENGTH_IMP_APPEND
      \\ full_simp_tac(srw_ss())[word_list_APPEND,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
      \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th])
      \\ Cases_on `zs` \\ full_simp_tac(srw_ss())[word_list_def,word_offset_eq]
      \\ full_simp_tac(srw_ss())[EL_LENGTH_APPEND] \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[]>>
      simp[GSYM set_var_def]>>
      match_mp_tac state_rel_set_var>>
      full_simp_tac(srw_ss())[reg_bound_def])
  THEN1 (* StackLoadAny *) (
    simp[comp_def]
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ strip_tac \\ rveq
    \\ simp[inst_def,assign_def,word_exp_def]
    \\ fs[reg_bound_def]
    \\ imp_res_tac state_rel_get_var
    \\ imp_res_tac state_rel_get_var_k
    \\ full_simp_tac(srw_ss())[get_var_def,set_var_def,FLOOKUP_UPDATE]
    \\ `r ≠ k` by fs[]
    \\ simp[wordLangTheory.word_op_def]
    \\ fs[FLOOKUP_UPDATE]
    \\ qexists_tac`0` \\ simp[]
    \\ simp[mem_load_def]
    \\ rpt(qpat_x_assum`∀x. _`kall_tac)
    \\ imp_res_tac LESS_LENGTH_IMP_APPEND
    \\ full_simp_tac(srw_ss())[word_list_APPEND]
    \\ Cases_on`zs` \\ full_simp_tac(srw_ss())[word_list_def]
    \\ full_simp_tac(srw_ss())[GSYM word_add_n2w]
    \\ full_simp_tac(srw_ss())[WORD_LEFT_ADD_DISTRIB]
    \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th,EL_LENGTH_APPEND])
    \\ `bytes_in_word * c >>> word_shift (:'a) = c` by
          rev_full_simp_tac(srw_ss())[lsl_word_shift,state_rel_def]
    \\ full_simp_tac(srw_ss())[] \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[]
    \\ simp[GSYM set_var_def])
  THEN1 (* StackStore *) (
    simp[comp_def]
    \\ IF_CASES_TAC
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ strip_tac \\ rveq
    \\ qexists_tac`0` \\ simp[]
    \\ full_simp_tac(srw_ss())[reg_bound_def]
    \\ imp_res_tac state_rel_get_var
    \\ imp_res_tac state_rel_get_var_k
    >-
      (simp[inst_def]
      \\ full_simp_tac(srw_ss())[]
      \\ simp[word_exp_def]
      \\ full_simp_tac(srw_ss())[get_var_def]
      \\ simp[wordLangTheory.word_op_def]
      \\ simp[mem_store_def]
      \\ full_simp_tac(srw_ss())[NOT_LESS_EQUAL]
      \\ imp_res_tac LESS_LENGTH_IMP_APPEND
      \\ full_simp_tac(srw_ss())[word_list_APPEND]
      \\ Cases_on`zs`\\full_simp_tac(srw_ss())[word_list_def]
      \\ full_simp_tac(srw_ss())[word_offset_eq,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
      \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[]
      \\ match_mp_tac (GEN_ALL state_rel_stack_store)
      \\ simp[])
    >>
      simp[stack_store_def,evaluate_def]>>
      fs[get_var_def]>>
      drule evaluate_upshift >> disch_then(qspec_then`n` assume_tac)>>
      simp[inst_def,word_exp_def,FLOOKUP_UPDATE,wordLangTheory.word_op_def]>>
      fs[get_var_def,FLOOKUP_UPDATE,set_var_def]>>
      simp[mem_store_def]>>
      full_simp_tac(srw_ss())[NOT_LESS_EQUAL]
      \\ simp[wordLangTheory.word_op_def]
      \\ simp[mem_store_def]
      \\ full_simp_tac(srw_ss())[NOT_LESS_EQUAL]
      \\ imp_res_tac LESS_LENGTH_IMP_APPEND
      \\ full_simp_tac(srw_ss())[word_list_APPEND]
      \\ Cases_on`zs`\\full_simp_tac(srw_ss())[word_list_def]
      \\ full_simp_tac(srw_ss())[word_offset_eq,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
      \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[]
      \\ qpat_abbrev_tac`t' = t1 with <|regs:=_ ; memory := _|>`>>
      `FLOOKUP t'.regs k = SOME (Word (c + bytes_in_word * n2w n + bytes_in_word * n2w s.stack_space))` by
        fs[Abbr`t'`,FLOOKUP_UPDATE]>>
      drule evaluate_downshift>>disch_then(qspec_then`n` assume_tac)>>
      fs[word_offset_eq,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,Abbr`t'`]>>
      qmatch_goalsub_abbrev_tac `t1 with <| regs:= R ; memory := M|>`>>
      `t1 with <|regs:=R;memory:=M|> = t1 with memory := M` by
        (simp[state_component_equality,Abbr`R`]>>
        match_mp_tac FUPDATE_ELIM>>
        qpat_x_assum`FLOOKUP _ k = SOME w` kall_tac>>
        qpat_x_assum`FLOOKUP _ k = SOME w` mp_tac>>
        simp[FDOM_FLOOKUP,Once FLOOKUP_DEF])>>
      simp[Abbr`M`]>>
      match_mp_tac (GEN_ALL state_rel_stack_store)>>
      simp[])
  THEN1 (* StackStoreAny *) (
    simp[comp_def]
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ strip_tac \\ rveq \\ full_simp_tac(srw_ss())[reg_bound_def]
    \\ qexists_tac`0`\\simp[]
    \\ simp[inst_def,assign_def,word_exp_def,GSYM get_var_def]
    \\ imp_res_tac state_rel_get_var_k \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[]
    \\ simp[wordLangTheory.word_op_def]
    \\ REWRITE_TAC[GSYM set_var_with_const]
    \\ REWRITE_TAC[with_same_clock]
    \\ simp[get_var_set_var]
    \\ pop_assum kall_tac
    \\ full_simp_tac(srw_ss())[NOT_LESS_EQUAL]
    \\ imp_res_tac LESS_LENGTH_IMP_APPEND
    \\ full_simp_tac(srw_ss())[word_list_APPEND]
    \\ Cases_on`zs` \\ full_simp_tac(srw_ss())[word_list_def]
    \\ `bytes_in_word * c >>> word_shift (:'a) = c` by
          rev_full_simp_tac(srw_ss())[lsl_word_shift,state_rel_def]
    \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[mem_store_def,WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w]
    \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[set_var_def,get_var_def,FLOOKUP_UPDATE]
    \\ full_simp_tac(srw_ss())[DECIDE ``n<m:num ==> n<>m``]
    \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th,EL_LENGTH_APPEND] \\ mp_tac th)
    \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th,EL_LENGTH_APPEND] \\ mp_tac th)
    \\ strip_tac \\ strip_tac
    \\ full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_UPDATE,DECIDE ``n<m:num ==> n<>m``]
    \\ rev_full_simp_tac(srw_ss())[ADD1,AC ADD_COMM ADD_ASSOC,word_list_def,word_list_APPEND]
    \\ full_simp_tac(srw_ss())[WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w]
    \\ qabbrev_tac `m = t1.memory`
    \\ qabbrev_tac `dm = t1.mdomain`
    \\ SEP_WRITE_TAC)
  THEN1 (* StackGetSize *) (
    simp[comp_def]
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ strip_tac \\ rveq
    \\ simp[inst_def,assign_def,word_exp_def]
    \\ imp_res_tac state_rel_get_var_k
    \\ full_simp_tac(srw_ss())[get_var_def,set_var_def,FLOOKUP_UPDATE]
    \\ `r ≠ k+1` by fs[reg_bound_def]
    \\ simp[wordLangTheory.word_op_def]
    \\ qexists_tac`0` \\ simp[]
    \\ simp[Once set_var_def,FLOOKUP_UPDATE]
    \\ simp[wordLangTheory.word_sh_def,wordLangTheory.num_exp_def]
    \\ IF_CASES_TAC \\ simp[]
    >- (
      full_simp_tac(srw_ss())[word_shift_def]
      \\ rev_full_simp_tac(srw_ss())[state_rel_def,labPropsTheory.good_dimindex_def]
      \\ rev_full_simp_tac(srw_ss())[] )
    \\ simp[]
    \\ ONCE_REWRITE_TAC[GSYM set_var_with_const]
    \\ REWRITE_TAC[with_same_clock]
    \\ dep_rewrite.DEP_REWRITE_TAC[bytes_in_word_word_shift]
    \\ qhdtm_x_assum`reg_bound`mp_tac \\simp[reg_bound_def]
    \\ strip_tac
    \\ qpat_x_assum`¬_`kall_tac
    \\ full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_UPDATE]
    \\ `r ≠ k+2` by fs[] \\ rfs[]
    \\ `s.stack_space MOD dimword (:'a) ≤ LENGTH s.stack`
    by (
      `0 < dimword (:'a)` by simp[]
      \\ metis_tac[MOD_LESS_EQ,LESS_EQ_TRANS] )
    \\ qmatch_assum_abbrev_tac`(a:num) + b * d < dw`
    \\ qmatch_abbrev_tac`d * f < dw`
    \\ `f ≤ s.stack_space ∧ f ≤ b` by
      (unabbrev_all_tac>>
      CONJ_ASM1_TAC>>fs[]>>
      match_mp_tac MOD_LESS_EQ>>
      fs[labPropsTheory.good_dimindex_def,dimword_def])
    \\ `d * f ≤ d * b ` by metis_tac[LESS_MONO_MULT,MULT_COMM]
    \\ decide_tac)
  THEN1 (* StackSetSize *) (
    simp[comp_def]
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ strip_tac \\ rveq
    \\ simp[inst_def,assign_def,word_exp_def]
    \\ full_simp_tac(srw_ss())[reg_bound_def]
    \\ imp_res_tac state_rel_get_var
    \\ imp_res_tac state_rel_get_var_k
    \\ full_simp_tac(srw_ss())[get_var_def]
    \\ simp[wordLangTheory.word_op_def]
    \\ qexists_tac`0` \\ simp[]
    \\ simp[Once set_var_def,FLOOKUP_UPDATE]
    \\ simp[wordLangTheory.word_sh_def,wordLangTheory.num_exp_def]
    \\ IF_CASES_TAC \\ simp[]
    >- (
      full_simp_tac(srw_ss())[word_shift_def]
      \\ rev_full_simp_tac(srw_ss())[state_rel_def,labPropsTheory.good_dimindex_def]
      \\ rev_full_simp_tac(srw_ss())[])
    \\ ONCE_REWRITE_TAC[GSYM set_var_with_const]
    \\ ONCE_REWRITE_TAC[GSYM set_var_with_const]
    \\ REWRITE_TAC[with_same_clock]
    \\ simp [set_var_def,FLOOKUP_UPDATE]
    \\ pop_assum kall_tac
    \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ simp[set_var_def,FLOOKUP_UPDATE]
    \\ rev_full_simp_tac(srw_ss())[lsl_word_shift])
  THEN1 (* BitmapLoad *)
   (full_simp_tac(srw_ss())[stackSemTheory.evaluate_def] \\ every_case_tac
    \\ full_simp_tac(srw_ss())[reg_bound_def,GSYM NOT_LESS] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[comp_def,list_Seq_def,stackSemTheory.evaluate_def]
    \\ `?ww. FLOOKUP s.store BitmapBase = SOME (Word ww)` by
     (full_simp_tac(srw_ss())[state_rel_def] \\ Cases_on `FLOOKUP s.store BitmapBase`
      \\ full_simp_tac(srw_ss())[is_SOME_Word_def] \\ Cases_on `x` \\ full_simp_tac(srw_ss())[is_SOME_Word_def])
    \\ `inst (Mem Load r (Addr (k + 1) (store_offset BitmapBase))) t1 =
          SOME (set_var r (Word ww) t1)` by
     (qpat_x_assum `state_rel jump off k s t1` mp_tac
      \\ simp [Once state_rel_def] \\ full_simp_tac(srw_ss())[]
      \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
      \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ strip_tac
      \\ full_simp_tac(srw_ss())[wordLangTheory.word_op_def,stackSemTheory.inst_def,
             word_exp_def,LET_THM]
      \\ `mem_load (c' + store_offset BitmapBase) t1 = SOME (Word ww)` by
        (
          match_mp_tac (GEN_ALL mem_load_lemma)>>fs[store_list_def]>>
          asm_exists_tac>> simp[])
      \\ simp[])
    \\ qexists_tac`0`
    \\ full_simp_tac(srw_ss())[LET_THM,stackSemTheory.inst_def,stackSemTheory.assign_def,
           word_exp_def,set_var_def,FLOOKUP_UPDATE,get_var_def]
    \\ `FLOOKUP t1.regs v = SOME (Word c)` by metis_tac [state_rel_def] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[wordLangTheory.word_op_def,FLOOKUP_UPDATE,wordLangTheory.num_exp_def,
           wordLangTheory.word_sh_def]
    \\ `mem_load (c << word_shift (:'a) + ww << word_shift (:'a)) t1 =
        SOME (Word (EL (w2n c) s.bitmaps))` by
     (full_simp_tac(srw_ss())[state_rel_def] \\ ntac 2 (qpat_x_assum `xx = SOME yy` kall_tac)
      \\ every_case_tac \\ full_simp_tac(srw_ss())[labPropsTheory.good_dimindex_def,word_shift_def]
      \\ rev_full_simp_tac(srw_ss())[WORD_MUL_LSL, the_SOME_Word_def]
      \\ imp_res_tac LESS_LENGTH_IMP_APPEND \\ full_simp_tac(srw_ss())[word_list_APPEND]
      \\ rev_full_simp_tac(srw_ss())[bytes_in_word_def]
      \\ pop_assum (fn th => simp [GSYM th])
      \\ Cases_on `zs` \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[rich_listTheory.EL_LENGTH_APPEND,word_list_def]
      \\ full_simp_tac(srw_ss())[mem_load_def]  \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[])
    \\ `good_dimindex(:'a)` by full_simp_tac(srw_ss())[state_rel_def]
    \\ full_simp_tac(srw_ss())[labPropsTheory.good_dimindex_def,word_shift_def,FLOOKUP_UPDATE]
    \\ full_simp_tac(srw_ss())[mem_load_def] \\ full_simp_tac(srw_ss())[GSYM mem_load_def] \\ full_simp_tac(srw_ss())[GSYM set_var_def]));

val compile_semantics = Q.store_thm("compile_semantics",
  `state_rel jump off k s1 s2 /\ semantics start s1 <> Fail ==>
   semantics start s2 ∈ extend_with_resource_limit { semantics start s1 }`,
  simp[GSYM AND_IMP_INTRO] \\ strip_tac
  \\ simp[semantics_def]
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  \\ DEEP_INTRO_TAC some_intro \\ full_simp_tac(srw_ss())[]
  \\ conj_tac
  >- (
    gen_tac >> ntac 2 strip_tac >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
      first_x_assum(qspec_then`k''`mp_tac)>>simp[]>>
      (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >>
      simp[] >>
      qmatch_assum_rename_tac`_ = (res,_)` >>
      Cases_on`res=SOME Error`>>simp[]>>
      drule comp_correct >>
      simp[reg_bound_def,RIGHT_FORALL_IMP_THM] >>
      drule (GEN_ALL state_rel_with_clock)
      \\ disch_then(qspec_then`k''`strip_assume_tac)
      \\ disch_then drule
      \\ simp[comp_def]
      \\ strip_tac \\ full_simp_tac(srw_ss())[]
      \\ qpat_x_assum`FST _ ≠ _`mp_tac
      \\ (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g)
      \\ drule (GEN_ALL evaluate_add_clock)
      \\ full_simp_tac(srw_ss())[]
      \\ disch_then(qspec_then`ck`mp_tac)
      \\ simp[]) >>
    DEEP_INTRO_TAC some_intro >> full_simp_tac(srw_ss())[] >>
    conj_tac >- (
      srw_tac[][] >>
      Cases_on`r=TimeOut`>>full_simp_tac(srw_ss())[]>-(
        qmatch_assum_abbrev_tac`evaluate (e,ss) = (SOME TimeOut,_)` >>
        qspecl_then[`k''`,`e`,`ss`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono)>>
        simp[Abbr`ss`] >>
        (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >>
        simp[] >> strip_tac >>
        drule comp_correct >>
        drule (GEN_ALL state_rel_with_clock)
        \\ disch_then(qspec_then`k'+k''`strip_assume_tac)
        \\ ONCE_REWRITE_TAC[CONJ_COMM]
        \\ simp[Once(GSYM AND_IMP_INTRO)]
        \\ disch_then drule
        \\ simp[AND_IMP_INTRO] >>
        impl_tac >- (
          simp[Abbr`e`,reg_bound_def] >>
          rpt(first_x_assum(qspec_then`k'+k''`mp_tac))>>srw_tac[][] ) >>
        simp[Abbr`e`,comp_def] >>
        strip_tac >>
        Cases_on`t.ffi.final_event`\\full_simp_tac(srw_ss())[]>>
        Cases_on`t'.ffi.final_event`>>full_simp_tac(srw_ss())[] >- (
          rveq
          \\ `t2.ffi = r''.ffi` by (every_case_tac \\ full_simp_tac(srw_ss())[state_rel_def])
          \\ ntac 2 (qhdtm_x_assum`evaluate`mp_tac) >>
          drule (GEN_ALL evaluate_add_clock) >>
          disch_then(qspec_then`ck+k'`mp_tac) >>
          simp[] >>
          impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
          simp[] >> ntac 3 strip_tac >>
          rveq >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]) >>
        qhdtm_x_assum`evaluate`mp_tac >>
        qmatch_assum_abbrev_tac`evaluate (e,ss) = (_,t')` >>
        qspecl_then[`ck+k'`,`e`,`ss`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono)>>
        simp[Abbr`ss`] >>
        ntac 2 strip_tac >> full_simp_tac(srw_ss())[] >>
        `t2.ffi = r''.ffi` by (every_case_tac \\ full_simp_tac(srw_ss())[state_rel_def])
        \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]
        \\ simp[extend_with_resource_limit_def]) >>
      qhdtm_x_assum`evaluate`mp_tac >>
      drule (GEN_ALL evaluate_add_clock) >>
      disch_then(qspec_then`k''`mp_tac) >>
      simp[] >> strip_tac >>
      drule comp_correct >>
      simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
      impl_tac >- (
        rpt(first_x_assum(qspec_then`k'`mp_tac))>>srw_tac[][] ) >>
      simp[reg_bound_def,comp_def] >>
      drule (GEN_ALL state_rel_with_clock) >>
      disch_then(qspec_then`k'+k''`strip_assume_tac) >>
      disch_then drule >>
      strip_tac >> full_simp_tac(srw_ss())[] >>
      strip_tac >>
      qmatch_assum_abbrev_tac`evaluate (e,ss) = _` >>
      qspecl_then[`ck+k'`,`e`,`ss`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono)>>
      simp[Abbr`ss`] >> strip_tac >>
      drule (GEN_ALL evaluate_add_clock) >>
      disch_then(qspec_then`ck+k'`mp_tac) >>
      simp[] >>
      Cases_on`t'.ffi.final_event`>>full_simp_tac(srw_ss())[]>- (
        first_x_assum(qspec_then`k''`mp_tac)
        \\ simp[]
        \\ strip_tac \\ full_simp_tac(srw_ss())[]
        \\ strip_tac \\ full_simp_tac(srw_ss())[] \\ rveq \\ full_simp_tac(srw_ss())[]
        \\ `t.ffi = t'.ffi` by full_simp_tac(srw_ss())[state_rel_def]
        \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]
        \\ simp[extend_with_resource_limit_def] ) >>
      `t.ffi = t'.ffi` by
        (BasicProvers.FULL_CASE_TAC >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[state_rel_def] ) >>
      full_simp_tac(srw_ss())[extend_with_resource_limit_def] ) >>
    strip_tac >>
    drule comp_correct >>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO,reg_bound_def] >>
    impl_tac >- (
      rpt(first_x_assum(qspec_then`k'`mp_tac))>>srw_tac[][]) >>
    simp[comp_def] >>
    drule (GEN_ALL state_rel_with_clock)
    \\ disch_then(qspec_then`k'`strip_assume_tac)
    \\ disch_then drule
    \\ simp[] \\ strip_tac
    \\ first_x_assum(qspec_then`ck+k'`mp_tac)
    \\ simp[] >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[extend_with_resource_limit_def] >>
    first_x_assum(qspec_then`ck+k'`mp_tac) >>
    simp[] >> strip_tac >> full_simp_tac(srw_ss())[] >>
    BasicProvers.FULL_CASE_TAC >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]) >>
  strip_tac
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  >- (
    full_simp_tac(srw_ss())[extend_with_resource_limit_def]
    \\ qpat_x_assum`_ ≠ _`mp_tac
    \\ (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g)
    \\ strip_tac \\ full_simp_tac(srw_ss())[]
    \\ last_x_assum(qspec_then`k'`mp_tac)
    \\ (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g)
    \\ drule comp_correct
    \\ qmatch_assum_rename_tac`_ = (res,_)`
    \\ Cases_on`res=SOME Error`\\ full_simp_tac(srw_ss())[]
    \\ drule (GEN_ALL state_rel_with_clock)
    \\ disch_then(qspec_then`k'`strip_assume_tac)
    \\ disch_then drule
    \\ simp[reg_bound_def,comp_def]
    \\ strip_tac
    \\ first_x_assum(qspec_then`k'`mp_tac)
    \\ simp[]
    \\ BasicProvers.FULL_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.FULL_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.FULL_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ ntac 2 (qhdtm_x_assum`evaluate`mp_tac)
    \\ drule (GEN_ALL evaluate_add_clock)
    \\ simp[] )
  \\ DEEP_INTRO_TAC some_intro \\ full_simp_tac(srw_ss())[]
  \\ conj_tac >- (
    srw_tac[][]
    \\ full_simp_tac(srw_ss())[METIS_PROVE[]``¬a ∨ b ⇔ a ⇒ b``]
    \\ full_simp_tac(srw_ss())[extend_with_resource_limit_def]
    \\ last_assum(qspec_then`k'`mp_tac)
    \\ (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g)
    \\ qpat_x_assum`∀x y. _`(fn th => assume_tac th >> qspec_then`k'`mp_tac th)
    \\ simp[]
    \\ drule comp_correct
    \\ qmatch_assum_rename_tac`_ = (res,_)`
    \\ Cases_on`res=SOME Error`\\ full_simp_tac(srw_ss())[]
    \\ drule (GEN_ALL state_rel_with_clock)
    \\ disch_then(qspec_then`k'`strip_assume_tac)
    \\ disch_then drule
    \\ simp[reg_bound_def,comp_def]
    \\ strip_tac
    \\ qpat_x_assum`∀k. _ ∨ _`(fn th => assume_tac th >> qspec_then`ck+k'`mp_tac th)
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp_tac(srw_ss())[]
    \\ strip_tac
    \\ qpat_x_assum`option_CASE _ _ _`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ strip_tac
    \\ `t2.ffi = r'.ffi`
    by (
      pop_assum mp_tac
      \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[state_rel_def] )
    \\ full_simp_tac(srw_ss())[]
    \\ qmatch_assum_abbrev_tac`evaluate (e,ss) = (_,t)`
    \\ qspecl_then[`e`,`ss`](mp_tac o Q.GEN`extra`) evaluate_add_clock_io_events_mono
    \\ disch_then(qspec_then`ck`mp_tac)
    \\ simp[Abbr`ss`] \\ strip_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ Cases_on`t.ffi.final_event` \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]
    \\ Cases_on`r = TimeOut` \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac evaluate_add_clock \\ rev_full_simp_tac(srw_ss())[]
    \\ first_x_assum(qspec_then`ck`mp_tac)
    \\ simp[])
  \\ simp[extend_with_resource_limit_def]
  \\ strip_tac
  \\ qmatch_abbrev_tac`build_lprefix_lub l1 = build_lprefix_lub l2`
  \\ `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
       suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_new_chain,unique_lprefix_lub]
  \\ conj_asm1_tac >- (
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
  simp[comp_def,reg_bound_def,RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
  impl_tac >- (
    rpt(first_x_assum(qspec_then`k'`mp_tac))>>srw_tac[][] ) >>
  drule (GEN_ALL state_rel_with_clock) >>
  disch_then(qspec_then`k'`strip_assume_tac) >>
  disch_then drule >>
  strip_tac >> full_simp_tac(srw_ss())[] >>
  `t2.ffi = r'.ffi` by (
    pop_assum mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ TRY BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ simp[state_rel_def] ) >>
  reverse conj_tac >- (
    srw_tac[][] >>
    qexists_tac`ck+k'`>>simp[] ) >>
  srw_tac[][] >>
  qexists_tac`k'`>>simp[] >>
  ntac 2 (qhdtm_x_assum`evaluate`mp_tac) >>
  qmatch_assum_abbrev_tac`evaluate (e,ss) = _` >>
  qspecl_then[`ck`,`e`,`ss`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono)>>
  simp[Abbr`ss`] >>
  ntac 3 strip_tac >> full_simp_tac(srw_ss())[] >>
  rev_full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[IS_PREFIX_APPEND] >>
  simp[EL_APPEND1]);

(* init code *)

val tac = simp [list_Seq_def,evaluate_def,inst_def,word_exp_def,get_var_def,
       wordLangTheory.word_op_def,mem_load_def,assign_def,set_var_def,
       FLOOKUP_UPDATE,mem_store_def,dec_clock_def,get_var_imm_def,
       asmTheory.word_cmp_def,wordLangTheory.num_exp_def,
       labSemTheory.word_cmp_def,GREATER_EQ,GSYM NOT_LESS,FUPDATE_LIST,
       wordLangTheory.word_sh_def,halt_inst_def]

val mem_val_def = Define `
  (mem_val regs (INL w) = Word w) /\
  (mem_val (regs:num |-> 'a word_loc) (INR n) = regs ' n)`

val store_list_code_thm = Q.store_thm("store_list_code_thm",
  `!xs s w frame ys m dm.
      (word_list w ys * frame) (fun2set (m,dm)) /\
      m = s.memory /\ dm = s.mdomain /\
      (LENGTH ys = LENGTH xs) /\ a <> t /\
      get_var a s = SOME (Word w) /\ t IN FDOM s.regs /\
      EVERY (\x. !n. (INR n = x) ==> n <> a /\ n <> t /\ n IN FDOM s.regs) xs ==>
      ?r1 m1.
        (word_list w (MAP (mem_val s.regs) xs) * frame) (fun2set (m1,s.mdomain)) /\
        evaluate (store_list_code a t xs,s) =
          (NONE,s with <| memory := m1;
                          regs := s.regs |++
            [(a,Word (w + bytes_in_word * n2w (LENGTH xs)));(t,r1)] |>)`,
  simp_tac std_ss []
  \\ Induct \\ fs [] THEN1
   (fs [word_list_def,SEP_CLAUSES,store_list_code_def,LENGTH_NIL]
    \\ tac
    \\ fs [finite_mapTheory.fmap_EXT,state_component_equality]
    \\ rw [] \\ qexists_tac `s.regs ' t`
    \\ fs [EXTENSION,FAPPLY_FUPDATE_THM,FLOOKUP_DEF]
    \\ metis_tac [])
  \\ Cases_on `ys` \\ Cases \\ fs [mem_val_def]
  \\ fs [word_list_def,SEP_CLAUSES,store_list_code_def,LENGTH_NIL]
  THEN1
   (tac \\ fs [store_list_code_def]
    \\ rpt strip_tac
    \\ SEP_R_TAC \\ fs []
    \\ fs [FLOOKUP_UPDATE]
    \\ qabbrev_tac `m = s.memory`
    \\ qabbrev_tac `dm = s.mdomain`
    \\ SEP_W_TAC
    \\ pop_assum mp_tac
    \\ once_rewrite_tac [GSYM STAR_ASSOC]
    \\ once_rewrite_tac [STAR_COMM]
    \\ once_rewrite_tac [GSYM STAR_ASSOC]
    \\ qpat_abbrev_tac `s4 = s with <| regs := _; memory := _ |>`
    \\ first_x_assum (qspec_then `s4` mp_tac)
    \\ unabbrev_all_tac \\ fs []
    \\ rpt strip_tac \\ first_x_assum drule
    \\ impl_tac
    THEN1 (fs [get_var_def,FLOOKUP_UPDATE,EVERY_MEM])
    \\ strip_tac
    \\ fs [state_component_equality,ADD1,GSYM word_add_n2w,
           WORD_LEFT_ADD_DISTRIB]
    \\ qexists_tac `r1` \\ fs []
    \\ `MAP (mem_val (s.regs |+ (t,Word x) |+ (a,Word (w + bytes_in_word)))) xs =
        MAP (mem_val s.regs) xs` by
     (fs [MAP_EQ_f,EVERY_MEM]
      \\ Cases \\ fs [mem_val_def]
      \\ rw [] \\ res_tac \\ fs [FAPPLY_FUPDATE_THM])
    \\ fs []
    \\ fs [finite_mapTheory.fmap_EXT,state_component_equality,
           FAPPLY_FUPDATE_THM,FUPDATE_LIST,EXTENSION]
    \\ metis_tac [])
  THEN1
   (tac \\ fs [store_list_code_def]
    \\ rpt strip_tac \\ SEP_R_TAC \\ fs []
    \\ fs [FLOOKUP_UPDATE]
    \\ fs [FLOOKUP_DEF]
    \\ qabbrev_tac `m = s.memory`
    \\ qabbrev_tac `dm = s.mdomain`
    \\ SEP_W_TAC
    \\ pop_assum mp_tac
    \\ once_rewrite_tac [GSYM STAR_ASSOC]
    \\ once_rewrite_tac [STAR_COMM]
    \\ once_rewrite_tac [GSYM STAR_ASSOC]
    \\ qpat_abbrev_tac `s4 = s with <| regs := _; memory := _ |>`
    \\ first_x_assum (qspec_then `s4` mp_tac)
    \\ unabbrev_all_tac \\ fs []
    \\ rpt strip_tac \\ first_x_assum drule
    \\ impl_tac
    THEN1 (fs [get_var_def,FLOOKUP_UPDATE,EVERY_MEM])
    \\ strip_tac
    \\ fs [state_component_equality,ADD1,GSYM word_add_n2w,
           WORD_LEFT_ADD_DISTRIB]
    \\ qexists_tac `r1` \\ fs []
    \\ `MAP (mem_val (s.regs |+ (a,Word (w + bytes_in_word)))) xs =
        MAP (mem_val s.regs) xs` by
     (fs [MAP_EQ_f,EVERY_MEM]
      \\ Cases \\ fs [mem_val_def]
      \\ rw [] \\ res_tac \\ fs [FAPPLY_FUPDATE_THM])
    \\ fs []
    \\ fs [finite_mapTheory.fmap_EXT,state_component_equality,
           FAPPLY_FUPDATE_THM,FUPDATE_LIST,EXTENSION]))

val halt_tac =
  tac \\ fs [labPropsTheory.good_dimindex_def]
  \\ rw [] \\ fs [dimword_def]

val MOD_EQ_IMP_MULT = Q.prove(
  `!n d. n MOD d = 0 /\ d <> 0 ==> ?k. n = d * k`,
  rw [] \\ fs [MOD_EQ_0_DIVISOR] \\ metis_tac []);

val star_move_lemma = Q.prove(
  `p0 * p1 * p2 * p3 * p4 = p2 * (p1 * STAR p3 (p4 * p0))`,
  fs [AC STAR_COMM STAR_ASSOC]);


val read_mem_def = Define `
  (read_mem a m 0 = []) /\
  (read_mem a m (SUC n) =
     m a :: read_mem (a + bytes_in_word) m n)`

val addresses_def = Define `
  (addresses a 0 = {}) /\
  (addresses a (SUC n) = a INSERT addresses (a + bytes_in_word) n)`

val LENGTH_read_mem = Q.prove(
  `!n a m. LENGTH (read_mem a m n) = n`,
  Induct \\ fs [read_mem_def]);

val IN_addresses = Q.prove(
  `!n a x. x IN addresses a n <=>
            ?i. i < n /\ x = a + n2w i * bytes_in_word`,
  Induct \\ fs [addresses_def]
  \\ rw [] \\ eq_tac \\ rw []
  THEN1 (qexists_tac `0` \\ fs [])
  THEN1 (qexists_tac `SUC i`
         \\ fs [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])
  \\ Cases_on `i` \\ fs []
  \\ fs [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ metis_tac []);

val memory_addresses = Q.prove(
  `!n (a:'a word) (m:'a word -> 'a word_loc).
      n * (dimindex (:'a) DIV 8) < dimword (:'a) /\ good_dimindex (:'a) ==>
      memory m (addresses a n) = word_list a (read_mem a m n)`,
  once_rewrite_tac [EQ_SYM_EQ]
  \\ Induct \\ fs [addresses_def,read_mem_def,word_list_def]
  THEN1 (fs [memory_def,FUN_EQ_THM,fun2set_def,emp_def])
  \\ simp [memory_def,Once FUN_EQ_THM,one_STAR]
  \\ rw []
  \\ fs [MULT_CLAUSES]
  \\ `n * (dimindex (:α) DIV 8) < dimword (:α)` by decide_tac
  \\ res_tac \\ fs []
  \\ fs [fun2set_def,memory_def]
  \\ fs [EXTENSION,FORALL_PROD]
  \\ fs [IN_addresses]
  \\ eq_tac \\ fs [] \\ strip_tac \\ fs [] THEN1 metis_tac []
  \\ rw [] \\ eq_tac \\ fs []
  \\ rw [] \\ fs []
  THEN1 metis_tac []
  THEN1 metis_tac []
  \\ full_simp_tac std_ss [GSYM WORD_ADD_ASSOC,addressTheory.WORD_EQ_ADD_CANCEL,
       bytes_in_word_def,word_add_n2w,word_mul_n2w]
  \\ sg `i * (dimindex (:α) DIV 8) + dimindex (:α) DIV 8 < dimword (:α)`
  \\ fs[]
  \\ fs [labPropsTheory.good_dimindex_def,dimword_def]
  \\ fs [labPropsTheory.good_dimindex_def,dimword_def]);

val MOD_LESS_EQ_MOD_IMP = Q.prove(
  `m MOD k <= n /\ m < k ==> m <= n`,
  rw [] \\ fs [])

val MAP_mem_val_MAP_INL = Q.prove(
  `!ws f. MAP (mem_val f) (MAP INL ws) = MAP Word ws`,
  Induct \\ fs [mem_val_def]);

val word_list_EQ_rev = Q.store_thm("word_list_EQ_rev",
  `!xs a. word_list a xs =
           word_list_rev (a + n2w (LENGTH xs) * bytes_in_word) (REVERSE xs)`,
  recInduct SNOC_INDUCT \\ fs [REVERSE_SNOC]
  \\ fs [SNOC_APPEND,word_list_APPEND,word_list_rev_def,word_list_def]
  \\ rw [SEP_CLAUSES,ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [AC STAR_COMM STAR_ASSOC])

val word_list_and_rev_join_lemma = Q.prove(
  `(b = a + n2w (LENGTH xs + LENGTH ys) * bytes_in_word) /\
    (p * word_list a (xs ++ REVERSE ys) * q) ss /\ b1 ==>
    (p * word_list a xs * word_list_rev b ys * q) ss /\ b1`,
  fs [word_list_APPEND,WORD_LEFT_ADD_DISTRIB]
  \\ fs [word_list_EQ_rev] \\ rw []
  \\ fs [AC STAR_COMM STAR_ASSOC,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]);

val word_list_IMP_read_mem = Q.prove(
  `!xs a p.
      (p * word_list a xs) (fun2set (m,dm)) ==>
      read_mem a m (LENGTH xs) = xs`,
  Induct \\ fs [read_mem_def,word_list_def,STAR_ASSOC]
  \\ rw [] \\ res_tac \\ SEP_R_TAC);

val INSERT_DELETE_EQ_DELETE = Q.prove(
  `(x INSERT s) DELETE x = s DELETE x`,
  fs [EXTENSION] \\ metis_tac []);

val word_list_exists_addresses = Q.store_thm("word_list_exists_addresses",
  `!n a. (dimindex(:'a) DIV 8) * n < dimword (:'a) /\
          good_dimindex (:'a) ==>
          word_list_exists a n (fun2set (m1,addresses (a:'a word) n))`,
  Induct
  THEN1 (fs [word_list_exists_thm,fun2set_def,emp_def,addresses_def])
  \\ fs [word_list_exists_thm,emp_def,addresses_def,INSERT_DELETE_EQ_DELETE,
         SEP_EXISTS_THM,MULT_CLAUSES,set_sepTheory.one_fun2set]
  \\ rw [] \\ imp_res_tac (DECIDE ``m+n<k:num ==> m < k``) \\ res_tac
  \\ sg `addresses (a + bytes_in_word) n DELETE a =
      addresses (a + bytes_in_word) n` \\ fs []
  \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ fs []
  \\ fs [IN_addresses,PULL_EXISTS]
  \\ full_simp_tac std_ss [addressTheory.WORD_EQ_ADD_CANCEL,GSYM WORD_ADD_ASSOC]
  \\ rw [] \\ fs [bytes_in_word_def,word_mul_n2w,word_add_n2w]
  \\ sg `(i * (dimindex (:'a) DIV 8) + dimindex (:'a) DIV 8)
      < dimword (:'a)` \\ fs []
  \\ fs [labPropsTheory.good_dimindex_def,dimword_def] \\ rfs [] \\ fs []);

val init_reduce_def = Define `
  init_reduce gen_gc k code bitmaps (s:('a,'ffi)stackSem$state) =
    let heap_ptr = theWord (s.regs ' (k + 2)) in
    let bitmap_ptr = theWord (s.regs ' 3) << word_shift (:'a) in
    let stack_ptr = theWord (s.regs ' k) in
    let base_ptr = theWord (s.regs ' (k + 1)) in
    let heap_sp = w2n (base_ptr - heap_ptr) DIV (dimindex (:'a) DIV 8) - (LENGTH store_list) in
    let stack_sp = w2n (stack_ptr - base_ptr) DIV (dimindex (:'a) DIV 8) in
      s with
      <| use_stack := T;
         use_store := T;
         use_alloc := F;
         mdomain := addresses heap_ptr heap_sp;
         bitmaps := bitmaps;
         code := code;
         stack_space := stack_sp;
         stack := read_mem base_ptr s.memory (stack_sp + 1);
         store := FEMPTY |++ (MAP (\n. case store_init gen_gc k n of
                                       | INL w => (n,Word w)
                                       | INR i => (n,s.regs ' i))
                               (CurrHeap::store_list)) |>`

val init_reduce_stack_space = Q.prove(
  `(init_reduce gen_gc k code bitmaps s8).stack_space <=
    LENGTH (init_reduce gen_gc k code bitmaps s8).stack`,
  fs [init_reduce_def,LENGTH_read_mem]);

val init_prop_def = Define `
  init_prop gen_gc max_heap (s:('a,'ffi)stackSem$state) =
    ?curr other bitmap_base len.
       FLOOKUP s.store CurrHeap = SOME (Word curr) /\
       FLOOKUP s.store NextFree = SOME (Word curr) /\
       FLOOKUP s.store TriggerGC = SOME (Word (if gen_gc then curr else other)) /\
       FLOOKUP s.store EndOfHeap = SOME (Word other) /\
       FLOOKUP s.store OtherHeap = SOME (Word other) /\
       FLOOKUP s.store BitmapBase = SOME (Word bitmap_base) /\
       FLOOKUP s.store HeapLength = SOME (Word (n2w len * bytes_in_word)) /\
       FLOOKUP s.store ProgStart = SOME (Word 0w) /\
       FLOOKUP s.store AllocSize = SOME (Word 0w) /\
       FLOOKUP s.store Globals = SOME (Word 0w) /\
       FLOOKUP s.store Handler = SOME (Word 0w) /\
       FLOOKUP s.store GenStart = SOME (Word 0w) /\
       s.use_stack /\ s.use_store /\
       FLOOKUP s.regs 0 = SOME (Loc 1 0) /\
       LENGTH s.bitmaps + 1 < dimword (:'a) /\
       LENGTH s.stack < dimword (:'a) /\
       (other = curr + bytes_in_word * n2w len) /\
       byte_aligned curr /\
       LAST s.stack = Word 0w /\
       LENGTH s.stack = SUC s.stack_space /\
       LENGTH s.stack * (dimindex (:α) DIV 8) < dimword (:α) /\
       len + len <= max_heap /\
       (word_list_exists curr len * word_list_exists other len)
          (fun2set (s.memory,s.mdomain))`

val init_code_pre_def = Define `
  init_code_pre k bitmaps s <=>
    ?ptr2 ptr3 ptr4 bitmap_ptr.
      good_dimindex (:'a) /\ 8 <= k /\ 1 ∈ domain s.code /\
      {k; k + 1; k + 2} SUBSET s.ffi_save_regs /\
      ~s.use_stack /\ ~s.use_store /\ ~s.use_alloc /\
      FLOOKUP s.regs 2 = SOME (Word (ptr2:'a word)) /\
      FLOOKUP s.regs 3 = SOME (Word ptr3) /\
      FLOOKUP s.regs 4 = SOME (Word ptr4) /\
      s.memory ptr2 = Word bitmap_ptr /\
      (* NOTE: The last conjunct only needs to hold if
        the entry checks hold. Probably can make more assumptions
        about the bitmap_ptr too
      *)
      (ptr2 <=+ ptr4 ∧ byte_aligned ptr2 ∧ byte_aligned ptr4 ⇒
      (word_list bitmap_ptr (MAP Word bitmaps) *
       word_list_exists ptr2 (w2n (ptr4 - ptr2) DIV w2n (bytes_in_word:'a word)))
        (fun2set (s.memory,s.mdomain)))`

val byte_aligned_bytes_in_word_MULT = Q.prove(
  `good_dimindex (:'a) ==>
    byte_aligned (bytes_in_word * w:'a word)`,
  fs [labPropsTheory.good_dimindex_def] \\ rw []
  \\ fs [alignmentTheory.byte_aligned_def,bytes_in_word_def]
  \\ qspecl_then [`2`,`w`] mp_tac alignmentTheory.aligned_mul_shift_1
  \\ qspecl_then [`3`,`w`] mp_tac alignmentTheory.aligned_mul_shift_1
  \\ fs [WORD_MUL_LSL]);

(* The extra b equality makes this work better with SEP_NEQ_TAC *)
val word_list_wrap = Q.prove(`
  good_dimindex (:'a) ∧
  dimword(:'a) DIV (dimindex(:'a) DIV 8) < LENGTH ls ⇒
  ∃x xs y ys b.
  word_list (a:'a word) ls = word_list a (x::xs) * word_list b (y::ys)  ∧
  b = a`,
  rw[]>>
  `∃r.r < LENGTH ls ∧ 0 < r ∧ a + bytes_in_word * n2w r = a` by
    (fs[addressTheory.WORD_EQ_ADD_CANCEL,bytes_in_word_def,word_mul_n2w]>>
    `0 <dimword(:'a)` by fs[labPropsTheory.good_dimindex_def] >>
    drule (GEN_ALL MOD_EQ_0_DIVISOR)>>fs[]>>disch_then kall_tac>>
    fs[labPropsTheory.good_dimindex_def,dimword_def,PULL_EXISTS]>>rfs[]>>
    asm_exists_tac>>fs[])>>
  Q.ISPECL_THEN [`TAKE r ls`,`DROP r ls`,`a`] assume_tac word_list_APPEND>>
  fs[]>>
  `0 < LENGTH (DROP r ls)` by fs[]>>
  Cases_on`DROP r ls`>>fs[]>>
  Cases_on`ls`>>fs[]>>
  metis_tac[]);

val sub_rewrite = Q.prove(`
  ptr <= ptr' ⇒
  -1w * n2w ptr + n2w ptr' = n2w (ptr'-ptr)`,
  rw[]>>simp[Once WORD_SUB_INTRO]>>
  simp[WORD_LITERAL_ADD]);

val div_rewrite = Q.prove(`
  n <= x ∧ 1 < n
  ⇒
  x DIV n ≠ 0`,
  rw[]>>
  fs[DIV_EQ_0]);

val init_code_thm = Q.store_thm("init_code_thm",
  `init_code_pre k bitmaps s /\ code_rel jump off k code s.code /\
    lookup stack_err_lab s.code = SOME (halt_inst 2w) ==>
    case evaluate (init_code gen_gc max_heap k,s) of
    | (SOME res,t) =>
         ?w. (res = Halt (Word w)) /\ w <> 0w /\ t.ffi = s.ffi
    | (NONE,t) =>
         (∃w2 w4.
         FLOOKUP s.regs 2 = SOME (Word w2) ∧ byte_aligned w2 ∧
         FLOOKUP s.regs 4 = SOME (Word w4) ∧ byte_aligned w4 ∧
         w2 <+ w4) ∧
         state_rel jump off k (init_reduce gen_gc k code bitmaps t) t /\
         t.ffi = s.ffi /\
         init_prop gen_gc max_heap (init_reduce gen_gc k code bitmaps t)`,
  simp_tac std_ss [init_code_pre_def] \\ strip_tac
  \\ `k <> 3 /\ k <> 4 /\ k <> 5` by decide_tac
  \\ full_simp_tac std_ss [init_code_def,LET_DEF]
  \\ qabbrev_tac `min_stack = LENGTH store_list + 1`
  \\ IF_CASES_TAC THEN1
   (tac \\ fs [labPropsTheory.good_dimindex_def]
    \\ rw [] \\ fs [dimword_def])
  \\ fs [GSYM NOT_LESS]
  \\ rpt (tac \\ IF_CASES_TAC THEN1 halt_tac) \\ tac
  \\ Cases_on `ptr2` \\ fs []
  \\ rename1 `FLOOKUP s.regs 2 = SOME (Word (n2w ptr2))`
  \\ Cases_on `ptr3` \\ fs []
  \\ rename1 `FLOOKUP s.regs 3 = SOME (Word (n2w ptr3))`
  \\ Cases_on `ptr4` \\ fs []
  \\ rename1 `FLOOKUP s.regs 4 = SOME (Word (n2w ptr4))`
  \\ reverse IF_CASES_TAC THEN1 halt_tac \\ tac>>
  (* discharging the entry preconditions *)
  `n2w ptr2 <=+ n2w ptr4` by
    fs[word_lo_n2w,word_ls_n2w] >>
  `n2w (ptr3 - ptr2) >>> 1 = n2w ((ptr3 - ptr2) DIV 2)` by
   (once_rewrite_tac [GSYM w2n_11] \\ rewrite_tac [w2n_lsr]
    \\ fs [DIV_LT_X] \\ NO_TAC)
  \\ fs [alignmentTheory.aligned_bitwise_and
         |> Q.SPEC `3` |> SIMP_RULE (srw_ss()) [] |> GSYM]
  \\ `2 < 3:num` by EVAL_TAC
  \\ drule alignmentTheory.aligned_imp
  \\ disch_then drule
  \\ fs [aligned_or] \\ strip_tac
  \\ `byte_aligned ((n2w ptr2):'a word) ∧ byte_aligned ((n2w ptr4):'a word)` by
    fs[alignmentTheory.byte_aligned_def,labPropsTheory.good_dimindex_def]>>
  `0 < w2n (((n2w ptr4):'a word) + -1w *n2w ptr2) DIV w2n (bytes_in_word:'a word)` by
    (fs[word_lo_n2w,bytes_in_word_def,word_mul_n2w]>>
    rfs[sub_rewrite,word_lo_n2w,NOT_LESS]>>
    fs[]>>
    DEP_REWRITE_TAC[LESS_MOD]>>
    fs[labPropsTheory.good_dimindex_def,dimword_def]>>rfs[]>>
    match_mp_tac bitTheory.DIV_GT0>>
    fs[markerTheory.Abbrev_def])>>
  `n2w ptr2 ∈ s.mdomain` by
    (fs[word_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM]>>
    fs[STAR_def,cond_def]>>
    Cases_on`xs`>>fs[]>>
    fs[word_list_def,one_def,SPLIT_EQ,STAR_def,SUBSET_DEF,fun2set_def,FORALL_PROD]>>
    fs[EXTENSION,FORALL_PROD]>>
    metis_tac[])
  \\ reverse IF_CASES_TAC THEN1 halt_tac \\ tac
  \\ reverse IF_CASES_TAC THEN1 halt_tac \\ tac
  \\ fs [alignmentTheory.aligned_bitwise_and
         |> Q.SPEC `3` |> SIMP_RULE (srw_ss()) [] |> GSYM]
  \\ `2 < 3:num` by EVAL_TAC
  \\ drule alignmentTheory.aligned_imp
  \\ disch_then drule
  \\ strip_tac
  \\ fs [] \\ tac
  \\ `~(dimindex (:'a) <= word_shift (:'a))` by
    fs [labPropsTheory.good_dimindex_def,dimword_def,word_shift_def]
  \\ fs [WORD_LO,NOT_LESS]
  \\ `-1w * n2w ptr2 + n2w ptr3 = n2w (ptr3 - ptr2):'a word /\
      -1w * n2w ptr3 + n2w ptr4 = n2w (ptr4 - ptr3):'a word /\
      -1w * n2w ptr2 + n2w ptr4 = n2w (ptr4 - ptr2):'a word` by
    (imp_res_tac LESS_EQ_TRANS
     \\ full_simp_tac std_ss [wordsLib.WORD_DECIDE ``-1w * w + v = v - w``,
       addressTheory.word_arith_lemma2,GSYM NOT_LESS] \\ NO_TAC)
  \\ full_simp_tac std_ss [] \\ ntac 3 (pop_assum kall_tac)
  \\ fs [FLOOKUP_UPDATE]
  \\ `((ptr3 − ptr2) DIV 2) < dimword (:α)` by fs [DIV_LT_X]
  \\ `bitmap_ptr ⋙ word_shift (:α) ≪ word_shift (:α) = bitmap_ptr` by (
    simp[GSYM alignmentTheory.align_shift,GSYM alignmentTheory.aligned_def]
    \\ simp[word_shift_def] \\ rw[])
  \\ fs [aligned_w2n] \\ rfs []
  \\ `w2n (bytes_in_word:'a word) = dimindex (:'a) DIV 8` by
    (fs [labPropsTheory.good_dimindex_def,bytes_in_word_def,dimword_def])
  \\ fs [] \\ pop_assum kall_tac
  \\ qabbrev_tac `d = dimindex (:α) DIV 8`
  \\ `d <> 0 /\ 0 < d /\
      ptr2 MOD d = 0 /\
      ptr3 MOD d = 0 /\
      ptr4 MOD d = 0 /\
      ((ptr3 − ptr2) DIV 2) MOD d = 0` by
    (unabbrev_all_tac \\ fs [labPropsTheory.good_dimindex_def])
  \\ ntac 4 (drule MOD_EQ_IMP_MULT \\ asm_rewrite_tac [] \\ pop_assum kall_tac)
  \\ strip_tac \\ rename1 `ptr2 = d * h2`
  \\ strip_tac \\ rename1 `ptr3 = d * h3`
  \\ strip_tac \\ rename1 `ptr4 = d * h4`
  \\ strip_tac \\ rename1 `_ = d * hi`
  \\ rpt var_eq_tac \\ fs []
  \\ fs [bytes_in_word_def,word_mul_n2w]
  \\ rfs [] \\ fs []
  \\ rpt (qpat_x_assum `_ MOD _ = 0n` kall_tac)
  \\ qpat_x_assum `h2 <= h3` mp_tac
  \\ simp_tac std_ss [Once LESS_EQ_EXISTS]
  \\ strip_tac \\ rename1 `h3 = h2 + heap_length`
  \\ qpat_x_assum `h3 <= h4` mp_tac
  \\ simp_tac std_ss [Once LESS_EQ_EXISTS]
  \\ strip_tac \\ rename1 `h4 = h3 + stack_length`
  \\ rpt var_eq_tac \\ fs [LEFT_ADD_DISTRIB]
  \\ full_simp_tac std_ss [GSYM ADD_ASSOC]
  \\ qpat_x_assum `n2w _ ⋙ 1 = n2w _` kall_tac
  \\ rpt (qpat_x_assum `T` kall_tac)
  \\ `(d * heap_length + d * stack_length) DIV d =
       heap_length + stack_length` by
    (fs [GSYM LEFT_ADD_DISTRIB,ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV] \\ NO_TAC)
  \\ full_simp_tac std_ss [] \\ pop_assum kall_tac
  \\ `LENGTH store_list <= stack_length` by
    (unabbrev_all_tac \\ rfs [labPropsTheory.good_dimindex_def] \\ rfs [])
  \\ pop_assum mp_tac
  \\ simp_tac std_ss [Once LESS_EQ_EXISTS]
  \\ strip_tac \\ rename1 `_ = _ + rest_of_stack_len:num`
  \\ var_eq_tac \\ full_simp_tac std_ss []
  \\ full_simp_tac std_ss [ADD_ASSOC]
  \\ full_simp_tac std_ss [word_list_exists_ADD]
  \\ fs [bytes_in_word_def,word_mul_n2w,word_add_n2w]
  \\ fs [word_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
  \\ rename1 `LENGTH rest = rest_of_stack_len`
  \\ qpat_x_assum `LENGTH rest = rest_of_stack_len` mp_tac
  \\ rename1 `LENGTH bitst = LENGTH store_list`
  \\ qpat_x_assum `LENGTH bitst = LENGTH store_list` mp_tac
  \\ rename1 `LENGTH heap = heap_length`
  \\ qpat_x_assum `LENGTH heap = heap_length` mp_tac
  \\ rpt strip_tac \\ rpt var_eq_tac
  \\ full_simp_tac std_ss [LEFT_ADD_DISTRIB,ADD_ASSOC]
  \\ pop_assum (mp_tac o GSYM)
  \\ simp_tac std_ss [markerTheory.Abbrev_def] \\ strip_tac
  \\ `LENGTH rest <> 0` by (unabbrev_all_tac \\ decide_tac)
  \\ full_simp_tac std_ss [LENGTH_NIL]
  \\ fs [init_memory_def] \\ tac
  \\ `?r1 rest1. rest = SNOC r1 rest1` by metis_tac [SNOC_CASES]
  \\ var_eq_tac \\ full_simp_tac std_ss [SNOC_APPEND,LENGTH_APPEND,
       LEFT_ADD_DISTRIB,ADD_ASSOC,word_list_APPEND,word_add_n2w,
       word_list_def,bytes_in_word_def,LENGTH,ADD1,word_mul_n2w,
       SEP_CLAUSES]
  \\ fs [GSYM word_add_n2w] \\ fs [word_add_n2w]
  \\ SEP_R_TAC \\ fs []
  \\ qabbrev_tac `m = s.memory`
  \\ qabbrev_tac `dm = s.mdomain`
  \\ SEP_W_TAC
  \\ qpat_abbrev_tac `m4 = (_ =+ Word 0w) m`
  \\ qpat_x_assum `_ (fun2set (m,dm))` kall_tac
  \\ fs [star_move_lemma]
  \\ qpat_abbrev_tac `s7 = s with <| regs := _ ; memory := m4 |>`
  \\ drule (GEN_ALL store_list_code_thm)
  \\ disch_then (qspecl_then [`0`,`k+1`,
       `(MAP (store_init gen_gc k) (REVERSE store_list))`,`s7`] mp_tac)
  \\ impl_tac THEN1
   (unabbrev_all_tac \\ fs [get_var_def] \\ tac
    \\ fs [EVERY_MAP]
    \\ fs [store_list_def] \\ EVAL_TAC
    \\ fs [FLOOKUP_DEF] \\ IF_CASES_TAC \\ fs [])
  \\ strip_tac \\ fs []
  \\ reverse IF_CASES_TAC \\ fs[]
  >- ( fs[Abbr`s7`,loc_check_def] )
  \\ qpat_abbrev_tac `s8 = s7 with <|regs := _ ; memory := _ |>`
  \\ fs [state_rel_def,GSYM CONJ_ASSOC]
  \\ rpt (conj_tac THEN1 (fs [init_reduce_def] \\ unabbrev_all_tac \\ fs []))
  \\ `FLOOKUP s8.regs (k + 1) = SOME (Word
          (n2w (d * h2 + d * LENGTH heap) +
           bytes_in_word * n2w (LENGTH store_list)))` by
    (unabbrev_all_tac \\ fs [FLOOKUP_UPDATE,FUPDATE_LIST] \\ NO_TAC)
  \\ fs [bytes_in_word_def,word_mul_n2w,word_add_n2w]
  \\ `s8.ffi_save_regs = s.ffi_save_regs` by
    (unabbrev_all_tac \\ fs [FLOOKUP_UPDATE,FUPDATE_LIST] \\ NO_TAC)
  \\ fs [init_reduce_stack_space,INSERT_SUBSET]
  \\ fs [init_reduce_def]
  \\ rpt (qpat_x_assum `evaluate _ = _` kall_tac)
  \\ drule MOD_LESS_EQ_MOD_IMP
  \\ impl_tac THEN1
   (unabbrev_all_tac
    \\ fs [labPropsTheory.good_dimindex_def,dimword_def,max_stack_alloc_def]
    \\ rfs [] \\ decide_tac) \\ strip_tac
  \\ qunabbrev_tac `s8`
  \\ qunabbrev_tac `s7`
  \\ fs [FUPDATE_LIST,FAPPLY_FUPDATE_THM,wordSemTheory.theWord_def,
         FLOOKUP_UPDATE,mem_val_def]
  \\ fs [store_init_def,store_list_def,UPDATE_LIST_def,APPLY_UPDATE_THM,
         FLOOKUP_UPDATE,word_store_def,mem_val_def,FAPPLY_FUPDATE_THM]
  \\ fs [FLOOKUP_DEF,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV,LENGTH_read_mem,
         wordSemTheory.theWord_def,init_prop_def,the_SOME_Word_def,
         is_SOME_Word_def, FLOOKUP_UPDATE]
  \\ fs [GSYM CONJ_ASSOC]
  \\ `read_mem (n2w (d * h2)) m1 (LENGTH heap) = heap` by
   (match_mp_tac(GEN_ALL(ONCE_REWRITE_RULE[STAR_COMM]word_list_IMP_read_mem))
    \\ fs [AC STAR_ASSOC STAR_COMM]
    \\ rename1`word_list (n2w(d*h2) + _) xxx`
    \\ metis_tac[STAR_ASSOC,STAR_COMM])
  \\ fs [mem_val_def,APPLY_UPDATE_THM,FAPPLY_FUPDATE_THM]
  \\ rfs [MAP_mem_val_MAP_INL]
  \\ `word_list
       (n2w (d * h2) + n2w (d * LENGTH bitst) + n2w (d * LENGTH heap)) rest1 *
      one (n2w (d * h2) + n2w (d * LENGTH bitst) +
        n2w (d * LENGTH heap) + n2w (d * LENGTH rest1):'a word,Word 0w) =
      word_list (n2w (d * h2) + n2w (d * LENGTH bitst) + n2w (d * LENGTH heap))
         (rest1 ++ [Word 0w])` by
   (fs [word_list_APPEND,word_list_def,SEP_CLAUSES,bytes_in_word_def,
        word_add_n2w,word_mul_n2w] \\ NO_TAC)
  \\ pop_assum (fn th => full_simp_tac std_ss [th])
  \\ fs [word_add_n2w]
  \\ `n2w (d * h2 + d * LENGTH heap) >>> word_shift (:'a) =
      n2w (h2 + LENGTH heap):'a word` by
   (simp_tac std_ss [GSYM w2n_11,w2n_lsr] \\ fs []
    \\ `2 ** word_shift (:'a) = d` by
     (unabbrev_all_tac
      \\ fs [labPropsTheory.good_dimindex_def,word_shift_def])
    \\ fs [GSYM LEFT_ADD_DISTRIB,ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
    \\ Cases_on `d` \\ fs [MULT_CLAUSES] \\ decide_tac)
  \\ fs []
  \\ `!ww:'a word. ww << word_shift (:'a) = ww * n2w d` by
   (`2 ** word_shift (:'a) = d` by
     (unabbrev_all_tac
      \\ fs [labPropsTheory.good_dimindex_def,word_shift_def])
    \\ fs [WORD_MUL_LSL] \\ NO_TAC)
  \\ fs [GSYM word_add_n2w,GSYM word_mul_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [word_mul_n2w,ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
  \\ `(LENGTH heap) * (dimindex (:'a) DIV 8) < dimword (:'a)` by rfs []
  \\ qmatch_goalsub_abbrev_tac`addresses _ lh`
  \\ `lh = LENGTH heap`
  by (
    simp[Abbr`lh`,GSYM LEFT_ADD_DISTRIB]
    \\ once_rewrite_tac[MULT_COMM]
    \\ simp[MULT_DIV] )
  \\ qunabbrev_tac`lh` \\ pop_assum SUBST_ALL_TAC
  \\ drule memory_addresses \\ fs []
  \\ disch_then kall_tac
  \\ qmatch_goalsub_abbrev_tac`read_mem a m1 b`
  \\ `read_mem a m1 (LENGTH (rest1 ++ [Word 0w])) = rest1 ++ [Word 0w]`
  by (
    match_mp_tac word_list_IMP_read_mem
    \\ fs[word_list_APPEND] \\ simp[word_list_def]
    \\ simp[bytes_in_word_def,word_mul_n2w,SEP_CLAUSES]
    \\ rename1`word_list (n2w(d*h2)+_) xxx`
    \\ metis_tac[STAR_ASSOC,STAR_COMM] )
  \\ fs[] \\ rfs[]
  \\ simp[word_list_APPEND,word_list_def,SEP_CLAUSES]
  \\ qmatch_asmsub_abbrev_tac`word_list aa xx * _`
  \\ `a = aa + n2w (LENGTH xx) * bytes_in_word`
  by (
    simp[Abbr`aa`,Abbr`a`,Abbr`xx`,bytes_in_word_def] \\
    simp[word_mul_n2w] )
  \\ first_assum SUBST1_TAC
  \\ qmatch_goalsub_abbrev_tac`word_list_rev _ yy`
  \\ `yy = REVERSE xx` by (
    simp[Abbr`xx`,Abbr`yy`]
    \\ Cases_on`gen_gc` \\ fs[] )
  \\ qunabbrev_tac`yy` \\ pop_assum SUBST_ALL_TAC
  \\ rewrite_tac[GSYM word_list_EQ_rev]
  \\ pop_assum (SUBST_ALL_TAC o GSYM)
  \\ fs[AC STAR_ASSOC STAR_COMM,bytes_in_word_def,word_mul_n2w]
  \\ Cases_on `gen_gc` \\ fs []
  \\ qexists_tac `hi`
  \\ fs [bytes_in_word_def,word_mul_n2w]
  \\ `n2w d = bytes_in_word` by fs [bytes_in_word_def]
  \\ fs [GSYM word_mul_n2w,GSYM word_list_exists_ADD]
  \\ `2 * hi = LENGTH heap` by
   (fs [DIV_EQ_X]
    \\ unabbrev_all_tac
    \\ fs [labPropsTheory.good_dimindex_def,bytes_in_word_def]
    \\ rfs [dimword_def] \\ fs [])
  \\ fs[]
  \\ (CONJ_TAC>-
    (CCONTR_TAC>>
    `dimword(:'a) ≤ LENGTH bitmaps+1` by fs[]>>
    `dimword(:'a) DIV d < LENGTH bitmaps` by
      (DEP_REWRITE_TAC [DIV_LT_X]>>
      `2 < d ∧ 0 < LENGTH bitmaps` by
        fs[Abbr`d`,labPropsTheory.good_dimindex_def]>>
      fs[]>>
      `LENGTH bitmaps +1 < LENGTH bitmaps * d` by
        (Cases_on`LENGTH bitmaps`>>fs[ADD1]>>
        Cases_on`d`>>fs[ADD1])>>
      fs[])>>
    fs[Abbr`d`]>>
    Q.ISPECL_THEN [`MAP Word bitmaps`,`bitmap_ptr`] mp_tac (GEN_ALL word_list_wrap)>>
    impl_tac>-
      fs[]>>
    strip_tac>>
    ntac 2 (pop_assum mp_tac)>>simp[word_list_def]>>
    strip_tac>>
    pop_assum SUBST_ALL_TAC>>
    SEP_NEQ_TAC>>fs[])
  \\ Cases_on`d`>>fs[Abbr`b`,ADD1]
  \\ fs[byte_aligned_bytes_in_word_MULT]
  \\ fs [] \\ match_mp_tac word_list_exists_addresses \\ fs []
  \\ match_mp_tac LESS_EQ_LESS_TRANS
  \\ qexists_tac `d * max_heap` \\ fs []));

val make_init_opt_def = Define `
  make_init_opt gen_gc max_heap bitmaps k code (s:('a,'ffi)stackSem$state) =
    case evaluate (init_code gen_gc max_heap k,s) of
    | (SOME _,t) => NONE
    | (NONE,t) => if init_prop gen_gc max_heap (init_reduce gen_gc k code bitmaps t)
                  then SOME (init_reduce gen_gc k code bitmaps t) else NONE`

val init_pre_def = Define `
  init_pre gen_gc max_heap bitmaps k start s <=>
    lookup 0 s.code = SOME (Seq (init_code gen_gc max_heap k)
                                (Call NONE (INL start) NONE)) /\
    (* TODO: remove: *) s.ffi.final_event = NONE /\
    init_code_pre k bitmaps s`

val evaluate_init_code = Q.store_thm("evaluate_init_code",
  `init_pre gen_gc max_heap bitmaps k start s /\
    lookup stack_err_lab s.code = SOME (halt_inst 2w) /\
    code_rel jump off k code s.code ==>
    case evaluate (init_code gen_gc max_heap k,s) of
    | (SOME (Halt (Word w)),t) =>
        w <> 0w /\ t.ffi = s.ffi /\
        make_init_opt gen_gc max_heap bitmaps k code s = NONE
    | (NONE,t) => ?r. make_init_opt gen_gc max_heap bitmaps k code s = SOME r /\
                      state_rel jump off k r t /\ t.ffi = s.ffi
    | _ => F`,
  strip_tac \\ fs [init_pre_def]
  \\ drule init_code_thm \\ fs []
  \\ CASE_TAC \\ CASE_TAC
  \\ fs [make_init_opt_def]
  \\ strip_tac \\ fs[]);

val clock_neutral_store_list_code = Q.store_thm("clock_neutral_store_list_code",
  `!xs n k. clock_neutral (store_list_code n k xs)`,
  Induct \\ fs [clock_neutral_def,store_list_code_def]
  \\ Cases \\ fs [clock_neutral_def,store_list_code_def,list_Seq_def]);

val evaluate_init_code_clock = Q.prove(
  `evaluate (init_code gen_gc max_heap k,s) = (res,t) ==>
    evaluate (init_code gen_gc max_heap k,s with clock := c) =
      (res,t with clock := c)`,
  srw_tac[][] \\ match_mp_tac evaluate_clock_neutral \\ fs []
  \\ fs [clock_neutral_def,init_code_def] \\ rw []
  \\ fs [clock_neutral_def,init_code_def,halt_inst_def,
         list_Seq_def,init_memory_def,clock_neutral_store_list_code]);

val evaluate_init_code_ffi = Q.prove(
  `evaluate (init_code gen_gc max_heap k,(s:('a,'ffi) stackSem$state)) = (res,t) ==>
    evaluate (init_code gen_gc max_heap k,s with ffi := c) =
      (res,(t with ffi := c):('a,'ffi) stackSem$state)`,
  srw_tac[][] \\ match_mp_tac evaluate_ffi_neutral \\ fs []
  \\ fs [clock_neutral_def,init_code_def] \\ rw []
  \\ fs [clock_neutral_def,init_code_def,halt_inst_def,
         list_Seq_def,init_memory_def,clock_neutral_store_list_code]);

val init_semantics = Q.store_thm("init_semantics",
  `lookup stack_err_lab s.code = SOME (halt_inst 2w) /\
    code_rel jump off k code s.code /\
    init_pre gen_gc max_heap bitmaps k start s ==>
    case evaluate (init_code gen_gc max_heap k,s) of
    | (SOME (Halt _),t) =>
        (semantics 0 s = Terminate Resource_limit_hit s.ffi.io_events) /\
        make_init_opt gen_gc max_heap bitmaps k code s = NONE
    | (NONE,t) =>
        (semantics 0 s = semantics start t) /\
        ?r. make_init_opt gen_gc max_heap bitmaps k code s = SOME r /\ state_rel jump off k r t
    | _ => F`,
  srw_tac[][]
  \\ pop_assum (fn th => assume_tac th \\ mp_tac th)
  \\ simp_tac std_ss [init_pre_def] \\ rw []
  \\ imp_res_tac evaluate_init_code
  \\ reverse every_case_tac \\ full_simp_tac(srw_ss())[] THEN1
   (full_simp_tac(srw_ss())[semantics_def |> Q.SPEC `0`,LET_DEF,
           evaluate_def,find_code_def]
    \\ match_mp_tac (METIS_PROVE [] ``~b /\ y = z ==> (if b then x else y) = z``)
    \\ conj_tac THEN1
     (full_simp_tac(srw_ss())[] \\ srw_tac[][dec_clock_def]
      \\ imp_res_tac evaluate_init_code_clock \\ full_simp_tac(srw_ss())[])
    \\ DEEP_INTRO_TAC some_intro \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[dec_clock_def]
    \\ imp_res_tac evaluate_init_code_clock \\ full_simp_tac(srw_ss())[]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]
    \\ qexists_tac `1` \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[semantics_def |> Q.SPEC `0`,LET_DEF]
  \\ once_rewrite_tac [evaluate_def] \\ full_simp_tac(srw_ss())[find_code_def]
  \\ once_rewrite_tac [evaluate_def] \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ full_simp_tac(srw_ss())[dec_clock_def]
  \\ imp_res_tac evaluate_init_code_clock \\ full_simp_tac(srw_ss())[]
  \\ pop_assum (K all_tac)
  \\ full_simp_tac(srw_ss())[semantics_def,LET_DEF]
  \\ match_mp_tac (METIS_PROVE []
      ``x1 = x2 /\ (x1 /\ x2 ==> y1 = y2) /\ (~x1 /\ ~x2 ==> z1 = z2) ==>
        (if x1 then y1 else z1) = (if x2 then y2 else z2)``)
  \\ conj_tac \\ full_simp_tac(srw_ss())[] THEN1
   (EQ_TAC \\ strip_tac THEN1
     (Cases_on `k' = 0` \\ full_simp_tac(srw_ss())[]
      \\ qexists_tac `k'-1` \\ full_simp_tac(srw_ss())[]
      \\ every_case_tac \\ full_simp_tac(srw_ss())[])
    \\ qexists_tac `k' + 1` \\ full_simp_tac(srw_ss())[]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ strip_tac
  \\ match_mp_tac (METIS_PROVE []
      ``x1 = x2 /\ y1 = y2 /\ z1 = z2 ==> f x1 y1 z1 = f x2 y2 z2``)
  \\ conj_tac \\ full_simp_tac(srw_ss())[] THEN1
   (AP_TERM_TAC \\ full_simp_tac(srw_ss())[FUN_EQ_THM]
    \\ srw_tac[][] \\ reverse EQ_TAC \\ strip_tac
    THEN1 (qexists_tac `k' + 1` \\ full_simp_tac(srw_ss())[])
    \\ qexists_tac `k' - 1` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `k' = 0` \\ full_simp_tac(srw_ss())[]
     THEN1 (srw_tac[][] \\ full_simp_tac(srw_ss())[empty_env_def]
            \\ rev_full_simp_tac(srw_ss())[])
    \\ Cases_on `evaluate (Call NONE (INL start) NONE,r with clock := k' - 1)`
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `q`
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ first_x_assum (qspec_then`k'-1`mp_tac) \\ full_simp_tac(srw_ss())[])
  \\ AP_TERM_TAC \\ full_simp_tac(srw_ss())[EXTENSION]
  \\ srw_tac[][] \\ reverse EQ_TAC \\ strip_tac
  THEN1 (full_simp_tac(srw_ss())[] \\ qexists_tac `k' + 1`
         \\ full_simp_tac(srw_ss())[] \\ every_case_tac
         \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[] \\ qexists_tac `k' - 1`
  \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `k' = 0` \\ full_simp_tac(srw_ss())[]
  THEN1 (full_simp_tac(srw_ss())[evaluate_def,empty_env_def]
         \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]);

val make_init_opt_SOME_semantics = Q.store_thm("make_init_opt_SOME_semantics",
  `init_pre gen_gc max_heap bitmaps k start s2 /\
    code_rel jump off k code s2.code /\
    lookup stack_err_lab s2.code = SOME (halt_inst 2w) /\
    make_init_opt gen_gc max_heap bitmaps k code s2 = SOME s1 /\
    semantics start s1 <> Fail ==>
    semantics 0 s2 IN extend_with_resource_limit {semantics start s1}`,
  srw_tac[][] \\ imp_res_tac init_semantics \\ pop_assum (assume_tac o SPEC_ALL)
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ match_mp_tac (GEN_ALL compile_semantics)
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ metis_tac []);

val make_init_opt_NONE_semantics = Q.store_thm("make_init_opt_NONE_semantics",
  `init_pre gen_gc max_heap bitmaps k start s2 /\ code_rel jump off k code s2.code /\
    lookup stack_err_lab s2.code = SOME (halt_inst 2w) /\
    make_init_opt gen_gc max_heap bitmaps k code s2 = NONE ==>
    semantics 0 s2 = Terminate Resource_limit_hit s2.ffi.io_events`,
  srw_tac[][] \\ imp_res_tac init_semantics \\ pop_assum (assume_tac o SPEC_ALL)
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[extend_with_resource_limit_def]);

val prog_comp_eta = Q.store_thm("prog_comp_eta",
  `prog_comp = \jump off k (n,p). (n,comp jump off k p)`,
  srw_tac[][FUN_EQ_THM,prog_comp_def,FORALL_PROD,LAMBDA_PROD]);

val IMP_code_rel = Q.prove(
  `EVERY (\(n,p). reg_bound p k /\ num_stubs ≤ n+1) code1 /\
   code2 = fromAList (compile jump off gen_gc max_heap k start code1) ==>
   code_rel jump off k (fromAList code1) code2`,
  full_simp_tac(srw_ss())[code_rel_def,lookup_fromAList]
  \\ strip_tac \\ rpt var_eq_tac
  \\ full_simp_tac(srw_ss())[ALOOKUP_def,compile_def,init_stubs_def] \\ rw []
  \\ imp_res_tac ALOOKUP_MEM
  \\ imp_res_tac EVERY_MEM \\ full_simp_tac(srw_ss())[]
  \\ simp[prog_comp_eta,ALOOKUP_MAP_gen]
  \\ pop_assum mp_tac \\ EVAL_TAC);

val make_init_any_def = Define `
  make_init_any gen_gc max_heap bitmaps k code s =
    case make_init_opt gen_gc max_heap bitmaps k code s of
    | SOME t => t
    | NONE => s with <| regs := FEMPTY |+ (0,Loc 1 0)
                      ; fp_regs := FEMPTY
                      ; mdomain := EMPTY
                      ; bitmaps := [4w]
                      ; use_stack := T
                      ; use_store := T
                      ; use_alloc := F
                      ; stack := [Word 0w]
                      ; stack_space := 0
                      ; code := code
                      ; store := FEMPTY |++ (MAP (\x. (x,Word 0w))
                                   (CurrHeap::store_list)) |>`

val discharge_these_def = Define`
  discharge_these jump off gen_gc max_heap k start code s2 ⇔
      EVERY (\(n,p). reg_bound p k /\ num_stubs ≤ n+1) code /\
      s2.code = fromAList (compile jump off gen_gc max_heap k start code)
       ∧ 8 ≤ k ∧ 1 ∈ domain s2.code ∧
      {k; k + 1; k + 2} ⊆ s2.ffi_save_regs ∧ ¬s2.use_stack ∧
      ¬s2.use_store ∧ ¬s2.use_alloc`;

val propagate_these_def = Define`
  propagate_these s (bitmaps:'a word list) ⇔
  good_dimindex(:'a) /\ s.ffi.final_event = NONE /\
  ∃ptr2 ptr3 ptr4 bitmap_ptr.
       FLOOKUP s.regs 2 = SOME (Word ptr2) ∧
       FLOOKUP s.regs 3 = SOME (Word ptr3) ∧
       FLOOKUP s.regs 4 = SOME (Word ptr4) ∧
       s.memory ptr2 = Word bitmap_ptr ∧
       (ptr2 ≤₊ ptr4 ∧ byte_aligned ptr2 ∧ byte_aligned ptr4 ⇒
        (word_list bitmap_ptr (MAP Word bitmaps) *
         word_list_exists ptr2
           (w2n (ptr4 − ptr2) DIV w2n (bytes_in_word:'a word)))
          (fun2set (s.memory,s.mdomain)))`;

val make_init_semantics = Q.store_thm("make_init_semantics",
  `discharge_these jump off gen_gc max_heap k start code s2 /\
   propagate_these s2 bitmaps /\
   make_init_opt gen_gc max_heap (bitmaps:'a word list) k (fromAList code) s2 = SOME s1 /\
   semantics start s1 <> Fail
    ==>
    semantics 0 s2 IN extend_with_resource_limit {semantics start s1}`,
  rw[discharge_these_def]
  \\ imp_res_tac IMP_code_rel
  \\ imp_res_tac make_init_opt_SOME_semantics
  \\ pop_assum kall_tac
  \\ pop_assum mp_tac
  \\ impl_tac
  >- (
    fs[compile_def,lookup_fromAList]
    \\ EVAL_TAC )
  \\ impl_tac
  >- (
    fs[init_pre_def,init_code_pre_def,propagate_these_def]
    \\ simp[lookup_fromAList,compile_def,ALOOKUP_APPEND]
    \\ EVAL_TAC )
  \\ rw[]);

val make_init_semantics_fail = Q.store_thm("make_init_semantics_fail",
  `discharge_these jump off gen_gc max_heap k start code s2 /\
   propagate_these s2 bitmaps /\
   make_init_opt gen_gc max_heap (bitmaps:'a word list) k (fromAList code) s2 = NONE
   ==>
   semantics 0 s2 = Terminate Resource_limit_hit s2.ffi.io_events`,
  rw[discharge_these_def]
  \\ imp_res_tac IMP_code_rel
  \\ imp_res_tac make_init_opt_NONE_semantics
  \\ pop_assum kall_tac
  \\ pop_assum mp_tac
  \\ impl_tac
  >- (
    fs[compile_def,lookup_fromAList]
    \\ EVAL_TAC )
  \\ disch_then(qspec_then`start`mp_tac)
  \\ impl_tac
  >- (
    fs[init_pre_def,init_code_pre_def,propagate_these_def]
    \\ simp[lookup_fromAList,compile_def,ALOOKUP_APPEND]
    \\ EVAL_TAC )
  \\ rw[]);

val make_init_any_ffi = Q.store_thm("make_init_any_ffi",
  `(make_init_any gen_gc max_heap bitmaps k code s).ffi =
    (s:('a,'ffi) stackSem$state).ffi`,
  fs [make_init_any_def,make_init_opt_def,init_reduce_def]
  \\ every_case_tac \\ fs []
  \\ imp_res_tac evaluate_init_code_ffi
  \\ pop_assum (qspec_then `s.ffi` mp_tac)
  \\ `s with ffi := s.ffi = s` by fs [state_component_equality]
  \\ fs [] \\ fs [state_component_equality]);

val make_init_any_bitmaps = Q.store_thm("make_init_any_bitmaps",
  `(make_init_any gen_gc max_heap bitmaps k code s).bitmaps =
       if IS_SOME (make_init_opt gen_gc max_heap bitmaps k code s)
       then bitmaps else [4w]`,
  fs [make_init_any_def,make_init_opt_def,init_reduce_def]
  \\ every_case_tac \\ fs []);

val make_init_any_use_stack = Q.store_thm("make_init_any_use_stack",
  `(make_init_any gen_gc max_heap bitmaps k code s).use_stack`,
  fs [make_init_any_def,make_init_opt_def,init_reduce_def]
  \\ every_case_tac \\ fs []);

val make_init_any_use_store = Q.store_thm("make_init_any_use_store",
  `(make_init_any gen_gc max_heap bitmaps k code s).use_store`,
  fs [make_init_any_def,make_init_opt_def,init_reduce_def]
  \\ every_case_tac \\ fs []);

val make_init_any_use_alloc = Q.store_thm("make_init_any_use_alloc",
  `~(make_init_any gen_gc max_heap bitmaps k code s).use_alloc`,
  fs [make_init_any_def,make_init_opt_def,init_reduce_def]
  \\ every_case_tac \\ fs []);

val make_init_any_code = Q.store_thm("make_init_any_code",
  `(make_init_any gen_gc max_heap bitmaps k code s).code = code`,
  fs [make_init_any_def,make_init_opt_def,init_reduce_def]
  \\ every_case_tac \\ fs []);

val make_init_any_stack_limit = Q.store_thm("make_init_any_stack_limit",
  `LENGTH ((make_init_any gen_gc max_heap (bitmaps:'a word list) k code s).stack) *
      (dimindex (:'a) DIV 8) < dimword (:'a)`,
  fs [make_init_any_def]
  \\ reverse (every_case_tac \\ fs [LENGTH_read_mem])
  \\ fs [make_init_opt_def]
  \\ reverse (every_case_tac \\ fs [LENGTH_read_mem])
  \\ fs [init_prop_def] \\ fs [dimword_def] \\ fs [DIV_LT_X]
  \\ match_mp_tac LESS_EQ_LESS_TRANS
  \\ qexists_tac `8 * dimindex (:'a)` \\ fs []
  \\ fs [X_LT_EXP_X_IFF]);

(* Syntactic *)

val stack_remove_lab_pres = Q.store_thm("stack_remove_lab_pres",`
  ∀jump off k p.
  extract_labels p = extract_labels (comp jump off k p)`,
  ho_match_mp_tac comp_ind>>Cases_on`p`>>rw[]>>
  once_rewrite_tac [comp_def]>>fs[extract_labels_def]>>
  TRY(IF_CASES_TAC)>>
  fs[extract_labels_def,stack_store_def,stack_load_def]
  >- (BasicProvers.EVERY_CASE_TAC>>fs[])
  >-
    (qid_spec_tac`n`>>completeInduct_on`n`>>rw[Once stack_alloc_def]>>
    fs[single_stack_alloc_def]>> rw[]>> fs[ extract_labels_def,halt_inst_def]>>
    first_assum match_mp_tac>>
    fs[max_stack_alloc_def])
  >-
    (qid_spec_tac`n`>>completeInduct_on`n`>>rw[Once stack_free_def]>>
    fs[extract_labels_def,single_stack_free_def]>>
    first_assum match_mp_tac>>
    fs[max_stack_alloc_def])
  >-
    (pop_assum kall_tac>>rw[]>>completeInduct_on`n0`>>rw[Once upshift_def,Once downshift_def]>>
    fs[extract_labels_def]>>
    first_assum match_mp_tac>>
    fs[max_stack_alloc_def])
  >-
    (pop_assum kall_tac>>rw[]>>completeInduct_on`n0`>>rw[Once upshift_def,Once downshift_def]>>
    fs[extract_labels_def]>>
    first_assum match_mp_tac>>
    fs[max_stack_alloc_def])
  >- EVAL_TAC);

val stack_remove_comp_stack_asm_name = Q.prove(`
  ∀jump off k p.
  stack_asm_name c p ∧ stack_asm_remove (c:'a asm_config) p ∧
  addr_offset_ok c 0w ∧
  good_dimindex (:'a) ∧
  (∀n. n ≤ max_stack_alloc ⇒
  c.valid_imm (INL Sub) (n2w (n * (dimindex (:'a) DIV 8))) ∧
  c.valid_imm (INL Add) (n2w (n * (dimindex (:'a) DIV 8)))) ∧
  (* Needed to implement the global store *)
  (∀s. addr_offset_ok c (store_offset s)) ∧
  reg_name (k+2) c ∧
  reg_name (k+1) c ∧
  reg_name k c ∧
  off = c.addr_offset ⇒
  stack_asm_name c (comp jump off k p)`,
  ho_match_mp_tac comp_ind>>Cases_on`p`>>rw[]>>
  simp[Once comp_def]>>
  rw[]>>
  fs[stack_asm_name_def,inst_name_def,stack_asm_remove_def,addr_name_def,arith_name_def,reg_imm_name_def,stackLangTheory.list_Seq_def]
  >-
    (every_case_tac>>fs[])
  >-
    (* stack alloc *)
    (completeInduct_on`n`>>
    simp[Once stack_alloc_def]>>rw[]
    >-
      EVAL_TAC
    >-
      (EVAL_TAC>>rw[]>>EVAL_TAC>>fs[reg_name_def])
    >>
      rw[stack_asm_name_def]
      >-
        (EVAL_TAC>>rw[]>>EVAL_TAC>>fs[reg_name_def,max_stack_alloc_def])
      >>
        first_x_assum(qspec_then `n-max_stack_alloc` assume_tac)>>fs[]>>
        rfs[max_stack_alloc_def])
  >- (* stack free *)
    (completeInduct_on`n`>>
    simp[Once stack_free_def]>>rw[]
    >-
      EVAL_TAC
    >-
      (EVAL_TAC>>fs[reg_name_def])
    >>
      rw[stack_asm_name_def]
      >-
        (EVAL_TAC>>fs[reg_name_def,max_stack_alloc_def])
      >>
        first_x_assum(qspec_then `n-max_stack_alloc` assume_tac)>>fs[]>>
        rfs[max_stack_alloc_def])
  >>
    fs[labPropsTheory.good_dimindex_def,word_shift_def]
  >>
    simp[stack_load_def,stack_store_def,stack_asm_name_def,inst_name_def,addr_name_def]>>
    qpat_assum`!n. A ⇒ B` mp_tac>>
    rpt(qpat_x_assum`reg_name _ c` mp_tac)>>
    rpt (pop_assum kall_tac)>>
    rw[]>>completeInduct_on`n0`>>
    simp[Once upshift_def,Once downshift_def]>>rw[]>>
    fs[stack_asm_name_def,inst_name_def,arith_name_def,reg_imm_name_def,word_offset_def]>>
    first_x_assum match_mp_tac>>fs[max_stack_alloc_def]
  );

val stack_remove_stack_asm_name = Q.store_thm("stack_remove_stack_asm_name",`
  EVERY (λ(n,p). stack_asm_name c p) prog ∧
  EVERY (λ(n,p). (stack_asm_remove (c:'a asm_config) p)) prog ∧
  addr_offset_ok c 0w ∧
  good_dimindex (:'a) ∧
  (∀n. n ≤ max_stack_alloc ⇒
  c.valid_imm (INL Sub) (n2w (n * (dimindex (:'a) DIV 8))) ∧
  c.valid_imm (INL Add) (n2w (n * (dimindex (:'a) DIV 8)))) ∧
  c.valid_imm (INL Add) 4w ∧
  c.valid_imm (INL Add) 8w ∧
  (* Needed to implement the global store *)
  (∀s. addr_offset_ok c (store_offset s)) ∧
  reg_name 5 c ∧
  reg_name (k+2) c ∧
  reg_name (k+1) c ∧
  reg_name k c ⇒
  EVERY (λ(n,p). stack_asm_name c p)
  (compile jump c.addr_offset gen_gc max_heap k start prog)`,
  rw[compile_def]
  >-
    (fs[labPropsTheory.good_dimindex_def]>>EVAL_TAC>>fs[]>>rw[]>>EVAL_TAC>>fs[reg_name_def]>>
    pairarg_tac>>fs[asmTheory.offset_ok_def]>>
    Induct_on`bitmaps`>>rw[]>>
    EVAL_TAC>>fs[])
  >>
    fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,prog_comp_def]>>
    metis_tac[stack_remove_comp_stack_asm_name]);

val upshift_downshift_call_args = Q.store_thm("upshift_downshift_call_args",`
  ∀n n0.
  call_args (upshift n n0) 1 2 3 4 0 ∧
  call_args (downshift n n0) 1 2 3 4 0`,
  completeInduct_on`n0`>>
  simp[Once stack_removeTheory.upshift_def,Once stack_removeTheory.downshift_def]>>
  strip_tac>>IF_CASES_TAC>>
  fs[call_args_def]>>
  first_assum match_mp_tac>>EVAL_TAC>>fs[]);

val stack_remove_call_args = Q.store_thm("stack_remove_call_args",
  `compile jump off gen_gc n k pos p = p' /\
    EVERY (λp. call_args p 1 2 3 4 0) (MAP SND p) ==>
    EVERY (λp. call_args p 1 2 3 4 0) (MAP SND p')`,
  rw[]>>
  unabbrev_all_tac>>fs[]>>
  EVAL_TAC>>
  IF_CASES_TAC>>EVAL_TAC>>
  pop_assum kall_tac>>
  fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,stack_removeTheory.prog_comp_def]>>
  TRY(CONJ_TAC>-
    (Induct_on`bitmaps`>>fs[stack_removeTheory.store_list_code_def]>>
    EVAL_TAC>>fs[]))>>
  (
  rw[]>>res_tac>>
  pop_assum mp_tac>> rpt (pop_assum kall_tac)>>
  map_every qid_spec_tac[`p_2`,`k`,`off`,`jump`]>>
  ho_match_mp_tac stack_removeTheory.comp_ind>>
  Cases_on`p_2`>>rw[]>>
  ONCE_REWRITE_TAC [stack_removeTheory.comp_def]>>
  fs[call_args_def]>>
  TRY(IF_CASES_TAC>>fs[call_args_def])
  >-
    (BasicProvers.EVERY_CASE_TAC>>fs[])
  >>
  TRY (* stack_alloc and stack_free *)
    (completeInduct_on`n`>>simp[Once stack_removeTheory.stack_alloc_def,stack_removeTheory.single_stack_alloc_def,Once stack_removeTheory.stack_free_def,stack_removeTheory.single_stack_free_def,stack_removeTheory.halt_inst_def]>>
    rpt (IF_CASES_TAC>>fs[call_args_def])>>
    first_assum match_mp_tac>>
    EVAL_TAC>>fs[]>>NO_TAC)>>
  simp[stack_removeTheory.stack_store_def,stack_removeTheory.stack_load_def,call_args_def,upshift_downshift_call_args]
  >- EVAL_TAC));

val _ = export_theory();
