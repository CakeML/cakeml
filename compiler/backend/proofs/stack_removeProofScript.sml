open preamble
     stack_removeTheory
     stackSemTheory
     stackPropsTheory
     set_sepTheory
     semanticsPropsTheory
     helperLib

val _ = new_theory"stack_removeProof";

(* TODO: move *)

val word_list_APPEND = store_thm("word_list_APPEND",
  ``!xs ys a.
      word_list a (xs ++ ys) =
      word_list a xs * word_list (a + bytes_in_word * n2w (LENGTH xs)) ys``,
  Induct \\ fs [word_list_def,SEP_CLAUSES,STAR_ASSOC,ADD1,GSYM word_add_n2w]
  \\ fs [WORD_LEFT_ADD_DISTRIB]);

val read_bytearray_def = wordSemTheory.read_bytearray_def

val read_bytearray_LENGTH = Q.store_thm("read_bytearray_LENGTH",
  `!n a m d y be. (read_bytearray a n m d be = SOME y) ==> (LENGTH y = n)`,
  Induct >> rw[read_bytearray_def,LENGTH_NIL]
  \\ every_case_tac >> fs[] >> rw[]
  \\ res_tac);

val call_FFI_LENGTH = Q.store_thm("call_FFI_LENGTH",
  `(call_FFI s i xs = (n,ys)) ==> (LENGTH ys = LENGTH xs)`,
  rw[ffiTheory.call_FFI_def]
  \\ every_case_tac >> fs[] >> rw[]);

(* --- *)

val good_syntax_def = Define `
  (good_syntax (Halt v1) k <=>
     v1 < k) /\
  (good_syntax (Raise v1) k <=>
     v1 < k) /\
  (good_syntax (Get v1 n) k <=>
     v1 < k) /\
  (good_syntax (Set n v1) k <=>
     v1 < k /\ n <> BitmapBase) /\
  (good_syntax (LocValue v1 l1 l2) k <=>
     v1 < k) /\
  (good_syntax (Return v1 v2) k <=>
     v1 < k /\ v2 < k) /\
  (good_syntax (JumpLess v1 v2 dest) k <=>
     v1 < k /\ v2 < k) /\
  (good_syntax ((Seq p1 p2):'a stackLang$prog) k <=>
     good_syntax p1 k /\ good_syntax p2 k) /\
  (good_syntax ((If c r ri p1 p2):'a stackLang$prog) k <=>
     r < k /\ (case ri of Reg n => n < k | _ => T) /\
     good_syntax p1 k /\ good_syntax p2 k) /\
  (good_syntax (Halt n) k <=> n < k) /\
  (good_syntax (FFI ffi_index ptr' len' ret') k <=>
     ptr' < k /\ len' < k /\ ret' < k) /\
  (good_syntax (Call x1 dest x2) k <=>
     (case dest of INR i => i < k | _ => T) /\
     (case x1 of
      | SOME (y,r,_,_) => good_syntax y k /\ r < k
      | NONE => T) /\
     (case x2 of SOME (y,_,_) => good_syntax y k | NONE => T)) /\
  (good_syntax (BitmapLoad r v) k <=> r < k /\ v < k) /\
  (good_syntax _ k <=> T)`

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
  code_rel k code1 code2 <=>
    !n prog.
      lookup n code1 = SOME prog ==>
      good_syntax prog k /\
      lookup n code2 = SOME (comp k prog)`

val is_SOME_Word_def = Define `
  (is_SOME_Word (SOME (Word w)) = T) /\
  (is_SOME_Word _ = F)`;

val the_SOME_Word_def = Define `
  (the_SOME_Word (SOME (Word w)) = w)`;

val state_rel_def = Define `
  state_rel k (s1:('a,'ffi) stackSem$state) s2 <=>
    s1.use_stack /\ s1.use_store /\
    ~s2.use_stack /\ ~s2.use_store /\
    ~s2.use_alloc /\ ~s1.use_alloc /\
    s2.be = s1.be /\
    s2.gc_fun = s1.gc_fun /\
    s2.clock = s1.clock /\
    s2.ffi = s1.ffi /\
    s2.ffi_save_regs = s1.ffi_save_regs /\
    good_dimindex (:'a) /\
    (!n.
       n < k ==>
       FLOOKUP s2.regs n = FLOOKUP s1.regs n) /\
    code_rel k s1.code s2.code /\
    FLOOKUP s2.regs (k+2) = FLOOKUP s1.store CurrHeap /\
    {k;k+1;k+2} SUBSET s2.ffi_save_regs /\
    is_SOME_Word (FLOOKUP s1.store BitmapBase) /\
    case FLOOKUP s2.regs (k+1) of
    | SOME (Word base) =>
      dimindex (:'a) DIV 8 * max_stack_alloc <= w2n base /\
      FLOOKUP s2.regs k =
        SOME (Word (base + bytes_in_word * n2w s1.stack_space)) /\
      (memory s1.memory s1.mdomain *
       word_list (the_SOME_Word (FLOOKUP s1.store BitmapBase) << word_shift (:'a))
         (MAP Word s1.bitmaps) *
       word_store base s1.store *
       word_list base s1.stack)
        (fun2set (s2.memory,s2.mdomain))
    | _ => F`

val state_rel_get_var = prove(
  ``state_rel k s t /\ n < k ==> (get_var n s = get_var n t)``,
  fs [state_rel_def,get_var_def]);

val state_rel_IMP = prove(
  ``state_rel k s t1 ==>
    state_rel k (dec_clock s) (dec_clock t1)``,
  rw [] \\ fs [state_rel_def,dec_clock_def,empty_env_def] \\ rfs [] \\ fs []
  \\ rw [] \\ res_tac \\ fs [])

val find_code_lemma = prove(
  ``state_rel k s t1 /\
    (case dest of INL v2 => T | INR i => i < k) /\
    find_code dest s.regs s.code = SOME x ==>
    find_code dest t1.regs t1.code = SOME (comp k x) /\ good_syntax x k``,
  CASE_TAC \\ fs [find_code_def,state_rel_def,code_rel_def]
  \\ strip_tac \\ res_tac
  \\ CASE_TAC \\ fs [] \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ fs [] \\ res_tac);

val state_rel_set_var = store_thm("state_rel_set_var[simp]",
  ``state_rel k s t1 /\ v < k ==>
    state_rel k (set_var v x s) (set_var v x t1)``,
  fs [state_rel_def,set_var_def] \\ rw [] \\ fs [FLOOKUP_UPDATE]
  \\ rw [] \\ fs [] \\ rfs [] \\ `F` by decide_tac);

val word_store_CurrHeap = prove(
  ``word_store base (s.store |+ (CurrHeap,x)) = word_store base s.store``,
  fs [word_store_def,store_list_def,FLOOKUP_UPDATE]);

val LESS_LENGTH_IMP_APPEND = prove(
  ``!xs n. n < LENGTH xs ==> ?ys zs. xs = ys ++ zs /\ LENGTH ys = n``,
  Induct \\ fs [] \\ Cases_on `n` \\ fs [LENGTH_NIL]
  \\ rw [] \\ res_tac \\ rw []
  \\ pop_assum (fn th => simp [Once th])
  \\ qexists_tac `h::ys` \\ fs [])

val memory_fun2set_IMP_read = prove(
  ``(memory m d * p) (fun2set (m1,d1)) /\ a IN d ==>
    a IN d1 /\ m1 a = m a``,
  simp [Once STAR_def,set_sepTheory.SPLIT_EQ,memory_def]
  \\ fs [fun2set_def,SUBSET_DEF,PULL_EXISTS]);

val state_rel_read = prove(
  ``state_rel k s t /\ a IN s.mdomain ==>
    a IN t.mdomain /\ (t.memory a = s.memory a)``,
  fs [state_rel_def] \\ every_case_tac \\ fs [] \\ strip_tac
  \\ fs [GSYM STAR_ASSOC] \\ metis_tac [memory_fun2set_IMP_read]);

val mem_load_byte_aux_IMP = prove(
  ``state_rel k s t /\
    mem_load_byte_aux a s.memory s.mdomain s.be = SOME x ==>
    mem_load_byte_aux a t.memory t.mdomain t.be = SOME x``,
  fs [wordSemTheory.mem_load_byte_aux_def] \\ rw []
  \\ `s.be = t.be` by fs [state_rel_def]
  \\ every_case_tac \\ fs [] \\ rw []
  \\ imp_res_tac state_rel_read
  \\ fs [] \\ rfs [] \\ rw [] \\ fs []);

val read_bytearray_IMP_read_bytearray = prove(
  ``!n a k s t x.
      state_rel k s t /\
      read_bytearray a n s.memory s.mdomain s.be = SOME x ==>
      read_bytearray a n t.memory t.mdomain t.be = SOME x``,
  Induct \\ fs [wordSemTheory.read_bytearray_def]
  \\ rw [] \\ every_case_tac \\ fs [] \\ res_tac \\ rw []
  \\ imp_res_tac mem_load_byte_aux_IMP \\ fs [] \\ rw [] \\ fs []);

val write_bytearray_NEQ_IMP = prove(
  ``write_bytearray a new_bytes m d be xx ≠
    write_bytearray a new_bytes m1 d1 be xx ==>
    m1 xx = m xx``,
  cheat); (* easy *)

val write_bytearray_IGNORE = prove(
  ``read_bytearray a (LENGTH new_bytes) m1 d1 be = SOME x /\ xx ∉ d1 ==>
    write_bytearray a new_bytes m d be xx = m xx``,
  cheat); (* easy *)

val write_bytearray_lemma = prove(
  ``!new_bytes a m1 d1 be x p m d.
      (memory m1 d1 * p) (fun2set (m,d)) /\
      read_bytearray a (LENGTH new_bytes) m1 d1 be = SOME x ==>
      (memory (write_bytearray a new_bytes m1 d1 be) d1 * p)
        (fun2set (write_bytearray a new_bytes m d be,d))``,
  simp [STAR_def,set_sepTheory.SPLIT_EQ,memory_def]
  \\ fs [fun2set_def,SUBSET_DEF,PULL_EXISTS] \\ rw []
  THEN1 (res_tac \\ fs [] \\ metis_tac [write_bytearray_NEQ_IMP])
  \\ qpat_assum `p xx` mp_tac
  \\ match_mp_tac (METIS_PROVE [] ``(x=y)==>x==>y``) \\ AP_TERM_TAC
  \\ fs [EXTENSION] \\ rw [] \\ EQ_TAC \\ rw []
  \\ CCONTR_TAC \\ fs [] \\ rw []
  \\ res_tac \\ fs []
  \\ pop_assum mp_tac \\ fs []
  \\ qcase_tac `xx IN d`
  \\ Cases_on `xx IN d1` \\ res_tac \\ fs []
  \\ imp_res_tac write_bytearray_IGNORE
  \\ fs [] \\ metis_tac [write_bytearray_NEQ_IMP]);

val comp_correct = Q.prove(
  `!p s1 r s2 t1 k.
     evaluate (p,s1) = (r,s2) /\ r <> SOME Error /\
     state_rel k s1 t1 /\ good_syntax p k ==>
     ?r2 t2. evaluate (comp k p,t1) = (r2,t2) /\
             (case r2 of
               | SOME (Halt _) =>
                   t2.ffi.io_events ≼ s2.ffi.io_events ∧
                   (IS_SOME t2.ffi.final_event ⇒ t2.ffi = s2.ffi)
               | SOME TimeOut => r2 = r /\ t2.ffi = s2.ffi
               | _ =>  (r2 = r /\ state_rel k s2 t2))`,
  recInduct evaluate_ind \\ rpt strip_tac
  THEN1 (fs [comp_def,evaluate_def] \\ rpt var_eq_tac \\ fs [])
  THEN1
   (fs [comp_def,evaluate_def,good_syntax_def]
    \\ imp_res_tac state_rel_get_var \\ fs []
    \\ every_case_tac \\ rw [] \\ fs []
    \\ fs[state_rel_def])
  THEN1 (fs [comp_def,evaluate_def] \\ fs [state_rel_def])
  THEN1 cheat (* easy but good_syntax needs updating *)
  THEN1 (* Get *)
   (`s.use_store` by fs [state_rel_def]
    \\ fs [comp_def,evaluate_def,good_syntax_def]
    \\ every_case_tac \\ fs [] \\ rw []
    \\ fs [evaluate_def,inst_def,assign_def,word_exp_def,LET_DEF]
    THEN1 (`FLOOKUP t1.regs (k + 2) = SOME x` by fs [state_rel_def] \\ fs [])
    \\ qpat_assum `state_rel k s t1` mp_tac
    \\ simp [Once state_rel_def] \\ fs []
    \\ BasicProvers.TOP_CASE_TAC \\ fs []
    \\ BasicProvers.TOP_CASE_TAC \\ fs [] \\ strip_tac
    \\ fs [wordLangTheory.word_op_def]
    \\ `mem_load (c + store_offset name) t1 = SOME x` by
     (Cases_on `name` \\ fs [store_offset_def,store_pos_def,word_offset_def,
        store_list_def,INDEX_FIND_def,word_store_def,GSYM word_mul_n2w,
        word_list_rev_def,bytes_in_word_def] \\ rfs[]
      \\ fs [mem_load_def] \\ SEP_R_TAC \\ fs [] \\ NO_TAC)
    \\ fs [] \\ res_tac \\ fs [] \\ match_mp_tac state_rel_set_var
    \\ fs [state_rel_def] \\ fs [AC MULT_COMM MULT_ASSOC])
  THEN1 (* Set *)
   (`s.use_store` by fs [state_rel_def]
    \\ fs [comp_def,evaluate_def,good_syntax_def]
    \\ every_case_tac \\ fs [] \\ rw []
    \\ fs [evaluate_def,inst_def,assign_def,word_exp_def,LET_DEF,get_var_def]
    THEN1 (fs [state_rel_def,set_var_def,set_store_def,FLOOKUP_UPDATE]
           \\ rfs [] \\ fs [] \\ fs [word_store_def,word_store_CurrHeap]
           \\ rw [] \\ `F` by decide_tac \\ fs [])
    \\ qpat_assum `state_rel k s t1` mp_tac
    \\ simp [Once state_rel_def] \\ fs []
    \\ BasicProvers.TOP_CASE_TAC \\ fs []
    \\ BasicProvers.TOP_CASE_TAC \\ fs [] \\ strip_tac
    \\ fs [wordLangTheory.word_op_def,mem_store_def]
    \\ `c + store_offset name IN t1.mdomain` by
     (Cases_on `name` \\ fs [store_offset_def,store_pos_def,word_offset_def,
        store_list_def,INDEX_FIND_def,word_store_def,GSYM word_mul_n2w,
        word_list_rev_def,bytes_in_word_def] \\ rfs[]
      \\ fs [mem_load_def] \\ SEP_R_TAC \\ fs [] \\ NO_TAC)
    \\ fs [] \\ fs [state_rel_def,set_store_def,FLOOKUP_UPDATE]
    \\ rfs [] \\ fs [AC MULT_COMM MULT_ASSOC]
    \\ Q.ABBREV_TAC `m = t1.memory`
    \\ Q.ABBREV_TAC `d = t1.mdomain`
    \\ Cases_on `name` \\ fs [store_offset_def,store_pos_def,word_offset_def,
         store_list_def,INDEX_FIND_def,word_store_def,GSYM word_mul_n2w,
         word_list_rev_def,bytes_in_word_def,FLOOKUP_UPDATE] \\ rfs[]
    \\ SEP_W_TAC \\ fs[AC STAR_COMM STAR_ASSOC])
  THEN1 (* Tick *)
   (fs [comp_def,evaluate_def]
    \\ `t1.clock = s.clock` by fs [state_rel_def] \\ fs []
    \\ CASE_TAC \\ fs [] \\ rw []
    \\ imp_res_tac state_rel_IMP \\ fs [] \\ fs [state_rel_def])
  THEN1 (* Seq *)
   (fs [] \\ simp [Once comp_def]
    \\ fs [evaluate_def,good_syntax_def,LET_DEF]
    \\ split_pair_tac \\ fs []
    \\ reverse(Cases_on `res = NONE`) \\ fs []
    >- (rpt var_eq_tac
      \\ first_x_assum drule >> simp[]
      \\ strip_tac >> fs[]
      \\ pop_assum mp_tac >> CASE_TAC
      \\ rpt var_eq_tac >> fs[] )
    \\ first_x_assum drule >> simp[] >> strip_tac
    \\ Cases_on `r2` \\ fs [] \\ rw []
    \\ Cases_on`x`>>fs[]>>rw[]>>fs[]
    \\ metis_tac[evaluate_io_events_mono,IS_PREFIX_TRANS])
  THEN1 (* Return *)
   (fs [comp_def,evaluate_def,good_syntax_def]
    \\ imp_res_tac state_rel_get_var \\ fs []
    \\ every_case_tac \\ rw [] \\ fs [])
  THEN1 (* Raise *)
   (fs [comp_def,evaluate_def,good_syntax_def]
    \\ imp_res_tac state_rel_get_var \\ fs []
    \\ every_case_tac \\ rw [] \\ fs [])
  THEN1 (* If *)
   (fs [] \\ simp [Once comp_def]
    \\ fs [evaluate_def,good_syntax_def]
    \\ imp_res_tac state_rel_get_var \\ fs []
    \\ `get_var_imm ri t1 = get_var_imm ri s` by all_tac
    \\ rpt (CASE_TAC \\ fs [])
    \\ Cases_on `ri` \\ fs [get_var_imm_def]
    \\ imp_res_tac state_rel_get_var \\ fs [])
  THEN1 (* JumpLess *)
   (simp [Once comp_def]
    \\ fs [good_syntax_def,evaluate_def]
    \\ imp_res_tac state_rel_get_var \\ fs [find_code_def]
    \\ Cases_on `get_var r1 t1` \\ fs [] \\ Cases_on `x` \\ fs []
    \\ Cases_on `get_var r2 t1` \\ fs [] \\ Cases_on `x` \\ fs []
    \\ reverse (Cases_on `word_cmp Less c c'`) \\ fs [] THEN1 (rw [])
    \\ Cases_on `lookup dest s.code` \\ fs []
    \\ `lookup dest t1.code = SOME (comp k x) /\
        good_syntax x k /\ s.clock = t1.clock` by
     (qpat_assum `bb ==> bbb` (K all_tac)
      \\ fs [state_rel_def,code_rel_def] \\ res_tac \\ fs [] \\ fs [])
    \\ fs [] \\ Cases_on `t1.clock = 0` \\ fs []
    THEN1 (rw [] \\ fs [state_rel_def,code_rel_def])
    \\ first_assum(subterm split_pair_case_tac o concl) \\ fs []
    \\ Cases_on `v'` \\ fs [] \\ rw [] \\ fs []
    \\ `state_rel k (dec_clock s) (dec_clock t1)` by metis_tac [state_rel_IMP]
    \\ res_tac \\ fs [] \\ rw []
    \\ Cases_on `r2'` \\ fs [])
  THEN1 (* Call *)
   (Cases_on `ret` \\ fs [] THEN1
     (fs [evaluate_def]
      \\ Cases_on `find_code dest s.regs s.code` \\ fs []
      \\ Cases_on `handler` \\ fs []
      \\ Cases_on `s.clock = 0` \\ fs [] \\ rw [] THEN1
       (fs [evaluate_def,Once comp_def,good_syntax_def]
        \\ imp_res_tac find_code_lemma \\ fs [] \\ pop_assum (K all_tac)
        \\ fs [state_rel_def,code_rel_def])
      \\ Cases_on `evaluate (x,dec_clock s)` \\ fs []
      \\ Cases_on `q` \\ fs [] \\ rw [] \\ fs []
      \\ simp [evaluate_def,Once comp_def,good_syntax_def]
      \\ fs [good_syntax_def]
      \\ `find_code dest t1.regs t1.code = SOME (comp k x) /\ good_syntax x k` by
           (match_mp_tac find_code_lemma \\ fs []) \\ fs []
      \\ `t1.clock <> 0` by fs [state_rel_def] \\ fs []
      \\ `state_rel k (dec_clock s) (dec_clock t1)` by
       (fs [state_rel_def,dec_clock_def] \\ rfs[] \\ metis_tac [])
      \\ first_x_assum drule \\ fs []
      \\ strip_tac \\ fs []
      \\ BasicProvers.TOP_CASE_TAC \\ fs [])
    \\ PairCases_on `x` \\ fs [good_syntax_def]
    \\ cheat)
  THEN1 (* FFI *)
   (simp [Once comp_def]
    \\ fs [good_syntax_def,evaluate_def]
    \\ imp_res_tac state_rel_get_var \\ fs []
    \\ qpat_assum `xxx = (r,s2)` mp_tac
    \\ rpt (BasicProvers.TOP_CASE_TAC \\ fs [])
    \\ imp_res_tac read_bytearray_IMP_read_bytearray \\ fs []
    \\ pop_assum kall_tac \\ rw [] \\ fs [LET_THM]
    \\ split_pair_tac \\ fs []
    \\ `t1.ffi = s.ffi` by fs [state_rel_def] \\ fs []
    \\ fs [markerTheory.Abbrev_def] \\ rw []
    \\ fs [state_rel_def,FLOOKUP_DRESTRICT]
    \\ rfs [] \\ CASE_TAC \\ fs [] \\ CASE_TAC \\ fs []
    \\ fs [GSYM STAR_ASSOC]
    \\ match_mp_tac write_bytearray_lemma \\ fs []
    \\ imp_res_tac read_bytearray_LENGTH \\ fs []
    \\ imp_res_tac call_FFI_LENGTH \\ fs [])
  THEN1 (* LocValue *)
   (fs [evaluate_def,Once comp_def] \\ rw []
    \\ fs [state_rel_def,set_var_def,FLOOKUP_UPDATE,good_syntax_def]
    \\ `r <> k /\ r <> k+1 /\ r <> k+2` by decide_tac \\ fs []
    \\ rw [] \\ fs [] \\ res_tac \\ fs [] \\ rfs [])
  THEN1 (* StackAlloc *) cheat
  THEN1 (* StackFree *) cheat
  THEN1 (* StackLoad *) cheat
  THEN1 (* StackLoadAny *) cheat
  THEN1 (* StackStore *) cheat
  THEN1 (* StackStoreAny *) cheat
  THEN1 (* StackGetSize *) cheat
  THEN1 (* StackSetSize *) cheat
  THEN1 (* BitmapLoad *)
   (fs [stackSemTheory.evaluate_def] \\ every_case_tac
    \\ fs [good_syntax_def,GSYM NOT_LESS] \\ rw []
    \\ qexists_tac `NONE` \\ fs []
    \\ fs [comp_def,list_Seq_def,stackSemTheory.evaluate_def]
    \\ `?ww. FLOOKUP s.store BitmapBase = SOME (Word ww)` by
     (fs [state_rel_def] \\ Cases_on `FLOOKUP s.store BitmapBase`
      \\ fs [is_SOME_Word_def] \\ Cases_on `x` \\ fs [is_SOME_Word_def])
    \\ `inst (Mem Load r (Addr (k + 1) (store_offset BitmapBase))) t1 =
          SOME (set_var r (Word ww) t1)` by
     (qpat_assum `state_rel k s t1` mp_tac
      \\ simp [Once state_rel_def] \\ fs []
      \\ BasicProvers.TOP_CASE_TAC \\ fs []
      \\ BasicProvers.TOP_CASE_TAC \\ fs [] \\ strip_tac
      \\ fs [wordLangTheory.word_op_def,stackSemTheory.inst_def,
             word_exp_def,LET_THM]
      \\ `mem_load (c' + store_offset BitmapBase) t1 = SOME (Word ww)` by all_tac
      \\ fs [] \\ fs [store_offset_def,store_pos_def,word_offset_def,
          store_list_def,INDEX_FIND_def,word_store_def,GSYM word_mul_n2w,
          word_list_rev_def,bytes_in_word_def] \\ rfs[]
      \\ fs [mem_load_def] \\ SEP_R_TAC \\ fs [] \\ NO_TAC)
    \\ fs [LET_THM,stackSemTheory.inst_def,stackSemTheory.assign_def,
           word_exp_def,set_var_def,FLOOKUP_UPDATE,get_var_def]
    \\ `FLOOKUP t1.regs v = SOME (Word c)` by metis_tac [state_rel_def] \\ fs []
    \\ fs [wordLangTheory.word_op_def,FLOOKUP_UPDATE,wordLangTheory.num_exp_def,
           wordSemTheory.word_sh_def]
    \\ `mem_load (c << word_shift (:'a) + ww << word_shift (:'a)) t1 =
        SOME (Word (EL (w2n c) s.bitmaps))` by
     (fs [state_rel_def] \\ ntac 2 (qpat_assum `xx = SOME yy` kall_tac)
      \\ every_case_tac \\ fs [labPropsTheory.good_dimindex_def,word_shift_def]
      \\ rfs [WORD_MUL_LSL, the_SOME_Word_def]
      \\ imp_res_tac LESS_LENGTH_IMP_APPEND \\ fs [word_list_APPEND]
      \\ rfs [bytes_in_word_def]
      \\ pop_assum (fn th => simp [GSYM th])
      \\ Cases_on `zs` \\ fs []
      \\ fs [rich_listTheory.EL_LENGTH_APPEND,word_list_def]
      \\ fs [mem_load_def]  \\ SEP_R_TAC \\ fs [])
    \\ `good_dimindex(:'a)` by fs [state_rel_def]
    \\ fs [labPropsTheory.good_dimindex_def,word_shift_def,FLOOKUP_UPDATE]
    \\ fs [mem_load_def] \\ fs [GSYM mem_load_def] \\ fs [GSYM set_var_def]));

val compile_semantics = store_thm("compile_semantics",
  ``state_rel k s1 s2 /\ semantics start s1 <> Fail ==>
    semantics start s2 ∈ extend_with_resource_limit { semantics start s1 }``,
  cheat);

(* init code *)

val make_init_store_def = Define `
  (make_init_store w m [] s = s) /\
  (make_init_store w m (n::ns) s =
     make_init_store (w - bytes_in_word) m ns s
       |+ (n,m (w - bytes_in_word)))`

val make_init_opt_def = Define `
  make_init_opt k max s code =
    case evaluate (init_code max k,s) of
    | (NONE,t) =>
       (case (FLOOKUP t.regs (k+1),FLOOKUP t.regs (k+2)) of
        | (SOME (Word w),SOME d) =>
          let store = FEMPTY |+ (CurrHeap,d) in
          let store = make_init_store w t.memory store_list store in
          let last_store = w - word_offset (LENGTH store_list) in
            SOME (t with
                  <| use_stack := T; use_store := T;
                     code := code; store := store;
                     mdomain := s.mdomain INTER { a |a| a <+ last_store } |>)
        | _ => NONE)
    | _ => NONE`

val init_pre_def = Define `
  init_pre k max start s <=>
    lookup 0 s.code = SOME (Seq (init_code max k)
                                (Call NONE (INL start) NONE)) /\
    (* TODO: remove: *) s.ffi.final_event = NONE /\
    ?prog_start heap_start heap_end stack_end anything.
      4n < k /\
      FLOOKUP s.regs 1 = SOME (Word (prog_start)) /\
      FLOOKUP s.regs 2 = SOME (Word (heap_start)) /\
      FLOOKUP s.regs 3 = SOME (Word (heap_end)) /\
      FLOOKUP s.regs 4 = SOME (Word (stack_end)) /\
      word_offset (LENGTH anything) = stack_end - heap_start /\
      (word_list heap_start anything) (fun2set (s.memory,s.mdomain))`

val push_if = prove(
  ``(if b then f x else f y) = f (if b then x else y) /\
    (if b then f x else g x) = (if b then f else g) x``,
  Cases_on `b` \\ fs []);

val evaluate_init_code = store_thm("evaluate_init_code",
  ``init_pre k max start s /\ code_rel k code s.code ==>
    case evaluate (init_code max k,s) of
    | (SOME (Halt (Word w)),t) =>
        w <> 0w /\ t.ffi = s.ffi /\ make_init_opt k max s code = NONE
    | (NONE,t) => ?r. make_init_opt k max s code = SOME r /\
                      state_rel k r t /\ t.ffi = s.ffi
    | _ => F``,
  fs [init_code_def,LET_DEF,halt_inst_def,init_pre_def] \\ rw []
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [evaluate_def,inst_def,assign_def,word_exp_def,LET_THM,set_var_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [evaluate_def,inst_def,assign_def,word_exp_def,LET_THM,set_var_def,
         FLOOKUP_UPDATE,wordLangTheory.word_op_def,get_var_def,get_var_imm_def,
         asmSemTheory.word_cmp_def,push_if]
  \\ cheat);

val evaluate_init_code_clock = prove(
  ``evaluate (init_code max k,s) = (res,t) ==>
    evaluate (init_code max k,s with clock := c) = (res,t with clock := c)``,
  rw [] \\ match_mp_tac evaluate_clock_neutral \\ fs [] \\ EVAL_TAC);

val init_semantics = store_thm("init_semantics",
  ``init_pre k max start s /\ code_rel k code s.code ==>
    case evaluate (init_code max k,s) of
    | (SOME (Halt _),t) =>
        (semantics 0 s = Terminate Resource_limit_hit s.ffi.io_events) /\
        make_init_opt k max s code = NONE
    | (NONE,t) =>
        (semantics 0 s = semantics start t) /\
        ?r. make_init_opt k max s code = SOME r /\ state_rel k r t
    | _ => F``,
  rw [] \\ `s.ffi.final_event = NONE /\
            lookup 0 s.code = SOME (Seq (init_code max k)
              (Call NONE (INL start) NONE))` by fs [init_pre_def]
  \\ imp_res_tac evaluate_init_code
  \\ pop_assum (assume_tac o SPEC_ALL)
  \\ reverse every_case_tac \\ fs [] THEN1
   (fs [semantics_def |> Q.SPEC `0`,LET_DEF,evaluate_def,find_code_def]
    \\ match_mp_tac (METIS_PROVE [] ``~b /\ y = z ==> (if b then x else y) = z``)
    \\ conj_tac THEN1
     (fs [] \\ rw [dec_clock_def]
      \\ imp_res_tac evaluate_init_code_clock \\ fs [])
    \\ DEEP_INTRO_TAC some_intro \\ fs [] \\ rw []
    \\ fs [dec_clock_def]
    \\ imp_res_tac evaluate_init_code_clock \\ fs []
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs [] \\ rfs []
    \\ qexists_tac `1` \\ fs [])
  \\ fs [semantics_def |> Q.SPEC `0`,LET_DEF]
  \\ once_rewrite_tac [evaluate_def] \\ fs [find_code_def]
  \\ once_rewrite_tac [evaluate_def] \\ fs [LET_DEF]
  \\ fs [dec_clock_def]
  \\ imp_res_tac evaluate_init_code_clock \\ fs []
  \\ pop_assum (K all_tac)
  \\ fs [semantics_def,LET_DEF]
  \\ match_mp_tac (METIS_PROVE []
      ``x1 = x2 /\ (x1 /\ x2 ==> y1 = y2) /\ (~x1 /\ ~x2 ==> z1 = z2) ==>
        (if x1 then y1 else z1) = (if x2 then y2 else z2)``)
  \\ conj_tac \\ fs [] THEN1
   (EQ_TAC \\ strip_tac THEN1
     (Cases_on `k' = 0` \\ fs []
      \\ qexists_tac `k'-1` \\ fs []
      \\ every_case_tac \\ fs [])
    \\ qexists_tac `k' + 1` \\ fs []
    \\ every_case_tac \\ fs [])
  \\ strip_tac
  \\ match_mp_tac (METIS_PROVE []
      ``x1 = x2 /\ y1 = y2 /\ z1 = z2 ==> f x1 y1 z1 = f x2 y2 z2``)
  \\ conj_tac \\ fs [] THEN1
   (AP_TERM_TAC \\ fs [FUN_EQ_THM] \\ rw [] \\ reverse EQ_TAC \\ strip_tac
    THEN1 (qexists_tac `k' + 1` \\ fs [])
    \\ qexists_tac `k' - 1` \\ fs []
    \\ Cases_on `k' = 0` \\ fs [] THEN1 (rw [] \\ fs [empty_env_def] \\ rfs[])
    \\ Cases_on `evaluate (Call NONE (INL start) NONE,r with clock := k' - 1)`
    \\ fs [] \\ Cases_on `q` \\ fs [] \\ rw []
    \\ first_x_assum (qspec_then`k'-1`mp_tac) \\ fs [])
  \\ AP_TERM_TAC \\ fs [EXTENSION] \\ rw [] \\ reverse EQ_TAC \\ strip_tac
  THEN1 (fs [] \\ qexists_tac `k' + 1` \\ fs [] \\ every_case_tac \\ fs [])
  \\ fs [] \\ qexists_tac `k' - 1` \\ fs []
  \\ Cases_on `k' = 0` \\ fs []
  THEN1 (fs [evaluate_def,empty_env_def] \\ every_case_tac \\ fs [])
  \\ every_case_tac \\ fs []);

val make_init_opt_SOME_semantics = store_thm("make_init_opt_SOME_semantics",
  ``init_pre k max start s2 /\ code_rel k code s2.code /\
    make_init_opt k max s2 code = SOME s1 /\ semantics start s1 <> Fail ==>
    semantics 0 s2 IN extend_with_resource_limit {semantics start s1}``,
  rw [] \\ imp_res_tac init_semantics \\ pop_assum (assume_tac o SPEC_ALL)
  \\ every_case_tac \\ fs []
  \\ match_mp_tac (GEN_ALL compile_semantics)
  \\ fs [] \\ rw [] \\ metis_tac []);

val make_init_opt_NONE_semantics = store_thm("make_init_opt_NONE_semantics",
  ``init_pre k max start s2 /\ code_rel k code s2.code /\ s2.ffi = s1.ffi /\
    make_init_opt k max s2 code = NONE /\ semantics start s1 <> Fail ==>
    semantics 0 s2 IN extend_with_resource_limit {semantics start s1}``,
  rw [] \\ imp_res_tac init_semantics \\ pop_assum (assume_tac o SPEC_ALL)
  \\ every_case_tac \\ fs [] \\ fs [extend_with_resource_limit_def]
  \\ Cases_on `semantics start s1` \\ fs [] \\ rpt disj2_tac
  \\ imp_res_tac semantics_Terminate_IMP_PREFIX
  \\ imp_res_tac semantics_Diverge_IMP_LPREFIX \\ fs []);

val default_state_def = Define `
  default_state s =
    s with <| store   := FEMPTY
            ; memory  := K (Word 0w)
            ; mdomain := UNIV
            ; regs    := FEMPTY |+ (1,Word 0w) |+ (2,Word 0w)
                                |+ (3,Word 32w) |+ (4,Word 256w) |>`;

val lemma = prove(
  ``(k+1=2<=>k=1n) /\
    (4=k+1<=>k=3n) /\
    (3=k+1<=>k=2n) /\
    (k+2=4<=>k=2n) /\
    (k+2=3<=>k=1) /\
    (1=k+1<=>k=0n)``,
  decide_tac);

val default_state_NOT_NONE = prove(
  ``(* good_dimindex (:'a) /\ ~(MEM k [0;1;2;3;4]) ==> *)
    make_init_opt k max (default_state (s2:('a,'ffi) stackSem$state)) code <> NONE``,
  fs [make_init_opt_def,init_code_def,default_state_def,LET_DEF,
      labPropsTheory.good_dimindex_def] \\ rw [] \\ fs []
  \\ EVAL_TAC \\ fs [dimword_def] \\ EVAL_TAC
  \\ cheat); (* could default_state be changed to make this proof simpler? *)

val make_init_def = Define `
  make_init k max s code =
    case make_init_opt k max s code of
    | SOME t => t
    | NONE => THE (make_init_opt k max (default_state s) code)`

val make_init_opt_SOME_IMP = store_thm("make_init_opt_SOME_IMP",
  ``make_init_opt k max s1 code = SOME s2 ==>
    s2.ffi = s1.ffi /\ s2.code = code /\ s2.use_alloc = s1.use_alloc``,
  cheat);

val make_init_consts = store_thm("make_init_consts[simp]",
  ``(make_init k max s code).ffi = s.ffi /\
    (make_init k max s code).code = code /\
    (make_init k max s code).use_alloc = s.use_alloc``,
  fs [make_init_def] \\ CASE_TAC \\ fs []
  \\ imp_res_tac make_init_opt_SOME_IMP \\ fs []
  \\ `make_init_opt k max (default_state s) code <> NONE` by
       fs [default_state_NOT_NONE]
  \\ Cases_on `make_init_opt k max (default_state s) code` \\ fs []
  \\ imp_res_tac make_init_opt_SOME_IMP \\ fs []
  \\ fs [default_state_def]);

val prog_comp_eta = Q.store_thm("prog_comp_eta",
  `prog_comp = λk (n,p). (n,comp k p)`,
  rw[FUN_EQ_THM,prog_comp_def,FORALL_PROD,LAMBDA_PROD]);

val IMP_code_rel = Q.prove(
  `EVERY (\(n,p). good_syntax p k /\ 3 < n) code1 /\
   code2 = fromAList (compile max_heap_bytes k start code1) ==>
   code_rel k (fromAList code1) code2`,
  fs [code_rel_def,lookup_fromAList] \\ strip_tac \\ rpt var_eq_tac
  \\ fs [ALOOKUP_def,compile_def,init_stubs_def] \\ rw []
  \\ imp_res_tac ALOOKUP_MEM
  \\ imp_res_tac EVERY_MEM \\ fs []
  \\ simp[prog_comp_eta,ALOOKUP_MAP_gen]);

val make_init_semantics = store_thm("make_init_semantics",
  ``init_pre k max start s2 /\
    EVERY (\(n,p). good_syntax p k /\ 3 < n) code /\
    s2.code = fromAList (compile max_heap_bytes k start code) /\
    make_init k max s2 (fromAList code) = s1 /\
    semantics start s1 <> Fail ==>
    semantics 0 s2 IN extend_with_resource_limit {semantics start s1}``,
  fs [make_init_def] \\ reverse CASE_TAC \\ rw []
  \\ imp_res_tac IMP_code_rel
  THEN1 imp_res_tac make_init_opt_SOME_semantics
  \\ match_mp_tac (GEN_ALL make_init_opt_NONE_semantics) \\ fs [] \\ rfs[]
  \\ Cases_on `make_init_opt k max (default_state s2) (fromAList code)`
  \\ fs [default_state_NOT_NONE]
  \\ imp_res_tac make_init_opt_SOME_IMP
  \\ fs [default_state_def] \\ metis_tac []);

val _ = export_theory();
