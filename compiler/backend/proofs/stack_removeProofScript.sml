open preamble
     stack_removeTheory
     stackSemTheory
     set_sepTheory
     semanticsPropsTheory (* TODO: should be in heap? *)

val _ = new_theory"stack_removeProof";

val good_syntax_def = Define `
  (good_syntax (Halt v1) k <=>
     v1 < k) /\
  (good_syntax (Raise v1) k <=>
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
  (good_syntax (Call x1 _ x2) k <=>
     (case x1 of
      | SOME (y,r,_,_) => good_syntax y k /\ r < k
      | NONE => T) /\
     (case x2 of SOME (y,_,_) => good_syntax y k | NONE => T)) /\
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
    (!n prog.
       lookup n s1.code = SOME prog ==>
       good_syntax prog k /\
       lookup n s2.code = SOME (comp k prog)) /\
    FLOOKUP s2.regs (k+2) = FLOOKUP s1.store CurrHeap /\
    {k;k+1;k+2} SUBSET s2.ffi_save_regs /\
    case FLOOKUP s2.regs (k+1) of
    | SOME (Word base) =>
        dimindex (:'a) DIV 8 * max_stack_alloc <= w2n base /\
        FLOOKUP s2.regs k =
          SOME (Word (base + bytes_in_word * n2w s1.stack_space)) /\
        (memory s1.memory s1.mdomain *
         word_store base s1.store *
         word_list base s1.stack)
          (fun2set (s2.memory,s2.mdomain))
    | _ => F`

val state_rel_get_var = prove(
  ``state_rel k s t /\ n < k ==> (get_var n s = get_var n t)``,
  fs [state_rel_def,get_var_def]);

val state_rel_IMP = prove(
  ``state_rel k s t1 ==>
    state_rel k (dec_clock s) (dec_clock t1) /\
    state_rel k (empty_env s) (empty_env t1)``,
  rw [] \\ fs [state_rel_def,dec_clock_def,empty_env_def] \\ rfs [] \\ fs []
  \\ cheat); (* not true for empty_env *)

val comp_correct = Q.prove(
  `!p s1 r s2 t1 k.
     evaluate (p,s1) = (r,s2) /\ r <> SOME Error /\
     state_rel k s1 t1 /\ good_syntax p k ==>
     ?r2 t2. evaluate (comp k p,t1) = (r2,t2) /\
             (case r2 of
               | SOME (Halt _) =>
                   t2.ffi.io_events ≼ s2.ffi.io_events ∧
                   (IS_SOME t2.ffi.final_event ⇒ t2.ffi = s2.ffi)
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
  THEN1 (* Get *) cheat
  THEN1 (* Set *) cheat
  THEN1 (* Tick *)
   (fs [comp_def,evaluate_def]
    \\ `t1.clock = s.clock` by fs [state_rel_def] \\ fs []
    \\ CASE_TAC \\ fs [] \\ rw []
    \\ imp_res_tac state_rel_IMP \\ fs [])
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
      \\ fs [state_rel_def] \\ res_tac \\ fs [] \\ fs [])
    \\ fs [] \\ Cases_on `t1.clock = 0` \\ fs []
    THEN1 (rw [] \\ imp_res_tac state_rel_IMP \\ fs [])
    \\ first_assum(subterm split_pair_case_tac o concl) \\ fs []
    \\ Cases_on `v'` \\ fs [] \\ rw [] \\ fs []
    \\ `state_rel k (dec_clock s) (dec_clock t1)` by metis_tac [state_rel_IMP]
    \\ res_tac \\ fs [] \\ rw []
    \\ Cases_on `r2'` \\ fs [])
  THEN1 (* Call *) cheat
  THEN1 (* FFI *)
   (simp [Once comp_def]
    \\ fs [good_syntax_def,evaluate_def]
    \\ imp_res_tac state_rel_get_var \\ fs []
    \\ Cases_on `get_var ptr t1` \\ fs [] \\ Cases_on `x` \\ fs []
    \\ Cases_on `get_var len t1` \\ fs [] \\ Cases_on `x` \\ fs []
    \\ cheat)
  THEN1 (* StackAlloc *) cheat
  THEN1 (* StackFree *) cheat
  THEN1 (* StackLoad *) cheat
  THEN1 (* StackLoadAny *) cheat
  THEN1 (* StackStore *) cheat
  THEN1 (* StackStoreAny *) cheat
  THEN1 (* StackGetSize *) cheat
  THEN1 (* StackSetSize *) cheat);

val compile_semantics = store_thm("compile_semantics",
  ``state_rel k s1 s2 /\ semantics start s1 <> Fail ==>
    semantics start s2 ∈ extend_with_resource_limit { semantics start s1 }``,
  cheat);

val _ = export_theory();
