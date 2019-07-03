(*
  Kommentar som beskriver filen ddd
*)

open preamble stackLangTheory stackSemTheory stack_callTheory wordLangTheory;

val _ = new_theory("stack_callProof");

Theorem dest_Call_NONE_INL_SOME[simp]:
  dest_Call_NONE_INL x = SOME m <=> x = (Call NONE (INL m) NONE)
Proof
  cheat
QED;

Theorem dest_StackFree_SOME[simp]:
  dest_StackFree x = SOME m <=> x = StackFree m
Proof
  Cases_on `x`
  \\ fs[dest_StackFree_def]
QED;

Theorem dest_StackFree_NONE[simp]:
  dest_StackFree x = NONE <=> !m. x <> StackFree m
Proof
  Cases_on `x`
  \\ fs[dest_StackFree_def]
QED;

val code_rel_def = Define `
  code_rel s_code t_code tree <=>
    !n x. lookup n s_code = SOME x ==>
          ?m. lookup n tree = SOME m /\
          lookup n t_code = SOME (strip_fun x (n + 1)) /\
          lookup (n + 1) t_code = SOME (opt_code (create_raw_ep x) tree) /\
          ?x2. x = Seq (StackAlloc m) x2
`;

val state_rel_def = Define `
  state_rel s t <=>
    t.clock = s.clock /\
    t.regs = s.regs /\
    t.stack = s.stack /\
    t.stack_space = s.stack_space /\
    t.use_alloc = s.use_alloc /\
    t.bitmaps = s.bitmaps /\
    t.fp_regs = s.fp_regs /\
    t.store = s.store /\
    t.memory = s.memory /\
    t.mdomain = s.mdomain /\
    t.gc_fun = s.gc_fun /\
    t.use_stack = s.use_stack /\
    t.use_store = s.use_store /\
    t.ffi = s.ffi /\
    t.ffi_save_regs = s.ffi_save_regs /\
    t.be = s.be`;

val tree_accurate_def = Define `
  tree_accurate tree (s_code:('a stackLang$prog) num_map) <=>
    T (* TODO: for every entry in tree,
                 there is code in s_code such that get_alloc for that
                 code returns what is stored in the tree (in other words,
                 tree is accurate w.r.t. s_code and get_alloc) *)`;

(*
  <| regs := dfgdg ; clock := 676 |> with clock := 3
=
  <| regs := dfgdg ; clock := 3 |>
*)

Theorem word_loc_case_eq:
  word_loc_CASE x f1 f2 = y <=>
  (?w. x = Word w /\ f1 w = y) \/
  ?l1 l2. x = Loc l1 l2 /\ f2 l1 l2 = y
Proof
  Cases_on `x` \\ fs[]
QED;

val opt_code_Seq = SIMP_CONV(srw_ss())[Once opt_code_def]``opt_code (Seq p1 p2) tree``

Theorem opt_code_correct:
  !prog s res s1 t tree.
    evaluate (prog,s) = (res,s1) /\ state_rel s t /\ code_rel s.code t.code tree /\
    tree_accurate tree s.code /\ res <> SOME Error ==>
    ?ck t1. evaluate (opt_code prog tree,t with clock := t.clock + ck) = (res,t1) /\
            (if res = SOME TimeOut \/ ?r. res = SOME (Halt r)
             then s1.ffi = t1.ffi else state_rel s1 t1) /\
            tree_accurate tree s1.code /\ code_rel s1.code t1.code tree
Proof

  recInduct evaluate_ind \\ rpt strip_tac
  THEN1
   (rename [`Skip`]
    \\ fs [opt_code_def, evaluate_def] \\ rveq
    \\ qexists_tac `0` \\ fs [state_rel_def])
  THEN1
   (rename [`Halt`]
    \\ fs [opt_code_def, evaluate_def]
    \\ rveq \\ fs [get_var_def, state_rel_def]
    \\ TOP_CASE_TAC \\ fs[]
    \\ rveq \\ fs [empty_env_def])
  THEN1
   (rename[`Alloc`]
    \\ fs[opt_code_def, evaluate_def, tree_accurate_def, state_rel_def, get_var_def, alloc_def, gc_def, set_store_def, has_space_def]
    \\ fs[bool_case_eq]
    \\ last_x_assum (assume_tac o SYM)
    \\ fs[option_case_eq]
    \\ fs[bool_case_eq, option_case_eq, word_loc_case_eq, pair_case_eq]
    \\ rveq \\ fs[empty_env_def])
  THEN1
   (rename [`Inst i`]
    \\ fs[evaluate_def, opt_code_def, option_case_eq, inst_def, state_rel_def]
    \\ Cases_on `i` \\ fs[]
       THEN1 (rveq \\ fs[])
       THEN1 (fs[assign_def, option_case_eq, word_exp_def]
         \\ rveq \\ fs[set_var_def])
       THEN1 (fs[option_case_eq]
         \\ Cases_on `a` \\ fs[option_case_eq, bool_case_eq]
         \\ rveq \\ fs[set_var_def, assign_def, word_exp_def, option_case_eq]
         \\ rveq \\ fs[]
           THEN1 (EVERY_CASE_TAC
             \\ fs[IS_SOME_EXISTS, word_exp_def, option_case_eq]
             \\ EVERY_CASE_TAC \\ fs[word_op_def]
             \\ EVERY_CASE_TAC \\ rveq \\ fs[])
           THEN1 (fs[IS_SOME_EXISTS, option_case_eq]
             \\ Cases_on `v1` \\ fs[word_exp_def]
             \\ EVERY_CASE_TAC \\ fs[word_exp_def, option_case_eq]
             \\ rveq \\ fs[]
             \\ EVERY_CASE_TAC \\ fs[word_op_def]
             \\ EVERY_CASE_TAC \\ rveq \\ fs[])
           \\ (EVERY_CASE_TAC
             \\ fs[get_vars_def, get_var_def, option_case_eq]
             \\ rveq \\ fs[]))
       THEN1 (Cases_on `a`
         \\ fs[option_case_eq]
         \\ Cases_on `m`
         \\ fs[option_case_eq, word_exp_def, IS_SOME_EXISTS]
         \\  Cases_on `v1` \\ fs[option_case_eq]
         \\ EVERY_CASE_TAC
         \\ fs[word_op_def, mem_load_def]
         \\ rveq
         \\ fs[set_var_def, get_var_def, mem_store_def]
         \\ rveq \\ fs[])
       THEN1 (Cases_on `f`
         \\ fs[option_case_eq, get_fp_var_def]
         \\ rveq
         \\ fs[set_var_def, set_fp_var_def, bool_case_eq]
         \\ fs[option_case_eq, get_var_def]
         \\ EVERY_CASE_TAC \\ fs[]
         \\ rveq \\ fs[]))
  THEN1
   (rename [`Get v name`]
    \\ fs[evaluate_def, opt_code_def, state_rel_def, tree_accurate_def, bool_case_eq, option_case_eq, set_var_def]
    \\ rveq
    \\ qexists_tac `0` \\ fs[])
  THEN1
   (rename [`Set name v`]
    \\ fs[evaluate_def, opt_code_def, state_rel_def, tree_accurate_def, bool_case_eq, get_var_def, option_case_eq, set_store_def]
    \\ rveq \\ qexists_tac `0` \\ fs[])
  THEN1
   (rename[`Tick`]
    \\ fs[evaluate_def, opt_code_def, state_rel_def, tree_accurate_def, bool_case_eq, empty_env_def, dec_clock_def]
    \\ qexists_tac `0` \\ fs[])
  THEN1
   (rename [`Seq p1 p2`]
    \\ Cases_on `opt_code (Seq p1 p2) tree = Seq (opt_code p1 tree) (opt_code p2 tree)`
    THEN1
     (fs [evaluate_def]
      \\ Cases_on `evaluate (p1,s)` \\ fs []
      \\ rename [`evaluate (p1,s) = (res0,s0)`]
      \\ reverse (Cases_on `res0`)
      THEN1
       (fs [] \\ rveq \\ fs []
        \\ first_x_assum (qspecl_then [`t`,`tree`] mp_tac)
        \\ fs [] \\ strip_tac
        \\ qexists_tac `ck` \\ fs [])
      \\ fs []
      \\ first_x_assum (qspecl_then [`t`,`tree`] mp_tac)
      \\ fs [] \\ strip_tac
      \\ first_x_assum (qspecl_then [`t1`,`tree`] mp_tac)
      \\ fs [] \\ strip_tac
      \\ qexists_tac `ck+ck'`
      \\ qpat_x_assum `_ = (NONE,t1)` assume_tac
      \\ drule (GEN_ALL stackPropsTheory.evaluate_add_clock)
      \\ fs [])
    \\ pop_assum mp_tac
    \\ rewrite_tac[opt_code_Seq]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    THEN1
      (once_rewrite_tac[opt_code_def] \\ fs[])
    \\ disch_then kall_tac
    \\ fs[] \\ rveq
    \\ fs[evaluate_def]
    \\ Cases_on `s.use_stack` \\ fs[]
    \\ Cases_on `LENGTH s.stack < x + s.stack_space` \\ fs[]
    \\ Cases_on `find_code (INL x') s.regs s.code` \\ fs[]
    \\ Cases_on `s.clock = 0` \\ fs[]
    THEN1
     (rveq \\ fs[]
      \\ fs[new_mem_def]
      \\ rw[] \\ fs[evaluate_def, state_rel_def, find_code_def]
      \\ qpat_assum `code_rel _ _ _` mp_tac
      \\ simp_tac std_ss [Once code_rel_def]
      \\ disch_then drule
      \\ strip_tac
      \\ qexists_tac `0` \\ simp [])
    \\ fs [pair_case_eq,option_case_eq] \\ rveq \\ fs []
    \\ qpat_x_assum `!x. _` kall_tac
    \\ fs [new_mem_def]
    \\ Cases_on `x = x''` \\ fs [] \\ rveq
    THEN1 (* case: no alloc/free required *)
     (fs [evaluate_def,find_code_def]
      \\ `t.clock <> 0` by fs [state_rel_def]
      \\ qpat_assum `code_rel s.code t.code tree` (drule o REWRITE_RULE [code_rel_def])
      \\ strip_tac \\ fs [] \\ rveq
      \\ fs [create_raw_ep_def]
      \\ fs [EVAL ``opt_code (Call NONE (INL x') NONE) tree``]
      \\ `state_rel (s with stack_space := m + s.stack_space)
                    (t with stack_space := m + t.stack_space)` by fs [state_rel_def]
      \\ first_x_assum drule \\ fs [] \\ strip_tac
      \\ first_x_assum drule \\ fs []
      \\ simp [evaluate_def,find_code_def,dec_clock_def] \\ rveq
      \\ fs [strip_fun_def]
      \\ rveq \\ fs []
      \\ fs [evaluate_def,dec_clock_def] \\ rveq
      \\ `t.use_stack` by fs [state_rel_def] \\ fs [find_code_def]
      \\ fs [pair_case_eq,option_case_eq,bool_case_eq] \\ rveq \\ fs []
      \\ strip_tac
      \\ rveq \\ fs [] \\ qexists_tac `ck` \\ fs []
      \\ qexists_tac `t1` \\ fs []
      \\ qpat_x_assum `_ = (_,_)` (fn th => rewrite_tac [GSYM th])
      \\ rpt AP_TERM_TAC \\ fs [state_component_equality])
    \\ TOP_CASE_TAC
    THEN1 (* case: free is req *)
     cheat (* similar proof as above *)
    THEN1 (* case: alloc is req *)
     cheat (* similar proof as above *))
  THEN1
   (rename [`Return n m`]
    \\ fs[evaluate_def, opt_code_def, get_var_def, option_case_eq]
    \\ EVERY_CASE_TAC \\ fs[]
    \\ fs[state_rel_def] \\ rveq \\ rfs[])
  THEN1
   (rename [`Raise n`]
    \\ fs[evaluate_def, opt_code_def, option_case_eq, get_var_def]
    \\ EVERY_CASE_TAC THEN1 (fs[])
    \\ fs[state_rel_def] \\ rveq \\ fs[])
  THEN1
   (rename [`If cmp r1 ri c1 c2`]
    \\ once_rewrite_tac [opt_code_def] \\ fs[]
    \\ fs[evaluate_def, get_var_def, option_case_eq, bool_case_eq]
    \\ rveq \\ fs[] \\ rfs[]
    \\ `s.regs = t.regs` by fs[state_rel_def] \\ fs[]
    \\ `get_var_imm ri t = get_var_imm ri s` by (Cases_on `ri`
        \\ fs[state_rel_def, get_var_imm_def, get_var_def])
    \\ fs[]
    \\ qpat_x_assum `(_,_) = _` (assume_tac o GSYM)
    \\ first_x_assum drule
    \\ rpt (disch_then drule)
    \\ strip_tac \\ qexists_tac `ck` \\ fs[])

  THEN1
   (rename [`While cmp r1 ri c1`]
    \\ once_rewrite_tac [opt_code_def]
    \\ reverse (fs[evaluate_def, option_case_eq, word_loc_case_eq,bool_case_eq])
    \\ rveq \\ fs [PULL_EXISTS]
    THEN1 (* case: loop is not entered *)
      cheat
    \\ qpat_x_assum `(_,_) = _` (assume_tac o GSYM)
    \\ pairarg_tac \\ fs []
    \\ fs [bool_case_eq] \\ fs [] \\ rveq \\ fs []
    THEN1 (* case: some exception is raised *)
      cheat
    THEN1 (* case: timeout after one iteration *)
      cheat
    THEN1 (* case: loop continues executing *)
      cheat
(* -- old stuff --
    \\ reverse (Cases_on `word_cmp cmp x y`) \\ fs[]
      THEN1 (rw[PULL_EXISTS]
        \\ `s.regs = t.regs` by fs[state_rel_def] \\ fs[]
        \\ `get_var_imm ri t = get_var_imm ri s` by (Cases_on `ri`
        \\ fs[state_rel_def, get_var_imm_def, get_var_def])
        \\ fs[] \\ fs[get_var_def]
        \\ qexists_tac `0` \\ fs[state_rel_def])
      THEN1 (rw[PULL_EXISTS]
        \\ `s.regs = t.regs` by fs[state_rel_def] \\ fs[]
        \\ `get_var_imm ri t = get_var_imm ri s` by (Cases_on `ri`
        \\ fs[state_rel_def, get_var_imm_def, get_var_def]))
        \\ fs[get_var_def]
        \\ pairarg_tac \\ fs[bool_case_eq]
        \\ rw[] \\ fs[] \\ rfs[]
        THEN1
         (first_x_assum drule
          \\ disch_then drule
          \\ rw[]
          \\ qexists_tac `ck` \\ qexists_tac `t1` \\ fs[])
        THEN1
         (first_x_assum drule
         \\ disch_then drule
         \\ rw[]
         \\ qexists_tac `ck` \\ qexists_tac `empty_env t1` \\ fs[state_rel_def]
         \\ fs[empty_env_def])
       THEN1
         (rfs[]
          \\ qpat_x_assum `(_,_) = _` (assume_tac o GSYM)
          \\ first_x_assum drule
          \\ rpt (disch_then drule)
          \\ rw[]
          \\ `state_rel (dec_clock s1') (dec_clock t1)` by fs [state_rel_def, dec_clock_def]
          \\ first_x_assum drule
          \\ rpt (disch_then drule)
          \\ rw[]
          \\ qexists_tac `ck + ck'` \\ fs[]
          \\ `t1.clock = s1'.clock` by fs [state_rel_def]
          \\ fs[]
          \\ qexists_tac `dec_clock t1'` \\ fs[]
          \\ qpat_x_assum `evaluate (opt_code _ _, _) = (NONE, _)` assume_tac
    \\ drule (GEN_ALL stackPropsTheory.evaluate_add_clock)
          \\ disch_then (qspec_then `ck'` mp_tac) \\ simp[]
          \\ rw[] \\ fs[STOP_def]
          \\ qpat_x_assum `evaluate (opt_code (While _ _ _ _) _, _) = _` mp_tac
          \\ once_rewrite_tac [opt_code_def] \\ fs[]
          \\ cheat) *)
          )

  THEN1
   (rename [`JumpLower r1 r2 dest`]
    \\ once_rewrite_tac [opt_code_def] \\ fs[evaluate_def]
    \\ fs[option_case_eq]
    \\ Cases_on `v6` \\ fs[option_case_eq]
    \\ Cases_on `v14` \\ fs[bool_case_eq, option_case_eq]
    \\ `t.regs = s.regs /\ t.clock = s.clock /\ t.ffi = s.ffi` by fs [state_rel_def]
    \\ fs[get_var_def,find_code_def]
    THEN1
     (fs [code_rel_def] \\ res_tac \\ fs []
      \\ qexists_tac `0` \\ fs [])
    \\ TRY (qexists_tac `0` \\ fs [state_rel_def] \\ NO_TAC)
    \\ qpat_x_assum `(_,_) = _` (assume_tac o GSYM)
    \\ fs [pair_case_eq,option_case_eq] \\ rveq \\ fs []
    \\ `state_rel (dec_clock s) (dec_clock t)` by fs [state_rel_def,dec_clock_def]
    \\ first_x_assum drule
    \\ fs [dec_clock_def]
    \\ disch_then drule \\ fs [] \\ strip_tac \\ fs [PULL_EXISTS]
    \\ cheat)
  THEN1
   (rename [`Call ret dest handler`]
    \\ fs [EVAL ``opt_code (Call _ _ _) tree``]
    \\ cheat)
  THEN1
   (rename [`Install ptr len dptr dlen ret`]
    \\ fs[evaluate_def, opt_code_def]
    \\ fs[option_case_eq]
    \\ Cases_on `v14` \\ fs[option_case_eq]
    \\ Cases_on `v26` \\ fs[option_case_eq]
    \\ Cases_on `v38` \\ fs[option_case_eq]
    \\ Cases_on `v46` \\ fs[]
    \\ fs[get_var_def, state_rel_def]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[option_case_eq]
    \\ Cases_on `v12` \\ fs[]
    \\ Cases_on `v10` \\ fs[]
    \\ Cases_on `progs'` \\ fs[option_case_eq]
    \\ Cases_on `v9` \\ fs[]
    \\ Cases_on `h` \\ fs[bool_case_eq]
    \\ rveq \\ fs[]
    \\ cheat)
  THEN1
   (rename [`CodeBufferWrite r1 r2`]
    \\ fs[evaluate_def, opt_code_def, option_case_eq]
    \\ Cases_on `v5` \\ fs[option_case_eq]
    \\ Cases_on `v13` \\ fs[option_case_eq]
    \\ fs[get_var_def, state_rel_def]
    \\ EVERY_CASE_TAC \\ fs[code_rel_def]
    \\ cheat)
  THEN1
   (rename [`DataBufferWrite r1 r2`]
    \\ fs[evaluate_def, opt_code_def, bool_case_eq, option_case_eq]
    \\ Cases_on `v5` \\ fs[option_case_eq]
    \\ Cases_on `v13` \\ fs[option_case_eq, state_rel_def, get_var_def]
    \\ cheat)
  THEN1
   (rename [`FFI ffi_index ptr len ptr2 len2 ret`]
    \\ fs[evaluate_def, opt_code_def, option_case_eq]
    \\ Cases_on `v7` \\ fs[option_case_eq]
    \\ Cases_on `v19` \\ fs[option_case_eq]
    \\ Cases_on `v31` \\ fs[option_case_eq]
    \\ Cases_on `v39` \\ fs[option_case_eq, get_var_def, state_rel_def]
    \\ EVERY_CASE_TAC \\ fs[]
    \\ rveq \\ fs[])
  THEN1
   (rename [`LocValue r l1 l2`]
    \\ fs[evaluate_def, opt_code_def, bool_case_eq, state_rel_def, set_var_def]
    \\ rveq \\ fs []
    \\ cheat)
  THEN1
   (rename [`StackAlloc n`]
    \\ fs[evaluate_def, opt_code_def, bool_case_eq, state_rel_def, empty_env_def])
  THEN1
   (rename [`StackFree n`]
    \\ fs[evaluate_def, opt_code_def, bool_case_eq, state_rel_def])
  THEN1
   (rename [`StackLoad r n`]
    \\ fs[evaluate_def, opt_code_def, bool_case_eq, state_rel_def, set_var_def])
  THEN1
   (rename [`StackLoadAny r rn`]
    \\ fs[evaluate_def, opt_code_def, bool_case_eq, state_rel_def, get_var_def]
    \\ EVERY_CASE_TAC \\ fs[set_var_def])
  THEN1
   (rename [`StackStore r n`]
    \\ fs[evaluate_def, opt_code_def, bool_case_eq, state_rel_def, get_var_def]
    \\ EVERY_CASE_TAC \\ fs[] \\ fs [])
  THEN1
   (rename [`StackStoreAny r rn`]
    \\ fs[evaluate_def, opt_code_def, bool_case_eq, state_rel_def, get_var_def]
    \\ EVERY_CASE_TAC \\ fs[] \\ fs [])
  THEN1
   (rename [`StackGetSize r`]
    \\ fs[evaluate_def, opt_code_def, bool_case_eq, state_rel_def, set_var_def] \\ fs [])
  THEN1
   (rename [`StackSetSize r`]
    \\ fs[evaluate_def, opt_code_def, bool_case_eq, state_rel_def, get_var_def]
    \\ EVERY_CASE_TAC \\ fs[set_var_def] \\ fs [])
  THEN1
   (rename [`BitmapLoad r v`]
    \\ fs[evaluate_def, opt_code_def, bool_case_eq, state_rel_def, get_var_def]
    \\ EVERY_CASE_TAC \\ fs[set_var_def] \\ fs [])
QED;

val _ = export_theory();
