open preamble
     stack_namesTheory
     stackSemTheory

val _ = new_theory"stack_namesProof";

val rename_state_def = Define `
  rename_state f s =
   s with
   <| regs := MAP_KEYS (find_name f) s.regs
    ; code := fromAList (compile f (toAList s.code))
    |>`

val BIJ_IMP_11 = prove(
  ``BIJ f UNIV UNIV ==> !x y. (f x = f y) = (x = y)``,
  fs [BIJ_DEF,INJ_DEF] \\ metis_tac []);

val get_var_find_name = store_thm("get_var_find_name[simp]",
  ``BIJ (find_name f) UNIV UNIV ==>
    get_var (find_name f v) (rename_state f s) = get_var v s``,
  fs [get_var_def,rename_state_def,FLOOKUP_DEF,MAP_KEYS_def]
  \\ rpt strip_tac \\ imp_res_tac BIJ_IMP_11 \\ fs []
  \\ rw [] \\ fs [] \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ match_mp_tac (MAP_KEYS_def |> SPEC_ALL |> CONJUNCT2 |> MP_CANON)
  \\ fs [INJ_DEF]);

val evaluate_consts = store_thm("evaluate_consts",
  ``!c s r s1.
      evaluate (c,s) = (r,s1) ==>
      s1.use_alloc = s.use_alloc /\
      s1.use_store = s.use_store /\
      s1.use_stack = s.use_stack /\
      s1.code = s.code /\
      s1.be = s.be /\
      s1.gc_fun = s.gc_fun /\
      s1.mdomain = s.mdomain``,
  cheat);

val comp_correct = prove(
  ``!p s r t.
      evaluate (p,s) = (r,t) /\ BIJ (find_name f) UNIV UNIV /\
      ~s.use_alloc /\ ~s.use_store /\ ~s.use_stack ==>
      evaluate (comp f p, rename_state f s) = (r, rename_state f t)``,
  recInduct evaluate_ind \\ rpt strip_tac
  THEN1 (fs [evaluate_def,comp_def] \\ rpt var_eq_tac)
  THEN1 (fs [evaluate_def,comp_def] \\ rpt var_eq_tac \\ CASE_TAC \\ fs [])
  THEN1 (fs [evaluate_def,comp_def,rename_state_def] \\ rpt var_eq_tac \\ fs [])
  THEN1 cheat
  THEN1 cheat
  THEN1 cheat
  THEN1 (fs [evaluate_def,comp_def,rename_state_def] \\ rw []
         \\ fs [] \\ rw [] \\ fs [empty_env_def,dec_clock_def])
  THEN1
   (simp [Once evaluate_def,Once comp_def]
    \\ fs [evaluate_def,LET_DEF] \\ split_pair_tac \\ fs []
    \\ rw [] \\ fs [] \\ rfs [] \\ fs []
    \\ imp_res_tac evaluate_consts \\ fs [])
  THEN1 (fs [evaluate_def,comp_def] \\ rpt var_eq_tac \\ every_case_tac \\ fs [])
  THEN1 (fs [evaluate_def,comp_def] \\ rpt var_eq_tac \\ every_case_tac \\ fs [])
  \\ cheat);

val compile_semantics = store_thm("compile_semantics",
  ``BIJ (find_name f) UNIV UNIV /\
    ~s.use_alloc /\ ~s.use_store /\ ~s.use_stack ==>
    semantics start (rename_state f s) = semantics start s``,
  cheat);

val _ = export_theory();
