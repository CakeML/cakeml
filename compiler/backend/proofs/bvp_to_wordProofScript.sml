open preamble bvlSemTheory bvpSemTheory bvpPropsTheory copying_gcTheory
     int_bitwiseTheory bvp_to_wordPropsTheory finite_mapTheory
     bvp_to_wordTheory;

val _ = new_theory "bvp_to_wordProof";

(* -------------------------------------------------------
    TODO:
     - sketch compiler proof
       - prove Return
       - prove Raise
       - prove Assign Const
   ------------------------------------------------------- *)

(* definition of state relation *)

val isWord_def = Define `
  (isWord (Word w) = T) /\ (isWord _ = F)`;

val theWord_def = Define `
  theWord (Word w) = w`;

val code_rel_def = Define `
  code_rel c s_code t_code <=>
    !n arg_count prog.
      (lookup n s_code = SOME (arg_count:num,prog)) ==>
      ?k. (lookup n t_code = SOME (arg_count,FST (comp c n 1 prog),k))`

val stack_rel_def = Define `
  (stack_rel (Env env) (StackFrame vs NONE) <=>
     !n. IS_SOME (lookup n env) <=>
         IS_SOME (lookup (adjust_var n) (fromAList vs))) /\
  (stack_rel (Exc env n) (StackFrame vs (SOME (x1,x2,x3))) <=>
     stack_rel (Env env) (StackFrame vs NONE) /\ (x1 = n)) /\
  (stack_rel _ _ <=> F)`

val flat_def = Define `
  (flat [] = []) /\
  (flat (Env env::xs) = MAP SND (toAList env) ++ flat xs) /\
  (flat (Exc env n::xs) = MAP SND (toAList env) ++ flat xs)`;

val flat2_def = Define `
  (flat2 (Env env::xs) (StackFrame vs _::ys) =
     MAP (\(n,_). THE (ALOOKUP vs (adjust_var n))) (toAList env) ++ flat2 xs ys) /\
  (flat2 (Exc env _::xs) (StackFrame vs _::ys) =
     MAP (\(n,_). THE (ALOOKUP vs (adjust_var n))) (toAList env) ++ flat2 xs ys) /\
  (flat2 _ _ = [])`;

val state_rel_def = Define `
  state_rel c l1 l2 (s:bvpSem$state) (t:'a wordSem$state) v1 w1 <=>
    (* I/O, clock and handler are the same, GC is fixed, code is compiled *)
    (t.io = s.io) /\
    (t.clock = s.clock) /\
    (t.handler = s.handler) /\
    (t.gc_fun = word_gc_fun c) /\
    code_rel c s.code t.code /\
    (* the store contains everything except Handler *)
    EVERY (\n. n IN FDOM t.store /\ isWord (t.store ' n))
      [NextFree; LastFree; FreeCount; CurrHeap; OtherHeap; AllocSize; ProgStart] /\
    EVERY (\n. n IN FDOM t.store) [Globals] /\
    (* every local is represented in word lang *)
    (v1 = LN ==> lookup 0 t.locals = SOME (Loc l1 l2)) /\
    (!n. IS_SOME (lookup n s.locals) ==>
         IS_SOME (lookup (adjust_var n) t.locals)) /\
    (* the stacks contain the same names, have same shape *)
    EVERY2 stack_rel s.stack t.stack /\
    (* there exists some GC-compatible abstraction *)
    ?heap limit a sp heap_addr_stack.
      (* the abstract heap is stored in memory *)
      (word_heap (theWord (t.store ' CurrHeap)) heap c heap *
       word_heap (theWord (t.store ' OtherHeap))
         [Unused (limit-1)] c [Unused (limit-1)])
           (fun2set (t.memory,t.mdomain)) /\
      (* the abstract heap relates to the values of BVP *)
      abs_ml_inv
        (flat (Env v1 :: Env s.locals :: Env (insert 0 (the (Number 0) (OPTION_MAP RefPtr s.global)) LN) :: s.stack))
        s.refs (heap_addr_stack,heap,F,a,sp) limit /\
      s.space <= sp /\
      (* word lang locals, globals and stack are correct *)
      EVERY2 (\v w. word_addr c heap v = w) heap_addr_stack
        (flat2 (Env v1 :: Env s.locals :: Env (insert 0 (the (Number 0) (OPTION_MAP RefPtr s.global)) LN) :: s.stack)
               (StackFrame (toAList w1) NONE ::
                StackFrame (toAList t.locals) NONE ::
                StackFrame [(adjust_var 0, t.store ' Globals)] NONE ::
                t.stack))`

(* compiler proof *)

val state_rel_get_var_IMP = prove(
  ``state_rel c l1 l2 s t LN LN ==>
    (get_var n s = SOME x) ==>
    ?w. get_var (adjust_var n) t = SOME w``,
  fs [bvpSemTheory.get_var_def,wordSemTheory.get_var_def]
  \\ fs [state_rel_def] \\ rpt strip_tac
  \\ `IS_SOME (lookup n s.locals)` by fs [] \\ res_tac
  \\ Cases_on `lookup (adjust_var n) t.locals` \\ fs []);

val compile_correct = prove(
  ``!(prog:bvp$prog) s c n l l1 l2 res s1 t.
      (bvpSem$evaluate (prog,s) = (res,s1)) /\
      res <> SOME (Rerr (Rabort Rtype_error)) /\
      state_rel c l1 l2 s t LN LN ==>
      ?t1 res1. (wordSem$evaluate (FST (comp c n l prog),t) = (res1,t1)) /\
                (res1 <> SOME NotEnoughSpace ==>
                 case res of
                 | NONE => state_rel c l1 l2 s1 t1 LN LN /\ (res1 = NONE)
                 | SOME (Rval v) =>
                     ?w. state_rel c l1 l2 s1 t1 (insert 0 v LN)
                            (insert (adjust_var 0) w LN) /\
                         (res1 = SOME (Result (Loc l1 l2) w))
                 | SOME (Rerr (Rraise v)) =>
                     ?w. state_rel c l1 l2 s1 t1 (insert 0 v LN)
                            (insert (adjust_var 0) w LN) /\
                         (res1 = SOME (Exception w w))
                 | SOME (Rerr (Rabort e)) => (res1 = SOME TimeOut))``,

  recInduct bvpSemTheory.evaluate_ind \\ rpt strip_tac \\ fs []
  THEN1 (* Skip *)
   (fs [comp_def,bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ rw [])
  THEN1 (* Move *) cheat
  THEN1 (* Assign *) cheat
  THEN1 (* Tick *)
   (fs [comp_def,bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ `t.clock = s.clock` by fs [state_rel_def] \\ fs [] \\ rw []
    \\ fs [] \\ rw [] \\ rpt (pop_assum mp_tac)
    \\ fs [state_rel_def,bvpSemTheory.dec_clock_def,wordSemTheory.dec_clock_def])
  THEN1 (* MakeSpace *) cheat
  THEN1 (* Raise *) cheat

  THEN1 (* Return *)
   (fs [comp_def,bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_var n s` \\ fs [] \\ rw []
    \\ `get_var 0 t = SOME (Loc l1 l2)` by
          fs [state_rel_def,wordSemTheory.get_var_def]
    \\ fs [] \\ imp_res_tac state_rel_get_var_IMP \\ fs []
    \\ fs [state_rel_def,wordSemTheory.call_env_def,lookup_def,
           bvpSemTheory.call_env_def,EVAL ``fromList []``,
           EVAL ``isEmpty (insert 0 x LN)``]
    \\ Q.LIST_EXISTS_TAC [`heap`,`limit`,`a`,`sp`] \\ fs []
    \\ cheat)

  THEN1 (* Seq *)
   (once_rewrite_tac [bvp_to_wordTheory.comp_def] \\ fs []
    \\ Cases_on `comp c n l c1` \\ fs [LET_DEF]
    \\ Cases_on `comp c n r c2` \\ fs [LET_DEF]
    \\ fs [bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `evaluate (c1,s)` \\ fs [LET_DEF]
    \\ `q'' <> SOME (Rerr (Rabort Rtype_error))` by
         (Cases_on `q'' = NONE` \\ fs []) \\ fs []
    \\ qpat_assum `state_rel c l1 l2 s t LN LN` (fn th =>
           first_x_assum (fn th1 => mp_tac (MATCH_MP th1 th)))
    \\ strip_tac \\ pop_assum (mp_tac o Q.SPECL [`n`,`l`])
    \\ rpt strip_tac \\ rfs[]
    \\ reverse (Cases_on `q'' = NONE`) \\ fs []
    THEN1 (rpt strip_tac \\ fs [] \\ rw [] \\ Cases_on `q''` \\ fs []
           \\ Cases_on `x` \\ fs [] \\ Cases_on `e` \\ fs [])
    \\ rw [] THEN1
     (qpat_assum `state_rel c l1 l2 s t LN LN` (fn th =>
             first_x_assum (fn th1 => mp_tac (MATCH_MP th1 th)))
      \\ strip_tac \\ pop_assum (mp_tac o Q.SPECL [`n`,`r`])
      \\ rpt strip_tac \\ rfs [])
    \\ Cases_on `res` \\ fs [])
  THEN1 (* If *) cheat
  THEN1 (* Call *) cheat);

val _ = export_theory();
