(*
  Computes the call graph for wordLang program with an acyclic call
  graph. This graph is in turn used to compute the max stack depth
  used by the wordLang program.
*)
open preamble wordLangTheory wordSemTheory wordPropsTheory;

val _ = new_theory "word_depthProof";

(* representation of acyclic call graph, i.e. tree *)

Datatype:
  call_tree = Leaf
            | Unknown
            | Call num call_tree
            | Branch call_tree call_tree
End

(* computing the max stack depth *)

Definition max_depth_def:
  max_depth frame_sizes Leaf = SOME 0 /\
  max_depth frame_sizes Unknown = NONE /\
  max_depth frame_sizes (Branch t1 t2) =
    OPTION_MAP2 MAX (max_depth frame_sizes t1) (max_depth frame_sizes t2) /\
  max_depth frame_sizes (Call n t) =
    OPTION_MAP2 (+) (lookup n frame_sizes) (max_depth frame_sizes t)
End

(* computing the call graph *)

Definition mk_Branch_def:
  mk_Branch t1 t2 =
    if t1 = t2 then t1 else
    if t1 = Leaf then t2 else
    if t2 = Leaf then t1 else
    if t1 = Unknown then t1 else
    if t2 = Unknown then t2 else
      Branch t1 t2
End

Definition call_graph_def:
  (call_graph funs n (Seq p1 p2) =
     mk_Branch (call_graph funs n p1) (call_graph funs n p2)) /\
  (call_graph funs n (If _ _ _ p1 p2) =
     mk_Branch (call_graph funs n p1) (call_graph funs n p2)) /\
  (call_graph funs n (Call ret dest args handler) =
     case dest of
     | NONE => Unknown
     | SOME d =>
       case lookup d funs of
       | NONE => Unknown
       | SOME (a:num,body) =>
         case ret of
         | NONE =>
           (if n = d then Call n Leaf else
            if lookup n funs = NONE then Unknown else
              let new_funs = delete n funs in
                mk_Branch (Call d (Leaf))
                  (call_graph new_funs d body))
         | SOME (_,_,ret_prog,_,_) =>
           if lookup n funs = NONE then Unknown else
             let new_funs = delete d funs in
             let t = Branch (Call n (Call d Leaf))
                      (mk_Branch (Call n (call_graph new_funs d body))
                                 (call_graph funs n ret_prog)) in
               case handler of NONE => t
               | SOME (_,p,_,_) => mk_Branch t (call_graph funs n p)) /\
  (call_graph funs n _ = Leaf)
Termination
  WF_REL_TAC `(inv_image (measure I LEX measure I)
              (\(funs,n,p). (size funs, prog_size (K 0) p)))`
  \\ rpt strip_tac \\ fs [size_delete]
  \\ imp_res_tac miscTheory.lookup_zero \\ fs []
End

Triviality option_le_lemma:
  option_le m (OPTION_MAP2 MAX m x)
Proof
  Cases_on `m` \\ Cases_on `x` \\ fs []
QED

Theorem max_depth_mk_Branch:
  !t1 t2. max_depth s (mk_Branch t1 t2) = max_depth s (Branch t1 t2)
Proof
  Cases \\ Cases \\ fs [mk_Branch_def] \\ fs [max_depth_def]
  \\ fs [OPTION_MAP2_DEF] \\ every_case_tac \\ fs []
  \\ fs [IS_SOME_EXISTS] \\ fs [max_depth_def]
QED

Triviality OPTION_MAP2_simps:
  OPTION_MAP2 MAX x x = x
Proof
  Cases_on `x` \\ fs []
QED

Triviality OPTION_MAP2_ADD_SOME_0:
  OPTION_MAP2 (+) x (SOME 0n) = x
Proof
  Cases_on `x` \\ fs []
QED

Triviality OPTION_MAP2_MAX_COMM:
  OPTION_MAP2 MAX x y = OPTION_MAP2 MAX y x
Proof
  Cases_on `x` \\ Cases_on `y` \\ fs [MAX_DEF]
QED

Triviality OPTION_MAP2_MAX_ASSOC:
  OPTION_MAP2 MAX x (OPTION_MAP2 MAX y z) =
  OPTION_MAP2 MAX (OPTION_MAP2 MAX x y) z
Proof
  Cases_on `x` \\ Cases_on `y` \\ Cases_on `z` \\ fs [MAX_DEF]
QED

Triviality OPTION_MAP2_DISTRIB:
  OPTION_MAP2 (+) t (OPTION_MAP2 MAX x y) =
  OPTION_MAP2 MAX (OPTION_MAP2 (+) t x) (OPTION_MAP2 (+) t y)
Proof
  Cases_on `x` \\ Cases_on `y` \\ Cases_on `t` \\ fs [MAX_DEF]
QED

Theorem max_depth_call_graph_lemma:
  !prog s res s1 funs n body funs2 a.
    evaluate (prog, s) = (res,s1) /\ subspt funs s.code /\
    lookup n s.code = SOME (a, body) /\ subspt funs funs2 /\
    s.locals_size = lookup n s.stack_size /\
    res <> SOME Error ==>
    option_le s1.stack_max
      (OPTION_MAP2 MAX s.stack_max
        (OPTION_MAP2 (+) (stack_size s.stack)
          (OPTION_MAP2 MAX
            (max_depth s.stack_size (call_graph funs2 n body))
            (max_depth s.stack_size (call_graph funs n prog)))))
Proof
  recInduct evaluate_ind \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac
  THEN1 (* Skip *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [option_le_lemma])
  THEN1 (* Alloc *) cheat
  THEN1 (* Move *) cheat
  THEN1 (* Inst *) cheat
  THEN1 (* Assign *) cheat
  THEN1 (* Get *) cheat
  THEN1 (* Set *) cheat
  THEN1 (* Store *) cheat
  THEN1 (* Tick *) cheat
  THEN1 (* MustTerminate *) cheat
  THEN1 (* Seq *) cheat
  THEN1 (* Return *) cheat
  THEN1 (* Raise *) cheat
  THEN1 (* If *) cheat
  THEN1 (* LocValue *) cheat
  THEN1 (* Install *) cheat
  THEN1 (* CodeBufferWrite *) cheat
  THEN1 (* DataBufferWrite *) cheat
  THEN1 (* FFI *) cheat
  (* Call *)
  \\ rpt gen_tac
  \\ Cases_on `call_graph funs n (Call ret dest args handler) = Unknown`
  THEN1 (fs [max_depth_def] \\ Cases_on `s.stack_max` \\ fs []
         \\ fs [OPTION_MAP2_DEF] \\ every_case_tac \\ fs [])
  \\ pop_assum mp_tac
  \\ rewrite_tac [call_graph_def]
  \\ TOP_CASE_TAC \\ simp []
  \\ TOP_CASE_TAC \\ simp []
  \\ TOP_CASE_TAC \\ simp []
  \\ rename [`lookup name funs = SOME (a,body)`]
  \\ TOP_CASE_TAC \\ simp []
  THEN1 (* ret = NONE i.e. tail-call *)
   (TOP_CASE_TAC \\ rveq \\ fs []
    \\ fs [evaluate_def,CaseEq"option",CaseEq"bool",pair_case_eq,find_code_def]
    \\ Cases_on `res = SOME Error` \\ fs [PULL_EXISTS]
    \\ rpt strip_tac \\ rveq \\ fs []
    \\ fs [flush_state_def,option_le_lemma]
    THEN1
     (first_x_assum (qspecl_then [`funs`,`n`,`body`,`funs2`] mp_tac)
      \\ rveq \\ fs []
      \\ fs [subspt_lookup] \\ res_tac \\ fs []
      \\ fs [call_env_def,max_depth_def,OPTION_MAP2_simps]
      \\ fs [OPTION_MAP2_ADD_SOME_0,OPTION_MAP2_DISTRIB] \\ cheat)
    \\ first_x_assum (qspecl_then
          [`delete n funs`,`name`,`body`,`delete n funs`,`a`] mp_tac)
    \\ impl_tac THEN1 (fs [subspt_lookup,lookup_delete] \\ rw []
                       \\ fs [call_env_def])
    \\ fs [subspt_lookup,lookup_delete] \\ res_tac \\ fs []
    \\ rveq \\ fs []
    \\ fs [max_depth_mk_Branch,max_depth_def,OPTION_MAP2_ADD_SOME_0]
    \\ fs [call_env_def]
    \\ fs [OPTION_MAP2_ADD_SOME_0,OPTION_MAP2_DISTRIB,OPTION_MAP2_MAX_ASSOC]
    \\ rveq \\ simp [AC OPTION_MAP2_MAX_ASSOC OPTION_MAP2_MAX_COMM]
    \\ simp [OPTION_MAP2_simps]
    \\ Cases_on `s.stack_max` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `stack_size s.stack` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `lookup name s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `max_depth s.stack_size (call_graph (delete n funs) name body)`
    THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `max_depth s.stack_size (call_graph funs2 n body')`
    THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `s1.stack_max`
    THEN1 fs [OPTION_MAP2_DEF]
    \\ fs [OPTION_MAP2_DEF])
  (* non-tail-call case *)
  \\ PairCases_on `x` \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  THEN1 (* handler = NONE *)
   (fs [evaluate_def,CaseEq"option",CaseEq"bool",pair_case_eq,find_code_def]
    \\ Cases_on `res = SOME Error` \\ fs [PULL_EXISTS]
    \\ rpt strip_tac \\ rveq \\ fs []
    \\ fs [flush_state_def,option_le_lemma]
    THEN1
     (fs [call_env_def,push_env_def] \\ pairarg_tac \\ fs []
      \\ fs [stack_size_def,stack_size_frame_def]
      \\ fs [GSYM stack_size_def,max_depth_def,OPTION_MAP2_ADD_SOME_0,
             max_depth_mk_Branch]
      \\ Cases_on `lookup name s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `s.stack_max` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `lookup n s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `stack_size s.stack` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `max_depth s.stack_size (call_graph (delete name funs) name body)`
      THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `max_depth s.stack_size (call_graph funs2 n body')`
      THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `max_depth s.stack_size (call_graph funs n x2)`
      THEN1 fs [OPTION_MAP2_DEF]
      \\ fs [] \\ rw [MAX_DEF])
    \\ rename [`_ = (SOME res,s2)`]
    \\ reverse (Cases_on `?x y. res = Result x y`) \\ fs [] \\ fs []
    THEN1
     (fs [pair_case_eq,CaseEq"bool",CaseEq"option"] \\ rveq \\ fs []
      \\ `s1 = s2 /\ res <> Error` by (Cases_on `res` \\ fs [])
      \\ rveq \\ fs []
      \\ fs [max_depth_def,max_depth_mk_Branch]
      \\ qpat_x_assum `_ = (_,_)` kall_tac
      \\ first_x_assum (qspecl_then [`delete name funs`,
           `name`,`body`,`delete name funs`,`a`] mp_tac)
      \\ impl_tac THEN1 (fs [subspt_lookup,lookup_delete] \\ fs [call_env_def])
      \\ fs [push_env_def] \\ pairarg_tac \\ fs []
      \\ fs [dec_clock_def,call_env_def]
      \\ fs [subspt_lookup] \\ res_tac \\ fs []
      \\ fs [OPTION_MAP2_simps,OPTION_MAP2_ADD_SOME_0]
      \\ fs [stack_size_def,stack_size_frame_def]
      \\ fs [GSYM stack_size_def,max_depth_def,OPTION_MAP2_ADD_SOME_0,
               max_depth_mk_Branch,OPTION_MAP2_DISTRIB]
      \\ Cases_on `lookup name s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `s.stack_max` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `lookup n s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `stack_size s.stack` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `max_depth s.stack_size (call_graph (delete name funs) name exp')`
      THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `max_depth s.stack_size (call_graph funs2 n body')`
      THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `max_depth s.stack_size (call_graph funs n x2)`
      THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `s1.stack_max`
      THEN1 fs [OPTION_MAP2_DEF]
      \\ fs [] \\ rw [MAX_DEF])
    \\ cheat)
  \\ cheat
QED

val _ = export_theory();
