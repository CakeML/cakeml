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
  (call_graph funs n ns (Seq p1 p2) =
     mk_Branch (call_graph funs n ns p1) (call_graph funs n ns p2)) /\
  (call_graph funs n ns (If _ _ _ p1 p2) =
     mk_Branch (call_graph funs n ns p1) (call_graph funs n ns p2)) /\
  (call_graph funs n ns (Call ret dest args handler) =
     case dest of
     | NONE => Unknown
     | SOME d =>
       case lookup d funs of
       | NONE => Unknown
       | SOME (a:num,body) =>
         case ret of
         | NONE =>
           (if MEM d ns then Call n Leaf else
            if lookup n funs = NONE then Unknown else
              let new_funs = delete n funs in
                mk_Branch (Call d (Leaf))
                  (call_graph new_funs d (d::ns) body))
         | SOME (_,_,ret_prog,_,_) =>
           if lookup n funs = NONE then Unknown else
             let new_funs = delete d funs in
             let t = Branch (Call n (Call d Leaf))
                      (mk_Branch (Call n (call_graph new_funs d [d] body))
                                 (call_graph funs n ns ret_prog)) in
               case handler of NONE => t
               | SOME (_,p,_,_) => mk_Branch t (call_graph funs n ns p)) /\
  (call_graph funs n ns (MustTerminate p) = call_graph funs n ns p) /\
  (call_graph funs n ns (Alloc _ _) = Call n Leaf) /\
  (call_graph funs n ns (Install _ _ _ _ _) = Unknown) /\
  (call_graph funs n ns _ = Leaf)
Termination
  WF_REL_TAC `(inv_image (measure I LEX measure I)
              (\(funs,n,ns,p). (size funs, prog_size (K 0) p)))`
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

Triviality OPTION_MAP2_MAX_SOME_0:
  OPTION_MAP2 MAX x (SOME 0n) = x
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

Definition max_depth_graphs_def:
  max_depth_graphs ss [] all funs all_funs = SOME 0 /\
  max_depth_graphs ss (n::ns) all funs all_funs =
    case lookup n all_funs of
    | NONE => NONE
    | SOME (a,body) =>
        OPTION_MAP2 MAX (max_depth ss (call_graph funs n all body))
                        (max_depth_graphs ss ns all funs all_funs)
End

Theorem max_depth_graphs_adjust:
  !ns all funs c1 c2 ss.
    subspt c1 c2 /\ set ns ⊆ domain c1 ==>
    max_depth_graphs ss ns all funs c2 =
    max_depth_graphs ss ns all funs c1
Proof
  Induct \\ fs [max_depth_graphs_def]
  \\ rw [] \\ fs [domain_lookup]
  \\ PairCases_on `v` \\ fs []
  \\ fs [subspt_lookup] \\ res_tac \\ fs []
QED

Theorem MEM_max_depth_graphs:
  MEM name ns ==>
  option_le (max_depth_graphs ss [name] xs funs code)
            (max_depth_graphs ss ns xs funs code)
Proof
  cheat
QED

Theorem max_depth_call_graph_lemma:
  !prog s res s1 funs n ns funs2.
    evaluate (prog, s) = (res,s1) /\ subspt funs s.code /\ subspt funs funs2 /\
    s.locals_size = lookup n s.stack_size /\ res <> SOME Error /\
    MEM n ns /\ set ns SUBSET domain s.code ==>
    option_le s1.stack_max
      (OPTION_MAP2 MAX s.stack_max
        (OPTION_MAP2 (+) (stack_size s.stack)
          (OPTION_MAP2 MAX
            (max_depth_graphs s.stack_size ns ns funs2 s.code)
            (max_depth s.stack_size (call_graph funs n ns prog))))) /\
    (max_depth_graphs s.stack_size ns ns funs2 s.code <> NONE /\
     max_depth s.stack_size (call_graph funs n ns prog) <> NONE ==>
     s1.stack_size = s.stack_size /\
     (res = NONE ==> s1.locals_size = s.locals_size))

Proof
  recInduct evaluate_ind \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac
  THEN1 (* Skip *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [option_le_lemma])
  THEN1 (* Alloc *)
   (fs [wordSemTheory.evaluate_def,alloc_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ fs [max_depth_def,call_graph_def]
    \\ rename [`MEM k _`]
    \\ drule gc_const
    \\ fs [push_env_def,flush_state_def] \\ pairarg_tac \\ fs []
    \\ drule pop_env_const
    \\ ntac 2 strip_tac
    \\ (reverse conj_tac THEN1
     (fs [pop_env_def]
      \\ drule gc_s_key_eq \\ fs [set_store_def]
      \\ Cases_on `v2.stack` \\ fs [s_key_eq_def]
      \\ rename [`s_frame_key_eq _ h1`]
      \\ Cases_on `h1` \\ fs [s_frame_key_eq_def]
      \\ rename [`_.stack = StackFrame _ _ opt::_`]
      \\ Cases_on `opt` \\ fs [s_frame_key_eq_def]
      \\ rveq \\ fs []))
    \\ rpt strip_tac
    \\ fs [set_store_def,stack_size_def,stack_size_frame_def]
    \\ fs [GSYM stack_size_def]
    \\ Cases_on `lookup k s.stack_size`
    \\ TRY (fs [OPTION_MAP2_DEF] \\ NO_TAC)
    \\ Cases_on `s.stack_max`
    \\ TRY (fs [OPTION_MAP2_DEF] \\ NO_TAC)
    \\ Cases_on `stack_size s.stack`
    \\ TRY (fs [OPTION_MAP2_DEF] \\ NO_TAC)
    \\ Cases_on `max_depth_graphs s.stack_size ns ns funs2 s.code`
    \\ TRY (fs [OPTION_MAP2_DEF] \\ NO_TAC)
    \\ fs [MAX_DEF])
  THEN1 (* Move *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ fs [option_le_lemma])
  THEN1 (* Inst *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ imp_res_tac inst_const_full \\ fs [option_le_lemma])
  THEN1 (* Assign *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ imp_res_tac assign_const \\ fs [option_le_lemma])
  THEN1 (* Get *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ imp_res_tac assign_const \\ fs [option_le_lemma])
  THEN1 (* Set *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ fs [option_le_lemma])
  THEN1 (* Store *)
   (fs [wordSemTheory.evaluate_def,mem_store_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ fs [option_le_lemma])
  THEN1 (* Tick *)
   (fs [wordSemTheory.evaluate_def,mem_store_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ fs [option_le_lemma,flush_state_def])
  THEN1 (* MustTerminate *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ rw [] \\ fs []
    \\ rpt (pop_assum mp_tac)
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ fs [call_graph_def] \\ metis_tac [])
  THEN1 (* Seq *)
   (rpt gen_tac
    \\ fs [wordSemTheory.evaluate_def] \\ rveq
    \\ pairarg_tac \\ fs []
    \\ reverse IF_CASES_TAC THEN1
     (fs [] \\ rpt strip_tac \\ rveq \\ fs []
      \\ first_x_assum (qspecl_then [`funs`,`n`,`ns`,`funs2`] mp_tac)
      \\ rw [] \\ rveq \\ fs [call_graph_def,max_depth_mk_Branch,max_depth_def]
      \\ Cases_on `s.stack_max`
      \\ TRY (fs [OPTION_MAP2_DEF] \\ NO_TAC)
      \\ Cases_on `stack_size s.stack`
      \\ TRY (fs [OPTION_MAP2_DEF] \\ NO_TAC)
      \\ Cases_on `max_depth_graphs s.stack_size ns ns funs2 s.code`
      \\ TRY (fs [OPTION_MAP2_DEF] \\ NO_TAC)
      \\ Cases_on `max_depth s.stack_size (call_graph funs n ns c1)`
      \\ TRY (fs [OPTION_MAP2_DEF] \\ NO_TAC)
      \\ Cases_on `max_depth s.stack_size (call_graph funs n ns c2)`
      \\ TRY (fs [OPTION_MAP2_DEF] \\ NO_TAC)
      \\ Cases_on `s1.stack_max`
      \\ TRY (fs [OPTION_MAP2_DEF] \\ NO_TAC)
      \\ fs [MAX_DEF])
    \\ strip_tac \\ fs [] \\ rveq \\ fs []
    \\ first_x_assum (qspecl_then [`funs`,`n`,`ns`,`funs2`] mp_tac)
    \\ rename [`evaluate (c1,s) = (NONE,s0)`]
    \\ fs [max_depth_def,call_graph_def,max_depth_mk_Branch]
    \\ imp_res_tac evaluate_code_only_grows
    \\ `subspt funs s0.code` by imp_res_tac subspt_trans
    \\ first_x_assum (qspecl_then [`funs`,`n`,`ns`,`funs2`] mp_tac)
    \\ `set ns SUBSET domain s0.code` by
     (imp_res_tac evaluate_code_only_grows
      \\ fs [SUBSET_DEF,domain_lookup,subspt_lookup]
      \\ rw [] \\ res_tac \\ fs [] \\ res_tac \\ fs [])
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns c1) = NONE`
    THEN1 fs [OPTION_MAP2_DEF] \\ simp []
    \\ Cases_on `s0.stack_size = s.stack_size` \\ fs []
    \\ Cases_on `s0.locals_size = lookup n s.stack_size` \\ fs []
    \\ drule evaluate_NONE_stack_size_const \\ fs []
    \\ `max_depth_graphs s.stack_size ns ns funs2 s0.code =
        max_depth_graphs s.stack_size ns ns funs2 s.code` by
     (match_mp_tac max_depth_graphs_adjust
      \\ imp_res_tac evaluate_code_only_grows \\ fs []) \\ fs []
    \\ Cases_on `s.stack_max`
    THEN1 (fs [OPTION_MAP2_DEF])
    \\ Cases_on `stack_size s.stack`
    THEN1 (fs [OPTION_MAP2_DEF])
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns c1)`
    THEN1 (fs [OPTION_MAP2_DEF])
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns c2)`
    THEN1 (fs [OPTION_MAP2_DEF])
    \\ Cases_on `max_depth_graphs s.stack_size ns ns funs2 s.code`
    THEN1 (fs [OPTION_MAP2_DEF])
    \\ Cases_on `s0.stack_max`
    THEN1 (fs [OPTION_MAP2_DEF])
    \\ Cases_on `s1.stack_max`
    THEN1 (fs [OPTION_MAP2_DEF])
    \\ simp [] \\ rw [MAX_DEF])
  THEN1 (* Return *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq]
    \\ rveq \\ fs [flush_state_def,option_le_lemma])
  THEN1 (* Raise *)
   (fs [wordSemTheory.evaluate_def,jump_exc_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq,CaseEq"list",
           CaseEq"stack_frame",pair_case_eq]
    \\ rveq \\ fs [flush_state_def,option_le_lemma]
    \\ rveq \\ fs [flush_state_def,option_le_lemma])
  THEN1 (* If *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",CaseEq"bool",CaseEq"list",
           CaseEq"stack_frame",pair_case_eq]
    \\ rw [] \\ rveq \\ fs [call_graph_def,max_depth_mk_Branch,max_depth_def]
    \\ first_x_assum (qspecl_then [`funs`,`n`,`ns`,`funs2`] mp_tac)
    \\ Cases_on `s.stack_max`
    \\ TRY (fs [OPTION_MAP2_DEF] \\ NO_TAC)
    \\ Cases_on `stack_size s.stack`
    \\ TRY (fs [OPTION_MAP2_DEF] \\ NO_TAC)
    \\ Cases_on `max_depth_graphs s.stack_size ns ns funs2 s.code`
    \\ TRY (fs [OPTION_MAP2_DEF] \\ NO_TAC)
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns c1)`
    \\ TRY (fs [OPTION_MAP2_DEF] \\ NO_TAC)
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns c2)`
    \\ TRY (fs [OPTION_MAP2_DEF] \\ NO_TAC)
    \\ Cases_on `s1.stack_max`
    \\ TRY (fs [OPTION_MAP2_DEF] \\ NO_TAC)
    \\ fs [MAX_DEF])
  THEN1 (* LocValue *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq]
    \\ rveq \\ fs [flush_state_def,option_le_lemma])
  THEN1 (* Install *)
   (fs [call_graph_def,max_depth_def,OPTION_MAP2_DEF])
  THEN1 (* CodeBufferWrite *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq]
    \\ rveq \\ fs [option_le_lemma])
  THEN1 (* DataBufferWrite *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq]
    \\ rveq \\ fs [option_le_lemma])
  THEN1 (* FFI *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",CaseEq"bool",CaseEq"ffi_result"]
    \\ rveq \\ fs [option_le_lemma,flush_state_def])
  (* Call *)
  \\ rpt gen_tac
  \\ Cases_on `call_graph funs n ns (Call ret dest args handler) = Unknown`
  THEN1 (simp [max_depth_def] \\ simp [OPTION_MAP2_DEF])
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
    \\ rpt gen_tac \\ strip_tac \\ rveq \\ fs []
    \\ fs [flush_state_def,option_le_lemma]
    THEN1
     (first_x_assum (qspecl_then [`funs2`,`name`,`ns`,`funs2`] mp_tac)
      \\ impl_tac THEN1 cheat
      \\ rveq \\ fs []
      \\ fs [subspt_lookup] \\ res_tac \\ fs []
      \\ fs [call_env_def,max_depth_def,OPTION_MAP2_simps] \\ rveq \\ fs []
      \\ fs [OPTION_MAP2_ADD_SOME_0,OPTION_MAP2_DISTRIB]
      \\ `option_le
           (OPTION_MAP2 MAX (lookup name s.stack_size)
              (max_depth s.stack_size (call_graph funs2 name ns body)))
           (max_depth_graphs s.stack_size ns ns funs2 s.code)` by
       (match_mp_tac backendPropsTheory.option_le_trans
        \\ qexists_tac `max_depth_graphs s.stack_size [name] ns funs2 s.code`
        \\ reverse conj_tac THEN1 (match_mp_tac MEM_max_depth_graphs \\ fs [])
        \\ fs [max_depth_graphs_def,OPTION_MAP2_MAX_SOME_0]
        \\ cheat)
      \\ qmatch_assum_abbrev_tac `option_le (_ _ x1) x2`
      \\ Cases_on `x2` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `x1` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `lookup name s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `lookup n s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `s.stack_max` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `stack_size s.stack` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `s1.stack_max` THEN1 fs [OPTION_MAP2_DEF]
      \\ fs [])
    \\ rpt gen_tac \\ strip_tac \\ rveq \\ fs [option_le_lemma]
    \\ first_x_assum (qspecl_then
          [`delete n funs`,`name`,`name::ns`,`delete n funs`] mp_tac)
    \\ impl_tac
    THEN1 (fs [subspt_lookup,lookup_delete] \\ rw []
           \\ fs [call_env_def,domain_lookup])
    \\ fs [subspt_lookup,lookup_delete] \\ res_tac \\ fs []
    \\ rveq \\ fs []
    \\ fs [max_depth_mk_Branch,max_depth_def,OPTION_MAP2_ADD_SOME_0]
    \\ fs [call_env_def]
    \\ fs [OPTION_MAP2_ADD_SOME_0,OPTION_MAP2_DISTRIB,OPTION_MAP2_MAX_ASSOC]
    \\ rveq \\ simp [AC OPTION_MAP2_MAX_ASSOC OPTION_MAP2_MAX_COMM]
    \\ simp [OPTION_MAP2_simps]
    \\ fs [max_depth_graphs_def,lookup_delete]
    \\ Cases_on `(max_depth s.stack_size
         (call_graph (delete n funs) name (name::ns) body))`
    THEN1 fs [OPTION_MAP2_DEF]
    \\ `option_le
         (max_depth_graphs s.stack_size ns (name::ns) (delete n funs) s.code)
         (max_depth_graphs s.stack_size ns ns funs2 s.code)` by cheat
    \\ qmatch_assum_abbrev_tac `option_le x1 x2`
    \\ Cases_on `x2` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `x1` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `lookup name s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `s.stack_max` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `stack_size s.stack` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `s1.stack_max` THEN1 fs [OPTION_MAP2_DEF]
    \\ fs [OPTION_MAP2_DEF,MAX_DEF])
  (* non-tail-call case *)
  \\ PairCases_on `x` \\ simp []
  \\ TOP_CASE_TAC \\ simp []
  \\ TOP_CASE_TAC \\ simp []
  THEN1 (* handler = NONE *)
   (simp [evaluate_def,CaseEq"option",CaseEq"bool",pair_case_eq,find_code_def]
    \\ Cases_on `res = SOME Error` \\ simp [PULL_EXISTS]
    \\ rpt gen_tac \\ strip_tac \\ rveq \\ fs []
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
      \\ Cases_on `max_depth s.stack_size
                    (call_graph (delete name funs) name [name] body)`
      THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `max_depth_graphs s.stack_size ns ns funs2 s.code`
      THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `max_depth s.stack_size (call_graph funs n ns x2)`
      THEN1 fs [OPTION_MAP2_DEF]
      \\ fs [] \\ rw [MAX_DEF])
    \\ rename [`_ = (SOME res,s2)`]
    \\ reverse (Cases_on `?x y. res = Result x y`) \\ fs [] \\ fs []
    THEN1
     (fs [pair_case_eq,CaseEq"bool",CaseEq"option"] \\ rveq \\ fs []
      \\ `s1 = s2 /\ res <> Error` by (Cases_on `res` \\ fs [])
      \\ rveq \\ fs []
      \\ fs [max_depth_def,max_depth_mk_Branch]
      \\ fs [find_code_def]
      \\ first_x_assum (qspecl_then [`delete name funs`,
           `name`,`[name]`,`delete name funs`] mp_tac)
      \\ impl_tac THEN1 (fs [subspt_lookup,lookup_delete]
                         \\ fs [call_env_def,domain_lookup])
      \\ fs [max_depth_graphs_def,OPTION_MAP2_MAX_SOME_0,OPTION_MAP2_simps]
      \\ fs [push_env_def] \\ pairarg_tac \\ fs []
      \\ fs [dec_clock_def,call_env_def]
      \\ fs [subspt_lookup] \\ res_tac \\ fs []
      \\ fs [OPTION_MAP2_simps,OPTION_MAP2_ADD_SOME_0]
      \\ fs [stack_size_def,stack_size_frame_def]
      \\ fs [GSYM stack_size_def,max_depth_def,OPTION_MAP2_ADD_SOME_0,
               max_depth_mk_Branch,OPTION_MAP2_DISTRIB]
      \\ Cases_on `lookup name s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `lookup n s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `max_depth s.stack_size (call_graph
                      (delete name funs) name [name] exp')`
      THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `max_depth s.stack_size (call_graph funs n ns x2)`
      THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `max_depth_graphs s.stack_size ns ns funs2 s.code`
      THEN1 fs [OPTION_MAP2_DEF]
      \\ `res' = NONE ⇒ s1.locals_size = s.locals_size` by
        (strip_tac \\ fs [CaseEq"wordSem$result"]) \\ fs []
      \\ Cases_on `stack_size s.stack` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `s.stack_max` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `s1.stack_max` THEN1 fs [OPTION_MAP2_DEF]
      \\ fs [] \\ rw [MAX_DEF])
    \\ cheat)
  \\ cheat
QED

Theorem max_depth_call_graph:
  !prog s res s1 funs n a.
    lookup n s.code = SOME (a,prog) /\
    evaluate (prog, s) = (res,s1) /\ subspt funs s.code /\
    s.locals_size = lookup n s.stack_size /\ res <> SOME Error ==>
    option_le s1.stack_max
      (OPTION_MAP2 MAX s.stack_max
        (OPTION_MAP2 (+) (stack_size s.stack)
          (max_depth s.stack_size (call_graph funs n [n] prog))))
Proof
  rw [] \\ drule max_depth_call_graph_lemma
  \\ disch_then drule
  \\ disch_then (qspecl_then [`n`,`[n]`,`funs`] mp_tac)
  \\ impl_tac
  \\ fs [max_depth_graphs_def,OPTION_MAP2_simps,OPTION_MAP2_MAX_SOME_0]
  \\ fs [domain_lookup]
QED

val _ = export_theory();
