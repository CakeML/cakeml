(*
  Proves correctness of the max_depth applied to the call graph of a
  wordLang program as produced by the word_depth$call_graph function.
*)
open preamble wordLangTheory wordSemTheory wordPropsTheory word_depthTheory;

val _ = new_theory "word_depthProof";

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
        OPTION_MAP2 MAX (lookup n ss)
       (OPTION_MAP2 MAX (max_depth ss (call_graph funs n all (size all_funs) body))
                        (max_depth_graphs ss ns all funs all_funs))
End

Theorem option_le_SOME_0:
  option_le (SOME 0) x
Proof
  Cases_on `x` \\ fs []
QED

Theorem MEM_max_depth_graphs:
  !ns name y.
    MEM name ns /\ lookup name code = SOME y ==>
    option_le (max_depth_graphs ss [name] xs funs code)
              (max_depth_graphs ss ns xs funs code)
Proof
  Induct \\ fs [] \\ rw []
  \\ fs [max_depth_graphs_def]
  THEN1
   (TOP_CASE_TAC \\ fs []
    \\ Cases_on `lookup h ss` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `max_depth ss (call_graph funs h xs (size code) r)`
    THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `max_depth_graphs ss ns xs funs code`
    \\ fs [OPTION_MAP2_DEF])
  \\ first_x_assum drule \\ fs []
  \\ PairCases_on `y` \\ fs []
  \\ Cases_on `lookup h code` THEN1 fs [OPTION_MAP2_DEF] \\ fs []
  \\ PairCases_on `x` \\ fs []
  \\ Cases_on `lookup h ss` THEN1 fs [OPTION_MAP2_DEF] \\ fs []
  \\ Cases_on `max_depth_graphs ss ns xs funs code`
  THEN1 fs [OPTION_MAP2_DEF] \\ fs []
  \\ Cases_on `max_depth ss (call_graph funs name xs (size code) y1)`
  THEN1 fs [OPTION_MAP2_DEF] \\ fs []
  \\ Cases_on `max_depth ss (call_graph funs h xs (size code) x1)`
  THEN1 fs [OPTION_MAP2_DEF] \\ fs []
  \\ Cases_on `lookup name ss` THEN1 fs [OPTION_MAP2_DEF] \\ fs []
QED

Theorem option_le_max_depth_graph:
  !funs h ns1 t x1 ns2.
    set ns2 ⊆ set ns1 /\ LENGTH ns2 <= LENGTH ns1 ==>
    option_le
      (max_depth ss (call_graph funs h ns1 t x1))
      (max_depth ss (call_graph funs h ns2 t x1))
Proof
  recInduct call_graph_ind \\ rw [] \\ fs [call_graph_def]
  \\ rpt (first_x_assum drule)
  \\ TRY
   (fs [max_depth_mk_Branch,max_depth_def]
    \\ Cases_on `max_depth ss (call_graph funs n ns2 total' p2)`
    THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `max_depth ss (call_graph funs n ns2 total' p1)`
    THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `max_depth ss (call_graph funs n ns total' p2)`
    THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `max_depth ss (call_graph funs n ns total' p1)`
    \\ fs [OPTION_MAP2_DEF] \\ NO_TAC)
  \\ Cases_on `dest` \\ fs [max_depth_def]
  \\ Cases_on `lookup x funs` \\ fs [max_depth_def]
  \\ Cases_on `x'` \\ fs [max_depth_def]
  \\ Cases_on `ret` \\ fs [max_depth_def]
  THEN1
   (Cases_on `MEM x ns2` \\ fs [SUBSET_DEF,max_depth_def]
    \\ Cases_on `MEM x ns` \\ fs [SUBSET_DEF,max_depth_def,option_le_SOME_0]
    \\ IF_CASES_TAC \\ fs [SUBSET_DEF,max_depth_def,option_le_SOME_0]
    \\ fs [max_depth_mk_Branch,max_depth_def]
    \\ Cases_on `lookup x ss` THEN1 fs [OPTION_MAP2_DEF]
    \\ first_x_assum (qspecl_then [`x::ns2`] mp_tac)
    \\ impl_tac THEN1 (rw [] \\ res_tac \\ fs [])
    \\ rename [`option_le x1 x2`]
    \\ Cases_on `x2` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `x1` THEN1 fs [OPTION_MAP2_DEF]
    \\ fs [OPTION_MAP2_DEF])
  \\ PairCases_on `x'` \\ fs []
  \\ IF_CASES_TAC \\ fs [max_depth_def]
  \\ TOP_CASE_TAC
  THEN1
   (fs [max_depth_def,max_depth_mk_Branch]
    \\ first_x_assum (qspec_then `[x]` mp_tac)
    \\ first_x_assum (qspec_then `ns2` mp_tac) \\ fs []
    \\ Cases_on `lookup n ss` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `lookup x ss` THEN1 fs [OPTION_MAP2_DEF]
    \\ rename [`option_le x1 x2`]
    \\ Cases_on `x2` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `x1` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `max_depth ss (call_graph (delete x funs) x [x] total' r)`
    \\ fs [OPTION_MAP2_DEF])
  \\ PairCases_on `x'`
  \\ fs [max_depth_def,max_depth_mk_Branch]
  \\ first_x_assum (qspec_then `ns2` mp_tac)
  \\ first_x_assum (qspec_then `[x]` mp_tac)
  \\ first_x_assum (qspec_then `ns2` mp_tac) \\ fs []
  \\ Cases_on `lookup n ss` THEN1 fs [OPTION_MAP2_DEF]
  \\ Cases_on `lookup x ss` THEN1 fs [OPTION_MAP2_DEF]
  \\ rename [`option_le x1 x2`] \\ strip_tac
  \\ Cases_on `x2` THEN1 fs [OPTION_MAP2_DEF]
  \\ Cases_on `x1` THEN1 fs [OPTION_MAP2_DEF]
  \\ Cases_on `max_depth ss (call_graph funs n ns2 total' x'1)`
  THEN1 fs [OPTION_MAP2_DEF]
  \\ Cases_on `max_depth ss (call_graph funs n ns total' x'1)`
  THEN1 fs [OPTION_MAP2_DEF]
  \\ Cases_on `max_depth ss (call_graph (delete x funs) x [x] total' r)`
  \\ fs [OPTION_MAP2_DEF]
QED

Theorem option_le_max_depth_graphs:
  !ns ns1 ns2.
    set ns2 SUBSET set ns1 /\ LENGTH ns2 <= LENGTH ns1 ==>
    option_le (max_depth_graphs ss ns ns1 funs funs2)
              (max_depth_graphs ss ns ns2 funs funs2)
Proof
  Induct \\ fs [max_depth_graphs_def]
  \\ rpt gen_tac \\ Cases_on `lookup h funs2` \\ fs []
  \\ PairCases_on `x` \\ fs []
  \\ Cases_on `lookup h ss` THEN1 fs [OPTION_MAP2_DEF]
  \\ strip_tac \\ first_x_assum drule
  \\ `option_le
       (max_depth ss (call_graph funs h ns1 (size funs2) x1))
       (max_depth ss (call_graph funs h ns2 (size funs2) x1))`
         by (match_mp_tac option_le_max_depth_graph \\ fs [])
  \\ Cases_on `(max_depth_graphs ss ns ns2 funs funs2)`
  THEN1 fs [OPTION_MAP2_DEF]
  \\ Cases_on `(max_depth_graphs ss ns ns1 funs funs2)`
  THEN1 fs [OPTION_MAP2_DEF]
  \\ Cases_on `max_depth ss (call_graph funs h ns2 (size funs2) x1)`
  THEN1 fs [OPTION_MAP2_DEF]
  \\ Cases_on `max_depth ss (call_graph funs h ns1 (size funs2) x1)`
  \\ fs [OPTION_MAP2_DEF]
QED

Theorem size_fromAList:
  !xs. ALL_DISTINCT (MAP FST xs) ==> size (fromAList xs) = LENGTH xs
Proof
  Induct THEN1 (fs [] \\ EVAL_TAC)
  \\ fs [FORALL_PROD]
  \\ fs [fromAList_def,size_insert,domain_lookup,lookup_fromAList,ADD1] \\ rw []
  \\ imp_res_tac ALOOKUP_MEM \\ fs []
  \\ fs [MEM_MAP,EXISTS_PROD] \\ metis_tac []
QED

Theorem LENGTH_LESS_size:
  !name ns funs y.
    ~MEM name ns /\ set ns ⊆ domain funs /\ ALL_DISTINCT ns /\
    lookup name funs = SOME y ==>
    LENGTH ns < size funs
Proof
  rw []
  \\ `LENGTH ns = size (fromAList (MAP (\n. (n,THE (lookup n funs))) ns))` by
   (qmatch_goalsub_abbrev_tac `LENGTH _ = size (fromAList xs)`
    \\ qsuff_tac `ALL_DISTINCT (MAP FST xs) /\ LENGTH ns = LENGTH xs`
    THEN1 (rw [] \\ match_mp_tac (GSYM size_fromAList) \\ fs [])
    \\ qsuff_tac `MAP FST xs = ns` \\ fs [] \\ fs [Abbr`xs`]
    \\ qid_spec_tac `ns` \\ Induct \\ fs [])
  \\ fs [] \\ match_mp_tac sptreeTheory.IMP_size_LESS_size
  \\ rpt conj_tac THEN1
   (fs [subspt_lookup,lookup_fromAList]
    \\ pop_assum kall_tac
    \\ pop_assum kall_tac
    \\ last_x_assum kall_tac
    \\ Induct_on `ns`
    \\ fs [] \\ rw []
    \\ Cases_on `h = x` \\ fs []
    \\ fs [domain_lookup] \\ rfs [])
  \\ fs [domain_fromAList]
  \\ fs [EXTENSION]
  \\ qexists_tac `name`
  \\ fs [domain_lookup]
  \\ fs [MEM_MAP,FORALL_PROD]
QED

Theorem max_depth_call_graph_lemma:
  !prog s res s1 funs n ns funs2.
    evaluate (prog, s) = (res,s1) /\
    subspt funs funs2 /\ subspt funs2 s.code /\
    s.locals_size = lookup n s.stack_size /\ res <> SOME Error /\
    MEM n ns /\ ALL_DISTINCT ns /\ set ns SUBSET domain funs2 ==>
    option_le s1.stack_max
      (OPTION_MAP2 MAX s.stack_max
        (OPTION_MAP2 (+) (stack_size s.stack)
          (OPTION_MAP2 MAX
            (max_depth_graphs s.stack_size ns ns funs funs2)
            (max_depth s.stack_size (call_graph funs n ns (size funs2) prog))))) /\
    (max_depth_graphs s.stack_size ns ns funs funs2 <> NONE /\
     max_depth s.stack_size (call_graph funs n ns (size funs2) prog) <> NONE ==>
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
    \\ Cases_on `max_depth_graphs s.stack_size ns ns funs funs2`
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
      \\ Cases_on `max_depth_graphs s.stack_size ns ns funs funs2`
      \\ TRY (fs [OPTION_MAP2_DEF] \\ NO_TAC)
      \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size funs2) c1)`
      \\ TRY (fs [OPTION_MAP2_DEF] \\ NO_TAC)
      \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size funs2) c2)`
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
    \\ `set ns SUBSET domain funs2 /\ subspt funs2 s0.code` by
     (imp_res_tac evaluate_code_only_grows
      \\ fs [SUBSET_DEF,domain_lookup,subspt_lookup]
      \\ rw [] \\ res_tac \\ fs [] \\ res_tac \\ fs [])
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size funs2) c1) = NONE`
    THEN1 fs [OPTION_MAP2_DEF] \\ simp []
    \\ Cases_on `s0.stack_size = s.stack_size` \\ fs []
    \\ Cases_on `s0.locals_size = lookup n s.stack_size` \\ fs []
    \\ drule evaluate_NONE_stack_size_const \\ fs []
    \\ Cases_on `s.stack_max`
    THEN1 (fs [OPTION_MAP2_DEF])
    \\ Cases_on `stack_size s.stack`
    THEN1 (fs [OPTION_MAP2_DEF])
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size funs2) c1)`
    THEN1 (fs [OPTION_MAP2_DEF])
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size funs2) c2)`
    THEN1 (fs [OPTION_MAP2_DEF])
    \\ Cases_on `max_depth_graphs s.stack_size ns ns funs funs2`
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
    \\ Cases_on `max_depth_graphs s.stack_size ns ns funs funs2`
    \\ TRY (fs [OPTION_MAP2_DEF] \\ NO_TAC)
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size funs2) c1)`
    \\ TRY (fs [OPTION_MAP2_DEF] \\ NO_TAC)
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size funs2) c2)`
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
  \\ Cases_on `call_graph funs n ns (size funs2)
                  (Call ret dest args handler) = Unknown`
  THEN1 (simp [max_depth_def] \\ simp [OPTION_MAP2_DEF])
  \\ pop_assum mp_tac
  \\ rewrite_tac [call_graph_def]
  \\ TOP_CASE_TAC \\ simp []
  \\ TOP_CASE_TAC \\ simp []
  \\ TOP_CASE_TAC \\ simp []
  \\ rename [`lookup name funs = SOME (a,body)`]
  \\ TOP_CASE_TAC \\ simp []
  THEN1 (* ret = NONE i.e. tail-call *)
   (Cases_on `MEM name ns` \\ fs []
    THEN1
     (simp [evaluate_def,CaseEq"option",CaseEq"bool",pair_case_eq,find_code_def]
      \\ Cases_on `res = SOME Error` \\ asm_rewrite_tac []
      \\ simp_tac std_ss [PULL_EXISTS]
      \\ rpt gen_tac \\ strip_tac \\ rveq \\ fs []
      \\ fs [flush_state_def,option_le_lemma,find_code_def]
      \\ first_x_assum (qspecl_then [`funs`,`name`,`ns`,`funs2`] mp_tac)
      \\ impl_tac THEN1 fs [call_env_def]
      \\ rveq \\ fs []
      \\ fs [subspt_lookup] \\ res_tac \\ fs []
      \\ fs [call_env_def,max_depth_def,OPTION_MAP2_simps] \\ rveq \\ fs []
      \\ fs [OPTION_MAP2_ADD_SOME_0,OPTION_MAP2_DISTRIB]
      \\ fs [subspt_lookup] \\ res_tac \\ fs [] \\ rveq \\ fs []
      \\ `option_le (lookup n s.stack_size)
           (max_depth_graphs s.stack_size ns ns funs funs2)` by
       (match_mp_tac backendPropsTheory.option_le_trans
        \\ qexists_tac `max_depth_graphs s.stack_size [n] ns funs funs2`
        \\ `?y. lookup n funs2 = SOME y` by
               fs [subspt_lookup,SUBSET_DEF,domain_lookup]
        \\ PairCases_on `y` \\ fs []
        \\ reverse conj_tac THEN1 (match_mp_tac MEM_max_depth_graphs \\ fs [])
        \\ fs [max_depth_graphs_def,OPTION_MAP2_MAX_SOME_0,option_le_lemma])
      \\ `option_le
           (OPTION_MAP2 MAX (lookup name s.stack_size)
              (max_depth s.stack_size (call_graph funs name ns (size funs2) body)))
           (max_depth_graphs s.stack_size ns ns funs funs2)` by
       (match_mp_tac backendPropsTheory.option_le_trans
        \\ qexists_tac `max_depth_graphs s.stack_size [name] ns funs funs2`
        \\ reverse conj_tac THEN1 (match_mp_tac MEM_max_depth_graphs \\ fs [])
        \\ fs [max_depth_graphs_def,OPTION_MAP2_MAX_SOME_0])
      \\ qmatch_assum_abbrev_tac `option_le (_ _ x1) x2`
      \\ Cases_on `x2` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `x1` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `lookup name s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `lookup n s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `s.stack_max` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `stack_size s.stack` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `s'.stack_max` THEN1 fs [OPTION_MAP2_DEF]
      \\ fs [])
    \\ Cases_on `set ns ⊆ domain funs2` \\ fs []
    \\ Cases_on `ALL_DISTINCT ns` \\ fs []
    \\ Cases_on `subspt funs funs2` \\ fs []
    \\ `LENGTH ns < size funs2` by
          (match_mp_tac LENGTH_LESS_size \\ asm_exists_tac \\ fs []
           \\ fs [subspt_lookup] \\ pop_assum drule \\ simp [])
    \\ asm_rewrite_tac []
    \\ fs [evaluate_def,CaseEq"option",CaseEq"bool",pair_case_eq,find_code_def]
    \\ Cases_on `res = SOME Error` \\ fs [PULL_EXISTS]
    \\ rpt gen_tac \\ strip_tac \\ rveq \\ fs []
    \\ fs [flush_state_def,option_le_lemma]
    \\ rpt gen_tac \\ strip_tac \\ rveq \\ fs [option_le_lemma]
    \\ first_x_assum (qspecl_then [`funs`,`name`,`name::ns`,`funs2`] mp_tac)
    \\ impl_tac
    THEN1 (fs [subspt_lookup,lookup_delete] \\ rw []
           \\ fs [call_env_def,domain_lookup] \\ res_tac \\ fs [])
    \\ fs [subspt_lookup,lookup_delete] \\ res_tac \\ fs []
    \\ rveq \\ fs []
    \\ fs [max_depth_mk_Branch,max_depth_def,OPTION_MAP2_ADD_SOME_0]
    \\ fs [call_env_def]
    \\ fs [OPTION_MAP2_ADD_SOME_0,OPTION_MAP2_DISTRIB,OPTION_MAP2_MAX_ASSOC]
    \\ rveq \\ simp [AC OPTION_MAP2_MAX_ASSOC OPTION_MAP2_MAX_COMM]
    \\ simp [OPTION_MAP2_simps]
    \\ fs [max_depth_graphs_def,lookup_delete]
    \\ Cases_on `(max_depth s.stack_size
         (call_graph funs name (name::ns) (size funs2) body))`
    THEN1 fs [OPTION_MAP2_DEF] \\ simp []
    \\ fs [subspt_lookup] \\ res_tac \\ fs [] \\ rveq
    \\ `option_le
         (max_depth_graphs s.stack_size ns (name::ns) funs funs2)
         (max_depth_graphs s.stack_size ns ns funs funs2)` by
      (match_mp_tac option_le_max_depth_graphs \\ fs [] \\ rw [])
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
                    (call_graph (delete name funs) name [name] (size funs2) body)`
      THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `max_depth_graphs s.stack_size ns ns funs funs2`
      THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size funs2) x2)`
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
           `name`,`[name]`,`funs2`] mp_tac)
      \\ impl_tac THEN1 (fs [subspt_lookup,lookup_delete]
                         \\ fs [call_env_def,domain_lookup] \\ res_tac \\ fs [])
      \\ fs [max_depth_graphs_def,OPTION_MAP2_MAX_SOME_0,OPTION_MAP2_simps]
      \\ fs [push_env_def] \\ pairarg_tac \\ fs []
      \\ fs [dec_clock_def,call_env_def]
      \\ fs [subspt_lookup] \\ res_tac \\ fs []
      \\ fs [OPTION_MAP2_simps,OPTION_MAP2_ADD_SOME_0]
      \\ fs [stack_size_def,stack_size_frame_def]
      \\ fs [GSYM stack_size_def,max_depth_def,OPTION_MAP2_ADD_SOME_0,
               max_depth_mk_Branch,OPTION_MAP2_DISTRIB]
      \\ fs [subspt_lookup] \\ res_tac \\ fs [] \\ rveq \\ fs []
      \\ Cases_on `lookup name s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `lookup n s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `max_depth s.stack_size (call_graph
                      (delete name funs) name [name] (size funs2) body)`
      THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size funs2) x2)`
      THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `max_depth_graphs s.stack_size ns ns funs funs2`
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
    evaluate (prog, s) = (res,s1) /\ subspt funs s.code /\
    lookup n funs = SOME (a,prog) /\
    s.locals_size = lookup n s.stack_size /\ res <> SOME Error ==>
    option_le s1.stack_max
      (OPTION_MAP2 MAX s.stack_max
        (OPTION_MAP2 (+) (stack_size s.stack)
          (max_depth s.stack_size (full_call_graph n funs))))
Proof
  rw [full_call_graph_def] \\ drule max_depth_call_graph_lemma
  \\ disch_then (qspecl_then [`funs`,`n`,`[n]`,`funs`] mp_tac)
  \\ fs [domain_lookup]
  \\ fs [max_depth_graphs_def,OPTION_MAP2_simps,OPTION_MAP2_MAX_SOME_0]
  \\ fs [subspt_lookup] \\ res_tac \\ fs []
  \\ fs [GSYM OPTION_MAP2_MAX_ASSOC,OPTION_MAP2_simps,max_depth_def,
         OPTION_MAP2_ADD_SOME_0]
QED

Theorem max_depth_Call_SOME:
  evaluate (Call (SOME (n1,n2,Skip,n3,n4)) (SOME dest) args NONE, s) = (res,s1) /\
  res <> SOME Error /\ subspt funs s.code ==>
  option_le s1.stack_max
    (OPTION_MAP2 MAX s.stack_max
      (OPTION_MAP2 (+) s.locals_size
        (OPTION_MAP2 (+) (stack_size s.stack)
          (max_depth s.stack_size (full_call_graph dest funs)))))
Proof
  Cases_on `res = SOME Error` \\ fs []
  \\ Cases_on `lookup dest funs`
  THEN1 (fs [full_call_graph_def,max_depth_def,OPTION_MAP2_DEF])
  \\ PairCases_on `x` \\ fs []
  \\ simp [evaluate_def,CaseEq"option",CaseEq"bool",pair_case_eq,find_code_def,
           PULL_EXISTS] \\ rw [flush_state_def]
  THEN1
   (fs [call_env_def,push_env_def] \\ pairarg_tac \\ fs []
    \\ fs [stack_size_def,stack_size_frame_def]
    \\ fs [GSYM stack_size_def,full_call_graph_def,max_depth_def]
    \\ Cases_on `s.stack_max` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `s.locals_size` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `stack_size s.stack` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `lookup dest s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `(max_depth s.stack_size
                         (call_graph funs dest [dest] (size funs) x1))`
    THEN1 fs [OPTION_MAP2_DEF] \\ fs [OPTION_MAP2_DEF])
  \\ fs [subspt_lookup] \\ res_tac \\ fs [] \\ rveq \\ fs []
  \\ drule max_depth_call_graph
  \\ disch_then (qspecl_then [`funs`,`dest`] mp_tac)
  \\ fs [] \\ impl_tac
  THEN1 (fs [subspt_lookup,call_env_def] \\ CCONTR_TAC \\ fs [])
  \\ fs [dec_clock_def,push_env_def,call_env_def]
  \\ pairarg_tac \\ fs []
  \\ fs [stack_size_def,stack_size_frame_def]
  \\ fs [GSYM stack_size_def,full_call_graph_def,max_depth_def]
  \\ `s2.stack_max = s1.stack_max` by
    (fs [CaseEq"wordSem$result",CaseEq"option",CaseEq"bool",pair_case_eq,
         pop_env_def,CaseEq"list",CaseEq"stack_frame"] \\ rveq \\ fs [])
  \\ fs []
  \\ Cases_on `s.stack_max` THEN1 fs [OPTION_MAP2_DEF]
  \\ Cases_on `s.locals_size` THEN1 fs [OPTION_MAP2_DEF]
  \\ Cases_on `stack_size s.stack` THEN1 fs [OPTION_MAP2_DEF]
  \\ Cases_on `lookup dest s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
  \\ Cases_on `(max_depth s.stack_size
                       (call_graph funs dest [dest] (size funs) exp'))`
  THEN1 fs [OPTION_MAP2_DEF]
  \\ Cases_on `s1.stack_max` \\ fs [OPTION_MAP2_DEF,MAX_DEF]
QED

Theorem max_depth_Call_NONE:
  evaluate (Call NONE (SOME dest) args NONE, s) = (res,s1) /\
  res <> SOME Error /\ subspt funs s.code ==>
  option_le s1.stack_max
    (OPTION_MAP2 MAX s.stack_max
      (OPTION_MAP2 (+) (stack_size s.stack)
        (max_depth s.stack_size (full_call_graph dest funs))))
Proof
  Cases_on `res = SOME Error` \\ fs []
  \\ Cases_on `lookup dest funs`
  THEN1 (fs [full_call_graph_def,max_depth_def,OPTION_MAP2_DEF])
  \\ PairCases_on `x` \\ fs []
  \\ simp [evaluate_def,CaseEq"option",CaseEq"bool",pair_case_eq,find_code_def,
           PULL_EXISTS] \\ rw [flush_state_def]
  THEN1 (fs [call_env_def,stack_size_def,stack_size_frame_def,option_le_lemma])
  \\ fs [subspt_lookup] \\ res_tac \\ fs [] \\ rveq \\ fs []
  \\ drule max_depth_call_graph
  \\ disch_then (qspecl_then [`funs`,`dest`] mp_tac)
  \\ fs [] \\ impl_tac
  THEN1 (fs [subspt_lookup,call_env_def] \\ CCONTR_TAC \\ fs [])
  \\ fs [dec_clock_def,push_env_def,call_env_def]
  \\ fs [stack_size_def,stack_size_frame_def]
  \\ fs [GSYM stack_size_def,full_call_graph_def,max_depth_def]
  \\ Cases_on `s.stack_max` THEN1 fs [OPTION_MAP2_DEF]
  \\ Cases_on `stack_size s.stack` THEN1 fs [OPTION_MAP2_DEF]
  \\ Cases_on `lookup dest s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
  \\ Cases_on `(max_depth s.stack_size
                       (call_graph funs dest [dest] (size funs) exp'))`
  THEN1 fs [OPTION_MAP2_DEF]
  \\ Cases_on `s1.stack_max` \\ fs [OPTION_MAP2_DEF,MAX_DEF]
QED

val _ = export_theory();
