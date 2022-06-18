(*
  Proves correctness of the max_depth applied to the call graph of a
  wordLang program as produced by the word_depth$call_graph function.
*)
open preamble wordLangTheory wordSemTheory wordPropsTheory word_depthTheory
     backendPropsTheory;

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = new_theory "word_depthProof";

Triviality option_le_X_MAX_X[simp]:
  option_le x (OPTION_MAP2 MAX m x) /\
  option_le x (OPTION_MAP2 MAX x m)
Proof
  Cases_on `m` \\ Cases_on `x` \\ fs []
QED

Triviality OPTION_MAP2_MAX_IDEMPOT[simp]:
  OPTION_MAP2 MAX x x = x
Proof
  Cases_on `x` \\ fs []
QED

Triviality OPTION_MAP2_SOME_0[simp]:
  OPTION_MAP2 (+) x (SOME 0n) = x /\
  OPTION_MAP2 MAX x (SOME 0n) = x
Proof
  Cases_on `x` \\ fs []
QED

Theorem max_depth_mk_Branch:
  !t1 t2. max_depth s (mk_Branch t1 t2) = max_depth s (Branch t1 t2)
Proof
  Cases \\ Cases \\ fs [mk_Branch_def] \\ fs [max_depth_def]
  \\ fs [OPTION_MAP2_DEF] \\ every_case_tac \\ fs []
  \\ fs [IS_SOME_EXISTS] \\ fs [max_depth_def]
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
  \\ IF_CASES_TAC
  \\ pop_assum mp_tac \\ fs [max_depth_def]
  \\ Cases_on `ret` \\ fs [max_depth_def]
  THEN1
   (strip_tac
    \\ Cases_on `MEM x ns2` \\ fs [SUBSET_DEF,max_depth_def]
    \\ Cases_on `lookup x funs` \\ fs [max_depth_def]
    \\ res_tac \\ fs []
    \\ Cases_on `x'` \\ fs [max_depth_def]
    \\ IF_CASES_TAC \\ fs [SUBSET_DEF,max_depth_def]
    \\ fs [max_depth_mk_Branch,max_depth_def]
    \\ Cases_on `lookup x ss` THEN1 fs [OPTION_MAP2_DEF]
    \\ first_x_assum (qspecl_then [`x::ns2`] mp_tac)
    \\ impl_tac THEN1 (rw [] \\ res_tac \\ fs [])
    \\ rename [`option_le x1 x2`]
    \\ Cases_on `x2` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `x1` THEN1 fs [OPTION_MAP2_DEF]
    \\ fs [OPTION_MAP2_DEF])
  \\ Cases_on `lookup x funs` \\ fs [max_depth_def]
  \\ rename [`_ = SOME z`]
  \\ PairCases_on `z` \\ fs [] \\ rpt strip_tac
  \\ Cases_on `x'` \\ fs [max_depth_def]
  \\ PairCases_on `r` \\ fs [max_depth_def]
  \\ TOP_CASE_TAC
  THEN1
   (fs [max_depth_def,max_depth_mk_Branch]
    \\ last_x_assum (qspec_then `[x]` mp_tac) \\ fs []
    \\ last_x_assum (qspec_then `ns2` mp_tac)
    \\ Cases_on `lookup n ss` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `lookup x ss` THEN1 fs [OPTION_MAP2_DEF]
    \\ rename [`option_le x1 x2`]
    \\ Cases_on `x2` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `x1` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `max_depth ss (call_graph (delete x funs) x [x] total' z1)`
    \\ fs [OPTION_MAP2_DEF])
  \\ TOP_CASE_TAC \\ PairCases_on `r`
  \\ fs [max_depth_def,max_depth_mk_Branch]
  \\ first_x_assum (qspec_then `[x]` mp_tac)
  \\ first_x_assum (qspec_then `ns2` mp_tac)
  \\ first_x_assum (qspec_then `ns2` mp_tac) \\ fs []
  \\ Cases_on `lookup n ss` THEN1 fs [OPTION_MAP2_DEF]
  \\ Cases_on `lookup x ss` THEN1 fs [OPTION_MAP2_DEF]
  \\ rename [`option_le x1 x2`] \\ strip_tac
  \\ Cases_on `x2` THEN1 fs [OPTION_MAP2_DEF]
  \\ Cases_on `x1` THEN1 fs [OPTION_MAP2_DEF]
  \\ Cases_on `max_depth ss (call_graph funs n ns2 total' r1)`
  THEN1 fs [OPTION_MAP2_DEF]
  \\ Cases_on `max_depth ss (call_graph (delete x funs) x [x] total' z1)`
  THEN1 fs [OPTION_MAP2_DEF]
  \\ Cases_on `max_depth ss (call_graph funs n ns total' r1)`
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

Triviality LENGTH_LESS_size:
  !name ns funs y.
    ~MEM name ns /\ set ns ⊆ domain funs /\ ALL_DISTINCT ns /\
    lookup name funs = SOME y ==>
    LENGTH ns < size funs
Proof
  rw []
  \\ `LENGTH ns = size (fromAList (MAP (\n. (n,THE (lookup n funs))) ns))` by
   (qmatch_goalsub_abbrev_tac `LENGTH _ = size (fromAList xs)`
    \\ qsuff_tac `ALL_DISTINCT (MAP FST xs) /\ LENGTH ns = LENGTH xs`
    THEN1 (rw [] \\ match_mp_tac (GSYM miscTheory.size_fromAList) \\ fs [])
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
    \\ fs [])
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
  THEN1 (* StoreConsts *)
   (gvs [wordSemTheory.evaluate_def,AllCaseEqs()])
  THEN1 (* Move *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs [])
  THEN1 (* Inst *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ imp_res_tac inst_const_full \\ fs [])
  THEN1 (* Assign *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ imp_res_tac assign_const \\ fs [])
  THEN1 (* Get *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ imp_res_tac assign_const \\ fs [])
  THEN1 (* Set *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ fs [])
  THEN1 (* OpCurrHeap *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ fs [])
  THEN1 (* Store *)
   (fs [wordSemTheory.evaluate_def,mem_store_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ fs [])
  THEN1 (* Tick *)
   (fs [wordSemTheory.evaluate_def,mem_store_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ fs [flush_state_def])
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
    \\ rveq \\ fs [flush_state_def,option_le_X_MAX_X])
  THEN1 (* Raise *)
   (fs [wordSemTheory.evaluate_def,jump_exc_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq,CaseEq"list",
           CaseEq"stack_frame",pair_case_eq]
    \\ rveq \\ fs [flush_state_def,option_le_X_MAX_X]
    \\ rveq \\ fs [flush_state_def,option_le_X_MAX_X])
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
    \\ rveq \\ fs [flush_state_def,option_le_X_MAX_X])
  THEN1 (* Install *)
   (fs [call_graph_def,max_depth_def,OPTION_MAP2_DEF])
  THEN1 (* CodeBufferWrite *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq]
    \\ rveq \\ fs [])
  THEN1 (* DataBufferWrite *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq]
    \\ rveq \\ fs [])
  THEN1 (* FFI *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",CaseEq"bool",CaseEq"ffi_result"]
    \\ rveq \\ fs [flush_state_def])
  (* Call *)
  \\ rpt gen_tac
  \\ Cases_on `call_graph funs n ns (size funs2)
                  (Call ret dest args handler) = Unknown`
  THEN1 (simp [max_depth_def] \\ simp [OPTION_MAP2_DEF])
  \\ pop_assum mp_tac
  \\ rewrite_tac [call_graph_def]
  \\ TOP_CASE_TAC \\ simp []
  \\ IF_CASES_TAC THEN1
     (fs [] \\ rename [`MEM name ns`] \\ rveq
      \\ simp [evaluate_def,CaseEq"option",CaseEq"bool",pair_case_eq,find_code_def]
      \\ Cases_on `res = SOME Error` \\ asm_rewrite_tac []
      \\ simp_tac std_ss [PULL_EXISTS]
      \\ rpt gen_tac \\ strip_tac \\ rveq \\ fs []
      \\ fs [flush_state_def,find_code_def]
      \\ first_x_assum (qspecl_then [`funs`,`name`,`ns`,`funs2`] mp_tac)
      \\ impl_tac THEN1 fs [call_env_def]
      \\ rveq \\ fs []
      \\ fs [subspt_lookup] \\ res_tac \\ fs []
      \\ fs [call_env_def,max_depth_def] \\ rveq \\ fs []
      \\ fs [backendPropsTheory.option_map2_max_add]
      \\ fs [subspt_lookup] \\ res_tac \\ fs [] \\ rveq \\ fs []
      \\ `option_le (lookup n s.stack_size)
           (max_depth_graphs s.stack_size ns ns funs funs2)` by
       (match_mp_tac backendPropsTheory.option_le_trans
        \\ qexists_tac `max_depth_graphs s.stack_size [n] ns funs funs2`
        \\ `?y. lookup n funs2 = SOME y` by
               fs [subspt_lookup,SUBSET_DEF,domain_lookup]
        \\ PairCases_on `y` \\ fs []
        \\ reverse conj_tac THEN1 (match_mp_tac MEM_max_depth_graphs \\ fs [])
        \\ fs [max_depth_graphs_def,option_le_X_MAX_X])
      \\ `?a body. lookup name funs2 = SOME (a, body)` by
       (fs [SUBSET_DEF,domain_lookup] \\ rw [] \\ res_tac \\ fs []
        \\ rename [`_ = SOME vv`] \\ PairCases_on `vv` \\ fs [])
      \\ fs [subspt_lookup] \\ res_tac \\ fs [] \\ rveq \\ fs []
      \\ `option_le
           (OPTION_MAP2 MAX (lookup name s.stack_size)
              (max_depth s.stack_size (call_graph funs name ns (size funs2) body)))
           (max_depth_graphs s.stack_size ns ns funs funs2)` by
       (match_mp_tac backendPropsTheory.option_le_trans
        \\ qexists_tac `max_depth_graphs s.stack_size [name] ns funs funs2`
        \\ reverse conj_tac THEN1 (match_mp_tac MEM_max_depth_graphs \\ fs [])
        \\ fs [max_depth_graphs_def])
      \\ qmatch_assum_abbrev_tac `option_le (_ _ x1) x2`
      \\ Cases_on `x2` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `x1` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `lookup name s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `lookup n s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `s.stack_max` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `stack_size s.stack` THEN1 fs [OPTION_MAP2_DEF]
      \\ Cases_on `s'.stack_max` THEN1 fs [OPTION_MAP2_DEF]
      \\ fs [])
  \\ TOP_CASE_TAC \\ simp []
  \\ TOP_CASE_TAC \\ simp []
  \\ rename [`lookup name funs = SOME (a,body)`]
  \\ qpat_x_assum `~_:bool` mp_tac
  \\ TOP_CASE_TAC \\ simp []
  THEN1 (* ret = NONE i.e. tail-call *)
   (strip_tac
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
    \\ fs [flush_state_def,option_le_X_MAX_X]
    \\ rpt gen_tac \\ strip_tac \\ rveq \\ fs []
    \\ first_x_assum (qspecl_then [`funs`,`name`,`name::ns`,`funs2`] mp_tac)
    \\ impl_tac
    THEN1 (fs [subspt_lookup,lookup_delete] \\ rw []
           \\ fs [call_env_def,domain_lookup] \\ res_tac \\ fs [])
    \\ fs [subspt_lookup,lookup_delete] \\ res_tac \\ fs []
    \\ rveq \\ fs []
    \\ fs [max_depth_mk_Branch,max_depth_def]
    \\ fs [call_env_def]
    \\ fs [backendPropsTheory.option_map2_max_add,OPTION_MAP2_MAX_ASSOC]
    \\ rveq \\ simp [AC OPTION_MAP2_MAX_ASSOC OPTION_MAP2_MAX_COMM]
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
  THEN1 (* handler = NONE *)
   (simp [evaluate_def,CaseEq"option",CaseEq"bool",pair_case_eq,find_code_def]
    \\ Cases_on `res = SOME Error` \\ simp [PULL_EXISTS]
    \\ rpt gen_tac \\ strip_tac \\ rveq \\ fs []
    \\ fs [flush_state_def,option_le_X_MAX_X]
    THEN1
     (fs [call_env_def,push_env_def] \\ pairarg_tac \\ fs []
      \\ fs [stack_size_def,stack_size_frame_def]
      \\ fs [GSYM stack_size_def,max_depth_def,
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
      \\ fs [max_depth_graphs_def]
      \\ fs [push_env_def] \\ pairarg_tac \\ fs []
      \\ fs [dec_clock_def,call_env_def]
      \\ fs [subspt_lookup] \\ res_tac \\ fs []
      \\ fs [stack_size_def,stack_size_frame_def]
      \\ fs [GSYM stack_size_def,max_depth_def,
               max_depth_mk_Branch,backendPropsTheory.option_map2_max_add]
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
    \\ rveq \\ fs [CaseEq"bool",CaseEq"option"] \\ rveq \\ fs [find_code_def]
    \\ rename [`evaluate (_,set_var _ y s2) = (res3,s3)`]
    \\ last_x_assum (qspecl_then [`delete name funs`,
         `name`,`[name]`,`funs2`] mp_tac)
    \\ impl_tac THEN1 (fs [subspt_lookup,lookup_delete,call_env_def]
                       \\ fs [domain_lookup] \\ metis_tac [])
    \\ `lookup name funs2 = SOME (a,body) /\
        lookup name s.code = SOME (a,body)`
          by (fs [subspt_lookup,lookup_delete,call_env_def]
                       \\ fs [domain_lookup] \\ metis_tac [])
    \\ fs [max_depth_graphs_def]
    \\ simp [call_env_def,dec_clock_def]
    \\ rename [`pop_env s1 = SOME s2`]
    \\ `s1.stack_max = s2.stack_max` by (imp_res_tac pop_env_const \\ fs [])
    \\ fs [max_depth_def,max_depth_mk_Branch,backendPropsTheory.option_map2_max_add]
    \\ fs [] \\ rveq \\ fs []
    \\ Cases_on `lookup name s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `max_depth s.stack_size
            (call_graph (delete name funs) name [name] (size funs2) body)`
    THEN1 fs [OPTION_MAP2_DEF] \\ fs []
    \\ Cases_on `s1.stack_size = s.stack_size` \\ fs []
    \\ last_x_assum (qspecl_then [`funs`,`n`,`ns`,`funs2`] mp_tac)
    \\ `stack_size s2.stack = stack_size s.stack /\
        s2.locals_size = s.locals_size` by
     (qmatch_assum_abbrev_tac `evaluate (body,s8) = _`
      \\ qspecl_then [`body`,`s8`] mp_tac evaluate_stack_swap
      \\ fs [] \\ strip_tac \\ pop_assum kall_tac
      \\ fs [Abbr`s8`,call_env_def] \\ ntac 2 (pop_assum mp_tac)
      \\ fs [push_env_def] \\ pairarg_tac \\ fs []
      \\ Cases_on `s1.stack` \\ fs [s_key_eq_def]
      \\ Cases_on `h` \\ fs [s_key_eq_def]
      \\ Cases_on `o0` \\ fs [s_key_eq_def,s_frame_key_eq_def]
      \\ fs [pop_env_def] \\ rveq \\ fs []
      \\ rw [] \\ imp_res_tac s_key_eq_stack_size \\ fs [])
    \\ impl_tac THEN1
       (imp_res_tac evaluate_code_only_grows \\ fs [call_env_def]
        \\ imp_res_tac subspt_trans \\ imp_res_tac pop_env_const \\ fs []
        \\ fs [set_var_def]) \\ fs []
    \\ `s2.stack_size = s1.stack_size` by (imp_res_tac pop_env_const \\ fs [])
    \\ fs []
    \\ Cases_on `max_depth_graphs s.stack_size ns ns funs funs2`
    THEN1 fs [OPTION_MAP2_DEF] \\ fs []
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size funs2) x2)`
    THEN1 fs [OPTION_MAP2_DEF] \\ fs []
    \\ rpt strip_tac
    \\ match_mp_tac backendPropsTheory.option_le_trans
    \\ goal_assum (first_x_assum o mp_then Any mp_tac)
    \\ pop_assum mp_tac
    \\ fs [push_env_def] \\ pairarg_tac \\ fs []
    \\ fs [stack_size_def,stack_size_frame_def]
    \\ fs [GSYM stack_size_def]
    \\ Cases_on `lookup n s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `stack_size s.stack` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `s.stack_max` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `s2.stack_max` THEN1 fs [OPTION_MAP2_DEF]
    \\ fs [OPTION_MAP2_DEF] \\ fs [] \\ rw [MAX_DEF])
  \\ rename [`Call _ _ _ (SOME h)`]
  \\ PairCases_on `h`
  \\ simp_tac (srw_ss()) [evaluate_def,CaseEq"option",CaseEq"bool",pair_case_eq,find_code_def]
  \\ Cases_on `res = SOME Error` \\ pop_assum mp_tac \\ simp_tac std_ss []
  \\ simp_tac std_ss [PULL_EXISTS] \\ asm_rewrite_tac []
  \\ rpt (disch_then assume_tac) \\ rpt gen_tac \\ strip_tac \\ rveq
  THEN1
   (fs [flush_state_def,option_le_X_MAX_X]
    \\ fs [call_env_def,push_env_def] \\ pairarg_tac \\ fs []
    \\ fs [stack_size_def,stack_size_frame_def]
    \\ fs [GSYM stack_size_def,max_depth_def,
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
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size funs2) h1)`
    THEN1 fs [OPTION_MAP2_DEF]
    \\ fs [] \\ rw [MAX_DEF])
  \\ rename [`_ = (SOME res,s2)`]
  \\ reverse (Cases_on `?x y. res = Result x y \/ res = Exception x y`)
  \\ pop_assum mp_tac \\ simp_tac std_ss []
  THEN1
   (strip_tac \\ fs []
    \\ `s1 = s2 /\ res <> Error` by
     (rpt (qpat_x_assum `!x y z. _` kall_tac)
      \\ fs [CaseEq"bool",CaseEq"option",CaseEq"wordSem$result"] \\ rfs [])
    \\ qpat_x_assum `!x y z. _` kall_tac
    \\ qpat_x_assum `!x y z. _` kall_tac
    \\ rveq \\ fs []
    \\ fs [max_depth_def,max_depth_mk_Branch]
    \\ fs [find_code_def]
    \\ first_x_assum (qspecl_then [`delete name funs`,
         `name`,`[name]`,`funs2`] mp_tac)
    \\ impl_tac THEN1 (fs [subspt_lookup,lookup_delete]
                       \\ fs [call_env_def,domain_lookup] \\ res_tac \\ fs [])
    \\ fs [max_depth_graphs_def]
    \\ fs [push_env_def] \\ pairarg_tac \\ fs []
    \\ fs [dec_clock_def,call_env_def]
    \\ fs [subspt_lookup] \\ res_tac \\ fs []
    \\ fs [stack_size_def,stack_size_frame_def]
    \\ fs [GSYM stack_size_def,max_depth_def,
             max_depth_mk_Branch,backendPropsTheory.option_map2_max_add]
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
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size funs2) h1)`
    THEN1 fs [OPTION_MAP2_DEF]
    \\ fs [] \\ rw [MAX_DEF])
  \\ strip_tac
  THEN1
   (qpat_x_assum `_ = (_,_)` mp_tac \\ asm_rewrite_tac []
    \\ simp_tac (srw_ss()) [CaseEq"bool",CaseEq"option"]
    \\ asm_simp_tac std_ss [] \\ strip_tac
    \\ rveq \\ fs [find_code_def]
    \\ rename [`evaluate (_,set_var _ y s2) = (res3,s3)`]
    \\ last_x_assum (qspecl_then [`delete name funs`,
         `name`,`[name]`,`funs2`] mp_tac)
    \\ impl_tac THEN1 (fs [subspt_lookup,lookup_delete,call_env_def]
                       \\ fs [domain_lookup] \\ metis_tac [])
    \\ `lookup name funs2 = SOME (a,body) /\
        lookup name s.code = SOME (a,body)`
          by (fs [subspt_lookup,lookup_delete,call_env_def]
                       \\ fs [domain_lookup] \\ metis_tac [])
    \\ fs [max_depth_graphs_def]
    \\ simp [call_env_def,dec_clock_def]
    \\ rename [`pop_env s1 = SOME s2`]
    \\ `s1.stack_max = s2.stack_max` by (imp_res_tac pop_env_const \\ fs [])
    \\ fs [max_depth_def,max_depth_mk_Branch,backendPropsTheory.option_map2_max_add]
    \\ fs [] \\ rveq \\ fs []
    \\ Cases_on `lookup name s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `max_depth s.stack_size
            (call_graph (delete name funs) name [name] (size funs2) body)`
    THEN1 fs [OPTION_MAP2_DEF] \\ fs []
    \\ Cases_on `s1.stack_size = s.stack_size` \\ fs []
    \\ last_x_assum (qspecl_then [`funs`,`n`,`ns`,`funs2`] mp_tac)
    \\ `stack_size s2.stack = stack_size s.stack /\
        s2.locals_size = s.locals_size` by
     (qmatch_assum_abbrev_tac `evaluate (body,s8) = _`
      \\ qspecl_then [`body`,`s8`] mp_tac evaluate_stack_swap
      \\ fs [] \\ strip_tac \\ pop_assum kall_tac
      \\ fs [Abbr`s8`,call_env_def] \\ ntac 2 (pop_assum mp_tac)
      \\ fs [push_env_def] \\ pairarg_tac \\ fs []
      \\ Cases_on `s1.stack` \\ fs [s_key_eq_def]
      \\ Cases_on `h` \\ fs [s_key_eq_def]
      \\ Cases_on `o0` \\ fs [s_key_eq_def,s_frame_key_eq_def]
      \\ fs [pop_env_def] \\ rveq \\ fs []
      \\ rw [] \\ imp_res_tac s_key_eq_stack_size \\ fs []
      \\ rw [] \\ fs [])
    \\ impl_tac THEN1
       (imp_res_tac evaluate_code_only_grows \\ fs [call_env_def]
        \\ imp_res_tac subspt_trans \\ imp_res_tac pop_env_const \\ fs []
        \\ fs [set_var_def]) \\ fs []
    \\ `s2.stack_size = s1.stack_size` by (imp_res_tac pop_env_const \\ fs [])
    \\ fs []
    \\ Cases_on `max_depth_graphs s.stack_size ns ns funs funs2`
    THEN1 fs [OPTION_MAP2_DEF] \\ fs []
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size funs2) x2)`
    THEN1 fs [OPTION_MAP2_DEF] \\ fs []
    \\ rpt strip_tac
    \\ match_mp_tac backendPropsTheory.option_le_trans
    \\ goal_assum (first_x_assum o mp_then Any mp_tac)
    \\ pop_assum mp_tac
    \\ fs [push_env_def] \\ pairarg_tac \\ fs []
    \\ fs [stack_size_def,stack_size_frame_def]
    \\ fs [GSYM stack_size_def]
    \\ Cases_on `lookup n s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `stack_size s.stack` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `s.stack_max` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `s2.stack_max` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size funs2) h1)`
    THEN1 fs [OPTION_MAP2_DEF] \\ fs []
    \\ fs [OPTION_MAP2_DEF] \\ fs [] \\ rw [MAX_DEF])
  THEN1 (* exception with handler *)
   (qpat_x_assum `_ = (_,_)` mp_tac \\ asm_rewrite_tac []
    \\ simp_tac (srw_ss()) [CaseEq"bool",CaseEq"option"]
    \\ asm_simp_tac std_ss [] \\ strip_tac
    \\ rveq \\ fs [find_code_def]
    \\ rename [`evaluate (_,set_var _ y s2) = (res3,s3)`]
    \\ last_x_assum (qspecl_then [`delete name funs`,
         `name`,`[name]`,`funs2`] mp_tac)
    \\ impl_tac THEN1 (fs [subspt_lookup,lookup_delete,call_env_def]
                       \\ fs [domain_lookup] \\ metis_tac [])
    \\ `lookup name funs2 = SOME (a,body) /\
        lookup name s.code = SOME (a,body)`
          by (fs [subspt_lookup,lookup_delete,call_env_def]
                       \\ fs [domain_lookup] \\ metis_tac [])
    \\ fs [max_depth_graphs_def]
    \\ simp [call_env_def,dec_clock_def]
    \\ rveq \\ fs []
    \\ fs [max_depth_def,max_depth_mk_Branch,backendPropsTheory.option_map2_max_add]
    \\ fs [] \\ rveq \\ fs []
    \\ Cases_on `lookup name s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `max_depth s.stack_size
            (call_graph (delete name funs) name [name] (size funs2) body)`
    THEN1 fs [OPTION_MAP2_DEF] \\ fs []
    \\ Cases_on `s2.stack_size = s.stack_size` \\ fs []
    \\ last_x_assum (qspecl_then [`funs`,`n`,`ns`,`funs2`] mp_tac)
    \\ `stack_size s2.stack = stack_size s.stack /\
        s2.locals_size = s.locals_size` by
     (qmatch_assum_abbrev_tac `evaluate (body,s8) = _`
      \\ qspecl_then [`body`,`s8`] mp_tac evaluate_stack_swap
      \\ fs [] \\ strip_tac \\ pop_assum kall_tac
      \\ fs [Abbr`s8`,call_env_def] \\ ntac 2 (pop_assum mp_tac)
      \\ fs [push_env_def] \\ pairarg_tac \\ fs [miscTheory.LASTN_LEMMA]
      \\ rveq \\ fs [] \\ rw [] \\ imp_res_tac s_key_eq_stack_size \\ fs [])
    \\ impl_tac THEN1
       (imp_res_tac evaluate_code_only_grows \\ fs [call_env_def]
        \\ imp_res_tac subspt_trans \\ imp_res_tac pop_env_const \\ fs []
        \\ fs [set_var_def]) \\ fs []
    \\ Cases_on `max_depth_graphs s.stack_size ns ns funs funs2`
    THEN1 fs [OPTION_MAP2_DEF] \\ fs []
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size funs2) x2)`
    THEN1 fs [OPTION_MAP2_DEF] \\ fs []
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size funs2) h1)`
    THEN1 fs [OPTION_MAP2_DEF] \\ fs []
    \\ rpt strip_tac
    \\ match_mp_tac backendPropsTheory.option_le_trans
    \\ goal_assum (first_x_assum o mp_then Any mp_tac)
    \\ pop_assum mp_tac
    \\ fs [push_env_def] \\ pairarg_tac \\ fs []
    \\ fs [stack_size_def,stack_size_frame_def]
    \\ fs [GSYM stack_size_def]
    \\ Cases_on `lookup n s.stack_size` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `stack_size s.stack` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `s.stack_max` THEN1 fs [OPTION_MAP2_DEF]
    \\ Cases_on `s2.stack_max` THEN1 fs [OPTION_MAP2_DEF]
    \\ fs [OPTION_MAP2_DEF] \\ fs [] \\ rw [MAX_DEF])
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
  \\ fs [max_depth_graphs_def]
  \\ fs [subspt_lookup] \\ res_tac \\ fs []
  \\ fs [GSYM OPTION_MAP2_MAX_ASSOC,max_depth_def]
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
                       (call_graph funs dest [dest] (size funs) exp))`
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
  THEN1 (fs [call_env_def,stack_size_def,stack_size_frame_def,option_le_X_MAX_X])
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
                       (call_graph funs dest [dest] (size funs) exp))`
  THEN1 fs [OPTION_MAP2_DEF]
  \\ Cases_on `s1.stack_max` \\ fs [OPTION_MAP2_DEF,MAX_DEF]
QED

val _ = export_theory();
