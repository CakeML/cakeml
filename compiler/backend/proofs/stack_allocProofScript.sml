open preamble
     stack_allocTheory
     stackSemTheory
     stackPropsTheory

val _ = new_theory"stack_allocProof";

val good_syntax_def = Define `
  (good_syntax (Alloc v) <=> (v = 1)) /\
  (good_syntax ((Seq p1 p2):'a stackLang$prog) <=>
     good_syntax p1 /\ good_syntax p2) /\
  (good_syntax ((If c r ri p1 p2):'a stackLang$prog) <=>
     good_syntax p1 /\ good_syntax p2) /\
  (good_syntax (Call x1 _ x2) <=>
     (case x1 of | SOME (y,r,_,_) => good_syntax y | NONE => T) /\
     (case x2 of SOME (y,_,_) => good_syntax y | NONE => T)) /\
  (good_syntax _ <=> T)`

val get_var_imm_case = prove(
  ``get_var_imm ri s =
    case ri of
    | Reg n => get_var n s
    | Imm w => SOME (Word w)``,
  Cases_on `ri` \\ fs [get_var_imm_def]);

val prog_comp_lemma = prove(
  ``prog_comp = \(n,p). (n,FST (comp n (next_lab p) p))``,
  fs [FUN_EQ_THM,FORALL_PROD,prog_comp_def]);

val ALOOKUP_MAP_ALT = prove(
  ``(!x n y m. (f (x,n) = (y,m)) ==> x = y) ==>
    (ALOOKUP (MAP f xs) n =
     case ALOOKUP xs n of
     | NONE => NONE
     | SOME x => SOME (SND (f(n,x))))``,
  Induct_on `xs` \\ fs [] \\ Cases \\ fs [ALOOKUP_def,FORALL_PROD]
  \\ rw [] \\ fs [] \\ Cases_on `f (n,r)` \\ fs [ALOOKUP_def] \\ res_tac \\ fs []
  \\ rw [] \\ fs [] \\ Cases_on `f (q,r)` \\ fs [ALOOKUP_def] \\ res_tac \\ fs [])

val lookup_IMP_lookup_compile = prove(
  ``lookup dest s.code = SOME x /\ 30 <= dest ==>
    ?m1 n1. lookup dest (fromAList (compile c (toAList s.code))) =
            SOME (FST (comp m1 n1 x))``,
  fs [lookup_fromAList,compile_def] \\ rw [ALOOKUP_APPEND]
  \\ `ALOOKUP (stubs c) dest = NONE` by
    (fs [stubs_def] \\ rw [] \\ fs [] \\ decide_tac) \\ fs []
  \\ fs [prog_comp_lemma] \\ fs [ALOOKUP_MAP_ALT,ALOOKUP_toAList]
  \\ metis_tac []);

val alloc_correct = prove(
  ``alloc w s = (r,t) /\ r <> SOME Error /\
    FLOOKUP s.regs 1 = SOME (Word w) ==>
    ?ck. evaluate
          (Call (SOME (Skip,0,n',m)) (INL 10) NONE,
           s with
           <|use_alloc := F; clock := s.clock + ck;
             code := fromAList (compile c (toAList s.code))|>) =
         (r,
          t with
           <|use_alloc := F; code := fromAList (compile c (toAList s.code))|>)``,
  cheat (* correctness of stubs *));

val find_code_IMP_lookup = prove(
  ``find_code dest regs (s:'a num_map) = SOME x ==>
    ?k. lookup k s = SOME x /\
        (find_code dest regs = ((lookup k):'a num_map -> 'a option))``,
  Cases_on `dest` \\ fs [find_code_def,FUN_EQ_THM]
  \\ every_case_tac \\ fs [] \\ metis_tac []);

val comp_correct = prove(
  ``!p s r t m n c.
      evaluate (p,s) = (r,t) /\ r <> SOME Error /\ good_syntax p /\
      (!k prog. lookup k s.code = SOME prog ==> 30 <= k /\ good_syntax prog) ==>
      ?ck.
        evaluate (FST (comp n m p),
           s with <| clock := s.clock + ck;
                     code := fromAList (stack_alloc$compile c (toAList s.code));
                     use_alloc := F |>) =
          (r, t with
              <| code := fromAList (stack_alloc$compile c (toAList s.code));
                 use_alloc := F |>)``,
  recInduct evaluate_ind \\ rpt strip_tac
  THEN1 (* Skip *)
   (fs [Once comp_def,evaluate_def] \\ rw [] \\ fs [state_component_equality])
  THEN1 (* Halt *)
   (fs [Once comp_def,evaluate_def,get_var_def]
    \\ CASE_TAC \\ fs [] \\ rw [] \\ fs [state_component_equality])
  THEN1 (* Alloc *)
   (fs [evaluate_def,get_var_def]
    \\ fs [Once comp_def,get_var_def]
    \\ every_case_tac \\ fs [good_syntax_def] \\ rw []
    \\ drule alloc_correct \\ fs [])
  THEN1 (* Inst *)
   (fs [Once comp_def] \\ fs [evaluate_def,inst_def]
    \\ CASE_TAC \\ fs [] \\ rw []
    \\ fs [assign_def,word_exp_def,set_var_def,mem_load_def,
         get_var_def,mem_store_def]
    \\ rw [] \\ fs [] \\ fs [state_component_equality]
    \\ every_case_tac \\ fs [markerTheory.Abbrev_def,LET_DEF,word_exp_def]
    \\ fs [state_component_equality] \\ rw [])
  THEN1 (* Get *)
   (fs [Once comp_def,evaluate_def,get_var_def]
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs [set_var_def]
    \\ fs [state_component_equality])
  THEN1 (* Set *)
   (fs [Once comp_def,evaluate_def,get_var_def,set_store_def]
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs [set_var_def]
    \\ fs [state_component_equality])
  THEN1 (* Tick *)
   (qexists_tac `0` \\ fs [Once comp_def,evaluate_def,dec_clock_def]
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs [set_var_def]
    \\ fs [state_component_equality,empty_env_def])
  THEN1 (* Seq *)
   (simp [Once comp_def,dec_clock_def] \\ fs [evaluate_def]
    \\ split_pair_tac \\ fs [LET_DEF]
    \\ split_pair_tac \\ fs [LET_DEF]
    \\ split_pair_tac \\ fs [LET_DEF]
    \\ fs [good_syntax_def,evaluate_def]
    \\ first_x_assum (qspecl_then[`m`,`n`,`c`]mp_tac)
    \\ match_mp_tac IMP_IMP \\ conj_tac
    THEN1 (CCONTR_TAC \\ fs [] \\ fs [] \\ res_tac)
    \\ strip_tac \\ rfs[]
    \\ reverse (Cases_on `res`) \\ fs []
    THEN1 (qexists_tac `ck` \\ fs [AC ADD_COMM ADD_ASSOC,LET_DEF] \\ rw [])
    \\ first_x_assum (qspecl_then[`m'`,`n`,`c`]mp_tac)
    \\ match_mp_tac IMP_IMP \\ conj_tac
    THEN1 (rw [] \\ imp_res_tac evaluate_consts \\ fs [] \\ res_tac \\ fs [])
    \\ strip_tac \\ pop_assum mp_tac
    \\ drule (GEN_ALL evaluate_add_clock) \\ simp []
    \\ disch_then (qspec_then `ck'`assume_tac) \\ strip_tac
    \\ qexists_tac `ck + ck'` \\ fs [AC ADD_COMM ADD_ASSOC]
    \\ imp_res_tac evaluate_consts \\ fs [])
  THEN1 (* Return *)
   (qexists_tac `0` \\ fs [Once comp_def,evaluate_def,get_var_def]
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs [get_var_def]
    \\ fs [state_component_equality,empty_env_def])
  THEN1 (* Raise *)
   (qexists_tac `0` \\ fs [Once comp_def,evaluate_def,get_var_def]
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs [get_var_def]
    \\ fs [state_component_equality,empty_env_def])
  THEN1 (* If *)
   (simp [Once comp_def] \\ fs [evaluate_def,get_var_def]
    \\ split_pair_tac \\ fs [] \\ split_pair_tac \\ fs []
    \\ every_case_tac \\ fs []
    \\ fs [evaluate_def,get_var_def,get_var_imm_case,good_syntax_def]
    \\ rfs []
    THENL [first_x_assum (qspecl_then[`m`,`n`,`c`]mp_tac),
           first_x_assum (qspecl_then[`m'`,`n`,`c`]mp_tac)]
    \\ match_mp_tac IMP_IMP \\ conj_tac
    \\ TRY (rw [] \\ res_tac \\ fs [] \\ NO_TAC)
    \\ strip_tac \\ fs [] \\ rfs []
    \\ qexists_tac `ck` \\ fs [AC ADD_COMM ADD_ASSOC])
  THEN1 (* JumpLess *)
   (fs [evaluate_def,get_var_def] \\ simp [Once comp_def]
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs [good_syntax_def]
    \\ fs [evaluate_def,get_var_def] \\ fs [find_code_def]
    \\ fs [state_component_equality,empty_env_def] \\ res_tac
    \\ imp_res_tac lookup_IMP_lookup_compile
    \\ pop_assum (qspec_then `c` strip_assume_tac) \\ fs []
    THEN1 (qexists_tac `0` \\ fs [state_component_equality,empty_env_def])
    \\ rfs [] \\ fs [PULL_FORALL,dec_clock_def]
    \\ first_x_assum (qspecl_then[`m1`,`n1`,`c`]mp_tac)
    \\ match_mp_tac IMP_IMP \\ conj_tac
    \\ TRY (rw [] \\ res_tac \\ fs [] \\ NO_TAC) \\ strip_tac \\ fs []
    \\ `ck + s.clock - 1 = ck + (s.clock - 1)` by decide_tac
    \\ qexists_tac `ck` \\ fs [AC ADD_COMM ADD_ASSOC])
  THEN1 (* Call *)
   (fs [evaluate_def] \\ Cases_on `ret` \\ fs [] THEN1
     (Cases_on `find_code dest s.regs s.code` \\ fs []
      \\ every_case_tac \\ fs [empty_env_def] \\ rw [] \\ fs []
      \\ fs [good_syntax_def] \\ simp [Once comp_def,evaluate_def]
      \\ drule find_code_IMP_lookup \\ fs [] \\ rw [] \\ fs [] \\ fs []
      \\ res_tac \\ imp_res_tac lookup_IMP_lookup_compile
      \\ pop_assum (strip_assume_tac o SPEC_ALL) \\ fs []
      THEN1 (qexists_tac `0` \\ fs [empty_env_def,state_component_equality])
      THEN1 (qexists_tac `0` \\ fs [empty_env_def,state_component_equality])
      \\ fs [dec_clock_def]
      \\ first_x_assum (qspecl_then[`n1`,`m1`,`c`]mp_tac)
      \\ match_mp_tac IMP_IMP \\ conj_tac
      \\ TRY (rw [] \\ res_tac \\ fs [] \\ NO_TAC) \\ strip_tac \\ fs []
      \\ `ck + s.clock - 1 = ck + (s.clock - 1)` by decide_tac
      \\ qexists_tac `ck` \\ fs [AC ADD_COMM ADD_ASSOC])
    \\ qmatch_assum_rename_tac `good_syntax (Call (SOME z) dest handler)`
    \\ PairCases_on `z` \\ fs [] \\ simp [Once comp_def] \\ fs []
    \\ split_pair_tac \\ fs []
    \\ Cases_on `find_code dest (s.regs \\ z1) s.code` \\ fs []
    \\ drule find_code_IMP_lookup \\ rw [] \\ fs []
    \\ res_tac \\ imp_res_tac lookup_IMP_lookup_compile
    \\ pop_assum (qspec_then`c`strip_assume_tac) \\ fs [good_syntax_def]
    \\ Cases_on `s.clock = 0` \\ fs [] THEN1
     (rw [] \\ fs [] \\ every_case_tac \\ fs []
      \\ TRY split_pair_tac \\ fs [evaluate_def]
      \\ qexists_tac `0` \\ fs []
      \\ fs [empty_env_def,state_component_equality])
    \\ Cases_on `evaluate (x,dec_clock (set_var z1 (Loc z2 z3) s))`
    \\ Cases_on `q` \\ fs []
    \\ Cases_on `x'` \\ fs [] \\ rw [] \\ TRY
     (every_case_tac \\ fs [] \\ TRY split_pair_tac
      \\ fs [evaluate_def,dec_clock_def,set_var_def]
      \\ first_x_assum (qspecl_then[`n1`,`m1`,`c`]mp_tac)
      \\ match_mp_tac IMP_IMP \\ conj_tac
      \\ TRY (rw [] \\ res_tac \\ fs [] \\ NO_TAC) \\ strip_tac \\ fs []
      \\ `ck + s.clock - 1 = s.clock - 1 + ck` by decide_tac
      \\ qexists_tac `ck` \\ fs [] \\ NO_TAC)
    THEN1
     (Cases_on `w = Loc z2 z3` \\ rw [] \\ fs []
      \\ first_x_assum (qspecl_then[`m`,`n`,`c`]mp_tac)
      \\ match_mp_tac IMP_IMP \\ conj_tac
      \\ TRY (imp_res_tac evaluate_consts \\ fs []
              \\ rw [] \\ res_tac \\ fs [] \\ NO_TAC)
      \\ strip_tac \\ fs [] \\ rfs []
      \\ first_x_assum (qspecl_then[`n1`,`m1`,`c`]mp_tac)
      \\ match_mp_tac IMP_IMP \\ conj_tac
      \\ TRY (imp_res_tac evaluate_consts \\ fs []
              \\ rw [] \\ res_tac \\ fs [] \\ NO_TAC) \\ rw []
      \\ Cases_on `handler` \\ fs []
      \\ TRY (PairCases_on `x'` \\ ntac 2 (split_pair_tac \\ fs []))
      \\ fs [evaluate_def,dec_clock_def,set_var_def]
      \\ first_assum (mp_tac o Q.SPEC `ck` o
             MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
             (evaluate_add_clock |> GEN_ALL))) \\ fs []
      \\ rw [] \\ qexists_tac `ck' + ck` \\ fs [AC ADD_COMM ADD_ASSOC]
      \\ `ck + (ck' + (s.clock - 1)) = ck + (ck' + s.clock) - 1` by decide_tac
      \\ fs [] \\ imp_res_tac evaluate_consts \\ fs [])
    \\ Cases_on `handler` \\ fs[]
    \\ fs [evaluate_def,dec_clock_def,set_var_def]
    THEN1
     (first_x_assum (qspecl_then[`n1`,`m1`,`c`]mp_tac)
      \\ match_mp_tac IMP_IMP \\ conj_tac
      \\ TRY (imp_res_tac evaluate_consts \\ fs []
              \\ rw [] \\ res_tac \\ fs [] \\ NO_TAC) \\ rw []
      \\ `ck + s.clock - 1 = s.clock - 1 + ck` by decide_tac
      \\ qexists_tac `ck` \\ fs [])
    \\ PairCases_on `x'` \\ fs []
    \\ split_pair_tac \\ fs []
    \\ fs [evaluate_def,dec_clock_def,set_var_def]
    \\ Cases_on `w = Loc x'1 x'2` \\ rw [] \\ fs []
    \\ ntac 2 (pop_assum mp_tac)
    \\ first_x_assum (qspecl_then[`n1`,`m1`,`c`]mp_tac)
    \\ match_mp_tac IMP_IMP \\ conj_tac
    \\ TRY (imp_res_tac evaluate_consts \\ fs []
            \\ rw [] \\ res_tac \\ fs [] \\ NO_TAC) \\ rw [] \\ rfs[]
    \\ first_x_assum (qspecl_then[`m'`,`n`,`c`]mp_tac)
    \\ match_mp_tac IMP_IMP \\ conj_tac
    \\ TRY (imp_res_tac evaluate_consts \\ fs []
            \\ rw [] \\ res_tac \\ fs [] \\ NO_TAC) \\ rw []
    \\ ntac 2 (pop_assum mp_tac)
    \\ first_assum (mp_tac o Q.SPEC `ck'` o
             MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
             (evaluate_add_clock |> GEN_ALL))) \\ fs [] \\ rw []
    \\ qexists_tac `ck+ck'` \\ fs []
    \\ `ck + ck' + s.clock - 1 = s.clock - 1 + ck + ck'` by decide_tac \\ fs[]
    \\ imp_res_tac evaluate_consts \\ fs [])
  THEN1 (* FFI *)
   (qexists_tac `0` \\ fs [Once comp_def,evaluate_def,get_var_def]
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs [get_var_def]
    \\ fs [state_component_equality,empty_env_def,LET_DEF])
  \\ qexists_tac `0` \\ fs [Once comp_def,evaluate_def,get_var_def,set_var_def]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs [get_var_def]
  \\ fs [state_component_equality,empty_env_def,LET_DEF]);

val compile_semantics = store_thm("compile_semantics",
  ``(!k prog. lookup k s.code = SOME prog ==> 30 < k /\ good_syntax prog) /\
    semantics start s <> Fail ==>
    semantics start (s with <|
                       code := fromAList (stack_alloc$compile c (toAList s.code));
                       use_alloc := F |>) =
    semantics start s``,
  cheat);

val _ = export_theory();
