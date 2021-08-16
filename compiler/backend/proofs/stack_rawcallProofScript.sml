(*
  Correctness proof for stack_rawcall
*)

open preamble stackLangTheory stackSemTheory stackPropsTheory stack_rawcallTheory
local open wordSemTheory labPropsTheory in end

val _ = new_theory"stack_rawcallProof";
val _ = (max_print_depth := 18);

val word_shift_def = backend_commonTheory.word_shift_def
val theWord_def = wordSemTheory.theWord_def;
val isWord_def = wordSemTheory.isWord_def;

val _ = set_grammar_ancestry["stack_rawcall","stackLang","stackSem","stackProps"];
Overload good_dimindex[local] = ``labProps$good_dimindex``
Overload comp[local] = ``stack_rawcall$comp``
Overload compile[local] = ``stack_rawcall$compile``
Type prog[pp] = “:α stackLang$prog”

Definition state_ok_def:
  state_ok i code <=>
    !n v.
      lookup n i = SOME v ==>
      ?p. lookup n code = SOME (Seq (StackAlloc v) p)
End

Definition state_rel_def:
  state_rel i s t <=>
    ?c (* co cc *).
      domain c = domain s.code /\
      t = s with <| code := c (* ;
                    compile := cc ;
                    compile_oracle := co *) |> /\
(*    s.compile = pure_cc compile t.compile /\
      t.compile_oracle = (I ## compile ## I) o s.compile_oracle /\ *)
      state_ok i s.code /\
      !n b.
        lookup n s.code = SOME b ==>
        ?i. state_ok i s.code /\
            lookup n c = SOME (comp_top i b)
End

Theorem state_rel_thm =
  state_rel_def |> SIMP_RULE (srw_ss()) [state_component_equality];

Triviality with_stack_space:
  t1 with stack_space := t1.stack_space = t1
Proof
  fs [state_component_equality]
QED

Theorem comp_LN:
  !(i:num num_map) b. comp_top LN b = b /\ comp LN b = b
Proof
  recInduct comp_ind \\ rw []
  \\ Cases_on `p` \\ simp [Once comp_def,Once comp_top_def]
  \\ fs [CaseEq"option",pair_case_eq,PULL_EXISTS,comp_seq_def,lookup_def]
  \\ CCONTR_TAC \\ fs []
  \\ rename [`oo <> NONE`]
  \\ Cases_on `oo` \\ fs []
  \\ PairCases_on `x` \\ fs [] \\ fs []
  \\ TRY (rename [`oo <> NONE`]
          \\ Cases_on `oo` \\ fs []
          \\ PairCases_on `x` \\ fs [] \\ fs [])
  \\ TRY (rename [`NONE <> oo`]
          \\ Cases_on `oo` \\ fs []
          \\ PairCases_on `x` \\ fs [] \\ fs [])
QED

Theorem comp_seq_neq_IMP:
  comp_seq p1 p2 i default <> default ==>
  ?k dest. p1 = StackFree k /\ p2 = Call NONE (INL dest) NONE
Proof
  fs [comp_seq_def,CaseEq"option",pair_case_eq,bool_case_eq]
  \\ rw []
  \\ Cases_on `dest_case p1 p2` \\ fs []
  \\ PairCases_on`x` \\ fs []
  \\ fs [dest_case_def,AllCaseEqs()]
  \\ rveq \\ fs []
QED

Theorem get_labels_comp:
  !i e.
    get_labels (comp i e) = get_labels e /\
    get_labels (comp_top i e) = get_labels e
Proof
  recInduct comp_ind
  \\ rpt gen_tac \\ strip_tac
  \\ Cases_on `p` \\ simp [comp_top_def]
  \\ TRY (once_rewrite_tac [comp_def] \\ simp [] \\ fs [get_labels_def] \\ NO_TAC)
  THEN1 (once_rewrite_tac [comp_def] \\ simp [] \\ every_case_tac \\ fs [get_labels_def])
  \\ simp [Once comp_def]
  \\ Cases_on `comp_seq p' p0 i (Seq (comp i p') (comp i p0)) =
               Seq (comp i p') (comp i p0)`
  THEN1 (fs [] \\ once_rewrite_tac [get_labels_def] \\ fs [])
  \\ drule comp_seq_neq_IMP
  \\ strip_tac \\ rveq \\ fs []
  \\ fs [get_labels_def]
  \\ fs [comp_seq_def,dest_case_def,CaseEq"option"]
  \\ CASE_TAC \\ fs []
  \\ rw [] \\ fs [get_labels_def]
QED

val simple_case =
  qexists_tac `0`
  \\ fs [Once comp_def,evaluate_def,get_var_def,set_var_def,loc_check_def,mem_load_def,
         alloc_def,gc_def,set_store_def,inst_def,assign_def,word_exp_def,get_vars_def,
         mem_store_def,get_fp_var_def,set_fp_var_def,wordLangTheory.word_op_def,
         store_const_sem_def]
  \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq,CaseEq"ffi_result",pair_case_eq,
         CaseEq"inst",CaseEq"arith",IS_SOME_EXISTS,CaseEq"list",CaseEq"memop",
         CaseEq"addr",CaseEq"fp",CaseEq"binop"] \\ rfs []
  \\ rveq \\ fs []
  \\ simp [state_rel_def,PULL_EXISTS]
  \\ fs [state_rel_thm,state_component_equality,empty_env_def]
  \\ fs [state_rel_thm,state_component_equality,empty_env_def,dec_clock_def]

Theorem evaluate_comp_Inst:
  evaluate (Inst i,s) = (r,s1) /\ r ≠ SOME Error /\ state_rel i' s t ==>
  ∃ck t1 k1.
    state_rel i' s1 t1 ∧
    evaluate (comp i' (Inst i),t with clock := ck + t.clock) =
    (r,t1 with stack_space := k1) ∧
    (r ≠ SOME TimeOut ∧ r ≠ SOME (Halt (Word 2w)) ⇒
     k1 = t1.stack_space)
Proof
  rw [] \\ reverse simple_case
  THEN1 (pairarg_tac \\ fs [] \\ fs [bool_case_eq] \\ rveq \\ fs [])
  \\ every_case_tac \\ fs [word_exp_def]
QED

Theorem comp_correct:
   !p (s:('a,'c,'b)stackSem$state) t i r s1.
     evaluate (p,s) = (r,s1) /\ r <> SOME Error /\ state_rel i s t
     ==>
     (?ck t1 k1.
        state_rel i s1 t1 /\
        evaluate (stack_rawcall$comp_top i p,t with clock := t.clock + ck) =
          (r,t1 with stack_space := k1) /\
        (r <> SOME TimeOut /\ r <> SOME (Halt (Word 2w)) ==> k1 = t1.stack_space)) /\
     (?ck t1 k1.
        state_rel i s1 t1 /\
        evaluate (stack_rawcall$comp i p,t with clock := t.clock + ck) =
          (r,t1 with stack_space := k1) /\
        (r <> SOME TimeOut /\ r <> SOME (Halt (Word 2w)) ==> k1 = t1.stack_space))
Proof
  recInduct evaluate_ind \\ rpt conj_tac \\ rpt gen_tac
  \\ strip_tac \\ simp [comp_top_def]
  THEN1
   (rename [`Skip`] \\ simple_case)
  THEN1
   (rename [`Halt`] \\ simple_case)
  THEN1
   (rename [`Alloc`] \\ simple_case)
  THEN1
   (rename [`StoreConsts`] \\ simple_case \\ rw []
    \\ fs [unset_var_def,check_store_consts_opt_def]
    \\ Cases_on ‘stub_opt’
    \\ fs [unset_var_def,check_store_consts_opt_def]
    \\ res_tac \\ fs [comp_top_def,Once comp_def])
  THEN1
   (rename [`Inst`] \\ match_mp_tac evaluate_comp_Inst \\ fs [])
  THEN1
   (rename [`Get`] \\ simple_case)
  THEN1
   (rename [`Set`] \\ simple_case)
  THEN1
   (rename [`OpCurrHeap`] \\ simple_case)
  THEN1
   (rename [`Tick`] \\ simple_case)
  THEN1
   (rename [`Seq`]
    \\ rpt gen_tac \\ strip_tac
    \\ conj_asm1_tac THEN1
     (fs [evaluate_def] \\ rpt (pairarg_tac \\ fs [])
      \\ reverse (fs [CaseEq"bool"]) \\ rveq \\ fs []
      THEN1
       (first_x_assum drule \\ strip_tac \\ fs []
        \\ qexists_tac `ck'` \\ fs [] \\ metis_tac [])
      \\ first_x_assum drule \\ rewrite_tac [GSYM AND_IMP_INTRO]
      \\ disch_then kall_tac \\ strip_tac
      \\ first_x_assum drule \\ rewrite_tac [GSYM AND_IMP_INTRO]
      \\ disch_then kall_tac \\ strip_tac
      \\ `t1 with stack_space := t1.stack_space = t1` by fs [state_component_equality]
      \\ fs []
      \\ qpat_x_assum `evaluate (comp i c1,_) = (NONE,_)` assume_tac
      \\ drule evaluate_add_clock \\ fs []
      \\ disch_then (qspec_then `ck'` assume_tac)
      \\ qexists_tac `ck + ck'` \\ fs []
      \\ asm_exists_tac \\ simp [state_component_equality])
    \\ Cases_on `comp i (Seq c1 c2) = Seq (comp i c1) (comp i c2)`
    THEN1 asm_rewrite_tac []
    \\ fs [] \\ simp [comp_top_def]
    \\ ntac 1 (pop_assum mp_tac)
    \\ simp [Q.SPECL[`Seq c1 c2`] comp_def]
    \\ simp [comp_seq_def]
    \\ simp [CaseEq"option",pair_case_eq,FORALL_PROD,PULL_EXISTS]
    \\ Cases_on `dest_case c1 c2` \\ fs []
    \\ PairCases_on `x` \\ fs []
    \\ Cases_on `lookup x1 i` \\ fs []
    \\ disch_then kall_tac
    \\ fs [dest_case_def,CaseEq"stackLang$prog",CaseEq"option",CaseEq"sum"]
    \\ rveq \\ fs []
    \\ qpat_x_assum `evaluate _ = _` kall_tac
    \\ qpat_x_assum `evaluate _ = _` mp_tac
    \\ qpat_x_assum `!x. _` kall_tac
    \\ simp [evaluate_def]
    \\ IF_CASES_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs [find_code_def]
    \\ qpat_assum `state_rel i s t` (mp_tac o REWRITE_RULE [state_rel_thm])
    \\ strip_tac
    \\ qpat_assum `state_ok i _` (mp_tac o REWRITE_RULE [state_ok_def])
    \\ disch_then drule \\ strip_tac
    \\ first_assum drule
    \\ strip_tac \\ fs []
    \\ IF_CASES_TAC \\ fs [] \\ rveq
    \\ Cases_on `s.clock = 0` \\ fs []
    THEN1
     (rpt strip_tac \\ rveq \\ fs []
      \\ qexists_tac `0` \\ fs []
      \\ simp [state_rel_def,PULL_EXISTS]
      \\ asm_exists_tac \\ simp [empty_env_def]
      \\ rw [] \\ fs [] \\ simp [evaluate_def,dest_Seq_def,comp_top_def,empty_env_def]
      \\ fs [state_component_equality,empty_env_def])
    \\ fs [dec_clock_def]
    \\ last_x_assum mp_tac
    \\ simp [Once evaluate_def]
    \\ simp [Once evaluate_def,find_code_def,dec_clock_def]
    \\ TOP_CASE_TAC \\ Cases_on `q` \\ fs []
    \\ rpt strip_tac \\ rveq \\ fs [] \\ rfs []
    \\ rename [`s with stack_space := k + s.stack_space`]
    \\ `state_rel i
           (s with stack_space := k + s.stack_space)
           (t with stack_space := k + t.stack_space)`
         by fs [state_rel_thm]
    \\ first_x_assum drule
    \\ rewrite_tac [GSYM AND_IMP_INTRO]
    \\ disch_then kall_tac
    \\ simp[Once comp_def]
    \\ simp [Once evaluate_def,find_code_def,dec_clock_def,comp_top_def]
    \\ simp[Once comp_def]
    \\ strip_tac
    \\ asm_exists_tac \\ simp []
    \\ rw []
    THEN1
     (simp [Once evaluate_def,comp_top_def,dest_Seq_def,dec_clock_def]
      \\ qexists_tac `ck'` \\ fs []
      \\ once_rewrite_tac [CONJ_COMM] \\ asm_exists_tac \\ simp []
      \\ ntac 2 (pop_assum mp_tac)
      \\ simp [evaluate_def]
      \\ qpat_abbrev_tac `pat1 = (comp i' p, _)`
      \\ qpat_abbrev_tac `pat2 = (comp i' p, _)`
      \\ qsuff_tac `pat1 = pat2` \\ fs []
      \\ unabbrev_all_tac \\ fs [state_component_equality])
    THEN1
     (simp [evaluate_def]
      \\ simp [comp_top_def,dest_Seq_def,dec_clock_def]
      \\ qexists_tac `ck'` \\ fs []
      \\ once_rewrite_tac [CONJ_COMM] \\ asm_exists_tac \\ simp []
      \\ qpat_x_assum `_ = (_,_)` mp_tac
      \\ simp [evaluate_def])
    THEN1
     (simp [evaluate_def]
      \\ simp [comp_top_def,dest_Seq_def,dec_clock_def]
      \\ qpat_x_assum `_ = (_,_)` mp_tac
      (* \\ qpat_x_assum `_ = (_,_)` mp_tac *)
      \\ simp [evaluate_def]
      \\ `k + s.stack_space < x <=> s.stack_space < x - k` by fs []
      \\ asm_rewrite_tac [] \\ pop_assum kall_tac
      \\ IF_CASES_TAC \\ fs [empty_env_def]
      THEN1
       (rw [] \\ fs [state_component_equality,empty_env_def]
        \\ qexists_tac `ck'` \\ fs [])
      \\ simp [dest_Seq_def,comp_top_def]
      \\ TOP_CASE_TAC \\ fs []
      \\ TOP_CASE_TAC \\ fs []
      \\ strip_tac \\ rveq \\ fs []
      \\ qexists_tac `ck' + 1` \\ fs []
      \\ once_rewrite_tac [CONJ_COMM] \\ asm_exists_tac \\ simp []))
  THEN1
   (rename [`Return`] \\ simple_case)
  THEN1
   (rename [`Raise`] \\ simple_case)
  THEN1
   (rename [`If`]
    \\ simp [Once comp_def]
    \\ fs [evaluate_def,get_var_def,CaseEq"option",CaseEq"bool"]
    \\ rpt strip_tac \\ rveq \\ fs [] \\ simp [PULL_EXISTS]
    \\ first_x_assum drule
    \\ rewrite_tac [GSYM AND_IMP_INTRO] \\ disch_then kall_tac
    \\ strip_tac
    \\ asm_exists_tac \\ fs []
    \\ qexists_tac `ck` \\ fs []
    \\ qexists_tac `k1` \\ fs []
    \\ once_rewrite_tac [METIS_PROVE [] ``b1/\b2/\b3/\b4 <=> b3/\b1/\b2/\b4``]
    \\ asm_exists_tac \\ fs []
    \\ fs [state_rel_thm]
    \\ Cases_on `ri` \\ fs [get_var_imm_def,get_var_def])
  THEN1
   (rename [`While`]
    \\ simp [Once comp_def]
    \\ fs [evaluate_def,get_var_def,CaseEq"option",CaseEq"bool",CaseEq"word_loc"]
    \\ reverse (rpt strip_tac \\ rveq \\ fs [] \\ simp [PULL_EXISTS])
    \\ `get_var_imm ri t = get_var_imm ri s` by
          (Cases_on `ri` \\ fs [get_var_imm_def,get_var_def,state_rel_thm]) \\ fs []
    THEN1
     (simp [state_rel_def,PULL_EXISTS]
      \\ fs [state_rel_thm] \\ fs [state_component_equality])
    \\ pairarg_tac \\ fs [CaseEq"bool"] \\ rveq \\ fs []
    THEN1
     (first_x_assum drule
      \\ rewrite_tac [GSYM AND_IMP_INTRO] \\ disch_then kall_tac
      \\ strip_tac \\ qexists_tac `ck` \\ fs []
      \\ asm_exists_tac \\ fs [] \\ fs [state_rel_thm]
      \\ qexists_tac `k1` \\ fs [])
    THEN1
     (first_x_assum drule
      \\ rewrite_tac [GSYM AND_IMP_INTRO] \\ disch_then kall_tac
      \\ strip_tac \\ qexists_tac `ck` \\ fs []
      \\ rename [`state_rel i s2 t2`]
      \\ `state_rel i (empty_env s2) (empty_env t2)` by
            fs [state_rel_thm,empty_env_def]
      \\ asm_exists_tac \\ fs [] \\ fs [state_rel_thm]
      \\ fs [empty_env_def,state_component_equality])
    \\ fs [with_stack_space]
    \\ first_x_assum drule
    \\ rewrite_tac [GSYM AND_IMP_INTRO] \\ disch_then kall_tac
    \\ strip_tac
    \\ rename [`state_rel i s2 t2`]
    \\ `state_rel i (dec_clock s2) (dec_clock t2)` by
          fs [state_rel_thm,dec_clock_def]
    \\ first_x_assum drule
    \\ rewrite_tac [GSYM AND_IMP_INTRO] \\ disch_then kall_tac
    \\ strip_tac \\ fs [dec_clock_def]
    \\ asm_exists_tac \\ fs []
    \\ fs [state_rel_thm]
    \\ qpat_x_assum `_ = (NONE,_)` assume_tac
    \\ drule evaluate_add_clock
    \\ disch_then (qspec_then `ck'` mp_tac)
    \\ simp [] \\ strip_tac
    \\ qexists_tac `ck + ck'` \\ fs [] \\ fs [STOP_def]
    \\ fs [Q.SPEC `While c r1 r2 b` comp_def]
    \\ rfs [] \\ qexists_tac `k1` \\ fs [])
  THEN1
   (rename [`JumpLower`]
    \\ simp [Once comp_def]
    \\ fs [evaluate_def,get_var_def,CaseEq"option",CaseEq"bool",CaseEq"word_loc"]
    \\ reverse (rpt strip_tac \\ rveq \\ fs [] \\ simp [PULL_EXISTS])
    THEN1 (asm_exists_tac \\ fs [] \\ fs [state_rel_thm]
           \\ fs [state_component_equality])
    THEN1
     (fs [pair_case_eq,CaseEq"option"] \\ rveq \\ fs []
      \\ qpat_assum `state_rel i s t` (fn th => mp_tac (REWRITE_RULE [state_rel_thm] th))
      \\ strip_tac \\ fs [find_code_def]
      \\ first_x_assum drule \\ strip_tac
      \\ `state_rel i' (dec_clock s) (dec_clock t)` by
            fs [state_rel_thm,dec_clock_def]
      \\ first_x_assum drule \\ strip_tac \\ fs [dec_clock_def]
      \\ qexists_tac `ck` \\ fs [] \\ rfs []
      \\ qexists_tac `t1` \\ fs [] \\ rfs []
      \\ qexists_tac `k1` \\ fs [] \\ rfs []
      \\ fs [state_rel_thm]
      \\ fs [state_ok_def] \\ rw []
      \\ res_tac \\ imp_res_tac evaluate_mono \\ fs []
      \\ metis_tac [subspt_lookup])
    \\ qexists_tac `0`
    \\ qexists_tac `empty_env t`
    \\ fs [state_rel_thm,empty_env_def,find_code_def]
    \\ res_tac \\ fs [state_component_equality])
  THEN1
   (rename [`RawCall`]
    \\ simp [Once comp_def]
    \\ fs [evaluate_def,get_var_def,CaseEq"option",CaseEq"bool",
           CaseEq"word_loc",pair_case_eq]
    \\ rpt strip_tac \\ rveq \\ fs [] \\ simp [PULL_EXISTS]
    \\ Cases_on `prog` \\ fs [dest_Seq_def]
    THEN1
     (qexists_tac `0` \\ qexists_tac `empty_env t`
      \\ fs [state_rel_thm,empty_env_def,find_code_def]
      \\ res_tac \\ fs [state_component_equality]
      \\ fs [dest_Seq_def,comp_top_def])
    \\ rveq \\ fs []
    \\ qpat_assum `state_rel i s t` (fn th => mp_tac (REWRITE_RULE [state_rel_thm] th))
    \\ strip_tac \\ fs [find_code_def]
    \\ res_tac
    \\ `state_rel i' (dec_clock s) (dec_clock t)` by
          fs [state_rel_thm,dec_clock_def]
    \\ last_x_assum drule
    \\ strip_tac \\ fs [] \\ simp [comp_top_def,dest_Seq_def]
    \\ qexists_tac `ck'` \\ rfs [dec_clock_def] \\ fs []
    \\ qexists_tac `t1'` \\ rfs [dec_clock_def] \\ fs []
    \\ qexists_tac `k1'` \\ rfs [dec_clock_def] \\ fs []
    \\ fs [state_rel_thm]
    \\ fs [state_ok_def] \\ rw []
    \\ res_tac \\ imp_res_tac evaluate_mono \\ fs []
    \\ metis_tac [subspt_lookup])
  THEN1
   (rename [`Call`]
    \\ simp [Once comp_def]
    \\ fs [evaluate_def,get_var_def,CaseEq"option",CaseEq"bool",
           CaseEq"word_loc",pair_case_eq]
    \\ rpt strip_tac \\ rveq \\ fs [] \\ simp [PULL_EXISTS]
    \\ (`?i. state_ok i s.code /\
            find_code dest t.regs t.code = SOME (comp_top i prog)` by
     (Cases_on `dest`
      \\ fs [find_code_def,CaseEq"option",CaseEq"word_loc",CaseEq"bool",CaseEq"num"]
      \\ fs [state_rel_thm]) ORELSE
        `?i. state_ok i s.code /\
            find_code dest (t.regs \\ link_reg) t.code = SOME (comp_top i prog)` by
     (Cases_on `dest`
      \\ fs [find_code_def,CaseEq"option",CaseEq"word_loc",CaseEq"bool",CaseEq"num"]
      \\ fs [state_rel_thm]))
    THEN1
     (qexists_tac `0` \\ qexists_tac `empty_env t`
      \\ fs [state_rel_thm,empty_env_def,evaluate_def] \\ rfs []
      \\ fs [state_component_equality])
    THEN1
     (`state_rel i' (dec_clock s) (dec_clock t)` by fs [dec_clock_def,state_rel_thm]
      \\ first_x_assum drule \\ strip_tac
      \\ qexists_tac `ck` \\ qexists_tac `t1`
      \\ fs [evaluate_def] \\ rfs [state_rel_thm,dec_clock_def]
      \\ fs [state_component_equality]
      \\ fs [state_ok_def] \\ rw []
      \\ res_tac \\ imp_res_tac evaluate_mono \\ fs []
      \\ metis_tac [subspt_lookup])
    THEN1
     (every_case_tac \\ fs []
      \\ qexists_tac `0` \\ qexists_tac `empty_env t`
      \\ fs [state_rel_thm,empty_env_def,evaluate_def]
      \\ rfs [state_component_equality])
    \\ qmatch_goalsub_abbrev_tac `evaluate (pp,_)`
    \\ `pp =
        Call (SOME (comp i ret_handler,link_reg,l1,l2)) dest
          (case handler of
           | NONE => NONE
           | SOME (p2,k1,k2) => SOME (comp i p2,k1,k2))` by
          (fs [Abbr`pp`] \\ every_case_tac \\ fs [])
    \\ simp [] \\ pop_assum kall_tac
    \\ fs [evaluate_def] \\ pop_assum kall_tac
    \\ qpat_assum `state_rel i s t` (fn th => mp_tac (REWRITE_RULE [state_rel_thm] th))
    \\ strip_tac \\ rfs []
    \\ reverse (fs [CaseEq"result"]) \\ rveq \\ fs []
    \\ first_x_assum (qspecl_then
         [`dec_clock (set_var link_reg (Loc l1 l2) t)`,`i'`] mp_tac)
    \\ (impl_tac THEN1 fs [state_rel_thm,set_var_def,dec_clock_def])
    \\ strip_tac
    THEN1
     (qexists_tac `ck` \\ fs []
      \\ qexists_tac `t1` \\ fs [dec_clock_def,set_var_def] \\ rfs []
      \\ fs [state_ok_def,state_rel_thm] \\ rw []
      \\ res_tac \\ imp_res_tac evaluate_mono \\ fs []
      \\ metis_tac [subspt_lookup])
    THEN1
     (qexists_tac `ck` \\ fs []
      \\ qexists_tac `t1` \\ fs [dec_clock_def,set_var_def]
      \\ rfs [state_component_equality]
      \\ fs [state_ok_def,state_rel_thm] \\ rw []
      \\ res_tac \\ imp_res_tac evaluate_mono \\ fs []
      \\ metis_tac [subspt_lookup])
    THEN1
     (qexists_tac `ck` \\ fs []
      \\ qexists_tac `t1` \\ fs [dec_clock_def,set_var_def]
      \\ rfs [state_component_equality]
      \\ fs [state_ok_def,state_rel_thm] \\ rw []
      \\ res_tac \\ imp_res_tac evaluate_mono \\ fs []
      \\ metis_tac [subspt_lookup])
    THEN1
     (Cases_on `handler` THEN1
       (qexists_tac `ck` \\ fs [evaluate_def]
        \\ qexists_tac `t1` \\ fs [dec_clock_def,set_var_def]
        \\ fs [with_stack_space] \\ rfs [] \\ rveq \\ fs [with_stack_space]
        \\ fs [state_ok_def,state_rel_thm] \\ rw []
        \\ res_tac \\ imp_res_tac evaluate_mono \\ fs []
        \\ metis_tac [subspt_lookup])
      \\ fs [CaseEq"option",pair_case_eq,CaseEq"bool"] \\ rveq \\ fs []
      \\ `state_rel i s2 t1` by
       (fs [state_ok_def,state_rel_thm] \\ rw []
        \\ first_x_assum drule \\ rw [] \\ imp_res_tac evaluate_mono \\ fs []
        \\ metis_tac [subspt_lookup])
      \\ first_x_assum drule
      \\ rewrite_tac [GSYM AND_IMP_INTRO] \\ disch_then kall_tac \\ strip_tac
      \\ qexists_tac `ck + ck''`
      \\ qexists_tac `t1''`
      \\ qexists_tac `k1` \\ fs [PULL_EXISTS]
      \\ qpat_x_assum `evaluate (comp_top i' prog,_) = _` assume_tac
      \\ drule evaluate_add_clock
      \\ disch_then (qspec_then `ck''` assume_tac)
      \\ fs [dec_clock_def,set_var_def] \\ rfs []
      \\ qpat_x_assum `evaluate (comp i h,_) = _` (fn th => rewrite_tac [GSYM th])
      \\ AP_TERM_TAC \\ fs [] \\ fs [state_component_equality])
    THEN1
     (`state_rel i s2 t1` by
       (fs [state_ok_def,state_rel_thm] \\ rw []
        \\ first_x_assum drule \\ rw [] \\ imp_res_tac evaluate_mono \\ fs []
        \\ metis_tac [subspt_lookup])
      \\ fs [CaseEq"bool"] \\ rveq \\ fs []
      \\ first_x_assum drule
      \\ rewrite_tac [GSYM AND_IMP_INTRO] \\ disch_then kall_tac \\ strip_tac
      \\ qexists_tac `ck + ck''`
      \\ qexists_tac `t1''`
      \\ qexists_tac `k1` \\ fs [PULL_EXISTS]
      \\ qpat_x_assum `evaluate (comp_top i' prog,_) = _` assume_tac
      \\ drule evaluate_add_clock
      \\ disch_then (qspec_then `ck''` assume_tac)
      \\ fs [dec_clock_def,set_var_def] \\ rfs []
      \\ qpat_x_assum `evaluate (comp i h,_) = _` (fn th => rewrite_tac [GSYM th])
      \\ AP_TERM_TAC \\ fs [] \\ fs [state_component_equality]))
  THEN1
   (rename [`Install`]
    \\ fs [evaluate_def,CaseEq"option",pair_case_eq,CaseEq"word_loc",
           state_rel_thm,Once comp_def,PULL_EXISTS]
    \\ rpt (pairarg_tac \\ fs [])
    \\ fs [evaluate_def,CaseEq"option",pair_case_eq,CaseEq"word_loc",CaseEq"list",
           CaseEq"bool"] \\ rveq \\ fs [PULL_EXISTS,with_stack_space]
    \\ fs [get_var_def]
    \\ qabbrev_tac `new_prog = (k,prog)::v7`
    \\ fs [domain_union]
    \\ (conj_asm1_tac THEN1 (fs [state_ok_def,lookup_union] \\ rw [] \\ res_tac \\ fs []))
    \\ fs [lookup_union,CaseEq"option"]
    \\ (reverse (rpt strip_tac) THEN1
     (res_tac \\ fs []
      \\ qexists_tac `i'` \\ fs []
      \\ fs [state_ok_def,lookup_union] \\ rw [] \\ res_tac \\ fs []))
    \\ qexists_tac `LN` \\ fs []
    \\ simp [state_ok_def,lookup_def,comp_LN]
    \\ fs [domain_lookup,EXTENSION]
    \\ last_x_assum (qspec_then `n` mp_tac)
    \\ Cases_on `lookup n t.code` \\ fs [])
  THEN1
   (rename [`CodeBufferWrite`] \\ simple_case)
  THEN1
   (rename [`DataBufferWrite`] \\ simple_case)
  THEN1
   (rename [`FFI`] \\ simple_case)
  THEN1
   (rename [`LocValue`] \\ simple_case
    \\ res_tac \\ disj2_tac \\ asm_exists_tac \\ fs [get_labels_comp])
  THEN1
   (rename [`StackAlloc`] \\ simple_case)
  THEN1
   (rename [`StackFree`] \\ simple_case)
  THEN1
   (rename [`StackLoad`] \\ simple_case)
  THEN1
   (rename [`StackLoadAny`] \\ simple_case)
  THEN1
   (rename [`StackStore`] \\ simple_case)
  THEN1
   (rename [`StackStoreAny`] \\ simple_case)
  THEN1
   (rename [`StackGetSize`] \\ simple_case)
  THEN1
   (rename [`StackSetSize`] \\ simple_case)
  THEN1
   (rename [`BitmapLoad`] \\ simple_case)
QED

Theorem domain_fromAList_compile:
  domain (fromAList (compile code)) = domain (fromAList code)
Proof
  fs [EXTENSION]
  \\ fs [domain_lookup,lookup_fromAList,compile_def,alistTheory.ALOOKUP_MAP]
  \\ fs [ALOOKUP_toAList]
QED

Theorem lookup_collect_info:
  !xs n rest.
    ALL_DISTINCT (MAP FST xs) ==>
    lookup n (collect_info xs rest) =
      case ALOOKUP xs n of
      | NONE => lookup n rest
      | SOME body => lookup n (collect_info [(n,body)] rest)
Proof
  Induct \\ fs [collect_info_def,FORALL_PROD]
  \\ rpt gen_tac \\ strip_tac
  \\ Cases_on `n = p_1` THEN1
   (rveq \\ fs [] \\ TOP_CASE_TAC \\ fs []
    \\ imp_res_tac ALOOKUP_MEM \\ fs [MEM_MAP,FORALL_PROD]
    \\ rfs [])
  \\ fs [] \\ CASE_TAC \\ fs []
  \\ fs [lookup_insert]
  \\ CASE_TAC \\ CASE_TAC \\ fs [lookup_insert]
QED

Theorem state_ok_collect_info:
  ALL_DISTINCT (MAP FST code) ==>
  state_ok (collect_info code LN) (fromAList code)
Proof
  fs [state_ok_def] \\ strip_tac
  \\ drule lookup_collect_info
  \\ fs [lookup_def] \\ disch_then kall_tac
  \\ fs [CaseEq"option",ALOOKUP_toAList]
  \\ fs [collect_info_def] \\ rw []
  \\ every_case_tac \\ fs [lookup_def]
  \\ fs [seq_stack_alloc_def,AllCaseEqs()]
  \\ fs [lookup_fromAList]
QED

Theorem compile_semantics:
   ALL_DISTINCT (MAP FST code) ∧ s.use_stack ∧
   s.code = fromAList code ∧
   semantics start s <> Fail
   ==>
   semantics start (s with code := fromAList (stack_rawcall$compile code)) =
   semantics start s
Proof
  simp[GSYM AND_IMP_INTRO] >> ntac 3 strip_tac >>
  simp[semantics_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  DEEP_INTRO_TAC some_intro >> full_simp_tac(srw_ss())[] >>
  conj_tac >- (
    gen_tac >> ntac 2 strip_tac >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
      first_x_assum(qspec_then`k'`mp_tac)>>simp[]>>
      (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >>
      simp[] >>
      qmatch_assum_rename_tac`_ = (res,_)` >>
      Cases_on`res=SOME Error`>>simp[]>>
      drule comp_correct >>
      fs [comp_top_def] >> simp [Once comp_def] >>
      simp [Once state_rel_def,PULL_EXISTS] >>
      disch_then (qspec_then `collect_info code LN` mp_tac) >>
      disch_then (qspec_then `fromAList (compile code)` mp_tac) >>
      impl_tac >-
       (simp [domain_fromAList_compile]
        \\ conj_asm1_tac \\ simp [state_ok_collect_info]
        \\ rw [] \\ asm_exists_tac \\ simp []
        \\ simp [compile_def,lookup_fromAList,ALOOKUP_MAP]
        \\ fs [ALOOKUP_toAList,lookup_fromAList]) >>
      strip_tac >>
      qpat_x_assum`_ ≠ SOME TimeOut`mp_tac >>
      (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >>
      strip_tac >>
      drule (Q.GEN`extra`evaluate_add_clock) >>
      disch_then(qspec_then`ck`mp_tac) >> full_simp_tac(srw_ss())[] >>
      fs[]) >>
    DEEP_INTRO_TAC some_intro >> full_simp_tac(srw_ss())[] >>
    conj_tac >- (
      srw_tac[][] >>
      Cases_on`r=TimeOut`>>full_simp_tac(srw_ss())[]>>
      qpat_x_assum `evaluate _ = (SOME r, t)` assume_tac >>
      drule comp_correct >>
      fs [comp_top_def] >> simp [Once comp_def] >>
      simp [Once state_rel_def,PULL_EXISTS] >>
      disch_then (qspec_then `collect_info code LN` mp_tac) >>
      disch_then (qspec_then `fromAList (compile code)` mp_tac) >>
      impl_tac >-
       (conj_tac THEN1 (strip_tac \\ fs [])
        \\ simp [domain_fromAList_compile]
        \\ conj_asm1_tac \\ simp [state_ok_collect_info]
        \\ rw [] \\ asm_exists_tac \\ simp []
        \\ simp [compile_def,lookup_fromAList,ALOOKUP_MAP]
        \\ fs [ALOOKUP_toAList,lookup_fromAList]) >>
      strip_tac >>
      old_dxrule(GEN_ALL evaluate_add_clock) >>
      disch_then(qspec_then `k'` mp_tac) >>
      impl_tac >- (CCONTR_TAC >> fs[]) >> simp [] >>
      dxrule evaluate_add_clock >>
      dxrule evaluate_add_clock >>
      disch_then(qspec_then `ck + k` mp_tac) >>
      impl_tac >- (CCONTR_TAC >> fs[]) >> simp [] >>
      rpt (disch_then assume_tac) >>
      fs[state_component_equality] >>
      rveq >> rpt(PURE_FULL_CASE_TAC >> fs[]) >>
      fs [state_rel_thm]) >>
    drule comp_correct >>
    fs [comp_top_def] >> simp [Once comp_def] >>
    simp [Once state_rel_def,PULL_EXISTS] >>
    disch_then (qspec_then `collect_info code LN` mp_tac) >>
    disch_then (qspec_then `fromAList (compile code)` mp_tac) >>
    impl_tac >-
     (conj_tac THEN1 (strip_tac \\ fs [])
      \\ simp [domain_fromAList_compile]
      \\ conj_asm1_tac \\ simp [state_ok_collect_info]
      \\ rw [] \\ asm_exists_tac \\ simp []
      \\ simp [compile_def,lookup_fromAList,ALOOKUP_MAP]
      \\ fs [ALOOKUP_toAList,lookup_fromAList]) >>
    strip_tac >>
    asm_exists_tac >> simp[] >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[]) >>
  strip_tac >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
    first_x_assum(qspec_then`k`mp_tac)>>simp[]>>
    first_x_assum(qspec_then`k`mp_tac)>>
    (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >>
    simp[] >> strip_tac >> fs[] >>
    drule comp_correct >>
    fs [comp_top_def] >> simp [Once comp_def] >>
    simp [Once state_rel_def,PULL_EXISTS] >>
    qexists_tac `collect_info code LN` >>
    qexists_tac `fromAList (compile code)` >>
    simp [domain_fromAList_compile] >>
    conj_asm1_tac \\ simp [state_ok_collect_info] >>
    conj_tac THEN1
     (rw [] \\ asm_exists_tac \\ fs []
      \\ simp [compile_def,lookup_fromAList,ALOOKUP_MAP]
      \\ fs [ALOOKUP_toAList,lookup_fromAList]) >>
    srw_tac[][] >>
    qpat_x_assum`_ ≠ SOME TimeOut`mp_tac >>
    (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >> srw_tac[][] >>
    drule (GEN_ALL evaluate_add_clock) >>
    disch_then(qspec_then`ck`mp_tac)>>simp[]) >>
  DEEP_INTRO_TAC some_intro >> full_simp_tac(srw_ss())[] >>
  conj_tac >- (
    srw_tac[][] >>
    qpat_x_assum`∀k t. _`(qspec_then`k`mp_tac) >>
    (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >>
    simp[] >>
    last_x_assum mp_tac >>
    last_x_assum mp_tac >>
    last_x_assum mp_tac >>
    last_x_assum mp_tac >>
    last_x_assum(qspec_then`k`mp_tac) >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    `q <> SOME Error` by
      (strip_tac \\ first_x_assum (qspec_then `k` mp_tac) \\ fs []) >>
    drule comp_correct >>
    fs [comp_top_def] >> simp [Once comp_def] >>
    simp [Once state_rel_def,PULL_EXISTS] >>
    disch_then (qspec_then `collect_info code LN` mp_tac) >>
    disch_then (qspec_then `fromAList (compile code)` mp_tac) >>
    (impl_tac >-
     (simp [domain_fromAList_compile]
      \\ conj_asm1_tac \\ simp [state_ok_collect_info]
      \\ rw [] \\ asm_exists_tac \\ simp []
      \\ simp [compile_def,lookup_fromAList,ALOOKUP_MAP]
      \\ fs [ALOOKUP_toAList,lookup_fromAList])) >>
    rveq \\ fs [] >>
    strip_tac >> pop_assum mp_tac >> pop_assum mp_tac >>
    last_x_assum assume_tac >>
    drule (GEN_ALL evaluate_add_clock) >>
    disch_then(qspec_then`ck`mp_tac)>>simp[] >>
    rpt strip_tac >> rveq \\ fs []) >>
  srw_tac[][] >>
  qmatch_abbrev_tac`build_lprefix_lub l1 = build_lprefix_lub l2` >>
  `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
    suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_new_chain,unique_lprefix_lub] >>
  conj_asm1_tac >- (
    UNABBREV_ALL_TAC >>
    conj_tac >>
    Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
    REWRITE_TAC[IMAGE_COMPOSE] >>
    match_mp_tac prefix_chain_lprefix_chain >>
    simp[prefix_chain_def,PULL_EXISTS] >>
    qx_genl_tac[`k1`,`k2`] >>
    qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
    match_mp_tac(PROVE[]``((a ⇒ c) ∧ (b ⇒ d)) ⇒ (a ∨ b ⇒ c ∨ d)``) \\
    simp[LESS_EQ_EXISTS] \\
    conj_tac \\ strip_tac \\ rveq \\
    qmatch_goalsub_abbrev_tac`e,ss` \\
    Q.ISPECL_THEN[`p`,`e`,`ss`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono) \\
    simp[Abbr`ss`]) >>
  simp[equiv_lprefix_chain_thm] >>
  unabbrev_all_tac >> simp[PULL_EXISTS] >>
  ntac 2 (pop_assum kall_tac) >>
  simp[LNTH_fromList,PULL_EXISTS] >>
  simp[GSYM FORALL_AND_THM] >>
  rpt gen_tac >>
  (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >> full_simp_tac(srw_ss())[] >>
  (fn g => subterm (fn tm => Cases_on`^(assert (fn tm => has_pair_type tm andalso free_in tm (#2 g)) tm)`) (#2 g) g) >> full_simp_tac(srw_ss())[] >>
  `q' <> SOME Error` by
    (last_x_assum (qspec_then `k` mp_tac) \\ fs [] \\ rw [] \\ fs []) >>
  drule comp_correct >>
  fs [comp_top_def] >> simp [Once comp_def] >>
  simp [Once state_rel_def,PULL_EXISTS] >>
  disch_then (qspec_then `collect_info code LN` mp_tac) >>
  disch_then (qspec_then `fromAList (compile code)` mp_tac) >>
  impl_tac >-
   (simp [domain_fromAList_compile]
    \\ conj_asm1_tac \\ simp [state_ok_collect_info]
    \\ rw [] \\ asm_exists_tac \\ simp []
    \\ simp [compile_def,lookup_fromAList,ALOOKUP_MAP]
    \\ fs [ALOOKUP_toAList,lookup_fromAList]) >>
  strip_tac >>
  reverse conj_tac >- (
    fs [state_rel_thm] >>
    srw_tac[][] >>
    qexists_tac`ck+k`>>simp[] ) >>
  srw_tac[][] >>
  qexists_tac`k`>>simp[] >>
  ntac 2 (qhdtm_x_assum`evaluate`mp_tac) >>
  qmatch_assum_abbrev_tac`evaluate (e,ss) = _` >>
  fs [state_rel_thm] >>
  Q.ISPECL_THEN[`ck`,`e`,`ss`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono)>>
  simp[Abbr`ss`] >>
  ntac 3 strip_tac >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[IS_PREFIX_APPEND] >>
  simp[EL_APPEND1] >> rfs [] >> simp[EL_APPEND1]
QED

Theorem extract_labels_comp:
  !i p.
    extract_labels (comp i p) = extract_labels p /\
    extract_labels (comp_top i p) = extract_labels p
Proof
  recInduct comp_ind \\ rpt gen_tac \\ strip_tac
  \\ Cases_on `p` \\ fs [] \\ simp [comp_top_def]
  \\ simp [Once comp_def]
  \\ TRY (fs [extract_labels_def] \\ NO_TAC)
  THEN1 (every_case_tac \\ fs [extract_labels_def])
  \\ reverse conj_asm2_tac THEN1 fs [extract_labels_def]
  \\ rename [`comp_seq p1 p2`]
  \\ Cases_on `comp_seq p1 p2 i (Seq (comp i p1) (comp i p2)) =
               Seq (comp i p1) (comp i p2)` \\ simp []
  \\ drule comp_seq_neq_IMP \\ strip_tac \\ rveq \\ fs []
  \\ fs [comp_seq_def,dest_case_def,CaseEq"option",CaseEq"bool"]
  \\ Cases_on `lookup dest i` \\ fs []  \\ rw []
  \\ fs [extract_labels_def]
QED

Theorem stack_asm_name_comp:
  !i p.
    (stack_asm_name c (comp i p) = stack_asm_name c p /\
     stack_asm_name c (comp_top i p) = stack_asm_name c p) /\
    (stack_asm_remove c (comp i p) = stack_asm_remove c p /\
     stack_asm_remove c (comp_top i p) = stack_asm_remove c p)
Proof
  recInduct comp_ind \\ rpt gen_tac \\ strip_tac
  \\ strip_tac
  \\ Cases_on `p` \\ fs [] \\ simp [comp_top_def]
  \\ simp [Once comp_def]
  \\ TRY (fs [stack_asm_name_def] \\ NO_TAC)
  \\ TRY (fs [stack_asm_remove_def] \\ NO_TAC)
  \\ TRY (every_case_tac \\ fs [stack_asm_name_def,stack_asm_remove_def] \\ NO_TAC)
  \\ (reverse conj_asm2_tac THEN1 fs [stack_asm_name_def,stack_asm_remove_def])
  \\ rename [`comp_seq p1 p2`]
  \\ Cases_on `comp_seq p1 p2 i (Seq (comp i p1) (comp i p2)) =
               Seq (comp i p1) (comp i p2)` \\ simp []
  \\ drule comp_seq_neq_IMP \\ strip_tac \\ rveq \\ fs []
  \\ fs [comp_seq_def,dest_case_def,CaseEq"option",CaseEq"bool"]
  \\ Cases_on `lookup dest i` \\ fs []  \\ rw []
  \\ fs [stack_asm_name_def,stack_asm_remove_def]
QED

Theorem stack_alloc_stack_asm_convs:
  EVERY (λ(n,p). stack_asm_name c p) (compile prog) =
  EVERY (λ(n,p). stack_asm_name c p) prog ∧
  EVERY (λ(n,p). stack_asm_remove c p) (compile prog) =
  EVERY (λ(n,p). stack_asm_remove c p) prog
Proof
  fs [compile_def] \\ rename [`comp_top i`]
  \\ Induct_on `prog` \\ fs [FORALL_PROD,stack_asm_name_comp]
QED

Theorem reg_bound_comp:
  !i p.
    reg_bound (comp i p) s = reg_bound p s /\
    reg_bound (comp_top i p) s = reg_bound p s
Proof
  recInduct comp_ind \\ rpt gen_tac \\ strip_tac
  \\ Cases_on `p` \\ fs [] \\ simp [comp_top_def]
  \\ simp [Once comp_def]
  \\ TRY (fs [reg_bound_def] \\ NO_TAC)
  THEN1 (every_case_tac \\ fs [reg_bound_def])
  \\ reverse conj_asm2_tac THEN1 fs [reg_bound_def]
  \\ rename [`comp_seq p1 p2`]
  \\ Cases_on `comp_seq p1 p2 i (Seq (comp i p1) (comp i p2)) =
               Seq (comp i p1) (comp i p2)` \\ simp []
  \\ drule comp_seq_neq_IMP \\ strip_tac \\ rveq \\ fs []
  \\ fs [comp_seq_def,dest_case_def,CaseEq"option",CaseEq"bool"]
  \\ Cases_on `lookup dest i` \\ fs []  \\ rw []
  \\ fs [reg_bound_def]
QED

Theorem stack_rawcall_reg_bound:
  EVERY (\p. reg_bound p sp) (MAP SND (compile prog1)) =
  EVERY (\p. reg_bound p sp) (MAP SND prog1)
Proof
  fs [compile_def] \\ rename [`comp_top i`]
  \\ Induct_on `prog1` \\ fs [FORALL_PROD,reg_bound_comp]
QED

Theorem call_args_comp:
  !i p.
    call_args (comp i p) r1 r2 r3 r4 r5 = call_args p r1 r2 r3 r4 r5 /\
    call_args (comp_top i p) r1 r2 r3 r4 r5 = call_args p r1 r2 r3 r4 r5
Proof
  recInduct comp_ind \\ rpt gen_tac \\ strip_tac
  \\ Cases_on `p` \\ fs [] \\ simp [comp_top_def]
  \\ simp [Once comp_def]
  \\ TRY (fs [call_args_def] \\ NO_TAC)
  THEN1 (every_case_tac \\ fs [call_args_def])
  \\ reverse conj_asm2_tac THEN1 fs [call_args_def]
  \\ rename [`comp_seq p1 p2`]
  \\ Cases_on `comp_seq p1 p2 i (Seq (comp i p1) (comp i p2)) =
               Seq (comp i p1) (comp i p2)` \\ simp []
  \\ drule comp_seq_neq_IMP \\ strip_tac \\ rveq \\ fs []
  \\ fs [comp_seq_def,dest_case_def,CaseEq"option",CaseEq"bool"]
  \\ Cases_on `lookup dest i` \\ fs []  \\ rw []
  \\ simp [call_args_def]
QED

Theorem stack_alloc_call_args:
   EVERY (λp. call_args p 1 2 3 4 0) (MAP SND (compile prog1)) =
   EVERY (λp. call_args p 1 2 3 4 0) (MAP SND prog1)
Proof
  fs [compile_def] \\ rename [`comp_top i`]
  \\ Induct_on `prog1` \\ fs [FORALL_PROD,call_args_comp]
QED

Theorem MAP_FST_compile:
  MAP FST (compile code) = MAP FST code
Proof
  fs [compile_def,MAP_MAP_o,o_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs []
QED

Theorem call_arg_comp:
  !i p.
    alloc_arg (comp i p) = alloc_arg p /\
    alloc_arg (comp_top i p) = alloc_arg p
Proof
  recInduct comp_ind \\ rpt gen_tac \\ strip_tac
  \\ Cases_on `p` \\ fs [] \\ simp [comp_top_def]
  \\ simp [Once comp_def]
  \\ TRY (fs [alloc_arg_def] \\ NO_TAC)
  THEN1 (every_case_tac \\ fs [alloc_arg_def])
  \\ reverse conj_asm2_tac THEN1 fs [alloc_arg_def]
  \\ rename [`comp_seq p1 p2`]
  \\ Cases_on `comp_seq p1 p2 i (Seq (comp i p1) (comp i p2)) =
               Seq (comp i p1) (comp i p2)` \\ simp []
  \\ drule comp_seq_neq_IMP \\ strip_tac \\ rveq \\ fs []
  \\ fs [comp_seq_def,dest_case_def,CaseEq"option",CaseEq"bool"]
  \\ Cases_on `lookup dest i` \\ fs []  \\ rw []
  \\ simp [alloc_arg_def]
QED

Theorem stack_get_handler_labels_comp:
  !i p k.
    stack_get_handler_labels k (stack_rawcall$comp i p) =
    stack_get_handler_labels k p /\
    stack_get_handler_labels k (comp_top i p) =
    stack_get_handler_labels k p
Proof
  recInduct comp_ind \\ rpt gen_tac \\ strip_tac
  \\ Cases_on `p` \\ fs [] \\ simp [comp_top_def]
  \\ simp [Once comp_def]
  \\ TRY (fs [stack_get_handler_labels_def] \\ NO_TAC)
  THEN1 (every_case_tac \\ fs [stack_get_handler_labels_def])
  \\ gen_tac
  \\ rename [`comp_seq p1 p2`]
  \\ Cases_on `comp_seq p1 p2 i (Seq (comp i p1) (comp i p2)) =
               Seq (comp i p1) (comp i p2)` \\ simp []
  \\ drule comp_seq_neq_IMP \\ strip_tac \\ rveq \\ fs []
  \\ fs [comp_seq_def,dest_case_def,CaseEq"option",CaseEq"bool"]
  \\ Cases_on `lookup dest i` \\ fs []  \\ rw []
  \\ simp [stack_get_handler_labels_def]
QED

val _ = export_theory();
