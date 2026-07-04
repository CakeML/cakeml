(*
  Correctness proof for loop_live
*)
Theory loop_liveProof
Ancestors
  loopSem loopProps loop_live loop_callProof backend_common
  wordSem[qualified]
Libs
  preamble


val _ = temp_delsimps ["fromAList_def", "domain_union",
                       "domain_inter", "domain_difference",
                       "domain_map", "sptree.map_def", "sptree.lookup_rwts",
                       "sptree.insert_notEmpty", "sptree.isEmpty_union"];

Theorem compile_correct:
  ∀v v1 res s1 lt locals prog1 l1 l0.
    evaluate (v,v1) = (res,s1) ∧ res ≠ SOME Error ∧
    shrink lt v l0 = (prog1,l1) ∧ subspt (inter v1.locals l1) locals ⇒
    ∃new_locals.
      evaluate (prog1,v1 with locals := locals) =
      (res,s1 with locals := new_locals) ∧
      case res of
        NONE => subspt (inter s1.locals l0) new_locals
      | SOME (Result v5) => new_locals = s1.locals
      | SOME (Exception v6) => new_locals = s1.locals
      | SOME (Break n) => (case oEL n lt of
                           | SOME (_, brk) => subspt (inter s1.locals brk) new_locals
                           | NONE => T)
      | SOME (Continue n) => (case oEL n lt of
                              | SOME (cont, _) => subspt (inter s1.locals cont) new_locals
                              | NONE => T)
      | SOME TimeOut => new_locals = s1.locals
      | SOME (FinalFFI v7) => new_locals = s1.locals
      | SOME Error => new_locals = s1.locals
Proof
  recInduct loopSemTheory.evaluate_ind
  \\ rpt conj_tac
  >~ [`loopLang$Skip`] >- suspend "Skip"
  >~ [`loopLang$Fail`] >- suspend "Fail"
  >~ [`loopLang$Tick`] >- suspend "Tick"
  >~ [`loopLang$Continue _`] >- suspend "Continue"
  >~ [`loopLang$Break _`] >- suspend "Break"
  >~ [`loopLang$Mark`] >- suspend "Mark"
  >~ [`loopLang$Return`] >- suspend "Return"
  >~ [`loopLang$Raise`] >- suspend "Raise"
  >~ [`loopLang$Seq`] >- suspend "Seq"
  >~ [`loopLang$Loop`] >- suspend "Loop"
  >~ [`loopLang$Assign`] >- suspend "Assign"
  >~ [`loopLang$SetGlobal`] >- suspend "SetGlobal"
  >~ [`loopLang$LocValue`] >- suspend "LocValue"
  >~ [`loopLang$If`] >- suspend "If"
  >~ [`loopLang$Call`] >- suspend "Call"
  >~ [`loopLang$Store`] >- suspend "Store"
  >~ [`loopLang$Store32`] >- suspend "Store32"
  >~ [`loopLang$StoreByte`] >- suspend "StoreByte"
  >~ [`loopLang$Load32`] >- suspend "Load32"
  >~ [`loopLang$LoadByte`] >- suspend "LoadByte"
  >~ [`loopLang$FFI`] >- suspend "FFI"
  >~ [`loopLang$Arith`] >- suspend "Arith"
  >~ [`loopLang$ShMem`] >- suspend "ShMem"
  >~ [`loopLang$Primitive`] >- suspend "Primitive"
QED

Resume compile_correct[Skip]:
  fs [shrink_def,evaluate_def] \\ fs [CaseEq"bool"] \\ rw []
  \\ fs [dec_clock_def,state_component_equality]
QED

Resume compile_correct[Fail]:
  fs [shrink_def,evaluate_def] \\ fs [CaseEq"bool"] \\ rw []
  \\ fs [dec_clock_def,state_component_equality]
QED

Resume compile_correct[Tick]:
  fs [shrink_def,evaluate_def] \\ fs [CaseEq"bool"] \\ rw []
  \\ fs [dec_clock_def,state_component_equality]
QED

Resume compile_correct[Continue]:
  fs [shrink_def,evaluate_def]
  \\ rw [] \\ fs [state_component_equality]
  \\ CASE_TAC \\ fs []
  \\ rename1 ‘oEL _ _ = SOME x’
  \\ PairCases_on ‘x’ \\ fs []
QED

Resume compile_correct[Break]:
  fs [shrink_def,evaluate_def]
  \\ rw [] \\ fs [state_component_equality]
  \\ CASE_TAC \\ fs []
  \\ rename1 ‘oEL _ _ = SOME x’
  \\ PairCases_on ‘x’ \\ fs []
QED

Resume compile_correct[Mark]:
  fs [shrink_def,evaluate_def]
QED

Resume compile_correct[Return]:
  fs [shrink_def,evaluate_def,CaseEq"option"] \\ rw []
  \\ fs [call_env_def] \\ fs [state_component_equality]
  \\ fs [subspt_lookup,lookup_inter_alt,domain_list_insert]
  \\ rpt $ pop_assum mp_tac
  \\ qid_spec_tac ‘vs’
  \\ qid_spec_tac ‘ns’
  \\ Induct
  \\ gvs [get_vars_def,AllCaseEqs()] \\ rw []
QED

Resume compile_correct[Raise]:
  fs [shrink_def,evaluate_def,CaseEq"option"] \\ rw []
  \\ fs [call_env_def] \\ fs [state_component_equality]
  \\ fs [subspt_lookup,lookup_inter_alt]
QED

Resume compile_correct[Seq]:
  fs [shrink_def,evaluate_def,CaseEq"option"] \\ rw []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ rename [‘_ = (res7,s7)’]
  \\ reverse (Cases_on ‘res7’) \\ fs []
  THEN1
   (rveq \\ fs [] \\ first_x_assum drule
    \\ disch_then drule \\ fs [] \\ strip_tac \\ fs [evaluate_def]
    \\ rveq \\ fs [] \\ fs [state_component_equality])
  \\ first_x_assum drule
  \\ disch_then drule \\ fs [] \\ strip_tac \\ fs [evaluate_def]
QED

Theorem subspt_IMP_domain[local]:
  subspt l1 l2 ⇒ domain l1 SUBSET domain l2
Proof
  fs [subspt_def,SUBSET_DEF]
QED

Theorem subspt_inter_domain_cut[local]:
  ∀X m1 m2.
    domain X ⊆ domain m1 ∧ subspt (inter m1 X) m2 ⇒
    domain X ⊆ domain m2
Proof
  rw [SUBSET_DEF, domain_lookup, subspt_lookup, lookup_inter_alt]
  \\ res_tac \\ fs []
  \\ first_x_assum drule
  \\ disch_then (qspec_then ‘v’ mp_tac) \\ fs []
QED

Theorem subspt_inter_union_R[local]:
  ∀A B C D.
    subspt (inter A (union B C)) D ⇒ subspt (inter A C) D
Proof
  rw [subspt_lookup, lookup_inter_alt]
  \\ first_x_assum (qspec_then ‘x’ mp_tac)
  \\ disch_then (qspec_then ‘y’ mp_tac) \\ fs [domain_union]
QED

Resume compile_correct[Loop]:
  rpt gen_tac \\ disch_then assume_tac \\ fs [] \\ rpt gen_tac
  \\ once_rewrite_tac [evaluate_def]
  \\ once_rewrite_tac [shrink_def] \\ fs []
  \\ TOP_CASE_TAC
  \\ reverse (Cases_on ‘q’) \\ fs []
  >- ((* Loop_cut_fail: cut failed *)
      strip_tac
      \\ gvs [cut_res_def, cut_state_def, CaseEq"option", CaseEq"bool"]
      >- (Cases_on ‘shrink ((live_in,inter live_out l0)::lt) body
                           (union live_in (inter live_out l0))’
          \\ gvs []
          \\ once_rewrite_tac [evaluate_def]
          \\ gvs [cut_res_def, cut_state_def]
          \\ ‘domain l1 ⊆ domain locals’ by
             (irule subspt_inter_domain_cut
              \\ qexists_tac ‘s.locals’ \\ fs [])
          \\ gvs [])
      \\ Cases_on ‘v’ \\ gvs []
      \\ once_rewrite_tac [evaluate_def]
      \\ gvs [cut_res_def, cut_state_def]
      \\ ‘domain (inter live_in r) ⊆ domain locals’ by
         (irule subspt_inter_domain_cut
          \\ qexists_tac ‘s.locals’
          \\ fs [SUBSET_DEF, domain_inter])
      \\ gvs [])
  \\ fs [cut_res_def,cut_state_def,CaseEq"option",CaseEq"prod",CaseEq"bool",dec_clock_def]
  \\ Cases_on ‘evaluate (body,r)’ \\ fs []
  \\ Cases_on ‘q’
  >- ((* Loop_body_NONE: body returned NONE *)
      rpt strip_tac \\ gvs []
      >- ((* no_fix case *)
          Cases_on ‘shrink ((live_in, inter live_out l0)::lt) body
                           (union live_in (inter live_out l0))’
          \\ gvs []
          \\ once_rewrite_tac [loopSemTheory.evaluate_def]
          \\ gvs [loopSemTheory.cut_res_def, loopSemTheory.cut_state_def]
          \\ ‘domain l1 ⊆ domain locals’ by
             (irule subspt_inter_domain_cut
              \\ qexists_tac ‘s.locals’ \\ fs [])
          \\ gvs []
          \\ qpat_x_assum ‘shrink _ body _ = _’ mp_tac
          \\ disch_then assume_tac
          \\ first_assum (fn th => drule_then mp_tac th)
          \\ disch_then (qspec_then ‘inter locals l1’ mp_tac)
          \\ impl_tac
          >- (fs [subspt_lookup, lookup_inter_alt, CaseEq"option"]
              \\ rw [] \\ res_tac \\ gvs [])
          \\ strip_tac
          \\ fs [loopSemTheory.dec_clock_def]
          \\ qpat_x_assum ‘∀_ _ _ _ _. shrink _ (Loop _ _ _) _ = _ ∧ _ ⇒ _’
               (qspecl_then [‘lt’, ‘new_locals’,
                             ‘loopLang$Loop l1 q (inter live_out l0)’,
                             ‘l1’, ‘l0’] mp_tac)
          \\ impl_tac
          >- (once_rewrite_tac [loop_liveTheory.shrink_def] \\ fs []
              \\ fs [subspt_lookup, lookup_inter_alt, CaseEq"option", domain_union]
              \\ rw [] \\ res_tac \\ gvs [])
          \\ strip_tac
          \\ asm_exists_tac \\ fs [])
      \\ (* fix case *)
         drule fixedpoint_thm \\ strip_tac
      \\ once_rewrite_tac [loopSemTheory.evaluate_def]
      \\ gvs [loopSemTheory.cut_res_def, loopSemTheory.cut_state_def]
      \\ ‘domain (inter live_in v2) ⊆ domain locals’ by
         (irule subspt_inter_domain_cut
          \\ qexists_tac ‘s.locals’ \\ fs [SUBSET_DEF, domain_inter])
      \\ gvs []
      \\ qpat_x_assum ‘shrink _ body _ = _’ mp_tac
      \\ disch_then assume_tac
      \\ first_assum (fn th => drule_then mp_tac th)
      \\ disch_then (qspec_then ‘inter locals (inter live_in v2)’ mp_tac)
      \\ impl_tac
      >- (fs [subspt_lookup, lookup_inter_alt, CaseEq"option"]
          \\ rw [] \\ res_tac \\ gvs [domain_inter])
      \\ strip_tac
      \\ fs [loopSemTheory.dec_clock_def]
      \\ qpat_x_assum ‘∀_ _ _ _ _. shrink _ (Loop _ _ _) _ = _ ∧ _ ⇒ _’
           (qspecl_then [‘lt’, ‘new_locals’,
                         ‘loopLang$Loop (inter live_in v2) v1 (inter live_out l0)’,
                         ‘inter live_in v2’, ‘l0’] mp_tac)
      \\ impl_tac
      >- (once_rewrite_tac [loop_liveTheory.shrink_def] \\ fs []
          \\ fs [subspt_lookup, lookup_inter_alt, CaseEq"option", domain_union,
                 domain_inter]
          \\ rw [] \\ res_tac \\ gvs [])
      \\ strip_tac
      \\ asm_exists_tac \\ fs [])
  \\ fs [PULL_EXISTS]
  \\ reverse (Cases_on ‘fixedpoint lt live_in LN (union live_in (inter live_out l0)) body’) \\ fs []
  >- ((* Loop_fix *)
      rpt strip_tac
      \\ gvs []
      \\ ‘x ≠ Error’ by (Cases_on ‘x’ \\ gvs [])
      \\ drule fixedpoint_thm \\ strip_tac
      \\ once_rewrite_tac [evaluate_def]
      \\ gvs [cut_res_def, cut_state_def]
      \\ ‘domain (inter live_in v2) ⊆ domain locals’ by
         (irule subspt_inter_domain_cut
          \\ qexists_tac ‘s.locals’
          \\ fs [SUBSET_DEF, domain_inter])
      \\ gvs []
      \\ last_x_assum
           (qspecl_then [‘(inter live_in v2, union live_in (inter live_out l0))::lt’,
                         ‘inter locals (inter live_in v2)’,
                         ‘v1’, ‘v2’, ‘union live_in (inter live_out l0)’] mp_tac)
      \\ impl_tac
      >- (fs []
          \\ fs [subspt_lookup, lookup_inter_alt, CaseEq"option", domain_inter]
          \\ rw [] \\ res_tac \\ gvs [])
      \\ strip_tac
      \\ Cases_on ‘x’ \\ gvs [dec_clock_def, cut_res_def, cut_state_def]
      \\ Cases_on ‘n’ \\ gvs [oEL_def, LLOOKUP_def]
      >- ((* Loop_fix_Break_0 *)
          imp_res_tac subspt_inter_union_R
          \\ Cases_on ‘domain live_out ⊆ domain r'.locals’ \\ gvs []
          \\ ‘domain (inter live_out l0) ⊆ domain new_locals’ by
             (irule subspt_inter_domain_cut
              \\ qexists_tac ‘r'.locals’
              \\ fs [SUBSET_DEF, domain_inter])
          \\ gvs []
          \\ Cases_on ‘r'.clock = 0’ \\ gvs []
          \\ qexists_tac ‘inter new_locals (inter live_out l0)’
          \\ fs [loopSemTheory.state_component_equality]
          \\ fs [subspt_lookup, lookup_inter_alt, CaseEq"option"]
          \\ rw [] \\ res_tac \\ fs [domain_inter] \\ res_tac \\ fs [])
      >- (qexists_tac ‘new_locals’ \\ fs [])
      >- ((* Loop_fix_Continue_0 *)
          first_x_assum
            (qspecl_then [‘lt’, ‘new_locals’,
                          ‘Loop (inter live_in v2) v1 (inter live_out l0)’,
                          ‘inter live_in v2’, ‘l0’] mp_tac)
          \\ impl_tac
          >- (once_rewrite_tac [shrink_def] \\ fs [])
          \\ strip_tac \\ asm_exists_tac \\ fs [])
      >- (qexists_tac ‘new_locals’ \\ fs []))
  >- ((* Loop_no_fix *)
      rpt strip_tac
      \\ gvs []
      \\ Cases_on ‘shrink ((live_in,inter live_out l0)::lt) body
                           (union live_in (inter live_out l0))’
      \\ gvs []
      \\ ‘x ≠ Error’ by (Cases_on ‘x’ \\ gvs [])
      \\ once_rewrite_tac [evaluate_def]
      \\ gvs [cut_res_def, cut_state_def]
      \\ ‘domain l1 ⊆ domain locals’ by
         (irule subspt_inter_domain_cut
          \\ qexists_tac ‘s.locals’ \\ fs [])
      \\ gvs []
      \\ last_x_assum
           (qspecl_then [‘(l1,inter live_out l0)::lt’, ‘inter locals l1’,
                         ‘q’, ‘r’, ‘union l1 (inter live_out l0)’] mp_tac)
      \\ impl_tac
      >- (fs []
          \\ fs [subspt_lookup, lookup_inter_alt, CaseEq"option"]
          \\ rw [] \\ res_tac \\ gvs [])
      \\ strip_tac
      \\ Cases_on ‘x’ \\ gvs [dec_clock_def, cut_res_def, cut_state_def]
      \\ Cases_on ‘n’ \\ gvs [oEL_def, LLOOKUP_def]
      >- ((* Loop_no_fix_Break_0 *)
          Cases_on ‘domain live_out ⊆ domain r'.locals’ \\ gvs []
          \\ ‘domain (inter live_out l0) ⊆ domain new_locals’ by
             (irule subspt_inter_domain_cut
              \\ qexists_tac ‘r'.locals’
              \\ fs [SUBSET_DEF, domain_inter])
          \\ gvs []
          \\ Cases_on ‘r'.clock = 0’ \\ gvs []
          \\ qexists_tac ‘inter new_locals (inter live_out l0)’
          \\ fs [loopSemTheory.state_component_equality]
          \\ fs [subspt_lookup, lookup_inter_alt, CaseEq"option"]
          \\ rw [] \\ res_tac \\ fs [domain_inter] \\ res_tac \\ fs [])
      >- (qexists_tac ‘new_locals’ \\ fs [])
      >- ((* Loop_no_fix_Continue_0 *)
          first_x_assum
            (qspecl_then [‘lt’, ‘new_locals’, ‘Loop l1 q (inter live_out l0)’,
                          ‘l1’, ‘l0’] mp_tac)
          \\ impl_tac
          >- (once_rewrite_tac [shrink_def] \\ fs [])
          \\ strip_tac \\ asm_exists_tac \\ fs [])
      >- (qexists_tac ‘new_locals’ \\ fs []))
QED

Theorem vars_of_exp_acc:
  ∀(exp:'a loopLang$exp) l.
     domain (vars_of_exp exp l) =
     domain (union (vars_of_exp exp LN) l)
Proof
  qsuff_tac ‘
    (∀(exp:'a loopLang$exp) (l_unused:num_set).
       ∀l. domain (vars_of_exp exp l) =
           domain (union (vars_of_exp exp LN) l)) ∧
    (∀(exps:'a loopLang$exp list) (l_unused:num_set).
       ∀l. domain (vars_of_exp_list exps l) =
           domain (union (vars_of_exp_list exps LN) l))’
  THEN1 metis_tac []
  \\ ho_match_mp_tac vars_of_exp_ind
  \\ rpt conj_tac
  >- (* Var *) (rpt strip_tac \\ once_rewrite_tac [vars_of_exp_def]
                \\ fs [domain_union] \\ ASM_SET_TAC [])
  >- (* Const *) (rpt strip_tac \\ once_rewrite_tac [vars_of_exp_def]
                  \\ fs [domain_union])
  >- (* BaseAddr *) (rpt strip_tac \\ once_rewrite_tac [vars_of_exp_def]
                     \\ fs [domain_union])
  >- (* TopAddr *) (rpt strip_tac \\ once_rewrite_tac [vars_of_exp_def]
                    \\ fs [domain_union])
  >- (* Lookup *) (rpt strip_tac \\ once_rewrite_tac [vars_of_exp_def]
                   \\ fs [domain_union])
  >- (* Load *) (rpt strip_tac \\ once_rewrite_tac [vars_of_exp_def]
                 \\ metis_tac [])
  >- (* Op *) (rpt strip_tac \\ once_rewrite_tac [vars_of_exp_def]
               \\ metis_tac [])
  >- (* Shift *) (rpt strip_tac \\ once_rewrite_tac [vars_of_exp_def]
                  \\ metis_tac [])
  >- suspend "list_case"
QED

Resume vars_of_exp_acc[list_case]:
  rpt strip_tac \\ once_rewrite_tac [vars_of_exp_def]
  \\ Cases_on ‘exps’
  >- (rewrite_tac [listTheory.list_case_def] \\ BETA_TAC
      \\ rewrite_tac [sptreeTheory.union_LN])
  \\ rewrite_tac [listTheory.list_case_def] \\ BETA_TAC
  \\ qpat_x_assum ‘∀exp xs'. _’ (qspecl_then [‘h’, ‘t’] mp_tac)
  \\ impl_tac >- simp []
  \\ strip_tac
  \\ qpat_x_assum ‘∀x exps'. _’ (qspecl_then [‘h’, ‘t’] mp_tac)
  \\ impl_tac >- simp []
  \\ strip_tac
  \\ qpat_x_assum ‘∀l. domain (vars_of_exp h l) = _’ (fn th =>
       assume_tac (Q.SPEC ‘vars_of_exp_list t l’ th) \\
       assume_tac (Q.SPEC ‘vars_of_exp_list t LN’ th))
  \\ first_x_assum (qspec_then ‘l’ assume_tac)
  \\ pop_assum mp_tac \\ pop_assum mp_tac \\ pop_assum mp_tac
  \\ rewrite_tac [domain_union]
  \\ ASM_SET_TAC []
QED

Finalise vars_of_exp_acc;

Theorem vars_of_exp_mono:
  ∀exp l. subspt l (vars_of_exp exp l)
Proof
  qsuff_tac ‘
   (∀(exp:'a loopLang$exp) (l:num_set).
      subspt l (vars_of_exp exp l)) ∧
   (∀(exp:'a loopLang$exp list) (l:num_set).
      subspt l (vars_of_exp_list exp l))’ THEN1 metis_tac []
  \\ ho_match_mp_tac vars_of_exp_ind \\ rw []
  \\ once_rewrite_tac [vars_of_exp_def] >>
  fs [pan_commonPropsTheory.subspt_insert]>>
  Cases_on ‘exp’ \\ fs []>>
  irule subspt_trans>>
  metis_tac[]
QED

Theorem eval_lemma':
  ∀s exp w l.
    eval s exp = SOME w ∧
    subspt s.locals locals ⇒
    eval (s with locals := locals) exp = SOME w
Proof
  ho_match_mp_tac eval_ind \\ rw [] \\ fs [eval_def]
  >- fs[subspt_lookup]
  >- (every_case_tac>>fs[mem_load_def])
  >- (fs [CaseEq"option",CaseEq"word_loc"] \\ rveq
      \\ goal_assum (first_assum o mp_then Any mp_tac)
      \\ pop_assum mp_tac
      \\ pop_assum kall_tac
      \\ pop_assum mp_tac
      \\ qid_spec_tac ‘ws’
      \\ Induct_on ‘wexps’ \\ fs [] \\ rw []>>
      fs[wordSemTheory.the_words_def]>>
      every_case_tac>>fs[]
      >- (first_x_assum $ qspec_then ‘h’ assume_tac>>fs[]>>
          first_x_assum $ qspec_then ‘Word c’ assume_tac>>fs[])
      >- (first_x_assum $ qspec_then ‘h’ assume_tac>>fs[]>>
          first_x_assum $ qspec_then ‘Word c'’ assume_tac>>gvs[])>>
      first_x_assum $ qspec_then ‘h’ assume_tac>>fs[]>>
      first_x_assum $ qspec_then ‘Word c’ assume_tac>>fs[])>>
  every_case_tac>>fs[]
QED

Theorem eval_lemma:
  ∀s exp w l.
    eval s exp = SOME w ∧
    subspt (inter s.locals (vars_of_exp exp l)) locals ⇒
    eval (s with locals := locals) exp = SOME w
Proof
  ho_match_mp_tac eval_ind \\ rw [] \\ fs [eval_def]
  THEN1 fs [vars_of_exp_def,subspt_lookup,lookup_inter_alt]
  THEN1
   (fs [CaseEq"option",CaseEq"word_loc",vars_of_exp_def,PULL_EXISTS] \\ rveq
    \\ res_tac \\ fs[] \\ fs [mem_load_def])
  THEN1
   (fs [CaseEq"option",CaseEq"word_loc"] \\ rveq
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ pop_assum mp_tac
    \\ once_rewrite_tac [vars_of_exp_def]
    \\ pop_assum kall_tac
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘ws’
    \\ Induct_on ‘wexps’ \\ fs [] \\ rw []
    \\ fs [wordSemTheory.the_words_def,CaseEq"option",CaseEq"word_loc",PULL_EXISTS]
    \\ rveq \\ fs [] \\ conj_tac
    \\ fs [PULL_FORALL,AND_IMP_INTRO]
    \\ first_x_assum match_mp_tac
    THEN1 (fs [Once vars_of_exp_def] \\ metis_tac [])
    \\ pop_assum mp_tac \\ simp [Once vars_of_exp_def]
    \\ rw [] THEN1 metis_tac []
    \\ fs [subspt_lookup,lookup_inter_alt]
    \\ pop_assum mp_tac
    \\ once_rewrite_tac [vars_of_exp_acc]
    \\ fs [domain_union])
  THEN1
   (fs [CaseEq"option",CaseEq"word_loc",vars_of_exp_def,PULL_EXISTS] \\ rveq
    \\ res_tac \\ fs[] \\ fs [mem_load_def])
QED

Resume compile_correct[Assign]:
  rw [shrink_def,CaseEq"option"] \\ rveq \\ fs []
  THEN1
   (fs [evaluate_def,state_component_equality,CaseEq"option",set_var_def]
    \\ rveq \\ fs [] \\ fs [subspt_lookup,lookup_inter,CaseEq"option"]
    \\ rw [] \\ res_tac
    \\ qpat_x_assum ‘insert _ _ _ = _’ (assume_tac o GSYM)
    \\ fs [lookup_insert,CaseEq"bool"] \\ rveq \\ fs [])
  \\ fs [evaluate_def,CaseEq"option"] \\ rveq \\ fs []
  \\ fs [state_component_equality,set_var_def,PULL_EXISTS]
  \\ qexists_tac ‘w’ \\ fs []
  \\ reverse conj_tac THEN1
   (pop_assum mp_tac
    \\ fs [subspt_lookup,lookup_inter_alt]
    \\ fs [lookup_insert]
    \\ once_rewrite_tac [vars_of_exp_acc] \\ fs [domain_union]
    \\ metis_tac [])
  \\ drule eval_lemma
  \\ disch_then drule \\ fs []
QED

Resume compile_correct[SetGlobal]:
  rw [shrink_def,CaseEq"option"] \\ rveq \\ fs []
  \\ fs [evaluate_def,CaseEq"option"] \\ rveq \\ fs [PULL_EXISTS,set_globals_def]
  \\ fs [state_component_equality]
  \\ drule eval_lemma \\ disch_then drule \\ fs []
  \\ fs [subspt_lookup,lookup_inter_alt]
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [vars_of_exp_acc] \\ fs [domain_union]
QED

Resume compile_correct[LocValue]:
  rw [shrink_def,CaseEq"option"] \\ rveq \\ fs []
  THEN1
   (fs [evaluate_def,CaseEq"bool"] \\ rveq \\ fs [set_var_def]
    \\ fs [state_component_equality]
    \\ ‘~(r IN domain l0)’ by fs [domain_lookup]
    \\ fs [subspt_lookup,lookup_inter_alt,lookup_insert]
    \\ rw [] \\ fs [])
  \\ fs [evaluate_def,CaseEq"bool"] \\ rveq \\ fs [set_var_def]
  \\ fs [state_component_equality]
  \\ fs [subspt_lookup,lookup_inter_alt,lookup_insert] \\ rw []
QED

Resume compile_correct[If]:
  fs [evaluate_def,CaseEq"option",CaseEq"word_loc",PULL_EXISTS]
  \\ rpt strip_tac \\ fs [] \\ rveq \\ fs []
  \\ Cases_on ‘evaluate (if word_cmp cmp x y then c1 else c2,s)’ \\ fs []
  \\ Cases_on ‘q = SOME Error’ THEN1 fs [cut_res_def] \\ fs []
  \\ fs [shrink_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ fs [evaluate_def]
  \\ ‘lookup r1 locals = SOME (Word x) ∧
      get_var_imm ri (s with locals := locals) = SOME (Word y)’ by
     (Cases_on ‘ri’ \\ fs [subspt_lookup,lookup_inter_alt,domain_union]
      \\ fs [get_var_imm_def])
  \\ fs [] \\ IF_CASES_TAC \\ fs []
  \\ first_x_assum drule
  \\ disch_then (qspec_then ‘locals’ mp_tac)
  \\ (impl_tac THEN1 fs [subspt_lookup,lookup_inter_alt,domain_union])
  \\ strip_tac \\ fs []
  \\ (reverse (Cases_on ‘q’) \\ fs [cut_res_def]
  THEN1 (Cases_on ‘x'’ \\ fs [] \\ rveq \\ fs [] \\ fs [state_component_equality]))
  \\ fs [cut_state_def,CaseEq"option",CaseEq"bool"]
  \\ rveq \\ fs [] \\ fs [state_component_equality,domain_inter]
  \\ imp_res_tac subspt_IMP_domain
  \\ fs [domain_inter,domain_insert,domain_union,SUBSET_DEF]
  \\ fs [dec_clock_def]
  \\ fs [subspt_lookup,lookup_inter_alt,domain_inter]
QED

Theorem domain_list_delete[simp]:
  ∀vs s. domain (list_delete vs s) = domain s DIFF set vs
Proof
  Induct \\ gvs [list_delete_def] \\ rw [EXTENSION] \\ metis_tac []
QED

Resume compile_correct[Call]:
  rw [] \\ fs [evaluate_def]
  \\ Cases_on ‘get_vars argvars s’ \\ fs []
  \\ Cases_on ‘find_code dest x s.code’ \\ fs []
  \\ rename [‘_ = SOME y’] \\ PairCases_on ‘y’ \\ fs []
  \\ ‘set argvars SUBSET domain l1’ by
   (Cases_on ‘ret’ \\ Cases_on ‘handler’ \\ fs [shrink_def,CaseEq"prod"]
    \\ rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs [domain_union,domain_fromAList,MAP_MAP_o,o_DEF,SUBSET_DEF])
  \\ ‘get_vars argvars (s with locals := locals) = SOME x’ by
    (pop_assum mp_tac \\ pop_assum kall_tac
     \\ ntac 2 (pop_assum mp_tac)
     \\ qid_spec_tac ‘x’
     \\ qid_spec_tac ‘argvars’ \\ rpt (pop_assum kall_tac)
     \\ Induct
     \\ fs [get_vars_def,CaseEq"option",PULL_EXISTS,PULL_FORALL]
     \\ rw [] \\ fs [subspt_lookup,lookup_inter_alt])
  \\ Cases_on ‘ret’ \\ fs []
  THEN1
   (Cases_on ‘handler’ \\ fs []
    \\ fs [shrink_def] \\ rveq \\ fs []
    \\ fs [evaluate_def]
    \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
    \\ fs [dec_clock_def] \\ fs [state_component_equality]
    \\ Cases_on ‘res’ \\ fs [] \\ fs [subspt_lookup,lookup_inter_alt]
    \\ Cases_on ‘x'’ \\ fs [] \\ rpt CASE_TAC \\ fs [subspt_lookup,lookup_inter_alt])
  \\ rename [‘Call (SOME z)’] \\ PairCases_on ‘z’ \\ fs []
  \\ Cases_on ‘handler’ \\ fs [shrink_def] \\ rveq \\ fs []
  >- ((* no handler *)
      fs [evaluate_def,cut_res_def,cut_state_def]
      \\ Cases_on ‘domain z1 ⊆ domain s.locals’ \\ fs []
      \\ reverse IF_CASES_TAC \\ fs []
      \\ imp_res_tac subspt_IMP_domain
      \\ rfs [SUBSET_DEF, domain_inter, domain_union, domain_list_delete,
              domain_fromAList, MEM_MAP, EXISTS_PROD]
      \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs [dec_clock_def]
      \\ fs [CaseEq"prod",CaseEq"option"] \\ rveq \\ fs []
      \\ fs [CaseEq"loopSem$result"] \\ rveq \\ fs [set_var_def,set_vars_def]
      \\ fs [state_component_equality]
      \\ ‘LENGTH retvs = LENGTH z0’ by
           (CCONTR_TAC \\ fs [] \\ rveq \\ fs [])
      \\ fs [] \\ rveq \\ fs []
      \\ qexists_tac
           ‘alist_insert z0 retvs (inter locals (list_delete z0 (inter l0 z1)))’
      \\ fs [state_component_equality,subspt_lookup,
             lookup_inter_alt,lookup_alist_insert_any]
      \\ rw [] \\ Cases_on ‘ALOOKUP (ZIP (z0,retvs)) x'’ \\ fs []
      \\ ‘MAP FST (ZIP (z0,retvs)) = z0’ by fs [MAP_ZIP]
      \\ fs [ALOOKUP_NONE, domain_inter]
      \\ first_x_assum irule
      \\ fs [domain_union, domain_list_delete, domain_inter])
  \\ (* handler *)
  PairCases_on ‘x'’ \\ fs []
  \\ fs [evaluate_def,cut_res_def,cut_state_def]
  \\ Cases_on ‘domain z1 ⊆ domain s.locals’ \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ fs [evaluate_def,cut_res_def,cut_state_def]
  \\ reverse IF_CASES_TAC \\ fs []
  \\ imp_res_tac subspt_IMP_domain
  \\ rfs [SUBSET_DEF, domain_inter, domain_union, domain_list_delete,
          domain_delete, domain_fromAList, MEM_MAP, EXISTS_PROD]
  \\ ‘∀x. x ∈ domain z1 ∧
          (x ∈ domain l2 ∧ ¬MEM x z0 ∨ x ∈ domain l3 ∧ x ≠ x'0) ⇒
          x ∈ domain locals’ by metis_tac []
  \\ fs []
  \\ Cases_on ‘s.clock = 0’ \\ fs [] \\ rveq
  >- (fs [loopSemTheory.state_component_equality]
      \\ IF_CASES_TAC \\ fs []
      \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
  \\ fs [dec_clock_def,CaseEq"prod",CaseEq"option"] \\ rveq \\ fs []
  \\ Cases_on ‘v11’ \\ fs []
  \\ fs [set_var_def,set_vars_def]
  \\ rpt strip_tac \\ rveq \\ fs [state_component_equality]
  \\ rpt (qpat_x_assum ‘x' ∉ domain locals’ mp_tac \\ metis_tac [])
  >~ [‘evaluate (y1,_) = (SOME (loopSem$Result _),_)’] >-
   (Cases_on ‘LENGTH l ≠ LENGTH z0’ \\ fs [] \\ rveq \\ fs [state_component_equality]
    \\ qmatch_goalsub_abbrev_tac ‘evaluate (r',st1)’
    \\ Cases_on ‘evaluate (x'2,st with locals := alist_insert z0 l (inter s.locals z1))’
    \\ fs []
    \\ Cases_on ‘q = SOME Error’
    >- fs [cut_res_def]
    \\ fs []
    \\ first_x_assum drule
    \\ disch_then (qspec_then ‘st1.locals’ mp_tac)
    \\ impl_tac
    >- (fs [Abbr‘st1’,subspt_lookup,lookup_inter_alt,lookup_alist_insert_any]
        \\ ‘MAP FST (ZIP (z0,l)) = z0’ by fs [MAP_ZIP]
        \\ qx_genl_tac [‘k’,‘v’] \\ strip_tac
        \\ Cases_on ‘ALOOKUP (ZIP (z0,l)) k’ \\ fs []
        \\ ‘¬MEM k z0’ by gvs [ALOOKUP_NONE]
        \\ rw []
        \\ ‘k ∈ domain (inter z1 (union (list_delete z0 l2) (delete x'0 l3)))’ by
             fs [domain_inter,domain_union,domain_list_delete]
        \\ fs []
        \\ first_x_assum irule
        \\ fs [domain_union,domain_inter,domain_fromAList])
    \\ strip_tac \\ fs []
    \\ unabbrev_all_tac \\ fs []
    \\ reverse (Cases_on ‘q’) \\ fs []
    >- (Cases_on ‘x'’ \\ fs [cut_res_def,state_component_equality]
        \\ Cases_on ‘res’ \\ fs []
        \\ Cases_on ‘x'’ \\ fs []
        \\ rpt CASE_TAC \\ gvs [subspt_lookup])
    \\ fs [cut_res_def,cut_state_def,CaseEq"option",CaseEq"bool"]
    \\ fs [state_component_equality,domain_inter,domain_union,dec_clock_def]
    \\ fs [SUBSET_DEF] \\ rw []
    \\ rpt (qpat_x_assum ‘inter _ _ = _’ (assume_tac o GSYM)) \\ fs []
    \\ fs [subspt_lookup,lookup_inter_alt,domain_inter]
    \\ fs [domain_lookup] \\ res_tac \\ res_tac \\ fs [])
  \\ qmatch_goalsub_abbrev_tac ‘evaluate (h',st1)’
  \\ Cases_on ‘evaluate (x'1,st with locals := insert x'0 w (inter s.locals z1))’
  \\ fs []
  \\ Cases_on ‘q = SOME Error’
  >- fs [cut_res_def]
  \\ fs []
  \\ first_x_assum drule
  \\ disch_then (qspec_then ‘st1.locals’ mp_tac)
  \\ impl_tac
  >- (fs [Abbr‘st1’,subspt_lookup,lookup_inter_alt,lookup_insert,
          domain_union,domain_inter,domain_list_delete,domain_delete,
          domain_fromAList]
      \\ rw [] \\ fs [])
  \\ strip_tac \\ fs []
  \\ unabbrev_all_tac \\ fs []
  \\ reverse (Cases_on ‘q’) \\ fs []
  >- (Cases_on ‘x'’ \\ fs [cut_res_def,state_component_equality]
      \\ Cases_on ‘res’ \\ fs []
      \\ Cases_on ‘x'’ \\ fs []
      \\ rpt CASE_TAC \\ gvs [subspt_lookup])
  \\ fs [cut_res_def,cut_state_def,CaseEq"option",CaseEq"bool"]
  \\ fs [state_component_equality,domain_inter,domain_union,dec_clock_def]
  \\ fs [SUBSET_DEF] \\ rw []
  \\ rpt (qpat_x_assum ‘inter _ _ = _’ (assume_tac o GSYM)) \\ fs []
  \\ fs [subspt_lookup,lookup_inter_alt,domain_inter]
  \\ fs [domain_lookup] \\ res_tac \\ res_tac \\ fs []
QED

Resume compile_correct[Store]:
  rw [shrink_def] \\ rveq
  \\ fs [evaluate_def,CaseEq"option",CaseEq"word_loc"] \\ rveq \\ fs []
  \\ fs [PULL_EXISTS]
  \\ fs [mem_store_def] \\ rveq \\ fs []
  \\ simp [state_component_equality]
  \\ drule eval_lemma
  \\ disch_then drule \\ fs []
  \\ fs [subspt_lookup,lookup_inter_alt]
  \\ qpat_x_assum ‘∀x. _’ mp_tac
  \\ once_rewrite_tac [vars_of_exp_acc] \\ fs [domain_union]
  \\ strip_tac
  \\ ‘lookup v locals = SOME w’ by metis_tac [] \\ fs []
QED

Resume compile_correct[Store32]:
  rw [shrink_def] \\ rveq
  \\ fs [evaluate_def,CaseEq"option",CaseEq"word_loc"] \\ rveq \\ fs []
  \\ fs [PULL_EXISTS]
  \\ simp [state_component_equality,set_var_def]
  \\ fs [subspt_lookup,lookup_inter_alt,lookup_insert]
  \\ res_tac \\ fs [] \\ rw []
QED

Resume compile_correct[StoreByte]:
  rw [shrink_def] \\ rveq
  \\ fs [evaluate_def,CaseEq"option",CaseEq"word_loc"] \\ rveq \\ fs []
  \\ fs [PULL_EXISTS]
  \\ simp [state_component_equality,set_var_def]
  \\ fs [subspt_lookup,lookup_inter_alt,lookup_insert]
  \\ res_tac \\ fs [] \\ rw []
QED

Resume compile_correct[Load32]:
  rw [shrink_def] \\ rveq
  \\ fs [evaluate_def,CaseEq"option",CaseEq"word_loc"] \\ rveq \\ fs []
  \\ fs [PULL_EXISTS]
  \\ simp [state_component_equality,set_var_def]
  \\ fs [subspt_lookup,lookup_inter_alt,lookup_insert]
  \\ res_tac \\ fs [] \\ rw []
QED

Resume compile_correct[LoadByte]:
  rw [shrink_def] \\ rveq
  \\ fs [evaluate_def,CaseEq"option",CaseEq"word_loc"] \\ rveq \\ fs []
  \\ fs [PULL_EXISTS]
  \\ simp [state_component_equality,set_var_def]
  \\ fs [subspt_lookup,lookup_inter_alt,lookup_insert]
  \\ res_tac \\ fs [] \\ rw []
QED

Resume compile_correct[FFI]:
  fs [evaluate_def] \\ rw []
  \\ fs [CaseEq"option",CaseEq"word_loc"] \\ rveq \\ fs []
  \\ fs [shrink_def] \\ rveq \\ fs []
  \\ fs [subspt_lookup,evaluate_def,lookup_inter_alt,domain_insert,
         cut_state_def, domain_inter]
  \\ ‘domain cutset ∩ domain l0 ⊆ domain locals’ by (
    fs [SUBSET_DEF]
    \\ rw []
    \\ res_tac \\ fs []
    \\ fs [domain_lookup] \\ metis_tac [])
  \\ fs []
  \\ res_tac \\ fs [] \\ fs []
  \\ fs [CaseEq"ffi_result"]
  \\ simp [state_component_equality]
  \\ Cases_on ‘res’ \\ fs []
  \\ fs [SUBSET_DEF,call_env_def]
  \\ rveq \\ fs []
  \\ qexists_tac ‘inter locals (inter cutset l0)’
  \\ fs []
  \\ rw [lookup_inter, domain_lookup]
  \\ fs [CaseEq "option"]
  \\ res_tac \\ fs [domain_lookup]
QED

Resume compile_correct[Arith]:
  rpt strip_tac >>
  gvs[evaluate_def, DefnBase.one_line_ify NONE loop_arith_def,
      AllCaseEqs(),shrink_def,PULL_EXISTS,
      subspt_lookup,lookup_inter_alt,domain_insert,
         cut_state_def, domain_inter,arith_vars,SF DNF_ss
     ] >>
  rw[state_component_equality,set_var_def,lookup_insert] >>
  rw[] >> gvs[]
QED

Theorem dom_vars_of_exp_in:
  v ∈ domain l ⇒ v ∈ domain (vars_of_exp x l)
Proof
  qid_spec_tac ‘v’>>
  simp[GSYM subspt_domain,GSYM SUBSET_DEF, vars_of_exp_mono]
QED

Resume compile_correct[ShMem]:
  rpt strip_tac >>
  gvs[evaluate_def,shrink_def,CaseEq"option",CaseEq"word_loc"]>>
  fs[PULL_EXISTS]>>
  drule eval_lemma>>strip_tac>>
  first_assum $ irule_at Any>>
  cases_on ‘op’>>
  fs[sh_mem_op_def,sh_mem_store_def,sh_mem_load_def,set_var_def,call_env_def]>>
  fs[CaseEq"bool",CaseEq"option",CaseEq"ffi_result",CaseEq"word_loc"]>>
  rveq>>fs[]>>
  first_assum $ irule_at Any>>
  qmatch_asmsub_abbrev_tac ‘lookup v s.locals = SOME X’>>
  ‘lookup v locals = SOME X’ by
    (fs[subspt_lookup,lookup_inter_alt]>>
     first_assum $ irule>>fs[]>>
     irule dom_vars_of_exp_in>>fs[])>>
  fs[Abbr ‘X’]>>
  rpt (irule_at Any EQ_REFL) >>
  gvs[subspt_lookup,lookup_insert,lookup_inter_EQ]>>
  rpt strip_tac>>
  every_case_tac>>fs[]>>
  first_x_assum $ irule_at Any>>fs[]>>
  ‘∃y. lookup x (vars_of_exp ad (insert v () l0)) = SOME y’ by
    (simp[GSYM domain_lookup]>>
     irule dom_vars_of_exp_in>>
     fs[domain_insert]>>fs[domain_lookup]>>
     CCONTR_TAC>>Cases_on ‘lookup x l0’>>fs[])>>fs[]
QED

Theorem get_vars_subspt[local]:
  ∀rhss ws s extra locals.
    get_vars rhss s = SOME ws ∧
    subspt (inter s.locals (list_insert rhss extra)) locals ⇒
    get_vars rhss (s with locals := locals) = SOME ws
Proof
  Induct \\ fs [get_vars_def,CaseEq"option",PULL_EXISTS]
  \\ rw []
  >- gvs [subspt_lookup,lookup_inter_alt,domain_list_insert]
  \\ first_x_assum irule
  \\ first_assum $ irule_at Any
  \\ qexists_tac ‘extra’
  \\ gvs [subspt_lookup,lookup_inter_alt,domain_list_insert]
  \\ metis_tac []
QED

Resume compile_correct[Primitive]:
  rpt strip_tac
  \\ gvs [shrink_def,evaluate_def,CaseEq"option",CaseEq"bool"]
  \\ drule_then drule get_vars_subspt \\ strip_tac \\ fs []
  \\ fs [state_component_equality,set_vars_def]
  \\ fs [subspt_lookup,lookup_alist_insert_any,lookup_inter_alt]
  \\ qx_genl_tac [‘k’,‘v’] \\ strip_tac
  \\ Cases_on ‘ALOOKUP (ZIP (lhss,res_ws)) k’ \\ fs []
  \\ ‘MAP FST (ZIP (lhss,res_ws)) = lhss’ by fs [MAP_ZIP]
  \\ ‘¬MEM k lhss’ by gvs [ALOOKUP_NONE]
  \\ first_x_assum (qspec_then ‘k’ mp_tac)
  \\ fs [domain_list_insert,domain_list_delete]
QED

Finalise compile_correct;

Theorem mark_correct:
  ∀prog s res s1. evaluate (prog,s) = (res,s1) ⇒
  evaluate (FST (mark_all prog),s) = (res,s1)
Proof
  recInduct evaluate_ind \\ rpt conj_tac
  >~ [‘loopLang$Seq’] >- suspend "Seq"
  >~ [‘loopLang$If’] >- suspend "If"
  >~ [‘loopLang$Loop’] >- suspend "Loop"
  >~ [‘loopLang$Call’] >- suspend "Call"
  \\ rw [] \\ fs [mark_all_def,evaluate_def]
QED

Resume mark_correct[Seq]:
  rw [] \\ fs [mark_all_def]
  \\ rpt (pairarg_tac \\ fs [] \\ rveq)
  \\ TOP_CASE_TAC \\ fs []
  \\ fs [evaluate_def]
  \\ rpt (pairarg_tac \\ gs [] \\ rveq)
  \\ every_case_tac \\ fs []
QED

Resume mark_correct[If]:
  rw [] \\ fs [mark_all_def]
  \\ rpt (pairarg_tac \\ fs [] \\ rveq)
  \\ TOP_CASE_TAC \\ fs []
  \\ fs [evaluate_def]
  \\ every_case_tac \\ fs []
  \\ Cases_on ‘evaluate (c1,s)’ \\ fs []
  \\ Cases_on ‘q’ \\ fs [cut_res_def] \\ rveq \\ gs []
  \\ fs [cut_res_def]
  \\ Cases_on ‘evaluate (c2,s)’ \\ fs []
  \\ Cases_on ‘q’ \\ fs [cut_res_def] \\ rveq \\ gs []
  \\ fs [cut_res_def]
QED

Resume mark_correct[Loop]:
  rw [] \\ fs [mark_all_def]
  \\ rpt (pairarg_tac \\ fs [] \\ rveq)
  \\ qpat_x_assum ‘evaluate (Loop _ _ _, _) = _’ mp_tac
  \\ once_rewrite_tac [loopSemTheory.evaluate_def]
  \\ Cases_on ‘cut_res live_in (NONE:'a result option,s)’ \\ Cases_on ‘q’ \\ fs []
  \\ strip_tac \\ Cases_on ‘evaluate (body, r)’ \\ fs []
  \\ Cases_on ‘q’ \\ fs []
  \\ Cases_on ‘x’ \\ fs []
  \\ Cases_on ‘n’ \\ fs []
QED

Resume mark_correct[Call]:
  rw [] \\ fs [mark_all_def]
  \\ fs [evaluate_def]
  \\ TOP_CASE_TAC \\ fs []
  >- rw [evaluate_def]
  \\ TOP_CASE_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ rw [evaluate_def]
  \\ every_case_tac \\ fs [] \\ rveq \\ fs []
  \\ Cases_on
       ‘evaluate (q'',set_vars q'³' l (r'⁴' with locals := r''.locals))’
  \\ Cases_on
       ‘evaluate (q',set_var q w (r'⁴' with locals := r''.locals))’
  \\ fs []
  \\ rveq
  \\ every_case_tac \\ fs [] \\ rveq \\ gs [cut_res_def]
QED

Finalise mark_correct;

Theorem comp_correct:
  evaluate (prog,s) = (res,s1) ∧
  res ≠ SOME Error ∧
  (∀n. res ≠ SOME (Break n)) ∧
  (∀n. res ≠ SOME (Continue n)) ∧
  res ≠ NONE ⇒
  evaluate (comp prog,s) = (res,s1)
Proof
  strip_tac
  \\ drule compile_correct \\ fs []
  \\ fs [comp_def]
  \\ Cases_on ‘shrink [] prog LN’ \\ fs []
  \\ disch_then drule
  \\ disch_then (qspec_then ‘s.locals’ mp_tac)
  \\ impl_tac THEN1 fs [subspt_lookup,lookup_inter_alt]
  \\ strip_tac
  \\ ‘s with locals := s.locals = s’ by fs [state_component_equality] \\ fs []
  \\ fs [state_component_equality]
  \\ Cases_on ‘res’ \\ fs []
  \\ Cases_on ‘x’ \\ fs []
  \\ match_mp_tac mark_correct
  \\ fs [state_component_equality]
QED

Theorem optimise_correct:
  evaluate (prog,s) = (res,s1) ∧
  res ≠ SOME Error ∧
  (∀n. res ≠ SOME (Break n)) ∧
  (∀n. res ≠ SOME (Continue n)) ∧
  res ≠ NONE  ⇒
  evaluate (optimise prog,s) = (res,s1)
Proof
  rw [] >>
  fs [optimise_def] >>
  cases_on ‘comp LN prog’ >>
  drule loop_callProofTheory.compile_correct >>
  fs [] >>
  disch_then (qspecl_then [‘LN’, ‘q’, ‘r’] mp_tac) >>
  fs [] >>
  impl_tac >- fs [labels_in_def, lookup_def] >>
  strip_tac >> fs [] >>
  drule comp_correct >>
  fs []
QED
