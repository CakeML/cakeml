(*
  Prove that kernel functions maintain Candle prover's invariants
 *)

open preamble helperLib;
open semanticPrimitivesTheory semanticPrimitivesPropsTheory
     evaluateTheory namespacePropsTheory evaluatePropsTheory
     sptreeTheory holKernelProofTheory ml_hol_kernel_funsProgTheory
     candle_kernel_permsTheory candle_kernelProgTheory;
open permsTheory candle_kernel_valsTheory candle_prover_invTheory ast_extrasTheory;
local open ml_progLib in end

val _ = new_theory "candle_kernel_funs";

val _ = set_grammar_ancestry [
  "candle_kernel_vals", "candle_prover_inv", "ast_extras", "evaluate",
  "namespaceProps", "perms", "semanticPrimitivesProps", "misc"];

Theorem Arrow1:
  (A --> B) f fv ∧
  do_opapp [fv; av] = SOME (env, exp) ∧
  evaluate (s:'ffi semanticPrimitives$state) env [exp] = (s', res) ∧
  A a av ∧
  perms_ok ∅ av ∧
  perms_ok ∅ fv ⇒
    s.ffi = s'.ffi ∧
    ((res = Rerr (Rabort Rtimeout_error)) ∨
     (res = Rerr (Rabort Rtype_error)) ∨
     s.refs = s'.refs ∧
     s.eval_state = s'.eval_state ∧
     s.next_type_stamp = s'.next_type_stamp ∧
     ∃rv. res = Rval [rv] ∧
          B (f a) rv)
Proof
  strip_tac
  \\ qabbrev_tac ‘env' = write "a" av (write "f" fv ARB)’
  \\ ‘Eval env' (Var (Short "a")) (A a)’
    by simp [Abbr ‘env'’, ml_translatorTheory.Eval_Var_SIMP]
  \\ ‘Eval env' (Var (Short "f")) ((A --> B) f)’
    by simp [Abbr ‘env'’, ml_translatorTheory.Eval_Var_SIMP]
  \\ qpat_x_assum ‘(_ --> _) _ _’ kall_tac
  \\ qpat_x_assum ‘A _ _’ kall_tac
  \\ dxrule_all ml_translatorTheory.Eval_Arrow
  \\ simp [ml_translatorTheory.Eval_def]
  \\ disch_then (qspec_then ‘s.refs’ strip_assume_tac)
  \\ dxrule ml_translatorTheory.evaluate_empty_state_IMP
  \\ simp [ml_progTheory.eval_rel_def, evaluate_def, Abbr ‘env'’,
           ml_progTheory.nsLookup_write]
  \\ strip_tac
  \\ gvs [AllCaseEqs(),evaluateTheory.dec_clock_def]
  \\ drule_then (qspec_then ‘s.clock’ mp_tac) evaluate_set_init_clock
  \\ simp [with_same_clock]
  \\ strip_tac \\ gvs []
  THEN1
   (drule evaluate_empty_perms
    \\ reverse impl_tac THEN1 fs []
    \\ fs [perms_ok_state_def]
    \\ drule_all perms_ok_do_opapp \\ fs [])
  \\ mp_tac (CONJUNCT1 is_clock_io_mono_evaluate)
  \\ qmatch_asmsub_abbrev_tac ‘evaluate s env1 [e]’
  \\ disch_then (qspecl_then [`s`,`env1`,`[e]`] mp_tac)
  \\ rw [is_clock_io_mono_def]
  \\ gs [io_events_mono_antisym]
QED

Theorem Arrow2:
  (A --> B --> C) f fv ∧
  do_partial_app fv av = SOME gv ∧
  do_opapp [gv; bv] = SOME (env, exp) ∧
  evaluate (s:'ffi semanticPrimitives$state) env [exp] = (s', res) ∧
  A a av ∧ B b bv ∧
  perms_ok ∅ av ∧
  perms_ok ∅ bv ∧
  perms_ok ∅ fv ⇒
    s.ffi = s'.ffi ∧
    ((res = Rerr (Rabort Rtimeout_error)) ∨
     (res = Rerr (Rabort Rtype_error)) ∨
     s.refs = s'.refs ∧
     s.eval_state = s'.eval_state ∧
     s.next_type_stamp = s'.next_type_stamp ∧
     ∃rv. res = Rval [rv] ∧
          C (f a b) rv)
Proof
  strip_tac
  \\ ‘LENGTH s'.refs = LENGTH s.refs’
    by (gvs [do_partial_app_def, AllCaseEqs(), do_opapp_cases,
             perms_ok_def]
        \\ drule evaluate_empty_perms
        \\ impl_tac \\ simp []
        \\ gs [perms_ok_state_def, perms_ok_env_def]
        \\ Cases \\ simp [ml_progTheory.nsLookup_nsBind_compute]
        \\ rw [] \\ gs []
        \\ first_x_assum irule
        \\ first_assum (irule_at (Pos last)) \\ gs [])
  \\ qabbrev_tac ‘env' = write "a" av (write "b" bv (write "f" fv ARB))’
  \\ ‘Eval env' (Var (Short "a")) (A a)’
    by simp [Abbr ‘env'’, ml_translatorTheory.Eval_Var_SIMP]
  \\ ‘Eval env' (Var (Short "b")) (B b)’
    by simp [Abbr ‘env'’, ml_translatorTheory.Eval_Var_SIMP]
  \\ ‘Eval env' (Var (Short "f")) ((A --> B --> C) f)’
    by simp [Abbr ‘env'’, ml_translatorTheory.Eval_Var_SIMP]
  \\ qpat_x_assum ‘(_ --> _) _ _’ kall_tac
  \\ qpat_x_assum ‘A _ _’ kall_tac
  \\ qpat_x_assum ‘B _ _’ kall_tac
  \\ dxrule_all ml_translatorTheory.Eval_Arrow \\ strip_tac
  \\ dxrule_all ml_translatorTheory.Eval_Arrow
  \\ simp [ml_translatorTheory.Eval_def]
  \\ disch_then (qspec_then ‘s.refs’ strip_assume_tac)
  \\ dxrule ml_translatorTheory.evaluate_empty_state_IMP
  \\ simp [ml_progTheory.eval_rel_def, evaluate_def, Abbr ‘env'’,
           ml_progTheory.nsLookup_write]
  \\ qpat_x_assum ‘do_partial_app _ _ = _’ mp_tac
  \\ simp [do_partial_app_def, Once do_opapp_def, AllCaseEqs (), PULL_EXISTS]
  \\ rpt gen_tac \\ strip_tac
  \\ rpt gen_tac \\ strip_tac \\ gvs []
  \\ qpat_x_assum ‘do_opapp _ = SOME (env,exp)’ mp_tac
  \\ simp [do_opapp_cases]
  \\ strip_tac \\ gvs [evaluate_def, do_opapp_cases,
                       evaluateTheory.dec_clock_def]
  \\ dxrule_then (qspec_then ‘s.clock’ mp_tac) evaluate_set_init_clock
  \\ simp [with_same_clock]
  \\ strip_tac \\ gvs []
  \\ mp_tac (CONJUNCT1 is_clock_io_mono_evaluate)
  \\ qmatch_asmsub_abbrev_tac ‘evaluate s env1 [e]’
  \\ disch_then (qspecl_then [`s`,`env1`,`[e]`] mp_tac)
  \\ rw [is_clock_io_mono_def]
  \\ gs [io_events_mono_antisym]
QED

Triviality GC_T:
  GC s = T
Proof
  fs [cfHeapsBaseTheory.GC_def,set_sepTheory.SEP_EXISTS_THM]
  \\ qexists_tac ‘λx. T’ \\ fs []
QED

Theorem MEM_st2heap: (* TODO: move *)
  Mem l x ∈ st2heap p s ⇔
  l < LENGTH s.refs ∧ x = EL l s.refs
Proof
  PairCases_on ‘p’
  \\ fs [cfStoreTheory.st2heap_def,cfStoreTheory.ffi2heap_def,
         cfAppTheory.store2heap_MAPi,MEM_MAPi]
  \\ IF_CASES_TAC \\ fs []
QED

Theorem HOL_STORE_not_kernel_locs:
  (∀loc. loc ∈ kernel_locs ⇒ kernel_loc_ok refs loc s.refs) ∧
  l < LENGTH s.refs ∧ l ∉ kernel_locs ⇒
  (HOL_STORE refs * one (Mem l (EL l s.refs)) * GC) (st2heap p s)
Proof
  fs [ml_monad_translatorBaseTheory.REFS_PRED_def,HOL_STORE_def]
  \\ fs [ml_monad_translatorBaseTheory.REF_REL_def,set_sepTheory.SEP_EXISTS_THM,
         set_sepTheory.SEP_CLAUSES,cfHeapsBaseTheory.REF_def]
  \\ full_simp_tac (std_ss ++ helperLib.sep_cond_ss) [set_sepTheory.cond_STAR]
  \\ fs [cfHeapsBaseTheory.cell_def,set_sepTheory.one_STAR,GSYM set_sepTheory.STAR_ASSOC]
  \\ fs [GC_T,MEM_st2heap]
  \\ fs [kernel_locs_def, SF DNF_ss, MEM_st2heap]
  \\ fs [the_type_constants_def,the_term_constants_def,the_axioms_def,
         the_context_def,kernel_loc_ok_def,listTheory.oEL_EQ_EL]
  \\ metis_tac []
QED

Theorem REFS_PRED_HOL_STORE:
  (∀loc. loc ∈ kernel_locs ⇒ kernel_loc_ok refs loc s.refs) ⇒
  REFS_PRED (HOL_STORE,p) refs s
Proof
  fs [ml_monad_translatorBaseTheory.REFS_PRED_def,HOL_STORE_def]
  \\ fs [ml_monad_translatorBaseTheory.REF_REL_def,set_sepTheory.SEP_EXISTS_THM,
         set_sepTheory.SEP_CLAUSES,cfHeapsBaseTheory.REF_def]
  \\ full_simp_tac (std_ss ++ helperLib.sep_cond_ss) [set_sepTheory.cond_STAR]
  \\ fs [cfHeapsBaseTheory.cell_def,set_sepTheory.one_STAR,GSYM set_sepTheory.STAR_ASSOC]
  \\ fs [GC_T,MEM_st2heap]
  \\ fs [kernel_locs_def, SF DNF_ss]
  \\ fs [the_type_constants_def,the_term_constants_def,the_axioms_def,
         the_context_def,kernel_loc_ok_def,listTheory.oEL_EQ_EL]
  \\ metis_tac []
QED

Theorem HOL_STORE_kernel_loc_ok:
  (HOL_STORE r * frame) (st2heap p s) ∧ loc ∈ kernel_locs ⇒
  kernel_loc_ok r loc s.refs
Proof
  fs [HOL_STORE_def]
  \\ simp [ml_monad_translatorBaseTheory.REF_REL_def,set_sepTheory.SEP_EXISTS_THM,
           set_sepTheory.SEP_CLAUSES,cfHeapsBaseTheory.REF_def]
  \\ full_simp_tac (std_ss ++ helperLib.sep_cond_ss) [set_sepTheory.cond_STAR]
  \\ fs [cfHeapsBaseTheory.cell_def,set_sepTheory.one_STAR,GSYM set_sepTheory.STAR_ASSOC]
  \\ fs [GC_T,MEM_st2heap]
  \\ strip_tac
  \\ fs [kernel_loc_ok_def]
  \\ fs [kernel_locs_def]
  \\ pop_assum (fn th => fs [GSYM th] THEN assume_tac th)
  \\ gvs [listTheory.oEL_EQ_EL]
  \\ first_x_assum $ irule_at $ Pos hd \\ fs []
  \\ fs [the_type_constants_def,
         the_term_constants_def,
         the_axioms_def,
         the_context_def]
QED

Triviality IMP_perms_ok_lemma:
  (LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) x1 v ⇒ perms_ok ps v) ∧
  (LIST_TYPE (PAIR_TYPE STRING_TYPE TYPE_TYPE) x2 v ⇒ perms_ok ps v) ∧
  (LIST_TYPE THM_TYPE x3 v ⇒ perms_ok ps v) ∧
  (LIST_TYPE UPDATE_TYPE x4 v ⇒ perms_ok ps v)
Proof
  rw []
  \\ drule_at (Pos last) LIST_TYPE_perms_ok \\ disch_then irule
  \\ rw []
  \\ TRY (drule_at (Pos last) PAIR_TYPE_perms_ok \\ disch_then irule)
  \\ rw []
  \\ imp_res_tac TYPE_TYPE_perms_ok \\ fs []
  \\ imp_res_tac TERM_TYPE_perms_ok \\ fs []
  \\ imp_res_tac THM_TYPE_perms_ok \\ fs []
  \\ imp_res_tac STRING_TYPE_perms_ok \\ fs []
  \\ imp_res_tac NUM_perms_ok \\ fs []
  \\ imp_res_tac UPDATE_TYPE_perms_ok \\ fs []
QED

val p = “p:('a -> (string |-> ffi)) # (string list #
           (string -> word8 list -> word8 list -> ffi -> ffi ffi_result option)) list”

Theorem ArrowM1:
  ArrowP F (HOL_STORE,^p) (PURE A) (MONAD B D) f fv ∧
  do_opapp [fv; av] = SOME (env, exp) ∧
  evaluate (s:'a semanticPrimitives$state) env [exp] = (s', res) ∧
  A a av ∧ STATE ctxt refs ∧
  (∀loc. loc ∈ kernel_locs ⇒ kernel_loc_ok refs loc s.refs) ∧
  (∀loc r. loc ∉ kernel_locs ∧ LLOOKUP s.refs loc = SOME r ⇒ ref_ok ctxt r) ∧
  perms_ok kernel_perms av ∧
  perms_ok kernel_perms fv ⇒
    s.ffi = s'.ffi ∧
    ((res = Rerr (Rabort Rtimeout_error)) ∨
     (res = Rerr (Rabort Rtype_error)) ∨
     s.next_type_stamp = s'.next_type_stamp ∧
     s.eval_state = s'.eval_state ∧
     ∃r refs2.
       f a refs = (r,refs2) ∧
       (∀loc. loc ∈ kernel_locs ⇒ kernel_loc_ok refs2 loc s'.refs) ∧
       (∀loc r. loc ∉ kernel_locs ∧ LLOOKUP s'.refs loc = SOME r ⇒ ref_ok ctxt r) ∧
       (∀x. r = M_success x ⇒ ∃rv. res = Rval [rv] ∧ B x rv) ∧
       (∀x. r = M_failure x ⇒ ∃rv. res = Rerr (Rraise rv) ∧ D x rv))
Proof
  fs [ml_monad_translatorTheory.ArrowP_def,ml_monad_translatorTheory.PURE_def,PULL_EXISTS]
  \\ strip_tac \\ last_x_assum drule \\ fs []
  \\ fs [state_ok_def]
  \\ rename [‘STATE ctxt refs’]
  \\ disch_then (qspecl_then [‘refs’,‘s’] mp_tac)
  \\ impl_tac >- fs [REFS_PRED_HOL_STORE]
  \\ disch_then (qspec_then ‘[]’ strip_assume_tac)
  \\ fs [ml_monad_translatorBaseTheory.REFS_PRED_FRAME_def]
  \\ drule_all perms_ok_do_opapp \\ strip_tac
  \\ drule evaluate_kernel_perms
  \\ disch_then drule
  \\ impl_tac
   >- (fs [kernel_perms_def,perms_ok_state_def]
       \\ rw [] \\ first_x_assum drule
       \\ fs [kernel_loc_ok_def,LLOOKUP_THM]
       \\ strip_tac \\ gvs [perms_ok_ref_def]
       \\ fs [kernel_locs_def]
       \\ gvs [IN_kernel_locs]
       \\ imp_res_tac IMP_perms_ok_lemma \\ fs [])
  \\ simp [kernel_perms_def]
  \\ csimp [GSYM kernel_perms_def]
  \\ strip_tac
  \\ drule evaluate_set_init_clock
  \\ disch_then (qspec_then ‘s.clock’ mp_tac)
  \\ impl_tac
  >- (strip_tac \\ fs [ml_monad_translatorTheory.MONAD_def]
      \\ every_case_tac \\ fs [])
  \\ fs []
  \\ ‘(s with refs := s.refs) = s’ by fs [state_component_equality]
  \\ fs [] \\ reverse strip_tac \\ gvs []
  THEN1
   (imp_res_tac evaluatePropsTheory.evaluate_io_events_mono_imp
    \\ fs [evaluatePropsTheory.io_events_mono_def]
    \\ imp_res_tac rich_listTheory.IS_PREFIX_ANTISYM \\ fs [])
  \\ gvs [] \\ pop_assum kall_tac
  \\ Cases_on ‘res = Rerr (Rabort Rtimeout_error)’ \\ fs []
  \\ Cases_on ‘res = Rerr (Rabort Rtype_error)’ \\ fs []
  \\ fs [ml_monad_translatorTheory.MONAD_def]
  \\ Cases_on ‘f a refs’ \\ fs []
  \\ rewrite_tac [CONJ_ASSOC]
  \\ reverse conj_tac THEN1 (every_case_tac \\ fs [])
  \\ reverse conj_tac THEN1 (every_case_tac \\ fs [])
  \\ ‘r = st3’ by (every_case_tac \\ fs [])
  \\ rw []
  THEN1
   (‘REFS_PRED (HOL_STORE,p) refs s’ by fs [REFS_PRED_HOL_STORE]
    \\ first_x_assum drule
    \\ fs [ml_monad_translatorBaseTheory.REFS_PRED_def]
    \\ first_x_assum drule \\ strip_tac
    \\ fs [GSYM set_sepTheory.STAR_ASSOC]
    \\ drule_all HOL_STORE_kernel_loc_ok \\ fs [])
  \\ fs [oEL_THM] \\ rw [] \\ fs []
  \\ ‘(HOL_STORE refs * one (Mem loc (EL loc s.refs)) * GC) (st2heap p s)’
        by fs [HOL_STORE_not_kernel_locs]
  \\ fs [GSYM set_sepTheory.STAR_ASSOC]
  \\ first_x_assum drule
  \\ fs [GSYM set_sepTheory.STAR_ASSOC]
  \\ once_rewrite_tac [set_sepTheory.STAR_COMM]
  \\ fs [GSYM set_sepTheory.STAR_ASSOC,set_sepTheory.one_STAR,MEM_st2heap]
  \\ strip_tac
  \\ qsuff_tac ‘ref_ok ctxt (EL loc s.refs)’ THEN1 asm_rewrite_tac []
  \\ fs []
QED

Theorem ArrowM2:
  ArrowP F (HOL_STORE,^p) (PURE A1) (ArrowM F (HOL_STORE,p) (PURE A2) (MONAD B D)) f fv ∧
  do_partial_app fv a1v = SOME gv ∧
  do_opapp [gv; a2v] = SOME (env, exp) ∧
  evaluate (s:'a semanticPrimitives$state) env [exp] = (s', res) ∧
  A1 a1 a1v ∧ A2 a2 a2v ∧ STATE ctxt refs ∧
  (∀loc. loc ∈ kernel_locs ⇒ kernel_loc_ok refs loc s.refs) ∧
  (∀loc r. loc ∉ kernel_locs ∧ LLOOKUP s.refs loc = SOME r ⇒ ref_ok ctxt r) ∧
  perms_ok kernel_perms a1v ∧
  perms_ok kernel_perms a2v ∧
  perms_ok kernel_perms fv ⇒
    s.ffi = s'.ffi ∧
    ((res = Rerr (Rabort Rtimeout_error)) ∨
     (res = Rerr (Rabort Rtype_error)) ∨
     s.next_type_stamp = s'.next_type_stamp ∧
     s.eval_state = s'.eval_state ∧
     ∃r refs2.
       f a1 a2 refs = (r,refs2) ∧
       (∀loc. loc ∈ kernel_locs ⇒ kernel_loc_ok refs2 loc s'.refs) ∧
       (∀loc r. loc ∉ kernel_locs ∧ LLOOKUP s'.refs loc = SOME r ⇒ ref_ok ctxt r) ∧
       (∀x. r = M_success x ⇒ ∃rv. res = Rval [rv] ∧ B x rv) ∧
       (∀x. r = M_failure x ⇒ ∃rv. res = Rerr (Rraise rv) ∧ D x rv))
Proof
  strip_tac \\ irule ArrowM1 \\ fs [SF SFY_ss]
  \\ first_assum $ irule_at $ Pos hd
  \\ first_assum $ irule_at $ Pos hd
  \\ first_assum $ irule_at $ Pos hd \\ fs []
  \\ gvs [do_partial_app_def,AllCaseEqs()]
  \\ qexists_tac ‘p’
  \\ conj_tac THEN1
   (simp [Once perms_ok_cases]
    \\ pop_assum mp_tac
    \\ simp [Once perms_ok_cases]
    \\ simp [perms_ok_env_def]
    \\ fs [ml_progTheory.nsLookup_nsBind_compute]
    \\ strip_tac \\ reverse Cases
    \\ fs [ml_progTheory.nsLookup_nsBind_compute]
    \\ rw [] \\ fs []
    \\ metis_tac [namespaceTheory.id_distinct,namespaceTheory.id_11])
  \\ fs [ml_monad_translatorTheory.ArrowP_def]
  \\ fs [ml_monad_translatorTheory.ArrowM_def]
  \\ fs [ml_monad_translatorTheory.PURE_def,PULL_EXISTS]
  \\ rpt strip_tac
  \\ last_x_assum drule_all
  \\ fs [do_opapp_def]
  \\ simp [Once evaluate_def]
  \\ fs [ml_monad_translatorTheory.ArrowP_def]
  \\ fs [ml_monad_translatorTheory.PURE_def,PULL_EXISTS]
  \\ fs [PULL_FORALL] \\ gen_tac
  \\ disch_then (qspec_then ‘junk’ strip_assume_tac)
  \\ fs [GSYM PULL_FORALL]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ fs [do_opapp_def]
QED

Theorem state_ok_with_clock[simp]:
  state_ok ctxt (s with clock := k) ⇔ state_ok ctxt s
Proof
  fs [state_ok_def]
QED

Theorem EqualityType_11:
  ∀abs x v v'. EqualityType abs ∧ abs x v ∧ abs x v' ⇒ v = v'
Proof
  fs [ml_translatorTheory.EqualityType_def] \\ metis_tac []
QED

Theorem IMP_EVERY_v_ok:
  (∀loc. if loc ∈ kernel_locs then kernel_loc_ok refs loc s'.refs
         else LLOOKUP s'.refs loc = LLOOKUP s.refs loc) ∧
  (∀loc. loc ∈ kernel_locs ⇒ kernel_loc_ok refs loc s.refs) ∧
  EVERY (ref_ok ctxt) s.refs ∧ STATE ctxt refs ⇒
  EVERY (ref_ok ctxt) s'.refs
Proof
  rw [EVERY_EL]
  \\ last_x_assum $ qspec_then ‘n’ mp_tac
  \\ reverse (rw [])
  >- (gvs [LLOOKUP_THM] \\ res_tac \\ fs [] \\ gvs [] \\ metis_tac [])
  \\ last_x_assum drule
  \\ strip_tac
  \\ fs [kernel_loc_ok_def]
  \\ gvs [IN_kernel_locs]
  \\ gvs [LLOOKUP_THM,ref_ok_def]
  \\ last_x_assum drule
  \\ fs [ref_ok_def]
  \\ ‘EqualityType (LIST_TYPE (PAIR_TYPE STRING_TYPE NUM)) ∧
      EqualityType (LIST_TYPE (PAIR_TYPE STRING_TYPE TYPE_TYPE)) ∧
      EqualityType (LIST_TYPE THM_TYPE) ∧
      EqualityType (LIST_TYPE UPDATE_TYPE)’ by
   (rw []
    \\ irule cfLetAutoTheory.EqualityType_LIST_TYPE
    \\ fs [EqualityType_THM_TYPE]
    \\ fs [EqualityType_UPDATE_TYPE]
    \\ TRY (irule cfLetAutoTheory.EqualityType_PAIR_TYPE)
    \\ fs [EqualityType_TYPE_TYPE]
    \\ fs [ml_translatorTheory.EqualityType_NUM_BOOL])
  \\ imp_res_tac EqualityType_11 \\ fs []
QED

Theorem HOL_EXN_TYPE_Fail_v_ok:
  HOL_EXN_TYPE (Failure m) v ⇒ v_ok ctxt v
Proof
  Cases_on ‘m’
  \\ rw [HOL_EXN_TYPE_def,ml_translatorTheory.STRING_TYPE_def]
  \\ irule v_ok_Conv \\ fs []
  \\ fs [Once v_ok_cases]
QED

Theorem inferred_APPEND:
  !c v. inferred c v ==>
    !x s. STATE (x ++ c) s /\ (!th. THM c th ==> THM (x ++ c) th) ==>
          inferred (x ++ c) v
Proof
  ho_match_mp_tac inferred_strongind
  \\ rw[]
  \\ rw[Once inferred_cases]
  >- metis_tac[TYPE_APPEND_EXTEND]
  >- metis_tac[TERM_APPEND_EXTEND]
  >- metis_tac[]
QED

Theorem v_ok_APPEND:
  (!c v. kernel_vals c v ⇒
    !x s. STATE (x ++ c) s /\ (!th. THM c th ==> THM (x ++ c) th)
    ==> kernel_vals (x ++ c) v) ∧
  (!c v. v_ok c v ⇒ ∀x s.
    !x s. STATE (x ++ c) s /\ (!th. THM c th ==> THM (x ++ c) th)
     ==> v_ok (x ++ c) v) ∧
  (∀c e. env_ok c e ⇒ ∀x s.
    !x s. STATE (x ++ c) s /\ (!th. THM c th ==> THM (x ++ c) th)
  ==> env_ok (x ++ c) e)
Proof
  ho_match_mp_tac v_ok_strongind
  \\ rw[]
  \\ rw[Once v_ok_cases]
  >- metis_tac[inferred_APPEND]
  \\ fs[EVERY_MEM] \\ metis_tac[]
QED

Theorem ref_ok_APPEND:
  !c v. ref_ok c v ⇒ ∀x s.
    !x s. STATE (x ++ c) s /\ (!th. THM c th ==> THM (x ++ c) th)
     ==> ref_ok (x ++ c) v
Proof
  gen_tac \\ Cases \\ rw[ref_ok_def]
  \\ fs[EVERY_MEM] \\ metis_tac[v_ok_APPEND]
QED

Theorem inferred_ok:
  inferred ctxt f ∧
  state_ok ctxt s ∧
  v_ok ctxt v ∧
  do_opapp [f; v] = SOME (env, exp) ∧
  evaluate (s:'ffi state) env [exp] = (s', res) ⇒
    (∃abort. s'.ffi = s.ffi ∧ res = Rerr (Rabort abort)) ∨
    ∃ctxt'.
      state_ok ctxt' s' ∧
      (∀v. v_ok ctxt v ⇒ v_ok ctxt' v) ∧
      (∀v. kernel_vals ctxt v ⇒ kernel_vals ctxt' v) ∧
      (∀vs. res = Rval vs ⇒ EVERY (v_ok ctxt') vs) ∧
      (∀v. res = Rerr (Rraise v) ⇒ v_ok ctxt' v)
Proof

  rw [Once inferred_cases]
  >~ [‘TYPE ctxt ty’] >- (
    Cases_on ‘ty’ \\ gs [TYPE_TYPE_def, do_opapp_cases])
  >~ [‘TERM ctxt tm’] >- (
    Cases_on ‘tm’ \\ gs [TERM_TYPE_def, do_opapp_cases])
  >~ [‘THM ctxt th’] >- (
    Cases_on ‘th’ \\ gs [THM_TYPE_def, do_opapp_cases])
  \\ rename [‘f ∈ kernel_funs’]
  \\ Cases_on ‘f ∈ { call_type_subst_v; call_freesin_v; call_vfree_in_v;
                     call_variant_v; vsubst_v; inst_v; trans_v; abs_v; eq_mp_v;
                     deduct_antisym_rule_v; inst_type_v; inst_1_v; trans_v }’ THEN1
   (gvs []
    \\ qpat_x_assum ‘do_opapp _ = _’ mp_tac
    \\ last_x_assum mp_tac
    \\ rewrite_tac [kernel_funs_v_def]
    \\ rename [‘Closure env1 a1 (Fun a2 ee)’]
    \\ fs [do_opapp_def] \\ rw [] \\ gvs [evaluate_def]
    \\ qexists_tac ‘ctxt’ \\ fs []
    \\ irule_at (Pos last) v_ok_KernelVals
    \\ irule_at Any v_ok_PartialApp
    \\ first_assum $ irule_at $ Pos last
    \\ irule_at Any v_ok_Inferred
    \\ irule_at Any inferred_KernelFuns
    \\ first_assum $ irule_at Any
    \\ fs [do_partial_app_def])
  \\ gvs [kernel_funs_def]
  \\ rpt (qpat_x_assum ‘_ ≠ (_:v)’ kall_tac)
  >~ [‘do_opapp [concl_v; v]’] >-
   (drule_all concl_v_head \\ strip_tac \\ gvs []
    \\ TRY (first_x_assum $ irule_at Any \\ gvs [] \\ NO_TAC)
    \\ rename [‘THM_TYPE_HEAD _’]
    \\ assume_tac concl_v_thm
    \\ drule_all v_ok_THM_TYPE_HEAD \\ strip_tac
    \\ (drule_then $ drule_then $ drule_then $ drule) Arrow1
    \\ impl_tac
    THEN1 (imp_res_tac THM_TYPE_perms_ok \\ fs [])
    \\ strip_tac \\ gvs []
    \\ qexists_tac ‘ctxt’ \\ fs []
    \\ fs [state_ok_def]
    \\ irule_at (Pos last) v_ok_KernelVals
    \\ irule_at Any v_ok_Inferred
    \\ irule_at Any inferred_TERM
    \\ first_assum $ irule_at Any
    \\ irule_at Any (holKernelProofTheory.concl_thm |> GEN_ALL |> SIMP_RULE std_ss [])
    \\ imp_res_tac v_ok_THM \\ fs []
    \\ first_assum $ irule_at Any
    \\ first_assum $ irule_at Any
    \\ fs [SF SFY_ss])
  >~ [‘do_opapp [beta_v; v]’] >-
   (drule_all beta_v_head \\ strip_tac \\ gvs []
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ drule_all v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ imp_res_tac v_ok_TERM \\ fs []
    \\ assume_tac beta_v_thm
    \\ fs [state_ok_def]
    \\ ‘perms_ok kernel_perms v ∧ perms_ok kernel_perms beta_v’ by
         fs [TERM_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all ArrowM1 \\ strip_tac \\ fs []
    \\ disj2_tac
    \\ drule_all holKernelProofTheory.BETA_thm \\ strip_tac \\ gvs []
    \\ qexists_tac ‘ctxt’ \\ fs []
    \\ fs [PULL_EXISTS]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ fs [SF SFY_ss]
    \\ Cases_on ‘r’ \\ fs []
    \\ imp_res_tac THM_IMP_v_ok \\ gvs []
    \\ rename [‘M_failure ff’] \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss])
  >~ [‘do_opapp [types_v; v]’] >- (
    drule_all types_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac types_v_thm
    \\ fs[state_ok_def]
    \\ `perms_ok kernel_perms v ∧ perms_ok kernel_perms types_v`
    by simp[UNIT_TYPE_perms_ok]
    \\ drule_all ArrowM1 \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ qexists_tac`ctxt` \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ fs[holKernelTheory.types_def]
    \\ fs[holKernelTheory.get_the_type_constants_def]
    \\ gvs[]
    \\ conj_tac >- metis_tac[]
    \\ drule_then irule LIST_TYPE_v_ok
    \\ rw[EVERY_MEM]
    \\ drule_then irule PAIR_TYPE_v_ok
    \\ conj_tac >- MATCH_ACCEPT_TAC NUM_v_ok
    \\ MATCH_ACCEPT_TAC STRING_TYPE_v_ok
  )
  >~ [‘do_opapp [get_type_arity_v; v]’] >- (
    drule_all get_type_arity_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac get_type_arity_v_thm
    \\ fs[state_ok_def, STRING_TYPE_HEAD_def]
    \\ `perms_ok kernel_perms v ∧ perms_ok kernel_perms get_type_arity_v`
    by simp[STRING_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all ArrowM1 \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ qexists_tac`ctxt` \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ fs [SF SFY_ss]
    \\ fs[holKernelTheory.get_type_arity_def, ml_monadBaseTheory.st_ex_bind_def]
    \\ fs[holKernelTheory.get_the_type_constants_def]
    \\ drule assoc_thm
    \\ strip_tac
    \\ fs[SF SFY_ss]
    \\ Cases_on`r` \\ fs[NUM_v_ok, SF SFY_ss]
    \\ rename [‘M_failure ff’] \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss])
  >~ [‘do_opapp [call_new_type_v; v]’] >- (
    drule_all call_new_type_v_head \\ strip_tac \\ gvs[]
    >- (first_assum $ irule_at Any \\ simp[])
    \\ assume_tac call_new_type_v_thm
    \\ fs[state_ok_def]
    \\ `∃pa. PAIR_TYPE STRING_TYPE INT pa v`
    by (
      irule v_ok_PAIR_TYPE_HEAD
      \\ first_assum $ irule_at Any
      \\ first_assum $ irule_at Any
      \\ simp[STRING_TYPE_HEAD_def, INT_HEAD_def])
    \\ PairCases_on`pa`
    \\ `perms_ok kernel_perms v ∧ perms_ok kernel_perms call_new_type_v`
    by (
      simp[]
      \\ drule_at_then Any irule PAIR_TYPE_perms_ok
      \\ simp[STRING_TYPE_perms_ok, INT_perms_ok, SF SFY_ss])
    \\ drule_all ArrowM1 \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ reverse(Cases_on`0 <= pa1` \\ fs[holKernelTheory.raise_Failure_def])
    >- (
      gvs[]
      \\ first_assum $ irule_at Any
      \\ simp[SF SFY_ss]
      \\ drule_then irule HOL_EXN_TYPE_Fail_v_ok )
    \\ drule new_type_thm
    \\ disch_then(qspecl_then[`pa0`,`Num(ABS pa1)`]mp_tac)
    \\ simp[]
    \\ reverse TOP_CASE_TAC \\ simp[]
    >- (
      strip_tac \\ gvs[]
      \\ first_assum $ irule_at Any
      \\ simp[SF SFY_ss]
      \\ rename1 `M_failure ff`
      \\ Cases_on`ff` \\ gvs[]
      \\ drule_then irule HOL_EXN_TYPE_Fail_v_ok )
    \\ strip_tac \\ gvs[ml_translatorTheory.UNIT_TYPE_def,v_ok_Conv_NONE]
    \\ first_assum $ irule_at Any
    \\ simp[]
    \\ reverse conj_tac >- metis_tac[v_ok_APPEND, CONS_APPEND]
    \\ metis_tac[ref_ok_APPEND, CONS_APPEND])
  >~ [‘do_opapp [mk_type_v; v]’] >- (
    drule_all mk_type_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac mk_type_v_thm
    \\ fs[state_ok_def]
    \\ `∃pa. PAIR_TYPE STRING_TYPE (LIST_TYPE TYPE_TYPE) pa v`
    by (
      irule v_ok_PAIR_TYPE_HEAD
      \\ first_assum $ irule_at Any
      \\ first_assum $ irule_at Any
      \\ simp[STRING_TYPE_HEAD_def]
      \\ rpt strip_tac \\ irule v_ok_LIST_TYPE_HEAD
      \\ first_assum $ irule_at Any
      \\ first_assum $ irule_at Any
      \\ MATCH_ACCEPT_TAC v_ok_TYPE_TYPE_HEAD )
    \\ PairCases_on`pa`
    \\ `perms_ok kernel_perms v ∧ perms_ok kernel_perms mk_type_v`
    by (
      simp[]
      \\ drule_at_then Any irule PAIR_TYPE_perms_ok
      \\ simp[STRING_TYPE_perms_ok, LIST_TYPE_TYPE_perms_ok, SF SFY_ss])
    \\ drule_all ArrowM1 \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ qexists_tac`ctxt` \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ fs [SF SFY_ss]
    \\ fs[ml_translatorTheory.PAIR_TYPE_def]
    \\ rveq \\ fs[v_ok_Conv_NONE]
    \\ drule_then drule v_ok_LIST_TYPE
    \\ strip_tac
    \\ drule_all mk_type_thm \\ strip_tac
    \\ Cases_on`r` \\ fs[]
    >- metis_tac[TYPE_IMP_v_ok]
    \\ rename [‘M_failure ff’] \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss])
  >~ [‘do_opapp [mk_vartype_v; v]’] >- (
    drule_all mk_vartype_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac mk_vartype_v_thm
    \\ fs[state_ok_def]
    \\ `perms_ok ∅ v ∧ perms_ok ∅ mk_vartype_v`
    by simp[STRING_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all Arrow1 \\ strip_tac \\ fs[]
    \\ qexists_tac`ctxt` \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ simp[SF SFY_ss]
    \\ irule TYPE_IMP_v_ok
    \\ first_assum $ irule_at $ Any
    \\ EVAL_TAC)
  >~ [‘do_opapp [dest_type_v; v]’] >- (
    drule_all dest_type_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac dest_type_v_thm
    \\ fs[state_ok_def]
    \\ drule_all v_ok_TYPE_TYPE_HEAD \\ strip_tac
    \\ imp_res_tac v_ok_TYPE \\ fs []
    \\ `perms_ok kernel_perms v ∧ perms_ok kernel_perms dest_type_v`
    by simp[TYPE_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all ArrowM1 \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ qexists_tac`ctxt` \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ fs [SF SFY_ss]
    \\ drule_all dest_type_thm \\ strip_tac
    \\ Cases_on ‘r’ \\ fs []
    >- (
      drule_then irule PAIR_TYPE_v_ok
      \\ rw[STRING_TYPE_v_ok, SF SFY_ss]
      \\ drule_then irule LIST_TYPE_v_ok
      \\ fs[EVERY_MEM]
      \\ metis_tac[TYPE_IMP_v_ok])
    \\ rename [‘M_failure ff’] \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss])
  >~ [‘do_opapp [dest_vartype_v; v]’] >- (
    drule_all dest_vartype_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac dest_vartype_v_thm
    \\ fs[state_ok_def]
    \\ drule_all v_ok_TYPE_TYPE_HEAD \\ strip_tac
    \\ imp_res_tac v_ok_TYPE \\ fs []
    \\ `perms_ok kernel_perms v ∧ perms_ok kernel_perms dest_vartype_v`
    by simp[TYPE_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all ArrowM1 \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ qexists_tac`ctxt` \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ fs [SF SFY_ss]
    \\ drule_all dest_vartype_thm \\ strip_tac
    \\ Cases_on ‘r’ \\ fs []
    >- rw[STRING_TYPE_v_ok, SF SFY_ss]
    \\ rename [‘M_failure ff’] \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss]
    \\ fs[holKernelTheory.dest_vartype_def]
    \\ Cases_on`ty` \\ fs[ml_monadBaseTheory.st_ex_return_def]
    \\ fs[holKernelTheory.raise_Failure_def])
  >~ [‘do_opapp [is_type_v; v]’] >- (
    drule_all is_type_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac is_type_v_thm
    \\ fs[state_ok_def]
    \\ drule_all v_ok_TYPE_TYPE_HEAD \\ strip_tac
    \\ `perms_ok ∅ v ∧ perms_ok ∅ is_type_v`
    by simp[TYPE_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all Arrow1 \\ strip_tac \\ fs[]
    \\ qexists_tac`ctxt` \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ simp[SF SFY_ss, BOOL_v_ok])
  >~ [‘do_opapp [is_vartype_v; v]’] >- (
    drule_all is_vartype_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac is_vartype_v_thm
    \\ fs[state_ok_def]
    \\ drule_all v_ok_TYPE_TYPE_HEAD \\ strip_tac
    \\ `perms_ok ∅ v ∧ perms_ok ∅ is_vartype_v`
    by simp[TYPE_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all Arrow1 \\ strip_tac \\ fs[]
    \\ qexists_tac`ctxt` \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ simp[SF SFY_ss, BOOL_v_ok])
  >~ [‘do_opapp [call_tyvars_v; v]’] >- (
    drule_all call_tyvars_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac call_tyvars_v_thm
    \\ fs[state_ok_def]
    \\ drule_all v_ok_TYPE_TYPE_HEAD \\ strip_tac
    \\ `perms_ok ∅ v ∧ perms_ok ∅ call_tyvars_v`
    by simp[TYPE_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all Arrow1
    \\ drule_all Arrow1 \\ strip_tac \\ fs[]
    \\ qexists_tac`ctxt` \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ simp[SF SFY_ss]
    \\ drule_then irule LIST_TYPE_v_ok
    \\ simp[STRING_TYPE_v_ok, SF SFY_ss])
  >~ [‘do_opapp [constants_v; v]’] >- (
    drule_all constants_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac constants_v_thm
    \\ fs[state_ok_def]
    \\ `perms_ok kernel_perms v ∧ perms_ok kernel_perms constants_v`
    by simp[UNIT_TYPE_perms_ok]
    \\ drule_all ArrowM1 \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ qexists_tac`ctxt` \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ fs[holKernelTheory.constants_def]
    \\ fs[holKernelTheory.get_the_term_constants_def]
    \\ gvs[SF SFY_ss]
    \\ drule_then irule LIST_TYPE_v_ok
    \\ rw[EVERY_MEM]
    \\ drule_then irule PAIR_TYPE_v_ok
    \\ conj_tac >- MATCH_ACCEPT_TAC STRING_TYPE_v_ok
    \\ rw[]
    \\ irule TYPE_IMP_v_ok
    \\ first_assum $ irule_at $ Any
    \\ drule the_term_constants_TYPE
    \\ simp[EVERY_MEM, FORALL_PROD]
    \\ Cases_on`x` \\ fs[SF SFY_ss])
  >~ [‘do_opapp [get_const_type_v; v]’] >- (
    drule_all get_const_type_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac get_const_type_v_thm
    \\ fs[state_ok_def]
    \\ fs[STRING_TYPE_HEAD_def]
    \\ `perms_ok kernel_perms v ∧ perms_ok kernel_perms get_const_type_v`
    by simp[STRING_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all ArrowM1 \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ qexists_tac`ctxt` \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ fs[holKernelTheory.get_const_type_def, ml_monadBaseTheory.st_ex_bind_def]
    \\ fs[holKernelTheory.get_the_term_constants_def]
    \\ drule assoc_thm
    \\ strip_tac
    \\ fs[SF SFY_ss]
    \\ drule the_term_constants_TYPE
    \\ simp[EVERY_MEM, FORALL_PROD] \\ strip_tac
    \\ Cases_on`r` \\ fs[]
    >- (drule_at_then Any irule TYPE_IMP_v_ok \\ simp[SF SFY_ss])
    \\ rename [‘M_failure ff’] \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss])
  >~ [‘do_opapp [new_constant_v; v]’] >- (
    drule_all new_constant_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac new_constant_v_thm
    \\ fs[state_ok_def]
    \\ `∃pa. PAIR_TYPE STRING_TYPE TYPE_TYPE pa v`
    by (
      irule v_ok_PAIR_TYPE_HEAD
      \\ first_assum $ irule_at Any
      \\ first_assum $ irule_at Any
      \\ simp[STRING_TYPE_HEAD_def]
      \\ MATCH_ACCEPT_TAC v_ok_TYPE_TYPE_HEAD )
    \\ PairCases_on`pa`
    \\ `perms_ok kernel_perms v ∧ perms_ok kernel_perms new_constant_v`
    by (
      simp[]
      \\ drule_at_then Any irule PAIR_TYPE_perms_ok
      \\ simp[STRING_TYPE_perms_ok, TYPE_TYPE_perms_ok, SF SFY_ss])
    \\ drule_all ArrowM1 \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ fs[ml_translatorTheory.PAIR_TYPE_def]
    \\ fs[v_ok_Conv_NONE]
    \\ drule_then drule v_ok_TYPE \\ strip_tac
    \\ drule_then drule new_constant_thm
    \\ disch_then(qspec_then`pa0`mp_tac) \\ simp[]
    \\ reverse TOP_CASE_TAC \\ simp[] \\ strip_tac \\ fs[ml_translatorTheory.UNIT_TYPE_def, v_ok_Conv_NONE]
    >- (
      first_assum $ irule_at Any
      \\ fs[SF SFY_ss]
      \\ rename1 `M_failure ff`
      \\ Cases_on`ff` \\ gvs[]
      \\ drule_then irule HOL_EXN_TYPE_Fail_v_ok )
    \\ first_assum $ irule_at Any
    \\ simp[]
    \\ reverse conj_tac >- metis_tac[v_ok_APPEND, CONS_APPEND]
    \\ metis_tac[ref_ok_APPEND, CONS_APPEND])
  >~ [‘do_opapp [call_type_of_v; v]’] >- (
    drule_all call_type_of_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac call_type_of_v_thm
    \\ fs[state_ok_def]
    \\ drule_all v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ imp_res_tac v_ok_TERM \\ fs []
    \\ `perms_ok kernel_perms v ∧ perms_ok kernel_perms call_type_of_v`
    by simp[TERM_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all ArrowM1 \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ first_assum $ irule_at $ Pos $ hd
    \\ fs [SF SFY_ss]
    \\ drule_then drule type_of_thm
    \\ strip_tac \\ fs[] \\ gvs[]
    \\ drule_at_then Any irule TYPE_IMP_v_ok
    \\ drule_at Any term_type
    \\ fs[STATE_def] \\ rw[] \\ gvs[])
  >~ [‘do_opapp [is_var_v; v]’] >- (
    drule_all is_var_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac is_var_v_thm
    \\ fs[state_ok_def]
    \\ drule_all v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ `perms_ok ∅ v ∧ perms_ok ∅ is_var_v`
    by simp[TERM_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all Arrow1 \\ strip_tac \\ fs[]
    \\ qexists_tac`ctxt` \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ simp[SF SFY_ss, BOOL_v_ok])
  >~ [‘do_opapp [is_const_v; v]’] >- (
    drule_all is_const_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac is_const_v_thm
    \\ fs[state_ok_def]
    \\ drule_all v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ `perms_ok ∅ v ∧ perms_ok ∅ is_const_v`
    by simp[TERM_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all Arrow1 \\ strip_tac \\ fs[]
    \\ qexists_tac`ctxt` \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ simp[SF SFY_ss, BOOL_v_ok])
  >~ [‘do_opapp [is_abs_v; v]’] >- (
    drule_all is_abs_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac is_abs_v_thm
    \\ fs[state_ok_def]
    \\ drule_all v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ `perms_ok ∅ v ∧ perms_ok ∅ is_abs_v`
    by simp[TERM_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all Arrow1 \\ strip_tac \\ fs[]
    \\ qexists_tac`ctxt` \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ simp[SF SFY_ss, BOOL_v_ok])
  >~ [‘do_opapp [is_comb_v; v]’] >- (
    drule_all is_comb_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac is_comb_v_thm
    \\ fs[state_ok_def]
    \\ drule_all v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ `perms_ok ∅ v ∧ perms_ok ∅ is_comb_v`
    by simp[TERM_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all Arrow1 \\ strip_tac \\ fs[]
    \\ qexists_tac`ctxt` \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ simp[SF SFY_ss, BOOL_v_ok])
  >~ [‘do_opapp [mk_var_v; v]’] >- (
    drule_all mk_var_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac mk_var_v_thm
    \\ fs[state_ok_def]
    \\ `∃pa. PAIR_TYPE STRING_TYPE TYPE_TYPE pa v`
    by (
      irule v_ok_PAIR_TYPE_HEAD
      \\ first_assum $ irule_at Any
      \\ first_assum $ irule_at Any
      \\ simp[STRING_TYPE_HEAD_def]
      \\ MATCH_ACCEPT_TAC v_ok_TYPE_TYPE_HEAD )
    \\ PairCases_on`pa`
    \\ `perms_ok ∅ v ∧ perms_ok ∅ mk_var_v` by (
      simp[]
      \\ drule_at_then Any irule PAIR_TYPE_perms_ok
      \\ simp[STRING_TYPE_perms_ok, TYPE_TYPE_perms_ok, SF SFY_ss])
    \\ drule_all Arrow1 \\ strip_tac \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ simp[SF SFY_ss]
    \\ irule TERM_IMP_v_ok
    \\ first_assum $ irule_at $ Any
    \\ irule mk_var_thm
    \\ simp[SF SFY_ss]
    \\ fs[ml_translatorTheory.PAIR_TYPE_def]
    \\ rveq \\ fs[v_ok_Conv_NONE]
    \\ drule_then (drule_then irule) v_ok_TYPE)
  >~ [‘do_opapp [mk_const_v; v]’] >- (
    drule_all mk_const_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac mk_const_v_thm
    \\ fs[state_ok_def]
    \\ `∃pa. PAIR_TYPE STRING_TYPE (LIST_TYPE (PAIR_TYPE TYPE_TYPE TYPE_TYPE)) pa v`
    by (
      irule v_ok_PAIR_TYPE_HEAD
      \\ first_assum $ irule_at Any
      \\ first_assum $ irule_at Any
      \\ simp[STRING_TYPE_HEAD_def]
      \\ rpt strip_tac
      \\ irule v_ok_LIST_PAIR_TYPE_HEAD
      \\ first_assum $ irule_at Any
      \\ first_assum $ irule_at Any
      \\ MATCH_ACCEPT_TAC v_ok_TYPE_TYPE_HEAD )
    \\ PairCases_on`pa`
    \\ `perms_ok kernel_perms v ∧ perms_ok kernel_perms mk_const_v` by (
      simp[]
      \\ drule_at_then Any irule PAIR_TYPE_perms_ok
      \\ simp[STRING_TYPE_perms_ok, SF SFY_ss]
      \\ rpt strip_tac \\ drule_at_then Any irule LIST_TYPE_perms_ok
      \\ rpt strip_tac \\ drule_at_then Any irule PAIR_TYPE_perms_ok
      \\ MATCH_ACCEPT_TAC TYPE_TYPE_perms_ok)
    \\ drule_all ArrowM1 \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ first_assum $ irule_at $ Pos $ hd
    \\ simp[SF SFY_ss]
    \\ drule_then drule mk_const_thm
    \\ fs[ml_translatorTheory.PAIR_TYPE_def]
    \\ rveq \\ fs[v_ok_Conv_NONE]
    \\ impl_tac
    >- (
      `EVERY ((λctxt p. TYPE ctxt (FST p) ∧ TYPE ctxt (SND p)) ctxt) pa1`
      suffices_by rw[EVERY_MEM, FORALL_PROD]
      \\ drule_at_then Any irule v_ok_LIST
      \\ simp[ml_translatorTheory.PAIR_TYPE_def, FORALL_PROD, PULL_EXISTS]
      \\ rw[v_ok_Conv_NONE]
      \\ metis_tac[v_ok_TYPE])
    \\ strip_tac
    \\ Cases_on`r` \\ gvs[]
    >- simp[SF SFY_ss, TERM_IMP_v_ok]
    \\ rename [‘M_failure ff’] \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss])
  >~ [‘do_opapp [mk_abs_v; v]’] >- (
    drule_all mk_abs_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac mk_abs_v_thm
    \\ fs[state_ok_def]
    \\ `∃pa. PAIR_TYPE TERM_TYPE TERM_TYPE pa v`
    by (
      irule v_ok_PAIR_TYPE_HEAD
      \\ first_assum $ irule_at Any
      \\ first_assum $ irule_at Any
      \\ MATCH_ACCEPT_TAC v_ok_TERM_TYPE_HEAD )
    \\ PairCases_on`pa`
    \\ `perms_ok kernel_perms v ∧ perms_ok kernel_perms mk_abs_v` by (
      simp[]
      \\ drule_at_then Any irule PAIR_TYPE_perms_ok
      \\ MATCH_ACCEPT_TAC TERM_TYPE_perms_ok)
    \\ drule_all ArrowM1 \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ first_assum $ irule_at $ Pos $ hd
    \\ simp[SF SFY_ss]
    \\ drule mk_abs_thm
    \\ fs[ml_translatorTheory.PAIR_TYPE_def]
    \\ rveq \\ fs[v_ok_Conv_NONE]
    \\ imp_res_tac v_ok_TERM
    \\ disch_then drule \\ simp[]
    \\ strip_tac
    \\ Cases_on`r` \\ fs[] \\ gvs[]
    \\ simp[SF SFY_ss, TERM_IMP_v_ok]
    \\ rename1 ‘M_failure ff’ \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss])
  >~ [‘do_opapp [mk_comb_v; v]’] >- (
    drule_all mk_comb_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac mk_comb_v_thm
    \\ fs[state_ok_def]
    \\ `∃pa. PAIR_TYPE TERM_TYPE TERM_TYPE pa v`
    by (
      irule v_ok_PAIR_TYPE_HEAD
      \\ first_assum $ irule_at Any
      \\ first_assum $ irule_at Any
      \\ MATCH_ACCEPT_TAC v_ok_TERM_TYPE_HEAD )
    \\ PairCases_on`pa`
    \\ `perms_ok kernel_perms v ∧ perms_ok kernel_perms mk_comb_v` by (
      simp[]
      \\ drule_at_then Any irule PAIR_TYPE_perms_ok
      \\ MATCH_ACCEPT_TAC TERM_TYPE_perms_ok)
    \\ drule_all ArrowM1 \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ first_assum $ irule_at $ Pos $ hd
    \\ simp[SF SFY_ss]
    \\ drule mk_comb_thm
    \\ fs[ml_translatorTheory.PAIR_TYPE_def]
    \\ rveq \\ fs[v_ok_Conv_NONE]
    \\ imp_res_tac v_ok_TERM
    \\ disch_then drule \\ simp[]
    \\ strip_tac
    \\ Cases_on`r` \\ fs[] \\ gvs[]
    \\ simp[SF SFY_ss, TERM_IMP_v_ok]
    \\ rename1 ‘M_failure ff’ \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss])
  >~ [‘do_opapp [dest_var_v; v]’] >- (
    drule_all dest_var_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac dest_var_v_thm
    \\ fs[state_ok_def]
    \\ drule_all v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ imp_res_tac v_ok_TERM \\ fs []
    \\ `perms_ok kernel_perms v ∧ perms_ok kernel_perms dest_var_v`
    by simp[TERM_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all ArrowM1 \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ qexists_tac`ctxt` \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ fs [SF SFY_ss]
    \\ drule_all dest_var_thm \\ strip_tac
    \\ Cases_on ‘r’ \\ fs []
    >- (
      drule_then irule PAIR_TYPE_v_ok
      \\ Cases_on`a` \\ simp[STRING_TYPE_v_ok,SF SFY_ss]
      \\ fs[] \\ simp[TYPE_IMP_v_ok, SF SFY_ss] )
    \\ rename [‘M_failure ff’] \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss])
  >~ [‘do_opapp [dest_const_v; v]’] >- (
    drule_all dest_const_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac dest_const_v_thm
    \\ fs[state_ok_def]
    \\ drule_all v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ imp_res_tac v_ok_TERM \\ fs []
    \\ `perms_ok kernel_perms v ∧ perms_ok kernel_perms dest_const_v`
    by simp[TERM_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all ArrowM1 \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ qexists_tac`ctxt` \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ fs [SF SFY_ss]
    \\ drule_all dest_const_thm \\ strip_tac
    \\ Cases_on ‘r’ \\ fs []
    >- (
      drule_then irule PAIR_TYPE_v_ok
      \\ Cases_on`a` \\ simp[STRING_TYPE_v_ok,SF SFY_ss]
      \\ fs[] \\ simp[TYPE_IMP_v_ok, SF SFY_ss] )
    \\ rename [‘M_failure ff’] \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss]
    \\ qhdtm_x_assum`dest_const`mp_tac
    \\ simp[holKernelTheory.dest_const_def]
    \\ CASE_TAC \\ simp[ml_monadBaseTheory.st_ex_return_def]
    \\ simp[holKernelTheory.raise_Failure_def])
  >~ [‘do_opapp [dest_comb_v; v]’] >- (
    drule_all dest_comb_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac dest_comb_v_thm
    \\ fs[state_ok_def]
    \\ drule_all v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ imp_res_tac v_ok_TERM \\ fs []
    \\ `perms_ok kernel_perms v ∧ perms_ok kernel_perms dest_comb_v`
    by simp[TERM_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all ArrowM1 \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ qexists_tac`ctxt` \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ fs [SF SFY_ss]
    \\ drule_all dest_comb_thm \\ strip_tac
    \\ Cases_on ‘r’ \\ fs []
    >- (
      drule_then irule PAIR_TYPE_v_ok
      \\ Cases_on`a` \\ fs[]
      \\ simp[TERM_IMP_v_ok, SF SFY_ss] )
    \\ rename [‘M_failure ff’] \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss])
  >~ [‘do_opapp [dest_abs_v; v]’] >- (
    drule_all dest_abs_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac dest_abs_v_thm
    \\ fs[state_ok_def]
    \\ drule_all v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ imp_res_tac v_ok_TERM \\ fs []
    \\ `perms_ok kernel_perms v ∧ perms_ok kernel_perms dest_abs_v`
    by simp[TERM_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all ArrowM1 \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ qexists_tac`ctxt` \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ fs [SF SFY_ss]
    \\ drule_all dest_abs_thm \\ strip_tac
    \\ Cases_on ‘r’ \\ fs []
    >- (
      drule_then irule PAIR_TYPE_v_ok
      \\ Cases_on`a` \\ fs[]
      \\ simp[TERM_IMP_v_ok, SF SFY_ss] )
    \\ rename [‘M_failure ff’] \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss])
  >~ [‘do_opapp [call_frees_v; v]’] >- (
    drule_all call_frees_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac call_frees_v_thm
    \\ fs[state_ok_def]
    \\ drule_then drule v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ `perms_ok ∅ v ∧ perms_ok ∅ call_frees_v`
    by simp[TERM_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all Arrow1 \\ strip_tac \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ simp[SF SFY_ss]
    \\ drule_then irule LIST_TYPE_v_ok
    \\ rw[EVERY_MEM]
    \\ drule_then drule v_ok_TERM \\ strip_tac
    \\ drule_then drule MEM_frees \\ strip_tac
    \\ drule_at_then(Pat`TERM_TYPE`) irule TERM_IMP_v_ok
    \\ rveq
    \\ simp[TERM_def]
    \\ simp[holSyntaxTheory.term_ok_def]
    \\ fs[TYPE_def])
  >~ [‘do_opapp [freesl_v; v]’] >- (
    drule_all freesl_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac freesl_v_thm
    \\ fs[state_ok_def]
    \\ drule_then drule v_ok_LIST_TERM_TYPE_HEAD \\ strip_tac
    \\ `perms_ok ∅ v ∧ perms_ok ∅ freesl_v`
    by simp[LIST_TERM_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all Arrow1 \\ strip_tac \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ simp[SF SFY_ss]
    \\ drule_then irule LIST_TYPE_v_ok
    \\ rw[EVERY_MEM]
    \\ drule_then drule v_ok_LIST_TERM \\ strip_tac
    \\ drule_then drule MEM_freesl \\ strip_tac
    \\ drule_at_then(Pat`TERM_TYPE`) irule TERM_IMP_v_ok
    \\ rveq
    \\ simp[TERM_def]
    \\ simp[holSyntaxTheory.term_ok_def]
    \\ fs[TYPE_def])
  >~ [‘do_opapp [call_type_vars_in_term_v; v]’] >- (
    drule_all call_type_vars_in_term_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac call_type_vars_in_term_v_thm
    \\ fs[state_ok_def]
    \\ drule_then drule v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ `perms_ok ∅ v ∧ perms_ok ∅ call_type_vars_in_term_v`
    by simp[TERM_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all Arrow1 \\ strip_tac \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ simp[SF SFY_ss]
    \\ drule_then irule LIST_TYPE_v_ok
    \\ simp[EVERY_MEM, SF SFY_ss, STRING_TYPE_v_ok])
  >~ [‘do_opapp [rand_v; v]’] >- (
    drule_all rand_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac rand_v_thm
    \\ fs[state_ok_def]
    \\ drule_all v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ imp_res_tac v_ok_TERM \\ fs []
    \\ `perms_ok kernel_perms v ∧ perms_ok kernel_perms rand_v`
    by simp[TERM_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all ArrowM1 \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ qexists_tac`ctxt` \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ fs [SF SFY_ss]
    \\ drule_all rand_thm \\ strip_tac
    \\ Cases_on ‘r’ \\ fs []
    >- simp[TERM_IMP_v_ok, SF SFY_ss]
    \\ rename [‘M_failure ff’] \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss]
    \\ fs[holKernelTheory.rand_def]
    \\ Cases_on`tm` \\ fs[ml_monadBaseTheory.st_ex_return_def]
    \\ fs[holKernelTheory.raise_Failure_def])
  >~ [‘do_opapp [rator_v; v]’] >- (
    drule_all rator_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac rator_v_thm
    \\ fs[state_ok_def]
    \\ drule_all v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ imp_res_tac v_ok_TERM \\ fs []
    \\ `perms_ok kernel_perms v ∧ perms_ok kernel_perms rator_v`
    by simp[TERM_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all ArrowM1 \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ qexists_tac`ctxt` \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ fs [SF SFY_ss]
    \\ drule_all rator_thm \\ strip_tac
    \\ Cases_on ‘r’ \\ fs []
    >- simp[TERM_IMP_v_ok, SF SFY_ss]
    \\ rename [‘M_failure ff’] \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss]
    \\ fs[holKernelTheory.rator_def]
    \\ Cases_on`tm` \\ fs[ml_monadBaseTheory.st_ex_return_def]
    \\ fs[holKernelTheory.raise_Failure_def])
  >~ [‘do_opapp [dest_eq_v; v]’] >- (
    drule_all dest_eq_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac dest_eq_v_thm
    \\ fs[state_ok_def]
    \\ drule_all v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ imp_res_tac v_ok_TERM \\ fs []
    \\ `perms_ok kernel_perms v ∧ perms_ok kernel_perms dest_eq_v`
    by simp[TERM_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all ArrowM1 \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ qexists_tac`ctxt` \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ fs [SF SFY_ss]
    \\ drule_all dest_eq_thm \\ strip_tac
    \\ Cases_on ‘r’ \\ fs []
    >- (
      drule_then irule PAIR_TYPE_v_ok
      \\ Cases_on`a` \\ fs[]
      \\ simp[TERM_IMP_v_ok, SF SFY_ss] )
    \\ rename [‘M_failure ff’] \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss])
  >~ [‘do_opapp [dest_thm_v; v]’] >- (
    drule_all dest_thm_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac dest_thm_v_thm
    \\ fs[state_ok_def]
    \\ drule_then drule v_ok_THM_TYPE_HEAD \\ strip_tac
    \\ `perms_ok ∅ v ∧ perms_ok ∅ dest_thm_v`
    by simp[THM_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all Arrow1 \\ strip_tac \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ simp[SF SFY_ss]
    \\ drule_then irule PAIR_TYPE_v_ok
    \\ Cases_on`dest_thm th`
    \\ drule_then drule v_ok_THM \\ strip_tac
    \\ drule_all dest_thm_thm
    \\ simp[SF SFY_ss, TERM_IMP_v_ok]
    \\ rpt strip_tac
    \\ drule_then irule LIST_TYPE_v_ok
    \\ gvs[EVERY_MEM] \\ rw[]
    \\ res_tac
    \\ simp[SF SFY_ss, TERM_IMP_v_ok])
  >~ [‘do_opapp [hyp_v; v]’] >- (
    drule_all hyp_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac hyp_v_thm
    \\ fs[state_ok_def]
    \\ drule_then drule v_ok_THM_TYPE_HEAD \\ strip_tac
    \\ `perms_ok ∅ v ∧ perms_ok ∅ hyp_v`
    by simp[THM_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all Arrow1 \\ strip_tac \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ simp[SF SFY_ss]
    \\ drule_then irule LIST_TYPE_v_ok
    \\ drule_then drule v_ok_THM \\ strip_tac
    \\ drule_then drule hyp_thm \\ rw[EVERY_MEM]
    \\ res_tac
    \\ simp[SF SFY_ss, TERM_IMP_v_ok])
  >~ [‘do_opapp [refl_v; v]’] >- (
    drule_all refl_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac refl_v_thm
    \\ fs[state_ok_def]
    \\ drule_then drule v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ ‘perms_ok kernel_perms v ∧ perms_ok kernel_perms refl_v’ by
         fs [TERM_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all ArrowM1 \\ strip_tac \\ fs []
    \\ disj2_tac
    \\ first_assum $ irule_at $ Pos $ hd
    \\ fs [SF SFY_ss]
    \\ drule_then drule v_ok_TERM \\ strip_tac
    \\ drule_then (drule_then drule) REFL_thm
    \\ strip_tac \\ gvs[]
    \\ Cases_on ‘r’ \\ fs []
    \\ imp_res_tac THM_IMP_v_ok \\ gvs []
    \\ rename [‘M_failure ff’] \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss])
  >~ [‘do_opapp [mk_comb_1_v; v]’] >- (
    drule_all mk_comb_1_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac mk_comb_1_v_thm
    \\ fs[state_ok_def]
    \\ `∃pa. PAIR_TYPE THM_TYPE THM_TYPE pa v`
    by (
      drule_at_then Any irule v_ok_PAIR_TYPE_HEAD
      \\ first_assum $ irule_at Any
      \\ simp[SF SFY_ss, v_ok_THM_TYPE_HEAD] )
    \\ PairCases_on`pa`
    \\ drule_at_then Any (drule_at Any) v_ok_PAIR
    \\ CONV_TAC(DEPTH_CONV BETA_CONV)
    \\ disch_then(qspecl_then[`THM`,`THM`]mp_tac)
    \\ simp[SF SFY_ss, v_ok_THM] \\ strip_tac
    \\ ‘perms_ok kernel_perms v ∧ perms_ok kernel_perms mk_comb_1_v’
    by ( simp[]
         \\ drule_at_then Any irule PAIR_TYPE_perms_ok
         \\ fs [THM_TYPE_perms_ok, SF SFY_ss] )
    \\ drule_all ArrowM1 \\ strip_tac \\ fs []
    \\ disj2_tac
    \\ first_assum $ irule_at $ Pos $ hd
    \\ fs [SF SFY_ss]
    \\ drule_all MK_COMB_thm
    \\ strip_tac \\ gvs[]
    \\ Cases_on ‘r’ \\ fs []
    \\ imp_res_tac THM_IMP_v_ok \\ gvs []
    \\ rename [‘M_failure ff’] \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss])
  >~ [‘do_opapp [assume_v; v]’] >- (
    drule_all assume_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac assume_v_thm
    \\ fs[state_ok_def]
    \\ drule_then drule v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ ‘perms_ok kernel_perms v ∧ perms_ok kernel_perms assume_v’ by
         fs [TERM_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all ArrowM1 \\ strip_tac \\ fs []
    \\ disj2_tac
    \\ first_assum $ irule_at $ Pos $ hd
    \\ fs [SF SFY_ss]
    \\ drule_then drule v_ok_TERM \\ strip_tac
    \\ drule_all ASSUME_thm
    \\ strip_tac \\ gvs[]
    \\ Cases_on ‘r’ \\ fs []
    \\ imp_res_tac THM_IMP_v_ok \\ gvs []
    \\ rename [‘M_failure ff’] \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss])
  >~ [‘do_opapp [axioms_v; v]’] >- (
    drule_all axioms_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac axioms_v_thm
    \\ fs[state_ok_def]
    \\ `perms_ok kernel_perms v ∧ perms_ok kernel_perms axioms_v`
    by simp[UNIT_TYPE_perms_ok]
    \\ drule_all ArrowM1 \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ qexists_tac`ctxt` \\ fs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ fs[holKernelTheory.axioms_def]
    \\ fs[holKernelTheory.get_the_axioms_def]
    \\ gvs[SF SFY_ss]
    \\ drule_then irule LIST_TYPE_v_ok
    \\ rw[EVERY_MEM]
    \\ irule THM_IMP_v_ok
    \\ first_assum $ irule_at $ Any
    \\ drule the_axioms_THM
    \\ simp[EVERY_MEM])
  >~ [‘do_opapp [new_axiom_v; v]’] >- (
    drule_all new_axiom_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac new_axiom_v_thm
    \\ fs[state_ok_def]
    \\ drule_then drule v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ `perms_ok kernel_perms v ∧ perms_ok kernel_perms new_axiom_v`
    by simp[TERM_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all ArrowM1 \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ drule_then drule v_ok_TERM \\ strip_tac
    \\ drule_then drule new_axiom_thm
    \\ simp[]
    \\ reverse TOP_CASE_TAC \\ simp[] \\ strip_tac
    >- (
      first_assum $ irule_at Any
      \\ fs[SF SFY_ss]
      \\ rename1 `M_failure ff`
      \\ Cases_on`ff` \\ gvs[]
      \\ drule_then irule HOL_EXN_TYPE_Fail_v_ok )
    \\ first_assum $ irule_at Any
    \\ gvs[SF SFY_ss, THM_IMP_v_ok]
    \\ reverse conj_tac >- metis_tac[v_ok_APPEND, CONS_APPEND]
    \\ metis_tac[ref_ok_APPEND, CONS_APPEND])
  >~ [‘do_opapp [new_basic_definition_v; v]’] >- (
    drule_all new_basic_definition_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac new_basic_definition_v_thm
    \\ fs[state_ok_def]
    \\ drule_then drule v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ `perms_ok kernel_perms v ∧ perms_ok kernel_perms new_basic_definition_v`
    by simp[TERM_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all ArrowM1 \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ drule_then drule v_ok_TERM \\ strip_tac
    \\ drule_then drule new_basic_definition_thm
    \\ simp[]
    \\ reverse TOP_CASE_TAC \\ simp[] \\ strip_tac
    >- (
      first_assum $ irule_at Any
      \\ fs[SF SFY_ss]
      \\ rename1 `M_failure ff`
      \\ Cases_on`ff` \\ gvs[]
      \\ drule_then irule HOL_EXN_TYPE_Fail_v_ok )
    \\ first_assum $ irule_at Any
    \\ gvs[SF SFY_ss, THM_IMP_v_ok]
    \\ reverse conj_tac >- metis_tac[v_ok_APPEND, CONS_APPEND]
    \\ metis_tac[ref_ok_APPEND, CONS_APPEND])
  >~ [‘do_opapp [new_basic_type_definition_v; v]’] >- (
    drule_all new_basic_type_definition_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac new_basic_type_definition_v_thm
    \\ qmatch_asmsub_abbrev_tac`PURE A`
    \\ `∃pa. A pa v`
    by (
      qunabbrev_tac`A`
      \\ drule_at_then(Pat`PAIR_TYPE_HEAD`)irule v_ok_PAIR_TYPE_HEAD
      \\ first_assum $ irule_at Any
      \\ simp[SF SFY_ss, STRING_TYPE_HEAD_def]
      \\ rpt strip_tac
      \\ drule_at_then(Pat`PAIR_TYPE_HEAD`)irule v_ok_PAIR_TYPE_HEAD
      \\ first_assum $ irule_at Any
      \\ simp[SF SFY_ss, STRING_TYPE_HEAD_def]
      \\ rpt strip_tac
      \\ drule_at_then(Pat`PAIR_TYPE_HEAD`)irule v_ok_PAIR_TYPE_HEAD
      \\ first_assum $ irule_at Any
      \\ simp[SF SFY_ss, STRING_TYPE_HEAD_def, v_ok_THM_TYPE_HEAD])
    \\ PairCases_on`pa`
    \\ fs[state_ok_def, Abbr`A`]
    \\ drule ArrowM1
    \\ rpt(disch_then drule)
    \\ impl_tac >- (
      simp[]
      \\ drule_at_then Any irule PAIR_TYPE_perms_ok
      \\ rw[STRING_TYPE_perms_ok, SF SFY_ss]
      \\ drule_at_then Any irule PAIR_TYPE_perms_ok
      \\ rw[STRING_TYPE_perms_ok, SF SFY_ss]
      \\ drule_at_then Any irule PAIR_TYPE_perms_ok
      \\ rw[THM_TYPE_perms_ok, STRING_TYPE_perms_ok, SF SFY_ss])
    \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ drule_at_then Any (drule_at Any) v_ok_PAIR
    \\ disch_then(qspecl_then[`λctxt. THM ctxt o SND o SND`,`K (K T)`]mp_tac)
    \\ simp[]
    \\ impl_tac
    >- (
      rpt strip_tac
      \\ drule_at_then Any (drule_at Any) v_ok_PAIR
      \\ disch_then(qspecl_then[`λctxt. THM ctxt o SND`,`K (K T)`]mp_tac)
      \\ simp[]
      \\ disch_then irule
      \\ rpt strip_tac
      \\ drule_at_then Any (drule_at Any) v_ok_PAIR
      \\ disch_then(qspecl_then[`λctxt. THM ctxt`,`K (K T)`]mp_tac)
      \\ simp[SF SFY_ss, v_ok_THM])
    \\ strip_tac
    \\ drule_all new_basic_type_definition_thm
    \\ disch_then(qspecl_then[`pa0`,`pa2`,`pa1`]mp_tac)
    \\ simp[]
    \\ reverse TOP_CASE_TAC \\ simp[] \\ strip_tac
    >- (
      first_assum $ irule_at Any
      \\ fs[SF SFY_ss]
      \\ rename1 `M_failure ff`
      \\ Cases_on`ff` \\ gvs[]
      \\ drule_then irule HOL_EXN_TYPE_Fail_v_ok )
    \\ Cases_on`a` \\ fs[]
    \\ first_assum $ irule_at Any
    \\ drule PAIR_TYPE_v_ok
    \\ simp[SF SFY_ss, THM_IMP_v_ok]
    \\ disch_then kall_tac
    \\ reverse conj_tac >- metis_tac[v_ok_APPEND]
    \\ metis_tac[ref_ok_APPEND])
  >~ [‘do_opapp [new_specification_v; v]’] >- (
    drule_all new_specification_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ assume_tac new_specification_v_thm
    \\ drule_then drule v_ok_THM_TYPE_HEAD \\ strip_tac
    \\ fs[state_ok_def]
    \\ drule ArrowM1
    \\ rpt(disch_then drule)
    \\ impl_tac >- simp[SF SFY_ss, THM_TYPE_perms_ok]
    \\ strip_tac \\ fs[]
    \\ disj2_tac
    \\ drule_at_then Any (drule_at Any) v_ok_THM
    \\ strip_tac
    \\ drule_then drule new_specification_thm
    \\ simp[]
    \\ reverse TOP_CASE_TAC \\ simp[] \\ strip_tac
    >- (
      first_assum $ irule_at Any
      \\ fs[SF SFY_ss]
      \\ rename1 `M_failure ff`
      \\ Cases_on`ff` \\ gvs[]
      \\ drule_then irule HOL_EXN_TYPE_Fail_v_ok )
    \\ first_assum $ irule_at Any
    \\ gvs[SF SFY_ss, THM_IMP_v_ok]
    \\ reverse conj_tac >- metis_tac[v_ok_APPEND, CONS_APPEND]
    \\ metis_tac[ref_ok_APPEND, CONS_APPEND])

  >~ [‘do_opapp [Kernel_print_thm_v; v]’] >- (



    drule_all Kernel_print_thm_v_head
    \\ strip_tac \\ gvs[]
    >- (first_assum $ irule_at Any \\ simp[])
    \\ drule_then drule v_ok_THM_TYPE_HEAD \\ strip_tac
    \\ drule_then drule v_ok_THM \\ strip_tac
    \\ fs[Kernel_print_thm_v_def]
    \\ qmatch_asmsub_abbrev_tac`Closure cenv`
    \\ fs[do_opapp_def]
    \\ rveq
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[Ntimes evaluate_def 3, astTheory.pat_bindings_def, can_pmatch_all_def]
    \\ Cases_on`th`
    \\ imp_res_tac THM_TYPE_def
    \\ rveq
    \\ simp[pmatch_def]
    \\ qmatch_goalsub_abbrev_tac`TypeStamp "Sequent" sn`
    \\ `nsLookup cenv.c (Short"Sequent") = SOME (2, TypeStamp "Sequent" sn)`
    by (
      unabbrev_all_tac
      \\ CONV_TAC ml_progLib.nsLookup_conv \\ simp[]
      \\ CONV_TAC ml_progLib.nsLookup_conv )
    \\ simp[]
    \\ `nsLookup cenv.v (Short"the_context") = SOME the_context`
    by (
      unabbrev_all_tac
      \\ CONV_TAC ml_progLib.nsLookup_conv \\ simp[]
      \\ CONV_TAC ml_progLib.nsLookup_conv )
    \\ `nsLookup cenv.v (Short"!") = SOME deref_v`
    by (
      unabbrev_all_tac
      \\ CONV_TAC ml_progLib.nsLookup_conv \\ simp[]
      \\ CONV_TAC ml_progLib.nsLookup_conv )
    \\ simp[Ntimes evaluate_def 5]
    \\ simp[Once do_opapp_def]
    \\ simp[mlbasicsProgTheory.deref_v_def]
    \\ IF_CASES_TAC \\ simp[]
    \\ simp[Ntimes evaluate_def 2]
    \\ drule get_the_context_thm
    \\ simp[ml_monad_translatorTheory.EvalM_def]
    \\ fs[state_ok_def]
    \\ drule REFS_PRED_HOL_STORE
    \\ strip_tac
    \\ simp[Ntimes evaluate_def 2]
    \\ simp[Once dec_clock_def]
    \\ simp[Once dec_clock_def]
    \\ strip_tac
    \\ CASE_TAC \\ simp[]
    >- (strip_tac \\ gvs[dec_clock_def])
    \\ PairCases_on`x` \\ simp[]
    \\ first_assum(first_assum o resolve_then Any mp_tac)
    \\ pop_assum mp_tac
    \\ simp_tac(srw_ss())[]
    \\ strip_tac
    \\ simp[ml_monad_translatorTheory.MONAD_def]
    \\ simp[holKernelTheory.get_the_context_def]
    \\ Cases_on`list_result x2` \\ simp[]
    \\ CASE_TAC
    \\ CASE_TAC
    \\ strip_tac \\ simp[]
    \\ simp[Ntimes evaluate_def 8]
    \\ simp[namespaceTheory.nsOptBind_def]
    \\ `nsLookup cenv.v (Short"thm_to_string") = SOME thm_to_string_v`
    by (
      unabbrev_all_tac
      \\ CONV_TAC ml_progLib.nsLookup_conv \\ simp[]
      \\ CONV_TAC ml_progLib.nsLookup_conv )
    \\ simp[]
    \\ `(x0,x1) = (s.refs,s.ffi)`
    by fs[do_app_cases] \\ fs[]
    \\ Cases_on`do_opapp [thm_to_string_v; h]` \\ simp[]
    >- ( strip_tac \\ gvs[] )
    \\ rveq
    \\ PairCases_on`x` \\ simp[]
    \\ CASE_TAC >- ( strip_tac \\ gvs[] )
    \\ `∃v1 e1. x1 = Fun v1 e1`
    by (qpat_x_assum ‘do_opapp [thm_to_string_v; h] = SOME (x0,x1)’ mp_tac
        \\ once_rewrite_tac [thm_to_string_v_def]
        \\ rename [‘Closure eee _ (Fun _ xxx)’]
        \\ EVAL_TAC \\ rw [] \\ gvs [])
    \\ `do_partial_app thm_to_string_v h = SOME (Closure x0 v1 e1)`
    by (qpat_x_assum ‘do_opapp [thm_to_string_v; h] = SOME (x0,x1)’ mp_tac
        \\ once_rewrite_tac [thm_to_string_v_def]
        \\ rename [‘Closure eee _ (Fun _ xxx)’]
        \\ EVAL_TAC \\ rw [] \\ gvs [])
    \\ simp[Once evaluate_def]
    \\ qmatch_goalsub_abbrev_tac`do_opapp xx`
    \\ Cases_on`do_opapp xx` \\ simp[]
    >- ( strip_tac \\ gvs[dec_clock_def] )
    \\ ntac 2 CASE_TAC
    >- ( strip_tac \\ gvs[dec_clock_def] )
    \\ CASE_TAC
    \\ qunabbrev_tac`xx`
    \\ resolve_then (Pos hd)
         (drule_at_then (Pat`do_partial_app`)
           (drule_then $ drule_then $ drule_at Any))
           thm_to_string_v_thm Arrow2
    \\ simp[dec_clock_def]
    \\ qmatch_asmsub_abbrev_tac`LIST_TYPE UPDATE_TYPE st h`
    \\ disch_then(qspec_then`st`mp_tac)
    \\ impl_keep_tac
    >- (
      conj_asm1_tac >- metis_tac[]
      \\ simp[SF SFY_ss, THM_TYPE_perms_ok]
      \\ drule_at_then Any irule LIST_TYPE_perms_ok
      \\ simp[SF SFY_ss, UPDATE_TYPE_perms_ok])
    \\ strip_tac \\ gvs[]
    \\ simp[evaluate_def, namespaceTheory.nsOptBind_def]
    \\ qunabbrev_tac`cenv`
    \\ CONV_TAC(DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp[]
    \\ CONV_TAC(DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp[]
    \\ TOP_CASE_TAC
    \\ pop_assum mp_tac
    \\ TOP_CASE_TAC
    >- (strip_tac \\ gvs[])
    \\ TOP_CASE_TAC
    \\ CASE_TAC
    >- (strip_tac \\ gvs[])
    \\ strip_tac
    \\ qmatch_asmsub_abbrev_tac`nsLookup cenv.v _`
    \\ resolve_then Any (drule_then drule)
         Word8ProgTheory.word8_fromint_v_thm Arrow1
    \\ simp[perms_ok_Litv]
    \\ strip_tac \\ gvs[]
    >- (strip_tac \\ gvs[dec_clock_def])
    >- (strip_tac \\ gvs[dec_clock_def])
    \\ TOP_CASE_TAC
    \\ pop_assum mp_tac \\ TOP_CASE_TAC
    \\ pop_assum mp_tac \\ TOP_CASE_TAC
    \\ pop_assum mp_tac \\ TOP_CASE_TAC
    >- (rpt strip_tac \\ gvs[dec_clock_def])
    \\ TOP_CASE_TAC
    \\ CASE_TAC >- (rpt strip_tac \\ gvs[dec_clock_def])
    \\ strip_tac
    \\ qhdtm_x_assum`do_opapp`mp_tac
    \\ simp[do_opapp_def, Word8ArrayProgTheory.Word8Array_array_v_def]
    \\ strip_tac \\ rveq
    \\ pop_assum mp_tac
    \\ simp[evaluate_def]
    \\ strip_tac \\ rveq
    \\ strip_tac \\ rveq \\ simp[]
    \\ CASE_TAC >- (rpt strip_tac \\ gvs[dec_clock_def])
    \\ simp[evaluate_def]
    \\ fs[ml_translatorTheory.WORD_def]
    \\ simp[do_app_def]
    \\ simp[store_alloc_def]
    \\ strip_tac \\ rveq \\ simp[]
    \\ qmatch_asmsub_abbrev_tac`STRING_TYPE sstr rv`
    \\ Cases_on`sstr` \\ fs[ml_translatorTheory.STRING_TYPE_def]
    \\ gvs[]
    \\ simp[store_lookup_def]
    \\ simp[EL_LENGTH_APPEND]
    \\ reverse CASE_TAC
    >- ( rpt strip_tac \\ gvs[dec_clock_def] )
    \\ simp[store_assign_def, EL_LENGTH_APPEND]
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ EVAL_TAC )
    \\ simp[]
    \\ strip_tac \\ gvs[v_ok_Conv_NONE]
    \\ qexists_tac`ctxt` \\ gvs[dec_clock_def]
    \\ qhdtm_x_assum`call_FFI`mp_tac
    \\ simp[ffiTheory.call_FFI_def]
    \\ CASE_TAC
    \\ CASE_TAC
    \\ strip_tac \\ gvs[]
    \\ simp[ok_event_def]
    \\ simp[kernel_ffi_def]
    \\ conj_tac
    >- (
      first_assum $ irule_at Any
      \\ simp[thm2bytes_def, MAP_MAP_o, o_DEF]
      \\ AP_TERM_TAC
      \\ fs[GSYM mlstringTheory.implode_def]
      \\ fs[STATE_def]
      \\ EVAL_TAC)
    \\ first_assum $ irule_at Any
    \\ fs[kernel_loc_ok_def]
    \\ conj_tac
    >- (
      rw[]
      \\ first_x_assum drule
      \\ strip_tac
      \\ fs[LLOOKUP_THM, EL_APPEND1])
    \\ rw[]
    \\ first_x_assum drule
    \\ fs[LLOOKUP_THM]
    \\ rw[]
    \\ qmatch_asmsub_rename_tac`loc < LENGTH xx + 1`
    \\ Cases_on`loc < LENGTH xx` \\ fs[EL_APPEND1]
    \\ simp[EL_APPEND2]
    \\ `loc = LENGTH xx` by fs[]
    \\ simp[EL_LENGTH_APPEND]
    \\ simp[ref_ok_def])
QED

Theorem kernel_vals_twice_partial_app:
  ∀ctxt f. kernel_vals ctxt f ⇒
           ∀v g w. do_partial_app f v = SOME g ⇒
                   do_partial_app g w = NONE
Proof
  ho_match_mp_tac kernel_vals_ind \\ reverse (rw [])
  THEN1 (res_tac \\ metis_tac [NOT_SOME_NONE])
  \\ gvs [inferred_cases]
  \\ TRY (TRY (rename [‘TYPE_TYPE ty f’] \\ Cases_on ‘ty’ \\ gvs [TYPE_TYPE_def])
          \\ TRY (rename [‘TERM_TYPE tm f’] \\ Cases_on ‘tm’ \\ gvs [TERM_TYPE_def])
          \\ TRY (rename [‘THM_TYPE th f’] \\ Cases_on ‘th’ \\ gvs [THM_TYPE_def])
          \\ fs [do_partial_app_def] \\ NO_TAC)
  \\ rename [‘f ∈ kernel_funs’]
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘g’
  \\ fs [kernel_funs_def]
  \\ rewrite_tac [kernel_funs_v_def,do_partial_app_def]
  \\ EVAL_TAC \\ fs []
QED

Theorem kernel_vals_max_app:
  kernel_vals ctxt f ∧
  do_partial_app f v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ⇒
    f ∈ kernel_funs
Proof
  strip_tac
  \\ last_assum mp_tac
  \\ simp_tac std_ss [Once v_ok_cases]
  \\ strip_tac
  THEN1
   (gvs [inferred_cases]
    \\ TRY (rename [‘TYPE_TYPE ty f’] \\ Cases_on ‘ty’ \\ gvs [TYPE_TYPE_def])
    \\ TRY (rename [‘TERM_TYPE tm f’] \\ Cases_on ‘tm’ \\ gvs [TERM_TYPE_def])
    \\ TRY (rename [‘THM_TYPE th f’] \\ Cases_on ‘th’ \\ gvs [THM_TYPE_def])
    \\ fs [do_partial_app_def])
  \\ drule_all kernel_vals_twice_partial_app
  \\ disch_then (qspec_then ‘v’ mp_tac) \\ fs []
QED

Theorem kernel_vals_ok:
  ∀ctxt f.
    kernel_vals ctxt f ⇒
      ∀s v env exp s' res.
        do_opapp [f; v] = SOME (env, exp) ∧
        state_ok ctxt s ∧
        v_ok ctxt v ∧
        evaluate (s:'ffi state) env [exp] = (s', res) ⇒
          (∃abort. s'.ffi = s.ffi ∧ res = Rerr (Rabort abort)) ∨
          ∃ctxt'.
            state_ok ctxt' s' ∧
            (∀v. v_ok ctxt v ⇒ v_ok ctxt' v) ∧
            (∀v. kernel_vals ctxt v ⇒ kernel_vals ctxt' v) ∧
            (∀vs. res = Rval vs ⇒ EVERY (v_ok ctxt') vs) ∧
            (∀v. res = Rerr (Rraise v) ⇒ v_ok ctxt' v)
Proof
  rw [Once v_ok_cases]
  >~ [‘inferred ctxt f’] >- (
    irule_at Any inferred_ok
    \\ first_assum (irule_at Any)
    \\ first_assum (irule_at Any) \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  \\ rename [‘do_partial_app f v = SOME g’]
  \\ rw [DISJ_EQ_IMP]
  \\ reverse (Cases_on ‘f ∈ kernel_funs’)
  >- (gs [Once v_ok_cases, Once inferred_cases]
      >- (Cases_on ‘ty’ \\ gs [TYPE_TYPE_def, do_partial_app_def])
      >- (Cases_on ‘tm’ \\ gs [TERM_TYPE_def, do_partial_app_def])
      >- (Cases_on ‘th’ \\ gs [THM_TYPE_def, do_partial_app_def])
      \\ ‘kernel_vals ctxt f’
        by (irule v_ok_PartialApp
            \\ first_assum (irule_at (Pos hd))
            \\ gs [])
      \\ drule_all kernel_vals_max_app
      \\ rw [kernel_funs_def])
  \\ Cases_on ‘f = concl_v’ \\ gvs []
  THEN1 (* same proof goes for any one argument function *)
   (qsuff_tac ‘F’ \\ fs []
    \\ qpat_x_assum ‘do_partial_app _ _ = SOME _’ mp_tac
    \\ rewrite_tac [kernel_funs_v_def] \\ EVAL_TAC)
  \\ Cases_on ‘f = call_type_subst_v’ \\ gvs [] >- (
    drule_all_then strip_assume_tac call_type_subst_v_head \\ gvs[]
    >- (qexists_tac`ctxt` \\ fs[])
    \\ assume_tac call_type_subst_v_thm
    \\ `∃ls. LIST_TYPE (PAIR_TYPE TYPE_TYPE TYPE_TYPE) ls v`
    by (
      drule_at_then (Pat`LIST_TYPE_HEAD`) irule v_ok_LIST_TYPE_HEAD
      \\ first_assum $ irule_at Any
      \\ rpt strip_tac
      \\ drule_at_then (Pat`PAIR_TYPE_HEAD`) irule v_ok_PAIR_TYPE_HEAD
      \\ first_assum $ irule_at Any
      \\ MATCH_ACCEPT_TAC v_ok_TYPE_TYPE_HEAD)
    \\ drule_then drule v_ok_TYPE_TYPE_HEAD \\ strip_tac
    \\ drule Arrow2 \\ rpt(disch_then drule)
    \\ impl_tac
    >- (
      simp[SF SFY_ss, TYPE_TYPE_perms_ok]
      \\ drule_at_then Any irule LIST_TYPE_perms_ok
      \\ rpt strip_tac \\ drule_at_then Any irule PAIR_TYPE_perms_ok
      \\ simp[SF SFY_ss, TYPE_TYPE_perms_ok])
    \\ strip_tac \\ gvs []
    \\ fs[state_ok_def]
    \\ first_assum $ irule_at Any
    \\ simp[SF SFY_ss]
    \\ drule_at_then Any irule TYPE_IMP_v_ok
    \\ irule (CONJUNCT2(SPEC_ALL type_subst))
    \\ simp[SF SFY_ss, v_ok_TYPE]
    \\ drule_at_then Any (drule_at Any) v_ok_LIST
    \\ disch_then(qspec_then`λctxt p. TYPE ctxt (FST p) ∧ TYPE ctxt (SND p)`mp_tac)
    \\ simp[LAMBDA_PROD, FORALL_PROD]
    \\ disch_then irule
    \\ simp[ml_translatorTheory.PAIR_TYPE_def, PULL_EXISTS, v_ok_Conv_NONE]
    \\ metis_tac[v_ok_TYPE])
  \\ Cases_on ‘f = call_freesin_v’ \\ gvs [] >- (
    drule_all_then strip_assume_tac call_freesin_v_head \\ gvs[]
    >- (first_assum $ irule_at Any \\ rw[])
    \\ assume_tac call_freesin_v_thm
    \\ drule_then drule v_ok_LIST_TERM_TYPE_HEAD \\ strip_tac
    \\ drule_then drule v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ drule Arrow2
    \\ rpt (disch_then drule)
    \\ impl_tac
    >- (
      simp[SF SFY_ss, TERM_TYPE_perms_ok]
      \\ drule_at_then Any irule LIST_TYPE_perms_ok
      \\ simp[SF SFY_ss, TERM_TYPE_perms_ok])
    \\ strip_tac \\ gvs []
    \\ fs[state_ok_def]
    \\ first_assum $ irule_at Any
    \\ simp[SF SFY_ss, BOOL_v_ok])
  \\ Cases_on ‘f = call_vfree_in_v’ \\ gvs [] >- (
    drule_all_then strip_assume_tac call_vfree_in_v_head \\ gvs[]
    >- (first_assum $ irule_at Any \\ rw[])
    \\ assume_tac call_vfree_in_v_thm
    \\ imp_res_tac v_ok_TERM_TYPE_HEAD
    \\ drule Arrow2
    \\ rpt (disch_then drule)
    \\ impl_tac
    >- simp[SF SFY_ss, TERM_TYPE_perms_ok]
    \\ strip_tac \\ gvs []
    \\ fs[state_ok_def]
    \\ first_assum $ irule_at Any
    \\ simp[SF SFY_ss, BOOL_v_ok])
  \\ Cases_on ‘f = call_variant_v’ \\ gvs [] >-
   (drule_all_then strip_assume_tac call_variant_v_head \\ gvs []
    >- (qexists_tac ‘ctxt’ \\ fs []
        \\ fs [state_ok_def] \\ first_assum (irule_at Any) \\ gs [])
    \\ rename1 ‘do_opapp [g; w]’
    \\ ‘∃tms. LIST_TYPE TERM_TYPE tms v’
      by (irule_at Any v_ok_LIST_TERM_TYPE_HEAD \\ gs [SF SFY_ss])
    \\ ‘∃tm2. TERM_TYPE tm2 w’
      by (irule_at Any v_ok_TERM_TYPE_HEAD \\ gs [SF SFY_ss])
    \\ ‘perms_ok {} call_variant_v’
      by (irule_at Any perms_ok_call_variant_v \\ gs [])
    \\ ‘perms_ok {} v ∧ perms_ok {} w’
      by gs [SF SFY_ss, TERM_TYPE_perms_ok, LIST_TERM_TYPE_perms_ok]
    \\ assume_tac call_variant_v_thm
    \\ drule_all Arrow2
    \\ strip_tac \\ gvs []
    \\ irule_at (Pos last) v_ok_KernelVals
    \\ irule_at Any v_ok_Inferred
    \\ irule_at Any inferred_TERM
    \\ first_assum (irule_at (Pos (el 2)))
    \\ irule_at Any variant_thm
    \\ drule_all v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ ‘TERM ctxt tm2’ by imp_res_tac v_ok_TERM
    \\ pop_assum (irule_at $ Pos $ el 2)
    \\ fs [state_ok_def]
    \\ first_assum (irule_at (Pos (el 2))) \\ gs []
    \\ first_assum (irule_at (Pos (el 2))) \\ gs []
    \\ drule_all v_ok_LIST_TERM \\ fs [SF SFY_ss])
  \\ Cases_on ‘f = vsubst_v’ \\ gvs [] >- (
    drule_all vsubst_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac`ctxt` \\ fs[])
    \\ rename1 ‘do_opapp [g; w]’
    \\ assume_tac vsubst_v_thm
    \\ fs[state_ok_def]
    \\ `∃ls. LIST_TYPE (PAIR_TYPE TERM_TYPE TERM_TYPE) ls v`
    by (
      irule v_ok_LIST_PAIR_TYPE_HEAD
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ simp[v_ok_TERM_TYPE_HEAD]
      \\ MATCH_ACCEPT_TAC v_ok_TERM_TYPE_HEAD )
    \\ drule_all v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ drule ArrowM2
    \\ rpt(disch_then drule)
    \\ impl_tac
    >- (
      simp[SF SFY_ss, TERM_TYPE_perms_ok]
      \\ drule_at_then Any irule LIST_TYPE_perms_ok
      \\ rpt strip_tac
      \\ drule_at_then Any irule PAIR_TYPE_perms_ok
      \\ simp[SF SFY_ss, TERM_TYPE_perms_ok])
    \\ strip_tac \\ gvs[]
    \\ qexists_tac ‘ctxt’
    \\ simp[]
    \\ drule_all v_ok_TERM \\ strip_tac
    \\ drule_at_then Any (drule_at Any) v_ok_LIST
    \\ disch_then(qspec_then`λctxt p. TERM ctxt (FST p) ∧ TERM ctxt (SND p)`mp_tac)
    \\ impl_tac
    >- (
      rpt strip_tac
      \\ irule v_ok_PAIR
      \\ first_assum $ irule_at Any
      \\ first_assum $ irule_at Any
      \\ metis_tac[v_ok_TERM] )
    \\ simp[Once LAMBDA_PROD] \\ strip_tac
    \\ drule_all vsubst_thm
    \\ strip_tac \\ rveq
    \\ conj_tac
    >- ( first_assum $ irule_at $ Any \\ simp[SF SFY_ss] )
    \\ Cases_on`r` \\ fs[]
    >- (
      irule TERM_IMP_v_ok
      \\ first_assum $ irule_at $ Any
      \\ rw[] )
    \\ rename1 ‘M_failure ff’ \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss])
  \\ Cases_on ‘f = inst_v’ \\ gvs [] >- (
    drule_all inst_v_head \\ strip_tac \\ gvs[]
    >- (qexists_tac`ctxt` \\ fs[])
    \\ rename1 ‘do_opapp [g; w]’
    \\ assume_tac inst_v_thm
    \\ fs[state_ok_def]
    \\ `∃ls. LIST_TYPE (PAIR_TYPE TYPE_TYPE TYPE_TYPE) ls v`
    by (
      irule v_ok_LIST_PAIR_TYPE_HEAD
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ simp[v_ok_TYPE_TYPE_HEAD]
      \\ MATCH_ACCEPT_TAC v_ok_TYPE_TYPE_HEAD )
    \\ drule_all v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ drule ArrowM2
    \\ rpt(disch_then drule)
    \\ impl_tac
    >- (
      simp[SF SFY_ss, TERM_TYPE_perms_ok]
      \\ drule_at_then Any irule LIST_TYPE_perms_ok
      \\ rpt strip_tac
      \\ drule_at_then Any irule PAIR_TYPE_perms_ok
      \\ simp[SF SFY_ss, TYPE_TYPE_perms_ok])
    \\ strip_tac \\ gvs[]
    \\ qexists_tac ‘ctxt’
    \\ simp[]
    \\ drule_all v_ok_TERM \\ strip_tac
    \\ drule_at_then Any (drule_at Any) v_ok_LIST
    \\ disch_then(qspec_then`λctxt p. TYPE ctxt (FST p) ∧ TYPE ctxt (SND p)`mp_tac)
    \\ impl_tac
    >- (
      rpt strip_tac
      \\ irule v_ok_PAIR
      \\ first_assum $ irule_at Any
      \\ first_assum $ irule_at Any
      \\ metis_tac[v_ok_TYPE] )
    \\ simp[Once LAMBDA_PROD] \\ strip_tac
    \\ drule_all inst_thm
    \\ strip_tac \\ rveq
    \\ conj_tac
    >- ( first_assum $ irule_at $ Any \\ simp[SF SFY_ss] )
    \\ fs[]
    \\ irule TERM_IMP_v_ok
    \\ first_assum $ irule_at $ Any
    \\ rw[])
  \\ Cases_on ‘f = abs_v’ \\ gvs [] >- (
    drule_all_then strip_assume_tac abs_v_head \\ gvs[]
    >- (first_assum $ irule_at Any \\ rw[])
    \\ assume_tac abs_v_thm
    \\ drule_then drule v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ drule_then drule v_ok_THM_TYPE_HEAD \\ strip_tac
    \\ fs[state_ok_def]
    \\ drule ArrowM2
    \\ rpt (disch_then drule)
    \\ impl_tac
    >- simp[SF SFY_ss, TERM_TYPE_perms_ok, THM_TYPE_perms_ok]
    \\ strip_tac \\ gvs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ simp [SF SFY_ss]
    \\ drule_all v_ok_THM \\ strip_tac
    \\ drule_all v_ok_TERM \\ strip_tac
    \\ drule_all holKernelProofTheory.ABS_thm
    \\ strip_tac \\ gvs []
    \\ Cases_on ‘r’ \\ fs []
    \\ imp_res_tac THM_IMP_v_ok \\ gvs []
    \\ rename [‘M_failure ff’] \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss])
  \\ Cases_on ‘f = eq_mp_v’ \\ gvs [] >- (
    drule_all_then strip_assume_tac eq_mp_v_head \\ gvs[]
    >- (first_assum $ irule_at Any \\ rw[])
    \\ assume_tac eq_mp_v_thm
    \\ imp_res_tac v_ok_THM_TYPE_HEAD
    \\ fs[state_ok_def]
    \\ drule ArrowM2
    \\ rpt (disch_then drule)
    \\ impl_tac
    >- simp[SF SFY_ss, THM_TYPE_perms_ok]
    \\ strip_tac \\ gvs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ simp [SF SFY_ss]
    \\ drule_all v_ok_THM \\ strip_tac
    \\ drule_at_then(Pat`EQ_MP`)(drule_at Any) holKernelProofTheory.EQ_MP_thm
    \\ impl_tac
    >- ( simp[] \\ drule_then (drule_then irule) v_ok_THM )
    \\ strip_tac \\ gvs []
    \\ Cases_on ‘r’ \\ fs []
    \\ imp_res_tac THM_IMP_v_ok \\ gvs []
    \\ rename [‘M_failure ff’] \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss])
  \\ Cases_on ‘f = deduct_antisym_rule_v’ \\ gvs [] >- (
    drule_all_then strip_assume_tac deduct_antisym_rule_v_head \\ gvs[]
    >- (first_assum $ irule_at Any \\ rw[])
    \\ assume_tac deduct_antisym_rule_v_thm
    \\ imp_res_tac v_ok_THM_TYPE_HEAD
    \\ fs[state_ok_def]
    \\ drule ArrowM2
    \\ rpt (disch_then drule)
    \\ impl_tac
    >- simp[SF SFY_ss, THM_TYPE_perms_ok]
    \\ strip_tac \\ gvs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ simp [SF SFY_ss]
    \\ drule_all v_ok_THM \\ strip_tac
    \\ drule_at_then(Pat`DEDUCT_ANTISYM_RULE`)(drule_at Any) holKernelProofTheory.DEDUCT_ANTISYM_RULE_thm
    \\ impl_tac
    >- ( simp[] \\ drule_then (drule_then irule) v_ok_THM )
    \\ strip_tac \\ gvs []
    \\ Cases_on ‘r’ \\ fs []
    \\ imp_res_tac THM_IMP_v_ok \\ gvs []
    \\ rename [‘M_failure ff’] \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss])
  \\ Cases_on ‘f = inst_type_v’ \\ gvs [] >- (
    drule_all_then strip_assume_tac inst_type_v_head \\ gvs[]
    >- (first_assum $ irule_at Any \\ rw[])
    \\ assume_tac inst_type_v_thm
    \\ drule_then drule v_ok_THM_TYPE_HEAD \\ strip_tac
    \\ qmatch_asmsub_abbrev_tac`PURE A`
    \\ `∃pa. A pa v`
    by (
      qunabbrev_tac`A`
      \\ drule_at_then(Pat`LIST_TYPE_HEAD`) irule v_ok_LIST_TYPE_HEAD
      \\ first_assum $ irule_at Any
      \\ rpt strip_tac
      \\ drule_at_then(Pat`PAIR_TYPE_HEAD`) irule v_ok_PAIR_TYPE_HEAD
      \\ simp[SF SFY_ss, v_ok_TYPE_TYPE_HEAD])
    \\ fs[state_ok_def]
    \\ drule ArrowM2
    \\ rpt (disch_then drule)
    \\ impl_tac >- (
      simp[SF SFY_ss, THM_TYPE_perms_ok]
      \\ qunabbrev_tac`A`
      \\ drule_at_then Any irule LIST_TYPE_perms_ok
      \\ rpt strip_tac
      \\ drule_at_then Any irule PAIR_TYPE_perms_ok
      \\ simp[SF SFY_ss, TYPE_TYPE_perms_ok])
    \\ strip_tac \\ gvs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ simp [SF SFY_ss]
    \\ drule_all v_ok_THM \\ strip_tac
    \\ qunabbrev_tac`A`
    \\ drule_at_then(Pat`INST_TYPE`)(drule_at Any) holKernelProofTheory.INST_TYPE_thm
    \\ impl_keep_tac >- (
      simp[]
      \\ drule_at_then Any (drule_at Any) v_ok_LIST
      \\ disch_then(qspec_then`λctxt p. TYPE ctxt (FST p) ∧ TYPE ctxt (SND p)`mp_tac)
      \\ simp[EVERY_MEM, FORALL_PROD]
      \\ disch_then match_mp_tac
      \\ simp[ml_translatorTheory.PAIR_TYPE_def,PULL_EXISTS,v_ok_Conv_NONE]
      \\ simp[SF SFY_ss, v_ok_TYPE])
    \\ strip_tac \\ gvs []
    \\ simp[SF SFY_ss, THM_IMP_v_ok])
  \\ Cases_on ‘f = inst_1_v’ \\ gvs [] >- (
    drule_all_then strip_assume_tac inst_1_v_head \\ gvs[]
    >- (first_assum $ irule_at Any \\ rw[])
    \\ assume_tac inst_1_v_thm
    \\ drule_then drule v_ok_THM_TYPE_HEAD \\ strip_tac
    \\ qmatch_asmsub_abbrev_tac`PURE A`
    \\ `∃ls. A ls v`
    by (
      qunabbrev_tac`A`
      \\ drule_at_then(Pat`LIST_TYPE_HEAD`) irule v_ok_LIST_TYPE_HEAD
      \\ first_assum $ irule_at Any
      \\ rpt strip_tac
      \\ drule_at_then(Pat`PAIR_TYPE_HEAD`) irule v_ok_PAIR_TYPE_HEAD
      \\ simp[SF SFY_ss, v_ok_TERM_TYPE_HEAD])
    \\ fs[state_ok_def]
    \\ drule ArrowM2
    \\ rpt (disch_then drule)
    \\ impl_tac >- (
      simp[SF SFY_ss, THM_TYPE_perms_ok]
      \\ qunabbrev_tac`A`
      \\ drule_at_then Any irule LIST_TYPE_perms_ok
      \\ rpt strip_tac
      \\ drule_at_then Any irule PAIR_TYPE_perms_ok
      \\ simp[SF SFY_ss, TERM_TYPE_perms_ok])
    \\ strip_tac \\ gvs[]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ simp [SF SFY_ss]
    \\ drule_all v_ok_THM \\ strip_tac
    \\ qunabbrev_tac`A`
    \\ drule_at_then(Pat`INST`)(drule_at Any) holKernelProofTheory.INST_thm
    \\ impl_tac >- (
      simp[]
      \\ drule_at_then Any (drule_at Any) v_ok_LIST
      \\ disch_then(qspec_then`λctxt p. TERM ctxt (FST p) ∧ TERM ctxt (SND p)`mp_tac)
      \\ simp[EVERY_MEM, FORALL_PROD]
      \\ disch_then match_mp_tac
      \\ simp[ml_translatorTheory.PAIR_TYPE_def,PULL_EXISTS,v_ok_Conv_NONE]
      \\ simp[SF SFY_ss, v_ok_TERM])
    \\ strip_tac \\ gvs []
    \\ Cases_on ‘r’ \\ fs []
    \\ imp_res_tac THM_IMP_v_ok \\ gvs []
    \\ rename [‘M_failure ff’] \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss])
  \\ Cases_on ‘f = trans_v’ \\ gvs [] >-
   (drule_all trans_v_head \\ strip_tac \\ gvs []
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ rename [‘do_opapp [g; w]’]
    \\ ‘∃th1. THM_TYPE th1 v’
      by (irule_at Any v_ok_THM_TYPE_HEAD \\ gs [SF SFY_ss])
    \\ ‘∃th2. THM_TYPE th2 w’
      by (irule_at Any v_ok_THM_TYPE_HEAD \\ gs [SF SFY_ss])
    \\ ‘THM ctxt th1 ∧ THM ctxt th2’ by (imp_res_tac v_ok_THM \\ fs [])
    \\ assume_tac trans_v_thm
    \\ fs [state_ok_def]
    \\ ‘perms_ok kernel_perms v ∧
        perms_ok kernel_perms w ∧
        perms_ok kernel_perms trans_v’ by
         fs [THM_TYPE_perms_ok, SF SFY_ss]
    \\ drule_all ArrowM2 \\ strip_tac \\ fs []
    \\ qexists_tac ‘ctxt’ \\ fs [SF SFY_ss]
    \\ fs [PULL_EXISTS]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ drule_all holKernelProofTheory.TRANS_thm
    \\ strip_tac \\ gvs []
    \\ Cases_on ‘r’ \\ fs []
    \\ imp_res_tac THM_IMP_v_ok \\ gvs []
    \\ rename [‘M_failure ff’] \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss])
  \\ qsuff_tac ‘∃v1 v2 x. f = Closure v1 v2 x ∧ ∀n w. x ≠ Fun n w’
  THEN1 (strip_tac \\ fs [do_partial_app_def,AllCaseEqs()])
  \\ fs [kernel_funs_def]
  \\ TRY (rewrite_tac [kernel_funs_v_def,v_11] \\ simp [] \\ NO_TAC)
QED

val _ = export_theory ();
