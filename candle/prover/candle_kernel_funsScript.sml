(*
  Prove that kernel functions maintain Candle prover's invariants
 *)

open preamble helperLib;
open semanticPrimitivesTheory semanticPrimitivesPropsTheory
     evaluateTheory namespacePropsTheory evaluatePropsTheory
     sptreeTheory ml_hol_kernelProgTheory candle_kernel_permsTheory;
open permsTheory candle_kernel_valsTheory candle_prover_invTheory ast_extrasTheory;
local open ml_progLib in end

val _ = new_theory "candle_kernel_funs";

val _ = set_grammar_ancestry [
  "candle_kernel_vals", "candle_prover_inv", "ast_extras", "evaluate",
  "namespaceProps", "perms", "semanticPrimitivesProps", "misc"];

Theorem variant_thm: (* ought to be proved in holKernelProof *)
  EVERY (TERM defs) tms ∧ TERM defs tm ∧ STATE defs s ⇒ TERM defs (variant tms tm)
Proof
  cheat
QED

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
       (∀x. r = Success x ⇒ ∃rv. res = Rval [rv] ∧ B x rv) ∧
       (∀x. r = Failure x ⇒ ∃rv. res = Rerr (Rraise rv) ∧ D x rv))
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
  HOL_EXN_TYPE (Fail m) v ⇒ v_ok ctxt v
Proof
  Cases_on ‘m’
  \\ rw [HOL_EXN_TYPE_def,ml_translatorTheory.STRING_TYPE_def]
  \\ irule v_ok_Conv \\ fs []
  \\ fs [Once v_ok_cases]
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
                     call_variant_v; vsubst_v; inst_v; trans_v; abs_1_v; eq_mp_v;
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
  \\ Cases_on ‘f = concl_v’ \\ gvs [] >-
   (drule_all concl_v_head \\ strip_tac \\ gvs []
    \\ TRY (first_x_assum $ irule_at Any \\ gvs [] \\ NO_TAC)
    \\ rename [‘THM_TYPE_HEAD _’]
    \\ assume_tac concl_v_thm
    \\ drule_all v_ok_THM_TYPE_HEAD \\ strip_tac
    \\ (drule_then $ drule_then $ drule_then $ drule) Arrow1
    \\ impl_tac
    THEN1 (imp_res_tac THM_TYPE_perms_ok \\ fs [perms_ok_concl])
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
  \\ Cases_on ‘f = beta_v’ \\ gvs [] >-
   (drule_all beta_v_head \\ strip_tac \\ gvs []
    >- (qexists_tac ‘ctxt’ \\ fs [])
    \\ drule_all v_ok_TERM_TYPE_HEAD \\ strip_tac
    \\ imp_res_tac v_ok_TERM \\ fs []
    \\ assume_tac beta_v_thm
    \\ fs [state_ok_def]
    \\ ‘perms_ok kernel_perms v ∧ perms_ok kernel_perms beta_v’ by
         fs [TERM_TYPE_perms_ok, SF SFY_ss, beta_v_perms_ok]
    \\ drule_all ArrowM1 \\ strip_tac \\ fs []
    \\ disj2_tac
    \\ drule_all holKernelProofTheory.BETA_thm \\ strip_tac \\ gvs []
    \\ qexists_tac ‘ctxt’ \\ fs []
    \\ fs [PULL_EXISTS]
    \\ first_assum $ irule_at $ Pos $ hd
    \\ fs [SF SFY_ss]
    \\ Cases_on ‘r’ \\ fs []
    \\ imp_res_tac THM_IMP_v_ok \\ gvs []
    \\ rename [‘Failure ff’] \\ Cases_on ‘ff’ \\ fs []
    \\ fs [HOL_EXN_TYPE_Fail_v_ok, SF SFY_ss])
  \\ cheat
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
    by (gvs [do_partial_app_def, CaseEqs ["v", "exp"], do_opapp_cases,
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
        evaluate s env [exp] = (s', res) ⇒
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
  \\ Cases_on ‘f = call_type_subst_v’ \\ gvs [] >- cheat
  \\ Cases_on ‘f = call_freesin_v’ \\ gvs [] >- cheat
  \\ Cases_on ‘f = call_vfree_in_v’ \\ gvs [] >- cheat
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
      by (irule_at Any call_variant_v_perms_ok \\ gs [])
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
    \\ drule_all LIST_TYPE_TERM_TYPE_v_ok \\ fs [SF SFY_ss])
  \\ Cases_on ‘f = vsubst_v’ \\ gvs [] >- cheat
  \\ Cases_on ‘f = inst_v’ \\ gvs [] >- cheat
  \\ Cases_on ‘f = abs_1_v’ \\ gvs [] >- cheat
  \\ Cases_on ‘f = eq_mp_v’ \\ gvs [] >- cheat
  \\ Cases_on ‘f = deduct_antisym_rule_v’ \\ gvs [] >- cheat
  \\ Cases_on ‘f = inst_type_v’ \\ gvs [] >- cheat
  \\ Cases_on ‘f = inst_1_v’ \\ gvs [] >- cheat
  \\ Cases_on ‘f = trans_v’ \\ gvs []
  >- (
    drule_all_then strip_assume_tac trans_v_head \\ gvs []
    >- (first_assum (irule_at Any) \\ gs [])
    \\ rename1 ‘do_opapp [g; w]’
    \\ ‘∃th1. THM_TYPE th1 v’
      by (irule_at Any v_ok_THM_TYPE_HEAD \\ gs [SF SFY_ss])
    \\ ‘∃th2. THM_TYPE th2 w’
      by (irule_at Any v_ok_THM_TYPE_HEAD \\ gs [SF SFY_ss])
    \\ ‘perms_ok kernel_perms v ∧ perms_ok kernel_perms w ∧
        perms_ok kernel_perms trans_v’
      by gs [SF SFY_ss, THM_TYPE_perms_ok, trans_v_perms_ok]
    \\ assume_tac trans_v_thm (*
    \\ drule_all Arrow2
    \\ strip_tac \\ gvs []
    \\ irule_at (Pos last) v_ok_KernelVals
    \\ irule_at Any v_ok_Inferred
    \\ irule_at Any inferred_THM
    \\ first_assum (irule_at (Pos (el 2)))
    \\ irule_at Any conj_thm
    \\ imp_res_tac v_ok_THM
    \\ first_assum (irule_at Any) \\ gs []
    \\ gs [state_ok_def] *) \\ cheat)
  \\ qsuff_tac ‘∃v1 v2 x. f = Closure v1 v2 x ∧ ∀n w. x ≠ Fun n w’
  THEN1 (strip_tac \\ fs [do_partial_app_def,AllCaseEqs()])
  \\ fs [kernel_funs_def]
  \\ TRY (rewrite_tac [kernel_funs_v_def,v_11] \\ simp [] \\ NO_TAC)
QED

val _ = export_theory ();
