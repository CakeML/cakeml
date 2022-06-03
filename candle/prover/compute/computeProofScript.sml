(*
  Proof of correctness for the compute primitive.
 *)

open preamble holSyntaxTheory holSyntaxExtraTheory holKernelTheory
     holKernelProofTheory ml_monadBaseTheory;
open compute_syntaxTheory compute_syntaxProofTheory;
open compute_evalTheory compute_evalProofTheory;
open computeTheory;

val _ = new_theory "computeProof";

val _ = numLib.prefer_num ();

Theorem compute_init_thy_ok:
  compute_init ths ∧
  STATE ctxt s ∧
  EVERY (THM ctxt) ths ⇒
    compute_thy_ok (thyof ctxt)
Proof
  strip_tac
  \\ gvs [compute_init_def]
  \\ gs [compute_thms_def, compute_thy_ok_def, numeral_thy_ok_def,
         bool_thy_ok_def, STATE_def, CONTEXT_def, THM_def, extends_theory_ok,
         init_theory_ok, SF SFY_ss]
QED

(* -------------------------------------------------------------------------
 * compute_add
 * ------------------------------------------------------------------------- *)

Theorem compute_add_thm:
  STATE ctxt s ∧
  EVERY (THM ctxt) ths ∧
  TERM ctxt tm ⇒
  compute_add ths tm s = (res, s') ⇒
    s' = s ∧
    (∀th. res = M_success th ⇒ THM ctxt th) ∧
    (∀tm. res ≠ M_failure (Clash tm))
Proof
  simp [compute_add_def, raise_Failure_def]
  \\ IF_CASES_TAC \\ gs [] \\ strip_tac
  \\ drule_all_then strip_assume_tac compute_init_thy_ok
  \\ drule_then strip_assume_tac compute_thy_ok_terms_ok
  \\ ‘theory_ok (thyof ctxt) ∧ numeral_thy_ok (thyof ctxt)’ by fs []
  \\ simp [Once st_ex_bind_def, otherwise_def]
  \\ CASE_TAC \\ gs []
  \\ ‘TERM ctxt _ADD_TM’
    by gs [TERM_def]
  \\ drule_all_then strip_assume_tac dest_binary_thm \\ gvs []
  \\ CASE_TAC \\ gs []
  \\ pairarg_tac \\ gvs []
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
  \\ drule_all_then strip_assume_tac dest_numeral_thm \\ gvs []
  \\ CASE_TAC \\ gs []
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
  \\ drule_all_then strip_assume_tac dest_numeral_thm \\ gvs []
  \\ CASE_TAC \\ gvs []
  \\ simp [Once st_ex_bind_def, st_ex_return_def] \\ CASE_TAC \\ gs []
  \\ rename [‘num2bit (x + y)’,
             ‘dest_binary _ (_ADD (_NUMERAL l) (_NUMERAL r)) s’]
  \\ ‘TERM ctxt (_NUMERAL (num2bit (x + y)))’
    by (‘TERM ctxt (num2bit (x + y))’
          suffices_by rw [TERM_def, term_ok_def]
        \\ simp [num2bit_thm])
  \\ drule_then (qspec_then ‘ctxt’ mp_tac) mk_eq_thm
  \\ impl_tac >- fs []
  \\ strip_tac \\ rveq
  \\ CASE_TAC \\ fs []
  \\ rw [] \\ rw [THM_def]
  \\ ‘term_type (_ADD (_NUMERAL l) (_NUMERAL r)) = Num’
    by (fs [STATE_def]
        \\ qpat_x_assum ‘TERM _ (_ADD _ _)’ assume_tac
        \\ drule_all term_type \\ gs [])
  \\ gvs []
  \\ fs [STATE_def]
  \\ dxrule num2bit_dest_numeral \\ fs [] \\ strip_tac
  \\ dxrule num2bit_dest_numeral \\ fs [] \\ strip_tac
  \\ gvs []
  \\ qmatch_asmsub_abbrev_tac ‘TERM ctxt _’
  \\ ‘TERM ctxt l ∧ TERM ctxt r’
    by gs [TERM_def, term_ok_def]
  \\ ‘l has_type Num ∧ r has_type Num’
    by gs [TERM_def, term_ok_def, WELLTYPED]
  \\ ‘(thyof ctxt,[]) |- _NUMERAL l === l’
    by gs [NUMERAL_eqn, TERM_def]
  \\ ‘(thyof ctxt,[]) |- _NUMERAL r === r’
    by gs [NUMERAL_eqn, TERM_def]
  \\ ‘(thyof ctxt,[]) |- _ADD (_NUMERAL l) (_NUMERAL r) ===
                         _NUMERAL (num2bit (x + y))’
    suffices_by rw [equation_def]
  \\ resolve_then Any irule sym_equation replaceL1
  \\ first_x_assum (irule_at Any)
  \\ resolve_then Any irule sym_equation replaceL2
  \\ first_x_assum (irule_at Any)
  \\ irule replaceL1 \\ first_x_assum (irule_at Any)
  \\ irule replaceL2 \\ first_x_assum (irule_at Any)
  \\ ‘numeral_thy_ok (thyof ctxt)’ by fs []
  \\ dxrule_then assume_tac num2bit_term_ok \\ fs []
  \\ resolve_then Any irule trans_equation_simple sym_equation
  \\ irule_at Any NUMERAL_eqn \\ rw [num2bit_ADD]
QED

(* -------------------------------------------------------------------------
 * compute
 * ------------------------------------------------------------------------- *)

Theorem const_list_ok[local]:
  ∀vs. set (const_list vs) = cexp_consts vs
Proof
  ho_match_mp_tac const_list_ind
  \\ rw [const_list_def, cexp_consts_def]
  \\ simp [Once EXTENSION]
  \\ rw [MEM_FLAT, MEM_MAP, PULL_EXISTS]
  \\ eq_tac \\ rw [DISJ_EQ_IMP] \\ gs []
  \\ first_x_assum (drule_then assume_tac)
  \\ first_x_assum (irule_at Any) \\ gs []
QED

Theorem var_list_ok[local]:
  ∀vs. set (var_list vs) = cexp_vars vs
Proof
  ho_match_mp_tac var_list_ind
  \\ rw [var_list_def, cexp_vars_def]
  \\ simp [Once EXTENSION]
  \\ rw [MEM_FLAT, MEM_MAP, PULL_EXISTS]
  \\ eq_tac \\ rw [DISJ_EQ_IMP] \\ gs []
  \\ first_x_assum (drule_then assume_tac)
  \\ first_x_assum (irule_at Any) \\ gs []
QED

Theorem check_cexp_closed_correct:
  ∀v. check_cexp_closed v ⇒ cexp_vars v = {}
Proof
  ho_match_mp_tac check_cexp_closed_ind
  \\ rw [check_cexp_closed_def, cexp_vars_def]
  \\ rw [DISJ_EQ_IMP] \\ gs [EVERY_MEM]
  \\ simp [Once EXTENSION, EQ_IMP_THM, MEM_MAP, PULL_EXISTS]
  \\ ‘∃c. MEM c cs’
    by (Cases_on ‘cs’ \\ gs [SF DNF_ss])
  \\ first_assum (irule_at Any)
  \\ gs [SF SFY_ss]
QED

Theorem map_check_var_thm:
  ∀tms s res s'.
    STATE ctxt s ∧
    EVERY (TERM ctxt) tms ∧
    map check_var tms s = (res, s') ⇒
      s = s' ∧
      (∀tm. res ≠ M_failure (Clash tm)) ∧
      ∀ns.
        res = M_success ns ⇒
        LIST_REL (λtm n. tm = Var n Cexp) tms ns
Proof
  Induct \\ simp [map_def, st_ex_return_def]
  \\ rpt gen_tac
  \\ strip_tac
  \\ qpat_x_assum ‘_ = (res,_)’ mp_tac
  \\ simp [Once st_ex_bind_def]
  \\ CASE_TAC \\ gs []
  \\ reverse CASE_TAC \\ gs []
  >- (
    strip_tac \\ gvs []
    \\ Cases_on ‘h’ \\ gs [check_var_def, raise_Failure_def, st_ex_return_def]
    \\ gvs [COND_RATOR, CaseEq "bool"])
  \\ Cases_on ‘h’ \\ gs [check_var_def, raise_Failure_def, st_ex_return_def]
  \\ gvs [COND_RATOR, CaseEq "bool"]
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
  \\ first_x_assum drule_all \\ rw []
  \\ gvs [CaseEq "exc"]
QED

Theorem check_eqn_thm:
  compute_thy_ok (thyof ctxt) ∧
  STATE ctxt s ∧
  THM ctxt th ∧
  check_eqn th s = (res, s') ⇒
    s = s' ∧
    (∀tm. res ≠ M_failure (Clash tm)) ∧
    ∀f vs r.
      res = M_success (f,vs,cv) ⇒
      ∃l r. ALL_DISTINCT vs ∧
            th = Sequent [] (l === r) ∧
            list_dest_comb [] l = Const f (app_type (LENGTH vs))::
                                  (MAP (λs. Var s Cexp) vs) ∧
            dest_cexp r = SOME cv ∧
            ∀v. v ∈ cexp_vars cv ⇒ MEM v vs
Proof
  strip_tac
  \\ qpat_x_assum ‘check_eqn _ _ = _’ mp_tac
  \\ Cases_on ‘th’ \\ gvs [check_eqn_def]
  \\ simp [st_ex_return_def, raise_Failure_def, st_ex_ignore_bind_def]
  \\ IF_CASES_TAC \\ gs []
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
  \\ ‘TERM ctxt t’
    by (fs [THM_def, TERM_def]
        \\ drule proves_term_ok \\ rw [])
  \\ drule_all_then strip_assume_tac dest_eq_thm \\ gvs []
  \\ reverse CASE_TAC \\ gs [] >- (rw [] \\ strip_tac \\ gs [])
  \\ pairarg_tac \\ gvs []
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
  \\ IF_CASES_TAC \\ gs []
  \\ simp [otherwise_def, Once st_ex_bind_def]
  \\ CASE_TAC \\ gs []
  \\ drule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
  \\ ‘TERM ctxt h ∧ EVERY (TERM ctxt) t’
    by (fs [TERM_def]
        \\ drule_then strip_assume_tac term_ok_FOLDL_Comb
        \\ fs [EVERY_MEM, TERM_def])
  \\ drule_all_then strip_assume_tac dest_const_thm \\ gvs []
  \\ CASE_TAC \\ gs []
  \\ pairarg_tac \\ gvs []
  \\ simp [Once st_ex_bind_def]
  \\ TOP_CASE_TAC
  \\ drule_all_then strip_assume_tac map_check_var_thm \\ gvs []
  \\ reverse TOP_CASE_TAC \\ gs [] >- (rpt strip_tac \\ gs [])
  \\ rename [‘LIST_REL _ xs ys’]
  \\ ‘ALL_DISTINCT ys’
    by (qpat_x_assum ‘ALL_DISTINCT xs’ mp_tac
        \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
        \\ qid_spec_tac ‘ys’
        \\ qid_spec_tac ‘xs’
        \\ Induct \\ rw []
        \\ gvs [LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS]
        \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”])
  \\ gvs [LIST_REL_EL_EQN]
  \\ TOP_CASE_TAC \\ gs []
  \\ drule_then drule dest_cexp_thm
  \\ impl_tac >- fs [TERM_def]
  \\ strip_tac
  \\ IF_CASES_TAC \\ gs [GSYM equation_def] \\ rw []
  \\ simp [equation_def]
  \\ irule_at Any LIST_EQ \\ gvs [LIST_REL_EL_EQN, EL_MAP]
  \\ gvs [EVERY_MEM, var_list_ok]
  \\ rename [‘tm = Const f (app_type (LENGTH tms))’]
  \\ qpat_x_assum ‘dest_const tm _ = _’ mp_tac
  \\ simp [dest_const_def, raise_Failure_def, st_ex_return_def]
  \\ CASE_TAC \\ gs [] \\ rw []
  \\ rename [‘FOLDL _ (Const f ty) xs’]
  \\ ‘LENGTH tms = LENGTH xs’
    by fs [map_LENGTH, SF SFY_ss]
  \\ gs [TERM_def]
  \\ ‘typeof (FOLDL Comb (Const f ty) xs) = Cexp’
    by fs [term_ok_def, equation_def]
  \\ ‘∀tm.
        term_ok (sigof ctxt) tm ∧
        (∀x. MEM x xs ⇒ term_ok (sigof ctxt) x ∧ typeof x = Cexp) ∧
        term_ok (sigof ctxt) (FOLDL Comb tm xs) ∧
        typeof (FOLDL Comb tm xs) = Cexp ⇒
          typeof tm = app_type (LENGTH xs)’
    suffices_by (
      rw []
      \\ first_x_assum (qspec_then ‘Const f ty’ assume_tac)
      \\ gs [MEM_EL, PULL_EXISTS, SF SFY_ss])
  \\ rpt (pop_assum kall_tac)
  \\ Induct_on ‘xs’ \\ simp [app_type]
  \\ rw [] \\ gs [SF DNF_ss]
  \\ drule_then strip_assume_tac term_ok_FOLDL_Comb
  \\ first_x_assum drule \\ gs [term_ok_def]
QED

Theorem map_check_eqn_thm:
  compute_thy_ok (thyof ctxt) ⇒
  ∀ceqs s res s'.
    STATE ctxt s ∧
    EVERY (THM ctxt) ceqs ∧
    map check_eqn ceqs s = (res, s') ⇒
      s = s' ∧
      (∀tm. res ≠ M_failure (Clash tm)) ∧
      ∀eqs. res = M_success eqs ⇒
        ∀n. n < LENGTH eqs ⇒
            ∃f vs cv l r.
              ALL_DISTINCT vs ∧
              EL n eqs = (f,vs,cv) ∧
              EL n ceqs = Sequent [] (l === r) ∧
              list_dest_comb [] l = Const f (app_type (LENGTH vs))::
                                    (MAP (λs. Var s Cexp) vs) ∧
              dest_cexp r = SOME cv ∧
              ∀v. v ∈ cexp_vars cv ⇒ MEM v vs
Proof
  strip_tac
  \\ Induct \\ simp [map_def, st_ex_return_def, raise_Failure_def]
  \\ qx_gen_tac ‘th’
  \\ rpt gen_tac \\ strip_tac
  \\ qpat_x_assum ‘_ = (res,s')’ mp_tac
  \\ simp [Once st_ex_bind_def]
  \\ CASE_TAC \\ gs []
  \\ drule_all_then strip_assume_tac check_eqn_thm \\ gvs []
  \\ reverse CASE_TAC \\ gs [] >- (strip_tac \\ gvs [])
  \\ rename [‘check_eqn _ _ = (M_success p, _)’]
  \\ PairCases_on ‘p’ \\ fs []
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gvs []
  \\ CASE_TAC \\ gs [] \\ strip_tac \\ gvs []
  \\ Cases \\ gs []
QED

Theorem map_check_consts_thm:
  ∀ceqs s res s'.
    STATE ctxt s ∧
    map (λ(f,(n,r)). check_consts ars f r) ceqs s = (res, s') ⇒
      s = s' ∧
      (∀tm. res ≠ M_failure (Clash tm)) ∧
      ∀u. res = M_success u ⇒
        ∀f vs cv.
          MEM (f,vs,cv) ceqs ⇒ EVERY (λ(c,n). MEM (c,n) ars) (const_list cv)
Proof
  Induct \\ fs [map_def, check_consts_def, st_ex_return_def, raise_Failure_def]
  \\ qx_gen_tac ‘h’ \\ PairCases_on ‘h’
  \\ rpt gen_tac \\ strip_tac
  \\ qpat_x_assum ‘_ = (res,s')’ mp_tac
  \\ simp [Once st_ex_bind_def]
  \\ reverse IF_CASES_TAC \\ gs [] >- rw []
  \\ simp [Once st_ex_bind_def]
  \\ CASE_TAC \\ gs []
  \\ first_x_assum drule_all
  \\ strip_tac \\ gvs []
  \\ reverse CASE_TAC \\ gs [] \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem compute_thm:
  STATE ctxt s ∧
  EVERY (THM ctxt) ths ∧
  EVERY (THM ctxt) ceqs ∧
  TERM ctxt tm ⇒
  compute (ths,ceqs) tm s = (res, s') ⇒
    s' = s ∧
    (∀th. res = M_success th ⇒ THM ctxt th) ∧
    (∀tm. res ≠ M_failure (Clash tm))
Proof
  strip_tac
  \\ simp [compute_def, handle_Clash_def, raise_Failure_def, st_ex_return_def]
  \\ IF_CASES_TAC \\ gs []
  \\ gs []
  \\ drule_all_then strip_assume_tac compute_init_thy_ok
  \\ ‘theory_ok (thyof ctxt) ∧ numeral_thy_ok (thyof ctxt)’
    by fs []
  \\ CASE_TAC \\ gs []
  \\ simp [Once st_ex_ignore_bind_def]
  \\ IF_CASES_TAC \\ gs []
  \\ drule_then assume_tac check_cexp_closed_correct
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
  \\ drule_all_then strip_assume_tac map_check_eqn_thm \\ gvs []
  \\ reverse CASE_TAC \\ gs [] >- (CASE_TAC \\ gs [] \\ rw [])
  \\ simp [st_ex_ignore_bind_def]
  \\ qmatch_goalsub_abbrev_tac ‘map g a r’
  \\ Cases_on ‘map g a r’ \\ gs []
  \\ unabbrev_all_tac \\ gs []
  \\ drule_all_then strip_assume_tac map_check_consts_thm \\ gvs []
  \\ rename [‘map _ a r = (res,r)’]
  \\ reverse (Cases_on ‘res’) \\ gs [] >- (CASE_TAC \\ gs [] \\ rw [])
  \\ rename [‘compute_eval_run _ eqs cv’]
  \\ CASE_TAC \\ gs []
  \\ rename [‘compute_eval_run _ _ _ = M_success tm'’]
  \\ ‘term_ok (sigof (thyof ctxt)) tm’
    by fs [TERM_def]
  \\ drule_all_then strip_assume_tac dest_cexp_thm
  \\ gs [EVERY_MEM, MEM_EL, PULL_EXISTS]
  \\ drule_then drule compute_eval_run_thm \\ simp []
  \\ impl_tac
  >- (
    gvs [EVERY_MEM, FORALL_PROD, MEM_EL, PULL_EXISTS]
    \\ drule_then assume_tac proves_term_ok
    \\ rgs [Once equation_def, term_ok_def]
    \\ rw []
    \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
    \\ drule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
    \\ first_x_assum (irule_at Any)
    \\ first_x_assum (irule_at Any) \\ gs []
    \\ imp_res_tac map_LENGTH \\ gs []
    \\ qpat_x_assum ‘∀n. _ ⇒ THM _ _’ drule
    \\ rw [THM_def]
    \\ gs [SUBSET_DEF, MEM_EL, SF SFY_ss])
  \\ strip_tac \\ gvs []
  \\ ‘TERM ctxt (cexp2term tm')’
    by (drule cexp2term_term_ok \\ simp [TERM_def])
  \\ simp [Once st_ex_bind_def]
  \\ CASE_TAC \\ gs []
  \\ drule_all_then strip_assume_tac mk_eq_thm \\ gvs []
  \\ reverse CASE_TAC >- (CASE_TAC \\ gs [] \\ rw [])
  \\ rw []
  \\ ‘term_type tm = Cexp’
    by (fs [STATE_def]
        \\ qpat_x_assum ‘TERM ctxt tm’ assume_tac
        \\ drule_all term_type \\ gs [])
  \\ ‘(thyof ctxt,[]) |- tm === cexp2term tm'’
    suffices_by rw [equation_def, THM_def]
  \\ resolve_then Any irule trans_equation_simple sym_equation
  \\ first_x_assum (irule_at Any) \\ gs [sym_equation]
QED


val _ = export_theory ();

