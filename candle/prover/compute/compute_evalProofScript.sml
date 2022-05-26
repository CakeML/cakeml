(*
   Proofs about the interpreter function for the Candle compute primitive.
 *)

open preamble holSyntaxTheory holSyntaxExtraTheory holSyntaxLibTheory
     holKernelTheory holKernelProofTheory;
open compute_evalTheory compute_syntaxTheory compute_syntaxProofTheory;
open ml_monadBaseTheory ml_monadBaseLib;

val _ = new_theory "compute_evalProof";

val _ = numLib.prefer_num ();

fun SIMPR ths = SIMP_RULE (srw_ss()) ths;
fun SIMPC ths = SIMP_CONV (srw_ss()) ths;

Theorem do_fst_thm:
  do_fst p s = (res, s') ⇒
    s = s' ∧
    ∃q. res = M_success q ∧ cval_consts q ⊆ cval_consts p
Proof
  Cases_on ‘p’ \\ rw [do_fst_def, cval_consts_def, st_ex_return_def]
QED

Theorem do_snd_thm:
  do_snd p s = (res, s') ⇒
    s = s' ∧
    ∃q. res = M_success q ∧ cval_consts q ⊆ cval_consts p
Proof
  Cases_on ‘p’ \\ rw [do_snd_def, cval_consts_def, st_ex_return_def]
QED

Theorem term_ok_FOLDL_Comb:
  ∀tms tm.
    term_ok sig (FOLDL Comb tm tms) ⇒
      term_ok sig tm ∧
      EVERY (term_ok sig) tms
Proof
  Induct \\ rw [term_ok_def]
  \\ first_x_assum drule \\ rw [term_ok_def]
QED

Theorem subst_term_ok:
  ∀env cv.
    term_ok ctxt (cval2term cv) ∧
    EVERY (term_ok ctxt o cval2term) (MAP SND env) ⇒
      term_ok ctxt (cval2term (subst env cv))
Proof
  ho_match_mp_tac subst_ind \\ rw []
  >~ [‘Var _’] >- (
    gs [subst_def, cval2term_def]
    \\ CASE_TAC \\ imp_res_tac ALOOKUP_MEM
    \\ gvs [cval2term_def, EVERY_MEM, MEM_MAP, PULL_EXISTS, EXISTS_PROD,
            term_ok_def, SF SFY_ss])
  \\ gs [subst_def, cval2term_def, EVERY_MEM, MEM_MAP, EXISTS_PROD, PULL_EXISTS,
         term_ok_def, SF SFY_ss]
  >~ [‘bop2term bop _ _’] >- (
    Cases_on ‘bop’
    \\ gs [subst_def, cval2term_def, EVERY_MEM, MEM_MAP, EXISTS_PROD,
           bop2term_def, PULL_EXISTS, term_ok_def, SF SFY_ss])
  \\ ‘∀tm tms.
        term_ok ctxt tm ∧
        tm has_type (app_type (LENGTH tms)) ∧
        EVERY (term_ok ctxt) tms ∧
        EVERY (λtm. tm has_type cval_ty) tms ⇒
          term_ok ctxt (FOLDL Comb tm tms)’
    suffices_by (
      disch_then irule
      \\ drule_then strip_assume_tac term_ok_FOLDL_Comb
      \\ gs [EVERY_MAP, EVERY_MEM, has_type_rules, SF SFY_ss])
  \\ Induct_on ‘tms’ \\ rw [] \\ gs []
  \\ first_x_assum irule
  \\ gs [term_ok_def, term_ok_welltyped, SF SFY_ss]
  \\ imp_res_tac WELLTYPED_LEMMA
  \\ gs [has_type_rules, app_type, SF SFY_ss]
QED

Definition cval_value_def[simp]:
  cval_value (Num n) = T ∧
  cval_value (Pair p q) = (cval_value p ∧ cval_value q) ∧
  cval_value _ = F
End

Theorem do_arith_value:
  ∀opn x y s z s'.
    do_arith opn x y s = (M_success z, s') ⇒ cval_value z
Proof
  ho_match_mp_tac do_arith_ind \\ rw [do_arith_def, st_ex_return_def] \\ fs []
QED

Theorem do_reln_value:
  ∀opn x y s z s'.
    do_reln opn x y s = (M_success z, s') ⇒ cval_value z
Proof
  ho_match_mp_tac do_reln_ind \\ rw [do_reln_def, st_ex_return_def] \\ fs []
QED

Theorem do_binop_value:
  ∀bop x y z s s'.
    do_binop bop x y s = (M_success z, s') ⇒ cval_value z
Proof
  Cases \\ rw [do_binop_def]
  \\ gs [do_arith_value, do_reln_value, SF SFY_ss]
QED

Theorem compute_eval_value:
  ∀ck ceqs cv s x s'.
    compute_eval ck ceqs cv s = (M_success x, s') ⇒ cval_value x
Proof
  ho_match_mp_tac compute_eval_ind \\ rw []
  \\ qpat_x_assum ‘compute_eval _ _ _ _ = _’ mp_tac
  \\ simp [Once compute_eval_def]
  \\ TOP_CASE_TAC \\ gs []
  >- ((* Pair *)
    simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
    \\ CASE_TAC \\ gs [st_ex_return_def]
    \\ rw [] \\ fs [SF SFY_ss])
  >- ((* Num *)
    rw [st_ex_return_def] \\ fs [])
  >- ((* Var *)
    simp [raise_Type_error_def])
  >- ((* App *)
    IF_CASES_TAC \\ gs [raise_Timeout_def]
    \\ simp [option_def, raise_Type_error_def]
    \\ simp [Once st_ex_bind_def, st_ex_return_def]
    \\ CASE_TAC \\ gs [] \\ pairarg_tac \\ gvs []
    \\ simp [check_def, raise_Type_error_def, st_ex_return_def,
             st_ex_ignore_bind_def]
    \\ IF_CASES_TAC \\ gs []
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
    \\ CASE_TAC \\ gs [] \\ rw []
    \\ last_x_assum irule
    \\ first_x_assum (irule_at Any))
  >- ((* If *)
    simp [Once st_ex_bind_def, raise_Type_error_def]
    \\ TOP_CASE_TAC \\ gs [] \\ TOP_CASE_TAC \\ gs []
    \\ TOP_CASE_TAC \\ gs [SF SFY_ss]
    \\ TOP_CASE_TAC \\ gs [SF SFY_ss])
  >- ((* Fst *)
    simp [Once st_ex_bind_def, raise_Type_error_def]
    \\ TOP_CASE_TAC \\ gs [] \\ TOP_CASE_TAC \\ gs [] \\ rw []
    \\ rename [‘do_fst p’]
    \\ Cases_on ‘p’ \\ gvs [do_fst_def, st_ex_return_def, SF SFY_ss]
    \\ first_x_assum drule \\ gs [])
  >- ((* Snd *)
    simp [Once st_ex_bind_def, raise_Type_error_def]
    \\ TOP_CASE_TAC \\ gs [] \\ TOP_CASE_TAC \\ gs [] \\ rw []
    \\ rename [‘do_snd p’]
    \\ Cases_on ‘p’ \\ gvs [do_snd_def, st_ex_return_def, SF SFY_ss]
    \\ first_x_assum drule \\ gs [])
  >- ((* Binop *)
    simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
    \\ rw [] \\ drule do_binop_value \\ rw [])
QED

Theorem dest_binary_thm:
  STATE ctxt s ∧
  TERM ctxt tm ∧
  TERM ctxt tm' ⇒
  dest_binary tm' tm s = (res,s') ⇒
    s' = s ∧
    ∀l r. res = M_success (l,r) ⇒
          TERM ctxt l ∧ TERM ctxt r ∧
          tm = Comb (Comb tm' l) r
Proof
  simp [dest_binary_def, raise_Failure_def, st_ex_return_def]
  \\ strip_tac
  \\ rpt CASE_TAC \\ gs []
  \\ rw [] \\ gs [TERM_def, term_ok_def]
QED

Theorem dest_numeral_thm:
  STATE ctxt s ∧
  TERM ctxt tm ⇒
  dest_numeral tm s = (res,s') ⇒
    s' = s ∧
    ∀n. res = M_success n ⇒
        (numeral_thy_ok (thyof ctxt) ⇒ typeof tm = num_ty) ∧
        ∃tm'. tm = _NUMERAL tm' ∧ dest_num tm' = SOME n
Proof
  simp [dest_numeral_def, raise_Failure_def, st_ex_return_def]
  \\ strip_tac
  \\ rpt CASE_TAC \\ gs []
  \\ rw [SF SFY_ss]
QED

Theorem num2bit_thm:
  numeral_thy_ok (thyof ctxt) ⇒
    TERM ctxt (num2bit x)
Proof
  strip_tac \\ qid_spec_tac ‘x’
  \\ drule_then strip_assume_tac numeral_thy_ok_terms_ok
  \\ ho_match_mp_tac num2bit_ind \\ rw []
  \\ gs [numeral_thy_ok_def]
  \\ rw [Once num2bit_def] \\ gs []
  \\ fs [TERM_def] \\ simp [Once term_ok_def]
QED

Theorem dest_num_num2bit:
  numeral_thy_ok thy ⇒
  ∀x y.
    dest_num x = SOME y ⇒
      (thy,[]) |- num2bit y === x
Proof
  strip_tac
  \\ drule_then strip_assume_tac numeral_thy_ok_terms_ok
  \\ ‘theory_ok thy’
    by fs [numeral_thy_ok_def]
  \\ ho_match_mp_tac dest_num_ind \\ rw []
  \\ qpat_x_assum ‘dest_num _ = _’ mp_tac
  \\ simp [Once dest_num_def]
  \\ rw [CaseEqs ["term", "option", "bool"]]
  \\ simp [Once num2bit_def, proves_REFL] \\ gs []
  \\ rw [] \\ simp [MK_COMB_simple, proves_REFL]
  \\ gs [Once num2bit_def]
  \\ irule trans_equation_simple
  \\ qexists_tac ‘_BIT0 _0’
  \\ simp [sym_equation, BIT0_0, numeral_thy_ok_def]
  \\ irule MK_COMB_simple \\ simp [proves_REFL]
QED

Theorem num2bit_dest_numeral:
  dest_numeral (_NUMERAL x) s = (M_success y, s') ∧
  numeral_thy_ok (thyof s.the_context) ⇒
    s = s' ∧ (thyof s.the_context,[]) |- num2bit y === x
Proof
  simp [dest_numeral_def, st_ex_return_def, raise_Failure_def]
  \\ CASE_TAC \\ gs [] \\ rw []
  \\ drule_all dest_num_num2bit \\ rw []
QED

Theorem cval2term_dest_numeral_opt:
  dest_numeral_opt x = SOME y ∧
  compute_thy_ok thy ⇒
    (thy,[]) |- cval2term (Num y) === _CVAL_NUM x
Proof
  simp [dest_numeral_opt_def]
  \\ CASE_TAC \\ gs []
  \\ TOP_CASE_TAC \\ gs []
  \\ CASE_TAC \\ gs [] \\ rw []
  \\ ‘numeral_thy_ok thy’
    by gs [compute_thy_ok_def]
  \\ drule_all dest_num_num2bit \\ rw [cval2term_def]
  \\ drule_then assume_tac num2bit_term_ok
  \\ irule replaceR2 \\ fs []
  \\ irule_at Any sym_equation
  \\ irule_at Any NUMERAL_eqn
  \\ simp [compute_thy_ok_terms_ok]
  \\ ‘term_ok (sigof thy) t0 ∧ t0 has_type num_ty’
    by (drule proves_term_ok
        \\ fs [equation_def, term_ok_def, numeral_thy_ok_terms_ok]
        \\ rw [] \\ fs [WELLTYPED])
  \\ simp [term_ok_welltyped, WELLTYPED_LEMMA, Once term_ok_def,
           welltyped_def, numeral_thy_ok_terms_ok, SF SFY_ss]
  \\ irule MK_COMB_simple
  \\ simp [proves_REFL, term_ok_welltyped, WELLTYPED_LEMMA, Once term_ok_def,
           welltyped_def, compute_thy_ok_terms_ok, SF SFY_ss]
  \\ irule trans_equation_simple
  \\ irule_at Any sym_equation
  \\ first_x_assum (irule_at Any)
  \\ rw [NUMERAL_eqn, sym_equation]
QED

Theorem dest_cval_thm:
  compute_thy_ok thy ⇒
    ∀tm cv.
      dest_cval tm = SOME cv ⇒
      term_ok (sigof thy) tm ⇒
        (thy,[]) |- cval2term cv === tm ∧
        typeof tm = cval_ty
Proof
  strip_tac
  \\ ho_match_mp_tac dest_cval_ind
  \\ ntac 3 strip_tac \\ simp [Once dest_cval_def]
  \\ TOP_CASE_TAC
  \\ TOP_CASE_TAC
  >- ((* variable *)
    fs [CaseEqs ["list", "option"]] \\ rw []
    \\ drule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
    \\ drule_then strip_assume_tac compute_thy_ok_terms_ok
    \\ fs [cval2term_def, proves_REFL, term_ok_def, SF SFY_ss])
  \\ TOP_CASE_TAC
  >- ((* 0-ary *)
    simp [mapOption_def]
    \\ drule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
    \\ rw [app_type]
    \\ drule_then strip_assume_tac compute_thy_ok_terms_ok
    \\ gvs [cval2term_def, cval_consts_def, app_type, proves_REFL])
  \\ TOP_CASE_TAC
  >- ((* unary: num, fst, snd or app *)
    fs [CaseEqs ["list", "option", "bool"]]
    \\ drule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
    \\ rw [] \\ fs []
    \\ gvs [cval2term_dest_numeral_opt] \\ gvs [cval2term_def]
    \\ rename [‘term_ok (sigof thy) tm ⇒ _’]
    \\ ‘term_ok (sigof thy) tm’
      by fs [term_ok_def]
    \\ gvs [app_type_def]
    \\ irule MK_COMB_simple \\ simp []
    \\ irule proves_REFL \\ fs [term_ok_def, SF SFY_ss])
  \\ TOP_CASE_TAC
  >- ((* binary: binop, pair, app *)
    fs [CaseEqs ["list", "option", "bool"]]
    \\ drule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
    \\ rw [] \\ fs []
    \\ rename [‘term_ok _ (Comb (Comb _ x) y)’]
    \\ ‘term_ok (sigof thy) x ∧ term_ok (sigof thy) y’
      by fs [term_ok_def]
    \\ gvs [cval2term_def, bop2term_def, MK_COMB_simple, proves_REFL,
            compute_thy_ok_terms_ok]
    \\ simp [app_type_def, numeralTheory.numeral_funpow]
    \\ irule MK_COMB_simple \\ simp []
    \\ irule MK_COMB_simple \\ simp []
    \\ irule proves_REFL
    \\ fs [term_ok_def, SF SFY_ss])
  \\ TOP_CASE_TAC
  >- ((* ternary: if *)
    fs [CaseEqs ["list", "option", "bool"]]
    \\ drule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
    \\ rw [] \\ fs []
    \\ rename [‘term_ok _ (Comb (Comb (Comb _ x) y) z)’]
    \\ ‘term_ok (sigof thy) x ∧ term_ok (sigof thy) y ∧ term_ok (sigof thy) z’
      by fs [term_ok_def]
    \\ gvs [cval2term_def, app_type_def, numeralTheory.numeral_funpow]
    \\ irule MK_COMB_simple \\ simp []
    \\ irule MK_COMB_simple \\ simp []
    \\ irule MK_COMB_simple
    \\ fs [compute_thy_ok_terms_ok, term_ok_def, proves_REFL, SF SFY_ss])
      (* n-ary: app *)
  \\ fs [CaseEqs ["list", "option", "bool"], SF ETA_ss]
  \\ strip_tac \\ gvs []
  \\ qmatch_asmsub_abbrev_tac ‘mapOption _ tms’
  \\ rename [‘tms = a::b::c::d::e’]
  \\ ‘∀tm. tm = a ∨ tm = b ∨ tm = c ∨ tm = d ∨ MEM tm e ⇔ MEM tm tms’
    by gs [Abbr ‘tms’]
  \\ fs []
  \\ ntac 2 (pop_assum kall_tac)
  \\ strip_tac
  \\ drule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
  \\ simp [cval2term_def, FOLDL_MAP]
  \\ ‘∀tm tm'.
        typeof tm = app_type (LENGTH tms) ∧
        term_ok (sigof thy) tm ∧
        (thy,[]) |- tm === tm' ⇒
          (thy,[]) |- FOLDL (λx y. Comb x (cval2term y)) tm' cvs ===
                      FOLDL Comb tm tms ∧
          typeof (FOLDL Comb tm tms) = cval_ty’
    suffices_by (
      disch_then irule
      \\ drule_then assume_tac mapOption_LENGTH \\ gs []
      \\ irule_at Any proves_REFL \\ fs []
      \\ drule term_ok_FOLDL_Comb \\ rw [])
  \\ qpat_x_assum ‘list_dest_comb _ _ = _’ kall_tac
  \\ dxrule_then strip_assume_tac term_ok_FOLDL_Comb
  \\ qpat_x_assum ‘term_ok _ (Const _ _)’ kall_tac
  \\ ntac 3 (pop_assum mp_tac)
  \\ qid_spec_tac ‘tms’
  \\ qid_spec_tac ‘cvs’
  \\ Induct \\ Cases_on ‘tms’ \\ simp [mapOption_def, app_type, proves_REFL,
                                       CaseEq "option", Once sym_equation]
  \\ ntac 7 strip_tac
  \\ rename [‘mapOption dest_cval tms’]
  \\ first_x_assum (qspec_then ‘tms’ assume_tac)
  \\ gs [SF SFY_ss] \\ first_x_assum irule \\ gs [SF DNF_ss]
  \\ conj_asm1_tac
  >- (
    qpat_x_assum ‘_ |- cval2term _ === _’ assume_tac
    \\ drule proves_term_ok
    \\ simp [term_ok_def, term_ok_welltyped, equation_def, SF SFY_ss])
  \\ irule MK_COMB_simple
  \\ pop_assum mp_tac
  \\ simp [proves_term_ok, term_ok_welltyped, term_ok_def, sym_equation]
QED

Theorem ALOOKUP_MAP_3[local]:
  ∀xs n.
    (∀x y. f x = f y ⇒ x = y) ⇒
      ALOOKUP (MAP (λ(k,v). (f k, g v)) xs) (f n) =
      ALOOKUP (MAP (λ(k,v). (k, g v)) xs) n
Proof
  Induct \\ simp []
  \\ Cases \\ rw [] \\ gs []
QED

Theorem cval_value_closed:
  ∀v. cval_value v ⇒ cval_vars v = {}
Proof
  ho_match_mp_tac cval_value_ind
  \\ rw [cval_value_def, cval_vars_def]
QED

Theorem cval_value_no_consts:
  ∀v. cval_value v ⇒ cval_consts v = {}
Proof
  ho_match_mp_tac cval_value_ind
  \\ rw [cval_value_def, cval_consts_def]
QED

Theorem closed_subst:
  ∀env v.
    (∀n w. MEM (n,w) env ∧ n ∈ cval_vars v ⇒ cval_value w) ∧
    cval_vars v ⊆ set (MAP FST env) ⇒
      cval_vars (subst env v) = {}
Proof
  ho_match_mp_tac subst_ind \\ rw [subst_def]
  \\ gs [cval_vars_def, cval_value_closed, SF SFY_ss, SF DNF_ss]
  >- (
    CASE_TAC \\ gs [ALOOKUP_NONE, MEM_MAP, EXISTS_PROD, PULL_EXISTS]
    \\ drule_then assume_tac ALOOKUP_MEM
    \\ gs [cval_value_closed, SF SFY_ss])
  \\ rw [DISJ_EQ_IMP] \\ gs [SF ETA_ss]
  \\ gs [BIGUNION, SUBSET_DEF, PULL_EXISTS]
  \\ rw [Once EXTENSION] \\ eq_tac \\ rw []
  \\ gvs [MEM_MAP, EXISTS_PROD, PULL_EXISTS, SF SFY_ss]
  \\ last_x_assum (irule_at Any)
  \\ Cases_on ‘cs’ \\ gs [SF DNF_ss]
QED

Theorem closed_subst':
  EVERY cval_value (MAP SND env) ∧
  cval_vars v ⊆ set (MAP FST env) ⇒
    cval_vars (subst env v) = {}
Proof
  rw [EVERY_MEM]
  \\ irule closed_subst
  \\ gs [MEM_MAP, EXISTS_PROD, PULL_EXISTS, SF SFY_ss]
QED

Theorem VSUBST_FOLDL_Comb_push:
  ∀tms t.
    FOLDL Comb (VSUBST is t) (MAP (VSUBST is) tms) =
    VSUBST is (FOLDL Comb t tms)
Proof
  Induct \\ rw [] \\ gs []
  \\ simp [GSYM VSUBST_thm]
QED

Theorem VSUBST_bop2term[simp]:
  VSUBST is (bop2term bop x y) = bop2term bop (VSUBST is x) (VSUBST is y)
Proof
  Cases_on ‘bop’ \\ gs [bop2term_def, VSUBST_thm]
QED

Theorem subst_VSUBST:
  ∀env x.
    EVERY (λv. cval_vars v = {}) (MAP SND env) ∧
    cval_vars x ⊆ set (MAP FST env) ⇒
      cval2term (subst env x) =
      VSUBST (MAP (λ(s,v). (cval2term v, Var s cval_ty)) env) (cval2term x)
Proof
  ho_match_mp_tac subst_ind \\ rw []
  >~ [‘Var n’] >- (
    simp [subst_def, cval2term_def, VSUBST_def, REV_ASSOCD_ALOOKUP,
          MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
    \\ gvs [EVERY_MEM, cval_vars_def]
    \\ CASE_TAC \\ CASE_TAC
    \\ imp_res_tac ALOOKUP_MEM
    \\ gvs [ALOOKUP_NONE, cval2term_def, MEM_MAP, EXISTS_PROD, PULL_EXISTS]
    \\ Q.ISPECL_THEN [‘cval2term’, ‘λs. Var s cval_ty’] assume_tac
                     (GEN_ALL ALOOKUP_MAP_3)
    \\ gs [ALOOKUP_MAP, SF SFY_ss])
  \\ gs [subst_def, cval2term_def, VSUBST_def, cval_vars_def, SF ETA_ss]
  \\ gs [BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS]
  \\ simp [GSYM VSUBST_FOLDL_Comb_push]
  \\ simp [VSUBST_thm]
  \\ AP_TERM_TAC
  \\ simp [MAP_MAP_o, o_DEF, LAMBDA_PROD, MAP_EQ_f]
QED

Theorem subst_REVERSE:
  ∀env v.
    ALL_DISTINCT (MAP FST env) ⇒
      subst (REVERSE env) v = subst env v
Proof
  ho_match_mp_tac subst_ind \\ rw [subst_def]
  \\ rw [alookup_distinct_reverse]
  \\ irule LIST_EQ \\ gvs [EL_MAP, MEM_EL, PULL_EXISTS]
QED

Theorem subst_closed:
  ∀env v. cval_vars v = {} ⇒ subst env v = v
Proof
  ho_match_mp_tac subst_ind
  \\ rw [cval_vars_def, subst_def] \\ gs []
  \\ irule LIST_EQ \\ rgs [Once EXTENSION, EQ_IMP_THM, IMP_CONJ_THM]
  \\ gs [SF DNF_ss, EL_MAP, MEM_EL, PULL_EXISTS]
QED

Theorem subst_closed_APPEND:
  ∀bs v as.
    EVERY (λv. cval_vars v = {}) (MAP SND as) ∧
    EVERY (λv. cval_vars v = {}) (MAP SND bs) ⇒
      subst (as ++ bs) v = subst bs (subst as v)
Proof
  ho_match_mp_tac subst_ind \\ rw [subst_def]
  >- (
    gs [ALL_DISTINCT_APPEND, ALOOKUP_APPEND, EVERY_MEM]
    \\ CASE_TAC \\ gs []
    >- (
      CASE_TAC \\ gs [ALOOKUP_NONE, subst_def]
      \\ CASE_TAC \\ gs []
      \\ drule_then assume_tac ALOOKUP_MEM
      \\ gs [MEM_MAP, EXISTS_PROD, PULL_EXISTS])
    \\ drule_then assume_tac ALOOKUP_MEM
    \\ gs [MEM_MAP, EXISTS_PROD, PULL_EXISTS]
    \\ first_x_assum (drule_all_then assume_tac)
    \\ drule_then assume_tac subst_closed \\ gs [])
  \\ irule LIST_EQ
  \\ gvs [EL_MAP, MEM_EL, PULL_EXISTS]
QED

Theorem MAP_subst_MAP_Var[local]:
 ∀xs ys.
   ALL_DISTINCT xs ∧
   LENGTH xs = LENGTH ys ⇒
     MAP (subst (ZIP(xs,ys))) (MAP Var xs) = ys
Proof
  Induct \\ simp [] \\ Cases_on ‘ys’ \\ rw [subst_def]
  \\ first_x_assum (drule_all_then assume_tac)
  \\ gs [MAP_MAP_o, combinTheory.o_DEF, LIST_EQ_REWRITE, EL_MAP,
         subst_def]
  \\ rw [] \\ gs [MEM_EL]
QED

Theorem do_binop_thm:
  compute_thy_ok thy ⇒
    term_ok (sigof thy) (cval2term p) ∧
    term_ok (sigof thy) (cval2term q) ∧
    (thy,[]) |- cval2term p === cval2term x ∧ cval_value x ∧
    (thy,[]) |- cval2term q === cval2term y ∧ cval_value y ∧
    do_binop bop x y s = (M_success cv, s') ⇒
      (thy,[]) |- bop2term bop (cval2term p) (cval2term q) === cval2term cv
Proof
  ntac 2 strip_tac
  \\ Cases_on ‘bop’ \\ gs [bop2term_def, do_binop_def, do_reln_def]
  >~ [‘_CVAL_ADD _ _’] >- (
    Cases_on ‘∃m. x = Num m’ \\ fs []
    >- (
      Cases_on ‘∃n. y = Num n’ \\ fs []
      >- (
        gvs [do_arith_def, st_ex_return_def, cval2term_def]
        \\ ‘(thy,[]) |- cval2term p === _CVAL_NUM (num2bit m)’
          by (irule trans_equation_simple \\ first_x_assum (irule_at Any)
              \\ simp [MK_COMB_simple, proves_REFL, compute_thy_ok_terms_ok,
                       NUMERAL_eqn, num2bit_term_ok])
        \\ ‘(thy,[]) |- cval2term q === _CVAL_NUM (num2bit n)’
          by (irule trans_equation_simple \\ first_x_assum (irule_at Any)
              \\ simp [MK_COMB_simple, proves_REFL, compute_thy_ok_terms_ok,
                       NUMERAL_eqn, num2bit_term_ok])
        \\ resolve_then Any irule sym_equation replaceL2
        \\ first_x_assum (irule_at Any)
        \\ resolve_then Any irule sym_equation replaceL1
        \\ first_x_assum (irule_at Any)
        \\ resolve_then Any irule sym_equation replaceR2
        \\ irule_at Any NUMERAL_eqn \\ simp [num2bit_term_ok]
        \\ irule replaceL2 \\ irule_at Any ADD_num2bit
        \\ rw [CVAL_ADD_eqn1, sym_equation, num2bit_term_ok])
      \\ ‘cval_value y’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. y = Pair p1 q1’
        by (Cases_on ‘y’ \\ fs [])
      \\ gvs [cval2term_def, do_arith_def, st_ex_return_def]
      \\ ‘term_ok (sigof thy) (cval2term p1) ∧
          term_ok (sigof thy) (cval2term q1)’
        by (drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ rw [CVAL_ADD_eqn2, num2bit_term_ok, compute_thy_ok_terms_ok])
    \\ Cases_on ‘∃n. y = Num n’ \\ gs []
    >- (
      gvs [cval2term_def, do_arith_def, st_ex_return_def]
      \\ ‘cval_value x’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. x = Pair p1 q1’
        by (Cases_on ‘x’ \\ fs [])
      \\ gvs [cval2term_def, do_arith_def, st_ex_return_def]
      \\ ‘term_ok (sigof thy) (cval2term p1) ∧
          term_ok (sigof thy) (cval2term q1)’
        by (qpat_x_assum ‘_ |- _ === _CVAL_PAIR _ _’ assume_tac
            \\ drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ rw [CVAL_ADD_eqn3, num2bit_term_ok, compute_thy_ok_terms_ok])
    \\ gvs [cval2term_def, do_arith_def, st_ex_return_def]
    \\ ‘cval_value x’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p1 q1. x = Pair p1 q1’
      by (Cases_on ‘x’ \\ fs [])
    \\ ‘cval_value y’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p2 q2. y = Pair p2 q2’
      by (Cases_on ‘y’ \\ fs [])
    \\ gvs [cval2term_def, do_arith_def, st_ex_return_def]
    \\ simp [Once num2bit_def]
    \\ ‘EVERY (term_ok (sigof thy) o cval2term) [p1;q1;p2;q2]’
      by (imp_res_tac proves_term_ok
          \\ gs [term_ok_def, equation_def])
    \\ resolve_then Any irule sym_equation replaceL2
    \\ first_x_assum (irule_at Any)
    \\ resolve_then Any irule sym_equation replaceL1
    \\ first_x_assum (irule_at Any)
    \\ fs [] \\ rw [CVAL_ADD_eqn4, compute_thy_ok_terms_ok])
  >~ [‘_CVAL_SUB _ _’] >- (
    Cases_on ‘∃m. x = Num m’ \\ fs []
    >- (
      Cases_on ‘∃n. y = Num n’ \\ fs []
      >- (
        gvs [do_arith_def, st_ex_return_def, cval2term_def]
        \\ ‘(thy,[]) |- cval2term p === _CVAL_NUM (num2bit m)’
          by (irule trans_equation_simple \\ first_x_assum (irule_at Any)
              \\ simp [MK_COMB_simple, proves_REFL, compute_thy_ok_terms_ok,
                       NUMERAL_eqn, num2bit_term_ok])
        \\ ‘(thy,[]) |- cval2term q === _CVAL_NUM (num2bit n)’
          by (irule trans_equation_simple \\ first_x_assum (irule_at Any)
              \\ simp [MK_COMB_simple, proves_REFL, compute_thy_ok_terms_ok,
                       NUMERAL_eqn, num2bit_term_ok])
        \\ resolve_then Any irule sym_equation replaceL2
        \\ first_x_assum (irule_at Any)
        \\ resolve_then Any irule sym_equation replaceL1
        \\ first_x_assum (irule_at Any)
        \\ resolve_then Any irule sym_equation replaceR2
        \\ irule_at Any NUMERAL_eqn \\ simp [num2bit_term_ok]
        \\ irule replaceL2 \\ irule_at Any SUB_num2bit
        \\ rw [CVAL_SUB_eqn1, sym_equation, num2bit_term_ok])
      \\ ‘cval_value y’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. y = Pair p1 q1’
        by (Cases_on ‘y’ \\ fs [])
      \\ gvs [cval2term_def, do_arith_def, st_ex_return_def]
      \\ ‘term_ok (sigof thy) (cval2term p1) ∧
          term_ok (sigof thy) (cval2term q1)’
        by (drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ rw [CVAL_SUB_eqn2, num2bit_term_ok, compute_thy_ok_terms_ok])
    \\ Cases_on ‘∃n. y = Num n’ \\ gs []
    >- (
      gvs [cval2term_def, do_arith_def, st_ex_return_def]
      \\ ‘cval_value x’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. x = Pair p1 q1’
        by (Cases_on ‘x’ \\ fs [])
      \\ gvs [cval2term_def, do_arith_def, st_ex_return_def]
      \\ simp [Once num2bit_def]
      \\ ‘(thy,[]) |- cval2term q === _CVAL_NUM (num2bit n)’
        by (irule trans_equation_simple \\ first_x_assum (irule_at Any)
            \\ simp [MK_COMB_simple, proves_REFL, compute_thy_ok_terms_ok,
                     num2bit_term_ok, NUMERAL_eqn])
      \\ ‘term_ok (sigof thy) (cval2term p1) ∧
          term_ok (sigof thy) (cval2term q1)’
        by (qpat_x_assum ‘_ |- _ === _CVAL_PAIR _ _’ assume_tac
            \\ drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ rw [CVAL_SUB_eqn3, num2bit_term_ok, compute_thy_ok_terms_ok])
    \\ gvs [cval2term_def, do_arith_def, st_ex_return_def]
    \\ ‘cval_value x’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p1 q1. x = Pair p1 q1’
      by (Cases_on ‘x’ \\ fs [])
    \\ ‘cval_value y’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p2 q2. y = Pair p2 q2’
      by (Cases_on ‘y’ \\ fs [])
    \\ gvs [cval2term_def, do_arith_def, st_ex_return_def]
    \\ simp [Once num2bit_def]
    \\ ‘EVERY (term_ok (sigof thy) o cval2term) [p1;q1;p2;q2]’
      by (imp_res_tac proves_term_ok
          \\ gs [term_ok_def, equation_def])
    \\ resolve_then Any irule sym_equation replaceL2
    \\ first_x_assum (irule_at Any)
    \\ resolve_then Any irule sym_equation replaceL1
    \\ first_x_assum (irule_at Any)
    \\ fs [] \\ rw [CVAL_SUB_eqn4, compute_thy_ok_terms_ok])
  >~ [‘_CVAL_MUL _ _’] >- (
    Cases_on ‘∃m. x = Num m’ \\ fs []
    >- (
      Cases_on ‘∃n. y = Num n’ \\ fs []
      >- (
        gvs [do_arith_def, st_ex_return_def, cval2term_def]
        \\ ‘(thy,[]) |- cval2term p === _CVAL_NUM (num2bit m)’
          by (irule trans_equation_simple \\ first_x_assum (irule_at Any)
              \\ simp [MK_COMB_simple, proves_REFL, compute_thy_ok_terms_ok,
                       NUMERAL_eqn, num2bit_term_ok])
        \\ ‘(thy,[]) |- cval2term q === _CVAL_NUM (num2bit n)’
          by (irule trans_equation_simple \\ first_x_assum (irule_at Any)
              \\ simp [MK_COMB_simple, proves_REFL, compute_thy_ok_terms_ok,
                       NUMERAL_eqn, num2bit_term_ok])
        \\ resolve_then Any irule sym_equation replaceL2
        \\ first_x_assum (irule_at Any)
        \\ resolve_then Any irule sym_equation replaceL1
        \\ first_x_assum (irule_at Any)
        \\ resolve_then Any irule sym_equation replaceR2
        \\ irule_at Any NUMERAL_eqn \\ simp [num2bit_term_ok]
        \\ irule replaceL2 \\ irule_at Any MUL_num2bit
        \\ rw [CVAL_MUL_eqn1, sym_equation, num2bit_term_ok])
      \\ ‘cval_value y’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. y = Pair p1 q1’
        by (Cases_on ‘y’ \\ fs [])
      \\ gvs [cval2term_def, do_arith_def, st_ex_return_def]
      \\ ‘term_ok (sigof thy) (cval2term p1) ∧
          term_ok (sigof thy) (cval2term q1)’
        by (drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ ‘(thy,[]) |- cval2term p === _CVAL_NUM (num2bit m)’
        by (irule trans_equation_simple \\ first_x_assum (irule_at Any)
            \\ simp [MK_COMB_simple, proves_REFL, compute_thy_ok_terms_ok,
                     NUMERAL_eqn, num2bit_term_ok])
      \\ simp [Once num2bit_def]
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ rw [CVAL_MUL_eqn2, num2bit_term_ok, compute_thy_ok_terms_ok])
    \\ Cases_on ‘∃n. y = Num n’ \\ gs []
    >- (
      gvs [cval2term_def, do_arith_def, st_ex_return_def]
      \\ ‘cval_value x’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. x = Pair p1 q1’
        by (Cases_on ‘x’ \\ fs [])
      \\ gvs [cval2term_def, do_arith_def, st_ex_return_def]
      \\ ‘term_ok (sigof thy) (cval2term p1) ∧
          term_ok (sigof thy) (cval2term q1)’
        by (qpat_x_assum ‘_ |- _ === _CVAL_PAIR _ _’ assume_tac
            \\ drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ ‘(thy,[]) |- cval2term q === _CVAL_NUM (num2bit n)’
        by (irule trans_equation_simple \\ first_x_assum (irule_at Any)
            \\ simp [MK_COMB_simple, proves_REFL, compute_thy_ok_terms_ok,
                     NUMERAL_eqn, num2bit_term_ok])
      \\ simp [Once num2bit_def]
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ rw [CVAL_MUL_eqn3, num2bit_term_ok, compute_thy_ok_terms_ok])
    \\ gvs [cval2term_def, do_arith_def, st_ex_return_def]
    \\ ‘cval_value x’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p1 q1. x = Pair p1 q1’
      by (Cases_on ‘x’ \\ fs [])
    \\ ‘cval_value y’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p2 q2. y = Pair p2 q2’
      by (Cases_on ‘y’ \\ fs [])
    \\ gvs [cval2term_def, do_arith_def, st_ex_return_def]
    \\ simp [Once num2bit_def]
    \\ ‘EVERY (term_ok (sigof thy) o cval2term) [p1;q1;p2;q2]’
      by (imp_res_tac proves_term_ok
          \\ gs [term_ok_def, equation_def])
    \\ resolve_then Any irule sym_equation replaceL2
    \\ first_x_assum (irule_at Any)
    \\ resolve_then Any irule sym_equation replaceL1
    \\ first_x_assum (irule_at Any)
    \\ fs [] \\ rw [CVAL_MUL_eqn4, compute_thy_ok_terms_ok])
  >~ [‘_CVAL_LESS _ _’] >- (
    Cases_on ‘∃m. x = Num m’ \\ fs []
    >- (
      Cases_on ‘∃n. y = Num n’ \\ fs []
      >- (
        gvs [do_reln_def, st_ex_return_def, cval2term_def]
        \\ qmatch_asmsub_abbrev_tac ‘_ |- cval2term p === A’
        \\ qmatch_asmsub_abbrev_tac ‘_ |- cval2term q === B’
        \\ ‘(thy,[]) |- _CVAL_NUM (_NUMERAL (num2bit (if m < n then 1 else 0)))
                    === _CVAL_LESS A B’
          suffices_by (
            rw [Abbr ‘A’, Abbr ‘B’]
            \\ resolve_then Any irule sym_equation replaceL2
            \\ first_x_assum (irule_at Any)
            \\ resolve_then Any irule sym_equation replaceL1
            \\ first_x_assum (irule_at Any)
            \\ fs [cval2term_def, sym_equation])
        \\ unabbrev_all_tac
        \\ irule replaceR2 \\ irule_at Any MK_COMB_simple
        \\ resolve_then Any (irule_at Any) NUMERAL_eqn sym_equation
        \\ irule_at Any proves_REFL
        \\ simp [compute_thy_ok_terms_ok, num2bit_term_ok]
        \\ irule replaceL1 \\ irule_at Any MK_COMB_simple
        \\ resolve_then Any (irule_at Any) NUMERAL_eqn sym_equation
        \\ irule_at Any proves_REFL
        \\ simp [compute_thy_ok_terms_ok, num2bit_term_ok]
        \\ irule trans_equation_simple \\ irule_at Any CVAL_LESS_eqn1
        \\ simp [num2bit_term_ok]
        \\ irule MK_COMB_simple \\ simp [proves_REFL, compute_thy_ok_terms_ok]
        \\ irule replaceL3 \\ irule_at Any bool2term_LESS_num2bit \\ simp []
        \\ ‘(thy,[]) |- _NUMERAL (_SUC _0) === _SUC (_NUMERAL _0)’
          by (irule trans_equation_simple
              \\ irule_at Any NUMERAL_eqn
              \\ simp [compute_thy_ok_terms_ok]
              \\ resolve_then Any irule sym_equation replaceR2
              \\ irule_at Any NUMERAL_eqn
              \\ gs [compute_thy_ok_terms_ok, proves_REFL])
        \\ irule replaceL1 \\ first_x_assum (irule_at Any)
        \\ resolve_then Any irule sym_equation replaceR2
        \\ irule_at Any num2bit_num2term \\ simp []
        \\ once_rewrite_tac [ONE]
        \\ IF_CASES_TAC \\ simp [bool2term_def, num2term_def]
        \\ gs [sym_equation, COND_eqn, compute_thy_ok_terms_ok])
      \\ ‘cval_value y’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. y = Pair p1 q1’
        by (Cases_on ‘y’ \\ fs [])
      \\ gvs [cval2term_def, do_reln_def, st_ex_return_def]
      \\ ‘term_ok (sigof thy) (cval2term p1) ∧
          term_ok (sigof thy) (cval2term q1)’
        by (drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ simp [Once num2bit_def, SimpR “(===)”]
      \\ rw [CVAL_LESS_eqn2, num2bit_term_ok])
    \\ Cases_on ‘∃n. y = Num n’ \\ gs []
    >- (
      gvs [cval2term_def, st_ex_return_def]
      \\ ‘cval_value x’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. x = Pair p1 q1’
        by (Cases_on ‘x’ \\ fs [])
      \\ gvs [cval2term_def, do_reln_def, st_ex_return_def]
      \\ ‘term_ok (sigof thy) (cval2term p1) ∧
          term_ok (sigof thy) (cval2term q1)’
        by (qpat_x_assum ‘_ |- _ === _CVAL_PAIR _ _’ assume_tac
            \\ drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ simp [Once num2bit_def, SimpR “(===)”]
      \\ rw [CVAL_LESS_eqn3, num2bit_term_ok])
    \\ gvs [cval2term_def, st_ex_return_def]
    \\ ‘cval_value x’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p1 q1. x = Pair p1 q1’
      by (Cases_on ‘x’ \\ fs [])
    \\ ‘cval_value y’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p2 q2. y = Pair p2 q2’
      by (Cases_on ‘y’ \\ fs [])
    \\ gvs [cval2term_def, do_reln_def, st_ex_return_def]
    \\ simp [Once num2bit_def]
    \\ ‘EVERY (term_ok (sigof thy) o cval2term) [p1;q1;p2;q2]’
      by (imp_res_tac proves_term_ok
          \\ gs [term_ok_def, equation_def])
    \\ resolve_then Any irule sym_equation replaceL2
    \\ first_x_assum (irule_at Any)
    \\ resolve_then Any irule sym_equation replaceL1
    \\ first_x_assum (irule_at Any)
    \\ gs [CVAL_LESS_eqn4])
QED

Theorem term_ok_bop2term:
  term_ok sig (bop2term bop tm1 tm2) ⇒
    term_ok sig tm1 ∧ term_ok sig tm2
Proof
  Cases_on ‘bop’ \\ rw [term_ok_def, bop2term_def]
QED

Theorem compute_eval_thm:
  compute_thy_ok thy ⇒
    ∀ck eqs cv s cv' s' tm.
      compute_eval ck eqs cv s = (M_success cv', s') ∧
      term_ok (sigof thy) (cval2term cv) ∧
      cval_vars cv = {} ∧
      EVERY (λ(f,vs,cv).
        ALL_DISTINCT vs ∧
        ∃r. (thy,[]) |- cval2term (App f (MAP Var vs)) === r ∧
            dest_cval r = SOME cv ∧
            cval_vars cv ⊆ set vs) eqs ⇒
        (thy,[]) |- cval2term cv === cval2term cv'
Proof
  strip_tac \\ fs []
  \\ ho_match_mp_tac compute_eval_ind
  \\ rpt gen_tac \\ strip_tac
  \\ rpt gen_tac \\ strip_tac
  \\ qpat_x_assum ‘compute_eval _ _ _ _ = _’ mp_tac
  \\ simp_tac std_ss [Once compute_eval_def, st_ex_return_def]
  \\ Cases_on ‘∃p q. cv = Pair p q’
  >- (
    pop_assum (qx_choosel_then [‘p’, ‘q’] SUBST_ALL_TAC) \\ fs []
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
    \\ first_x_assum (drule_then strip_assume_tac)
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
    \\ first_x_assum (drule_then strip_assume_tac)
    \\ strip_tac \\ gvs [term_ok_def, cval_vars_def]
    \\ fs [cval2term_def, term_ok_def, MK_COMB_simple, proves_REFL, SF SFY_ss])
  \\ Cases_on ‘∃n. cv = Num n’
  >- (
    pop_assum (CHOOSE_THEN SUBST_ALL_TAC) \\ fs []
    \\ strip_tac \\ gvs []
    \\ simp [compute_eval_def, proves_REFL, cval2term_term_ok, cval_vars_def,
             SF SFY_ss])
  \\ Cases_on ‘∃p. cv = Fst p’
  >- (
    pop_assum (CHOOSE_THEN SUBST_ALL_TAC) \\ fs [] \\ gvs [cval2term_def]
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
    \\ strip_tac
    \\ drule_then strip_assume_tac do_fst_thm \\ gvs []
    \\ gs [term_ok_def, cval_vars_def]
    \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
    \\ rename [‘do_fst p r = (M_success cv,_)’]
    \\ drule_then assume_tac compute_eval_value
    \\ drule_then assume_tac cval_value_no_consts
    \\ Cases_on ‘∃p1 q1. p = Pair p1 q1’ \\ gvs []
    >- (
      gvs [do_fst_def, st_ex_return_def, cval2term_def]
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ gs [CVAL_FST_eqn1, cval2term_term_ok, cval_consts_def])
    \\ ‘cv = Num 0’
      by (Cases_on ‘p’ \\ gs [do_fst_def, st_ex_return_def])
    \\ drule_then assume_tac compute_eval_value
    \\ ‘∃m. p = Num m’
      by (Cases_on ‘p’ \\ gs [])
    \\ gvs [cval2term_def]
    \\ resolve_then Any irule sym_equation replaceL2
    \\ first_x_assum (irule_at Any)
    \\ simp [Once num2bit_def, SimpR “(===)”]
    \\ irule CVAL_FST_eqn2
    \\ simp [Ntimes has_type_cases 3]
    \\ gs [term_ok_def, compute_thy_ok_terms_ok, num2bit_term_ok])
  \\ Cases_on ‘∃p. cv = Snd p’
  >- (
    pop_assum (CHOOSE_THEN SUBST_ALL_TAC) \\ fs [] \\ gvs [cval2term_def]
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
    \\ strip_tac
    \\ drule_then strip_assume_tac do_snd_thm \\ gvs []
    \\ gs [term_ok_def, cval_vars_def]
    \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
    \\ rename [‘do_snd p r = (M_success cv,_)’]
    \\ drule_then assume_tac compute_eval_value
    \\ drule_then assume_tac cval_value_no_consts
    \\ Cases_on ‘∃p1 q1. p = Pair p1 q1’ \\ gvs []
    >- (
      gvs [do_snd_def, st_ex_return_def, cval2term_def]
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ gs [CVAL_SND_eqn1, cval2term_term_ok, cval_consts_def])
    \\ ‘cv = Num 0’
      by (Cases_on ‘p’ \\ gs [do_snd_def, st_ex_return_def])
    \\ drule_then assume_tac compute_eval_value
    \\ ‘∃m. p = Num m’
      by (Cases_on ‘p’ \\ gs [])
    \\ gvs [cval2term_def]
    \\ resolve_then Any irule sym_equation replaceL2
    \\ first_x_assum (irule_at Any)
    \\ simp [Once num2bit_def, SimpR “(===)”]
    \\ irule CVAL_SND_eqn2
    \\ simp [Ntimes has_type_cases 3]
    \\ gs [term_ok_def, compute_thy_ok_terms_ok, num2bit_term_ok])
  \\ Cases_on ‘∃s. cv = Var s’
  >- (
    pop_assum (CHOOSE_THEN SUBST_ALL_TAC) \\ fs []
    \\ gs [raise_Type_error_def])
  \\ Cases_on ‘∃p q r. cv = If p q r’
  >- (
    pop_assum (qx_choosel_then [‘p’, ‘q’, ‘r’] SUBST_ALL_TAC)
    \\ simp_tac (srw_ss()) [Once st_ex_bind_def, raise_Type_error_def]
    \\ CASE_TAC \\ CASE_TAC
    \\ rename [‘compute_eval _ _ _ _ = (M_success cv', _)’]
    \\ fs [cval_vars_def]
    \\ Cases_on ‘cv' = Num 0’
    >- (
      pop_assum SUBST_ALL_TAC \\ simp_tac (srw_ss()) []
      \\ strip_tac
      \\ first_x_assum (drule o SIMPR [])
      \\ first_x_assum (drule o SIMPR [])
      \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac) \\ gs []
      \\ gs [cval2term_def, term_ok_def] \\ rw []
      \\ resolve_then Any irule sym_equation replaceL3
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_assum (irule_at Any)
      \\ simp [cval2term_def, Once num2bit_def]
      \\ irule_at Any CVAL_IF_eqn3 \\ gs []
      \\ drule_then assume_tac proves_term_ok
      \\ fs [equation_def, term_ok_def])
    \\ Cases_on ‘∃x y. cv' = Pair x y’
    >- (
      pop_assum (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))
      \\ simp_tac (srw_ss()) [] \\ strip_tac
      \\ first_x_assum (drule o SIMPR [])
      \\ first_x_assum (drule o SIMPR [])
      \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac) \\ gs []
      \\ fs [cval2term_def]
      \\ fs [term_ok_def] \\ rw []
      \\ resolve_then Any irule sym_equation replaceL3
      \\ first_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_assum (irule_at Any)
      \\ fs [cval2term_def, cval_vars_def]
      \\ irule_at Any CVAL_IF_eqn2 \\ gs []
      \\ imp_res_tac proves_term_ok
      \\ fs [equation_def, term_ok_def])
    \\ Cases_on ‘∃n. cv' = Num (SUC n)’
    >- (
      pop_assum (CHOOSE_THEN SUBST_ALL_TAC)
      \\ simp_tac (srw_ss()) [] \\ strip_tac
      \\ first_x_assum (drule o SIMPR [])
      \\ first_x_assum (drule o SIMPR [])
      \\ first_x_assum (drule o SIMPR [])
      \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac) \\ gs []
      \\ fs [cval2term_def]
      \\ fs [term_ok_def] \\ rw []
      \\ resolve_then Any irule sym_equation replaceL3
      \\ first_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_assum (irule_at Any)
      \\ fs [cval2term_def]
      \\ irule replaceL3 \\ Q.REFINE_EXISTS_TAC ‘_CVAL_NUM x’
      \\ irule_at Any MK_COMB_simple
      \\ simp [proves_REFL, compute_thy_ok_terms_ok]
      \\ resolve_then Any (irule_at Any) NUMERAL_eqn sym_equation
      \\ simp [num2bit_term_ok, compute_thy_ok_def, compute_thy_ok_terms_ok,
               proves_REFL]
      \\ irule replaceL3 \\ Q.REFINE_EXISTS_TAC ‘_CVAL_NUM x’
      \\ irule_at Any MK_COMB_simple
      \\ resolve_then Any (irule_at Any) num2bit_num2term sym_equation
      \\ simp [num2bit_term_ok, compute_thy_ok_def, compute_thy_ok_terms_ok,
               proves_REFL]
      \\ simp [num2term_def]
      \\ irule CVAL_IF_eqn1 \\ fs [num2term_term_ok]
      \\ imp_res_tac proves_term_ok
      \\ fs [equation_def, term_ok_def])
    \\ CASE_TAC \\ gs []
    \\ CASE_TAC \\ gs [])
  \\ Cases_on ‘∃bop p q. cv = Binop bop p q’
  >- (
    pop_assum (qx_choosel_then [‘bop’, ‘p’, ‘q’] SUBST_ALL_TAC) \\ fs []
    \\ fs [cval2term_def, term_ok_def]
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
    \\ first_x_assum (drule_then strip_assume_tac)
    \\ first_x_assum (drule_then strip_assume_tac)
    \\ gs [cval_vars_def]
    \\ rename [‘do_binop bop x y s’] \\ strip_tac
    \\ drule_then strip_assume_tac term_ok_bop2term \\ gvs []
    \\ imp_res_tac compute_eval_value
    \\ drule_all do_binop_thm \\ gs [])
  \\ Cases_on ‘∃f cs. cv = App f cs’
  >- (
    pop_assum (qx_choosel_then [‘f’, ‘cs’] SUBST_ALL_TAC)
    \\ simp_tac (srw_ss()) [raise_Timeout_def]
    \\ IF_CASES_TAC \\ simp_tac (srw_ss()) []
    \\ simp_tac (srw_ss()) [option_def, Once st_ex_bind_def,
                            raise_Type_error_def, st_ex_return_def]
    \\ CASE_TAC
    \\ pairarg_tac \\ pop_assum SUBST_ALL_TAC
    \\ simp_tac (srw_ss()) [check_def, raise_Type_error_def, st_ex_return_def,
                            Once st_ex_ignore_bind_def]
    \\ IF_CASES_TAC \\ simp_tac (srw_ss()) []
    \\ simp_tac (srw_ss()) [Once st_ex_bind_def]
    \\ CASE_TAC \\ CASE_TAC \\ strip_tac
    \\ first_x_assum (drule o SIMPR [])
    \\ first_x_assum (drule o SIMPR [])
    \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac)
    \\ strip_tac \\ gvs []
    \\ disch_then drule \\ gs []
    \\ drule_then strip_assume_tac map_thm \\ gvs []
    \\ qpat_x_assum ‘term_ok _ (cval2term _)’
                    (strip_assume_tac o SIMPR [cval2term_def])
    \\ drule_then strip_assume_tac term_ok_FOLDL_Comb \\ gvs [EVERY_MAP]
    \\ drule_then ASSUME_TAC ALOOKUP_MEM
    \\ rename [‘ZIP(as,bs)’]
    \\ gvs [EVERY_MEM, FORALL_PROD]
    \\ first_x_assum (drule_then strip_assume_tac)
    \\ rename [‘dest_cval rhs = SOME exp’]
    \\ qmatch_asmsub_abbrev_tac ‘_ |- lhs === rhs’
    \\ ‘term_ok (sigof thy) lhs ∧ term_ok (sigof thy) rhs’
      by (imp_res_tac proves_term_ok
          \\ gs [term_ok_def, equation_def])
    \\ unabbrev_all_tac
    \\ drule_then drule dest_cval_thm \\ gs [] \\ strip_tac
    \\ ‘∀n. n < LENGTH bs ⇒
              cval_value (EL n bs) ∧ term_ok (sigof thy) (cval2term (EL n bs))’
      by (gen_tac
          \\ strip_tac
          \\ irule_at Any compute_eval_value
          \\ first_x_assum (drule_then strip_assume_tac)
          \\ first_assum (irule_at Any)
          \\ gs [MEM_EL, PULL_EXISTS]
          \\ first_x_assum (drule_all_then assume_tac)
          \\ first_x_assum (drule_then drule)
          \\ gs [cval_vars_def]
          \\ impl_tac
          >- (
            qpat_x_assum ‘set _ = {_}’ mp_tac
            \\ simp [Once EXTENSION, EQ_IMP_THM]
            \\ rw [SF DNF_ss]
            \\ gs [MEM_EL, PULL_EXISTS, EL_MAP])
          \\ strip_tac
          \\ drule_then assume_tac proves_term_ok
          \\ gs [equation_def, term_ok_def])
    \\ impl_keep_tac
    >- (
      irule_at Any closed_subst'
      \\ irule_at Any subst_term_ok
      \\ gvs [MAP_ZIP, EVERY_EL, PULL_EXISTS]
      \\ drule proves_term_ok \\ simp [equation_def, term_ok_def] \\ rw [])
    \\ rw []
    \\ irule trans_equation_simple
    \\ first_x_assum (irule_at Any) \\ gvs [SF ETA_ss]
    (*
    \\ ‘(thy,[]) |- rhs === cval2term (App f (MAP Var as))’
      by (irule sym_equation
          \\ simp [cval2term_def, MAP_MAP_o, combinTheory.o_DEF])
    \\ ‘(thy,[]) |- cval2term exp === cval2term (App f (MAP Var as))’
      by (irule trans_equation_simple
          \\ first_x_assum (irule_at Any)
          \\ rw [sym_equation])*)
    \\ ‘(thy,[]) |- VSUBST (MAP (λ(s,v). (cval2term v, Var s cval_ty))
                                (ZIP (as,bs)))
                           (cval2term exp === cval2term (App f (MAP Var as)))’
      by (qspecl_then [‘c’,‘[]’] (irule o SIMPR []) proves_INST
          \\ simp [MEM_MAP, EXISTS_PROD, PULL_EXISTS]
          \\ rw [MEM_ZIP] \\ gs [SF SFY_ss]
          \\ irule trans_equation_simple
          \\ first_x_assum (irule_at Any)
          \\ rw [sym_equation])
    \\ ‘(thy,[]) |- VSUBST (MAP (λ(s,v). (cval2term v, Var s cval_ty))
                                (ZIP (as,bs))) (cval2term exp) ===
                    VSUBST (MAP (λ(s,v). (cval2term v, Var s cval_ty))
                                (ZIP (as,bs))) (cval2term (App f (MAP Var as)))’
      by (qmatch_goalsub_abbrev_tac ‘VSUBST env’
          \\ qpat_x_assum ‘_ |- VSUBST _ _’ mp_tac
          \\ simp [Once equation_def]
          \\ simp [VSUBST_thm]
          \\ ‘typeof (VSUBST env (cval2term exp)) = cval_ty’
            by (irule WELLTYPED_LEMMA
                \\ irule VSUBST_HAS_TYPE
                \\ gs [Abbr ‘env’, MEM_MAP, EXISTS_PROD, PULL_EXISTS])
          \\ pop_assum (SUBST1_TAC o SYM)
          \\ simp [GSYM equation_def])
    \\ ‘(thy,[]) |- cval2term (subst (ZIP(as,bs)) exp) ===
                    cval2term (subst (ZIP(as,bs)) (App f (MAP Var as)))’
      by (DEP_REWRITE_TAC [subst_VSUBST]
          \\ simp [MAP_ZIP, cval_vars_def, MAP_MAP_o, combinTheory.o_DEF,
                   BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS]
          \\ rw [EVERY_EL]
          \\ first_x_assum (drule_then strip_assume_tac)
          \\ drule_then assume_tac cval_value_closed \\ gs [])
    \\ resolve_then Any irule trans_equation_simple sym_equation
    \\ first_x_assum (irule_at Any)
    \\ simp [subst_def, SF ETA_ss]
    \\ simp [MAP_subst_MAP_Var, cval2term_def]
    \\ ‘∀xs ys tm tm1.
          LENGTH xs = LENGTH ys ∧
          tm has_type app_type (LENGTH xs) ∧
          (thy,[]) |- tm === tm1 ∧
          (∀n.
             n < LENGTH xs ⇒
               (thy,[]) |- cval2term (EL n xs) ===  cval2term (EL n ys)) ⇒
            (thy,[]) |- FOLDL Comb tm (MAP cval2term xs) ===
                        FOLDL Comb tm1 (MAP cval2term ys)’
      suffices_by (
        simp [SF ETA_ss]
        \\ disch_then irule
        \\ simp [proves_REFL]
        \\ gs [has_type_rules] \\ rw []
        \\ first_x_assum (drule_then strip_assume_tac)
        \\ first_x_assum (drule_then strip_assume_tac)
        \\ gs [MEM_EL, PULL_EXISTS]
        \\ first_x_assum (drule_then drule) \\ gs []
        \\ impl_tac \\ rw [sym_equation]
        \\ qpat_x_assum ‘cval_vars (App _ _) = {}’ mp_tac
        \\ dsimp [cval_vars_def, Once EXTENSION, MEM_EL, EL_MAP, DISJ_COMM,
                  DISJ_EQ_IMP]
        \\ rw [] \\ first_x_assum drule
        \\ rw [EXTENSION])
    \\ Induct \\ simp [app_type, proves_REFL]
    \\ qx_gen_tac ‘x’ \\ Cases_on ‘ys’ \\ simp []
    \\ rw [] \\ first_x_assum irule \\ gs []
    \\ irule_at Any MK_COMB_simple
    \\ ‘term_ok (sigof thy) tm1 ∧ term_ok (sigof thy) tm’
      by (drule_then assume_tac proves_term_ok
          \\ gs [term_ok_def, equation_def])
    \\ gs [term_ok_welltyped, SF SFY_ss]
    \\ irule_at Any WELLTYPED_LEMMA
    \\ qexists_tac ‘app_type (LENGTH t)’ \\ simp []
    \\ simp [Once has_type_cases]
    \\ first_x_assum (irule_at Any) \\ gs []
    \\ conj_tac >- (first_x_assum (qspec_then ‘0’ mp_tac) \\ gs [])
    \\ rw [] \\ first_x_assum (qspec_then ‘SUC n’ assume_tac) \\ gs [])
  \\ Cases_on ‘cv’ \\ fs []
QED

Theorem compute_eval_run_thm:
  compute_thy_ok thy ⇒
    compute_eval_run ck eqs cv = M_success cv' ∧
    cval_vars cv = {} ∧
    term_ok (sigof thy) (cval2term cv) ∧
    EVERY (λ(f,vs,cv).
      ALL_DISTINCT vs ∧
      ∃l r. (thy,[]) |- l === r ∧
            list_dest_comb [] l = Const f (app_type (LENGTH vs))::
                                  MAP (λs. Var s cval_ty) vs ∧
            dest_cval r = SOME cv ∧ cval_vars cv ⊆ set vs) eqs ⇒
            (thy,[]) |- cval2term cv === cval2term cv' ∧
            cval_consts cv' = {}
Proof
  simp [compute_eval_run_def, run_def]
  \\ strip_tac \\ strip_tac
  \\ gs [FST_EQ_EQUIV]
  \\ drule compute_eval_thm
  \\ disch_then drule \\ simp []
  \\ drule_then assume_tac compute_eval_value
  \\ drule_then assume_tac cval_value_no_consts
  \\ impl_tac \\ rw []
  \\ gs [EVERY_MEM, FORALL_PROD]
  \\ rw [] \\ gs [SF SFY_ss]
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ drule_then strip_assume_tac list_dest_comb_folds_back
  \\ gvs [cval2term_def, MAP_MAP_o, combinTheory.o_DEF, SF SFY_ss]
QED

val _ = export_theory ();

