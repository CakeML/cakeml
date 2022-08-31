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
    ∃q. res = M_success q ∧ cexp_consts q ⊆ cexp_consts p
Proof
  Cases_on ‘p’ \\ rw [do_fst_def, cexp_consts_def, st_ex_return_def]
QED

Theorem do_snd_thm:
  do_snd p s = (res, s') ⇒
    s = s' ∧
    ∃q. res = M_success q ∧ cexp_consts q ⊆ cexp_consts p
Proof
  Cases_on ‘p’ \\ rw [do_snd_def, cexp_consts_def, st_ex_return_def]
QED

Theorem do_ispair_thm:
  do_ispair p s = (res, s') ⇒
    s = s' ∧
    ∃q. res = M_success q ∧ cexp_consts q ⊆ cexp_consts p
Proof
  Cases_on ‘p’ \\ rw [do_ispair_def, cexp_consts_def, st_ex_return_def]
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
    term_ok ctxt (cexp2term cv) ∧
    EVERY (term_ok ctxt o cexp2term) (MAP SND env) ⇒
      term_ok ctxt (cexp2term (subst env cv))
Proof
  ho_match_mp_tac subst_ind \\ rw []
  >~ [‘Var _’] >- (
    gs [subst_def, cexp2term_def]
    \\ CASE_TAC \\ imp_res_tac ALOOKUP_MEM
    \\ gvs [cexp2term_def, EVERY_MEM, MEM_MAP, PULL_EXISTS, EXISTS_PROD,
            term_ok_def, SF SFY_ss])
  \\ gs [subst_def, cexp2term_def, EVERY_MEM, MEM_MAP, EXISTS_PROD, PULL_EXISTS,
         term_ok_def, SF SFY_ss]
  >~ [‘uop2term uop _’] >- (
    Cases_on ‘uop’
    \\ gs [subst_def, cexp2term_def, EVERY_MEM, MEM_MAP, EXISTS_PROD,
           uop2term_def, PULL_EXISTS, term_ok_def, SF SFY_ss])
  >~ [‘bop2term bop _ _’] >- (
    Cases_on ‘bop’
    \\ gs [subst_def, cexp2term_def, EVERY_MEM, MEM_MAP, EXISTS_PROD,
           bop2term_def, PULL_EXISTS, term_ok_def, SF SFY_ss])
  >~ [‘FILTER _ _’] >- (
    last_x_assum irule
    \\ rw [MEM_FILTER]
    \\ gs [SF SFY_ss])
  \\ ‘∀tm tms.
        term_ok ctxt tm ∧
        tm has_type (app_type (LENGTH tms)) ∧
        EVERY (term_ok ctxt) tms ∧
        EVERY (λtm. tm has_type Cexp) tms ⇒
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

Theorem do_arith_value:
  ∀opn x y s z s'.
    do_arith opn x y s = (M_success z, s') ⇒ cexp_value z
Proof
  ho_match_mp_tac do_arith_ind \\ rw [do_arith_def, st_ex_return_def] \\ fs []
QED

Theorem do_reln_value:
  ∀opn x y s z s'.
    do_reln opn x y s = (M_success z, s') ⇒ cexp_value z
Proof
  ho_match_mp_tac do_reln_ind \\ rw [do_reln_def, st_ex_return_def] \\ fs []
QED

Theorem do_eq_value:
  do_eq (x:compute_exp) y (s:'a) = (M_success z, s') ⇒ cexp_value z
Proof
  rw [do_eq_def, st_ex_return_def] \\ fs []
QED

Theorem do_binop_value:
  ∀bop x y z s s'.
    do_binop bop x y s = (M_success z, s') ⇒ cexp_value z
Proof
  Cases \\ rw [do_binop_def]
  \\ gs [do_arith_value, do_reln_value, do_eq_value, SF SFY_ss]
QED

Theorem compute_eval_value:
  (∀ck ceqs cv s x s'.
    compute_eval ck ceqs cv s = (M_success x, s') ⇒ cexp_value x) ∧
  (∀ck ceqs cvs s xs s'.
    compute_eval_list ck ceqs cvs s = (M_success xs, s') ⇒ EVERY cexp_value xs)
Proof
  ho_match_mp_tac compute_eval_ind \\ rw []
  \\ gvs [compute_eval_def, raise_Failure_def, st_ex_return_def]
  \\ qpat_x_assum ‘_ = (M_success _, _)’ mp_tac
  >- ((* Pair *)
    simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
    \\ CASE_TAC \\ gs [st_ex_return_def]
    \\ rw [] \\ fs [SF SFY_ss])
  >- ((* Uop *)
    simp [Once st_ex_bind_def]
    \\ TOP_CASE_TAC \\ gs [] \\ TOP_CASE_TAC \\ gs [] \\ rw []
    \\ first_x_assum (drule_then assume_tac) \\ gs []
    \\ rename [‘do_uop p’]
    \\ Cases_on ‘p’ \\ gvs [do_uop_def]
    \\ rename [‘_ a r = (M_success x,_)’]
    \\ Cases_on ‘a’ \\ gs [do_fst_def, do_snd_def, do_ispair_def,
                           st_ex_return_def])
  >- ((* Binop *)
    simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
    \\ rw [] \\ drule do_binop_value \\ rw [])
  >- ((* App *)
    IF_CASES_TAC \\ gs []
    \\ simp [option_def, Once st_ex_bind_def, st_ex_return_def,
             raise_Failure_def]
    \\ CASE_TAC \\ gs [] \\ pairarg_tac \\ gvs []
    \\ simp [check_def, raise_Failure_def, st_ex_return_def,
             st_ex_ignore_bind_def]
    \\ IF_CASES_TAC \\ gs []
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
    \\ CASE_TAC \\ gs [] \\ rw []
    \\ last_x_assum irule
    \\ first_x_assum (irule_at Any))
  >- ((* If *)
    simp [Once st_ex_bind_def]
    \\ TOP_CASE_TAC \\ gs [] \\ TOP_CASE_TAC \\ gs []
    \\ TOP_CASE_TAC \\ gs [SF SFY_ss]
    \\ TOP_CASE_TAC \\ gs [SF SFY_ss])
  >- ((* Let *)
    IF_CASES_TAC \\ gs []
    \\ simp [Once st_ex_bind_def]
    \\ TOP_CASE_TAC \\ gs [] \\ TOP_CASE_TAC \\ gs []
    \\ rw [] \\ gs [SF SFY_ss])
  >- ((* List *)
    simp [Once st_ex_bind_def]
    \\ TOP_CASE_TAC \\ gs [] \\ TOP_CASE_TAC \\ gs []
    \\ simp [Once st_ex_bind_def]
    \\ TOP_CASE_TAC \\ TOP_CASE_TAC \\ rw [] \\ gs [SF SFY_ss])
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
        (numeral_thy_ok (thyof ctxt) ⇒ typeof tm = Num) ∧
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

Theorem cexp2term_dest_numeral_opt:
  dest_numeral_opt x = SOME y ∧
  compute_thy_ok thy ⇒
    (thy,[]) |- cexp2term (Num y) === _CEXP_NUM x
Proof
  simp [dest_numeral_opt_def]
  \\ CASE_TAC \\ gs []
  \\ TOP_CASE_TAC \\ gs []
  \\ CASE_TAC \\ gs [] \\ rw []
  \\ ‘numeral_thy_ok thy’
    by gs [compute_thy_ok_def]
  \\ drule_all dest_num_num2bit \\ rw [cexp2term_def]
  \\ drule_then assume_tac num2bit_term_ok
  \\ irule replaceR2 \\ fs []
  \\ irule_at Any sym_equation
  \\ irule_at Any NUMERAL_eqn
  \\ simp [compute_thy_ok_terms_ok]
  \\ ‘term_ok (sigof thy) t0 ∧ t0 has_type Num’
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

Theorem dest_cexp_thm:
  compute_thy_ok thy ⇒
    ∀tm cv.
      dest_cexp tm = SOME cv ⇒
      term_ok (sigof thy) tm ⇒
        (thy,[]) |- cexp2term cv === tm ∧
        typeof tm = Cexp
Proof
  strip_tac
  \\ ho_match_mp_tac dest_cexp_ind
  \\ ntac 3 strip_tac \\ simp [Once dest_cexp_def]
  \\ TOP_CASE_TAC
  \\ TOP_CASE_TAC
  >- ((* variable *)
    fs [CaseEqs ["list", "option"]] \\ rw []
    \\ drule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
    \\ fs [cexp2term_def, proves_REFL, term_ok_def, SF SFY_ss])
  \\ TOP_CASE_TAC
  >- ((* LET *)
    fs [CaseEqs ["term", "list", "option"], PULL_EXISTS]
    \\ rpt gen_tac \\ ntac 2 strip_tac \\ gvs []
    \\ simp [cexp2term_def]
    \\ drule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
    \\ ‘is_std_sig (sigof thy)’
      by (irule theory_ok_sig \\ gs [])
    \\ gs [term_ok_clauses]
    \\ irule MK_COMB_simple \\ simp []
    \\ irule MK_COMB_simple \\ simp [proves_REFL]
    \\ irule proves_ABS \\ simp [])
  \\ TOP_CASE_TAC
  >- ((* 0-ary *)
    rw [mapOption_def, app_type]
    \\ drule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
    \\ gvs [cexp2term_def, cexp_consts_def, app_type, proves_REFL])
  \\ TOP_CASE_TAC
  >- ((* unary: num, uop or app *)
    fs [CaseEqs ["list", "option", "bool"]]
    \\ drule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
    \\ rw [] \\ fs []
    \\ gvs [cexp2term_dest_numeral_opt] \\ gvs [cexp2term_def, uop2term_def]
    \\ rename [‘term_ok (sigof thy) tm ⇒ _’]
    \\ ‘term_ok (sigof thy) tm’
      by fs [term_ok_def]
    \\ gvs [app_type_def]
    \\ irule MK_COMB_simple \\ simp []
    \\ irule proves_REFL \\ fs [term_ok_def, SF SFY_ss])
  \\ TOP_CASE_TAC
  >- (
    simp [mapOption_def, CaseEq "option"])
  \\ TOP_CASE_TAC
  >- ((* binary: binop, pair, app *)
    simp [mapOption_def, CaseEq "option", PULL_EXISTS]
    \\ rename [‘MAP _ xs = [x1; SOME x]’] \\ Cases_on ‘x1’ \\ gs []
    \\ fs [CaseEqs ["list", "option", "bool"]]
    \\ drule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
    \\ Cases_on ‘xs’ \\ gvs []
    \\ rw [] \\ fs []
    \\ rename [‘term_ok _ (Comb (Comb _ x) y)’]
    \\ ‘term_ok (sigof thy) x ∧ term_ok (sigof thy) y’
      by fs [term_ok_def]
    \\ gvs [cexp2term_def, bop2term_def, MK_COMB_simple, proves_REFL,
            compute_thy_ok_terms_ok]
    \\ simp [app_type_def, numeralTheory.numeral_funpow]
    \\ irule MK_COMB_simple \\ simp []
    \\ irule MK_COMB_simple \\ simp []
    \\ irule proves_REFL
    \\ fs [term_ok_def, SF SFY_ss])
  \\ TOP_CASE_TAC
  >- (
    simp [mapOption_def, CaseEq "option"])
  \\ TOP_CASE_TAC
  >- ((* ternary: if *)
    simp [mapOption_def, CaseEq "option", PULL_EXISTS]
    \\ rename [‘MAP _ xs = [x1; SOME x; SOME y]’] \\ Cases_on ‘x1’ \\ gs []
    \\ fs [CaseEqs ["list", "option", "bool"]]
    \\ drule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
    \\ Cases_on ‘xs’ \\ gvs []
    \\ rename [‘MAP _ xs = _’] \\ Cases_on ‘xs’ \\ gvs []
    \\ rw [] \\ fs []
    \\ rename [‘term_ok _ (Comb (Comb (Comb _ x) y) z)’]
    \\ ‘term_ok (sigof thy) x ∧ term_ok (sigof thy) y ∧ term_ok (sigof thy) z’
      by fs [term_ok_def]
    \\ gvs [cexp2term_def, app_type_def, numeralTheory.numeral_funpow]
    \\ irule MK_COMB_simple \\ simp []
    \\ irule MK_COMB_simple \\ simp []
    \\ irule MK_COMB_simple
    \\ fs [compute_thy_ok_terms_ok, term_ok_def, proves_REFL, SF SFY_ss])
      (* n-ary: app *)
  \\ fs [CaseEqs ["list", "option", "bool"], SF ETA_ss]
  \\ strip_tac \\ gvs []
  \\ qpat_x_assum ‘∀x y z w. _ ∧ (_ = «LET» ∧ _) ∧ _ ⇒ _’ kall_tac
  \\ qpat_x_assum ‘_ = «LET» ⇒ _’ kall_tac
  \\ qmatch_asmsub_abbrev_tac ‘mapOption _ tms’
  \\ rename [‘tms = a::b::c::d::e’]
  \\ ‘∀tm. tm = a ∨ tm = b ∨ tm = c ∨ tm = d ∨ MEM tm e ⇔ MEM tm tms’
    by gs [Abbr ‘tms’]
  \\ fs []
  \\ ntac 2 (pop_assum kall_tac)
  \\ strip_tac
  \\ drule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
  \\ simp [cexp2term_def, FOLDL_MAP]
  \\ rename [‘mapOption I (MAP dest_cexp tms)’]
  \\ ‘∀tm tm'.
        typeof tm = app_type (LENGTH tms) ∧
        term_ok (sigof thy) tm ∧
        (thy,[]) |- tm === tm' ⇒
          (thy,[]) |- FOLDL (λx y. Comb x (cexp2term y)) tm' cvs ===
                      FOLDL Comb tm tms ∧
          typeof (FOLDL Comb tm tms) = Cexp’
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
  \\ rename [‘mapOption I (MAP dest_cexp tms)’]
  \\ first_x_assum (qspec_then ‘tms’ assume_tac)
  \\ gs [SF SFY_ss] \\ first_x_assum irule \\ gs [SF DNF_ss]
  \\ conj_asm1_tac
  >- (
    qpat_x_assum ‘_ |- cexp2term _ === _’ assume_tac
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

Theorem cexp_value_closed:
  ∀v. cexp_value v ⇒ cexp_vars v = {}
Proof
  ho_match_mp_tac cexp_value_ind
  \\ rw [cexp_value_def, cexp_vars_def]
QED

Theorem closed_subst:
  ∀env v.
    EVERY cexp_value (MAP SND env) ⇒
      cexp_vars (subst env v) = cexp_vars v DIFF set (MAP FST env)
Proof
  ho_match_mp_tac subst_ind \\ simp []
  \\ rpt conj_tac \\ simp [subst_def, cexp_vars_def]
  >- (
    rw [] \\ CASE_TAC \\ gs [ALOOKUP_NONE, cexp_vars_def]
    \\ drule_then assume_tac ALOOKUP_MEM
    \\ gs [MEM_MAP, EXISTS_PROD, PULL_EXISTS, EVERY_MEM, SF SFY_ss]
    \\ irule cexp_value_closed \\ gs [SF SFY_ss])
  >- (
    gs [DIFF_DEF, UNION_DEF, EXTENSION]
    \\ rw [EQ_IMP_THM] \\ gs [])
  >~ [‘FILTER _ _’] >- (
    rw [] \\ gs [EVERY_MAP, EVERY_FILTER, LAMBDA_PROD]
    \\ qpat_x_assum ‘_ ⇒ _’ mp_tac
    \\ impl_tac >- gs [EVERY_MEM, FORALL_PROD, SF DNF_ss, SF SFY_ss]
    \\ rw []
    \\ gs [EXTENSION, MEM_MAP, EXISTS_PROD, FORALL_PROD, PULL_EXISTS,
           MEM_FILTER]
    \\ metis_tac [])
  \\ gs [BIGUNION, EXTENSION, PULL_EXISTS, SF ETA_ss, MEM_MAP, EXISTS_PROD,
         PULL_EXISTS, EVERY_MEM, FORALL_PROD]
  \\ rw [EQ_IMP_THM] \\ gs [] \\ metis_tac []
QED

Theorem closed_subst':
  EVERY cexp_value (MAP SND env) ∧
  cexp_vars v ⊆ set (MAP FST env) ⇒
    cexp_vars (subst env v) = {}
Proof
  rw []
  \\ drule_all_then (qspec_then ‘v’ SUBST1_TAC) closed_subst
  \\ gs [DIFF_DEF, SUBSET_DEF, EXTENSION, DISJ_EQ_IMP]
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

Theorem VSUBST_uop2term[simp]:
  VSUBST is (uop2term uop x) = uop2term uop (VSUBST is x)
Proof
  Cases_on ‘uop’ \\ gs [uop2term_def, VSUBST_thm]
QED


Theorem VFREE_IN_FOLDL:
  ∀ts v t.
    VFREE_IN v (FOLDL Comb t ts) ⇔ EXISTS (VFREE_IN v) ts ∨ VFREE_IN v t
Proof
  Induct \\ simp [] \\ rw []
  \\ eq_tac \\ rw [] \\ gs []
QED

Theorem VFREE_IN_cexp_vars:
  ∀v. cexp_vars v = {n | VFREE_IN (Var n Cexp) (cexp2term v) }
Proof
  ho_match_mp_tac cexp2term_ind
  \\ rw [cexp2term_def, cexp_vars_def]
  >- (
    rw [EXTENSION]
    \\ qid_spec_tac ‘n’
    \\ ho_match_mp_tac num2bit_ind \\ rw []
    \\ simp [Once num2bit_def] \\ rw [] \\ gs [])
  >- (
    gs [EXTENSION, PULL_EXISTS, EQ_IMP_THM, SF DNF_ss, SF SFY_ss])
  >- (
    Cases_on ‘uop’ \\ gs [uop2term_def])
  >- (
    Cases_on ‘bop’ \\ gs [bop2term_def]
    \\ gs [EXTENSION, PULL_EXISTS, EQ_IMP_THM, SF DNF_ss, SF SFY_ss])
  >- (
    gs [EXTENSION, PULL_EXISTS, EQ_IMP_THM, SF DNF_ss, SF SFY_ss])
  >- (
    gs [EXTENSION, DIFF_DEF, PULL_EXISTS, EQ_IMP_THM, SF DNF_ss, SF SFY_ss])
  >- (
    gs [VFREE_IN_FOLDL, EXISTS_MAP, BIGUNION, EXISTS_MEM, MEM_MAP,
          PULL_EXISTS, EXTENSION]
    \\ rw [EQ_IMP_THM] \\ gs [SF SFY_ss, SF DNF_ss]
    \\ first_assum (irule_at Any) \\ gs []
    \\ qexists_tac ‘cexp_vars a’ \\ gs [])
QED

Theorem subst_VSUBST:
  ∀env x.
    EVERY (λv. cexp_vars v = {}) (MAP SND env) ⇒
      cexp2term (subst env x) =
      VSUBST (MAP (λ(s,v). (cexp2term v, Var s Cexp)) env) (cexp2term x)
Proof
  ho_match_mp_tac subst_ind \\ rw []
  >~ [‘Var n’] >- (
    simp [subst_def, cexp2term_def, VSUBST_def, REV_ASSOCD_ALOOKUP,
          MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
    \\ gvs [EVERY_MEM, cexp_vars_def]
    \\ CASE_TAC \\ CASE_TAC
    \\ imp_res_tac ALOOKUP_MEM
    \\ gvs [ALOOKUP_NONE, cexp2term_def, MEM_MAP, EXISTS_PROD, PULL_EXISTS]
    \\ Q.ISPECL_THEN [‘cexp2term’, ‘λs. Var s Cexp’] assume_tac
                     (GEN_ALL ALOOKUP_MAP_3)
    \\ gs [ALOOKUP_MAP, SF SFY_ss])
  >~ [‘Let s x y’] >- (
    gs [cexp_vars_def, cexp2term_def, subst_def, VSUBST_thm]
    \\ IF_CASES_TAC \\ gs []
    >- (
      ‘F’ suffices_by rw []
      \\ pop_assum mp_tac
      \\ gs [o_DEF, LAMBDA_PROD, EVERY_FILTER, EVERY_MAP, EVERY_MEM,
             FORALL_PROD]
      \\ rw [] \\ first_x_assum (drule_then assume_tac)
      \\ gs [VFREE_IN_cexp_vars, EXTENSION])
    \\ gs [FILTER_MAP, combinTheory.o_DEF, LAMBDA_PROD, EVERY_MAP, EVERY_FILTER,
           EVERY_MEM, FORALL_PROD, SF SFY_ss])
  \\ gs [subst_def, cexp2term_def, VSUBST_def, cexp_vars_def, SF ETA_ss]
  \\ gs [BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS]
  \\ simp [GSYM VSUBST_FOLDL_Comb_push]
  \\ simp [VSUBST_thm]
  \\ AP_TERM_TAC
  \\ simp [MAP_MAP_o, o_DEF, LAMBDA_PROD, MAP_EQ_f]
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

(* TODO Move *)
Theorem SAFEDIV_0[simp]:
  0 SAFEDIV n = 0
Proof
  rw [SAFEDIV_def, ZERO_DIV]
QED

Theorem NUMERAL_ONE[local]:
  numeral_thy_ok thy ⇒
    (thy,[]) |- _NUMERAL (_SUC _0) === _SUC (_NUMERAL _0)
Proof
  rw []
  \\ irule trans_equation_simple \\ irule_at Any NUMERAL_eqn
  \\ irule_at Any MK_COMB_simple
  \\ gs [numeral_thy_ok_terms_ok, proves_REFL, NUMERAL_eqn, sym_equation]
QED

Theorem do_binop_thm:
  compute_thy_ok thy ⇒
    term_ok (sigof thy) (cexp2term p) ∧
    term_ok (sigof thy) (cexp2term q) ∧
    (thy,[]) |- cexp2term p === cexp2term x ∧ cexp_value x ∧
    (thy,[]) |- cexp2term q === cexp2term y ∧ cexp_value y ∧
    do_binop bop x y s = (res, s') ⇒
      s' = s ∧
      ∃cv. res = M_success cv ∧
           (thy,[]) |- bop2term bop (cexp2term p) (cexp2term q) === cexp2term cv
Proof
  ntac 2 strip_tac
  \\ Cases_on ‘bop’ \\ gs [bop2term_def, do_binop_def, do_reln_def]
  >~ [‘_CEXP_ADD _ _’] >- (
    Cases_on ‘∃m. x = Num m’ \\ fs []
    >- (
      Cases_on ‘∃n. y = Num n’ \\ fs []
      >- (
        gvs [do_arith_def, st_ex_return_def, cexp2term_def]
        \\ ‘(thy,[]) |- cexp2term p === _CEXP_NUM (num2bit m)’
          by (irule trans_equation_simple \\ first_x_assum (irule_at Any)
              \\ simp [MK_COMB_simple, proves_REFL, compute_thy_ok_terms_ok,
                       NUMERAL_eqn, num2bit_term_ok])
        \\ ‘(thy,[]) |- cexp2term q === _CEXP_NUM (num2bit n)’
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
        \\ rw [CEXP_ADD_eqn1, sym_equation, num2bit_term_ok])
      \\ ‘cexp_value y’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. y = Pair p1 q1’
        by (Cases_on ‘y’ \\ fs [])
      \\ gvs [cexp2term_def, do_arith_def, st_ex_return_def]
      \\ ‘term_ok (sigof thy) (cexp2term p1) ∧
          term_ok (sigof thy) (cexp2term q1)’
        by (drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ rw [CEXP_ADD_eqn2, num2bit_term_ok, compute_thy_ok_terms_ok])
    \\ Cases_on ‘∃n. y = Num n’ \\ gs []
    >- (
      gvs [cexp2term_def, do_arith_def, st_ex_return_def]
      \\ ‘cexp_value x’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. x = Pair p1 q1’
        by (Cases_on ‘x’ \\ fs [])
      \\ gvs [cexp2term_def, do_arith_def, st_ex_return_def]
      \\ ‘term_ok (sigof thy) (cexp2term p1) ∧
          term_ok (sigof thy) (cexp2term q1)’
        by (qpat_x_assum ‘_ |- _ === _CEXP_PAIR _ _’ assume_tac
            \\ drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ rw [CEXP_ADD_eqn3, num2bit_term_ok, compute_thy_ok_terms_ok])
    \\ gvs [cexp2term_def, do_arith_def, st_ex_return_def]
    \\ ‘cexp_value x’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p1 q1. x = Pair p1 q1’
      by (Cases_on ‘x’ \\ fs [])
    \\ ‘cexp_value y’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p2 q2. y = Pair p2 q2’
      by (Cases_on ‘y’ \\ fs [])
    \\ gvs [cexp2term_def, do_arith_def, st_ex_return_def]
    \\ simp [Once num2bit_def]
    \\ ‘EVERY (term_ok (sigof thy) o cexp2term) [p1;q1;p2;q2]’
      by (imp_res_tac proves_term_ok
          \\ gs [term_ok_def, equation_def])
    \\ resolve_then Any irule sym_equation replaceL2
    \\ first_x_assum (irule_at Any)
    \\ resolve_then Any irule sym_equation replaceL1
    \\ first_x_assum (irule_at Any)
    \\ fs [] \\ rw [CEXP_ADD_eqn4, compute_thy_ok_terms_ok])
  >~ [‘_CEXP_SUB _ _’] >- (
    Cases_on ‘∃m. x = Num m’ \\ fs []
    >- (
      Cases_on ‘∃n. y = Num n’ \\ fs []
      >- (
        gvs [do_arith_def, st_ex_return_def, cexp2term_def]
        \\ ‘(thy,[]) |- cexp2term p === _CEXP_NUM (num2bit m)’
          by (irule trans_equation_simple \\ first_x_assum (irule_at Any)
              \\ simp [MK_COMB_simple, proves_REFL, compute_thy_ok_terms_ok,
                       NUMERAL_eqn, num2bit_term_ok])
        \\ ‘(thy,[]) |- cexp2term q === _CEXP_NUM (num2bit n)’
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
        \\ rw [CEXP_SUB_eqn1, sym_equation, num2bit_term_ok])
      \\ ‘cexp_value y’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. y = Pair p1 q1’
        by (Cases_on ‘y’ \\ fs [])
      \\ gvs [cexp2term_def, do_arith_def, st_ex_return_def]
      \\ ‘term_ok (sigof thy) (cexp2term p1) ∧
          term_ok (sigof thy) (cexp2term q1)’
        by (drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ rw [CEXP_SUB_eqn2, num2bit_term_ok, compute_thy_ok_terms_ok])
    \\ Cases_on ‘∃n. y = Num n’ \\ gs []
    >- (
      gvs [cexp2term_def, do_arith_def, st_ex_return_def]
      \\ ‘cexp_value x’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. x = Pair p1 q1’
        by (Cases_on ‘x’ \\ fs [])
      \\ gvs [cexp2term_def, do_arith_def, st_ex_return_def]
      \\ simp [Once num2bit_def]
      \\ ‘(thy,[]) |- cexp2term q === _CEXP_NUM (num2bit n)’
        by (irule trans_equation_simple \\ first_x_assum (irule_at Any)
            \\ simp [MK_COMB_simple, proves_REFL, compute_thy_ok_terms_ok,
                     num2bit_term_ok, NUMERAL_eqn])
      \\ ‘term_ok (sigof thy) (cexp2term p1) ∧
          term_ok (sigof thy) (cexp2term q1)’
        by (qpat_x_assum ‘_ |- _ === _CEXP_PAIR _ _’ assume_tac
            \\ drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ rw [CEXP_SUB_eqn3, num2bit_term_ok, compute_thy_ok_terms_ok])
    \\ gvs [cexp2term_def, do_arith_def, st_ex_return_def]
    \\ ‘cexp_value x’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p1 q1. x = Pair p1 q1’
      by (Cases_on ‘x’ \\ fs [])
    \\ ‘cexp_value y’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p2 q2. y = Pair p2 q2’
      by (Cases_on ‘y’ \\ fs [])
    \\ gvs [cexp2term_def, do_arith_def, st_ex_return_def]
    \\ simp [Once num2bit_def]
    \\ ‘EVERY (term_ok (sigof thy) o cexp2term) [p1;q1;p2;q2]’
      by (imp_res_tac proves_term_ok
          \\ gs [term_ok_def, equation_def])
    \\ resolve_then Any irule sym_equation replaceL2
    \\ first_x_assum (irule_at Any)
    \\ resolve_then Any irule sym_equation replaceL1
    \\ first_x_assum (irule_at Any)
    \\ fs [] \\ rw [CEXP_SUB_eqn4, compute_thy_ok_terms_ok])
  >~ [‘_CEXP_MUL _ _’] >- (
    Cases_on ‘∃m. x = Num m’ \\ fs []
    >- (
      Cases_on ‘∃n. y = Num n’ \\ fs []
      >- (
        gvs [do_arith_def, st_ex_return_def, cexp2term_def]
        \\ ‘(thy,[]) |- cexp2term p === _CEXP_NUM (num2bit m)’
          by (irule trans_equation_simple \\ first_x_assum (irule_at Any)
              \\ simp [MK_COMB_simple, proves_REFL, compute_thy_ok_terms_ok,
                       NUMERAL_eqn, num2bit_term_ok])
        \\ ‘(thy,[]) |- cexp2term q === _CEXP_NUM (num2bit n)’
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
        \\ rw [CEXP_MUL_eqn1, sym_equation, num2bit_term_ok])
      \\ ‘cexp_value y’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. y = Pair p1 q1’
        by (Cases_on ‘y’ \\ fs [])
      \\ gvs [cexp2term_def, do_arith_def, st_ex_return_def]
      \\ ‘term_ok (sigof thy) (cexp2term p1) ∧
          term_ok (sigof thy) (cexp2term q1)’
        by (drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ ‘(thy,[]) |- cexp2term p === _CEXP_NUM (num2bit m)’
        by (irule trans_equation_simple \\ first_x_assum (irule_at Any)
            \\ simp [MK_COMB_simple, proves_REFL, compute_thy_ok_terms_ok,
                     NUMERAL_eqn, num2bit_term_ok])
      \\ simp [Once num2bit_def]
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ rw [CEXP_MUL_eqn2, num2bit_term_ok, compute_thy_ok_terms_ok])
    \\ Cases_on ‘∃n. y = Num n’ \\ gs []
    >- (
      gvs [cexp2term_def, do_arith_def, st_ex_return_def]
      \\ ‘cexp_value x’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. x = Pair p1 q1’
        by (Cases_on ‘x’ \\ fs [])
      \\ gvs [cexp2term_def, do_arith_def, st_ex_return_def]
      \\ ‘term_ok (sigof thy) (cexp2term p1) ∧
          term_ok (sigof thy) (cexp2term q1)’
        by (qpat_x_assum ‘_ |- _ === _CEXP_PAIR _ _’ assume_tac
            \\ drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ ‘(thy,[]) |- cexp2term q === _CEXP_NUM (num2bit n)’
        by (irule trans_equation_simple \\ first_x_assum (irule_at Any)
            \\ simp [MK_COMB_simple, proves_REFL, compute_thy_ok_terms_ok,
                     NUMERAL_eqn, num2bit_term_ok])
      \\ simp [Once num2bit_def]
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ rw [CEXP_MUL_eqn3, num2bit_term_ok, compute_thy_ok_terms_ok])
    \\ gvs [cexp2term_def, do_arith_def, st_ex_return_def]
    \\ ‘cexp_value x’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p1 q1. x = Pair p1 q1’
      by (Cases_on ‘x’ \\ fs [])
    \\ ‘cexp_value y’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p2 q2. y = Pair p2 q2’
      by (Cases_on ‘y’ \\ fs [])
    \\ gvs [cexp2term_def, do_arith_def, st_ex_return_def]
    \\ simp [Once num2bit_def]
    \\ ‘EVERY (term_ok (sigof thy) o cexp2term) [p1;q1;p2;q2]’
      by (imp_res_tac proves_term_ok
          \\ gs [term_ok_def, equation_def])
    \\ resolve_then Any irule sym_equation replaceL2
    \\ first_x_assum (irule_at Any)
    \\ resolve_then Any irule sym_equation replaceL1
    \\ first_x_assum (irule_at Any)
    \\ fs [] \\ rw [CEXP_MUL_eqn4, compute_thy_ok_terms_ok])
  >~ [‘_CEXP_DIV _ _’] >- (
    Cases_on ‘∃m. x = Num m’ \\ fs []
    >- (
      Cases_on ‘∃n. y = Num n’ \\ fs []
      >- (
        gvs [do_arith_def, st_ex_return_def, cexp2term_def]
        \\ ‘(thy,[]) |- cexp2term p === _CEXP_NUM (num2bit m)’
          by (irule trans_equation_simple \\ first_x_assum (irule_at Any)
              \\ simp [MK_COMB_simple, proves_REFL, compute_thy_ok_terms_ok,
                       NUMERAL_eqn, num2bit_term_ok])
        \\ ‘(thy,[]) |- cexp2term q === _CEXP_NUM (num2bit n)’
          by (irule trans_equation_simple \\ first_x_assum (irule_at Any)
              \\ simp [MK_COMB_simple, proves_REFL, compute_thy_ok_terms_ok,
                       NUMERAL_eqn, num2bit_term_ok])
        \\ resolve_then Any irule sym_equation replaceL2
        \\ first_x_assum (irule_at Any)
        \\ resolve_then Any irule sym_equation replaceL1
        \\ first_x_assum (irule_at Any)
        \\ resolve_then Any irule sym_equation replaceR2
        \\ irule_at Any NUMERAL_eqn \\ simp [num2bit_term_ok]
        \\ irule replaceL2 \\ irule_at Any DIV_num2bit
        \\ rw [CEXP_DIV_eqn1, sym_equation, num2bit_term_ok])
      \\ ‘cexp_value y’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. y = Pair p1 q1’
        by (Cases_on ‘y’ \\ fs [])
      \\ gvs [cexp2term_def, do_arith_def, st_ex_return_def]
      \\ ‘term_ok (sigof thy) (cexp2term p1) ∧
          term_ok (sigof thy) (cexp2term q1)’
        by (drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ ‘(thy,[]) |- cexp2term p === _CEXP_NUM (num2bit m)’
        by (irule trans_equation_simple \\ first_x_assum (irule_at Any)
            \\ simp [MK_COMB_simple, proves_REFL, compute_thy_ok_terms_ok,
                     NUMERAL_eqn, num2bit_term_ok])
      \\ simp [SAFEDIV_def, Once num2bit_def]
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ rw [CEXP_DIV_eqn2, num2bit_term_ok, compute_thy_ok_terms_ok])
    \\ Cases_on ‘∃n. y = Num n’ \\ gs []
    >- (
      gvs [cexp2term_def, do_arith_def, st_ex_return_def]
      \\ ‘cexp_value x’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. x = Pair p1 q1’
        by (Cases_on ‘x’ \\ fs [])
      \\ gvs [cexp2term_def, do_arith_def, st_ex_return_def]
      \\ ‘term_ok (sigof thy) (cexp2term p1) ∧
          term_ok (sigof thy) (cexp2term q1)’
        by (qpat_x_assum ‘_ |- _ === _CEXP_PAIR _ _’ assume_tac
            \\ drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ ‘(thy,[]) |- cexp2term q === _CEXP_NUM (num2bit n)’
        by (irule trans_equation_simple \\ first_x_assum (irule_at Any)
            \\ simp [MK_COMB_simple, proves_REFL, compute_thy_ok_terms_ok,
                     NUMERAL_eqn, num2bit_term_ok])
      \\ simp [Once num2bit_def]
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ rw [CEXP_DIV_eqn3, num2bit_term_ok, compute_thy_ok_terms_ok])
    \\ gvs [cexp2term_def, do_arith_def, st_ex_return_def]
    \\ ‘cexp_value x’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p1 q1. x = Pair p1 q1’
      by (Cases_on ‘x’ \\ fs [])
    \\ ‘cexp_value y’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p2 q2. y = Pair p2 q2’
      by (Cases_on ‘y’ \\ fs [])
    \\ gvs [cexp2term_def, do_arith_def, st_ex_return_def]
    \\ simp [Once num2bit_def]
    \\ ‘EVERY (term_ok (sigof thy) o cexp2term) [p1;q1;p2;q2]’
      by (imp_res_tac proves_term_ok
          \\ gs [term_ok_def, equation_def])
    \\ resolve_then Any irule sym_equation replaceL2
    \\ first_x_assum (irule_at Any)
    \\ resolve_then Any irule sym_equation replaceL1
    \\ first_x_assum (irule_at Any)
    \\ fs [] \\ rw [CEXP_DIV_eqn4, compute_thy_ok_terms_ok])
  >~ [‘_CEXP_MOD _ _’] >- (
    Cases_on ‘∃m. x = Num m’ \\ fs []
    >- (
      Cases_on ‘∃n. y = Num n’ \\ fs []
      >- (
        gvs [do_arith_def, st_ex_return_def, cexp2term_def]
        \\ ‘(thy,[]) |- cexp2term p === _CEXP_NUM (num2bit m)’
          by (irule trans_equation_simple \\ first_x_assum (irule_at Any)
              \\ simp [MK_COMB_simple, proves_REFL, compute_thy_ok_terms_ok,
                       NUMERAL_eqn, num2bit_term_ok])
        \\ ‘(thy,[]) |- cexp2term q === _CEXP_NUM (num2bit n)’
          by (irule trans_equation_simple \\ first_x_assum (irule_at Any)
              \\ simp [MK_COMB_simple, proves_REFL, compute_thy_ok_terms_ok,
                       NUMERAL_eqn, num2bit_term_ok])
        \\ resolve_then Any irule sym_equation replaceL2
        \\ first_x_assum (irule_at Any)
        \\ resolve_then Any irule sym_equation replaceL1
        \\ first_x_assum (irule_at Any)
        \\ resolve_then Any irule sym_equation replaceR2
        \\ irule_at Any NUMERAL_eqn \\ simp [num2bit_term_ok]
        \\ irule replaceL2 \\ irule_at Any MOD_num2bit
        \\ rw [CEXP_MOD_eqn1, sym_equation, num2bit_term_ok])
      \\ ‘cexp_value y’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. y = Pair p1 q1’
        by (Cases_on ‘y’ \\ fs [])
      \\ gvs [cexp2term_def, do_arith_def, st_ex_return_def]
      \\ ‘term_ok (sigof thy) (cexp2term p1) ∧
          term_ok (sigof thy) (cexp2term q1)’
        by (drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ simp [SAFEMOD_def]
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ rw [CEXP_MOD_eqn2, num2bit_term_ok, compute_thy_ok_terms_ok])
    \\ Cases_on ‘∃n. y = Num n’ \\ gs []
    >- (
      gvs [cexp2term_def, do_arith_def, st_ex_return_def]
      \\ ‘cexp_value x’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. x = Pair p1 q1’
        by (Cases_on ‘x’ \\ fs [])
      \\ gvs [cexp2term_def, do_arith_def, st_ex_return_def]
      \\ ‘term_ok (sigof thy) (cexp2term p1) ∧
          term_ok (sigof thy) (cexp2term q1)’
        by (qpat_x_assum ‘_ |- _ === _CEXP_PAIR _ _’ assume_tac
            \\ drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ simp [SAFEMOD_def, Once num2bit_def]
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ rw [CEXP_MOD_eqn3, num2bit_term_ok, compute_thy_ok_terms_ok])
    \\ gvs [cexp2term_def, do_arith_def, st_ex_return_def]
    \\ ‘cexp_value x’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p1 q1. x = Pair p1 q1’
      by (Cases_on ‘x’ \\ fs [])
    \\ ‘cexp_value y’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p2 q2. y = Pair p2 q2’
      by (Cases_on ‘y’ \\ fs [])
    \\ gvs [cexp2term_def, do_arith_def, st_ex_return_def]
    \\ simp [Once num2bit_def]
    \\ ‘EVERY (term_ok (sigof thy) o cexp2term) [p1;q1;p2;q2]’
      by (imp_res_tac proves_term_ok
          \\ gs [term_ok_def, equation_def])
    \\ resolve_then Any irule sym_equation replaceL2
    \\ first_x_assum (irule_at Any)
    \\ resolve_then Any irule sym_equation replaceL1
    \\ first_x_assum (irule_at Any)
    \\ fs [] \\ rw [CEXP_MOD_eqn4, compute_thy_ok_terms_ok])
  >~ [‘_CEXP_LESS _ _’] >- (
    Cases_on ‘∃m. x = Num m’ \\ fs []
    >- (
      Cases_on ‘∃n. y = Num n’ \\ fs []
      >- (
        gvs [do_reln_def, st_ex_return_def, cexp2term_def]
        \\ qmatch_asmsub_abbrev_tac ‘_ |- cexp2term p === A’
        \\ qmatch_asmsub_abbrev_tac ‘_ |- cexp2term q === B’
        \\ ‘(thy,[]) |- _CEXP_NUM (_NUMERAL (num2bit (if m < n then 1 else 0)))
                    === _CEXP_LESS A B’
          suffices_by (
            rw [Abbr ‘A’, Abbr ‘B’]
            \\ resolve_then Any irule sym_equation replaceL2
            \\ first_x_assum (irule_at Any)
            \\ resolve_then Any irule sym_equation replaceL1
            \\ first_x_assum (irule_at Any)
            \\ fs [cexp2term_def, sym_equation])
        \\ unabbrev_all_tac
        \\ irule replaceR2 \\ irule_at Any MK_COMB_simple
        \\ resolve_then Any (irule_at Any) NUMERAL_eqn sym_equation
        \\ irule_at Any proves_REFL
        \\ simp [compute_thy_ok_terms_ok, num2bit_term_ok]
        \\ irule replaceL1 \\ irule_at Any MK_COMB_simple
        \\ resolve_then Any (irule_at Any) NUMERAL_eqn sym_equation
        \\ irule_at Any proves_REFL
        \\ simp [compute_thy_ok_terms_ok, num2bit_term_ok]
        \\ irule trans_equation_simple \\ irule_at Any CEXP_LESS_eqn1
        \\ simp [num2bit_term_ok]
        \\ irule MK_COMB_simple \\ simp [proves_REFL, compute_thy_ok_terms_ok]
        \\ irule replaceL3 \\ irule_at Any bool2term_LESS_num2bit \\ simp []
        \\ irule replaceL1 \\ irule_at Any NUMERAL_ONE \\ gs []
        \\ resolve_then Any irule sym_equation replaceR2
        \\ irule_at Any num2bit_num2term \\ simp []
        \\ once_rewrite_tac [ONE]
        \\ IF_CASES_TAC \\ simp [bool2term_def, num2term_def]
        \\ gs [sym_equation, COND_eqn, compute_thy_ok_terms_ok])
      \\ ‘cexp_value y’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. y = Pair p1 q1’
        by (Cases_on ‘y’ \\ fs [])
      \\ gvs [cexp2term_def, do_reln_def, st_ex_return_def]
      \\ ‘term_ok (sigof thy) (cexp2term p1) ∧
          term_ok (sigof thy) (cexp2term q1)’
        by (drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ simp [Once num2bit_def, SimpR “(===)”]
      \\ rw [CEXP_LESS_eqn2, num2bit_term_ok])
    \\ Cases_on ‘∃n. y = Num n’ \\ gs []
    >- (
      gvs [cexp2term_def, st_ex_return_def]
      \\ ‘cexp_value x’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. x = Pair p1 q1’
        by (Cases_on ‘x’ \\ fs [])
      \\ gvs [cexp2term_def, do_reln_def, st_ex_return_def]
      \\ ‘term_ok (sigof thy) (cexp2term p1) ∧
          term_ok (sigof thy) (cexp2term q1)’
        by (qpat_x_assum ‘_ |- _ === _CEXP_PAIR _ _’ assume_tac
            \\ drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ simp [Once num2bit_def, SimpR “(===)”]
      \\ rw [CEXP_LESS_eqn3, num2bit_term_ok])
    \\ gvs [cexp2term_def, st_ex_return_def]
    \\ ‘cexp_value x’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p1 q1. x = Pair p1 q1’
      by (Cases_on ‘x’ \\ fs [])
    \\ ‘cexp_value y’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p2 q2. y = Pair p2 q2’
      by (Cases_on ‘y’ \\ fs [])
    \\ gvs [cexp2term_def, do_reln_def, st_ex_return_def]
    \\ simp [Once num2bit_def]
    \\ ‘EVERY (term_ok (sigof thy) o cexp2term) [p1;q1;p2;q2]’
      by (imp_res_tac proves_term_ok
          \\ gs [term_ok_def, equation_def])
    \\ resolve_then Any irule sym_equation replaceL2
    \\ first_x_assum (irule_at Any)
    \\ resolve_then Any irule sym_equation replaceL1
    \\ first_x_assum (irule_at Any)
    \\ gs [CEXP_LESS_eqn4])
  >~ [‘_CEXP_EQ _ _’] >- (
    Cases_on ‘∃m. x = Num m’ \\ fs []
    >- (
      Cases_on ‘∃n. y = Num n’ \\ fs []
      >- (
        gvs [do_eq_def, st_ex_return_def, cexp2term_def]
        \\ qmatch_asmsub_abbrev_tac ‘_ |- cexp2term p === A’
        \\ qmatch_asmsub_abbrev_tac ‘_ |- cexp2term q === B’
        \\ ‘(thy,[]) |- _CEXP_NUM (_NUMERAL (num2bit (if m = n then 1 else 0)))
                    === _CEXP_EQ A B’
          suffices_by (
            rw [Abbr ‘A’, Abbr ‘B’]
            \\ resolve_then Any irule sym_equation replaceL2
            \\ first_x_assum (irule_at Any)
            \\ resolve_then Any irule sym_equation replaceL1
            \\ first_x_assum (irule_at Any)
            \\ fs [cexp2term_def, sym_equation])
        \\ unabbrev_all_tac
        \\ irule replaceR2 \\ irule_at Any MK_COMB_simple
        \\ resolve_then Any (irule_at Any) NUMERAL_eqn sym_equation
        \\ irule_at Any proves_REFL
        \\ simp [compute_thy_ok_terms_ok, num2bit_term_ok]
        \\ irule replaceL1 \\ irule_at Any MK_COMB_simple
        \\ resolve_then Any (irule_at Any) NUMERAL_eqn sym_equation
        \\ irule_at Any proves_REFL
        \\ simp [compute_thy_ok_terms_ok, num2bit_term_ok]
        \\ irule trans_equation_simple \\ irule_at Any CEXP_EQ_eqn1
        \\ ‘theory_ok thy’ by fs []
        \\ ‘is_std_sig (sigof thy)’
          by gs [theory_ok_def]
        \\ simp [num2bit_term_ok, compute_thy_ok_terms_ok, term_ok_clauses]
        \\ simp [Ntimes has_type_cases 3]
        \\ simp [Ntimes has_type_cases 3]
        \\ irule MK_COMB_simple
        \\ gs [compute_thy_ok_terms_ok, proves_REFL, welltyped_equation,
               EQUATION_HAS_TYPE_BOOL, term_ok_welltyped, SF SFY_ss]
        \\ simp [Once equation_def]
        \\ resolve_then Any irule sym_equation replaceL3
        \\ irule_at Any CEXP_EQ_eqn3 \\ gs [num2bit_term_ok]
        \\ irule replaceL3
        \\ irule_at Any bool2term_EQ_num2bit \\ simp []
        \\ irule replaceL1 \\ irule_at Any NUMERAL_ONE \\ gs []
        \\ resolve_then Any irule sym_equation replaceR2
        \\ irule_at Any num2bit_num2term \\ simp []
        \\ once_rewrite_tac [ONE]
        \\ IF_CASES_TAC \\ simp [bool2term_def, num2term_def]
        \\ gs [sym_equation, COND_eqn, compute_thy_ok_terms_ok])
      \\ ‘cexp_value y’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. y = Pair p1 q1’
        by (Cases_on ‘y’ \\ fs [])
      \\ gvs [cexp2term_def, do_eq_def, st_ex_return_def]
      \\ ‘term_ok (sigof thy) (cexp2term p1) ∧
          term_ok (sigof thy) (cexp2term q1)’
        by (drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ simp [Once num2bit_def, SimpR “(===)”]
      \\ irule trans_equation_simple \\ irule_at Any CEXP_EQ_eqn1
      \\ ‘theory_ok thy’ by fs []
      \\ ‘is_std_sig (sigof thy)’
        by gs [theory_ok_def]
      \\ gs [num2bit_term_ok, compute_thy_ok_terms_ok, term_ok_clauses]
      \\ simp [Ntimes has_type_cases 3]
      \\ simp [Ntimes has_type_cases 3]
      \\ irule MK_COMB_simple
      \\ gs [compute_thy_ok_terms_ok, proves_REFL, welltyped_equation,
             EQUATION_HAS_TYPE_BOOL, term_ok_welltyped, SF SFY_ss]
      \\ simp [Once equation_def]
      \\ resolve_then Any irule sym_equation replaceL3
      \\ irule_at Any CEXP_EQ_eqn4 \\ gs [num2bit_term_ok]
      \\ irule (DISCH_ALL (CONJUNCT2 (UNDISCH_ALL COND_eqn)))
      \\ gs [numeral_thy_ok_terms_ok])
    \\ Cases_on ‘∃n. y = Num n’ \\ gs []
    >- (
      gvs [cexp2term_def, st_ex_return_def]
      \\ ‘cexp_value x’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. x = Pair p1 q1’
        by (Cases_on ‘x’ \\ fs [])
      \\ gvs [cexp2term_def, do_eq_def, st_ex_return_def]
      \\ ‘term_ok (sigof thy) (cexp2term p1) ∧
          term_ok (sigof thy) (cexp2term q1)’
        by (qpat_x_assum ‘_ |- _ === _CEXP_PAIR _ _’ assume_tac
            \\ drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ simp [Once num2bit_def, SimpR “(===)”]
      \\ irule trans_equation_simple \\ irule_at Any CEXP_EQ_eqn1
      \\ ‘theory_ok thy’ by fs []
      \\ ‘is_std_sig (sigof thy)’
        by gs [theory_ok_def]
      \\ gs [num2bit_term_ok, compute_thy_ok_terms_ok, term_ok_clauses]
      \\ simp [Ntimes has_type_cases 3]
      \\ simp [Ntimes has_type_cases 3]
      \\ irule MK_COMB_simple
      \\ gs [compute_thy_ok_terms_ok, proves_REFL, welltyped_equation,
             EQUATION_HAS_TYPE_BOOL, term_ok_welltyped, SF SFY_ss]
      \\ simp [Once equation_def]
      \\ resolve_then Any irule sym_equation replaceL3
      \\ irule_at Any CEXP_EQ_eqn5 \\ gs [num2bit_term_ok]
      \\ irule (DISCH_ALL (CONJUNCT2 (UNDISCH_ALL COND_eqn)))
      \\ gs [numeral_thy_ok_terms_ok])
    \\ gvs [cexp2term_def, st_ex_return_def]
    \\ ‘cexp_value x’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p1 q1. x = Pair p1 q1’
      by (Cases_on ‘x’ \\ fs [])
    \\ ‘cexp_value y’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p2 q2. y = Pair p2 q2’
      by (Cases_on ‘y’ \\ fs [])
    \\ gvs [cexp2term_def, do_eq_def, st_ex_return_def]
    \\ ‘EVERY (term_ok (sigof thy) o cexp2term) [p1;q1;p2;q2]’
      by (imp_res_tac proves_term_ok
          \\ gs [term_ok_def, equation_def])
    \\ resolve_then Any (irule_at Any) sym_equation replaceR2
    \\ irule_at Any MK_COMB_simple \\ irule_at Any num2bit_num2term
    \\ irule_at Any proves_REFL \\ gs [numeral_thy_ok_terms_ok]
    \\ irule sym_equation
    \\ resolve_then Any irule sym_equation replaceL2
    \\ first_x_assum (irule_at Any)
    \\ resolve_then Any irule sym_equation replaceL1
    \\ first_x_assum (irule_at Any)
    \\ irule trans_equation_simple \\ irule_at Any CEXP_EQ_eqn1
    \\ ‘theory_ok thy’ by fs []
    \\ ‘is_std_sig (sigof thy)’
      by gs [theory_ok_def]
    \\ gs [num2bit_term_ok, compute_thy_ok_terms_ok, term_ok_clauses]
    \\ simp [Ntimes has_type_cases 3]
    \\ simp [Ntimes has_type_cases 3]
    \\ irule MK_COMB_simple
    \\ gs [compute_thy_ok_terms_ok, proves_REFL, welltyped_equation,
           EQUATION_HAS_TYPE_BOOL, term_ok_welltyped, SF SFY_ss]
    \\ simp [Once equation_def]
    \\ resolve_then Any irule sym_equation replaceL3
    \\ irule_at Any CEXP_EQ_eqn2 \\ gs [num2bit_term_ok]
    \\ irule replaceL3
    \\ qexists_tac ‘_IF (bool2term (p1 = p2)) (bool2term (q1 = q2)) _FALSE’
    \\ irule_at Any MK_COMB_simple \\ gs []
    \\ irule_at Any MK_COMB_simple \\ gs []
    \\ irule_at Any MK_COMB_simple \\ gs []
    \\ simp [proves_REFL, bool_thy_ok_terms_ok, bool2term_EQ_cexpterm]
    \\ Cases_on ‘p1 = p2’ \\ Cases_on ‘q1 = q2’ \\ gs [bool2term_def]
    \\ once_rewrite_tac [ONE] \\ simp [num2term_def]
    \\ resolve_then Any irule sym_equation replaceL3
    \\ (irule_at Any (DISCH_ALL (CONJUNCT1 (UNDISCH_ALL IF_eqn))) ORELSE
        irule_at Any (DISCH_ALL (CONJUNCT2 (UNDISCH_ALL IF_eqn))))
    \\ gs [bool_thy_ok_terms_ok, term_ok_clauses, has_type_rules]
    \\ irule replaceL1 \\ irule_at Any NUMERAL_ONE \\ gs []
    \\ (irule_at Any (DISCH_ALL (CONJUNCT1 (UNDISCH_ALL COND_eqn))) ORELSE
        irule_at Any (DISCH_ALL (CONJUNCT2 (UNDISCH_ALL COND_eqn))))
    \\ gs [numeral_thy_ok_terms_ok])
QED

Theorem do_uop_thm:
  compute_thy_ok thy ⇒
    term_ok (sigof thy) (cexp2term p) ∧
    (thy,[]) |- cexp2term p === cexp2term x ∧ cexp_value x ∧
    do_uop uop x s = (res, s') ⇒
      s' = s ∧
      ∃cv. res = M_success cv ∧
           (thy,[]) |- uop2term uop (cexp2term p)=== cexp2term cv
Proof
  ntac 2 strip_tac
  \\ Cases_on ‘uop’ \\ gs [uop2term_def, do_uop_def]
  >~ [‘_CEXP_FST p’] >- (
    drule_then strip_assume_tac do_fst_thm \\ gvs []
    \\ rename [‘do_fst p r = (M_success cv,_)’]
    \\ drule_then assume_tac cexp_value_no_consts
    \\ Cases_on ‘∃p1 q1. p = Pair p1 q1’ \\ gvs []
    >- (
      gvs [do_fst_def, st_ex_return_def, cexp2term_def]
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ gs [CEXP_FST_eqn1, cexp2term_term_ok, cexp_consts_def])
    \\ ‘cv = Num 0’
      by (Cases_on ‘p’ \\ gs [do_fst_def, st_ex_return_def])
    \\ ‘∃m. p = Num m’
      by (Cases_on ‘p’ \\ gs [])
    \\ gvs [cexp2term_def]
    \\ resolve_then Any irule sym_equation replaceL2
    \\ first_x_assum (irule_at Any)
    \\ simp [Once num2bit_def, SimpR “(===)”]
    \\ irule CEXP_FST_eqn2
    \\ simp [Ntimes has_type_cases 3]
    \\ gs [term_ok_def, compute_thy_ok_terms_ok, num2bit_term_ok])
  >~ [‘_CEXP_SND p’] >- (
    drule_then strip_assume_tac do_snd_thm \\ gvs []
    \\ rename [‘do_snd p r = (M_success cv,_)’]
    \\ drule_then assume_tac cexp_value_no_consts
    \\ Cases_on ‘∃p1 q1. p = Pair p1 q1’ \\ gvs []
    >- (
      gvs [do_snd_def, st_ex_return_def, cexp2term_def]
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ gs [CEXP_SND_eqn1, cexp2term_term_ok, cexp_consts_def])
    \\ ‘cv = Num 0’
      by (Cases_on ‘p’ \\ gs [do_snd_def, st_ex_return_def])
    \\ ‘∃m. p = Num m’
      by (Cases_on ‘p’ \\ gs [])
    \\ gvs [cexp2term_def]
    \\ resolve_then Any irule sym_equation replaceL2
    \\ first_x_assum (irule_at Any)
    \\ simp [Once num2bit_def, SimpR “(===)”]
    \\ irule CEXP_SND_eqn2
    \\ simp [Ntimes has_type_cases 3]
    \\ gs [term_ok_def, compute_thy_ok_terms_ok, num2bit_term_ok])
  >~ [‘_CEXP_ISPAIR p’] >- (
    drule_then strip_assume_tac do_ispair_thm \\ gvs []
    \\ rename [‘do_ispair p r = (M_success cv,_)’]
    \\ drule_then assume_tac cexp_value_no_consts
    \\ Cases_on ‘∃p1 q1. p = Pair p1 q1’ \\ gvs []
    >- (
      gvs [do_ispair_def, st_ex_return_def, cexp2term_def]
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ irule replaceR2 \\ qexists_tac ‘_NUMERAL (num2term 1)’
      \\ simp [MK_COMB_simple, proves_REFL, numeral_thy_ok_terms_ok,
               num2bit_num2term, Once sym_equation]
      \\ once_rewrite_tac [ONE] \\ simp [num2term_def]
      \\ irule replaceL2 \\ qexists_tac ‘_SUC (_NUMERAL _0)’
      \\ resolve_then Any (irule_at Any) sym_equation replaceL2
      \\ irule_at Any NUMERAL_eqn \\ gs [numeral_thy_ok_terms_ok]
      \\ irule_at Any sym_equation \\ irule_at Any NUMERAL_eqn
      \\ gs [numeral_thy_ok_terms_ok, Once sym_equation, CEXP_ISPAIR_eqn1,
             cexp2term_term_ok, cexp_consts_def])
    \\ ‘cv = Num 0’
      by (Cases_on ‘p’ \\ gs [do_ispair_def, st_ex_return_def])
    \\ ‘∃m. p = Num m’
      by (Cases_on ‘p’ \\ gs [])
    \\ gvs [cexp2term_def]
    \\ resolve_then Any irule sym_equation replaceL2
    \\ first_x_assum (irule_at Any)
    \\ simp [Once num2bit_def, SimpR “(===)”]
    \\ irule CEXP_ISPAIR_eqn2 \\ gs []
    \\ gs [term_ok_def, compute_thy_ok_terms_ok, num2bit_term_ok])
QED

Theorem term_ok_bop2term:
  term_ok sig (bop2term bop tm1 tm2) ⇒
    term_ok sig tm1 ∧ term_ok sig tm2
Proof
  Cases_on ‘bop’ \\ rw [term_ok_def, bop2term_def]
QED

Theorem term_ok_uop2term:
  term_ok sig (uop2term uop tm) ⇒
    term_ok sig tm
Proof
  Cases_on ‘uop’ \\ rw [term_ok_def, uop2term_def]
QED

Theorem compute_eval_list_map:
  ∀cvs s. compute_eval_list ck eqs cvs s = map (compute_eval ck eqs) cvs s
Proof
  Induct \\ rw [map_def, compute_eval_def, st_ex_return_def, st_ex_bind_def]
QED

Theorem compute_thy_ok_is_std_sig:
  compute_thy_ok thy ⇒ is_std_sig (sigof thy)
Proof
  rw []
  \\ ‘theory_ok thy’ by gs []
  \\ gs [theory_ok_def]
QED

Definition cexp_consts_ok_def:
  cexp_consts_ok eqs (Var s) = T ∧
  cexp_consts_ok eqs (Num n) = T ∧
  cexp_consts_ok eqs (Pair p q) =
    (cexp_consts_ok eqs p ∧ cexp_consts_ok eqs q) ∧
  cexp_consts_ok eqs (If p q r) =
    (cexp_consts_ok eqs p ∧ cexp_consts_ok eqs q ∧ cexp_consts_ok eqs r) ∧
  cexp_consts_ok eqs (Uop uop p) = cexp_consts_ok eqs p ∧
  cexp_consts_ok eqs (Binop bop p q) =
    (cexp_consts_ok eqs p ∧ cexp_consts_ok eqs q) ∧
  cexp_consts_ok eqs (Let s p q) =
    (cexp_consts_ok eqs p ∧ cexp_consts_ok eqs q) ∧
  cexp_consts_ok eqs (App f cs) =
    (MEM (f,LENGTH cs) (MAP (λ(f,n,x). (f,LENGTH n)) eqs) ∧
     EVERY (cexp_consts_ok eqs) cs)
Termination
  wf_rel_tac ‘measure (compute_exp_size o SND)’
End

Theorem cexp_consts_ok_value:
  ∀eqs cv.
    cexp_value cv ⇒
    cexp_consts_ok eqs cv
Proof
  ho_match_mp_tac cexp_consts_ok_ind \\ rw []
  \\ gs [cexp_consts_ok_def, cexp_consts_def]
QED

Theorem cexp_consts_ok_subst:
  ∀xs x.
    cexp_consts_ok eqs x ∧
    EVERY (cexp_consts_ok eqs) (MAP SND xs) ⇒
      cexp_consts_ok eqs (subst xs x)
Proof
  ho_match_mp_tac subst_ind \\ rw [] \\ gs [cexp_consts_ok_def, subst_def]
  >- (
    gs [EVERY_MEM, MEM_MAP, EXISTS_PROD, PULL_EXISTS]
    \\ CASE_TAC \\ gs [cexp_consts_ok_def]
    \\ drule_then assume_tac ALOOKUP_MEM \\ gs [SF SFY_ss])
  \\ gs [EVERY_MAP, EVERY_MEM, EXISTS_PROD, PULL_EXISTS, MEM_FILTER]
QED

(* N.B. This can be cleaned up a bit. There's a derivation of general beta
 *      conversion hidden in here that could be pulled out into a lemma if its
 *      ever needed.
 *)

Theorem LET_VSUBST:
  compute_thy_ok thy ∧
  term_ok (sigof thy) q ∧ term_ok (sigof thy) p ∧ term_ok (sigof thy) r ∧
  (thy,[]) |- p === r ∧ p has_type Cexp ∧ q has_type Cexp ⇒
    (thy,[]) |- _LET (Abs (Var s Cexp) q) p === VSUBST [(r,Var s Cexp)] q
Proof
  strip_tac
  \\ irule trans_equation_simple
  \\ irule_at Any LET_eqn \\ gs []
  \\ ‘is_std_sig (sigof thy)’
    by (irule theory_ok_sig \\ gs [])
  \\ gs [term_ok_clauses]
  \\ simp [Ntimes has_type_cases 3]
  \\ ‘r has_type Cexp ∧ welltyped q ∧ welltyped r ∧ welltyped p’
    by (drule_then strip_assume_tac proves_term_ok
        \\ gs [term_ok_clauses, EQUATION_HAS_TYPE_BOOL] \\ rgs [WELLTYPED]
        \\ imp_res_tac WELLTYPED_LEMMA \\ gs [])
  \\ conj_asm1_tac
  >- (
    drule_then strip_assume_tac compute_thy_ok_terms_ok
    \\ rfs [])
  \\ resolve_then Any irule sym_equation replaceL2
  \\ first_x_assum (irule_at Any)
  \\ qabbrev_tac ‘_S = Var s Cexp’
  \\ irule trans_equation_simple
  \\ qexists_tac ‘VSUBST [r,_S] (Comb (Abs _S q) _S)’
  \\ conj_tac
  >- (
    simp [VSUBST_thm, Abbr ‘_S’, REV_ASSOCD_def]
    \\ irule proves_REFL
    \\ fs [term_ok_clauses]
    \\ irule WELLTYPED_LEMMA \\ fs [])
  \\ qspecl_then [‘(Comb (Abs _S q) _S) === q’,‘[]’,‘[r,_S]’,‘thy’]
                 mp_tac proves_INST
  \\ simp []
  \\ impl_tac
  >- (
    simp [Abbr ‘_S’, proves_BETA])
  \\ simp [equation_def, VSUBST_thm]
QED

Theorem compute_eval_thm:
  compute_thy_ok thy ⇒
    ((∀ck eqs cv s res s' tm.
      compute_eval ck eqs cv s = (res, s') ∧
      term_ok (sigof thy) (cexp2term cv) ∧
      cexp_vars cv = {} ∧
      cexp_consts_ok eqs cv ∧
      ALL_DISTINCT (MAP FST eqs) ∧
      EVERY (λ(f,vs,cv).
        ALL_DISTINCT vs ∧
        cexp_consts_ok eqs cv ∧
        ∃r. (thy,[]) |- cexp2term (App f (MAP Var vs)) === r ∧
            dest_cexp r = SOME cv ∧
            cexp_vars cv ⊆ set vs) eqs ⇒
        s' = s ∧
        (∀err. res = M_failure err ⇒ err = Failure «timeout») ∧
        ∀cv'. res = M_success cv' ⇒
          (thy,[]) |- cexp2term cv === cexp2term cv') ∧
    (∀ck eqs cvs s res s' tm.
      compute_eval_list ck eqs cvs s = (res, s') ∧
      EVERY (term_ok (sigof thy)) (MAP cexp2term cvs) ∧
      EVERY (λcv. cexp_vars cv = {}) cvs ∧
      EVERY (cexp_consts_ok eqs) cvs ∧
      ALL_DISTINCT (MAP FST eqs) ∧
      EVERY (λ(f,vs,cv).
        ALL_DISTINCT vs ∧
        cexp_consts_ok eqs cv ∧
        ∃r. (thy,[]) |- cexp2term (App f (MAP Var vs)) === r ∧
            dest_cexp r = SOME cv ∧
            cexp_vars cv ⊆ set vs) eqs ⇒
        s' = s ∧
        (∀err. res = M_failure err ⇒ err = Failure «timeout») ∧
        ∀cvs'. res = M_success cvs' ⇒
          LIST_REL (λcv cv'. (thy,[]) |- cexp2term cv === cexp2term cv')
                    cvs cvs'))
Proof
  strip_tac \\ fs []
  \\ drule_then assume_tac compute_thy_ok_is_std_sig
  \\ ho_match_mp_tac compute_eval_ind \\ rpt conj_tac
  \\ rpt (gen_tac ORELSE disch_then strip_assume_tac)
  \\ qpat_x_assum ‘_ = (res, _)’ mp_tac
  \\ simp [compute_eval_def, st_ex_return_def, raise_Failure_def]
  >~ [‘Var s’] >- (
    gs [cexp_vars_def])
  >~ [‘Num n’] >- (
    strip_tac
    \\ gvs [cexp2term_term_ok, proves_REFL])
  >~ [‘Pair p q’] >- (
    simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
    \\ gs [cexp2term_def, term_ok_clauses, cexp_vars_def, cexp_consts_ok_def]
    \\ first_x_assum (drule_then strip_assume_tac) \\ gvs []
    \\ CASE_TAC \\ gs []
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
    \\ first_x_assum (drule_then strip_assume_tac) \\ gvs []
    \\ reverse CASE_TAC \\ gs []
    \\ strip_tac \\ gvs []
    \\ fs [cexp2term_def, term_ok_def, MK_COMB_simple, proves_REFL, SF SFY_ss])
  >~ [‘Uop uop p’] >- (
    gvs [cexp2term_def, cexp_vars_def, cexp_consts_ok_def]
    \\ drule_then strip_assume_tac term_ok_uop2term
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
    \\ first_x_assum (drule_then strip_assume_tac) \\ gvs []
    \\ CASE_TAC \\ gs []
    \\ rename [‘do_uop uop x s’] \\ strip_tac
    \\ imp_res_tac (CONJUNCT1 compute_eval_value)
    \\ drule_all_then strip_assume_tac do_uop_thm \\ gs [])
  >~ [‘If p q r’] >- (
    gvs [cexp2term_def, term_ok_clauses, cexp_vars_def, cexp_consts_ok_def]
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
    \\ first_x_assum (drule_then strip_assume_tac) \\ gvs []
    \\ CASE_TAC \\ gs []
    \\ rename [‘compute_eval _ _ _ _ = (M_success cv', _)’]
    \\ Cases_on ‘cv' = Num 0’
    >- (
      gvs [] \\ rw []
      \\ first_x_assum (drule_then strip_assume_tac) \\ gvs []
      \\ resolve_then Any irule sym_equation replaceL3
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_assum (irule_at Any)
      \\ simp [cexp2term_def, Once num2bit_def]
      \\ irule_at Any CEXP_IF_eqn3 \\ gs []
      \\ drule_then assume_tac proves_term_ok
      \\ fs [equation_def, term_ok_def])
    \\ Cases_on ‘∃x y. cv' = Pair x y’
    >- (
      gvs [] \\ rw []
      \\ first_x_assum (drule_then strip_assume_tac) \\ gvs []
      \\ resolve_then Any irule sym_equation replaceL3
      \\ first_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_assum (irule_at Any)
      \\ fs [cexp2term_def, cexp_vars_def]
      \\ irule_at Any CEXP_IF_eqn2 \\ gs []
      \\ imp_res_tac proves_term_ok
      \\ fs [equation_def, term_ok_def])
    \\ Cases_on ‘∃n. cv' = Num (SUC n)’
    >- (
      gvs [] \\ rw []
      \\ first_x_assum (drule_then strip_assume_tac) \\ gvs []
      \\ resolve_then Any irule sym_equation replaceL3
      \\ first_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_assum (irule_at Any)
      \\ fs [cexp2term_def]
      \\ irule replaceL3 \\ Q.REFINE_EXISTS_TAC ‘_CEXP_NUM x’
      \\ irule_at Any MK_COMB_simple
      \\ simp [proves_REFL, compute_thy_ok_terms_ok]
      \\ resolve_then Any (irule_at Any) NUMERAL_eqn sym_equation
      \\ simp [num2bit_term_ok, compute_thy_ok_def, compute_thy_ok_terms_ok,
               proves_REFL]
      \\ irule replaceL3 \\ Q.REFINE_EXISTS_TAC ‘_CEXP_NUM x’
      \\ irule_at Any MK_COMB_simple
      \\ resolve_then Any (irule_at Any) num2bit_num2term sym_equation
      \\ simp [num2bit_term_ok, compute_thy_ok_def, compute_thy_ok_terms_ok,
               proves_REFL]
      \\ simp [num2term_def]
      \\ irule CEXP_IF_eqn1 \\ fs [num2term_term_ok]
      \\ imp_res_tac proves_term_ok
      \\ fs [equation_def, term_ok_def])
    \\ ‘cexp_value cv'’
      by (irule (CONJUNCT1 compute_eval_value)
          \\ first_x_assum (irule_at Any))
    \\ CASE_TAC \\ gs []
    \\ CASE_TAC \\ gs [])
  >~ [‘Binop bop p q’] >- (
    gvs [cexp2term_def, cexp_vars_def, cexp_consts_ok_def]
    \\ drule_then strip_assume_tac term_ok_bop2term
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
    \\ first_x_assum (drule_then strip_assume_tac) \\ gvs []
    \\ CASE_TAC \\ gs []
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
    \\ first_x_assum (drule_then strip_assume_tac) \\ gvs []
    \\ CASE_TAC \\ gs []
    \\ rename [‘do_binop bop x y s’] \\ strip_tac
    \\ drule_then strip_assume_tac term_ok_bop2term \\ gvs []
    \\ imp_res_tac (CONJUNCT1 compute_eval_value)
    \\ drule_all_then strip_assume_tac do_binop_thm \\ gs [])
  >~ [‘Let s p q’] >- (
    IF_CASES_TAC \\ gs []
    \\ simp [Once st_ex_bind_def]
    \\ gs [cexp_consts_ok_def, cexp_vars_def, cexp2term_def]
    \\ ‘is_std_sig (sigof thy)’
      by (irule theory_ok_sig \\ gs [])
    \\ gs [term_ok_clauses]
    \\ CASE_TAC
    \\ first_x_assum (drule_then strip_assume_tac) \\ gvs []
    \\ CASE_TAC \\ gs []
    \\ strip_tac
    \\ first_x_assum drule
    \\ ‘term_ok (sigof thy) (cexp2term a)’
      by (drule proves_term_ok \\ gs [term_ok_clauses])
    \\ ‘cexp_value a’
      by (irule_at Any (CONJUNCT1 compute_eval_value)
          \\ first_assum (irule_at Any))
    \\ impl_keep_tac
    >- (
      irule_at Any closed_subst' \\ gs [SUBSET_DIFF_EMPTY]
      \\ irule_at Any cexp_consts_ok_subst \\ gs []
      \\ irule_at Any cexp_consts_ok_value
      \\ irule_at Any subst_term_ok \\ gs [])
    \\ rw [] \\ gs []
    \\ irule trans_equation_simple
    \\ first_x_assum (irule_at Any) \\ gvs [SF ETA_ss]
    \\ DEP_REWRITE_TAC [subst_VSUBST] \\ simp []
    \\ gs [SUBSET_DIFF_EMPTY]
    \\ irule_at Any cexp_value_closed \\ gs []
    \\ irule LET_VSUBST \\ fs [])
  >~ [‘App f cs’] >- (
    IF_CASES_TAC \\ gs []
    \\ simp [option_def, Once st_ex_bind_def, st_ex_return_def,
             raise_Failure_def]
    \\ gs [cexp_consts_ok_def]
    \\ CASE_TAC
    >- (
      strip_tac \\ gvs []
      \\ gs [ALOOKUP_NONE, MEM_MAP, EXISTS_PROD])
    \\ pairarg_tac \\ gvs []
    \\ simp [check_def, st_ex_return_def, Once st_ex_ignore_bind_def,
             raise_Failure_def]
    \\ reverse IF_CASES_TAC \\ simp [] \\ simp [Once st_ex_bind_def]
    >- (
      strip_tac
      \\ gs [MEM_ALOOKUP, MEM_MAP, EXISTS_PROD])
    \\ CASE_TAC
    \\ first_x_assum drule
    \\ impl_keep_tac
    >- (
      gs [term_ok_def, cexp_vars_def, cexp2term_def]
      \\ drule_then strip_assume_tac term_ok_FOLDL_Comb \\ gs [SF ETA_ss]
      \\ qpat_x_assum ‘_ = {{}}’ mp_tac
      \\ rw [Once EXTENSION]
      \\ gs [EVERY_MEM, MEM_MAP, PULL_EXISTS, EQ_IMP_THM])
    \\ strip_tac \\ gvs []
    \\ qpat_x_assum ‘term_ok _ (cexp2term _)’
                    (strip_assume_tac o SIMPR [cexp2term_def])
    \\ drule_then strip_assume_tac term_ok_FOLDL_Comb \\ gvs [EVERY_MAP]
    \\ drule_then ASSUME_TAC ALOOKUP_MEM
    \\ reverse CASE_TAC >- (strip_tac \\ gvs [])
    \\ strip_tac
    \\ rename [‘ZIP(as,bs)’]
    \\ gvs [EVERY_MEM, FORALL_PROD]
    \\ first_x_assum (drule_then strip_assume_tac)
    \\ rename [‘dest_cexp rhs = SOME exp’]
    \\ qmatch_asmsub_abbrev_tac ‘_ |- lhs === rhs’
    \\ ‘term_ok (sigof thy) lhs ∧ term_ok (sigof thy) rhs’
      by (imp_res_tac proves_term_ok
          \\ gs [term_ok_def, equation_def])
    \\ unabbrev_all_tac
    \\ drule_then drule dest_cexp_thm \\ gs [] \\ strip_tac
    \\ ‘∀n. n < LENGTH bs ⇒
              cexp_value (EL n bs) ∧ term_ok (sigof thy) (cexp2term (EL n bs))’
      by (gen_tac
          \\ strip_tac
          \\ drule (CONJUNCT2 compute_eval_value) \\ rw [EVERY_EL]
          \\ gvs [LIST_REL_EL_EQN]
          \\ first_x_assum (drule_then strip_assume_tac)
          \\ first_x_assum (drule_then strip_assume_tac)
          \\ drule_then assume_tac proves_term_ok
          \\ gvs [equation_def, term_ok_def])
    \\ first_x_assum drule
    \\ gs [compute_eval_list_map]
    \\ drule_then strip_assume_tac map_thm
    \\ impl_keep_tac
    >- (
      irule_at Any closed_subst'
      \\ irule_at Any subst_term_ok
      \\ irule_at Any cexp_consts_ok_subst
      \\ gvs [GSYM MEM_ALOOKUP]
      \\ gvs [MAP_ZIP, EVERY_EL, PULL_EXISTS, MEM_MAP, EXISTS_PROD, MEM_EL,
              PULL_EXISTS, SF SFY_ss]
      \\ drule proves_term_ok \\ simp [term_ok_clauses] \\ rw []
      \\ irule cexp_consts_ok_value
      \\ irule (CONJUNCT1 compute_eval_value)
      \\ first_x_assum (drule_then strip_assume_tac)
      \\ first_x_assum (irule_at Any))
    \\ rw []
    \\ irule trans_equation_simple
    \\ first_x_assum (irule_at Any) \\ gvs [SF ETA_ss]
    \\ ‘(thy,[]) |- VSUBST (MAP (λ(s,v). (cexp2term v, Var s Cexp))
                                (ZIP (as,bs)))
                           (cexp2term exp === cexp2term (App f (MAP Var as)))’
      by (qspecl_then [‘c’,‘[]’] (irule o SIMPR []) proves_INST
          \\ simp [MEM_MAP, EXISTS_PROD, PULL_EXISTS]
          \\ rw [MEM_ZIP] \\ gs [SF SFY_ss]
          \\ irule trans_equation_simple
          \\ first_x_assum (irule_at Any)
          \\ rw [sym_equation])
    \\ ‘(thy,[]) |- VSUBST (MAP (λ(s,v). (cexp2term v, Var s Cexp))
                                (ZIP (as,bs))) (cexp2term exp) ===
                    VSUBST (MAP (λ(s,v). (cexp2term v, Var s Cexp))
                                (ZIP (as,bs))) (cexp2term (App f (MAP Var as)))’
      by (qmatch_goalsub_abbrev_tac ‘VSUBST env’
          \\ qpat_x_assum ‘_ |- VSUBST _ _’ mp_tac
          \\ simp [Once equation_def]
          \\ simp [VSUBST_thm]
          \\ ‘typeof (VSUBST env (cexp2term exp)) = Cexp’
            by (irule WELLTYPED_LEMMA
                \\ irule VSUBST_HAS_TYPE
                \\ gs [Abbr ‘env’, MEM_MAP, EXISTS_PROD, PULL_EXISTS])
          \\ pop_assum (SUBST1_TAC o SYM)
          \\ simp [GSYM equation_def])
    \\ ‘(thy,[]) |- cexp2term (subst (ZIP(as,bs)) exp) ===
                    cexp2term (subst (ZIP(as,bs)) (App f (MAP Var as)))’
      by (DEP_REWRITE_TAC [subst_VSUBST]
          \\ simp [MAP_ZIP, cexp_vars_def, MAP_MAP_o, combinTheory.o_DEF,
                   BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS]
          \\ rw [EVERY_EL]
          \\ first_x_assum (drule_then strip_assume_tac)
          \\ first_x_assum (drule_then strip_assume_tac)
          \\ drule_then assume_tac cexp_value_closed \\ gs [])
    \\ resolve_then Any irule trans_equation_simple sym_equation
    \\ first_x_assum (irule_at Any)
    \\ simp [subst_def, SF ETA_ss]
    \\ simp [MAP_subst_MAP_Var, cexp2term_def]
    \\ ‘∀xs ys tm tm1.
          LENGTH xs = LENGTH ys ∧
          tm has_type app_type (LENGTH xs) ∧
          (thy,[]) |- tm === tm1 ∧
          (∀n.
             n < LENGTH xs ⇒
               (thy,[]) |- cexp2term (EL n xs) ===  cexp2term (EL n ys)) ⇒
            (thy,[]) |- FOLDL Comb tm (MAP cexp2term xs) ===
                        FOLDL Comb tm1 (MAP cexp2term ys)’
      suffices_by (
        simp [SF ETA_ss]
        \\ disch_then irule
        \\ simp [proves_REFL]
        \\ gs [has_type_rules] \\ rw []
        \\ first_x_assum (drule_then strip_assume_tac)
        \\ first_x_assum (drule_then strip_assume_tac)
        \\ gs [MEM_EL, PULL_EXISTS]
        \\ gvs [LIST_REL_EL_EQN]
        \\ irule sym_equation
        \\ first_x_assum irule \\ gs [])
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
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC
  \\ first_x_assum drule \\ gs [] \\ strip_tac \\ gvs []
  \\ reverse CASE_TAC >- (strip_tac \\ gvs [])
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC
  \\ first_x_assum drule \\ gs [] \\ strip_tac \\ gvs []
  \\ reverse CASE_TAC >- (strip_tac \\ gvs [])
  \\ rw [] \\ gs [SF SFY_ss]
QED

val _ = export_theory ();

