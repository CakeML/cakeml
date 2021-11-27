(*
  semantics for timeLang
*)

open preamble
     timeLangTheory timeSemTheory
     pan_commonPropsTheory

val _ = new_theory "timeProps";

val _ = set_grammar_ancestry
        ["timeLang","timeSem",
         "pan_commonProps"];



Definition good_dimindex_def:
  good_dimindex (:'a) ⇔
    dimindex (:'a) = 32 ∨ dimindex (:'a) = 64
End

Theorem eval_term_inpput_ios_same:
  ∀s m n cnds tclks dest wt s'.
    evalTerm s (SOME m) (Tm (Input n) cnds tclks dest wt) s' ⇒
    m = n
Proof
  rw [] >>
  fs [evalTerm_cases]
QED


Theorem eval_term_clocks_reset:
  ∀s io n cnds tclks dest wt s' ck t.
    FLOOKUP s.clocks ck = SOME t ∧
    evalTerm s io (Tm n cnds tclks dest wt) s' ⇒
    (FLOOKUP s'.clocks ck = SOME t ∨ FLOOKUP s'.clocks ck = SOME 0)
Proof
  rw [] >>
  fs [evalTerm_cases, resetClocks_def] >>
  rveq >> gs [] >>(
  cases_on ‘MEM ck tclks’
  >- (
    gs [MEM_EL] >>
    metis_tac [update_eq_zip_map_flookup]) >>
  last_x_assum (assume_tac o GSYM) >>
  gs [] >>
  disj1_tac >>
  match_mp_tac flookup_fupdate_zip_not_mem >>
  gs [])
QED


Theorem list_min_option_some_mem:
  ∀xs x.
    list_min_option xs = SOME x ⇒
    MEM x xs
Proof
  Induct >> rw [] >>
  fs [list_min_option_def] >>
  every_case_tac >> fs [] >> rveq >> rfs []
QED


Theorem fdom_reset_clks_eq_clks:
  ∀fm clks.
    EVERY (λck. ck IN FDOM fm) clks ⇒
    FDOM (resetClocks fm clks) = FDOM fm
Proof
  rw [] >>
  fs [resetClocks_def] >>
  fs [FDOM_FUPDATE_LIST] >>
  ‘LENGTH clks = LENGTH (MAP (λx. 0:num) clks)’ by fs [] >>
  drule MAP_ZIP >>
  fs [] >>
  strip_tac >> pop_assum kall_tac >>
  ‘set clks ⊆ FDOM fm’ by (
    fs [SUBSET_DEF] >>
    rw [] >>
    fs [EVERY_MEM]) >>
  fs [SUBSET_UNION_ABSORPTION] >>
  fs [UNION_COMM]
QED


Theorem reset_clks_mem_flookup_zero:
  ∀clks ck fm.
    MEM ck clks ⇒
    FLOOKUP (resetClocks fm clks) ck = SOME 0
Proof
  rw [] >>
  fs [timeSemTheory.resetClocks_def] >>
  fs [MEM_EL] >> rveq >>
  match_mp_tac update_eq_zip_map_flookup >> fs []
QED



Theorem reset_clks_not_mem_flookup_same:
  ∀clks ck fm v.
    FLOOKUP fm ck = SOME v ∧
    ~MEM ck clks ⇒
    FLOOKUP (resetClocks fm clks) ck = SOME v
Proof
  rw [] >>
  fs [timeSemTheory.resetClocks_def] >>
  last_x_assum (mp_tac o GSYM) >>
  fs [] >>
  strip_tac >>
  match_mp_tac flookup_fupdate_zip_not_mem >>
  fs []
QED


Theorem flookup_reset_clks_leq:
  ∀fm ck v tclks q.
    FLOOKUP fm ck = SOME v ∧ v ≤ q ⇒
    ∃v. FLOOKUP (resetClocks fm tclks) ck = SOME v ∧ v ≤ q
Proof
  rw [] >>
  cases_on ‘MEM ck tclks’
  >- (
    drule reset_clks_mem_flookup_zero >>
    fs []) >>
  drule reset_clks_not_mem_flookup_same >>
  fs []
QED


Theorem exprClks_accumulates:
  ∀xs e ys.
    EVERY (λck. MEM ck ys) (exprClks xs e) ⇒
    EVERY (λck. MEM ck ys) xs
Proof
  ho_match_mp_tac exprClks_ind >>
  rw [] >>
  cases_on ‘e’
  >- fs [Once exprClks_def]
  >- (
   gs [] >>
   fs [exprClks_def] >>
   every_case_tac >> fs []) >>
  gs [] >>
  pop_assum mp_tac >>
  once_rewrite_tac [exprClks_def] >>
  fs []
QED


Theorem exprClks_sublist_accum:
  ∀xs e ck ys.
    MEM ck (exprClks xs e) ∧
    EVERY (λx. MEM x ys) xs ⇒
    MEM ck (exprClks ys e)
Proof
  ho_match_mp_tac exprClks_ind >>
  rw [] >>
  gs [] >>
  cases_on ‘e’
  >- fs [Once exprClks_def, EVERY_MEM]
  >- (
    gs [] >>
    fs [exprClks_def] >>
    every_case_tac >> gs [EVERY_MEM]) >>
  gs [] >>
  once_rewrite_tac [exprClks_def] >>
  fs [] >>
  first_x_assum match_mp_tac >>
  conj_tac
  >- (
    qpat_x_assum ‘MEM ck _’ mp_tac >>
    rewrite_tac [Once exprClks_def] >>
    fs []) >>
  fs [EVERY_MEM]
QED


Theorem terms_out_signals_append:
  ∀xs ys.
    terms_out_signals (xs ++ ys) =
    terms_out_signals xs ++ terms_out_signals ys
Proof
  Induct >> rw [] >>
  gs [timeLangTheory.terms_out_signals_def] >>
  cases_on ‘h’ >> gs [] >>
  cases_on ‘i’ >> gs [timeLangTheory.terms_out_signals_def]
QED


Theorem terms_out_signals_prog:
  ∀xs x out.
    MEM x xs ∧
    MEM out (terms_out_signals x) ⇒
    MEM out (terms_out_signals (FLAT xs))
Proof
  Induct >> rw [] >>
  gs [timeLangTheory.terms_out_signals_def] >>
  gs [terms_out_signals_append] >>
  metis_tac []
QED

Theorem calculate_wtime_reset_output_eq:
  calculate_wtime s clks difs = SOME wt ⇒
  calculate_wtime (resetOutput s) clks difs = SOME wt
Proof
  rw [calculate_wtime_def, resetOutput_def] >>
  gs [] >>
  qmatch_asmsub_abbrev_tac ‘list_min_option xs’ >>
  qmatch_goalsub_abbrev_tac ‘list_min_option ys’ >>
  ‘xs = ys’ by (
    unabbrev_all_tac >>
    gs [MAP_EQ_f] >>
    rw [] >> gs [] >>
    cases_on ‘e’ >>
    gs [evalDiff_def, evalExpr_def]) >>
  gs []
QED


Theorem step_ffi_bounded:
  ∀p lbl m n st st'.
    step p lbl m n st st' ⇒
    n < m
Proof
  rw [] >>
  gs [step_cases]
QED

Theorem steps_ffi_bounded:
  ∀lbls sts p m n st.
    steps p lbls m n st sts ∧
    lbls ≠ [] ⇒
    n < m
Proof
  Induct >>
  rw [] >>
  cases_on ‘sts’ >>
  gs [steps_def, step_cases]
QED

Theorem steps_lbls_sts_len_eq:
  ∀lbls sts p m n st.
    steps p lbls m n st sts ⇒
    LENGTH lbls = LENGTH sts
Proof
  Induct >>
  rw [] >>
  cases_on ‘sts’ >>
  gs [steps_def, step_cases] >>
  res_tac >> gs []
QED

Theorem pickTerm_panic_st_eq:
  ∀tms st m i st st'.
    pickTerm st m (SOME i) tms st' (LPanic (PanicInput i)) ⇒
    st' = st
Proof
 Induct >> rw [] >>
 rgs [Once pickTerm_cases] >>
 gvs [] >>
 res_tac >> gs []
QED


val _ = export_theory();
