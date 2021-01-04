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


Theorem eval_term_inpput_ios_same:
  ∀s m n cnds tclks dest wt s'.
    evalTerm s (SOME m) (Tm (Input n) cnds tclks dest wt) s' ⇒
    m = n
Proof
  rw [] >>
  fs [evalTerm_cases]
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


val _ = export_theory();
