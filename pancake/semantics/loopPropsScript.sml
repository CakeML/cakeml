(*
  Properties of loopLang and loopSem
*)
open preamble
     loopLangTheory loopSemTheory
     pan_commonTheory pan_commonPropsTheory;

local open wordSemTheory in end;

val _ = new_theory"loopProps";

val _ = set_grammar_ancestry ["loopSem", "pan_commonProps"];


Definition every_prog_def:
  (every_prog p (Seq p1 p2) <=>
    p (Seq p1 p2) /\ every_prog p p1 /\ every_prog p p2) /\
  (every_prog p (Loop l1 body l2) <=>
    p (Loop l1 body l2) /\ every_prog p body) /\
  (every_prog p (If x1 x2 x3 p1 p2 l1) <=>
    p (If x1 x2 x3 p1 p2 l1) /\ every_prog p p1 /\ every_prog p p2) /\
  (every_prog p (Mark p1) <=>
    p (Mark p1) /\ every_prog p p1) /\
  (every_prog p (Call ret dest args handler) <=>
    p (Call ret dest args handler) /\
    (case handler of SOME (n,q,r,l) => every_prog p q ∧ every_prog p r | NONE => T)) /\
  (every_prog p prog <=> p prog)
End

Definition no_Loop_def:
  no_Loop = every_prog (\q. !l1 x l2. q <> Loop l1 x l2)
End

Definition no_Loops_def:
  no_Loops p ⇔ no_Loop p ∧ every_prog (\r. r ≠ Break ∧ r ≠ Continue) p
End

Definition syntax_ok_def: (* syntax expected by loop_remove *)
  (syntax_ok (Seq p1 p2) <=>
    ~(no_Loop (Seq p1 p2)) ∧ syntax_ok p1 /\ syntax_ok p2) /\
  (syntax_ok (Loop l1 body l2) <=>
    syntax_ok body) /\
  (syntax_ok (If x1 x2 x3 p1 p2 l1) <=>
    ~(no_Loop (If x1 x2 x3 p1 p2 l1)) ∧ syntax_ok p1 /\ syntax_ok p2) /\
  (syntax_ok (Mark p1) <=>
    no_Loop p1) /\
  (syntax_ok (Call ret dest args handler) <=>
    ~(no_Loop (Call ret dest args handler)) ∧
    (case handler of SOME (n,q,r,l) => syntax_ok q ∧ syntax_ok r | NONE => F)) /\
  (syntax_ok prog <=> F)
End

Theorem evaluate_Loop_body_same:
  (∀(s:('a,'b)state). evaluate (body,s) = evaluate (body',s)) ⇒
  ∀(s:('a,'b)state). evaluate (Loop l1 body l2,s) = evaluate (Loop l1 body' l2,s)
Proof
  rw [] \\ completeInduct_on ‘s.clock’
  \\ rw [] \\ fs [PULL_EXISTS,PULL_FORALL]
  \\ once_rewrite_tac [evaluate_def]
  \\ TOP_CASE_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ first_x_assum match_mp_tac
  \\ fs [cut_res_def,CaseEq"option",CaseEq"bool",cut_state_def]
  \\ rveq \\ fs [dec_clock_def]
  \\ imp_res_tac evaluate_clock \\ fs [dec_clock_def]
QED

Theorem evaluate_no_Break_Continue:
  ∀prog s res t.
    evaluate (prog, s) = (res,t) ∧
    every_prog (\r. r ≠ Break ∧ r ≠ Continue) prog ⇒
    res ≠ SOME Break ∧ res ≠ SOME Continue
Proof
  recInduct evaluate_ind \\ fs [] \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac
  \\ (rename [‘Loop’] ORELSE
    (fs [evaluate_def,CaseEq"option",CaseEq"word_loc",CaseEq"bool",CaseEq"ffi_result"]
     \\ rveq \\ fs []))
  \\ rpt gen_tac \\ TRY strip_tac
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [every_prog_def]
  \\ fs [CaseEq"bool"] \\ rveq \\ fs []
  THEN1
   (Cases_on ‘word_cmp cmp x y’ \\ fs []
    \\ rename [‘evaluate (xx,s)’] \\ Cases_on ‘evaluate (xx,s)’ \\ fs []
    \\ Cases_on ‘x’ \\ fs [cut_res_def,CaseEq"option",CaseEq"bool"] \\ rveq \\ fs [])
  THEN1
   (qpat_x_assum ‘evaluate _ = _’ mp_tac
    \\ once_rewrite_tac [evaluate_def]
    \\ TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC \\ fs []
    \\ fs [cut_res_def,CaseEq"option",CaseEq"bool",cut_state_def] \\ rveq \\ fs []
    \\ rw [] \\ fs [CaseEq"option",CaseEq"bool",CaseEq"prod",CaseEq"result"]
    \\ rveq \\ fs [])
  \\ fs [CaseEq"prod",CaseEq"option"] \\ rveq \\ fs []
  THEN1
   (fs [CaseEq"bool"] \\ rveq \\ fs []
    \\ fs [CaseEq"bool",CaseEq"prod",CaseEq"result",CaseEq"option"] \\ rveq \\ fs [])
  \\ fs [CaseEq"bool",CaseEq"prod",CaseEq"result",CaseEq"option",cut_res_def]
  \\ rveq \\ fs [] \\ rename [‘cut_res _ xx’] \\ Cases_on ‘xx’ \\ fs []
  \\ fs [CaseEq"bool",CaseEq"prod",CaseEq"result",CaseEq"option",cut_res_def]
  \\ rveq \\ fs []
QED


Theorem locals_touched_eq_eval_eq:
  !s e t.
   s.globals = t.globals /\ s.memory = t.memory /\ s.mdomain = t.mdomain /\
   (!n. MEM n (locals_touched e) ==> lookup n s.locals = lookup n t.locals) ==>
      eval t e = eval s e
Proof
  ho_match_mp_tac eval_ind >> rw []
  >- fs [eval_def]
  >- fs [eval_def, locals_touched_def]
  >- fs [eval_def, locals_touched_def]
  >- (
   fs [eval_def, locals_touched_def] >>
   every_case_tac >> fs [mem_load_def])
  >- (
   fs [eval_def, locals_touched_def] >>
   every_case_tac >> fs []
   >- (
    ‘the_words (MAP (λa. eval t a) wexps) = SOME x’ suffices_by fs [] >>
    pop_assum mp_tac >> pop_assum kall_tac >>
    rpt (pop_assum mp_tac) >>
    MAP_EVERY qid_spec_tac [‘x’, ‘t’, ‘s’, ‘wexps’] >>
    Induct >> rw [] >>
    fs [wordSemTheory.the_words_def,
        CaseEq "option", CaseEq "word_loc"] >> rveq >> fs [] >>
    last_x_assum (qspecl_then [‘s’, ‘t’, ‘xs’] mp_tac) >> fs [])
   >- (
    ‘the_words (MAP (λa. eval s a) wexps) = SOME x’ suffices_by fs [] >>
    pop_assum kall_tac >>
    rpt (pop_assum mp_tac) >>
    MAP_EVERY qid_spec_tac [‘x’, ‘t’, ‘s’, ‘wexps’] >>
    Induct >> rw [] >>
    fs [wordSemTheory.the_words_def,
        CaseEq "option", CaseEq "word_loc"] >> rveq >> fs [] >>
    last_x_assum (qspecl_then [‘s’, ‘t’, ‘xs’] mp_tac) >> fs []) >>
   ‘x = x'’ suffices_by fs [] >>
   rpt (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac [‘x'’, ‘x’, ‘t’, ‘s’, ‘wexps’] >>
   Induct >> rw [] >>
   fs [wordSemTheory.the_words_def,
       CaseEq "option", CaseEq "word_loc"] >> rveq >> fs [] >>
   last_x_assum (qspecl_then [‘s’, ‘t’, ‘xs’] mp_tac) >> fs []) >>
  fs [eval_def, locals_touched_def]
QED

Theorem loop_eval_nested_assign_distinct_eq:
  !es ns t ev.
   MAP (eval t) es = MAP SOME ev /\
   distinct_lists ns (FLAT (MAP locals_touched es)) /\
   ALL_DISTINCT ns /\
   LENGTH ns = LENGTH es ==>
     evaluate (nested_seq (MAP2 Assign ns es),t) =
     (NONE, t with locals := (alist_insert ns ev t.locals))
Proof
  Induct
  >- (
   rpt gen_tac >> strip_tac >>
   cases_on ‘ns’ >> fs [] >>
   fs [nested_seq_def, evaluate_def,
       alist_insert_def,
       state_component_equality]) >>
  rpt gen_tac >>
  strip_tac >>
  cases_on ‘ns’ >>
  fs [nested_seq_def] >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>
  fs [MAP_EQ_CONS] >>
  rveq >> rfs [] >>
  fs [OPT_MMAP_def] >>
  rveq >> rfs [] >>
  rveq >>
  rename [‘eval t e = SOME v’] >>
  rename [‘MAP (eval t) es = MAP SOME ev’] >>
  fs [alist_insert_def] >>
  ‘MAP (eval (set_var h' v t)) es = MAP SOME ev’ by (
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    rw [] >>
    first_x_assum (qspec_then ‘n’ assume_tac) >>
    rfs [] >>
    ‘eval (set_var h' v t) (EL n es) = eval t (EL n es)’
    suffices_by fs [] >>
    match_mp_tac locals_touched_eq_eval_eq >>
    fs [set_var_def] >>
    rw [] >>
    fs [distinct_lists_def, lookup_insert] >>
    TOP_CASE_TAC >> fs [] >> rveq >>
    metis_tac [MEM_FLAT, EL_MEM, MEM_MAP]) >>
  fs [] >>
  last_x_assum drule >>
  disch_then (qspec_then ‘t'’ mp_tac) >>
  fs [] >>
  impl_tac
  >- (
   ho_match_mp_tac (GEN_ALL distinct_lists_cons) >>
   qexists_tac ‘locals_touched e’ >>
   qexists_tac ‘[h']’ >>
   fs []) >>
  strip_tac >>
  fs [set_var_def] >>
  drule (INST_TYPE [``:'a``|->``:'a word_loc``]
         alist_insert_pull_insert) >>
  disch_then (qspecl_then [‘v’, ‘ev’, ‘t.locals’] mp_tac) >>
  fs []
QED

Theorem get_var_imm_add_clk_eq:
  get_var_imm ri (s with clock := ck) =
  get_var_imm ri s
Proof
  rw [] >>
  cases_on ‘ri’ >> fs [get_var_imm_def]
QED


Theorem get_vars_local_clock_upd_eq:
  !ns st l ck.
   get_vars ns (st with <|locals := l; clock := ck|>) =
   get_vars ns (st with locals := l)
Proof
  Induct >> rw [] >>
  fs [get_vars_def]
QED

Theorem get_vars_local_update_some_eq:
  !ns vs st.
   ALL_DISTINCT ns /\ LENGTH ns = LENGTH vs ==>
   get_vars ns (st with locals := alist_insert ns vs st.locals) = SOME vs
Proof
  Induct >> rw [] >>
  fs [get_vars_def] >>
  cases_on ‘vs’ >>
  fs [alist_insert_def] >>
  first_x_assum (qspecl_then
                 [‘t’, ‘st with locals := insert h h' st.locals’] mp_tac) >>
  fs [] >> strip_tac >>
  qsuff_tac ‘alist_insert ns t (insert h h' st.locals) =
             insert h h' (alist_insert ns t st.locals)’
  >- (strip_tac >> fs []) >>
  ho_match_mp_tac alist_insert_pull_insert >>
  fs []
QED

Definition survives_def:
  (survives n (If c r ri p q cs) <=>
     survives n p ∧ survives n q ∧ n ∈ domain cs) ∧
  (survives n (Loop il p ol) <=>
    n ∈ domain il ∧ n ∈ domain ol ∧ survives n p) ∧
  (survives n (Call (SOME (m,cs)) trgt args NONE) <=>
     n ∈ domain cs) ∧
  (survives n (Call (SOME (m,cs)) trgt args (SOME (r,p,q,ps))) <=>
     n ∈ domain cs ∧ n ∈ domain ps ∧ survives n p ∧ survives n q) ∧
  (survives n (FFI fi ptr1 len1 ptr2 len2 cs) <=> n ∈ domain cs) ∧
  (survives n (Mark p) <=> survives n p) ∧
  (survives n (Seq p q) <=> survives n p ∧ survives n q) ∧
  (survives n p <=> T)
End


Theorem unassigned_vars_evaluate_same:
  !p s res t (l:sptree$num_set) n v.
   evaluate (p,s) = (res,t) /\
   (res = NONE ∨ res = SOME Continue ∨ res = SOME Break) /\
   lookup n s.locals = SOME v /\
    ~MEM n (assigned_vars p) /\ survives n p ==>
  lookup n t.locals = lookup n s.locals
Proof
  recInduct evaluate_ind >>
  rpt conj_tac >> rpt gen_tac >>
  TRY (
  rename [‘Mark’] >>
  rw [] >>
  fs [Once evaluate_def, AllCaseEqs(), assigned_vars_def,
      survives_def]) >>
  TRY (
  rename [‘FFI’] >>
  rw [] >>
  fs [Once evaluate_def,AllCaseEqs(), assigned_vars_def, survives_def] >>
  rveq >> fs [cut_state_def] >> rveq >>
  fs [lookup_inter,AllCaseEqs(), domain_lookup]) >>
  TRY (
  rename [‘Seq’] >>
  rw [] >>
  fs [Once evaluate_def,AllCaseEqs(), assigned_vars_def,
      survives_def] >>
  pairarg_tac >> fs [AllCaseEqs()] >> rveq >>
  res_tac >> fs []) >>
  TRY (
  rename [‘If’] >>
  rw [] >>
  fs [Once evaluate_def, AllCaseEqs(), assigned_vars_def,
      survives_def] >> rveq >>
  FULL_CASE_TAC >> fs [] >>
  rename [‘cut_res _ (evaluate (c1,s))’] >>
  cases_on ‘evaluate (c1,s)’ >> fs [] >>
  cases_on ‘q’ >> fs [cut_res_def, AllCaseEqs(), dec_clock_def, cut_state_def] >>
  rveq >> fs [lookup_inter, AllCaseEqs()] >>
  res_tac >> rfs [domain_lookup]) >>
  TRY (
  rename [‘Loop’] >>
  rpt strip_tac >>
  qpat_x_assum ‘evaluate (Loop _ _ _,_) = _’ mp_tac >>
  once_rewrite_tac [evaluate_def] >>
  rewrite_tac [cut_res_def, cut_state_def, dec_clock_def] >>
  reverse (cases_on ‘domain live_in ⊆ domain s.locals’)
  >- rw [] >>
  rw [] >>
  FULL_CASE_TAC >>
  cases_on ‘q’ >> fs [] >>
  fs [Once cut_res_def, cut_state_def] >>
  fs [survives_def, assigned_vars_def, dec_clock_def] >>
  fs [AllCaseEqs()] >> rveq >> fs [] >>
  res_tac >> rfs [lookup_inter, AllCaseEqs(), domain_lookup]) >>
  TRY (
  rename [‘Call’] >>
  rpt strip_tac >>
  qpat_x_assum ‘evaluate (Call _ _ _ _,_) = _’ mp_tac >>
  once_rewrite_tac [evaluate_def] >>
  rpt TOP_CASE_TAC
  >- (
   strip_tac >>
   rfs [] >> rveq >>
   fs [assigned_vars_def, survives_def, set_var_def, cut_res_def,
       dec_clock_def, cut_state_def, AllCaseEqs(), lookup_insert] >>
   rveq >> fs [lookup_inter, AllCaseEqs(), domain_lookup]) >> cheat) >>
  rw [] >>
  fs [Once evaluate_def,AllCaseEqs(), set_var_def, set_globals_def,
      dec_clock_def, assigned_vars_def, survives_def] >>
  rveq >> fs [lookup_insert, mem_store_def, AllCaseEqs()] >>
  rveq >> fs [state_component_equality]
QED

(*
Theorem unassigned_vars_evaluate_same:
  !p s res t (l:sptree$num_set) n.
   evaluate (p,s) = (res,t) /\
   (res = NONE ∨ res = SOME Continue ∨ res = SOME Break) /\
    ~MEM n (assigned_vars p) /\ (?v. lookup n (cutset l p) = SOME v) ==>
  lookup n t.locals = lookup n s.locals
Proof
  recInduct evaluate_ind >>
  rpt conj_tac >> rpt gen_tac >>
  TRY (
  rw [] >>
  fs [Once evaluate_def,AllCaseEqs(), set_var_def, set_globals_def,
      dec_clock_def, assigned_vars_def, cutset_def] >>
  rveq >> fs [lookup_insert, mem_store_def, AllCaseEqs()] >>
  rveq >> fs [state_component_equality] >> NO_TAC) >>
  TRY (
  rename [‘Mark’] >>
  rw [] >>
  fs [Once evaluate_def,AllCaseEqs(), assigned_vars_def,
      cutset_def, lookup_inter] >>
  res_tac >> fs []) >>
  TRY (
  rename [‘FFI’] >>
  rw [] >>
  fs [Once evaluate_def,AllCaseEqs(), assigned_vars_def, cutset_def] >>
  rveq >> fs [cut_state_def] >> rveq >> fs [lookup_inter,AllCaseEqs()] >>
  cases_on ‘lookup n s.locals’ >> fs []) >>
  TRY (
  rename [‘Seq’] >>
  rw [] >>
  fs [Once evaluate_def,AllCaseEqs(), assigned_vars_def,
      cutset_def, lookup_inter] >>
  pairarg_tac >> fs [AllCaseEqs()] >> rveq >>
  res_tac >> fs [] >> res_tac >> fs [] >> NO_TAC) >>
  TRY (
  rename [‘If’] >>
  rw [] >>
  fs [Once evaluate_def, AllCaseEqs(), assigned_vars_def,
      cutset_def] >> rveq >> fs [lookup_inter, AllCaseEqs()] >>
  FULL_CASE_TAC >> fs [] >>
  rename [‘cut_res _ (evaluate (c1,s))’] >>
  cases_on ‘evaluate (c1,s)’ >> fs [] >>
  cases_on ‘q’ >> fs [cut_res_def, AllCaseEqs(), dec_clock_def, cut_state_def] >>
  rveq >> fs [lookup_inter, AllCaseEqs()] >>
  res_tac >> rfs [] >> rw [] >>
  cases_on ‘lookup n s.locals’ >> fs []) >>
  TRY (
  rename [‘Loop’] >>
  rw [] >>
  qpat_x_assum ‘evaluate (Loop _ _ _,_) = _’ mp_tac >>
  once_rewrite_tac [evaluate_def] >>
  strip_tac >> fs [AllCaseEqs ()] >> rveq >>
  fs [assigned_vars_def, cutset_def, cut_res_def, cut_state_def,
      AllCaseEqs (), dec_clock_def] >>
  rveq >> fs [] >>
  fs [lookup_inter_alt] >>
  res_tac >> rfs [domain_lookup] >>
  res_tac >> fs []) >>
  rename [‘Call’] >>
  rw [] >>
  fs [evaluate_def] >>
  FULL_CASE_TAC >> fs []
  >- (
   every_case_tac >>
   fs [cut_res_def, cut_state_def, AllCaseEqs()]) >>
  fs [AllCaseEqs()] >> fs [] >> rveq >> fs [] >>
  fs [cut_res_def, cut_state_def, AllCaseEqs(),
      dec_clock_def, set_var_def] >> rveq >> fs [] >>
  fs [cutset_def, lookup_inter, CaseEq "option"] >> rveq >>
  fs [assigned_vars_def, lookup_insert,
      lookup_inter_alt, domain_lookup] >>
  rename [‘evaluate
           (r,st with locals := insert n' retv (inter s.locals live))’] >>
  cases_on ‘evaluate
            (r,st with locals := insert n' retv (inter s.locals live))’ >>
  fs [cut_res_def, cut_state_def, AllCaseEqs()] >> rveq >> fs [dec_clock_def] >>
  res_tac >> fs [lookup_inter] >> TOP_CASE_TAC >> fs []
QED
*)

val _ = export_theory();
