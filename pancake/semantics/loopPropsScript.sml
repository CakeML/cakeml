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


Definition cut_sets_def:
  (cut_sets l Skip = l) ∧
  (cut_sets l (LocValue n m) = insert n () l) ∧
  (cut_sets l (Assign n e) = insert n () l) ∧
  (cut_sets l (LoadByte n m) = insert m () l) ∧
  (cut_sets l (Seq p q) = cut_sets (cut_sets l p) q) ∧
  (cut_sets l (If _ _ _ p q nl) = nl) ∧
  (cut_sets l _ = l)
End

Definition comp_syntax_ok_def:
  comp_syntax_ok l p <=>
    p = Skip ∨
    ?n m. p = LocValue n m ∨
    ?n e. p = Assign n e ∨
    ?n m. p = LoadByte n m ∨
    ?c n m v v'. p = If c n (Reg m) (Assign n v) (Assign n v') (list_insert [n; m] l) ∨
    ?q r. p = Seq q r ∧ comp_syntax_ok l q ∧ comp_syntax_ok (cut_sets l q) r
Termination
 cheat
End

Theorem evaluate_tail_calls_eqs:
  !f t lc x. find_code (SOME f) ([]:'a word_loc list) t.code = SOME x ==>
   evaluate ((Call NONE (SOME f) [] NONE): 'a loopLang$prog, t) =
   evaluate (Call NONE (SOME f) [] NONE, t with locals := lc)
Proof
  rw [] >>
  fs [evaluate_def] >>
  TOP_CASE_TAC >> fs [get_vars_def] >> rveq >>
  fs [] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  fs [dec_clock_def]
QED

Theorem acc_vars_acc:
  ∀p l.
    domain (acc_vars p l) = domain (acc_vars p LN) ∪ domain l
Proof
  qsuff_tac ‘∀p (l:num_set) l.
    domain (acc_vars p l) = domain (acc_vars p LN) UNION domain l’
  >- metis_tac [] >>
  ho_match_mp_tac acc_vars_ind >> rw [] >> fs [] >>
  ntac 4 (once_asm_rewrite_tac [acc_vars_def]) >>
  simp_tac (srw_ss()) [domain_def,AC UNION_COMM UNION_ASSOC,domain_union,
       domain_insert,LET_THM] >>
  every_case_tac >>
  simp_tac (srw_ss()) [domain_def,AC UNION_COMM UNION_ASSOC,domain_union,
       domain_insert,LET_THM] >>
  once_rewrite_tac [INSERT_SING_UNION] >>
  simp_tac (srw_ss()) [domain_def,AC UNION_COMM UNION_ASSOC,domain_union,
       domain_insert,LET_THM] >>
  rpt (pop_assum (fn th => mp_tac (SIMP_RULE std_ss [] th))) >>
  rewrite_tac [AND_IMP_INTRO] >>
  disch_then (fn th => ntac 6 (once_rewrite_tac [th])) >>
  simp_tac (srw_ss()) [domain_def,AC UNION_COMM UNION_ASSOC,domain_union,
       domain_insert,LET_THM] >> fs [EXTENSION] >> metis_tac []
QED

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

Theorem get_vars_clock_upd_eq:
  !ns st l ck.
   get_vars ns (st with clock := ck) =
   get_vars ns st
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


Theorem unassigned_vars_evaluate_same:
  !p s res t n v.
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
  rpt strip_tac
  >- (
   (* NONE result *)
   qpat_x_assum ‘evaluate (Call _ _ _ _,_) = _’ mp_tac >>
   once_rewrite_tac [evaluate_def] >>
   rpt TOP_CASE_TAC
   >- (
    strip_tac >>
    rfs [] >> rveq >>
    fs [assigned_vars_def, survives_def, set_var_def, cut_res_def,
        dec_clock_def, cut_state_def, AllCaseEqs(), lookup_insert] >>
    rveq >> fs [lookup_inter, AllCaseEqs(), domain_lookup])
   >- (
    pop_assum kall_tac >>
    pop_assum mp_tac >>
    pop_assum kall_tac >>
    strip_tac >>
    rfs [] >> rveq >>
    fs [assigned_vars_def, survives_def, set_var_def, cut_res_def,
        dec_clock_def, cut_state_def, AllCaseEqs(), lookup_insert] >>
    rveq >> fs [lookup_inter, AllCaseEqs(), domain_lookup] >>
    qmatch_goalsub_abbrev_tac ‘cut_res nr (evaluate (rq,ar)) = _’ >>
    cases_on ‘evaluate (rq, ar)’ >>
    qmatch_asmsub_rename_tac ‘ evaluate _ = (tq,tr)’ >>
    strip_tac >> cases_on ‘tq’ >>
    fs [cut_res_def, cut_state_def, dec_clock_def,
        AllCaseEqs()] >> rveq >>
    fs [] >>
    unabbrev_all_tac >> fs [] >>
    qsuff_tac ‘lookup n tr.locals = SOME v’
    >- (strip_tac >> fs [lookup_inter]) >>
    first_x_assum match_mp_tac >>
    fs []) >>
   pop_assum mp_tac >>
   pop_assum kall_tac >>
   pop_assum kall_tac >>
   strip_tac >>
   rfs [] >> rveq >>
   fs [assigned_vars_def, survives_def, set_var_def, cut_res_def,
       dec_clock_def, cut_state_def, AllCaseEqs(), lookup_insert] >>
   rveq >> fs [lookup_inter, AllCaseEqs(), domain_lookup] >>
   qmatch_goalsub_abbrev_tac ‘cut_res nr (evaluate (rq,ar)) = _’ >>
   cases_on ‘evaluate (rq, ar)’ >>
   qmatch_asmsub_rename_tac ‘ evaluate _ = (tq,tr)’ >>
   strip_tac >> cases_on ‘tq’ >>
   fs [cut_res_def, cut_state_def, dec_clock_def,
       AllCaseEqs()] >> rveq >>
   fs [] >>
   unabbrev_all_tac >> fs [] >>
   qsuff_tac ‘lookup n tr.locals = SOME v’
   >- (strip_tac >> fs [lookup_inter]) >>
   first_x_assum match_mp_tac >>
   fs []) >>
  (* non-NONE result *)
  (qpat_x_assum ‘evaluate (Call _ _ _ _,_) = _’ mp_tac >>
  once_rewrite_tac [evaluate_def] >>
  rpt TOP_CASE_TAC
  >- (
   pop_assum kall_tac >>
   pop_assum mp_tac >>
   pop_assum kall_tac >>
   strip_tac >>
   rfs [] >> rveq >>
   fs [assigned_vars_def, survives_def, set_var_def, cut_res_def,
       dec_clock_def, cut_state_def, AllCaseEqs(), lookup_insert] >>
   rveq >> fs [lookup_inter, AllCaseEqs(), domain_lookup] >>
   qmatch_goalsub_abbrev_tac ‘cut_res nr (evaluate (rq,ar)) = _’ >>
   cases_on ‘evaluate (rq, ar)’ >>
   qmatch_asmsub_rename_tac ‘ evaluate _ = (tq,tr)’ >>
   strip_tac >> cases_on ‘tq’ >>
   fs [cut_res_def, cut_state_def, dec_clock_def,
       AllCaseEqs()]) >>
  pop_assum mp_tac >>
  pop_assum kall_tac >>
  pop_assum kall_tac >>
  strip_tac >>
  rfs [] >> rveq >>
  fs [assigned_vars_def, survives_def, set_var_def, cut_res_def,
      dec_clock_def, cut_state_def, AllCaseEqs(), lookup_insert] >>
  rveq >> fs [lookup_inter, AllCaseEqs(), domain_lookup] >>
  qmatch_goalsub_abbrev_tac ‘cut_res nr (evaluate (rq,ar)) = _’ >>
  cases_on ‘evaluate (rq, ar)’ >>
  qmatch_asmsub_rename_tac ‘ evaluate _ = (tq,tr)’ >>
  strip_tac >> cases_on ‘tq’ >>
  fs [cut_res_def, cut_state_def, dec_clock_def,
      AllCaseEqs()])) >>
  rw [] >>
  fs [Once evaluate_def,AllCaseEqs(), set_var_def, set_globals_def,
      dec_clock_def, assigned_vars_def, survives_def] >>
  rveq >> fs [lookup_insert, mem_store_def, AllCaseEqs()] >>
  rveq >> fs [state_component_equality]
QED


Theorem evaluate_nested_seq_cases:
  (!p q s st t.
    evaluate (nested_seq (p ++ q), s) = (NONE, t) /\
    evaluate (nested_seq p,s) = (NONE,st) ==>
    evaluate (nested_seq q,st) = (NONE,t)) /\
  (!p s st q.
    evaluate (nested_seq p, s) = (NONE, st) ==>
    evaluate (nested_seq (p ++ q), s) =  evaluate (nested_seq q, st)) /\
  (!p s res st q.
    evaluate (nested_seq p, s) = (res, st) /\
    res <> NONE ==>
    evaluate (nested_seq (p ++ q), s) =  evaluate (nested_seq p, s))
Proof
  rpt conj_tac >>
  Induct >> rw []
  >- fs [nested_seq_def, evaluate_def] >>
  fs [nested_seq_def, evaluate_def] >>
  pairarg_tac >> fs [] >>
  FULL_CASE_TAC >> fs [] >>
  res_tac >> fs []
QED


Theorem survives_nested_seq_intro:
  !p q n.
   survives n (nested_seq p) /\
   survives n (nested_seq q) ==>
   survives n (nested_seq (p ++ q))
Proof
  Induct >> rw [] >>
  fs [nested_seq_def, survives_def]
QED

Theorem nested_assigns_survives:
  !xs ys n.
   LENGTH xs = LENGTH ys ==>
   survives n (nested_seq (MAP2 Assign xs ys))
Proof
  Induct >> rw [] >>
  TRY (cases_on ‘ys’) >>
  fs [nested_seq_def, survives_def]
QED

Theorem comp_syn_ok_basic_cases:
  (!l. comp_syntax_ok l Skip) /\
  (!l n m. comp_syntax_ok l (LocValue n m)) /\
  (!l n e. comp_syntax_ok l (Assign n e)) /\
  (!l n m. comp_syntax_ok l (LoadByte n m)) /\
  (!l c n m v v'. comp_syntax_ok l (If c n (Reg m)
       (Assign n v) (Assign n v') (list_insert [n; m] l)))
Proof
  rw [] >>
  ntac 3 (fs [Once comp_syntax_ok_def])
QED


Theorem comp_syn_ok_seq:
  !l p q. comp_syntax_ok l (Seq p q) ==>
   comp_syntax_ok l p /\ comp_syntax_ok (cut_sets l p) q
Proof
  rw [] >>
  fs [Once comp_syntax_ok_def]
QED


Theorem comp_syn_ok_if:
  comp_syntax_ok l (If cmp n ri p q ns) ==>
    ?v v' m. ri = Reg m /\ p = Assign n v /\
       q = Assign n v' /\ ns = list_insert [n; m] l
Proof
  rw [] >>
  fs [Once comp_syntax_ok_def]
QED


Theorem comp_syn_ok_seq2:
  !l p q. comp_syntax_ok l p /\ comp_syntax_ok (cut_sets l p) q ==>
   comp_syntax_ok l (Seq p q)
Proof
  rw [] >>
  once_rewrite_tac [comp_syntax_ok_def] >>
  fs []
QED


Theorem comp_syn_ok_nested_seq:
  !p q l. comp_syntax_ok l (nested_seq p) ∧
   comp_syntax_ok (cut_sets l (nested_seq p)) (nested_seq q) ==>
   comp_syntax_ok l (nested_seq (p ++ q))
Proof
  Induct >> rw [] >>
  fs [nested_seq_def] >>
  fs [cut_sets_def] >>
  drule comp_syn_ok_seq >>
  strip_tac >> res_tac >> fs [] >>
  metis_tac [comp_syn_ok_seq2]
QED

Theorem comp_syn_ok_nested_seq2:
  !p q l. comp_syntax_ok l (nested_seq (p ++ q)) ==>
   comp_syntax_ok l (nested_seq p) ∧
   comp_syntax_ok (cut_sets l (nested_seq p)) (nested_seq q)
Proof
  Induct >> rw [] >>
  fs [nested_seq_def, comp_syn_ok_basic_cases, cut_sets_def] >>
  drule comp_syn_ok_seq >> strip_tac >> fs [] >>
  metis_tac [comp_syn_ok_seq2]
QED


Theorem cut_sets_nested_seq:
  !p q l. cut_sets l (nested_seq (p ++ q)) =
   cut_sets (cut_sets l (nested_seq p)) (nested_seq q)
Proof
  Induct >> rw [] >>
  fs [nested_seq_def]
  >- fs [cut_sets_def] >>
  fs [cut_sets_def]
QED


Theorem cut_sets_union_accumulate:
  !p l. comp_syntax_ok l p ==> (* need this assumption for the If case *)
   ?(l' :sptree$num_set). cut_sets l p = union l l'
Proof
  Induct >> rw [] >>
  TRY (fs [Once comp_syntax_ok_def] >> NO_TAC) >>
  fs [cut_sets_def] >>
  TRY (qexists_tac ‘LN’ >> fs [] >> NO_TAC) >>
  TRY (
  rename [‘insert vn () l’] >>
  qexists_tac ‘insert vn () LN’ >>
  fs [Once insert_union, union_num_set_sym] >> NO_TAC)
  >- (
   drule comp_syn_ok_seq >>
   strip_tac >>
   last_x_assum drule >>
   strip_tac >> fs [] >>
   last_x_assum (qspec_then ‘union l l'’ mp_tac) >>
   fs [] >> strip_tac >>
   qexists_tac ‘union l' l''’ >>
   fs [] >> metis_tac [union_assoc]) >>
  drule comp_syn_ok_if >>
  strip_tac >> rveq >>
  qexists_tac ‘insert m () (insert n () LN)’ >>
  fs [list_insert_def] >>
  metis_tac [union_insert_LN, insert_union, union_num_set_sym, union_assoc]
QED


Theorem cut_sets_union_domain_subset:
  !p l. comp_syntax_ok l p ==>
    domain l ⊆ domain (cut_sets l p)
Proof
  rw [] >>
  drule cut_sets_union_accumulate >>
  strip_tac >> fs [] >>
  fs [domain_union]
QED

Theorem cut_sets_union_domain_union:
  !p l. comp_syntax_ok l p ==>
   ?(l' :sptree$num_set). domain (cut_sets l p) = domain l ∪ domain l'
Proof
  rw [] >>
  drule cut_sets_union_accumulate >>
  strip_tac >> fs [] >>
  qexists_tac ‘l'’ >>
  fs [domain_union]
QED

Theorem comp_syn_impl_cut_sets_subspt:
  !p l. comp_syntax_ok l p ==>
  subspt l (cut_sets l p)
Proof
  rw [] >>
  drule cut_sets_union_accumulate >>
  strip_tac >>
  fs [subspt_union]
QED

Theorem comp_syn_cut_sets_mem_domain:
  !p l n .
   comp_syntax_ok l p /\ n ∈ domain l ==>
    n ∈ domain (cut_sets l p)
Proof
  rw [] >>
  drule cut_sets_union_domain_union >>
  strip_tac >> fs []
QED


Theorem comp_syn_ok_upd_local_clock:
  !p s res t l.
    evaluate (p,s) = (res,t) /\
    comp_syntax_ok l p ==>
     t = s with <|locals := t.locals; clock := t.clock|>
Proof
  recInduct evaluate_ind >> rw [] >>
  TRY (fs [Once comp_syntax_ok_def, every_prog_def] >> NO_TAC) >>
  TRY (
  fs [evaluate_def] >> rveq >>
  TRY every_case_tac >> fs [set_var_def, state_component_equality] >> NO_TAC)
  >- (
   drule comp_syn_ok_seq >>
   strip_tac >>
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >>
   FULL_CASE_TAC >> fs []  >> rveq >>
   res_tac >> fs [state_component_equality]) >>
  drule comp_syn_ok_if >>
  strip_tac >> rveq >>
  fs [evaluate_def] >>
  every_case_tac >> fs [] >> rveq >>
  fs [state_component_equality, evaluate_def, comp_syn_ok_basic_cases] >>
  every_case_tac >>
  fs [cut_res_def, cut_state_def, dec_clock_def, set_var_def] >>
  every_case_tac >> fs [] >> rveq >> fs []
QED


Theorem assigned_vars_nested_seq_split:
  !p q.
    assigned_vars (nested_seq (p ++ q)) =
    assigned_vars (nested_seq p) ++ assigned_vars (nested_seq q)
Proof
  Induct >> rw [] >>
  fs [nested_seq_def, assigned_vars_def]
QED


Theorem assigned_vars_seq_split:
  !q p. assigned_vars (Seq p q) =
    assigned_vars p ++ assigned_vars q
Proof
  rw [] >> fs [assigned_vars_def, cut_sets_def]
QED

Theorem assigned_vars_nested_assign:
  !xs ys.
   LENGTH xs = LENGTH ys ==>
   assigned_vars (nested_seq (MAP2 Assign xs ys)) = xs
Proof
  Induct >> rw [] >>
  TRY (cases_on ‘ys’) >>
  fs [nested_seq_def, assigned_vars_def]
QED


Theorem comp_syn_ok_lookup_locals_eq:
  !p s res t l n.
   evaluate (p,s) = (res,t) /\ res <> SOME TimeOut /\
   comp_syntax_ok l p /\ n ∈ domain l /\
    ~MEM n (assigned_vars p) ==>
  lookup n t.locals = lookup n s.locals
Proof
  recInduct evaluate_ind >> rw [] >>
  TRY (fs [Once comp_syntax_ok_def, every_prog_def] >> NO_TAC) >>
  TRY (
  fs [evaluate_def] >>
  every_case_tac >> fs [] >> rveq >>
  fs [set_var_def, assigned_vars_def, lookup_insert] >> NO_TAC)
  >- (
   drule comp_syn_ok_seq >>
   strip_tac >>
   fs [evaluate_def, assigned_vars_def] >>
   pairarg_tac >> fs [AllCaseEqs ()] >> rveq >> fs []
   >- (
    qpat_x_assum ‘evaluate (_,s1) = _’ assume_tac  >>
    drule evaluate_clock >> fs [] >>
    strip_tac >> fs [] >>
    dxrule comp_syn_ok_seq >>
    strip_tac >>
    first_x_assum drule >>
    disch_then (qspec_then ‘n’ mp_tac) >>
    fs [] >>
    strip_tac >>
    first_x_assum drule >>
    disch_then (qspec_then ‘n’ mp_tac) >>
    fs [] >>
    impl_tac
    >- (
     qpat_x_assum ‘comp_syntax_ok l c1’ assume_tac >>
     drule cut_sets_union_domain_union >>
     strip_tac >> fs []) >>
    fs []) >>
   drule comp_syn_ok_seq >>
   strip_tac >>
   res_tac >> fs []) >>
  drule evaluate_clock >> fs [] >>
  strip_tac >> fs [] >>
  drule comp_syn_ok_if >>
  strip_tac >> rveq >> fs [] >>
  fs [evaluate_def, assigned_vars_def] >>
  fs [AllCaseEqs()]  >> rveq >> fs [domain_inter] >>
  cases_on ‘word_cmp cmp x y’ >> fs [] >>
  fs [evaluate_def, list_insert_def, AllCaseEqs()] >>
  FULL_CASE_TAC >> fs [cut_res_def, set_var_def, dec_clock_def, cut_state_def] >>
  FULL_CASE_TAC >> fs [] >> rveq >>
  every_case_tac >> rfs [] >> rveq >> fs [] >>
  fs [state_component_equality, lookup_inter, lookup_insert] >>
  every_case_tac >> rfs [domain_lookup]
QED

Theorem eval_upd_clock_eq:
  !t e ck. eval (t with clock := ck) e =  eval t e
Proof
  ho_match_mp_tac eval_ind >> rw [] >>
  fs [eval_def]
  >- (
   every_case_tac >> fs [] >>
   fs [mem_load_def]) >>
  qsuff_tac ‘the_words (MAP (λa. eval (t with clock := ck) a) wexps) =
             the_words (MAP (λa. eval t a) wexps)’ >>
  fs [] >>
  pop_assum mp_tac >>
  qid_spec_tac ‘wexps’ >>
  Induct >> rw [] >>
  last_x_assum mp_tac >>
  impl_tac >- metis_tac [] >>
  strip_tac >> fs [wordSemTheory.the_words_def]
QED

(* should be trivial, but record updates are annoying *)

Theorem eval_upd_locals_clock_eq:
  !t e l ck. eval (t with <|locals := l; clock := ck|>) e =  eval (t with locals := l) e
Proof
  ho_match_mp_tac eval_ind >> rw [] >>
  fs [eval_def]
  >- (
   every_case_tac >> fs [] >>
   fs [mem_load_def]) >>
  qsuff_tac ‘the_words (MAP (λa. eval (t with <|locals := l; clock := ck|>) a) wexps) =
             the_words (MAP (λa. eval (t with locals := l) a) wexps)’ >>
  fs [] >>
  pop_assum mp_tac >>
  qid_spec_tac ‘wexps’ >>
  Induct >> rw [] >>
  last_x_assum mp_tac >>
  impl_tac >- metis_tac [] >>
  strip_tac >> fs [wordSemTheory.the_words_def]
QED

Theorem cut_res_add_clock:
  cut_res l (res,s) = (q,r) /\ q <> SOME TimeOut ==>
  cut_res l (res,s with clock := ck + s.clock) =
    (q,r with clock := ck + r.clock)
Proof
  rw [cut_res_def, cut_state_def] >>
  ‘s.clock <> 0’ by fs [AllCaseEqs()] >>
  fs [] >> rveq >> fs [dec_clock_def]
QED

Theorem evaluate_add_clock_eq:
  !p t res st ck.
   evaluate (p,t) = (res,st) /\ res <> SOME TimeOut ==>
    evaluate (p,t with clock := t.clock + ck) = (res,st with clock := st.clock + ck)
Proof
  recInduct evaluate_ind >> rw [] >>
  TRY (fs [Once evaluate_def] >> NO_TAC) >>
  TRY (
  rename [‘Seq’] >>
  fs [evaluate_def] >> pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  fs [AllCaseEqs ()] >> rveq >> fs [] >>
  first_x_assum (qspec_then ‘ck’ mp_tac) >>
  fs []) >>
  TRY (
  rename [‘If’] >>
  fs [evaluate_def, AllCaseEqs ()] >>
  rveq >> cases_on ‘ri’ >> fs [get_var_imm_def] >>
  TOP_CASE_TAC >> cases_on ‘evaluate (c1,s)’ >> cases_on ‘evaluate (c2,s)’ >>
  fs [cut_res_def, cut_state_def, AllCaseEqs (), dec_clock_def] >>
  rveq >> fs []) >>
  TRY (
  rename [‘FFI’] >>
  fs [evaluate_def, AllCaseEqs (), cut_state_def, call_env_def] >>
  rveq >> fs []) >>
  TRY (
  rename [‘Loop’] >>
  fs [Once evaluate_def] >>
  TOP_CASE_TAC >> fs [] >>
  cases_on ‘cut_res live_in ((NONE:'a result option),s)’ >>
  fs [] >>
  ‘q' <> SOME TimeOut’ by (
    CCONTR_TAC >>
    fs [cut_res_def, cut_state_def, AllCaseEqs(), dec_clock_def]) >>
  drule cut_res_add_clock >>
  disch_then (qspec_then ‘ck’ mp_tac) >> fs [] >>
  strip_tac >> fs [] >> rveq >>
  TOP_CASE_TAC >> fs [] >>
  cases_on ‘evaluate (body,r')’ >> fs [] >> rveq >>
  cases_on ‘q’ >> fs [] >>
  cases_on ‘x’ >> fs [] >> rveq >> fs []
  >- (imp_res_tac cut_res_add_clock >> res_tac >> fs []) >>
  first_x_assum match_mp_tac >>
  TOP_CASE_TAC >> fs [] >>
  reverse TOP_CASE_TAC >> fs []
  >- fs [Once evaluate_def] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  fs [Once evaluate_def]) >>
  TRY (
  rename [‘Call’] >>
  fs [evaluate_def, get_vars_clock_upd_eq, dec_clock_def] >>
  ntac 4 (TOP_CASE_TAC >> fs [])
  >- (
   fs [AllCaseEqs()] >>
   ‘s.clock <> 0’ by (
     fs [AllCaseEqs()] >> rveq >> fs []) >>
   rveq >> fs []) >>
  TOP_CASE_TAC >> fs [] >>
  cases_on ‘cut_res r' ((NONE:'a result option),s)’ >>
  fs [] >>
  ‘q'' <> SOME TimeOut’ by (
    CCONTR_TAC >>
    fs [cut_res_def, cut_state_def, AllCaseEqs(), dec_clock_def]) >>
  drule cut_res_add_clock >>
  disch_then (qspec_then ‘ck’ mp_tac) >> fs [] >>
  strip_tac >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  cases_on ‘evaluate (r,r'' with locals := q)’ >> fs [] >> rveq >>
  cases_on ‘q''’ >> fs [] >> rveq >>
  cases_on ‘x'’ >> fs [] >> rveq >>
  TOP_CASE_TAC >> fs [] >> rveq >>
  fs [set_var_def] >>
  rpt (TOP_CASE_TAC >> fs []) >>
  qmatch_goalsub_abbrev_tac ‘cut_res nr (evaluate (rq,ar)) = _’ >>
  qmatch_asmsub_abbrev_tac ‘evaluate (rq, lr)’ >>
  cases_on ‘evaluate (rq, lr)’ >>
  qmatch_asmsub_rename_tac ‘ evaluate _ = (tq,tr)’ >>
  ‘tq <> SOME TimeOut’ by (
    CCONTR_TAC >>
    unabbrev_all_tac >>
    fs [cut_res_def, cut_state_def, AllCaseEqs(), dec_clock_def]) >>
  first_x_assum (qspecl_then [‘tq’, ‘tr’, ‘ck’] mp_tac) >>
  fs [] >> strip_tac >>
  imp_res_tac cut_res_add_clock >>
  res_tac >> fs []) >>
  fs [evaluate_def, eval_upd_clock_eq, AllCaseEqs () ,
      set_var_def, mem_store_def, set_globals_def,
      call_env_def, dec_clock_def] >> rveq >>
  fs [state_component_equality]
QED

Theorem evaluate_nested_seq_comb_seq:
  !p q t.
   evaluate (Seq (nested_seq p) (nested_seq q), t) =
   evaluate (nested_seq (p ++ q), t)
Proof
  Induct >> rw [] >>
  fs [nested_seq_def, evaluate_def] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  cases_on ‘res' = NONE’ >> fs [] >> rveq >> fs [] >>
  first_x_assum (qspecl_then [‘q’,‘s1'’] mp_tac) >>
  fs []
QED


Theorem nested_seq_pure_evaluation:
  !p q t r st l m e v ck ck'.
  evaluate (nested_seq p,t with clock := ck + t.clock) = (NONE,st) /\
  evaluate (nested_seq q,st with clock := ck' + st.clock) = (NONE,r) /\
  comp_syntax_ok l (nested_seq p) /\
  comp_syntax_ok (cut_sets l (nested_seq p)) (nested_seq q) /\
  (!n. MEM n (assigned_vars (nested_seq p)) ==> n < m) /\
  (!n. MEM n (assigned_vars (nested_seq q)) ==> m <= n) /\
  (!n. MEM n (locals_touched e) ==> n < m /\ n ∈ domain (cut_sets l (nested_seq p))) /\
   eval st e = SOME v ==>
    eval r e = SOME v
Proof
  rw [] >>
  drule_all comp_syn_ok_upd_local_clock >>
  fs [] >> strip_tac >>
  ‘st.globals = r.globals /\ st.memory = r.memory /\
   st.mdomain = r.mdomain’ by fs [state_component_equality] >>
  drule locals_touched_eq_eval_eq >> fs [] >>
  disch_then (qspec_then ‘e’ mp_tac) >> fs [] >>
  impl_tac
  >- (
   rw []  >>
   drule comp_syn_ok_lookup_locals_eq >>
   disch_then (qspecl_then [‘cut_sets l (nested_seq p)’, ‘n’] mp_tac) >>
   impl_tac
   >- (
    fs [] >>
    CCONTR_TAC >> fs [] >>
    res_tac >> fs []) >> fs []) >> fs []
QED

Theorem evaluate_io_events_mono:
   !exps s1 res s2.
    evaluate (exps,s1) = (res, s2)
    ⇒
    s1.ffi.io_events ≼ s2.ffi.io_events
Proof
  recInduct evaluate_ind >>
  rw [] >>
  TRY (
  rename [‘Seq’] >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >> rveq >>
  every_case_tac >> fs [] >> rveq >>
  metis_tac [IS_PREFIX_TRANS]) >>
  TRY (
  rename [‘If’] >>
  fs [evaluate_def] >>
  every_case_tac >> fs [] >> rveq >>
  fs [] >>
  TRY (cases_on ‘evaluate (c1,s)’) >>
  TRY (cases_on ‘evaluate (c2,s)’) >>
  fs [cut_res_def] >>
  every_case_tac >> fs [] >> rveq >>
  fs [cut_state_def] >> rveq >> fs [dec_clock_def]) >>
  TRY (
  rename [‘Loop’] >>
  pop_assum mp_tac >>
  once_rewrite_tac [evaluate_def, LET_THM] >>
  fs [AllCaseEqs()] >>
  fs [cut_res_def, cut_state_def, dec_clock_def] >> rveq >>
  fs [AllCaseEqs()] >>
  strip_tac >> fs [] >> rveq >> fs [] >>
  metis_tac [IS_PREFIX_TRANS]) >>
  TRY (
  rename [‘Call’] >>
  pop_assum mp_tac >>
  once_rewrite_tac [evaluate_def, LET_THM] >>
  fs [AllCaseEqs(), cut_res_def, cut_state_def,
      dec_clock_def, set_var_def] >>
  strip_tac >> fs [] >> rveq >> fs []
  >- (
   cases_on ‘evaluate (r,st with locals := insert n retv (inter s.locals live))’ >>
   fs [AllCaseEqs(), cut_res_def, cut_state_def,
       dec_clock_def, set_var_def] >> rveq >> fs [] >>
   metis_tac [IS_PREFIX_TRANS]) >>
  cases_on ‘evaluate (h,st with locals := insert n' exn (inter s.locals live))’ >>
  fs [AllCaseEqs(), cut_res_def, cut_state_def,
      dec_clock_def, set_var_def] >> rveq >> fs [] >>
  metis_tac [IS_PREFIX_TRANS]) >>
  TRY (
  rename [‘FFI’] >>
  fs [evaluate_def, AllCaseEqs(), cut_state_def,
      dec_clock_def, ffiTheory.call_FFI_def, call_env_def] >>
  rveq >> fs []) >>
  fs [evaluate_def] >>
  every_case_tac >>
  fs [set_var_def, mem_store_def, set_globals_def, call_env_def,
      dec_clock_def] >> rveq >>
  fs []
QED

Theorem evaluate_add_clock_io_events_mono:
   ∀exps s extra.
    (SND(evaluate(exps,s))).ffi.io_events ≼
    (SND(evaluate(exps,s with clock := s.clock + extra))).ffi.io_events
Proof
  cheat
  (* recInduct evaluate_ind >>
  srw_tac[][evaluate_def,LET_THM] >>
  TRY (
    rename1`find_code` >>
    Cases_on`get_vars args s`>>full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    Cases_on`ret`>>full_simp_tac(srw_ss())[] >- (
      every_case_tac >> full_simp_tac(srw_ss())[] >> rveq >>
      imp_res_tac evaluate_io_events_mono >> full_simp_tac(srw_ss())[] >>
      imp_res_tac evaluate_add_clock >> full_simp_tac(srw_ss())[] >>
      fsrw_tac[ARITH_ss][dec_clock_def] >>
      rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[])) >>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    qpat_abbrev_tac`opt = find_code _ _ _ _` >>
    Cases_on`opt`>>full_simp_tac(srw_ss())[markerTheory.Abbrev_def]>>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    Cases_on`cut_env names s.locals`>>full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    CASE_TAC >> full_simp_tac(srw_ss())[] >>
    CASE_TAC >> full_simp_tac(srw_ss())[] >>
    CASE_TAC >> full_simp_tac(srw_ss())[] >>
    CASE_TAC >> full_simp_tac(srw_ss())[] >> rveq >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
    TRY IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
    TRY (
      split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
      split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
      imp_res_tac evaluate_add_clock >> full_simp_tac(srw_ss())[] >>
      fsrw_tac[ARITH_ss][dec_clock_def] >>
      qpat_x_assum`z ≠ SOME TimeOut ⇒ _`mp_tac >>
      qmatch_assum_rename_tac`z ≠ SOME TimeOut ⇒ _` >>
      Cases_on`z=SOME TimeOut`>>full_simp_tac(srw_ss())[]>-(
        strip_tac >>
        every_case_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
        rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[]) >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
        imp_res_tac evaluate_io_events_mono >> full_simp_tac(srw_ss())[] >>
        imp_res_tac pop_env_const >> rveq >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
        metis_tac[evaluate_io_events_mono,set_var_const,IS_PREFIX_TRANS,SND,PAIR,set_var_with_const,with_clock_ffi]) >>
      rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[]) >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
      every_case_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
      rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[]) >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
      imp_res_tac evaluate_io_events_mono >> full_simp_tac(srw_ss())[] >>
      imp_res_tac pop_env_const >> rveq >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
      metis_tac[evaluate_io_events_mono,set_var_const,IS_PREFIX_TRANS,SND,PAIR,set_var_with_const,with_clock_ffi]) >>
    TRY(
      split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
      imp_res_tac evaluate_add_clock >> full_simp_tac(srw_ss())[] >>
      fsrw_tac[ARITH_ss][dec_clock_def] >>
      rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[]) >> srw_tac[][] >>
      every_case_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
      rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[]) >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
      imp_res_tac evaluate_io_events_mono >> full_simp_tac(srw_ss())[] >>
      imp_res_tac pop_env_const >> rveq >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
      metis_tac[evaluate_io_events_mono,set_var_const,IS_PREFIX_TRANS,SND,PAIR,set_var_with_const,with_clock_ffi]) >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
    rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[]) >> srw_tac[][] >>
    imp_res_tac evaluate_io_events_mono >> full_simp_tac(srw_ss())[] >>
    imp_res_tac pop_env_const >> rveq >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
    metis_tac[evaluate_io_events_mono,set_var_const,IS_PREFIX_TRANS,SND,PAIR,set_var_with_const,with_clock_ffi]) >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  rpt (pairarg_tac >> full_simp_tac(srw_ss())[]) >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_add_clock >> full_simp_tac(srw_ss())[] >>
  rveq >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_io_events_mono >> rev_full_simp_tac(srw_ss())[] >>
  metis_tac[evaluate_io_events_mono,IS_PREFIX_TRANS,SND,PAIR] *)
QED





val _ = export_theory();
