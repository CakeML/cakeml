(*
  Properties of loopLang and loopSem
*)
Theory loopProps
Ancestors
  loopSem pan_commonProps loopLang pan_common wordSem[qualified]
Libs
  preamble

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
  (cut_sets l (Load32 n m) = insert m () l) ∧
  (cut_sets l (LoadByte n m) = insert m () l) ∧
  (cut_sets l (Seq p q) = cut_sets (cut_sets l p) q) ∧
  (cut_sets l (If _ _ _ p q nl) = nl) ∧
  (cut_sets l (Arith arith) =
   case arith of
     LLongDiv r1 r2 _ _ _ => insert r1 () $ insert r2 () l
   | LLongMul r1 r2 _ _ => insert r1 () $ insert r2 () l
   | LDiv r1 _ _ => insert r1 () l
  ) ∧
  (cut_sets l _ = l)
End

Definition comp_syntax_ok_def:
  (comp_syntax_ok l loopLang$Skip = T) ∧
  (comp_syntax_ok l (Assign n e) = T) ∧
  (comp_syntax_ok l (Loop lin p lout) = (l = lin ∧ l = lout ∧ comp_syntax_ok lin p)) ∧
  (comp_syntax_ok l (Arith arith) = T) ∧
  (comp_syntax_ok l Break = T) ∧
  (comp_syntax_ok l (LocValue n m) = T) ∧
  (comp_syntax_ok l (Load32 n m) = T) ∧
  (comp_syntax_ok l (LoadByte n m) = T) ∧
  (comp_syntax_ok l (Seq p q) = (comp_syntax_ok l p ∧ comp_syntax_ok (cut_sets l p) q)) ∧
  (comp_syntax_ok l (If c n r p q nl) =
   (comp_syntax_ok l p ∧ comp_syntax_ok l q ∧
    ∃ns. nl = FOLDL (λsp n. insert n () sp) l ns))
    ∧
  (comp_syntax_ok _ _ = F)
End

Theorem evaluate_tail_calls_eqs:
  !f t lc x.
    find_code (SOME f) ([]:'a word_loc list) t.code = SOME x ==>
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
       domain_insert,LET_THM,domain_list_insert] >>
  every_case_tac
  >~ [‘domain (acc_vars _ _) = domain _ ∪ domain(acc_vars _ _)’] >-
       (rpt (pop_assum (fn th => mp_tac (SIMP_RULE std_ss [] th))) >>
        rewrite_tac [AND_IMP_INTRO] >>
        disch_then (fn th => ntac 6 (once_rewrite_tac [th])) >>
        simp_tac (srw_ss()) [domain_def,AC UNION_COMM UNION_ASSOC,domain_union,
                             domain_insert,LET_THM] >>
        fs [EXTENSION,domain_list_insert] >> metis_tac []) >>
  rw[SET_EQ_SUBSET,SUBSET_DEF] >>
  fs [domain_list_insert] >> rw[]
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
  \\ fs [CaseEq"prod",CaseEq"option"] \\ rveq \\ fs [] >>
  TRY
   (Cases_on ‘op’>>fs[sh_mem_op_def,sh_mem_store_def,sh_mem_load_def]>>
   every_case_tac>>fs[] \\ rveq \\ fs [])
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
    s.base_addr = t.base_addr ∧ s.top_addr = t.top_addr ∧
    (!n. MEM n (locals_touched e) ==> lookup n s.locals = lookup n t.locals) ==>
    eval t e = eval s e
Proof
  ho_match_mp_tac eval_ind >> rw [] >>
  gvs[locals_touched_def,MEM_FLAT,MEM_MAP,PULL_EXISTS,eval_def,mem_load_def] >>
  ntac 2 AP_THM_TAC >> ntac 2 AP_TERM_TAC >>
  match_mp_tac MAP_CONG >>
  rw[] >>
  first_x_assum $ match_mp_tac o MP_CANON >>
  rw[] >> res_tac
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

Theorem lookup_set_vars:
  lookup n (set_vars xs ys s).locals =
  case ALOOKUP (ZIP (xs,ys)) n of
  | NONE => lookup n s.locals
  | SOME v => SOME v
Proof
  simp [loopSemTheory.set_vars_def] >>
  qabbrev_tac `t = s.locals` >> pop_assum kall_tac >>
  qid_spec_tac `t` >> qid_spec_tac `ys` >> qid_spec_tac `xs` >>
  recInduct alist_insert_ind >> rw [] >>
  simp [alist_insert_def, ZIP_def, ALOOKUP_def, lookup_insert]
QED

Theorem lookup_set_vars_not_MEM:
  ~MEM n xs ⇒ lookup n (set_vars xs ys s).locals = lookup n s.locals
Proof
  rw [lookup_set_vars] >>
  every_case_tac >> fs [] >>
  imp_res_tac ALOOKUP_MEM >>
  imp_res_tac MEM_ZIP2 >>
  fs [MEM_EL] >>
  metis_tac []
QED

Theorem lookup_alist_insert_any:
  lookup n (alist_insert xs ys t) =
  case ALOOKUP (ZIP (xs,ys)) n of
  | NONE => lookup n t
  | SOME v => SOME v
Proof
  qid_spec_tac ‘t’ >> qid_spec_tac ‘ys’ >> qid_spec_tac ‘xs’ >>
  recInduct alist_insert_ind >> rw [] >>
  simp [alist_insert_def, ZIP_def, ALOOKUP_def, lookup_insert]
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
  rpt conj_tac >> rpt gen_tac
  >~ [‘Mark’] >- suspend "Mark"
  >~ [‘loopLang$FFI _ _ _ _ _ _’] >- suspend "FFI"
  >~ [‘Seq’] >- suspend "Seq"
  >~ [‘If’] >- suspend "If"
  >~ [‘Loop’] >- suspend "Loop"
  >~ [‘Call’] >- suspend "Call"
  >~ [‘Arith arith’] >- suspend "Arith"
  >~ [‘ShMem’] >- suspend "ShMem" >>
  (rw [] >>
   fs [Once evaluate_def,AllCaseEqs(), set_var_def, set_globals_def,
       dec_clock_def, assigned_vars_def, survives_def] >>
   rveq >> fs [lookup_insert, mem_store_def, AllCaseEqs(),
               DefnBase.one_line_ify NONE loop_arith_def] >>
   rveq >> fs [state_component_equality])
QED

Resume unassigned_vars_evaluate_same[Mark]:
  rw [] >>
  fs [Once evaluate_def, AllCaseEqs(), assigned_vars_def,
      survives_def]
QED

Resume unassigned_vars_evaluate_same[FFI]:
  rw [] >>
  fs [Once evaluate_def,AllCaseEqs(), assigned_vars_def, survives_def] >>
  rveq >> fs [cut_state_def] >> rveq >>
  fs [lookup_inter,AllCaseEqs(), domain_lookup]
QED

Resume unassigned_vars_evaluate_same[Seq]:
  rw [] >>
  fs [Once evaluate_def,AllCaseEqs(), assigned_vars_def,
      survives_def] >>
  pairarg_tac >> fs [AllCaseEqs()] >> rveq >>
  res_tac >> fs []
QED

Resume unassigned_vars_evaluate_same[If]:
  rw [] >>
  fs [Once evaluate_def, AllCaseEqs(), assigned_vars_def,
      survives_def] >> rveq >>
  FULL_CASE_TAC >> fs [] >>
  rename [‘cut_res _ (evaluate (c1,s))’] >>
  cases_on ‘evaluate (c1,s)’ >> fs [] >>
  cases_on ‘q’ >> fs [cut_res_def, AllCaseEqs(), dec_clock_def, cut_state_def] >>
  rveq >> fs [lookup_inter, AllCaseEqs()] >>
  res_tac >> rfs [domain_lookup]
QED

Resume unassigned_vars_evaluate_same[Loop]:
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
  res_tac >> rfs [lookup_inter, AllCaseEqs(), domain_lookup]
QED

Resume unassigned_vars_evaluate_same[Call]:
  rpt strip_tac >>
  qpat_x_assum ‘evaluate (Call _ _ _ _,_) = _’ mp_tac >>
  once_rewrite_tac [evaluate_def, LET_THM] >>
  fs [AllCaseEqs(), cut_res_def, cut_state_def,
      dec_clock_def, set_var_def, set_vars_def] >>
  rpt strip_tac >> fs [] >> rveq >>
  fs [assigned_vars_def, survives_def, lookup_inter, AllCaseEqs(),
      domain_lookup, lookup_alist_insert_any, lookup_insert]
  >~ [‘ALOOKUP _ _ = NONE’]
  >- (disj1_tac >> simp [ALOOKUP_NONE] >>
      CCONTR_TAC >> fs [MEM_MAP, MEM_ZIP] >>
      Cases_on ‘y’ >> fs [] >>
      imp_res_tac MEM_ZIP2 >> rveq >> fs [] >>
      metis_tac [EL_MEM])
  >~ [‘cut_res _ (evaluate (_, st with locals := alist_insert ns retvs _)) = (NONE, _)’]
  >- (cases_on ‘evaluate (r,st with locals := alist_insert ns retvs (inter s.locals live))’ >>
      fs [cut_res_def, AllCaseEqs(), cut_state_def, dec_clock_def] >> rveq >> fs [] >>
      last_x_assum (qspecl_then [‘n’,‘v’] mp_tac) >>
      impl_tac
      >- (simp [] >>
          simp [ALOOKUP_NONE] >> CCONTR_TAC >> fs [MEM_MAP] >>
          Cases_on ‘y’ >> fs [] >> imp_res_tac MEM_ZIP2 >> rveq >>
          fs [] >> metis_tac [EL_MEM]) >>
      strip_tac >> fs [lookup_inter, domain_lookup])
  >~ [‘cut_res _ (evaluate (_, st with locals := alist_insert ns retvs _)) = (SOME Continue, _)’]
  >- (cases_on ‘evaluate (r,st with locals := alist_insert ns retvs (inter s.locals live))’ >>
      fs [cut_res_def, AllCaseEqs(), cut_state_def, dec_clock_def] >> rveq >> fs [] >>
      last_x_assum (qspecl_then [‘n’,‘v’] mp_tac) >>
      impl_tac
      >- (simp [] >>
          simp [ALOOKUP_NONE] >> CCONTR_TAC >> fs [MEM_MAP] >>
          Cases_on ‘y’ >> fs [] >> imp_res_tac MEM_ZIP2 >> rveq >>
          fs [] >> metis_tac [EL_MEM]) >>
      strip_tac >> fs [lookup_inter, domain_lookup])
  >~ [‘cut_res _ (evaluate (_, st with locals := alist_insert ns retvs _)) = (SOME Break, _)’]
  >- (cases_on ‘evaluate (r,st with locals := alist_insert ns retvs (inter s.locals live))’ >>
      fs [cut_res_def, AllCaseEqs(), cut_state_def, dec_clock_def] >> rveq >> fs [] >>
      last_x_assum (qspecl_then [‘n’,‘v’] mp_tac) >>
      impl_tac
      >- (simp [] >>
          simp [ALOOKUP_NONE] >> CCONTR_TAC >> fs [MEM_MAP] >>
          Cases_on ‘y’ >> fs [] >> imp_res_tac MEM_ZIP2 >> rveq >>
          fs [] >> metis_tac [EL_MEM]) >>
      strip_tac >> fs [lookup_inter, domain_lookup])
  >~ [‘cut_res _ (evaluate (_, st with locals := insert exn_v exn_val _)) = (NONE, _)’]
  >- (cases_on ‘evaluate (h,st with locals := insert exn_v exn_val (inter s.locals live))’ >>
      fs [cut_res_def, AllCaseEqs(), cut_state_def, dec_clock_def] >> rveq >> fs [] >>
      qpat_x_assum ‘∀a b. _ ⇒ lookup _ _ = SOME _’ (qspecl_then [‘n’,‘v’] mp_tac) >>
      impl_tac >- simp [] >>
      strip_tac >> fs [lookup_inter, domain_lookup])
  >~ [‘cut_res _ (evaluate (_, st with locals := insert exn_v exn_val _)) = (SOME Continue, _)’]
  >- (cases_on ‘evaluate (h,st with locals := insert exn_v exn_val (inter s.locals live))’ >>
      fs [cut_res_def, AllCaseEqs(), cut_state_def, dec_clock_def] >> rveq >> fs []) >>
  (* Call_Exn_Break catchall — original names n', exn (pre-rename). *)
  cases_on ‘evaluate (h,st with locals := insert n' exn (inter s.locals live))’ >>
  fs [cut_res_def, AllCaseEqs(), cut_state_def, dec_clock_def] >> rveq >> fs []
QED

Resume unassigned_vars_evaluate_same[Arith]:
  Cases_on ‘arith’ >>
  rw [] >>
  fs [Once evaluate_def,AllCaseEqs(), set_var_def, set_globals_def,
      dec_clock_def, assigned_vars_def, survives_def,loop_arith_def] >>
  rveq >> fs [lookup_insert, mem_store_def, AllCaseEqs()] >>
  rveq >> fs [state_component_equality]
QED

Resume unassigned_vars_evaluate_same[ShMem]:
  Cases_on ‘op’ >> rw [] >>
  fs [Once evaluate_def,AllCaseEqs(), set_var_def, set_globals_def,
      dec_clock_def, assigned_vars_def, survives_def] >>
  fs [sh_mem_op_def,sh_mem_store_def,sh_mem_load_def,set_var_def] >>
  rveq >> fs [lookup_insert, mem_store_def, AllCaseEqs(),
              DefnBase.one_line_ify NONE loop_arith_def] >>
  rveq >> fs [state_component_equality,lookup_insert]
QED

Finalise unassigned_vars_evaluate_same;

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
  fs [nested_seq_def,cut_sets_def,comp_syntax_ok_def]
QED

Theorem comp_syn_ok_nested_seq2:
  !p q l. comp_syntax_ok l (nested_seq (p ++ q)) ==>
   comp_syntax_ok l (nested_seq p) ∧
   comp_syntax_ok (cut_sets l (nested_seq p)) (nested_seq q)
Proof
  Induct >> rw [] >>
  fs [nested_seq_def, cut_sets_def,comp_syntax_ok_def] >>
  metis_tac[comp_syn_ok_nested_seq]
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
  ∀p l. comp_syntax_ok l p ==> (* need this assumption for the If case *)
   ∃(l' :sptree$num_set). cut_sets l p = union l l'
Proof
  Induct >> rw [] >>
  TRY (fs [Once comp_syntax_ok_def] >> NO_TAC) >>
  fs [cut_sets_def] >>
  TRY (qexists_tac ‘LN’ >> fs [] >> NO_TAC) >>
  TRY (
  rename [‘insert vn () l’] >>
  qexists_tac ‘insert vn () LN’ >>
  fs [Once insert_union, union_num_set_sym] >> NO_TAC)
  >- (rename1 ‘Arith l’ >> Cases_on ‘l’  >> rw[] >>
      simp[Once insert_union,union_num_set_sym] >>
      simp[Once insert_union,SimpR “union”, union_num_set_sym] >>
      metis_tac[union_num_set_sym,union_assoc])
  >- (
   gvs[comp_syntax_ok_def] >>
   res_tac >>
   simp[] >>
   metis_tac[union_assoc]) >>
  gvs[comp_syntax_ok_def] >>
  rpt $ pop_assum kall_tac >>
  qid_spec_tac ‘l’ >>
  Induct_on ‘ns’ >>
  rw[]
  >- metis_tac[union_LN] >>
  rename1 ‘insert x () sp’ >>
  first_x_assum $ qspec_then ‘insert x () sp’ strip_assume_tac >>
  rw[] >>
  metis_tac[union_num_set_sym,union_assoc,union_insert_LN]
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
  recInduct evaluate_ind >> rw []
  >~ [‘Arith’] >-
   (gvs[comp_syntax_ok_def,evaluate_def,AllCaseEqs(),
        DefnBase.one_line_ify NONE loop_arith_def] >>
    simp[state_component_equality,set_var_def])
  >~ [‘Loop’] >-
   (qpat_x_assum ‘evaluate _ = _’ $ strip_assume_tac o PURE_ONCE_REWRITE_RULE [evaluate_def] >>
    gvs[comp_syntax_ok_def,DefnBase.one_line_ify NONE cut_res_def,cut_state_def,
        AllCaseEqs(),dec_clock_def] >>
    res_tac >> gvs[state_component_equality])
  >~ [‘If’] >-
   (gvs[comp_syntax_ok_def,Once evaluate_def,DefnBase.one_line_ify NONE cut_res_def,cut_state_def,
        AllCaseEqs(),dec_clock_def] >>
    simp[state_component_equality] >>
    Cases_on ‘word_cmp cmp x y’ >> gvs[] >>
    res_tac >> gvs[state_component_equality]) >>
  gvs[comp_syntax_ok_def,Once evaluate_def] >>
  gvs[AllCaseEqs(),set_var_def] >>
  TRY pairarg_tac >> gvs[AllCaseEqs()] >>
  res_tac >>
  gvs[state_component_equality]
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
  recInduct evaluate_ind >> rw []
  >~ [‘Arith’] >-
   (gvs[evaluate_def,assigned_vars_def,
        DefnBase.one_line_ify NONE loop_arith_def,
        AllCaseEqs(),set_var_def,lookup_insert
       ])
  >~ [‘Loop’] >-
   (qpat_x_assum ‘evaluate _ = _’ $ strip_assume_tac o PURE_ONCE_REWRITE_RULE [evaluate_def] >>
    gvs[comp_syntax_ok_def,DefnBase.one_line_ify NONE cut_res_def,cut_state_def,
        AllCaseEqs(),dec_clock_def,assigned_vars_def] >>
    first_x_assum $ drule_then $ drule_at $ Pos last >>
    rw[lookup_inter_alt])
  >~ [‘If’] >-
   (gvs[comp_syntax_ok_def,Once evaluate_def,DefnBase.one_line_ify NONE cut_res_def,cut_state_def,
        AllCaseEqs(),dec_clock_def,assigned_vars_def] >>
    Cases_on ‘word_cmp cmp x y’ >>
    gvs[] >>
    res_tac >>
    rw[lookup_inter_alt])
  >~ [‘Seq’] >-
   (gvs[comp_syntax_ok_def,assigned_vars_def,Once evaluate_def] >>
    pairarg_tac >>
    gvs[AllCaseEqs()] >>
    last_x_assum drule_all >>
    rw[] >>
    first_x_assum drule >>
    disch_then $ drule_at $ Pos last >>
    imp_res_tac cut_sets_union_domain_union >>
    fs []) >>
  gvs[comp_syntax_ok_def,assigned_vars_def,Once evaluate_def,AllCaseEqs(),set_var_def,lookup_insert]
QED

Theorem eval_upd_clock_eq:
  !t e ck. eval (t with clock := ck) e =  eval t e
Proof
  ho_match_mp_tac eval_ind >> rw [] >>
  fs [eval_def]
  >- (
   every_case_tac >> fs [] >>
   fs [mem_load_def]) >>
  ntac 2 AP_THM_TAC >> ntac 2 AP_TERM_TAC >>
  match_mp_tac MAP_CONG >>
  rw[]
QED

Theorem eval_upd_locals_clock_eq:
  !t e l ck. eval (t with <|locals := l; clock := ck|>) e =  eval (t with locals := l) e
Proof
  rpt strip_tac >>
  qspec_then ‘ck’
             (dep_rewrite.DEP_ONCE_REWRITE_TAC o single o GSYM)
             (CONV_RULE (RESORT_FORALL_CONV List.rev) eval_upd_clock_eq) >>
  simp[]
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

Theorem get_vars_clock:
  ∀vs s c. get_vars vs (s with clock := c) = get_vars vs s
Proof
  Induct \\ gvs [get_vars_def]
QED

Theorem evaluate_add_clock_eq:
  !p t res st ck.
    evaluate (p,t) = (res,st) /\ res <> SOME TimeOut ==>
    evaluate (p,t with clock := t.clock + ck) = (res,st with clock := st.clock + ck)
Proof
  recInduct evaluate_ind >> rw []
  >~ [‘Seq’] >-
   (fs [evaluate_def] >> pairarg_tac >> fs [] >>
    pairarg_tac >> fs [] >> rveq >>
    fs [AllCaseEqs ()] >> rveq >> fs [] >>
    first_x_assum (qspec_then ‘ck’ mp_tac) >>
    fs [])
  >~ [‘If’] >-
   (fs [evaluate_def, AllCaseEqs ()] >>
    rveq >> cases_on ‘ri’ >> fs [get_var_imm_def] >>
    TOP_CASE_TAC >> cases_on ‘evaluate (c1,s)’ >> cases_on ‘evaluate (c2,s)’ >>
    fs [cut_res_def, cut_state_def, AllCaseEqs (), dec_clock_def] >>
    rveq >> fs [])
  >~ [‘FFI’] >-
   (fs [evaluate_def, AllCaseEqs (), cut_state_def, call_env_def] >>
    rveq >> fs [])
  >~ [‘Loop’] >-
   (fs [Once evaluate_def] >>
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
    fs [Once evaluate_def])
  >~ [‘Call’] >-
   (fs [evaluate_def, get_vars_clock_upd_eq, dec_clock_def] >>
    ntac 4 (TOP_CASE_TAC >> fs [])
    >- (
     fs [AllCaseEqs()] >>
     ‘s.clock <> 0’ by (
       fs [AllCaseEqs()] >> rveq >> fs []) >>
     rveq >> fs []) >>
    TOP_CASE_TAC >> fs [] >>
    IF_CASES_TAC >> fs [] >>
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
    fs [set_vars_def,set_var_def] >>
    rpt (TOP_CASE_TAC >> fs []) >>
    gvs [state_component_equality] >>
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
  TRY (Cases_on ‘op’)>>
  fs [evaluate_def, eval_upd_clock_eq, AllCaseEqs () ,
      set_var_def, mem_store_def, set_globals_def,
      call_env_def, dec_clock_def, set_vars_def, get_vars_clock,
      sh_mem_op_def,sh_mem_load_def,sh_mem_store_def,
      DefnBase.one_line_ify NONE loop_arith_def] >> rveq >>
  gvs [state_component_equality]
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
   st.base_addr = r.base_addr ∧ st.top_addr = r.top_addr ∧ st.mdomain = r.mdomain’
    by fs [state_component_equality] >>
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
  rw []
  >~ [‘Seq’] >- suspend "Seq"
  >~ [‘If’] >- suspend "If"
  >~ [‘Loop’] >- suspend "Loop"
  >~ [‘Call’] >- suspend "Call"
  >~ [‘loopLang$FFI _ _ _ _ _ _’] >- suspend "FFI"
  >~ [‘ShMem’] >- suspend "ShMem" >>
  (fs [evaluate_def,DefnBase.one_line_ify NONE loop_arith_def,AllCaseEqs()] >>
   fs [set_var_def, mem_store_def, set_globals_def, call_env_def, dec_clock_def,
       sh_mem_op_def,sh_mem_store_def,sh_mem_load_def] >> rveq >>
   fs [])
QED

Resume evaluate_io_events_mono[Seq]:
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >> rveq >>
  every_case_tac >> fs [] >> rveq >>
  metis_tac [IS_PREFIX_TRANS]
QED

Resume evaluate_io_events_mono[If]:
  fs [evaluate_def] >>
  every_case_tac >> fs [] >> rveq >>
  fs [] >>
  TRY (cases_on ‘evaluate (c1,s)’) >>
  TRY (cases_on ‘evaluate (c2,s)’) >>
  fs [cut_res_def] >>
  every_case_tac >> fs [] >> rveq >>
  fs [cut_state_def] >> rveq >> fs [dec_clock_def]
QED

Resume evaluate_io_events_mono[Loop]:
  pop_assum mp_tac >>
  once_rewrite_tac [evaluate_def, LET_THM] >>
  fs [AllCaseEqs()] >>
  fs [cut_res_def, cut_state_def, dec_clock_def] >> rveq >>
  fs [AllCaseEqs()] >>
  strip_tac >> fs [] >> rveq >> fs [] >>
  metis_tac [IS_PREFIX_TRANS]
QED

Resume evaluate_io_events_mono[Call]:
  pop_assum mp_tac >>
  once_rewrite_tac [evaluate_def, LET_THM] >>
  fs [AllCaseEqs(), cut_res_def, cut_state_def,
      dec_clock_def, set_var_def, set_vars_def] >>
  strip_tac >> fs [] >> rveq >> fs []
  >- (
   cases_on ‘evaluate (r,st with locals := alist_insert ns retvs (inter s.locals live))’ >>
   fs [AllCaseEqs(), cut_res_def, cut_state_def,
       dec_clock_def, set_var_def] >> rveq >> fs [] >>
   metis_tac [IS_PREFIX_TRANS]) >>
  cases_on ‘evaluate (h,st with locals := insert n exn (inter s.locals live))’ >>
  fs [AllCaseEqs(), cut_res_def, cut_state_def,
      dec_clock_def, set_var_def] >> rveq >> fs [] >>
  metis_tac [IS_PREFIX_TRANS]
QED

Resume evaluate_io_events_mono[FFI]:
  fs [evaluate_def, AllCaseEqs(), cut_state_def,
      dec_clock_def, ffiTheory.call_FFI_def, call_env_def] >>
  rveq >> fs []
QED

Resume evaluate_io_events_mono[ShMem]:
  Cases_on ‘op’ >>
  fs [evaluate_def,DefnBase.one_line_ify NONE loop_arith_def,AllCaseEqs()] >>
  fs [set_var_def, sh_mem_op_def,sh_mem_store_def,sh_mem_load_def,call_env_def] >>
  rveq >>
  fs [ffiTheory.call_FFI_def,AllCaseEqs()] >> rveq >>
  fs [state_component_equality]
QED

Finalise evaluate_io_events_mono;

Theorem evaluate_add_clock_io_events_mono:
   ∀exps s extra.
    (SND(evaluate(exps,s))).ffi.io_events ≼
    (SND(evaluate(exps,s with clock := s.clock + extra))).ffi.io_events
Proof
  recInduct evaluate_ind >>
  rw []
  >~ [‘Seq’] >- suspend "Seq"
  >~ [‘If’] >- suspend "If"
  >~ [‘Loop’] >- suspend "Loop"
  >~ [‘Call’] >- suspend "Call"
  >~ [‘loopLang$FFI _ _ _ _ _ _’] >- suspend "FFI"
  >~ [‘ShMem’] >- suspend "ShMem" >>
  (fs [evaluate_def, DefnBase.one_line_ify NONE loop_arith_def, AllCaseEqs()] >>
   fs [set_var_def, mem_store_def, set_globals_def, call_env_def, dec_clock_def,
       sh_mem_op_def, sh_mem_store_def, sh_mem_load_def] >> rveq >>
   every_case_tac >> fs [] >> rveq >> fs [])
QED

Resume evaluate_add_clock_io_events_mono[Seq]:
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >> rveq >>
  pairarg_tac >> fs [] >> rveq >>
  every_case_tac >> fs [] >> rveq >> fs []
  >- (pop_assum mp_tac >>
      drule evaluate_add_clock_eq >>
      disch_then (qspec_then ‘extra’ mp_tac) >>
      fs [] >> rpt strip_tac >> rveq >> fs [])
  >- (pop_assum mp_tac >> pop_assum mp_tac >>
      drule evaluate_add_clock_eq >>
      disch_then (qspec_then ‘extra’ mp_tac) >>
      fs [])
  >- (first_x_assum (qspec_then ‘extra’ mp_tac) >>
      strip_tac >>
      ‘s1.ffi.io_events ≼ s1'.ffi.io_events’ by rfs [] >>
      Cases_on ‘evaluate (c2,s1')’ >> fs [] >>
      ‘s1'.ffi.io_events ≼ r.ffi.io_events’ by
        metis_tac [evaluate_io_events_mono] >>
      metis_tac [IS_PREFIX_TRANS]) >>
  first_x_assum (qspec_then ‘extra’ mp_tac) >> fs []
QED

Resume evaluate_add_clock_io_events_mono[If]:
  fs [evaluate_def] >>
  every_case_tac >> fs [get_var_imm_add_clk_eq] >> rveq >>
  first_x_assum (qspec_then ‘extra’ assume_tac) >>
  fs [] >>
  Cases_on ‘evaluate (c1,s)’ >> Cases_on ‘evaluate (c2,s)’ >>
  Cases_on ‘evaluate (c1,s with clock := extra + s.clock)’ >>
  Cases_on ‘evaluate (c2,s with clock := extra + s.clock)’ >>
  fs [cut_res_def, cut_state_def, dec_clock_def] >>
  every_case_tac >> fs [] >> rveq >> fs []
QED

Resume evaluate_add_clock_io_events_mono[Loop]:
  once_rewrite_tac [evaluate_def, LET_THM] >>
  TOP_CASE_TAC >> fs [] >>
  reverse TOP_CASE_TAC
  >- (fs [cut_res_def, cut_state_def, AllCaseEqs()] >> rveq >> fs [] >>
      Cases_on ‘extra = 0’ >> fs [dec_clock_def] >>
      Cases_on ‘evaluate (body,
           s with <|locals := inter s.locals live_in; clock := extra - 1|>)’ >>
      fs [] >>
      every_case_tac >> fs [] >> rveq >> fs [] >>
      imp_res_tac evaluate_io_events_mono >> fs [] >>
      metis_tac [IS_PREFIX_TRANS, evaluate_io_events_mono, SND, PAIR]) >>
  fs [cut_res_def, cut_state_def, AllCaseEqs()] >> rveq >> fs [dec_clock_def] >>
  first_x_assum (qspec_then ‘extra’ assume_tac) >>
  Cases_on ‘evaluate
                (body,
                 s with
                   <|locals := inter s.locals live_in; clock := s.clock - 1|>)’ >>
  fs [] >>
  Cases_on ‘evaluate
                (body,
                 s with
                 <|locals := inter s.locals live_in;
                 clock := extra + s.clock - 1|>)’ >>
  fs [] >>
  Cases_on ‘q’ >> fs [] >> rveq >> fs []
  >- (Cases_on ‘q'’ >> fs [] >>
      reverse (Cases_on ‘x’) >> fs []
      >- (Cases_on ‘evaluate (Loop live_in body live_out,r')’ >>
          drule evaluate_io_events_mono >> fs [] >>
          metis_tac [IS_PREFIX_TRANS]) >>
      every_case_tac >> fs []) >>
  Cases_on ‘x’ >> fs [] >> rveq >> fs []
  >~ [‘evaluate _ = (SOME Break,_)’]
  >- (every_case_tac >> fs [] >> rveq >> fs [] >>
      Cases_on ‘evaluate (Loop live_in body live_out,r')’ >>
      drule evaluate_io_events_mono >> fs [] >>
      metis_tac [IS_PREFIX_TRANS])
  >~ [‘evaluate _ = (SOME TimeOut,_)’]
  >- (Cases_on ‘q'’ >> fs [] >>
      rename1 ‘evaluate _ = (SOME res,r')’ >>
      Cases_on ‘res’ >> fs []
      >~ [‘evaluate _ = (SOME Break,r')’]
      >- (Cases_on ‘domain live_out ⊆ domain r'.locals’ >> fs [] >>
          Cases_on ‘r'.clock = 0’ >> fs [])
      >~ [‘evaluate _ = (SOME Continue,r')’]
      >- (Cases_on ‘evaluate (Loop live_in body live_out,r')’ >>
          drule evaluate_io_events_mono >> fs [] >>
          metis_tac [IS_PREFIX_TRANS]))
  >~ [‘evaluate _ = (SOME Continue,_)’]
  >- (qpat_x_assum ‘evaluate (body,_) = (SOME Continue,r)’ assume_tac >>
      drule evaluate_add_clock_eq >> fs [] >>
      disch_then (qspec_then ‘extra’ assume_tac) >>
      fs [] >> rveq >> fs [] >>
      first_x_assum (qspec_then ‘r’ mp_tac) >> simp [] >>
      disch_then (qspec_then ‘extra’ mp_tac) >>
      fs [])
  >~ [‘evaluate _ = (SOME (Result _),_)’]
  >- (qpat_x_assum ‘evaluate _ = (SOME (Result _),_)’ assume_tac >>
      drule evaluate_add_clock_eq >> simp [] >>
      disch_then (qspec_then ‘extra’ mp_tac) >>
      strip_tac >> fs [] >> rveq >> fs [])
  >~ [‘evaluate _ = (SOME (Exception _),_)’]
  >- (qpat_x_assum ‘evaluate _ = (SOME (Exception _),_)’ assume_tac >>
      drule evaluate_add_clock_eq >> simp [] >>
      disch_then (qspec_then ‘extra’ mp_tac) >>
      strip_tac >> fs [] >> rveq >> fs [])
  >~ [‘evaluate _ = (SOME (FinalFFI _),_)’]
  >- (qpat_x_assum ‘evaluate _ = (SOME (FinalFFI _),_)’ assume_tac >>
      drule evaluate_add_clock_eq >> simp [] >>
      disch_then (qspec_then ‘extra’ mp_tac) >>
      strip_tac >> fs [] >> rveq >> fs [])
  >~ [‘evaluate _ = (SOME Error,_)’]
  >- (qpat_x_assum ‘evaluate _ = (SOME Error,_)’ assume_tac >>
      drule evaluate_add_clock_eq >> simp [] >>
      disch_then (qspec_then ‘extra’ mp_tac) >>
      strip_tac >> fs [] >> rveq >> fs [])
QED

Resume evaluate_add_clock_io_events_mono[Call]:
  once_rewrite_tac [evaluate_def, LET_THM] >>
  TOP_CASE_TAC >> fs [get_vars_clock_upd_eq] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs []
  >- (* ret = NONE (tail call) *)
   (rw []
    >- (* s.clock = 0, extra ≠ 0: LHS TimeOut, RHS evaluates body. evaluate_io_events_mono. *)
     (Cases_on ‘evaluate (r, dec_clock (s with clock := extra) with locals := q)’ >> fs [] >>
      drule evaluate_io_events_mono >> fs [dec_clock_def] >>
      Cases_on ‘q'’ >> fs [] >>
      Cases_on ‘x'’ >> fs []) >>
    (* s.clock ≠ 0: apply IH to align LHS/RHS evaluates. *)
    fs [dec_clock_def] >>
    last_x_assum drule >>
    disch_then (qspec_then ‘extra’ assume_tac) >>
    Cases_on ‘evaluate (r,s with <|locals := q; clock := s.clock - 1|>)’ >> fs [] >>
    Cases_on ‘evaluate (r,s with <|locals := q; clock := extra + s.clock - 1|>)’ >> fs [] >>
    Cases_on ‘q'’ >> Cases_on ‘q''’ >> fs [] >>
    Cases_on ‘x'’ >> fs [] >>
    rpt (Cases_on ‘x''’ >> fs [])) >>
  (* ret = SOME (ns, live) *)
  PairCases_on ‘x'’ >> fs [] >>
  IF_CASES_TAC >> fs [] >>
  fs [cut_res_def, cut_state_def] >>
  Cases_on ‘domain x'1 ⊆ domain s.locals’ >> fs [] >>
  Cases_on ‘s.clock = 0’ >> fs [] >> rveq >> fs []
  >- (* s.clock = 0: IHs vacuous. evaluate_io_events_mono + IS_PREFIX_TRANS chains throughout. *)
   (Cases_on ‘extra = 0’ >> fs [] >>
    (* extra = 0: both sides give TimeOut with same .ffi. extra ≠ 0 continues. *)
    Cases_on ‘evaluate (r,dec_clock (s with <|locals := inter s.locals x'1; clock := extra|>) with locals := q)’ >> fs [] >>
    drule evaluate_io_events_mono >> fs [dec_clock_def] >> strip_tac >>
    (* derived: s.ffi.io_events ≼ r'.ffi.io_events *)
    Cases_on ‘q'’ >> fs [] >>
    Cases_on ‘x'’ >> fs []
    (* Most x' constructors close via the inequality. Result/Exception with handler=SOME remain. *)
    >~ [‘evaluate _ = (SOME (Result _),_)’]
    >- (IF_CASES_TAC >> fs [] >>
        TOP_CASE_TAC >> fs [set_vars_def] >>
        rpt (TOP_CASE_TAC >> fs []) >>
        Cases_on ‘evaluate (q',r' with locals := alist_insert x'0 l (inter s.locals x'1))’ >> fs [] >>
        drule evaluate_io_events_mono >> fs [] >> strip_tac >>
        fs [cut_res_def, cut_state_def, dec_clock_def] >>
        every_case_tac >> fs [] >> rveq >> fs [] >>
        metis_tac [IS_PREFIX_TRANS])
    >~ [‘evaluate _ = (SOME (Exception _),_)’]
    >- (TOP_CASE_TAC >> fs [] >>
        rpt (TOP_CASE_TAC >> fs []) >>
        Cases_on ‘evaluate (q'',set_var q' w (r' with locals := inter s.locals x'1))’ >> fs [] >>
        drule evaluate_io_events_mono >> fs [set_var_def] >> strip_tac >>
        fs [cut_res_def, cut_state_def, dec_clock_def] >>
        every_case_tac >> fs [] >> rveq >> fs [] >>
        metis_tac [IS_PREFIX_TRANS])) >>
  (* s.clock ≠ 0: cut_res yields (NONE, dec_clock state). IHs apply.
     evaluate_add_clock_eq aligns LHS/RHS for non-TimeOut; IH2/3/4 for the rest. *)
  fs [dec_clock_def] >>
  Cases_on ‘evaluate (r,s with <|locals := q; clock := s.clock - 1|>)’ >> fs [] >>
  Cases_on ‘q'’ >> fs []
  >- (drule evaluate_add_clock_eq >> simp [] >>
      disch_then (qspec_then ‘extra’ mp_tac) >> simp []) >>
  Cases_on ‘x'’ >> fs []
  >~ [‘evaluate _ = (SOME (Result _),_)’]
  >- (drule evaluate_add_clock_eq >> simp [] >>
      disch_then (qspec_then ‘extra’ mp_tac) >> simp [] >> strip_tac >> fs [] >>
      IF_CASES_TAC >> fs [] >>
      TOP_CASE_TAC >> fs [set_vars_def] >>
      namedCases_on ‘x'’ ["v1 v3 hr live_out"] >> fs [] >>
      first_x_assum (qspec_then ‘extra’ assume_tac) >>
      Cases_on ‘evaluate (hr,r' with locals := alist_insert x'0 l (inter s.locals x'1))’ >> fs [] >>
      Cases_on ‘evaluate (hr,r' with <|locals := alist_insert x'0 l (inter s.locals x'1); clock := extra + r'.clock|>)’ >> fs [] >>
      fs [cut_res_def, cut_state_def, dec_clock_def] >>
      every_case_tac >> fs [] >> rveq >> fs [])
  >~ [‘evaluate _ = (SOME (Exception _),_)’]
  >- (drule evaluate_add_clock_eq >> simp [] >>
      disch_then (qspec_then ‘extra’ mp_tac) >> simp [] >> strip_tac >> fs [] >>
      TOP_CASE_TAC >> fs [] >>
      namedCases_on ‘x'’ ["nh hh vh live_out"] >> fs [set_var_def] >>
      first_x_assum (qspec_then ‘extra’ assume_tac) >>
      Cases_on ‘evaluate (hh,r' with locals := insert nh w (inter s.locals x'1))’ >> fs [] >>
      Cases_on ‘evaluate (hh,r' with <|locals := insert nh w (inter s.locals x'1); clock := extra + r'.clock|>)’ >> fs [] >>
      fs [cut_res_def, cut_state_def, dec_clock_def] >>
      every_case_tac >> fs [] >> rveq >> fs [])
  >~ [‘evaluate _ = (SOME TimeOut,_)’]
  >- (first_x_assum (qspec_then ‘extra’ assume_tac) >>
      Cases_on ‘evaluate (r,s with <|locals := q; clock := extra + s.clock - 1|>)’ >> fs [] >>
      Cases_on ‘q'’ >> fs [] >>
      Cases_on ‘x'’ >> fs []
      >~ [‘evaluate _ = (SOME (Result _),_)’]
      >- (IF_CASES_TAC >> fs [] >>
          TOP_CASE_TAC >> fs [set_vars_def] >>
          rpt (TOP_CASE_TAC >> fs []) >>
          Cases_on ‘evaluate (q',r'' with locals := alist_insert x'0 l (inter s.locals x'1))’ >> fs [] >>
          drule evaluate_io_events_mono >> fs [] >> strip_tac >>
          fs [cut_res_def, cut_state_def, dec_clock_def] >>
          every_case_tac >> fs [] >> rveq >> fs [] >>
          metis_tac [IS_PREFIX_TRANS])
      >~ [‘evaluate _ = (SOME (Exception _),_)’]
      >- (TOP_CASE_TAC >> fs [] >>
          namedCases_on ‘x'’ ["nh hh vh live_out"] >> fs [] >>
          Cases_on ‘evaluate (hh,set_var nh w (r'' with locals := inter s.locals x'1))’ >> fs [] >>
          drule evaluate_io_events_mono >> fs [set_var_def] >> strip_tac >>
          fs [cut_res_def, cut_state_def, dec_clock_def] >>
          every_case_tac >> fs [] >> rveq >> fs [] >>
          metis_tac [IS_PREFIX_TRANS])) >>
  (* Catchall: Break, Continue, FinalFFI, Error — non-TimeOut so evaluate_add_clock_eq aligns. *)
  drule evaluate_add_clock_eq >> simp [] >>
  disch_then (qspec_then ‘extra’ mp_tac) >> simp []
QED

Resume evaluate_add_clock_io_events_mono[FFI]:
  fs [evaluate_def] >>
  every_case_tac >>
  fs [cut_state_def, dec_clock_def, ffiTheory.call_FFI_def, call_env_def] >>
  rveq >> fs [] >> rveq >> fs []
QED

Resume evaluate_add_clock_io_events_mono[ShMem]:
  Cases_on ‘op’ >>
  fs [evaluate_def, DefnBase.one_line_ify NONE loop_arith_def, AllCaseEqs()] >>
  every_case_tac >>
  fs [set_var_def, eval_upd_clock_eq, call_env_def,
      sh_mem_op_def, sh_mem_store_def, sh_mem_load_def] >> rveq >>
  fs [ffiTheory.call_FFI_def, AllCaseEqs()] >>
  every_case_tac >> rveq >>
  fs [state_component_equality]
QED

Finalise evaluate_add_clock_io_events_mono;
