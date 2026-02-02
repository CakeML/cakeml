(*
  crepLang Properties
*)
Theory crepProps
Libs
  preamble
Ancestors
  panSem pan_common panProps crepLang crepSem pan_commonProps


Definition cexp_heads_simp_def:
  cexp_heads_simp es =
  if (MEM [] es) then NONE
  else SOME (MAP HD es)
End

Theorem lookup_locals_eq_map_vars:
  ∀ns t.
  OPT_MMAP (FLOOKUP t.locals) ns =
  OPT_MMAP (eval t) (MAP Var ns)
Proof
  rw [] >>
  match_mp_tac IMP_OPT_MMAP_EQ >>
  fs [MAP_MAP_o] >>
  fs [MAP_EQ_f] >> rw [] >>
  fs [crepSemTheory.eval_def]
QED


Theorem length_load_shape_eq_shape:
  !n a e.
   LENGTH (load_shape a n e) = n
Proof
  Induct >> rw [] >>
  once_rewrite_tac [load_shape_def] >>
  fs [] >>
  every_case_tac >> fs []
QED

Theorem eval_load_shape_el_rel:
  !m n a t e.
  n < m ==>
  eval t (EL n (load_shape a m e)) =
  eval t (Load (Op Add [e; Const (a + bytes_in_word * n2w n)]))
Proof
  Induct >> rw [] >>
  once_rewrite_tac [load_shape_def] >>
  fs [ADD1] >>
  cases_on ‘n’ >> fs []
  >- (
   TOP_CASE_TAC >> fs [] >>
   fs [eval_def, OPT_MMAP_def] >>
   TOP_CASE_TAC >> fs [] >>
   TOP_CASE_TAC >> fs [] >>
   fs [wordLangTheory.word_op_def]) >>
  rw [] >>
  fs [ADD1] >>
  fs [GSYM word_add_n2w, WORD_LEFT_ADD_DISTRIB]
QED

Theorem mem_load_flat_rel:
  ∀sh adr s v n.
  mem_load sh adr s.memaddrs (s.memory: 'a word -> 'a word_lab) = SOME v ∧
  n < LENGTH (flatten v) ==>
  crepSem$mem_load (adr + bytes_in_word * n2w (LENGTH (TAKE n (flatten v)))) s =
  SOME (EL n (flatten v))
Proof
  rw [] >>
  qmatch_asmsub_abbrev_tac `mem_load _ adr dm m = _` >>
  ntac 2 (pop_assum(mp_tac o REWRITE_RULE [markerTheory.Abbrev_def])) >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [‘n’,‘s’, `v`,`m`,`dm`,`adr`, `sh`] >>
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL] >>
  qsuff_tac ‘(∀sh adr dm (m: 'a word -> 'a word_lab) v.
       mem_load sh adr dm m = SOME v ⇒
       ∀(s :(α, β) state) n.
           n < LENGTH (flatten v) ⇒
           dm = s.memaddrs ⇒
           m = s.memory ⇒
           mem_load (adr + bytes_in_word * n2w n) s = SOME (EL n (flatten v))) /\
       (∀sh adr dm (m: 'a word -> 'a word_lab) v.
       mem_loads sh adr dm m = SOME v ⇒
       ∀(s :(α, β) state) n.
           n < LENGTH (FLAT (MAP flatten v)) ⇒
           dm = s.memaddrs ⇒
           m = s.memory ⇒
           mem_load (adr + bytes_in_word * n2w n) s = SOME (EL n (FLAT (MAP flatten v))))’
  >- metis_tac [] >>
  ho_match_mp_tac mem_load_ind >>
  rpt strip_tac >> rveq
  >- (
   fs [panSemTheory.mem_load_def] >>
   cases_on ‘sh’ >> fs [option_case_eq] >>
   rveq
   >- (fs [flatten_def] >> rveq  >> fs [mem_load_def]) >>
   first_x_assum drule >>
   disch_then (qspec_then ‘s’ mp_tac) >>
   fs [flatten_def, ETA_AX])
  >-  (
   fs [panSemTheory.mem_load_def] >>
   rveq >> fs [flatten_def]) >>
  fs [panSemTheory.mem_load_def] >>
  cases_on ‘sh’ >> fs [option_case_eq] >> rveq
  >- (
   fs [flatten_def] >>
   cases_on ‘n’ >> fs [EL] >>
   fs [panLangTheory.size_of_shape_def] >>
   fs [n2w_SUC, WORD_LEFT_ADD_DISTRIB]) >>
  first_x_assum drule >>
  disch_then (qspec_then ‘s’ mp_tac) >>
  fs [] >>
  strip_tac >>
  first_x_assum (qspec_then ‘s’ mp_tac) >>
  strip_tac >> fs [] >>
  fs [flatten_def, ETA_AX] >>
  cases_on ‘0 <= n /\ n < LENGTH (FLAT (MAP flatten vs))’ >>
  fs []
  >- fs [EL_APPEND_EQN] >>
  fs [NOT_LESS] >>
  ‘n - LENGTH (FLAT (MAP flatten vs)) < LENGTH (FLAT (MAP flatten vs'))’ by
    DECIDE_TAC >>
  last_x_assum drule >>
  strip_tac >> fs [] >>
  fs [EL_APPEND_EQN] >>
  ‘size_of_shape (Comb l) = LENGTH (FLAT (MAP flatten vs))’ by (
    ‘mem_load (Comb l) adr s.memaddrs s.memory = SOME (Struct vs)’ by
       rw [panSemTheory.mem_load_def] >>
    drule mem_load_some_shape_eq >>
    strip_tac >> pop_assum (assume_tac o GSYM) >>
    fs [] >>
    metis_tac [GSYM length_flatten_eq_size_of_shape, flatten_def]) >>
  fs [] >>
  drule n2w_sub >>
  strip_tac >> fs [] >>
  fs [WORD_LEFT_ADD_DISTRIB] >>
  fs [GSYM WORD_NEG_RMUL]
QED

Theorem update_locals_not_vars_eval_eq:
  ∀s e v n w.
  ~MEM n (var_cexp e) /\
  eval s e = SOME v ==>
  eval (s with locals := s.locals |+ (n,w)) e = SOME v
Proof
  ho_match_mp_tac eval_ind >> rpt strip_tac >>
  gvs[eval_def,var_cexp_def, FLOOKUP_UPDATE,AllCaseEqs(),
      mem_load_def, wordLangTheory.word_op_def, PULL_EXISTS,
      oneline crep_op_def, MAP_EQ_CONS, MEM_FLAT, MEM_MAP,
      opt_mmap_eq_some, SF DNF_ss] >>
  irule_at (Pos last) EQ_REFL >>
  gvs[MAP_EQ_EVERY2,LIST_REL_EL_EQN] >>
  rw[] >> metis_tac[EL_MEM]
QED

Theorem update_locals_not_vars_eval_eq'[local]:
  ∀s e v n w res.
  ~MEM n (var_cexp e) ∧
   eval s e = res
  ==>
  eval (s with locals := s.locals |+ (n,w)) e = res
Proof
  ho_match_mp_tac eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (fs [eval_def])
  >- fs [eval_def, var_cexp_def, FLOOKUP_UPDATE]
  >- (
   rpt strip_tac >> fs [var_cexp_def] >>
   fs [eval_def, CaseEq "option", CaseEq "word_lab"] >>
   rveq >> fs [mem_load_def]
   )
  >- (
   rpt gen_tac >>
   strip_tac >> fs [var_cexp_def] >>
   fs [eval_def, CaseEq "option", CaseEq "word_lab"] >>
   rveq >> fs [mem_load_def])
  >- (
   rpt gen_tac >>
   strip_tac >> fs [var_cexp_def] >>
   fs [eval_def, CaseEq "option", CaseEq "word_lab"] >>
   rveq >> fs [mem_load_def])
  >- fs [var_cexp_def, eval_def, CaseEq "option"]
  >- (
   rpt strip_tac \\
   fs[eval_def,AllCaseEqs()] \\
   gvs[]
   THEN1 (disj1_tac \\
          pop_assum (rw o single o GSYM) \\
          match_mp_tac OPT_MMAP_CONG \\
          rw[]\\
          gvs[var_cexp_def,MEM_MAP,MEM_FLAT] \\
          first_x_assum(match_mp_tac o MP_CANON) \\
          metis_tac[]) \\
   disj2_tac \\
   qexists_tac ‘ws’ \\
   simp[] \\
   FULL_SIMP_TAC std_ss [GSYM NOT_EVERY] \\
   qpat_x_assum ‘_ = SOME ws’ (rw o single o GSYM) \\
   match_mp_tac OPT_MMAP_CONG \\
   rw[]\\
   gvs[var_cexp_def,MEM_MAP,MEM_FLAT] \\
   first_x_assum(match_mp_tac o MP_CANON) \\
   metis_tac[])
  >- (
   rpt strip_tac >>
   gvs[eval_def,var_cexp_def,MEM_FLAT,MEM_MAP] >>
   qmatch_goalsub_abbrev_tac ‘option_CASE a1 _ _ = option_CASE a2 _ _’ >>
   ‘a1 = a2’ suffices_by simp[] >>
   unabbrev_all_tac >>
   match_mp_tac OPT_MMAP_cong >>
   rw[] >>
   metis_tac[]) >>
  rpt gen_tac >>
  rpt strip_tac >> fs [var_cexp_def, ETA_AX] >>
  fs [eval_def, CaseEq "option", CaseEq "word_lab"] >>
  rveq >> metis_tac []
QED

Theorem update_locals_not_vars_eval_eq':
  ∀s e v n w.
  ~MEM n (var_cexp e)
  ==>
  eval (s with locals := s.locals |+ (n,w)) e = eval s e
Proof
  metis_tac[update_locals_not_vars_eval_eq']
QED

Theorem update_locals_not_vars_eval_eq'':
  ∀s e v n w locals.
  ~MEM n (var_cexp e)
  ==>
  eval (s with locals := locals |+ (n,w)) e = eval (s with locals := locals) e
Proof
  rpt strip_tac \\
  ‘(s with locals := locals |+ (n,w)) = (s with locals := locals) with locals := (s with locals := locals).locals |+ (n,w)’ by simp[state_component_equality] \\
  pop_assum $ SUBST_TAC o single \\
  metis_tac[update_locals_not_vars_eval_eq']
QED

Theorem var_exp_load_shape:
  !i a e n.
   MEM n (load_shape a i e) ==>
   var_cexp n = var_cexp e
Proof
  Induct >>
  rw [load_shape_def] >>
  fs [var_cexp_def] >>
  metis_tac []
QED


Theorem map_var_cexp_eq_var:
  !vs. FLAT (MAP var_cexp (MAP Var vs)) = vs
Proof
  Induct >> rw [var_cexp_def] >>
  fs [var_cexp_def]
QED

Theorem res_var_commutes:
  n ≠ h ==>
  res_var (res_var lc (h,FLOOKUP lc' h))
  (n,FLOOKUP lc' n) =
  res_var (res_var lc (n,FLOOKUP lc' n))
  (h,FLOOKUP lc' h)
Proof
  rw [] >>
  cases_on ‘FLOOKUP lc' h’ >>
  cases_on ‘FLOOKUP lc' n’ >>
  fs[res_var_def] >>
  fs [DOMSUB_COMMUTES, DOMSUB_FUPDATE_NEQ] >>
  metis_tac [FUPDATE_COMMUTES]
QED

Theorem flookup_res_var_diff_eq:
  n <> m ==>
  FLOOKUP (res_var l (m,v)) n = FLOOKUP l n
Proof
  rw [] >> cases_on ‘v’ >>
  fs [res_var_def, FLOOKUP_UPDATE, DOMSUB_FLOOKUP_NEQ]
QED

Theorem flookup_res_var_thm:
  FLOOKUP (res_var l (m,v)) n =
  if n = m then
    v
  else
    FLOOKUP l n
Proof
  Cases_on ‘v’ \\ rw[res_var_def,DOMSUB_FLOOKUP_THM,FLOOKUP_UPDATE]
QED

Theorem unassigned_free_vars_evaluate_same:
  !p s res t n.
   evaluate (p,s) = (res,t) /\
   (res = NONE ∨ res = SOME Continue ∨ res = SOME Break) /\
    ~MEM n (assigned_free_vars p) ==>
  FLOOKUP t.locals n = FLOOKUP s.locals n
Proof
  recInduct evaluate_ind >> rw [] >> fs [] >>
  TRY(qpat_x_assum ‘evaluate (While _ _,_) = (_,_)’ mp_tac >>
      once_rewrite_tac [evaluate_def] >>
      ntac 4 (TOP_CASE_TAC >> fs []) >>
      pairarg_tac >> fs [] >>
      fs [] >>
      TOP_CASE_TAC >> fs [] >>
      strip_tac
      >- (
       first_x_assum drule >>
       fs [] >>
       disch_then drule >>
       fs [assigned_free_vars_def] >>
       first_x_assum drule >>
       fs [dec_clock_def]) >>
      FULL_CASE_TAC >> fs [] >>
      fs [assigned_free_vars_def] >>
      first_x_assum drule >>
      fs [dec_clock_def]) >>
  TRY
  (fs [evaluate_def, assigned_free_vars_def, AllCaseEqs(),
       set_globals_def, state_component_equality] >>
   TRY (pairarg_tac) >> rveq >> fs [] >> rveq >>
   FULL_CASE_TAC >> metis_tac [] >>
   NO_TAC) >>
  TRY
  (fs [evaluate_def, assigned_free_vars_def,MEM_FILTER] >> fs [CaseEq "option"] >>
   pairarg_tac >> fs [] >> rveq >> gvs[flookup_res_var_thm] >>
   first_x_assum drule >>
   fs [state_component_equality, FLOOKUP_UPDATE] >>
   metis_tac[] >> NO_TAC) >>
  TRY
  (fs [evaluate_def, assigned_free_vars_def,MEM_FILTER] >> fs [CaseEq "option", CaseEq "word_lab"] >>
   rveq >> fs [state_component_equality, FLOOKUP_UPDATE] >>
   fs [panSemTheory.mem_store_def, state_component_equality] >> NO_TAC) >>
  TRY
  (cases_on ‘caltyp’ >>
   fs [evaluate_def, assigned_free_vars_def, CaseEq "option",  CaseEq "word_lab"]  >>
   rveq >> rename1 ‘lookup_code _ _ _ _ = SOME v6’ >> cases_on ‘v6’ >> fs[] >>
   every_case_tac >> fs [set_var_def, state_component_equality, assigned_free_vars_def] >>
   TRY (qpat_x_assum ‘s.locals |+ (_,_) = t.locals’ (mp_tac o GSYM) >>
        fs [FLOOKUP_UPDATE] >> NO_TAC) >>
   res_tac >> fs [FLOOKUP_UPDATE] >> NO_TAC) >>
  TRY
  (fs [evaluate_def, assigned_free_vars_def,MEM_FILTER] >> fs [CaseEq "option"] >>
   pairarg_tac >> fs [] >> rveq >>
   FULL_CASE_TAC >>
   metis_tac [] >> NO_TAC) >>
  fs [evaluate_def, assigned_free_vars_def, dec_clock_def, CaseEq "option",
      CaseEq "word_lab", CaseEq "ffi_result"]  >>
  rveq >> TRY (FULL_CASE_TAC) >>fs [state_component_equality]
>>
(Cases_on ‘op’>>fs[sh_mem_op_def,sh_mem_load_def,sh_mem_store_def]>>
 every_case_tac>>fs[set_var_def,empty_locals_def]>>rveq>>fs[FLOOKUP_UPDATE])
QED

Theorem assigned_free_vars_IMP_assigned_vars:
  ∀prog x. MEM x (assigned_free_vars prog) ⇒ MEM x (assigned_vars prog)
Proof
  Induct using assigned_vars_ind \\ rw[assigned_free_vars_def,assigned_vars_def,MEM_FILTER] \\
  gvs[]
QED

Theorem unassigned_vars_evaluate_same:
  !p s res t n.
   evaluate (p,s) = (res,t) /\
   (res = NONE ∨ res = SOME Continue ∨ res = SOME Break) /\
    ~MEM n (assigned_free_vars p) ==>
  FLOOKUP t.locals n = FLOOKUP s.locals n
Proof
  metis_tac[assigned_free_vars_IMP_assigned_vars,unassigned_free_vars_evaluate_same]
QED

Theorem assigned_vars_nested_decs_append:
  !ns es p.
  LENGTH ns = LENGTH es ==>
  assigned_vars (nested_decs ns es p) = ns ++ assigned_vars p
Proof
  Induct >> rw [] >> fs [nested_decs_def] >>
  cases_on ‘es’ >>
  fs [nested_decs_def, assigned_vars_def]
QED

Theorem assigned_free_vars_nested_decs_append:
  !ns es p.
  LENGTH ns = LENGTH es ==>
  assigned_free_vars (nested_decs ns es p) = FILTER (λx. ¬MEM x ns) $ assigned_free_vars p
Proof
  Induct >> rw [] >> fs [nested_decs_def] >>
  cases_on ‘es’ >>
  fs [nested_decs_def, assigned_free_vars_def,FILTER_FILTER] >>
  rpt(AP_TERM_TAC ORELSE AP_THM_TAC) >> metis_tac[]
QED

Theorem nested_seq_assigned_vars_eq:
  !ns vs.
  LENGTH ns = LENGTH vs ==>
  assigned_vars (nested_seq (MAP2 Assign ns vs)) = ns
Proof
  Induct >> rw [] >- fs [nested_seq_def, assigned_vars_def] >>
  cases_on ‘vs’ >> fs [nested_seq_def, assigned_vars_def]
QED

Theorem nested_seq_assigned_free_vars_eq:
  !ns vs.
  LENGTH ns = LENGTH vs ==>
  assigned_free_vars (nested_seq (MAP2 Assign ns vs)) = ns
Proof
  Induct >> rw [] >- fs [nested_seq_def, assigned_free_vars_def] >>
  cases_on ‘vs’ >> fs [nested_seq_def, assigned_free_vars_def]
QED

Theorem assigned_vars_seq_store_empty:
  !es ad a.
  assigned_vars (nested_seq (stores ad es a)) =  []
Proof
  Induct >> rw [] >>
  fs [stores_def, assigned_vars_def, nested_seq_def] >>
  FULL_CASE_TAC >> fs [stores_def, assigned_vars_def,
                       nested_seq_def]
QED

Theorem assigned_free_vars_seq_store_empty:
  !es ad a.
  assigned_free_vars (nested_seq (stores ad es a)) =  []
Proof
  Induct >> rw [] >>
  fs [stores_def, assigned_free_vars_def, nested_seq_def] >>
  FULL_CASE_TAC >> fs [stores_def, assigned_free_vars_def,
                       nested_seq_def]
QED

Theorem assigned_vars_store_globals_empty:
  !es ad.
  assigned_vars (nested_seq (store_globals ad es)) =  []
Proof
  Induct >> rw [] >>
  fs [store_globals_def, assigned_vars_def, nested_seq_def] >>
  fs [store_globals_def, assigned_vars_def, nested_seq_def]
QED

Theorem assigned_free_vars_store_globals_empty:
  !es ad.
  assigned_free_vars (nested_seq (store_globals ad es)) =  []
Proof
  Induct >> rw [] >>
  fs [store_globals_def, assigned_free_vars_def, nested_seq_def] >>
  fs [store_globals_def, assigned_free_vars_def, nested_seq_def]
QED

Theorem length_load_globals_eq_read_size:
  !ads a.
   LENGTH (load_globals a ads) = ads
Proof
  Induct >> rw [] >> fs [load_globals_def]
QED

Theorem el_load_globals_elem:
  !ads a n.
   n < ads  ==>
    EL n (load_globals a ads) = LoadGlob (a + n2w n)
Proof
  Induct >> rw [] >> fs [load_globals_def] >>
  cases_on ‘n’ >> fs [] >> fs [n2w_SUC]
QED

Theorem evaluate_seq_stroes_locals_eq:
  !es ad a s res t.
   evaluate (nested_seq (stores ad es a),s) = (res,t) ==>
   t.locals = s.locals
Proof
  Induct >> rw []
  >- fs [stores_def, nested_seq_def, evaluate_def] >>
  fs [stores_def] >> FULL_CASE_TAC >> rveq >> fs [] >>
  fs [nested_seq_def, evaluate_def] >>
  pairarg_tac >> fs [] >> rveq >>
  every_case_tac >> fs [] >> rveq >>
  last_x_assum drule >>
  fs [panSemTheory.mem_store_def,state_component_equality]
QED

Theorem evaluate_seq_stores_mem_state_rel:
  !es vs ad a s res t addr m.
   LENGTH es = LENGTH vs /\ ~MEM ad es /\ ALL_DISTINCT es /\
   mem_stores (addr+a) vs s.memaddrs s.memory = SOME m /\
   evaluate (nested_seq (stores (Var ad) (MAP Var es) a),
             s with locals := s.locals |++
               ((ad,Word addr)::ZIP (es,vs))) = (res,t) ==>
   res = NONE ∧ t.memory = m ∧
   t.memaddrs = s.memaddrs ∧
   t.sh_memaddrs = s.sh_memaddrs ∧ (t.be ⇔ s.be) /\
   t.ffi = s.ffi ∧ t.code = s.code /\ t.clock = s.clock /\
   t.base_addr = s.base_addr /\
   t.top_addr = s.top_addr
Proof
  Induct >> rpt gen_tac >> strip_tac >> rfs [] >> rveq
  >- fs [stores_def, nested_seq_def, evaluate_def,
         mem_stores_def, state_component_equality] >>
  cases_on ‘vs’ >> fs [] >>
  fs [mem_stores_def, CaseEq "option"] >>
  qmatch_asmsub_abbrev_tac ‘s with locals := lc’ >>
  ‘eval (s with locals := lc) (Var h) = SOME h'’ by (
    fs [Abbr ‘lc’, eval_def] >>
    fs [FUPDATE_LIST_THM] >>
    ‘~MEM h (MAP FST (ZIP (es,t')))’ by (
      drule MAP_ZIP >>
      strip_tac >> fs []) >>
   drule FUPDATE_FUPDATE_LIST_COMMUTES >>
   disch_then (qspecl_then [‘h'’, ‘s.locals |+ (ad,Word addr)’] assume_tac) >>
   fs [FLOOKUP_UPDATE]) >>
  ‘lc |++ ((ad,Word addr)::ZIP (es,t')) = lc’ by (
    fs [Abbr ‘lc’] >> metis_tac [fm_multi_update]) >>
  fs [stores_def] >>
  FULL_CASE_TAC >> fs []
  >- (
   fs [nested_seq_def, evaluate_def] >>
   pairarg_tac >> fs [] >>
   ‘eval (s with locals := lc) (Var ad) = SOME (Word addr)’ by (
     fs [Abbr ‘lc’, eval_def] >>
     fs [Once FUPDATE_LIST_THM] >>
     ‘~MEM ad (MAP FST ((h,h')::ZIP (es,t')))’ by (
      drule MAP_ZIP >>
      strip_tac >> fs []) >>
    drule FUPDATE_FUPDATE_LIST_COMMUTES >>
    disch_then (qspecl_then [‘Word addr’, ‘s.locals’] assume_tac) >>
    fs [FLOOKUP_UPDATE]) >> fs [] >>
   rfs [] >> rveq >> fs [] >>
   last_x_assum (qspecl_then [‘t'’, ‘ad’, ‘bytes_in_word’] mp_tac) >> fs [] >>
   disch_then (qspec_then ‘s with <|locals := lc; memory := m'|>’ mp_tac) >> fs [] >>
   disch_then drule >> fs []) >>
  fs [nested_seq_def, evaluate_def] >>
  pairarg_tac >> fs [] >>
  ‘eval (s with locals := lc) (Op Add [Var ad; Const a]) = SOME (Word (addr+a))’ by (
    fs [eval_def, OPT_MMAP_def, Abbr ‘lc’] >>
    fs [Once FUPDATE_LIST_THM] >>
    ‘~MEM ad (MAP FST ((h,h')::ZIP (es,t')))’ by (
      drule MAP_ZIP >>
      strip_tac >> fs []) >>
    drule FUPDATE_FUPDATE_LIST_COMMUTES >>
    disch_then (qspecl_then [‘Word addr’, ‘s.locals’] assume_tac) >>
    fs [FLOOKUP_UPDATE, wordLangTheory.word_op_def]) >> fs [] >>
   rfs [] >> rveq >> fs [] >>
   pop_assum kall_tac >>
   pop_assum kall_tac >>
   last_x_assum (qspecl_then [‘t'’, ‘ad’, ‘a + bytes_in_word’] mp_tac) >> fs [] >>
   disch_then (qspec_then ‘s with <|locals := lc; memory := m'|>’ mp_tac) >> fs [] >>
   disch_then drule >> fs []
QED

Theorem evaluate_seq_store_globals_res:
  !vars vs t a.
   ALL_DISTINCT vars ∧ LENGTH vars = LENGTH vs ∧ w2n a + LENGTH vs <= 32 ==>
   evaluate (nested_seq (store_globals a (MAP Var vars)),
             t with locals := t.locals |++ ZIP (vars,vs)) =
   (NONE,t with <|locals := t.locals |++ ZIP (vars,vs);
                  globals := t.globals |++ ZIP (GENLIST (λx. a + n2w x) (LENGTH vs), vs)|>)
Proof
  Induct >> rw []
  >- fs [store_globals_def, nested_seq_def, evaluate_def,
         FUPDATE_LIST_THM, state_component_equality] >>
  cases_on ‘vs’ >> fs [] >>
  fs [store_globals_def, nested_seq_def, evaluate_def] >>
  pairarg_tac >> fs [] >>
  fs [eval_def, FUPDATE_LIST_THM] >>
  ‘~MEM h (MAP FST (ZIP (vars, t')))’ by
    metis_tac [MEM_MAP, MEM_ZIP,FST, MEM_EL] >>
  drule FUPDATE_FUPDATE_LIST_COMMUTES >>
  disch_then (qspecl_then [‘h'’, ‘t.locals’] assume_tac) >>
  fs [FLOOKUP_UPDATE] >> rveq >>
  fs [set_globals_def] >>
  cases_on ‘t' = []’
  >- (
   rveq >> fs [] >> rveq >>
   fs [store_globals_def, nested_seq_def, evaluate_def,
       FUPDATE_LIST_THM, state_component_equality]) >>
  qmatch_goalsub_abbrev_tac ‘nested_seq _, st’ >>
  last_x_assum (qspecl_then [‘t'’, ‘st’, ‘a + 1w’] mp_tac) >>
  fs [] >> impl_tac
  >- (
   fs [ADD1] >>
   qmatch_asmsub_abbrev_tac ‘m + (w2n a + 1) <= 32’ >>
   ‘0 < m’ by (fs [Abbr ‘m’] >> cases_on ‘t'’ >> fs []) >>
   ‘(w2n a + 1) <= 32 - m’ by DECIDE_TAC >>
   fs [w2n_plus1] >>
   FULL_CASE_TAC >>
   fs []) >>
  ‘st.locals |++ ZIP (vars,t') = st.locals’ by (
    fs [Abbr ‘st’] >>
    drule FUPDATE_FUPDATE_LIST_COMMUTES >>
    disch_then (qspecl_then [‘h'’, ‘t.locals |++ ZIP (vars,t')’] assume_tac) >>
    fs [] >> metis_tac [FUPDATE_LIST_CANCEL, MEM_ZIP]) >>
  fs [Abbr ‘st’]  >> fs [] >> strip_tac >> fs [state_component_equality] >>
  fs [GENLIST_CONS, FUPDATE_LIST_THM, o_DEF, n2w_SUC]
QED


Theorem res_var_lookup_original_eq:
  !xs ys lc. ALL_DISTINCT xs ∧ LENGTH xs = LENGTH ys ==>
   FOLDL res_var (lc |++ ZIP (xs,ys)) (ZIP (xs,MAP (FLOOKUP lc) xs)) = lc
Proof
  Induct >> rw [] >- fs [FUPDATE_LIST_THM] >>
  fs [] >> cases_on ‘ys’ >> fs [] >>
  fs [FUPDATE_LIST_THM] >>
  ‘~MEM h (MAP FST (ZIP (xs, t)))’ by
    metis_tac [MEM_MAP, MEM_ZIP,FST, MEM_EL] >>
  drule FUPDATE_FUPDATE_LIST_COMMUTES >>
  disch_then (qspecl_then [‘h'’, ‘lc’] mp_tac) >>
  fs [] >> strip_tac >>
  cases_on ‘FLOOKUP lc h’ >> fs [] >>
  fs [res_var_def] >>
  qpat_x_assum ‘~MEM h xs’ assume_tac
  >- (
   drule domsub_commutes_fupdate >>
   disch_then (qspecl_then [‘t’, ‘lc’] mp_tac) >>
   fs [] >>
   metis_tac [flookup_thm, DOMSUB_NOT_IN_DOM]) >>
  drule FUPDATE_FUPDATE_LIST_COMMUTES >>
  disch_then (qspecl_then [‘x’, ‘lc’] assume_tac o GSYM) >>
  fs [] >>
  metis_tac [FUPDATE_ELIM, flookup_thm]
QED

Theorem eval_exps_not_load_global_eq:
  !s e v g. eval s e = SOME v ∧
   (!ad. ~MEM (LoadGlob ad) (exps e))  ==>
    eval (s with globals := g) e = SOME v
Proof
  ho_match_mp_tac eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- fs [eval_def]
  >- fs [eval_def]
  >- (
   rpt gen_tac >>
   strip_tac >> fs [exps_def] >>
   fs [eval_def, CaseEq "option", CaseEq "word_lab"] >>
   rveq >> fs [mem_load_def] >> rveq >> metis_tac [])
  >- (
   rpt gen_tac >>
   strip_tac >> fs [exps_def] >>
   fs [eval_def, CaseEq "option", CaseEq "word_lab"] >>
   rveq >> fs [mem_load_def] >> rveq >> metis_tac [])
  >- (
   rpt gen_tac >>
   strip_tac >> fs [exps_def] >>
   fs [eval_def, CaseEq "option", CaseEq "word_lab"] >>
   rveq >> metis_tac [])
  >- fs [exps_def, eval_def, CaseEq "option"]
  >- (
   rpt gen_tac >>
   strip_tac >> fs [exps_def, ETA_AX] >>
   fs [eval_def, CaseEq "option", ETA_AX] >>
   qexists_tac ‘ws’ >>
   fs [opt_mmap_eq_some, ETA_AX,
       MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
   rw [] >>
   fs [MEM_FLAT, MEM_MAP] >>
   metis_tac [EL_MEM])
  >- (
   rpt gen_tac >>
   strip_tac >>
   gvs [exps_def, eval_def, AllCaseEqs(),opt_mmap_eq_some,SF DNF_ss,
        MAP_EQ_CONS,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
   first_x_assum $ irule_at $ Pos last >>
   simp[] >>
   gvs[MAP_EQ_EVERY2,LIST_REL_EL_EQN] >>
   metis_tac[EL_MEM]) >>
  rpt gen_tac >>
  rpt strip_tac >> fs [exps_def, ETA_AX] >>
  fs [eval_def, CaseEq "option", CaseEq "word_lab"] >>
  rveq >> metis_tac []
QED

Theorem load_glob_not_mem_load:
  !i a h ad.
  ~MEM (LoadGlob ad) (exps h) ==>
  ~MEM (LoadGlob ad) (FLAT (MAP exps (load_shape a i h)))
Proof
  Induct >> rw [] >- fs [load_shape_def] >>
  fs [load_shape_def] >>
  TOP_CASE_TAC >> fs [MAP, load_shape_def, exps_def]
QED

Theorem var_cexp_load_globals_empty:
  !ads a.
   FLAT (MAP var_cexp (load_globals a ads)) = []
Proof
  Induct >> rw [] >>
  fs [var_cexp_def, load_globals_def]
QED

Theorem evaluate_seq_assign_load_globals:
  !ns t a.
  ALL_DISTINCT ns /\ w2n a + LENGTH ns <= 32 /\
  (!n. MEM n ns ==> FLOOKUP t.locals n <> NONE) /\
  (!n. MEM n (GENLIST (λx. a + n2w x) (LENGTH ns)) ==> FLOOKUP t.globals n <> NONE) ==>
  evaluate (nested_seq (MAP2 Assign ns (load_globals a (LENGTH ns))), t) =
  (NONE, t with locals := t.locals |++
           ZIP (ns, MAP (\n. THE (FLOOKUP t.globals n)) (GENLIST (λx. a + n2w x) (LENGTH ns))))
Proof
  Induct >> rw []
  >- (
   fs [nested_seq_def, evaluate_def] >>
   fs [FUPDATE_LIST_THM, state_component_equality]) >>
  fs [nested_seq_def, GENLIST_CONS, load_globals_def] >>
  fs [evaluate_def] >> pairarg_tac >> fs [] >>
  fs [eval_def] >>
  cases_on ‘FLOOKUP t.globals a’
  >- (
   first_assum (qspec_then ‘a’ mp_tac) >>
   fs []) >>
  fs [] >>
  cases_on ‘FLOOKUP t.locals h’
  >- (
   first_assum (qspec_then ‘h’ mp_tac) >>
   fs []) >>
  fs [] >> rveq >>
  fs [FUPDATE_LIST_THM] >>
  last_x_assum (qspecl_then [‘t with locals := t.locals |+ (h,x)’, ‘a + 1w’] mp_tac) >>
  impl_tac
  >- (
   conj_tac
   >- (
    ‘w2n a <= 31 - LENGTH ns’ by fs [] >>
    cases_on ‘a = 31w:word5’ >> fs [] >>
    ‘w2n (a + 1w) = w2n a + 1’ by (
      fs [w2n_plus1] >>
      FULL_CASE_TAC >> fs []) >>
    fs []) >>
   conj_tac
   >- (
    rw [] >> fs [FLOOKUP_UPDATE] >>
    TOP_CASE_TAC >> fs []) >>
   rw [] >> fs [MEM_GENLIST] >>
   first_x_assum match_mp_tac >>
   disj2_tac >> fs [] >>
   qexists_tac ‘x''’ >> fs [] >>
   fs [n2w_SUC]) >>
  strip_tac >> fs [] >>
  fs [state_component_equality] >>
  ‘GENLIST (λx. a + n2w x + 1w) (LENGTH ns)=
   GENLIST ((λx. a + n2w x) ∘ SUC) (LENGTH ns)’
  suffices_by fs [] >>
  fs [GENLIST_FUN_EQ] >>
  rw [] >>
  fs [n2w_SUC]
QED

Theorem flookup_res_var_distinct_eq:
  !xs x fm.
  ~MEM x (MAP FST xs) ==>
  FLOOKUP (FOLDL res_var fm xs) x =
  FLOOKUP fm x
Proof
  Induct >> rw [] >>
  cases_on ‘h’ >> fs [] >>
  cases_on ‘r’ >> fs [res_var_def] >>
  fs [MEM_MAP]  >>
  metis_tac [DOMSUB_FLOOKUP_NEQ, FLOOKUP_UPDATE]
QED


Theorem flookup_res_var_distinct_zip_eq:
  LENGTH xs = LENGTH ys /\
  ~MEM x xs ==>
  FLOOKUP (FOLDL res_var fm (ZIP (xs,ys))) x =
  FLOOKUP fm x
Proof
  rw [] >>
  qmatch_goalsub_abbrev_tac `FOLDL res_var _ l` >>
  pop_assum(mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  rpt (pop_assum mp_tac) >>
  MAP_EVERY qid_spec_tac [`x`,`ys`,`xs`,`fm`, `l`] >>
  Induct >> rw [] >> rveq >>
  cases_on ‘xs’ >> cases_on ‘ys’ >> fs [ZIP] >>
  rveq >>
  cases_on ‘h''’ >> fs [res_var_def] >>
  fs [MEM_MAP]  >>
  metis_tac [DOMSUB_FLOOKUP_NEQ, FLOOKUP_UPDATE]
QED

Theorem flookup_res_var_distinct:
  !ys xs zs fm.
  distinct_lists xs ys /\
  LENGTH xs = LENGTH zs ==>
  MAP (FLOOKUP (FOLDL res_var fm (ZIP (xs,zs)))) ys =
  MAP (FLOOKUP fm) ys
Proof
  Induct
  >- rw[MAP] >> rw []
  >- (
   fs [pan_commonTheory.distinct_lists_def, EVERY_MEM, FUPDATE_LIST_THM] >>
   ‘~MEM h xs’ by metis_tac [] >>
   drule flookup_res_var_distinct_zip_eq >>
   disch_then (qspecl_then [‘h’,‘fm’] mp_tac) >>
   fs [] >>
   strip_tac >> fs [] >>
   metis_tac [flookup_fupdate_zip_not_mem]) >>
  fs [FUPDATE_LIST_THM] >>
  drule distinct_lists_simp_cons >>
  strip_tac >>
  first_x_assum drule >>
  disch_then (qspec_then ‘zs’ mp_tac) >> fs []
QED

Theorem flookup_res_var_zip_distinct:
  !ys xs as cs fm.
   distinct_lists xs ys /\
   LENGTH xs = LENGTH as /\
   LENGTH xs = LENGTH cs ==>
    MAP (FLOOKUP (FOLDL res_var (fm |++ ZIP (xs,as)) (ZIP (xs,cs)))) ys =
    MAP (FLOOKUP fm) ys
Proof
  rw [] >>
  drule flookup_res_var_distinct >>
  disch_then (qspecl_then [‘cs’,‘fm |++ ZIP (xs,as)’] mp_tac) >>
  fs [] >>
  metis_tac [map_flookup_fupdate_zip_not_mem]
QED

Theorem eval_some_var_cexp_local_lookup:
  ∀s e v n. eval s e = SOME v /\ MEM n (var_cexp e) ==>
    ?w. FLOOKUP s.locals n = SOME w
Proof
  ho_match_mp_tac eval_ind >> rw [] >>
  gvs [var_cexp_def,MEM_FLAT,MEM_MAP,eval_def,AllCaseEqs(),opt_mmap_eq_some,
       MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  first_x_assum irule >>
  ntac 2 $ first_assum $ irule_at $ Pos last >>
  gvs[MEM_EL]
QED


Theorem eval_upd_clock_eq:
  !t e ck. eval (t with clock := ck) e =  eval t e
Proof
  ho_match_mp_tac eval_ind >> rw [] >>
  fs [eval_def]
  >- (
   every_case_tac >> fs [] >>
   fs [mem_load_def]) >>
  qsuff_tac ‘OPT_MMAP (λa. eval (t with clock := ck) a) es =
             OPT_MMAP (λa. eval t a) es’ >>
  fs [] >>
  pop_assum mp_tac >>
  qid_spec_tac ‘es’ >>
  Induct >> rw [] >>
  fs [OPT_MMAP_def]
QED

Theorem opt_mmap_eval_upd_clock_eq:
   !es s ck. OPT_MMAP (eval (s with clock := ck + s.clock)) es =
   OPT_MMAP (eval s) es
Proof
  rw [] >>
  match_mp_tac IMP_OPT_MMAP_EQ >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  rw [] >>
  metis_tac [eval_upd_clock_eq]
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
  fs [evaluate_def, AllCaseEqs ()] >> rveq >>
  fs [eval_upd_clock_eq]) >>
  TRY (
  rename [‘ExtCall’] >>
  fs [evaluate_def, AllCaseEqs ()] >> rveq >> fs []) >>
  TRY (
  rename [‘While’] >>
  qpat_x_assum ‘evaluate (While _ _,_) = _’ mp_tac >>
  once_rewrite_tac [evaluate_def] >>
  fs [eval_upd_clock_eq] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >> rveq >> fs [] >>
  TOP_CASE_TAC >> fs [] >> rveq >> fs []
  >- (
   strip_tac >> fs [] >>
   TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
   fs [dec_clock_def] >>
   last_x_assum (qspec_then ‘ck’ mp_tac) >>
   fs []) >>
  TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
  strip_tac >> fs [] >> rveq >> fs [dec_clock_def] >>
  first_x_assum (qspec_then ‘ck’ mp_tac) >>
  fs []) >>
  TRY (
  rename [‘Call’] >>
  qpat_x_assum ‘evaluate (Call _ _ _,_) = _’ mp_tac >>
  once_rewrite_tac [evaluate_def] >>
  fs [dec_clock_def, eval_upd_clock_eq] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  ‘OPT_MMAP (eval (s with clock := ck + s.clock)) argexps =
   OPT_MMAP (eval s) argexps’ by fs [opt_mmap_eval_upd_clock_eq] >>
  fs [] >>
  fs [AllCaseEqs(), empty_locals_def, dec_clock_def] >> rveq >> fs [] >>
  strip_tac >> fs [] >> rveq >> fs []) >>
  TRY (
  rename [‘Dec’] >>
  fs [evaluate_def, eval_upd_clock_eq, AllCaseEqs () ] >>
  pairarg_tac >> fs [] >> rveq >> fs [] >>
  pairarg_tac >> fs [] >> rveq >> fs [] >>
  last_x_assum (qspec_then ‘ck’ mp_tac) >>
  fs []) >>
  fs [evaluate_def, eval_upd_clock_eq, AllCaseEqs () ,
      set_var_def, mem_store_def, set_globals_def,
      dec_clock_def, empty_locals_def] >> rveq >>
  fs [state_component_equality]>>
  (Cases_on ‘op’>>fs[sh_mem_op_def,sh_mem_load_def,sh_mem_store_def]>>
   every_case_tac>>fs[set_var_def,empty_locals_def]>>rveq>>fs[])
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
    rename [‘ExtCall’] >>
    fs [evaluate_def, AllCaseEqs(), empty_locals_def,
        dec_clock_def, ffiTheory.call_FFI_def] >>
    rveq >> fs []) >>
  TRY (
    rename [‘If’] >>
    fs [evaluate_def] >>
    every_case_tac >> fs []) >>
  TRY (
    rename [‘While’] >>
    qpat_x_assum ‘evaluate (While _ _,_) = _’ mp_tac >>
    once_rewrite_tac [evaluate_def] >>
    TOP_CASE_TAC >> fs [] >>
    TOP_CASE_TAC >> fs [] >>
    TOP_CASE_TAC >> fs [] >>
    TOP_CASE_TAC >> fs [empty_locals_def]
    >- (strip_tac >> rveq >> fs []) >>
    pairarg_tac >> fs [] >>
    TOP_CASE_TAC >> fs [] >> rveq >> fs []
    >- (
      strip_tac >> fs [] >>
      fs [dec_clock_def] >>
      metis_tac [IS_PREFIX_TRANS]) >>
    TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
    strip_tac >> fs [] >> rveq >> fs [dec_clock_def] >>
    metis_tac [IS_PREFIX_TRANS]) >>
  TRY (
    rename [‘Call’] >>
    pop_assum mp_tac >>
    once_rewrite_tac [evaluate_def, LET_THM] >>
    fs [AllCaseEqs(), empty_locals_def,
        dec_clock_def, set_var_def] >>
    strip_tac >> fs [] >> rveq >> fs [] >>
    metis_tac [IS_PREFIX_TRANS]) >>
  TRY (
    rename [‘Dec’] >>
    fs [evaluate_def, AllCaseEqs () ] >>
    pairarg_tac >> fs [] >> rveq >> fs []) >>
  fs [evaluate_def, eval_upd_clock_eq, AllCaseEqs () ,
      set_var_def, mem_store_def, set_globals_def,
      dec_clock_def, empty_locals_def] >> rveq >>
  fs [state_component_equality]>>
  (Cases_on ‘op’>>
   fs[sh_mem_op_def,sh_mem_load_def,sh_mem_store_def,
      ffiTheory.call_FFI_def,eval_upd_clock_eq]>>
   every_case_tac>>fs[set_var_def,empty_locals_def]>>rveq>>fs[])
QED

Theorem evaluate_add_clock_io_events_mono:
   ∀exps s extra.
    (SND(evaluate(exps,s))).ffi.io_events ≼
    (SND(evaluate(exps,s with clock := s.clock + extra))).ffi.io_events
Proof
  recInduct evaluate_ind >>
  rw []
  >~ [‘While’]
  >- (once_rewrite_tac [evaluate_def] >>
      TOP_CASE_TAC >> fs [eval_upd_clock_eq] >>
      TOP_CASE_TAC >> fs [] >>
      TOP_CASE_TAC >> fs [] >>
      TOP_CASE_TAC >> fs [empty_locals_def]
      >- (
       TOP_CASE_TAC >> fs [] >> rveq >>
       fs [dec_clock_def] >>
       pairarg_tac >> fs [] >>
       TOP_CASE_TAC >> fs [] >>
       TRY (cases_on ‘x’) >> fs [] >>
       TRY (cases_on ‘evaluate (While e c,s1)’) >> fs [] >>
       imp_res_tac evaluate_io_events_mono >> fs [] >>
       metis_tac [IS_PREFIX_TRANS]) >>
      pairarg_tac >> fs [] >> rveq >>
      pairarg_tac >> fs [] >> rveq >>
      fs [dec_clock_def] >>
      cases_on ‘res’ >> fs []
      >- (
       pop_assum mp_tac >>
       drule evaluate_add_clock_eq >>
       fs [] >>
       disch_then (qspec_then ‘extra’ mp_tac) >>
       fs [] >>
       strip_tac >> strip_tac >> rveq >> fs []) >>
      cases_on ‘x = Continue’ >> fs []
      >- (
       pop_assum mp_tac >>
       pop_assum mp_tac >>
       drule evaluate_add_clock_eq >>
       fs [] >>
       disch_then (qspec_then ‘extra’ mp_tac) >>
       fs [] >>
       strip_tac >> strip_tac >> strip_tac >> rveq >> fs []) >>
      cases_on ‘x = TimeOut’ >> rveq >> fs []
      >- (
       TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
       TRY (cases_on ‘x’) >> fs [] >> rveq >> fs [] >>
       first_x_assum (qspec_then ‘extra’ mp_tac) >>
       fs [] >> strip_tac >>
       cases_on ‘evaluate (While e c,s1')’ >> fs [] >>
       drule evaluate_io_events_mono >>
       strip_tac >>
       metis_tac [IS_PREFIX_TRANS]) >>
      TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
      drule evaluate_add_clock_eq >>
      fs [] >>
      disch_then (qspec_then ‘extra’ mp_tac) >>
      fs [] >>
      strip_tac >> strip_tac >> strip_tac >> rveq >> fs [])
  >~ [‘Seq’]
  >- (fs [evaluate_def] >>
      pairarg_tac >> fs [] >> rveq >>
      pairarg_tac >> fs [] >> rveq >>
      every_case_tac >> fs [] >> rveq >> fs []
      >- (
       pop_assum mp_tac >>
       drule evaluate_add_clock_eq >>
       disch_then (qspec_then ‘extra’ mp_tac) >>
       fs [] >>
       strip_tac >>
       strip_tac >> rveq >> fs [])
      >- (
       pop_assum mp_tac >>
       pop_assum mp_tac >>
       drule evaluate_add_clock_eq >>
       disch_then (qspec_then ‘extra’ mp_tac) >>
       fs [])
      >- (
       first_x_assum (qspec_then ‘extra’ mp_tac) >>
       strip_tac >>
       ‘s1.ffi.io_events ≼ s1'.ffi.io_events’ by rfs [] >>
       cases_on ‘evaluate (c2,s1')’ >>
       fs [] >>
       ‘s1'.ffi.io_events ≼ r.ffi.io_events’ by
         metis_tac [evaluate_io_events_mono] >>
       metis_tac [IS_PREFIX_TRANS]) >>
      first_x_assum (qspec_then ‘extra’ mp_tac) >>
      fs [])
  >~ [‘If’]
  >- (fs [evaluate_def, AllCaseEqs()] >> rveq >> fs [] >>
      every_case_tac >> fs [eval_upd_clock_eq])
  >~ [‘Call’]
  >- (once_rewrite_tac [evaluate_def, LET_THM] >>
      fs [eval_upd_clock_eq, opt_mmap_eval_upd_clock_eq] >>
      TOP_CASE_TAC >> fs [] >>
      TOP_CASE_TAC >> fs [] >>
      TOP_CASE_TAC >> fs [] >>
      TOP_CASE_TAC >> fs [] >>
      TOP_CASE_TAC >> fs [empty_locals_def]
      >- (
       every_case_tac >> fs [dec_clock_def, empty_locals_def] >>
       rveq >> fs [] >>
       imp_res_tac evaluate_io_events_mono >>
       fs [] >>
       TRY (rename1 ‘evaluate (p,s' with locals := s.locals)’>>
            cases_on ‘evaluate (p,s' with locals := s.locals)’) >> fs [] >>
       TRY (rename1 ‘evaluate (p,s' with locals := s.locals |+ (x',w))’>>
            cases_on ‘evaluate (p,s' with locals := s.locals |+ (x',w))’) >> fs [] >>
       imp_res_tac evaluate_io_events_mono >>
       fs [] >> metis_tac [IS_PREFIX_TRANS]) >>
      fs [dec_clock_def] >>
      TOP_CASE_TAC >> gvs []
      >- (
       first_x_assum (qspec_then ‘extra’ mp_tac) >>
       strip_tac >> fs [] >>
       TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
       TOP_CASE_TAC >> gvs[] >>
       TOP_CASE_TAC >> gvs[]
       >- (
         TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
         TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
         TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
         TOP_CASE_TAC >> fs [] >> rveq >> fs []
         >- (
           rename1 ‘evaluate (p,r'' with locals := s.locals)’ >>
           cases_on ‘evaluate (p,r'' with locals := s.locals)’ >>
           fs [] >>
           imp_res_tac evaluate_io_events_mono >>
           fs [] >> metis_tac [IS_PREFIX_TRANS]) >>
         TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
         rename1 ‘evaluate (p,r'' with locals := s.locals |+ (x',w))’ >>
         cases_on ‘evaluate (p,r'' with locals := s.locals |+ (x',w))’ >>
         fs [] >>
         imp_res_tac evaluate_io_events_mono >>
         fs [] >> metis_tac [IS_PREFIX_TRANS]) >>
       every_case_tac >> fs [] >> rveq >> fs [] >>
       rename1 ‘evaluate (p,r'' with locals := s.locals)’ >>
       cases_on ‘evaluate (p,r'' with locals := s.locals)’ >>
       fs [] >>
       imp_res_tac evaluate_io_events_mono >>
       fs [] >> metis_tac [IS_PREFIX_TRANS]) >>
      TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
      TRY (drule evaluate_add_clock_eq >> fs [] >> NO_TAC)
      >- (
       TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
       TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
       TRY (cases_on ‘x'’) >> fs [] >> rveq >> fs [] >>
       TRY (
         first_x_assum (qspec_then ‘extra’ mp_tac) >>
         strip_tac >> fs [] >>
         cases_on ‘evaluate (q,s with <|locals := r;
                                        clock := extra + s.clock - 1|>)’ >>
         fs [] >> rveq >> fs [] >> NO_TAC)
       >- (
         every_case_tac >> fs [] >> rveq >> fs [] >>
         first_x_assum (qspec_then ‘extra’ mp_tac) >>
         strip_tac >> fs [] >> rfs []
         >- (
           rename1 ‘evaluate (p,r'' with locals := s.locals)’ >>
           cases_on ‘evaluate (p,r'' with locals := s.locals)’ >>
           imp_res_tac evaluate_io_events_mono >>
           fs [] >> metis_tac [IS_PREFIX_TRANS]) >>
         rename1 ‘evaluate (p,r'' with locals := s.locals |+ (x',w))’ >>
         cases_on ‘evaluate (p,r'' with locals := s.locals |+ (x',w))’ >>
         imp_res_tac evaluate_io_events_mono >>
         fs [] >> metis_tac [IS_PREFIX_TRANS]) >>
       every_case_tac >> fs [] >> rveq >> fs [] >>
       first_x_assum (qspec_then ‘extra’ mp_tac) >>
       strip_tac >> fs [] >> rfs [] >>
       rename1 ‘evaluate (p,r'' with locals := s.locals)’ >>
       cases_on ‘evaluate (p,r'' with locals := s.locals)’ >>
       imp_res_tac evaluate_io_events_mono >>
       fs [] >> metis_tac [IS_PREFIX_TRANS])
      >- (
       TOP_CASE_TAC >> fs [] >> rveq >> fs []
       >- (
         first_x_assum (qspec_then ‘extra’ mp_tac) >>
         strip_tac >> fs [] >>
         rename1 ‘evaluate (q,s with <|locals := r; clock := extra + s.clock - 1|>)’ >>
         cases_on ‘evaluate (q,s with <|locals := r; clock := extra + s.clock - 1|>)’ >>
         fs [] >>
         TOP_CASE_TAC >> fs [] >>
         TOP_CASE_TAC >> fs [] >> rveq >> fs [])
       >- (
         TOP_CASE_TAC >> fs [] >> rveq >> fs []>>
         TOP_CASE_TAC >> fs [] >> rveq >> fs []>>
         TOP_CASE_TAC >> fs [] >> rveq >> fs []
         >- (drule evaluate_add_clock_eq >> fs []) >>
         TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
         drule evaluate_add_clock_eq >> fs []) >>
       drule evaluate_add_clock_eq >> fs []) >> (* ? *)
      TOP_CASE_TAC >> fs [] >> rveq >> fs []
      >- (
       first_x_assum (qspec_then ‘extra’ mp_tac) >>
       strip_tac >> fs [] >>
       cases_on ‘evaluate (q,s with <|locals := r; clock := extra + s.clock - 1|>)’ >>
       fs [] >>
       TOP_CASE_TAC >> fs [] >>
       TOP_CASE_TAC >> fs [] >> rveq >> fs []) >>
      TOP_CASE_TAC >> fs [] >> rveq >> fs []>>
      TOP_CASE_TAC >> fs [] >> rveq >> fs []>>
      TOP_CASE_TAC >> fs [] >> rveq >> fs []
      >- (
       first_x_assum (qspec_then ‘extra’ mp_tac) >>
       strip_tac >> fs [] >>
       cases_on ‘evaluate (q,s with <|locals := r; clock := extra + s.clock - 1|>)’ >>
       fs [] >>
       TOP_CASE_TAC >> fs [] >>
       TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
       pop_assum mp_tac >>
       drule evaluate_add_clock_eq >> fs []) >>
      TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
      TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
      drule evaluate_add_clock_eq >> fs [])
  >~ [‘Dec’]
  >- (fs [evaluate_def] >>
      fs [eval_upd_clock_eq] >>
      TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
      pairarg_tac >> fs [] >> rveq >> fs [] >>
      pairarg_tac >> fs [] >> rveq >> fs [] >>
      last_x_assum (qspec_then ‘extra’ mp_tac) >>
      fs [])
  >~ [‘ExtCall’]
  >- (fs [evaluate_def, eval_upd_clock_eq] >>
      every_case_tac >> fs [])
  >~ [‘ShMem’]
  >- (Cases_on ‘op’>>
      fs [evaluate_def, eval_upd_clock_eq] >>
      fs[sh_mem_op_def,sh_mem_load_def,sh_mem_store_def,
         ffiTheory.call_FFI_def,eval_upd_clock_eq]>>
      every_case_tac>>fs[set_var_def,empty_locals_def]>>rveq>>fs[]) >>
  fs [evaluate_def, eval_upd_clock_eq] >>
  every_case_tac >> fs [] >>
  fs [set_var_def, mem_store_def, set_globals_def,
      dec_clock_def, empty_locals_def] >> rveq >>
  fs []
QED

Theorem evaluate_code_invariant:
  ∀p t res st.
    crepSem$evaluate (p,t) = (res,st) ⇒
    st.code = t.code
Proof
  recInduct crepSemTheory.evaluate_ind >> rw[]
  >~ [‘While’]
  >- (pop_assum mp_tac >>
      rw[Once crepSemTheory.evaluate_def] >>
      gvs[AllCaseEqs(),crepSemTheory.empty_locals_def,UNCURRY_eq_pair,
          crepSemTheory.dec_clock_def])
  >~ [‘Call’]
  >- (pop_assum mp_tac >>
      rw[Once crepSemTheory.evaluate_def] >>
      rfs[AllCaseEqs(),crepSemTheory.empty_locals_def,
          crepSemTheory.dec_clock_def] >>
      rveq >>
      fs[]) >>
  gvs[crepSemTheory.evaluate_def,AllCaseEqs(),
      oneline crepSemTheory.sh_mem_op_def,
      oneline crepSemTheory.sh_mem_load_def,
      oneline crepSemTheory.sh_mem_store_def,
      crepSemTheory.set_var_def,
      crepSemTheory.empty_locals_def,
      UNCURRY_eq_pair,
      crepSemTheory.dec_clock_def,
      crepSemTheory.set_globals_def
     ]
QED

Definition exps_of_def:
  (exps_of (Dec _ e p) = e::exps_of p) ∧
  (exps_of (Seq p q) = exps_of p ++ exps_of q) ∧
  (exps_of (If e p q) = e::exps_of p ++ exps_of q) ∧
  (exps_of (While e p) = e::exps_of p) ∧
  (exps_of (Call NONE e es) = es) ∧
  (exps_of (Call (SOME (_,p,NONE)) e es) = es++exps_of p) ∧
  (exps_of (Call (SOME (_,p,SOME(_,p'))) e es) = es++exps_of p++exps_of p') ∧
  (exps_of (Store e1 e2) = [e1;e2]) ∧
  (exps_of (Store32 e1 e2) = [e1;e2]) ∧
  (exps_of (StoreByte e1 e2) = [e1;e2]) ∧
  (exps_of (StoreGlob _ e) = [e]) ∧
  (exps_of (Return e) = [e]) ∧
  (exps_of (Assign _ e) = [e]) ∧
  (exps_of (ShMem _ _ e) = [e]) ∧
  (exps_of _ = [])
End

Definition every_exp_def:
  (every_exp P (crepLang$Const w) = P(Const w)) ∧
  (every_exp P (Var v) = P(Var v)) ∧
  (every_exp P (Load e) = (P(Load e) ∧ every_exp P e)) ∧
  (every_exp P (Load32 e) = (P(Load32 e) ∧ every_exp P e)) ∧
  (every_exp P (LoadByte e) = (P(LoadByte e) ∧ every_exp P e)) ∧
  (every_exp P (LoadGlob w) = (P(LoadGlob w))) ∧
  (every_exp P (Op bop es) = (P(Op bop es) ∧ EVERY (every_exp P) es)) ∧
  (every_exp P (Crepop op es) = (P(Crepop op es) ∧ EVERY (every_exp P) es)) ∧
  (every_exp P (Cmp c e1 e2) = (P(Cmp c e1 e2) ∧ every_exp P e1 ∧ every_exp P e2)) ∧
  (every_exp P (Shift sh e num) = (P(Shift sh e num) ∧ every_exp P e)) ∧
  (every_exp P (BaseAddr) = P BaseAddr) ∧
  (every_exp P (TopAddr) = P TopAddr)
Termination
  wf_rel_tac `measure (exp_size ARB o SND)` >>
  rpt strip_tac >>
  imp_res_tac MEM_IMP_exp_size >>
  TRY (first_x_assum (assume_tac o Q.SPEC `ARB`)) >>
  decide_tac
End
