(*
  crepLang Properties
*)

open preamble
     panSemTheory panPropsTheory
     crepLangTheory crepSemTheory
     pan_commonTheory pan_commonPropsTheory;

val _ = new_theory"crepProps";

val _ = set_grammar_ancestry ["panProps", "crepLang","crepSem", "pan_commonProps"];

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
  ho_match_mp_tac eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (fs [eval_def])
  >- fs [eval_def, var_cexp_def, FLOOKUP_UPDATE]
  >- fs [eval_def]
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
   rpt gen_tac >>
   strip_tac >> fs [var_cexp_def, ETA_AX] >>
   fs [eval_def, CaseEq "option", ETA_AX] >>
   qexists_tac ‘ws’ >>
   fs [opt_mmap_eq_some, ETA_AX,
       MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
   rw [] >>
   fs [MEM_FLAT, MEM_MAP] >>
   metis_tac [EL_MEM]) >>
  rpt gen_tac >>
  strip_tac >> fs [var_cexp_def, ETA_AX] >>
  fs [eval_def, CaseEq "option", CaseEq "word_lab"] >>
  rveq >> metis_tac []
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

Theorem unassigned_vars_evaluate_same:
  !p s res t n.
   evaluate (p,s) = (res,t) /\
   (res = NONE ∨ res = SOME Continue ∨ res = SOME Break) /\
    ~MEM n (assigned_vars p) ==>
  FLOOKUP t.locals n = FLOOKUP s.locals n
Proof
  recInduct evaluate_ind >> rw [] >> fs [] >>
  TRY (
  rename1 ‘While _ _’ >>
  qpat_x_assum ‘evaluate (While _ _,_) = (_,_)’ mp_tac >>
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
   fs [assigned_vars_def] >>
   first_x_assum drule >>
   fs [dec_clock_def]) >>
  FULL_CASE_TAC >> fs [] >>
  fs [assigned_vars_def] >>
  first_x_assum drule >>
  fs [dec_clock_def] >> NO_TAC) >>
  TRY
  (fs [evaluate_def, assigned_vars_def, CaseEq "option", CaseEq "word_lab",
       set_globals_def, state_component_equality] >>
   TRY (pairarg_tac) >> rveq >> fs [] >> rveq >>
   FULL_CASE_TAC >> metis_tac [] >>
   NO_TAC) >>
  TRY
  (fs [evaluate_def, assigned_vars_def] >> fs [CaseEq "option"] >>
   pairarg_tac >> fs [] >> rveq >>
   first_x_assum drule  >>
   fs [state_component_equality, FLOOKUP_UPDATE] >>
   metis_tac [flookup_res_var_diff_eq] >> NO_TAC) >>
  TRY
  (fs [evaluate_def, assigned_vars_def] >> fs [CaseEq "option", CaseEq "word_lab"] >>
   rveq >> fs [state_component_equality, FLOOKUP_UPDATE] >>
   fs [panSemTheory.mem_store_def, state_component_equality] >> NO_TAC) >>
  TRY
  (cases_on ‘caltyp’ >>
   fs [evaluate_def, assigned_vars_def, CaseEq "option",  CaseEq "ret", CaseEq "word_lab"]  >>
   rveq >> cases_on ‘v6’ >> fs[] >>
   every_case_tac >> fs [set_var_def, state_component_equality, assigned_vars_def] >>
   TRY (qpat_x_assum ‘s.locals |+ (_,_) = t.locals’ (mp_tac o GSYM) >>
        fs [FLOOKUP_UPDATE] >> NO_TAC) >>
   res_tac >> fs [FLOOKUP_UPDATE] >> NO_TAC) >>
  TRY
  (fs [evaluate_def, assigned_vars_def] >> fs [CaseEq "option"] >>
   pairarg_tac >> fs [] >> rveq >>
   FULL_CASE_TAC >>
   metis_tac [] >> NO_TAC) >>
  fs [evaluate_def, assigned_vars_def, dec_clock_def, CaseEq "option",
      CaseEq "word_lab", CaseEq "ffi_result"]  >>
  rveq >> TRY (FULL_CASE_TAC) >>fs [state_component_equality]
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


Theorem nested_seq_assigned_vars_eq:
  !ns vs.
  LENGTH ns = LENGTH vs ==>
  assigned_vars (nested_seq (MAP2 Assign ns vs)) = ns
Proof
  Induct >> rw [] >- fs [nested_seq_def, assigned_vars_def] >>
  cases_on ‘vs’ >> fs [nested_seq_def, assigned_vars_def]
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

Theorem assigned_vars_store_globals_empty:
  !es ad.
  assigned_vars (nested_seq (store_globals ad es)) =  []
Proof
  Induct >> rw [] >>
  fs [store_globals_def, assigned_vars_def, nested_seq_def] >>
  fs [store_globals_def, assigned_vars_def, nested_seq_def]
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
   t.memaddrs = s.memaddrs ∧ (t.be ⇔ s.be) ∧ (t.eids = s.eids) /\
   t.ffi = s.ffi ∧ t.code = s.code /\ t.clock = s.clock
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
   metis_tac [EL_MEM]) >>
  rpt gen_tac >>
  strip_tac >> fs [exps_def, ETA_AX] >>
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
  TRY (fs [eval_def, var_cexp_def] >> NO_TAC) >>
  TRY (
  fs [eval_def, var_cexp_def] >>
  FULL_CASE_TAC >> fs [] >> NO_TAC)
  >- (
   fs [var_cexp_def, ETA_AX] >>
   fs [eval_def] >>
   FULL_CASE_TAC >> fs [ETA_AX] >> rveq >>
   pop_assum kall_tac >> pop_assum kall_tac >>
   rpt (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac [`n`,`x`,`s`, `es`] >>
   Induct >- rw [] >>
   rpt gen_tac >>
   rpt strip_tac >>
   fs [OPT_MMAP_def] >> rveq >> fs [] >>
   last_x_assum (qspecl_then [‘s’, ‘t’, ‘n’] mp_tac) >>
   fs [] >>
   impl_tac >- metis_tac [] >>
   fs []) >>
  fs [var_cexp_def, eval_def] >>
  every_case_tac >> fs []
QED


Theorem eval_label_eq_state_contains_label:
  !s e w f. eval s e = SOME w /\ w = Label f ==>
   (?v. FLOOKUP s.locals v = SOME (Label f)) ∨
   (?n args. FLOOKUP s.code f = SOME (n,args)) ∨
   (?ad. s.memory ad = Label f) ∨
   (?gadr. FLOOKUP s.globals gadr = SOME (Label f))
Proof
  ho_match_mp_tac eval_ind >> rw [] >>
  fs [eval_def, mem_load_def, AllCaseEqs ()] >> fs [] >> rveq >>
  TRY (cases_on ‘v1’) >>
  metis_tac []
QED


val _ = export_theory();
