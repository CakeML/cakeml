(*
  panLang Properties
*)

open preamble
     panLangTheory panSemTheory
     pan_commonPropsTheory;

val _ = new_theory"panProps";

val _ = set_grammar_ancestry ["panLang","panSem", "pan_commonProps"];


Definition v2word_def:
  v2word (ValWord v) = Word v
End

Theorem length_flatten_eq_size_of_shape:
  !v.
   LENGTH (flatten v) = size_of_shape (shape_of v)
Proof
  ho_match_mp_tac flatten_ind >> rw []
  >- (cases_on ‘w’ >> fs [shape_of_def, flatten_def, size_of_shape_def]) >>
  fs [shape_of_def, flatten_def, size_of_shape_def] >>
  fs [LENGTH_FLAT, MAP_MAP_o] >> fs[SUM_MAP_FOLDL] >>
  match_mp_tac FOLDL_CONG >> fs []
QED

Theorem mem_load_some_shape_eq:
  ∀sh adr dm (m: 'a word -> 'a word_lab) v.
  mem_load sh adr dm m = SOME v ==>
  shape_of v = sh
Proof
  qsuff_tac ‘(∀sh adr dm (m: 'a word -> 'a word_lab) v.
  mem_load sh adr dm m = SOME v ==> shape_of v = sh) /\
  (∀sh adr dm (m: 'a word -> 'a word_lab) v.
   mem_loads sh adr dm m = SOME v ==> MAP shape_of v = sh)’
  >- metis_tac [] >>
  ho_match_mp_tac mem_load_ind >> rw [mem_load_def] >>
  cases_on ‘sh’ >> fs [option_case_eq] >>
  rveq >> TRY (cases_on ‘m adr’) >> fs [shape_of_def] >>
  metis_tac []
QED


Theorem flookup_res_var_some_eq_lookup:
  FLOOKUP (res_var lc (v,FLOOKUP lc' v)) v = SOME value ==>
  FLOOKUP lc' v = SOME value
Proof
  rw [] >> cases_on ‘FLOOKUP lc' v’ >>
  fs [res_var_def, FLOOKUP_UPDATE]
QED

Theorem flookup_res_var_diff_eq_org:
  n <> m ==>
  FLOOKUP (res_var lc (n,v)) m = FLOOKUP lc m
Proof
  rw [] >> cases_on ‘v’ >>
  fs [res_var_def, FLOOKUP_UPDATE, DOMSUB_FLOOKUP_NEQ]
QED

Theorem FLOOKUP_pan_res_var_thm:
  FLOOKUP (panSem$res_var l (m,v)) n = if n = m then v else FLOOKUP l n
Proof
  simp[oneline panSemTheory.res_var_def] >>
  PURE_FULL_CASE_TAC >>
  rw[DOMSUB_FLOOKUP_THM,FLOOKUP_UPDATE]
QED

Theorem list_rel_length_shape_of_flatten:
  !vshs args.
  LIST_REL (λvsh arg. SND vsh = shape_of arg) vshs args ==>
  size_of_shape (Comb (MAP SND vshs)) = LENGTH (FLAT (MAP flatten args))
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (cases_on ‘args’ >> fs [size_of_shape_def]) >>
  cases_on ‘args’ >> fs [] >> rveq >>
  fs [size_of_shape_def] >>
  last_x_assum (qspecl_then [‘t’] mp_tac) >>
  fs [] >> last_x_assum (assume_tac o GSYM) >>
  fs [] >>
  fs [length_flatten_eq_size_of_shape]
QED


Theorem length_with_shape_eq_shape:
  !sh ns.
  LENGTH ns = size_of_shape (Comb sh) ==>
  LENGTH sh = LENGTH (with_shape sh ns)
Proof
  Induct >> rw [] >>
  fs [with_shape_def] >>
  fs [size_of_shape_def]
QED


Theorem fdoms_eq_flookup_some_none:
  !fm fm' n v v'. FDOM fm =  FDOM fm' /\
  FLOOKUP fm n = SOME v ==>  ?v. FLOOKUP fm' n = SOME v
Proof
  rw [] >>
  fs [flookup_thm] >> rveq >> fs [] >>
  rfs []
QED


Theorem all_distinct_with_shape:
  !sh ns n.
  ALL_DISTINCT ns /\ n < LENGTH sh /\
  LENGTH ns = size_of_shape (Comb sh) ==>
  ALL_DISTINCT (EL n (with_shape sh ns))
Proof
  Induct >> rw [] >>
  fs [with_shape_def] >>
  cases_on ‘n’ >> fs []
  >- (
   fs [size_of_shape_def] >>
   ‘size_of_shape h <= LENGTH ns’ by DECIDE_TAC >>
   drule all_distinct_take >> fs []) >>
  last_x_assum (qspecl_then [‘DROP (size_of_shape h) ns’, ‘n'’] mp_tac) >>
  impl_tac
  >- (
   fs [size_of_shape_def] >>
   ‘size_of_shape h <= LENGTH ns’ by DECIDE_TAC >>
   drule all_distinct_drop >> fs []) >> fs []
QED

Theorem el_mem_with_shape:
  !sh ns n x.
  n < LENGTH (with_shape sh ns) /\
  LENGTH ns = size_of_shape (Comb sh) /\
  MEM x (EL n (with_shape sh ns)) ==>
  MEM x ns
Proof
  Induct >> rw [] >>
  fs [with_shape_def] >>
  cases_on ‘n’ >> fs []
  >- (
   fs [size_of_shape_def] >>
   ‘size_of_shape h <= LENGTH ns’ by DECIDE_TAC >> drule MEM_TAKE >> fs []) >>
  fs [size_of_shape_def] >>
  last_x_assum (qspecl_then [‘DROP (size_of_shape h) ns’, ‘n'’, ‘x’] mp_tac) >>
  fs [] >>
  strip_tac >> drule MEM_DROP_IMP >>
  fs []
QED


Theorem mem_with_shape_length:
  !sh ns n.
   LENGTH ns = size_of_shape (Comb sh) ∧ n < LENGTH sh ==>
   MEM (EL n (with_shape sh ns)) (with_shape sh ns)
Proof
  Induct >> rw [] >>
  cases_on ‘n’ >> fs [] >>
  fs [with_shape_def] >>
  disj2_tac >>
  first_x_assum match_mp_tac >>
  fs [size_of_shape_def]
QED

Theorem with_shape_el_take_drop_eq:
 !sh ns n.
   LENGTH ns = size_of_shape (Comb sh) ∧
    n < LENGTH sh ==>
    EL n (with_shape sh ns) =
    TAKE (size_of_shape (EL n sh)) (DROP (size_of_shape (Comb (TAKE n sh))) ns)
Proof
  Induct >> rw [] >>
  cases_on ‘n’ >> fs []
  >- fs [with_shape_def, size_of_shape_def] >>
  fs [with_shape_def, size_of_shape_def] >>
  last_x_assum (qspecl_then [‘DROP (size_of_shape h) ns’, ‘n'’] mp_tac) >>
  impl_tac >- fs [] >>
  strip_tac >> fs [DROP_DROP_T]
QED

Theorem all_distinct_with_shape_distinct:
  !sh ns x y.
   ALL_DISTINCT ns ∧ LENGTH ns = size_of_shape (Comb sh) ∧
   MEM x (with_shape sh ns) ∧ MEM y (with_shape sh ns) ∧ x <> y ∧
   x <> [] ∧ y <> [] ==>
   DISJOINT (set x) (set y)
Proof
  Induct >> rw [] >>
  fs [with_shape_def]
  >- (
   cases_on ‘size_of_shape h = 0’ >> fs [] >>
   ‘x = y’ suffices_by fs [] >>
   ‘size_of_shape h <= LENGTH ns’ by
     fs [size_of_shape_def] >>
   qpat_x_assum ‘x ≠ y’ kall_tac >>
   fs [TAKE])
  >- (
   fs [MEM_EL] >>
   ‘EL n (with_shape sh (DROP (size_of_shape h) ns)) =
    TAKE (size_of_shape (EL n sh)) (DROP (size_of_shape (Comb (TAKE n sh)))
                                    (DROP (size_of_shape h) ns))’ by (
     match_mp_tac with_shape_el_take_drop_eq >>
     fs [size_of_shape_def] >>
     ‘LENGTH (DROP (size_of_shape h) ns) = size_of_shape (Comb sh)’ by
       fs [size_of_shape_def] >>
     drule length_with_shape_eq_shape >> fs []) >>
   fs [] >>
   fs [DROP_DROP_T, DROP_TAKE] >>
   match_mp_tac disjoint_take_drop_sum >>
   fs [])
  >- (
   fs [MEM_EL] >>
   ‘EL n (with_shape sh (DROP (size_of_shape h) ns)) =
    TAKE (size_of_shape (EL n sh)) (DROP (size_of_shape (Comb (TAKE n sh)))
                                    (DROP (size_of_shape h) ns))’ by (
     match_mp_tac with_shape_el_take_drop_eq >>
     fs [size_of_shape_def] >>
     ‘LENGTH (DROP (size_of_shape h) ns) = size_of_shape (Comb sh)’ by
       fs [size_of_shape_def] >>
     drule length_with_shape_eq_shape >> fs []) >>
   fs [] >>
   fs [DROP_DROP_T, DROP_TAKE] >>
   match_mp_tac disjoint_drop_take_sum >>
   fs []) >>
  last_x_assum (qspec_then ‘DROP (size_of_shape h) ns’ mp_tac) >>
  disch_then (qspecl_then [‘x’,‘y’] mp_tac) >>
  impl_tac
  >- fs [ALL_DISTINCT_DROP, size_of_shape_def] >>
  fs []
QED


Theorem all_distinct_disjoint_with_shape:
  !sh ns n n'.
   ALL_DISTINCT ns /\ n < LENGTH sh /\ n' < LENGTH sh /\
   n <> n' /\
   LENGTH ns = size_of_shape (Comb sh) ==>
   DISJOINT (set (EL n (with_shape sh ns))) (set (EL n' (with_shape sh ns)))
Proof
  Induct >> rw [] >>
  fs [with_shape_def] >>
  cases_on ‘n’ >> cases_on ‘n'’ >> fs []
  >- (
   fs [MEM_EL] >>
   ‘EL n (with_shape sh (DROP (size_of_shape h) ns)) =
    TAKE (size_of_shape (EL n sh)) (DROP (size_of_shape (Comb (TAKE n sh)))
                                    (DROP (size_of_shape h) ns))’ by (
     match_mp_tac with_shape_el_take_drop_eq >>
     fs [size_of_shape_def] >>
     ‘LENGTH (DROP (size_of_shape h) ns) = size_of_shape (Comb sh)’ by
       fs [size_of_shape_def] >>
     drule length_with_shape_eq_shape >> fs []) >>
   fs [] >>
   fs [DROP_DROP_T, DROP_TAKE] >>
   match_mp_tac disjoint_take_drop_sum >>
   fs [])
  >- (
   fs [MEM_EL] >>
   ‘EL n'' (with_shape sh (DROP (size_of_shape h) ns)) =
    TAKE (size_of_shape (EL n'' sh)) (DROP (size_of_shape (Comb (TAKE n'' sh)))
                                    (DROP (size_of_shape h) ns))’ by (
     match_mp_tac with_shape_el_take_drop_eq >>
     fs [size_of_shape_def] >>
     ‘LENGTH (DROP (size_of_shape h) ns) = size_of_shape (Comb sh)’ by
       fs [size_of_shape_def] >>
     drule length_with_shape_eq_shape >> fs []) >>
   fs [] >>
   fs [DROP_DROP_T, DROP_TAKE] >>
   match_mp_tac disjoint_drop_take_sum >>
   fs []) >>
  last_x_assum match_mp_tac >>
  fs [size_of_shape_def, ALL_DISTINCT_DROP]
QED


Theorem all_distinct_mem_zip_disjoint_with_shape:
  LENGTH l = LENGTH sh /\ LENGTH sh = LENGTH (with_shape sh ns) /\
  ALL_DISTINCT ns /\ LENGTH ns = size_of_shape (Comb sh) /\
  MEM (x,a,xs) (ZIP (l,ZIP (sh,with_shape sh ns))) /\
  MEM (y,b,ys) (ZIP (l,ZIP (sh,with_shape sh ns))) /\
  x ≠ y ==>
   DISJOINT (set xs) (set ys)
Proof
  rw [] >>
  ‘LENGTH l = LENGTH (ZIP (sh,with_shape sh ns))’ by fs [] >>
  drule MEM_ZIP >>
  disch_then (qspec_then ‘(x,a,xs)’ assume_tac) >>
  drule MEM_ZIP >>
  disch_then (qspec_then ‘(y,b,ys)’ assume_tac) >>
  fs [] >> rveq >>
  cases_on ‘n = n'’ >> fs [] >>
  drule EL_ZIP >> drule EL_ZIP >>
  disch_then (qspec_then ‘n’ assume_tac) >>
  disch_then (qspec_then ‘n'’ assume_tac) >>
  rfs [] >> rveq >> fs [] >>
  match_mp_tac all_distinct_disjoint_with_shape >>
  fs []
QED

Theorem all_distinct_alist_no_overlap:
  ALL_DISTINCT (ns:num list) /\
  LENGTH ns = size_of_shape (Comb sh) ∧
  LENGTH vs = LENGTH sh ⇒
  no_overlap (alist_to_fmap (ZIP (vs,ZIP (sh,with_shape sh ns))))
Proof
  rw [] >>
  fs [no_overlap_def] >>
  conj_tac
  >- (
   rw [] >>
   drule ALOOKUP_MEM >>
   strip_tac >> fs [] >>
   drule length_with_shape_eq_shape >>
   strip_tac >>
   drule LENGTH_ZIP >>
   strip_tac >> fs [] >>
   ‘LENGTH vs = LENGTH (ZIP (sh,with_shape sh ns))’ by fs [] >>
   drule MEM_ZIP >>
   disch_then (qspec_then ‘(x,a,xs)’ mp_tac) >>
   strip_tac >> fs [] >> rveq >>
   ‘LENGTH sh = LENGTH (with_shape sh ns)’ by fs [] >>
   drule EL_ZIP >>
   disch_then (qspec_then ‘n’ mp_tac) >>
   impl_tac >- fs [] >>
   strip_tac >> fs [] >>
   match_mp_tac all_distinct_with_shape >>
   fs []) >>
  rw [] >>
  CCONTR_TAC >> fs [] >>
  dxrule ALOOKUP_MEM >>
  dxrule ALOOKUP_MEM >>
  rpt strip_tac >>
  drule length_with_shape_eq_shape >>
  strip_tac >>
  drule length_with_shape_eq_shape >>
  drule (INST_TYPE [``:'b``|->``:num``] all_distinct_mem_zip_disjoint_with_shape) >>
  disch_then (qspecl_then [‘ys’, ‘y’, ‘xs’, ‘x’, ‘ns’, ‘b’, ‘a’] assume_tac) >>
  rfs []
QED

Theorem all_distinct_alist_ctxt_max:
  ALL_DISTINCT (ns:num list) /\
  LENGTH ns = size_of_shape (Comb sh) ∧
  LENGTH vs = LENGTH sh ⇒
   ctxt_max (list_max ns)
      (alist_to_fmap (ZIP (vs,ZIP (sh,with_shape sh ns))))
Proof
  rw [] >> fs [ctxt_max_def] >>
  rw [] >>
  ‘MEM x ns’ suffices_by (
             assume_tac list_max_max >>
             pop_assum (qspec_then ‘ns’ assume_tac) >>
             fs [EVERY_MEM]) >>
  drule ALOOKUP_MEM >>
  strip_tac >>
  drule length_with_shape_eq_shape >>
  strip_tac >>
  drule LENGTH_ZIP >>
  strip_tac >> fs [] >>
  ‘LENGTH vs = LENGTH (ZIP (sh,with_shape sh ns))’ by fs [] >>
  drule MEM_ZIP >>
  disch_then (qspec_then ‘(v,a,xs)’ mp_tac) >>
  strip_tac >> fs [] >>
  rveq >> ‘LENGTH sh = LENGTH (with_shape sh ns)’ by fs [] >>
  drule EL_ZIP >>
  disch_then (qspec_then ‘n’ mp_tac) >>
  impl_tac >- fs [] >>
  strip_tac >> fs [] >> rveq >>
  drule el_mem_with_shape >>
  fs []
QED

Theorem list_rel_flatten_with_shape_length:
  !sh ns args v n.
  LENGTH ns = LENGTH (FLAT (MAP flatten args))/\
  size_of_shape (Comb sh) = LENGTH (FLAT (MAP flatten args)) /\
  EL n args = v /\ n < LENGTH args /\ LENGTH args = LENGTH sh /\
  LIST_REL (λsh arg. sh = shape_of arg) sh args ==>
  LENGTH (EL n (with_shape sh ns)) = LENGTH (flatten v)
Proof
  Induct >> rw []
  >- fs [with_shape_def, size_of_shape_def] >>
  fs [with_shape_def, size_of_shape_def] >>
  cases_on ‘n’ >> fs []
  >-  fs [length_flatten_eq_size_of_shape] >>
  last_x_assum match_mp_tac >>
  ‘LENGTH (flatten arg) = size_of_shape (shape_of arg)’ by
    fs [length_flatten_eq_size_of_shape] >>
  fs []
QED

Theorem list_rel_flatten_with_shape_flookup:
  !sh ns args v n n'.
  ALL_DISTINCT ns ∧ LENGTH ns = LENGTH (FLAT (MAP flatten args)) /\
  size_of_shape (Comb sh) = LENGTH (FLAT (MAP flatten args)) /\
  EL n args = v /\ n < LENGTH args /\ LENGTH args = LENGTH sh /\
  LIST_REL (λsh arg. sh = shape_of arg) sh args /\
  LENGTH (EL n (with_shape sh ns)) = LENGTH (flatten v) /\
  n' < LENGTH (EL n (with_shape sh ns)) ==>
   FLOOKUP (FEMPTY |++ ZIP (ns,FLAT (MAP flatten args)))
     (EL n' (EL n (with_shape sh ns))) =
   SOME (EL n' (flatten v))
Proof
  Induct >> rw []
  >- fs [with_shape_def, size_of_shape_def] >>
  fs [with_shape_def, size_of_shape_def] >>
  cases_on ‘n’ >> fs []
  >- (
   ‘FLOOKUP (FEMPTY |++ ZIP (ns,flatten arg ++ FLAT (MAP flatten ys)))
    (EL n' (TAKE (size_of_shape (shape_of arg)) ns)) =
    SOME (EL n' (flatten arg ++ FLAT (MAP flatten ys)))’ by (
     ‘size_of_shape (shape_of arg) = LENGTH (flatten arg)’ by
       fs [length_flatten_eq_size_of_shape] >>
     fs [] >>
     ‘EL n' (flatten arg ++ FLAT (MAP flatten ys)) = EL n' (flatten arg)’ by (
       match_mp_tac EL_APPEND1 >> fs []) >>
     fs [] >>
     ‘FEMPTY |++ ZIP (TAKE (LENGTH (flatten arg)) ns ++ DROP (LENGTH (flatten arg)) ns,
                      flatten arg ++ FLAT (MAP flatten ys)) =
      FEMPTY |++ ZIP (TAKE (LENGTH (flatten arg)) ns,flatten arg) |++
      ZIP (DROP (LENGTH (flatten arg)) ns,FLAT (MAP flatten ys))’ by (
       drule ZIP_APPEND >>
       disch_then (qspecl_then [‘DROP (LENGTH (flatten arg)) ns’, ‘FLAT (MAP flatten ys)’]mp_tac) >>
       impl_tac >- fs [] >>
       strip_tac >> pop_assum (assume_tac o GSYM) >>
       fs [] >>
       fs [FUPDATE_LIST_APPEND]) >>
     fs [] >> pop_assum kall_tac >>
     ‘FEMPTY |++ ZIP (TAKE (LENGTH (flatten arg)) ns,flatten arg) |++
      ZIP (DROP (LENGTH (flatten arg)) ns,FLAT (MAP flatten ys)) =
      FEMPTY  |++
      ZIP (DROP (LENGTH (flatten arg)) ns,FLAT (MAP flatten ys)) |++
      ZIP (TAKE (LENGTH (flatten arg)) ns,flatten arg)’ by (
       match_mp_tac FUPDATE_LIST_APPEND_COMMUTES >>
       fs [MAP_ZIP] >> match_mp_tac all_distinct_take_frop_disjoint >> fs []) >>
     fs [] >> pop_assum kall_tac >>
     match_mp_tac update_eq_zip_flookup >>
     fs [] >>
     match_mp_tac all_distinct_take >>
     fs []) >>
   fs [] >>
   pop_assum kall_tac >>
   metis_tac [EL_APPEND1]) >>
  ‘FLOOKUP (FEMPTY |++ ZIP (ns,flatten arg ++ FLAT (MAP flatten ys)))
    (EL n'
     (EL n'' (with_shape sh (DROP (size_of_shape (shape_of arg)) ns))))  =
    FLOOKUP (FEMPTY |++ ZIP (DROP (size_of_shape (shape_of arg)) ns,FLAT (MAP flatten ys)))
    (EL n'
     (EL n'' (with_shape sh (DROP (size_of_shape (shape_of arg)) ns))))’ by (
    ‘FEMPTY |++ ZIP (ns,flatten arg ++ FLAT (MAP flatten ys)) =
     FEMPTY  |++
     ZIP (TAKE (LENGTH (flatten arg)) ns,flatten arg) |++
     ZIP (DROP (LENGTH (flatten arg)) ns,FLAT (MAP flatten ys))’ by (
      match_mp_tac fm_zip_append_take_drop >>
      fs []) >>
    fs [] >> pop_assum kall_tac >>
    ‘FLOOKUP
     (FEMPTY |++ ZIP (TAKE (LENGTH (flatten arg)) ns,flatten arg))
     (EL n'
      (EL n'' (with_shape sh (DROP (size_of_shape (shape_of arg)) ns)))) = NONE’ by (
      match_mp_tac not_mem_fst_zip_flookup_empty >>
      fs [] >> drule all_distinct_take >> disch_then (qspec_then ‘LENGTH (flatten arg)’ assume_tac) >>
      fs [] >>
      CCONTR_TAC >> fs [] >>
      fs [GSYM length_flatten_eq_size_of_shape] >>
      ‘TAKE (LENGTH (flatten arg)) ns =
       EL 0 (with_shape (shape_of arg::sh) ns)’ by
        fs [with_shape_def, length_flatten_eq_size_of_shape] >>
      ‘EL n'' (with_shape sh (DROP (LENGTH (flatten arg)) ns)) =
       EL (SUC n'') (with_shape (shape_of arg::sh) ns)’ by
        fs [with_shape_def, length_flatten_eq_size_of_shape] >>
      drule all_distinct_disjoint_with_shape >>
      disch_then (qspecl_then [‘shape_of arg::sh’, ‘SUC n''’, ‘0’] mp_tac) >>
      impl_tac >- fs [length_flatten_eq_size_of_shape, size_of_shape_def] >>
      strip_tac >> fs [] >> drule disjoint_not_mem_el >> metis_tac []) >>
    drule fupdate_flookup_zip_elim >>
    disch_then (qspecl_then [‘DROP (LENGTH (flatten arg)) ns’, ‘FLAT (MAP flatten ys)’] mp_tac) >>
    impl_tac >- (fs [] >> match_mp_tac all_distinct_take >> fs []) >>
    fs [] >> strip_tac >>
    fs [length_flatten_eq_size_of_shape]) >>
  fs [] >>
  pop_assum kall_tac >>
  last_x_assum (qspecl_then [‘DROP (size_of_shape (shape_of arg)) ns’,
                             ‘ys’, ‘n''’, ‘n'’] mp_tac) >>
  impl_tac >-  fs [ALL_DISTINCT_DROP, GSYM length_flatten_eq_size_of_shape] >> fs []
QED

Theorem eval_upd_clock_eq:
  !t e ck. eval (t with clock := ck) e =  eval t e
Proof
  ho_match_mp_tac eval_ind >> rw [] >>
  fs [eval_def] >>
  qsuff_tac ‘OPT_MMAP (λa. eval (t with clock := ck) a) es =
             OPT_MMAP (λa. eval t a) es’ >>
  fs [] >>
  pop_assum mp_tac >>
   qid_spec_tac ‘es’ >>
   Induct >> rw [] >>
   fs [OPT_MMAP_def]
QED

Theorem eval_upd_code_eq:
  !t e code. eval (t with code := code) e =  eval t e
Proof
  ho_match_mp_tac eval_ind >> rw [] >>
  fs [eval_def] >>
  qsuff_tac ‘OPT_MMAP (λa. eval (t with code := code) a) es =
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


Theorem opt_mmap_eval_upd_clock_eq1:
   !es s ck. OPT_MMAP (eval (s with clock := ck)) es =
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
  recInduct evaluate_ind >> rw []
  >~ [‘While’]
  >- (once_rewrite_tac [evaluate_def] >>
      qpat_x_assum ‘evaluate _ = _’ mp_tac >>
      rw[Once evaluate_def] >>
      gvs[eval_upd_clock_eq,AllCaseEqs()] >>
      rpt(pairarg_tac >> gvs[]) >>
      gvs[AllCaseEqs(),dec_clock_def]) >>
  gvs[evaluate_def,AllCaseEqs(),eval_upd_clock_eq] >>
  rpt(pairarg_tac >> gvs[]) >>
  gvs[oneline nb_op_def,AllCaseEqs(),
      oneline sh_mem_load_def,
      oneline sh_mem_store_def,
      set_var_def,
      set_global_def,
      empty_locals_def,
      dec_clock_def,
      opt_mmap_eval_upd_clock_eq,
      lookup_kvar_def,
      set_kvar_def
     ] >>
  PURE_TOP_CASE_TAC >> gvs[]
QED

Theorem evaluate_clock_sub:
  !p t res st ck.
    evaluate (p,t) = (res,st with clock := st.clock + ck) ∧
    res <> SOME TimeOut ⇒
    evaluate (p,t with clock := t.clock - ck) = (res,st)
Proof
  (* TODO: generated names *)
  recInduct evaluate_ind >> rw []
  >~ [‘While’]
  >- (once_rewrite_tac [evaluate_def] >>
      qpat_x_assum ‘evaluate _ = _’ mp_tac >>
      rw[Once evaluate_def] >>
      gvs[eval_upd_clock_eq,AllCaseEqs()] >>
      rpt(pairarg_tac >> gvs[]) >>
      gvs[AllCaseEqs(),dec_clock_def] >>
      imp_res_tac evaluate_clock >>
      gvs[] >>
      rw[state_component_equality] >>
      first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
      rw[] >>
      last_x_assum $ qspecl_then [‘s1' with clock := s1'.clock - ck’,‘ck’] mp_tac >>
      (impl_tac >- rw[state_component_equality]) >>
      strip_tac >>
      gvs[])
  >~ [‘Seq’]
  >- (once_rewrite_tac [evaluate_def] >>
      qpat_x_assum ‘evaluate _ = _’ mp_tac >>
      rw[Once evaluate_def] >>
      gvs[eval_upd_clock_eq,AllCaseEqs()] >>
      rpt(pairarg_tac >> gvs[]) >>
      gvs[AllCaseEqs(),dec_clock_def] >>
      imp_res_tac evaluate_clock >>
      gvs[] >>
      rw[state_component_equality] >>
      first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
      rw[] >>
      last_x_assum $ qspecl_then [‘s1' with clock := s1'.clock - ck’,‘ck’] mp_tac >>
      (impl_tac >- rw[state_component_equality]) >>
      strip_tac >>
      gvs[])
  >~ [‘Dec’]
  >- (once_rewrite_tac [evaluate_def] >>
      qpat_x_assum ‘evaluate _ = _’ mp_tac >>
      rw[Once evaluate_def] >>
      gvs[eval_upd_clock_eq,AllCaseEqs()] >>
      rpt(pairarg_tac >> gvs[]) >>
      gvs[AllCaseEqs(),dec_clock_def] >>
      imp_res_tac evaluate_clock >>
      gvs[]
      >- rw[state_component_equality] >>
      last_x_assum $ qspecl_then [‘st'' with clock := st''.clock - ck’,‘ck’] mp_tac >>
      (impl_tac >- gvs[state_component_equality]) >>
      strip_tac >>
      gvs[state_component_equality])
  >~ [‘Call’]
  >- (gvs[evaluate_def,AllCaseEqs(),eval_upd_clock_eq,opt_mmap_eval_upd_clock_eq1,dec_clock_def,
         empty_locals_def,set_var_def,set_kvar_def,set_global_def] >>
      imp_res_tac evaluate_clock >>
      gvs[empty_locals_def] >>
      TRY $ first_x_assum $ irule_at $ Pat ‘evaluate _ = _’ >>
      gvs[state_component_equality,PULL_EXISTS] >>
      TRY $ first_x_assum $ irule_at $ Pat ‘evaluate _ = _’ >>
      rw[] >>
      qrefine ‘_ with <|globals := (_:('a,'b) state).globals;
                        locals := (_:('a,'b) state).locals|>’ >>
      rw[] >>
      gvs[] >>
      metis_tac[]
     )
  >~ [‘DecCall’]
  >- (gvs[evaluate_def,AllCaseEqs(),eval_upd_clock_eq,opt_mmap_eval_upd_clock_eq1,dec_clock_def,
         empty_locals_def,set_var_def] >>
      rpt(pairarg_tac >> gvs[]) >>
      imp_res_tac evaluate_clock >>
      gvs[empty_locals_def] >>
      TRY $ first_x_assum $ irule_at $ Pat ‘evaluate _ = _’ >>
      gvs[state_component_equality] >>
      TRY $ first_x_assum $ irule_at $ Pat ‘evaluate _ = _’ >>
      rw[]
      >~ [‘UNCURRY’]
      >- (qexists_tac ‘st' with clock := st'.clock - ck’ >>
          simp[] >>
          last_x_assum $ qspec_then ‘st with <|locals := st''.locals|>’ $ dep_rewrite.DEP_ONCE_REWRITE_TAC o single >>
          simp[] >>
          rw[state_component_equality]) >>
      qrefine ‘_ with locals := (_:('a,'b) state).locals’ >>
      rw[] >>
      gvs[] >>
      metis_tac[]) >>
  gvs[evaluate_def,state_component_equality,AllCaseEqs(),eval_upd_clock_eq,
      oneline nb_op_def,oneline sh_mem_load_def,
      oneline sh_mem_store_def, set_var_def, empty_locals_def,
      dec_clock_def,opt_mmap_eval_upd_clock_eq1,
      set_global_def, lookup_kvar_def, set_kvar_def
     ] >>
  rpt(pairarg_tac >> gvs[]) >>
  gvs[state_component_equality]
QED

Theorem evaluate_io_events_mono:
   !exps s1 res s2.
    evaluate (exps,s1) = (res, s2)
    ⇒
    s1.ffi.io_events ≼ s2.ffi.io_events
Proof
  recInduct evaluate_ind >>
  rw []
  >~ [‘While’]
  >- (pop_assum mp_tac >>
      simp[Once evaluate_def] >> strip_tac >>
      gvs[AllCaseEqs(),empty_locals_def] >>
      rpt(pairarg_tac >> gvs[]) >>
      gvs[AllCaseEqs(),dec_clock_def] >>
      imp_res_tac IS_PREFIX_TRANS) >>
  gvs[evaluate_def,AllCaseEqs(),
      oneline nb_op_def,oneline sh_mem_load_def,
      oneline sh_mem_store_def, set_var_def, empty_locals_def,
      set_global_def,lookup_kvar_def,set_kvar_def,
      dec_clock_def,opt_mmap_eval_upd_clock_eq1,
      ffiTheory.call_FFI_def] >>
  rpt(pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs()] >>
  imp_res_tac IS_PREFIX_TRANS
QED

Theorem evaluate_add_clock_io_events_mono:
   ∀exps s extra.
    (SND(evaluate(exps,s))).ffi.io_events ≼
    (SND(evaluate(exps,s with clock := s.clock + extra))).ffi.io_events
Proof
  ‘∀exps s extra res s'.
     evaluate(exps,s) = (res,s') ⇒
     s'.ffi.io_events ≼ (SND(evaluate(exps,s with clock := s.clock + extra))).ffi.io_events’
    suffices_by metis_tac [FST,SND,PAIR] >>
  recInduct evaluate_ind >>
  rw []
  >~ [‘While’]
  >- (simp[Once evaluate_def] >>
      pop_assum mp_tac >>
      simp[Once evaluate_def] >>
      strip_tac >>
      gvs[AllCaseEqs(),
          eval_upd_clock_eq,
          empty_locals_def,
          dec_clock_def]
      >- (IF_CASES_TAC >> gvs[] >>
          pairarg_tac >>
          gvs[] >>
          rpt(PURE_TOP_CASE_TAC >> gvs[]) >>
          metis_tac[FST,SND,PAIR,evaluate_io_events_mono,IS_PREFIX_TRANS,
                    Q.prove(‘(x with clock := y).ffi = x.ffi’,simp[])]) >>
      rpt(pairarg_tac >> gvs[]) >>
      gvs[AllCaseEqs()]
      >~ [‘evaluate _ = (SOME TimeOut, _)’]
      >- (rpt(PURE_TOP_CASE_TAC >> gvs[]) >>
          metis_tac[FST,SND,PAIR,evaluate_io_events_mono,IS_PREFIX_TRANS,
                    Q.prove(‘(x with clock := y).ffi = x.ffi’,simp[])]) >>
      qpat_x_assum ‘evaluate (_,_ with <|clock := _.clock − 1|>) = _’ assume_tac >>
      drule_then (qspec_then ‘extra’ assume_tac) evaluate_add_clock_eq >>
      gvs[])
  >~ [‘Seq’]
  >- (gvs[evaluate_def,AllCaseEqs(),
          oneline nb_op_def,oneline sh_mem_load_def,
          oneline sh_mem_store_def, set_var_def, empty_locals_def,
          dec_clock_def,opt_mmap_eval_upd_clock_eq1,
          eval_upd_clock_eq,ffiTheory.call_FFI_def] >>
      rpt(pairarg_tac >> gvs[]) >>
      gvs[AllCaseEqs()]
      >- (drule_then (qspec_then ‘extra’ assume_tac) evaluate_add_clock_eq >>
          gvs[]) >>
      rw[] >>
      metis_tac[FST,SND,PAIR,evaluate_io_events_mono,IS_PREFIX_TRANS])
  >~ [‘Call’]
  >- (gvs[evaluate_def,AllCaseEqs(),
          oneline nb_op_def,oneline sh_mem_load_def,
          oneline sh_mem_store_def, set_var_def, empty_locals_def,
          set_kvar_def, set_global_def,
          dec_clock_def,opt_mmap_eval_upd_clock_eq1,
          eval_upd_clock_eq,ffiTheory.call_FFI_def] >>
      rpt(pairarg_tac >> gvs[]) >>
      gvs[AllCaseEqs()] >>
      rw[] >>
      rpt(IF_CASES_TAC ORELSE PURE_TOP_CASE_TAC >> gvs[]) >>
      imp_res_tac evaluate_io_events_mono >> gvs[] >>
      TRY(qpat_x_assum ‘evaluate (_,_ with <|locals := _; clock := _.clock − 1|>) = _’ assume_tac >>
          drule_then (qspec_then ‘extra’ assume_tac) evaluate_add_clock_eq >>
          gvs[]) >>
      metis_tac[FST,SND,PAIR,evaluate_io_events_mono,IS_PREFIX_TRANS,
                Q.prove(‘(x with locals := y).ffi = x.ffi’,simp[])])
  >~ [‘DecCall’]
  >- (gvs[evaluate_def,AllCaseEqs(),
          oneline nb_op_def,oneline sh_mem_load_def,
          oneline sh_mem_store_def, set_var_def, empty_locals_def,
          dec_clock_def,opt_mmap_eval_upd_clock_eq1,
          eval_upd_clock_eq,ffiTheory.call_FFI_def] >>
      rpt(pairarg_tac >> gvs[]) >>
      gvs[AllCaseEqs()] >>
      rw[] >>
      rpt(IF_CASES_TAC ORELSE PURE_TOP_CASE_TAC >> gvs[]) >>
      imp_res_tac evaluate_io_events_mono >> gvs[] >>
      rpt(pairarg_tac >> gvs[]) >>
      TRY(qpat_x_assum ‘evaluate (_,_ with <|locals := _; clock := _.clock − 1|>) = _’ assume_tac >>
          drule_then (qspec_then ‘extra’ assume_tac) evaluate_add_clock_eq >>
          gvs[]) >>
      metis_tac[FST,SND,PAIR,evaluate_io_events_mono,IS_PREFIX_TRANS,
                Q.prove(‘(x with locals := y).ffi = x.ffi’,simp[])]
     ) >>
  gvs[evaluate_def,AllCaseEqs(),
      oneline nb_op_def,oneline sh_mem_load_def,
      oneline sh_mem_store_def, set_var_def, empty_locals_def,
      set_global_def,lookup_kvar_def,set_kvar_def,
      dec_clock_def,opt_mmap_eval_upd_clock_eq1,
      eval_upd_clock_eq,ffiTheory.call_FFI_def] >>
  rpt(pairarg_tac >> gvs[]) >>
  rw[] >>
  gvs[AllCaseEqs()] >>
  metis_tac[FST,SND,PAIR,IS_PREFIX_TRANS]
QED

Theorem update_locals_not_vars_eval_eq:
  ∀s e v n w.
  ~MEM n (var_exp e) /\
  eval s e = SOME v ==>
  eval (s with locals := s.locals |+ (n,w)) e = SOME v
Proof
  ho_match_mp_tac eval_ind >>
  rpt conj_tac >> rpt gen_tac
  >~ [‘Struct’]
  >- (fs [var_exp_def] >>
      rpt strip_tac >>
      gvs[eval_def,AllCaseEqs()] >>
      imp_res_tac opt_mmap_el >>
      imp_res_tac opt_mmap_length_eq >>
      gvs[opt_mmap_eq_some] >>
      irule LIST_EQ >>
      rw[EL_MAP] >>
      first_x_assum irule >>
      simp[MEM_EL,PULL_EXISTS] >>
      irule_at (Pos last) EQ_REFL >>
      simp[] >>
      rw[] >>
      gvs[MEM_FLAT,MEM_MAP,MEM_EL,PULL_FORALL, SF DNF_ss] >>
      metis_tac[]) >>
  rw[] >>
  gvs[eval_def,var_exp_def, lookup_kvar_def, FLOOKUP_UPDATE,AllCaseEqs(),
      PULL_EXISTS] >>
  ntac 2 $ first_assum $ irule_at $ Pos last >>
  imp_res_tac opt_mmap_el >>
  imp_res_tac opt_mmap_length_eq >>
  gvs[opt_mmap_eq_some] >>
  irule LIST_EQ >>
  rw[EL_MAP] >>
  first_x_assum irule >>
  simp[MEM_EL,PULL_EXISTS] >>
  irule_at (Pos last) EQ_REFL >>
  simp[] >>
  rw[] >>
  gvs[MEM_FLAT,MEM_MAP,MEM_EL,PULL_FORALL, SF DNF_ss] >>
  metis_tac[]
QED

Theorem write_bytearray_update_byte:
  ∀bytes ad ad' m adrs be.
    byte_aligned ad ∧
    (∃w. m ad = Word w) ⇒
    ∃w.
      write_bytearray ad' bytes m adrs be
                      ad = Word w
Proof
  Induct >>
  rw [] >>
  gs [panSemTheory.write_bytearray_def] >>
  TOP_CASE_TAC >> gs [] >>
  gs [mem_store_byte_def] >>
  every_case_tac >> gs [] >>
  rveq >> gs [] >>
  gs [byte_align_aligned] >>
  fs [APPLY_UPDATE_THM] >>
  every_case_tac >> gs [] >>
  fs [APPLY_UPDATE_THM]
QED

Theorem evaluate_clock_sub1:
  !p t res st t' ck.
    evaluate (p,t) = (res,st) /\ res <> SOME TimeOut ∧
    evaluate (p,t with clock := ck + t.clock) =
    evaluate (p,t') ⇒
    evaluate (p,t) = evaluate (p,t' with clock := t'.clock - ck)
Proof
  rw [] >> gs [] >>
  last_x_assum assume_tac >>
  drule evaluate_add_clock_eq >>
  disch_then (qspec_then ‘ck’ mp_tac) >>
  gs [] >>
  strip_tac >>
  qpat_x_assum ‘_ = evaluate (p,t')’ kall_tac >>
  once_rewrite_tac [EQ_SYM_EQ] >>
  match_mp_tac evaluate_clock_sub >>
  gs []
QED

Theorem evaluate_invariants:
  ∀p t res st.
  evaluate (p,t) = (res,st) ⇒
  st.memaddrs = t.memaddrs ∧ st.sh_memaddrs = t.sh_memaddrs ∧
  st.be = t.be ∧ st.eshapes = t.eshapes ∧ st.base_addr = t.base_addr ∧
  st.code = t.code
Proof
  Ho_Rewrite.PURE_REWRITE_TAC[FORALL_AND_THM,IMP_CONJ_THM] >> rpt conj_tac >>
  recInduct evaluate_ind >>
    (rw[Once evaluate_def]
     >~ [‘While’]
     >- (qpat_x_assum ‘evaluate _ = _’ (strip_assume_tac o ONCE_REWRITE_RULE[evaluate_def]) >>
         gvs[AllCaseEqs(),empty_locals_def,ELIM_UNCURRY,dec_clock_def] >>
         metis_tac[PAIR,FST,SND])
     >~[‘ShMemLoad’]
     >- (Cases_on ‘op’>>
         gvs[Once evaluate_def,AllCaseEqs(),ELIM_UNCURRY,empty_locals_def,
             dec_clock_def,set_kvar_def,nb_op_def,sh_mem_store_def,
             set_var_def, set_global_def,sh_mem_load_def,lookup_kvar_def] >>
         metis_tac[PAIR,FST,SND])
     >~[‘ShMemStore’]
     >- (Cases_on ‘op’>>
         gvs[Once evaluate_def,AllCaseEqs(),ELIM_UNCURRY,empty_locals_def,
             dec_clock_def,set_var_def,nb_op_def,sh_mem_store_def,
             sh_mem_load_def] >>
         metis_tac[PAIR,FST,SND])>>
     gvs[Once evaluate_def,AllCaseEqs(),ELIM_UNCURRY,empty_locals_def,dec_clock_def,set_var_def,set_kvar_def,set_global_def] >>
     metis_tac[PAIR,FST,SND])
QED

Definition every_exp_def:
  (every_exp P (panLang$Const w) = P(Const w)) ∧
  (every_exp P (Var vk v) = P(Var vk v)) ∧
  (every_exp P (Struct es) = (P(Struct es) ∧ EVERY (every_exp P) es)) ∧
  (every_exp P (Field i e) = (P(Field i e) ∧ every_exp P e)) ∧
  (every_exp P (Load sh e) = (P(Load sh e) ∧ every_exp P e)) ∧
  (every_exp P (Load32 e) = (P(Load32 e) ∧ every_exp P e)) ∧
  (every_exp P (LoadByte e) = (P(LoadByte e) ∧ every_exp P e)) ∧
  (every_exp P (Op bop es) = (P(Op bop es) ∧ EVERY (every_exp P) es)) ∧
  (every_exp P (Panop op es) = (P(Panop op es) ∧ EVERY (every_exp P) es)) ∧
  (every_exp P (Cmp c e1 e2) = (P(Cmp c e1 e2) ∧ every_exp P e1 ∧ every_exp P e2)) ∧
  (every_exp P (Shift sh e num) = (P(Shift sh e num) ∧ every_exp P e)) ∧
  (every_exp P BaseAddr = P BaseAddr) ∧
  (every_exp P TopAddr = P TopAddr) ∧
  (every_exp P BytesInWord = P BytesInWord)
Termination
  wf_rel_tac `measure (exp_size ARB o SND)` >>
  rpt strip_tac >>
  imp_res_tac MEM_IMP_exp_size >>
  TRY (first_x_assum (assume_tac o Q.SPEC `ARB`)) >>
  decide_tac
End

Definition exps_of_def:
  (exps_of (Raise _ e) = [e]) ∧
  (exps_of (Dec _ e p) = e::exps_of p) ∧
  (exps_of (Seq p q) = exps_of p ++ exps_of q) ∧
  (exps_of (If e p q) = e::exps_of p ++ exps_of q) ∧
  (exps_of (While e p) = e::exps_of p) ∧
  (exps_of (Call NONE _ es) = es) ∧
  (exps_of (Call (SOME (_ , (SOME (_ ,  _ , ep)))) _ es) = es++exps_of ep) ∧
  (exps_of (Call (SOME (_ , NONE)) _ es) = es) ∧
  (exps_of (DecCall _ _ _ es p) = es++exps_of p) ∧
  (exps_of (Store e1 e2) = [e1;e2]) ∧
  (exps_of (Store32 e1 e2) = [e1;e2]) ∧
  (exps_of (StoreByte e1 e2) = [e1;e2]) ∧
  (exps_of (Return e) = [e]) ∧
  (exps_of (ExtCall _ e1 e2 e3 e4) = [e1;e2;e3;e4]) ∧
  (exps_of (Assign _ _ e) = [e]) ∧
  (exps_of (ShMemLoad _ _ _ e) = [e]) ∧
  (exps_of (ShMemStore _ e1 e2) = [e1;e2]) ∧
  (exps_of _ = [])
End

Definition localised_exp_def:
  (localised_exp (Const w) = T) ∧
  (localised_exp (BytesInWord) = T) ∧
  (localised_exp (BaseAddr) = T) ∧
  (localised_exp (TopAddr) = T) ∧
  (localised_exp (BytesInWord) = T) ∧
  (localised_exp (Var Local v) = T) ∧
  (localised_exp (Var Global v) = F) ∧
  (localised_exp (Struct es) = EVERY localised_exp es) ∧
  (localised_exp (Field i e) = localised_exp e) ∧
  (localised_exp (Load sh e) = localised_exp e) ∧
  (localised_exp (Load32 e) = localised_exp e) ∧
  (localised_exp (LoadByte e) = localised_exp e) ∧
  (localised_exp (Op bop es) = EVERY localised_exp es) ∧
  (localised_exp (Panop op es) = EVERY localised_exp es) ∧
  (localised_exp (Cmp c e1 e2) = (localised_exp e1 ∧ localised_exp e2)) ∧
  (localised_exp (Shift sh e num) = localised_exp e)
Termination
  wf_rel_tac `measure (\e. exp_size ARB e)` >>
  rpt strip_tac >>
  imp_res_tac MEM_IMP_exp_size >>
  TRY (first_x_assum (assume_tac o Q.SPEC `ARB`)) >>
  decide_tac
End

Definition localised_prog_def:
  (localised_prog (Raise _ e) ⇔ localised_exp e) ∧
  (localised_prog (Dec _ e p) ⇔ localised_exp e ∧ localised_prog p) ∧
  (localised_prog (Seq p q) ⇔ localised_prog p ∧ localised_prog q) ∧
  (localised_prog (If e p q) ⇔ localised_exp e ∧ localised_prog p ∧ localised_prog q) ∧
  (localised_prog (While e p) ⇔ localised_exp e ∧ localised_prog p) ∧
  (localised_prog (Store e1 e2) ⇔ localised_exp e1 ∧ localised_exp e2) ∧
  (localised_prog (Store32 e1 e2) ⇔ localised_exp e1 ∧ localised_exp e2) ∧
  (localised_prog (StoreByte e1 e2) ⇔ localised_exp e1 ∧ localised_exp e2) ∧
  (localised_prog (ExtCall fn e1 e2 e3 e4) ⇔ localised_exp e1 ∧ localised_exp e2 ∧ localised_exp e3 ∧ localised_exp e4) ∧
  (localised_prog (Return e) ⇔ localised_exp e) ∧
  (localised_prog (ShMemStore op e1 e2) ⇔ localised_exp e1 ∧ localised_exp e2) ∧
  (localised_prog (ShMemLoad op vk v e) ⇔ vk = Local ∧ localised_exp e) ∧
  (localised_prog (Call hdl f args) ⇔
   EVERY localised_exp args ∧
   (case hdl of
    | SOME(_,SOME(_,_,p)) => localised_prog p
    | _ => T)) ∧
  (localised_prog (DecCall vn sh fn args p) ⇔
   EVERY localised_exp args ∧ localised_prog p) ∧
  (localised_prog(Assign Local _ e) ⇔ localised_exp e) ∧
  (localised_prog(Assign Global _ _) ⇔ F) ∧
  (localised_prog _ ⇔ T)
End

Theorem evaluate_decl_commute:
  evaluate_decls s (Function fi::Decl sh v' e::ds) =
  evaluate_decls s (Decl sh v' e::Function fi::ds)
Proof
  rw[evaluate_decls_def] >>
  irule option_case_cong >> simp[] >>
  PURE_REWRITE_TAC[Once $ GSYM state_fupdcanon] >>
  irule eval_upd_code_eq
QED

Theorem functions_eq_FILTER:
  functions prog =
  MAP (λx. case x of Function fi => (fi.name,fi.params,fi.body) | Decl _ _ _ => ARB)
  $ FILTER is_function prog
Proof
  Induct_on ‘prog’ using functions_ind >>
  rw[functions_def,is_function_def]
QED

Theorem functions_append:
  functions(prog1 ++ prog2) = functions prog1 ++ functions prog2
Proof
  rw[functions_eq_FILTER,MAP_APPEND,FILTER_APPEND]
QED

Theorem functions_FILTER:
  ∀prog.
    functions(FILTER is_function prog) = functions prog
Proof
  Induct_on ‘prog’ using functions_ind >>
  rw[functions_def,is_function_def]
QED

Theorem evaluate_decls_functions:
  ∀s pan_code s'.
    evaluate_decls s pan_code = SOME s' ⇒
    s'.code = s.code |++ functions pan_code
Proof
  recInduct evaluate_decls_ind >>
  rw[evaluate_decls_def,functions_def,FUPDATE_LIST_THM] >>
  gvs[AllCaseEqs()]
QED

Theorem evaluate_decls_only_functions:
  ∀s pan_code s'.
    EVERY is_function pan_code ∧
    evaluate_decls s pan_code = SOME s' ⇒
    s' = s with code := s.code |++ functions pan_code
Proof
  recInduct evaluate_decls_ind >>
  rw[evaluate_decls_def,functions_def,FUPDATE_LIST_THM] >>
  gvs[AllCaseEqs(),is_function_def] >>
  simp[state_component_equality]
QED

Theorem evaluate_decls_only_functions':
  ∀s pan_code.
    EVERY is_function pan_code ⇒
    evaluate_decls s pan_code = SOME(s with code := s.code |++ functions pan_code)
Proof
  recInduct evaluate_decls_ind >>
  rw[evaluate_decls_def,functions_def,FUPDATE_LIST_THM] >>
  gvs[AllCaseEqs(),is_function_def] >>
  simp[state_component_equality]
QED

Theorem evaluate_decls_append:
  ∀s ds1 ds2.
    evaluate_decls s (ds1 ++ ds2) =
    case evaluate_decls s ds1 of
      NONE => NONE
    | SOME s' => evaluate_decls s' ds2
Proof
  recInduct evaluate_decls_ind >>
  rw[evaluate_decls_def] >>
  ntac 2 (TOP_CASE_TAC >> gvs[])
QED

Theorem eval_empty_locals_IMP:
  ∀s e v.
    eval (s with locals := FEMPTY) e = SOME v ⇒
    eval s e = SOME v
Proof
  recInduct eval_ind >>
  rw[eval_def,AllCaseEqs(),PULL_EXISTS] >>
  res_tac >> gvs[] >>
  rpt $ first_assum $ irule_at(Pos last) >>
  irule EQ_TRANS >>
  first_assum $ irule_at $ Pos last >>
  irule OPT_MMAP_CONG >>
  rw[] >>
  drule_all pan_commonPropsTheory.opt_mmap_mem_func >>
  strip_tac >> gvs[]
QED

Theorem semantics_decls_has_main:
  semantics_decls s start code <> Fail ⇒
  ∃body.
    FLOOKUP (s.code |++ functions code) start = SOME ([],body)
Proof
  rw[semantics_decls_def] >>
  PURE_FULL_CASE_TAC >> gvs[] >>
  imp_res_tac evaluate_decls_functions >>
  gvs[semantics_def] >>
  PURE_FULL_CASE_TAC >>
  gvs[AllCaseEqs()] >>
  PRED_ASSUM is_forall mp_tac >>
  simp[Once evaluate_def] >>
  disch_then $ qspec_then ‘0’ mp_tac >>
  every_case_tac >> gvs[lookup_code_def,AllCaseEqs()]
QED

Theorem semantics_decls_has_main':
  semantics_decls s start code <> Fail ⇒
  ∃body.
    FLOOKUP (s.code |++ functions code) start = SOME ([],body)
Proof
  rw[semantics_decls_def] >>
  PURE_FULL_CASE_TAC >> gvs[] >>
  imp_res_tac evaluate_decls_functions >>
  gvs[semantics_def] >>
  PURE_FULL_CASE_TAC >>
  gvs[AllCaseEqs()] >>
  PRED_ASSUM is_forall mp_tac >>
  simp[Once evaluate_def] >>
  disch_then $ qspec_then ‘0’ mp_tac >>
  every_case_tac >> gvs[lookup_code_def,AllCaseEqs()]
QED

Theorem evaluate_decls_swap_locals:
  ∀s prog s' locals.
    evaluate_decls s prog = SOME s' ⇒
    evaluate_decls (s with locals := locals) prog = SOME(s' with locals := locals)
Proof
  recInduct evaluate_decls_ind >>
  rw[evaluate_decls_def,AllCaseEqs()] >>
  res_tac >>
  fs[]
QED

Theorem mem_load_swap_memory:
  (∀sh (addr:'a word) addrs memory1 v memory2.
    mem_load sh addr addrs memory1 = SOME v ∧
    (∀addr. addr ∈ addrs ⇒ memory1 addr = memory2 addr)
    ⇒
    mem_load sh addr addrs memory2 = SOME v) ∧
  (∀shs (addr:'a word) addrs memory1 v memory2.
    mem_loads shs addr addrs memory1 = SOME v ∧
    (∀addr. addr ∈ addrs ⇒ memory1 addr = memory2 addr)
    ⇒
    mem_loads shs addr addrs memory2 = SOME v)
Proof
  Induct >>
  simp[cj 1 mem_load_def] >>
  simp[cj 2 mem_load_def, cj 3 mem_load_def] >>
  rw[AllCaseEqs()] >>
  res_tac >>
  fs[]
QED

Theorem mem_load_swap_memaddrs:
  (∀sh (addr:'a word) addrs memory v addrs2.
    mem_load sh addr addrs memory = SOME v ∧
    addrs ⊆ addrs2
    ⇒
    mem_load sh addr addrs2 memory = SOME v) ∧
  (∀shs (addr:'a word) addrs memory v addrs2.
    mem_loads shs addr addrs memory = SOME v ∧
    addrs ⊆ addrs2
    ⇒
    mem_loads shs addr addrs2 memory = SOME v)
Proof
  Induct >>
  simp[cj 1 mem_load_def] >>
  simp[cj 2 mem_load_def, cj 3 mem_load_def] >>
  rw[AllCaseEqs()] >>
  res_tac >>
  fs[SUBSET_DEF]
QED

Theorem eval_swap_memaddrs:
  ∀s exp v memaddrs.
    eval s exp = SOME v ∧
    s.memaddrs ⊆ memaddrs
    ⇒
    eval (s with memaddrs := memaddrs) exp = SOME v
Proof
  recInduct eval_ind >>
  rw[eval_def,AllCaseEqs(),PULL_EXISTS,mem_load_byte_def,mem_load_32_def] >>
  rpt $ irule_at (Pos last) EQ_REFL >>
  rpt $ first_assum $ irule_at (Pos last) >>
  fs[]
  >~ [‘mem_load’]
  >- (irule $ cj 1 mem_load_swap_memaddrs >> metis_tac[]) >>
  fs[SUBSET_DEF] >>
  irule EQ_TRANS >>
  first_assum $ irule_at $ Pos last >>
  irule OPT_MMAP_CONG >>
  rw[] >>
  drule_all_then strip_assume_tac pan_commonPropsTheory.opt_mmap_mem_func >>
  gvs[]
QED

Theorem evaluate_decls_swap_memaddrs:
  ∀s prog s' memaddrs.
    evaluate_decls s prog = SOME s' ∧
    s.memaddrs ⊆ memaddrs ⇒
    evaluate_decls (s with memaddrs := memaddrs) prog = SOME(s' with memaddrs := memaddrs)
Proof
  recInduct evaluate_decls_ind >>
  rw[evaluate_decls_def,AllCaseEqs()] >>
  first_x_assum drule >>
  simp[] >>
  disch_then $ irule_at Any >>
  simp[] >>
  drule eval_swap_memaddrs >>
  simp[]
QED

Theorem eval_swap_memory:
  ∀s exp v mry.
    eval s exp = SOME v ∧
    (∀addr. addr ∈ s.memaddrs ⇒ s.memory addr = mry addr)
    ⇒
    eval (s with memory := mry) exp = SOME v
Proof
  recInduct eval_ind >>
  rw[eval_def,AllCaseEqs(),PULL_EXISTS,mem_load_byte_def,mem_load_32_def] >>
  rpt $ irule_at (Pos last) EQ_REFL >>
  rpt $ first_assum $ irule_at (Pos last) >>
  fs[]
  >~ [‘mem_load’]
  >- (irule $ cj 1 mem_load_swap_memory >> metis_tac[]) >>
  irule EQ_TRANS >>
  first_assum $ irule_at $ Pos last >>
  irule OPT_MMAP_CONG >>
  rw[] >>
  drule_all_then strip_assume_tac pan_commonPropsTheory.opt_mmap_mem_func >>
  gvs[]
QED

Theorem evaluate_decls_swap_memory:
  ∀s prog s' mry.
    evaluate_decls s prog = SOME s' ∧
    (∀addr. addr ∈ s.memaddrs ⇒ s.memory addr = mry addr) ⇒
    evaluate_decls (s with memory := mry) prog = SOME(s' with memory := mry)
Proof
  recInduct evaluate_decls_ind >>
  rw[evaluate_decls_def,AllCaseEqs()] >>
  first_x_assum drule >>
  simp[] >>
  disch_then $ irule_at Any >>
  simp[] >>
  drule eval_swap_memory >>
  simp[]
QED

Theorem evaluate_decls_memaddrs_mono:
  ∀s prog s' memaddrs.
    evaluate_decls s prog = SOME s' ∧
    s.memaddrs ⊆ memaddrs ⇒
    evaluate_decls (s with memaddrs := memaddrs) prog = SOME(s' with memaddrs := memaddrs)
Proof
  recInduct evaluate_decls_ind >>
  rw[evaluate_decls_def,AllCaseEqs()] >>
  first_x_assum drule >>
  simp[] >>
  disch_then $ irule_at Any >>
  simp[] >>
  drule eval_swap_memaddrs >>
  simp[]
QED

val _ = export_theory();
