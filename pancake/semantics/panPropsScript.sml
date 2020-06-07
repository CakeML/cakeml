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

Theorem list_rel_length_shape_of_flatten:
  !vshs args ns.
  LIST_REL (λvsh arg. SND vsh = shape_of arg) vshs args /\
  size_of_shape (Comb (MAP SND vshs)) = LENGTH ns ==>
  LENGTH ns = LENGTH (FLAT (MAP flatten args))
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (cases_on ‘args’ >> fs [size_of_shape_def]) >>
  cases_on ‘args’ >> fs [] >> rveq >>
  fs [size_of_shape_def] >>
  ‘size_of_shape (SND h) <= LENGTH ns’ by DECIDE_TAC >>
  last_x_assum (qspecl_then [‘t’,
                             ‘DROP (size_of_shape (SND h)) ns’] mp_tac) >>
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


val _ = export_theory();
