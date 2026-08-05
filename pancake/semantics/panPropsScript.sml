(*
  panLang Properties
*)
Theory panProps
Ancestors
  panLang panSem pan_commonProps
Libs
  preamble

Definition is_decl_def:
  is_decl (Decl sh v e) = T /\
  is_decl _ = F
End

Definition v2word_def:
  v2word (ValWord v) = Word v
End

Theorem shape_of_val:
  shape_of (Val x) = One
Proof
  Cases_on `x` \\ simp [shape_of_def]
QED

val structs_nil_v = EVAL ``(TAKE 0 s.structs)`` |> concl |> rhs

Overload is_wf_shape_nil = ``is_wf_shape ^structs_nil_v``

Definition is_wf_shape_v_def:
  is_wf_shape_v sctxt (Val v) = T /\
  is_wf_shape_v sctxt (RStruct vs) = EVERY (is_wf_shape_v sctxt) vs /\
  is_wf_shape_v sctxt (NStruct nm nm_vs) = ((ALOOKUP sctxt nm <> NONE) /\
    EVERY (is_wf_shape_v sctxt) (MAP SND nm_vs))
Termination
  WF_REL_TAC `measure (v_size ARB o SND)`
  \\ simp [MEM_MAP, PULL_EXISTS, FORALL_PROD]
  \\ rw [MEM_SPLIT]
  \\ simp [list_size_append]
End

Overload is_wf_shape_v_nil = ``is_wf_shape_v ^structs_nil_v``

Theorem is_wf_shape_of_v:
  !sctxt v. is_wf_shape_v sctxt v ==> is_wf_shape sctxt (shape_of v)
Proof
  recInduct is_wf_shape_v_ind
  \\ rw [is_wf_shape_def, shape_of_def, is_wf_shape_v_def, shape_of_val]
  \\ simp [EVERY_MAP] \\ fs [EVERY_MEM]
  \\ every_case_tac
  \\ fs []
QED

Theorem is_wf_shape_v_nil_step1[local]:
  !sctxt v. sctxt = [] /\ is_wf_shape sctxt (shape_of v) ==> is_wf_shape_v sctxt v
Proof
  recInduct is_wf_shape_v_ind
  \\ rw [is_wf_shape_v_def, is_wf_shape_def, shape_of_def]
  \\ fs [EVERY_MAP] \\ fs [EVERY_MEM]
QED

Theorem is_wf_shape_v_nil:
  !xs. xs = [] ==>
  is_wf_shape xs (shape_of v) = is_wf_shape_v xs v
Proof
  metis_tac [is_wf_shape_v_nil_step1, is_wf_shape_of_v]
QED

Theorem is_wf_shape_v_drop:
  !sctxt v. is_wf_shape_v (DROP k sctxt) v ==> is_wf_shape_v sctxt v
Proof
  recInduct is_wf_shape_v_ind
  \\ rw [is_wf_shape_v_def]
  \\ fs [EVERY_MEM]
  \\ qspecl_then [`TAKE k sctxt`, `DROP k sctxt`, `nm`] mp_tac ALOOKUP_APPEND
  \\ simp []
  \\ simp [option_case_eq]
QED

Theorem dropWhile_eq_cons_IMP[local]:
  dropWhile P xs = y :: ys ==>
  ?n. n < LENGTH xs /\ y = EL n xs /\ ~ P y /\ DROP n xs = y :: ys
Proof
  Induct_on `xs` \\ rw [dropWhile_def]
  >- (
    fs []
    \\ qexists_tac `SUC n`
    \\ simp []
  )
  >- (
    qexists_tac `0`
    \\ simp []
  )
QED

Theorem mem_load_is_wf_shape_v:
  (∀shape (w : 'a word) sa sm sctxt v.
      mem_load shape w sa sm sctxt = SOME v ⇒
      is_wf_shape_v sctxt v) ∧
  (∀shapes (w : 'a word) sa sm sctxt vs.
      mem_loads shapes w sa sm sctxt = SOME vs ⇒
      EVERY (is_wf_shape_v sctxt) vs) ∧
  (∀flds (w : 'a word) sa sm sctxt nm_vs.
      mem_load_flds flds w sa sm sctxt = SOME nm_vs ⇒
      EVERY (is_wf_shape_v sctxt) (MAP SND nm_vs))
Proof
  ho_match_mp_tac mem_load_ind
  \\ rw []
  \\ gvs [mem_load_def, AllCaseEqs (), is_wf_shape_v_def, SF ETA_ss]
  \\ imp_res_tac dropWhile_eq_cons_IMP
  \\ fs []
  \\ simp [ALOOKUP_LEAST_EL, MEM_MAP]
  \\ drule_then (irule_at Any) EL_MEM
  \\ fs [PAIR_FST_SND_EQ]
  \\ fs [EVERY_MEM]
  \\ qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `DROP 1`)
  \\ rw [DROP_DROP]
  \\ metis_tac [is_wf_shape_v_drop]
QED

Theorem OPT_MMAP_MEM_IMP:
  OPT_MMAP f xs = SOME ys /\ MEM y ys ==>
  ?x. MEM x xs /\ f x = SOME y
Proof
  rw []
  \\ imp_res_tac pan_commonPropsTheory.opt_mmap_length_eq
  \\ fs [MEM_EL, PULL_EXISTS]
  \\ irule_at Any pan_commonPropsTheory.opt_mmap_el
  \\ simp []
QED

Theorem eval_is_wf_shape_v:
  !s exp v. eval s exp = SOME v /\
    FEVERY (\(nm, v). is_wf_shape_v s.structs v) s.locals /\
    FEVERY (\(nm, v). is_wf_shape_v s.structs v) s.globals ==>
  is_wf_shape_v s.structs v
Proof
  recInduct (name_ind_cases [] eval_ind)
  \\ simp [eval_def, shape_of_def, is_wf_shape_v_def]
  \\ rw []
  \\ gvs [AllCaseEqs (), UNZIP_MAP, is_wf_shape_v_def, shape_of_def]
  \\ rpt (drule_then dxrule FEVERY_FLOOKUP)
  \\ simp []
  >~ [`RStruct _`]
  >- (
    rw [EVERY_MEM]
    \\ dxrule_then drule OPT_MMAP_MEM_IMP
    \\ simp []
  )
  >~ [`NStruct _ _`]
  >- (
    rw [EVERY_MEM]
    \\ gvs [MEM_EL, PULL_EXISTS]
    \\ first_x_assum (drule_then irule)
    \\ imp_res_tac pan_commonPropsTheory.opt_mmap_length_eq
    \\ fs [EL_MAP, EL_ZIP]
    \\ dxrule pan_commonPropsTheory.opt_mmap_el
    \\ simp [EL_MAP]
  )
  \\ fs [EVERY_MAP]
  \\ imp_res_tac ALOOKUP_MEM
  \\ imp_res_tac mem_load_is_wf_shape_v
  \\ imp_res_tac EVERY_MEM
  \\ imp_res_tac EVERY_EL
  \\ fs []
QED

Theorem pan_primop_is_wf_shape_v:
  !sctxt pop args value.
    pan_primop pop args = SOME value ==> is_wf_shape_v sctxt value
Proof
  gen_tac \\ Cases
  \\ rw [pan_primop_def, AllCaseEqs(), UNCURRY_EQ]
  \\ simp [is_wf_shape_v_def]
QED

Theorem length_flatten_eq_size_of_shape:
  !v. is_wf_shape_nil (shape_of v) ==>
   LENGTH (flatten v) = size_of_shape (shape_of v)
Proof
  recInduct flatten_ind >> rw [] >>
  fs [is_wf_shape_def, shape_of_def, shape_of_val] >>
  simp [flatten_def, shape_of_def, size_of_shape_def] >>
  simp [LENGTH_FLAT, MAP_MAP_o, o_DEF] >>
  fs[SUM_MAP_FOLDL] >>
  match_mp_tac FOLDL_CONG >> fs [] >>
  fs [EVERY_MAP] >> fs [EVERY_MEM]
QED

Theorem size_of_sh_with_ctxt_eq:
  !sh sctxt. is_wf_shape_nil sh ==>
  size_of_sh_with_ctxt sctxt sh = size_of_shape sh
Proof
  recInduct size_of_shape_ind
  \\ simp [is_wf_shape_def, size_of_shape_def, size_of_sh_with_ctxt_def]
  \\ simp [EVERY_MEM, Cong MAP_CONG]
  \\ simp [SF ETA_ss]
QED

Theorem mem_loads_some_shape_eq:
  (∀sh adr dm (m: 'a word -> 'a word_lab) stcs v.
  mem_load sh adr dm m stcs = SOME v ==> shape_of v = sh) /\
  (∀shs adr dm (m: 'a word -> 'a word_lab) stcs vs.
   mem_loads shs adr dm m stcs = SOME vs ==> MAP shape_of vs = shs) /\
  (∀flds adr dm (m: 'a word -> 'a word_lab) stcs vs.
   mem_load_flds flds adr dm m stcs = SOME vs ==>
    MAP (shape_of o SND) vs = MAP SND flds)
Proof
  ho_match_mp_tac mem_load_ind
  \\ rw [mem_load_def]
  \\ fs [shape_case_eq, option_case_eq, list_case_eq, pair_case_eq]
  \\ imp_res_tac dropWhile_eq_cons_IMP \\ fs []
  \\ rw [shape_of_def, shape_of_val]
  \\ gs []
  \\ simp_tac (bool_ss ++ ETA_ss) []
QED

Theorem mem_load_some_shape_eq:
  ∀sh adr dm (m: 'a word -> 'a word_lab) stcs v.
  mem_load sh adr dm m stcs = SOME v ==>
  shape_of v = sh
Proof
  metis_tac [mem_loads_some_shape_eq]
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

Theorem list_rel_length_shape_of_flatten_better[local]:
  !vshs args.
  LIST_REL (λvsh arg. vsh = shape_of arg) vshs args /\
  EVERY is_wf_shape_v_nil args ==>
  size_of_shape (Comb vshs) = LENGTH (FLAT (MAP flatten args))
Proof
  Induct >> rpt gen_tac >> strip_tac >>
  fs [LIST_REL_THM, size_of_shape_def] >>
  res_tac >>
  gs [length_flatten_eq_size_of_shape, is_wf_shape_v_def, is_wf_shape_v_nil]
QED

Theorem list_rel_length_shape_of_flatten:
  !vshs args.
  LIST_REL (λvsh arg. SND vsh = shape_of arg) vshs args /\
  EVERY is_wf_shape_v_nil args ==>
  size_of_shape (Comb (MAP SND vshs)) = LENGTH (FLAT (MAP flatten args))
Proof
  simp [list_rel_length_shape_of_flatten_better, EVERY_MAP, o_DEF, LIST_REL_MAP]
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
   ctxt_max (MAX_LIST ns)
      (alist_to_fmap (ZIP (vs,ZIP (sh,with_shape sh ns))))
Proof
  rw [] >> fs [ctxt_max_def] >>
  rw [] >>
  ‘MEM x ns’ suffices_by (
             assume_tac MAX_LIST_max >>
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
  LIST_REL (λsh arg. sh = shape_of arg) sh args /\
  EVERY is_wf_shape_v_nil args ==>
  LENGTH (EL n (with_shape sh ns)) = LENGTH (flatten v)
Proof
  Induct >> rw [] >>
  fs [with_shape_def, size_of_shape_def] >>
  cases_on ‘n’ >> fs []
  >- fs [length_flatten_eq_size_of_shape, is_wf_shape_v_nil] >>
  last_x_assum match_mp_tac >>
  ‘LENGTH (flatten arg) = size_of_shape (shape_of arg)’ by
    fs [length_flatten_eq_size_of_shape, is_wf_shape_v_nil] >>
  fs []
QED

Theorem el_el_with_shape:
  LENGTH xs = size_of_shape (Comb shs) /\
  n < LENGTH shs /\ n' < size_of_shape (EL n shs) /\
  EVERY is_wf_shape_nil shs ==>
  EL n' (EL n (with_shape shs xs)) =
  EL (n' + size_of_shape (Comb (TAKE n shs))) xs
Proof
  simp [with_shape_el_take_drop_eq]
  \\ rw [EL_TAKE]
  \\ irule EL_DROP
  \\ simp []
  \\ qspecl_then [`shs`, `n`] assume_tac LESS_LENGTH
  \\ gs [TAKE_APPEND1, TAKE_APPEND2, TAKE_LENGTH_TOO_LONG]
  \\ fs [EL_APPEND1, EL_APPEND2]
  \\ simp [size_of_shape_def, SUM_APPEND]
QED

Theorem list_rel_flatten_with_shape_flookup:
  !sh ns args v n n'.
  ALL_DISTINCT ns ∧ LENGTH ns = LENGTH (FLAT (MAP flatten args)) /\
  size_of_shape (Comb sh) = LENGTH (FLAT (MAP flatten args)) /\
  EL n args = v /\ n < LENGTH args /\ LENGTH args = LENGTH sh /\
  LIST_REL (λsh arg. sh = shape_of arg) sh args /\
  EVERY is_wf_shape_v_nil args /\
  LENGTH (EL n (with_shape sh ns)) = LENGTH (flatten v) /\
  n' < LENGTH (EL n (with_shape sh ns)) ==>
   FLOOKUP (FEMPTY |++ ZIP (ns,FLAT (MAP flatten args)))
     (EL n' (EL n (with_shape sh ns))) =
   SOME (EL n' (flatten v))
Proof
  rw []
  \\ dep_rewrite.DEP_REWRITE_TAC [el_el_with_shape]
  \\ simp []
  \\ subgoal `EVERY is_wf_shape_nil sh`
  >- (
    fs [EVERY_EL, LIST_REL_EL_EQN, is_wf_shape_v_nil]
  )
  \\ dep_rewrite.DEP_REWRITE_TAC [update_eq_zip_flookup]
  \\ qspecl_then [`args`, `n`] assume_tac LESS_LENGTH
  \\ qspecl_then [`sh`, `n`] assume_tac LESS_LENGTH
  \\ gs [EL_APPEND1, EL_APPEND2, TAKE_APPEND1, TAKE_LENGTH_TOO_LONG]
  \\ gs [listTheory.LIST_REL_APPEND_EQ, length_flatten_eq_size_of_shape]
  \\ imp_res_tac list_rel_length_shape_of_flatten_better
  \\ simp [EL_APPEND1, EL_APPEND2, length_flatten_eq_size_of_shape]
QED

Theorem opt_mmap_helper_thm[local] =
  Q.SPECL [`es`, `es`] OPT_MMAP_CONG
    |> Q.ISPEC `\e. eval ((if T then f else I) st) e`
    |> Q.SPEC `\e. eval st e`
    |> REWRITE_RULE []
    |> Q.GENL [`f`, `st`, `es`]

Theorem eval_upd_clock_eq:
  !t e ck. eval (t with clock := ck) e =  eval t e
Proof
  ho_match_mp_tac eval_ind >> rw [] >>
  fs [eval_def] >>
  gs [Q.SPEC `clock_fupd g` opt_mmap_helper_thm] >>
  rpt ((pairarg_tac ORELSE TOP_CASE_TAC) >> fs []) >>
  gs [Q.SPEC `clock_fupd g` opt_mmap_helper_thm]
QED

Theorem eval_upd_code_eq:
  !t e code. eval (t with code := code) e =  eval t e
Proof
  ho_match_mp_tac eval_ind >> rw [] >>
  fs [eval_def] >>
  gs [Q.SPEC `code_fupd g` opt_mmap_helper_thm] >>
  rpt ((pairarg_tac ORELSE TOP_CASE_TAC) >> fs []) >>
  gs [Q.SPEC `code_fupd g` opt_mmap_helper_thm]
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
            empty_locals_def,
      dec_clock_def,
      opt_mmap_eval_upd_clock_eq,
      kvar_defs
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
      gvs[] >>
      simp [REWRITE_RULE [EQ_IMP_THM] state_component_equality] >>
      last_x_assum $ qspecl_then [‘st'' with clock := st''.clock - ck’,‘ck’] mp_tac >>
      (impl_tac >- gvs[state_component_equality]) >>
      strip_tac >>
      gvs[state_component_equality])
  >~ [‘Call’]
  >- (gvs[evaluate_def,AllCaseEqs(),eval_upd_clock_eq,opt_mmap_eval_upd_clock_eq1,dec_clock_def,
          empty_locals_def,kvar_defs] >>
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
      oneline sh_mem_store_def, empty_locals_def,
      dec_clock_def,opt_mmap_eval_upd_clock_eq1,kvar_defs
     ] >>
  rpt(pairarg_tac >> gvs[]) >>
  gvs[state_component_equality]
QED

Theorem evaluate_min_clock:
  evaluate (prog,s) = (q,r) ∧ q ≠ SOME TimeOut ⇒
  ∃k. evaluate (prog,s with clock := k) = (q,r with clock := 0)
Proof
  qabbrev_tac ‘x = r with clock := 0’>>
  ‘r = x with clock := x.clock + r.clock’
    by simp[state_component_equality,Abbr‘x’]>>
  pop_assum (fn h => rewrite_tac[Once h])>>strip_tac>>
  drule_all evaluate_clock_sub>>
  strip_tac>>fs[]>>metis_tac[]
QED

Theorem evaluate_add_clock_or_timeout:
  evaluate (p,s) = (q,t with clock := 0) ∧ q ≠ SOME TimeOut ⇒
  evaluate (p,s with clock := k) = (q', t') ⇒
      (q' = SOME TimeOut ∧ k < s.clock ∨
       q' = q ∧ s.clock ≤ k ∧ t' = t with clock := k - s.clock)
Proof
  rw[]>>
  rev_drule evaluate_add_clock_eq>>rw[]>>
  Cases_on ‘q' = SOME TimeOut’>>fs[]
  >- (CCONTR_TAC>>fs[NOT_LESS]>>
      imp_res_tac LESS_EQUAL_ADD>>
      first_x_assum $ qspec_then ‘p'’ assume_tac>>gvs[])>>
  Cases_on ‘s.clock ≤ k’>>fs[NOT_LESS_EQUAL]
  >- (imp_res_tac LESS_EQUAL_ADD>>
      first_x_assum $ qspec_then ‘p'’ assume_tac>>gvs[])>>
  drule evaluate_add_clock_eq>>strip_tac>>
  imp_res_tac LESS_ADD>>
  first_x_assum $ qspec_then ‘p'’ assume_tac>>rfs[]>>
  ‘s with clock := s.clock = s’ by simp[state_component_equality]>>fs[]>>
  fs[state_component_equality]
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
      oneline sh_mem_store_def,empty_locals_def,kvar_defs,
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
          oneline sh_mem_store_def, kvar_defs, empty_locals_def,
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
          oneline is_valid_value_def,
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
      oneline sh_mem_store_def, empty_locals_def,kvar_defs,
      dec_clock_def,opt_mmap_eval_upd_clock_eq1,
      eval_upd_clock_eq,ffiTheory.call_FFI_def] >>
  rpt(pairarg_tac >> gvs[]) >>
  rw[] >>
  gvs[AllCaseEqs()] >>
  metis_tac[FST,SND,PAIR,IS_PREFIX_TRANS]
QED

Theorem io_events_eq_imp_ffi_eq:
  evaluate (p, s) = (res, t) ∧ s.ffi.io_events = t.ffi.io_events ⇒
  t.ffi = s.ffi
Proof
  map_every qid_spec_tac [‘res’,‘t’,‘s’,‘p’]>>
  recInduct evaluate_ind>>rw[]>>
  qpat_x_assum ‘_ = (res,t)’ mp_tac
  >~ [‘ShMemLoad’] >-
   (simp[Once evaluate_def]>>
    fs[sh_mem_load_def,sh_mem_store_def,ffiTheory.call_FFI_def]>>
    gvs[AllCaseEqs(),empty_locals_def,dec_clock_def]>>
    rw[]>>gvs[]>>
    gvs[state_component_equality,ffiTheory.ffi_state_component_equality])
  >~ [‘ShMemStore’] >-
   (simp[Once evaluate_def]>>
    fs[sh_mem_load_def,sh_mem_store_def,ffiTheory.call_FFI_def]>>
    gvs[AllCaseEqs(),empty_locals_def,dec_clock_def]>>
    rw[]>>gvs[]>>
    gvs[state_component_equality,ffiTheory.ffi_state_component_equality])
  >~ [‘Call’] >-
   (simp[Once evaluate_def]>>
    fs[ffiTheory.call_FFI_def,kvar_defs]>>
    gvs[AllCaseEqs(),empty_locals_def,dec_clock_def]>>
    rw[]>>gvs[]>>
    imp_res_tac evaluate_io_events_mono>>
    gvs[IS_PREFIX_ANTISYM])
  >~ [‘DecCall’] >-
   (simp[Once evaluate_def]>>
    fs[ffiTheory.call_FFI_def]>>
    gvs[empty_locals_def,dec_clock_def,set_var_def]>>
    rpt (TOP_CASE_TAC>>fs[])>>
    TRY (pairarg_tac>>fs[])>>
    rw[]>>gvs[]>>
    imp_res_tac evaluate_io_events_mono>>
    gvs[IS_PREFIX_ANTISYM])
  >~ [‘Seq’] >-
   (simp[Once evaluate_def]>>
    gvs[AllCaseEqs(),empty_locals_def,dec_clock_def]>>
    rpt (pairarg_tac>>fs[])>>
    rw[]>>gvs[]>>
    imp_res_tac evaluate_io_events_mono>>
    gvs[IS_PREFIX_ANTISYM,dec_clock_def])
  >~ [‘ExtCall’] >-
   (simp[Once evaluate_def]>>
    fs[ffiTheory.call_FFI_def]>>
    gvs[AllCaseEqs(),empty_locals_def,dec_clock_def]>>
    rw[]>>gvs[]>>
    gvs[state_component_equality,ffiTheory.ffi_state_component_equality])
  >~ [‘While’] >-
   (simp[Once evaluate_def]>>
    rpt (pairarg_tac>>fs[])>>
    gvs[AllCaseEqs()]>>rw[]>>
    gvs[dec_clock_def,empty_locals_def]>>
    imp_res_tac evaluate_io_events_mono>>
    gvs[IS_PREFIX_ANTISYM,IS_PREFIX_TRANS])>>
  simp[Once evaluate_def,kvar_defs]>>
  gvs[AllCaseEqs()]>>rw[]>>
  rpt (pairarg_tac>>fs[])>>
  gvs[empty_locals_def,dec_clock_def]
QED

Theorem not_mem_map_flat[local]:
  ~ MEM y (FLAT (MAP f xs)) = (!x. MEM x xs ==> ~ MEM y (f x))
Proof
  simp [MEM_MAP, MEM_FLAT]
  \\ metis_tac []
QED

Theorem update_locals_not_vars_eval_eq_eq:
  ∀s e v n w.
  ~MEM n (var_exp e) ==>
  eval (s with locals := s.locals |+ (n,w)) e = eval s e
Proof
  ho_match_mp_tac eval_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp [var_exp_def, eval_def, FLOOKUP_UPDATE, bool_case_eq] >>
  rpt ((TOP_CASE_TAC ORELSE pairarg_tac) \\ fs []) >>
  csimp [Q.SPEC `locals_fupd foo` opt_mmap_helper_thm] >>
  rw [] >>
  full_simp_tac bool_ss [o_DEF, EXISTS_NOT_EVERY] >>
  gvs [UNZIP_MAP, MEM_MAP, FORALL_PROD, PULL_EXISTS] >>
  gs [not_mem_map_flat, MEM_MAP, FORALL_PROD, PULL_EXISTS,
        SF SFY_ss, Q.SPEC `locals_fupd foo` opt_mmap_helper_thm] >>
  full_simp_tac bool_ss [o_DEF, EXISTS_NOT_EVERY, SF SFY_ss]
QED

Theorem update_locals_not_vars_eval_eq:
  ∀s e v n w.
  ~MEM n (var_exp e) /\
  eval s e = SOME v ==>
  eval (s with locals := s.locals |+ (n,w)) e = SOME v
Proof
  simp [update_locals_not_vars_eval_eq_eq]
QED

Theorem update_locals_not_vars_eval_eq_NONE:
  ∀s e v n w.
  ~MEM n (var_exp e) /\
  eval s e = NONE ==>
  eval (s with locals := s.locals |+ (n,w)) e = NONE
Proof
  simp [update_locals_not_vars_eval_eq_eq]
QED

Theorem eval_fresh_var:
  ∀s e n w.
  ~MEM n (var_exp e) ⇒
  eval (s with locals := s.locals |+ (n,w)) e = eval s e
Proof
  rpt strip_tac >>
  Cases_on ‘eval s e’ >>
  metis_tac[update_locals_not_vars_eval_eq_NONE,update_locals_not_vars_eval_eq]
QED

Theorem OPT_MMAP_update_locals_not_vars_eval_eq:
  ∀s es vs n w.
  ~MEM n (FLAT(MAP var_exp es)) /\
  OPT_MMAP (eval s) es = SOME vs ==>
  OPT_MMAP (eval (s with locals := s.locals |+ (n,w))) es = SOME vs
Proof
  strip_tac >> Induct_on ‘es’ >>
  rw[update_locals_not_vars_eval_eq]
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

Theorem read_write_bytearray_lemma:
  ∀n addr bytes.
   good_dimindex(:α) ∧
   read_bytearray (addr:α word) n (mem_load_byte m addrs be) = SOME bytes
   ⇒ write_bytearray addr bytes m addrs be = m
Proof
  Induct >>
  rw[Once $ oneline read_bytearray_def,AllCaseEqs(),mem_load_byte_def] >>
  gvs[write_bytearray_def,mem_store_byte_def] >>
  gvs[set_byte_get_byte,good_dimindex_def]
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
  st.structs = t.structs ∧
  st.code = t.code ∧ st.ffi.oracle = t.ffi.oracle
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
         gvs[Once evaluate_def,AllCaseEqs(),ELIM_UNCURRY,empty_locals_def,ffiTheory.call_FFI_def,
             dec_clock_def,kvar_defs,nb_op_def,sh_mem_store_def,sh_mem_load_def] >>
         metis_tac[PAIR,FST,SND])
     >~[‘ShMemStore’]
     >- (Cases_on ‘op’>>
         gvs[Once evaluate_def,AllCaseEqs(),ELIM_UNCURRY,empty_locals_def,
             dec_clock_def,set_var_def,nb_op_def,sh_mem_store_def,ffiTheory.call_FFI_def,
             sh_mem_load_def] >>
         metis_tac[PAIR,FST,SND])>>
     gvs[Once evaluate_def,AllCaseEqs(),ELIM_UNCURRY,empty_locals_def,
         ffiTheory.call_FFI_def,dec_clock_def,kvar_defs] >>
     metis_tac[PAIR,FST,SND])
QED

Theorem evaluate_global_shape_invariant:
  ∀p s res st n v.
    evaluate(p,s) = (res,st) ∧ FLOOKUP s.globals n = SOME v ⇒
    ∃v'. FLOOKUP st.globals n = SOME v' ∧ shape_of v' = shape_of v
Proof
  recInduct evaluate_ind >> rpt conj_tac
  >~ [‘While’]
  >- (rpt gen_tac >>
      strip_tac >>
      simp[Once evaluate_def] >>
      rw[AllCaseEqs(),empty_locals_def,UNCURRY_EQ] >> rw[] >>
      gvs[dec_clock_def] >>
      metis_tac[])
  >~ [‘ShMemLoad’]
  >- (rw[Once evaluate_def,AllCaseEqs(),UNCURRY_EQ,kvar_defs,
         sh_mem_load_def,empty_locals_def,sh_mem_store_def,dec_clock_def] >>
      rw[] >>
      rw[FLOOKUP_UPDATE] >> gvs[] >>
      gvs[lookup_kvar_def] >>
      simp[oneline shape_of_def] >>
      PURE_TOP_CASE_TAC >> simp[]) >>
  rw[Once evaluate_def,AllCaseEqs(),UNCURRY_EQ,empty_locals_def,
     sh_mem_store_def,dec_clock_def,kvar_defs] >>
  rw[FLOOKUP_UPDATE] >> gvs[] >> res_tac >>
  metis_tac[]
QED

Theorem evaluate_structs_invariant[local]:
  evaluate (p, s) = (res, s') ==>
  s'.structs = s.structs
Proof
  rw [] \\ imp_res_tac evaluate_invariants
QED

Theorem structs_simps[local] = LIST_CONJ
  [EVAL ``(dec_clock s).structs``, EVAL ``(empty_locals s).structs``,
    EVAL ``(dec_clock s).globals``, EVAL ``(empty_locals s).globals``,
    EVAL ``(dec_clock s).locals``, EVAL ``(empty_locals s).locals``]

Theorem FEVERY_res_var_FLOOKUP[local]:
  FEVERY P fm /\ FEVERY P fm2 ==>
  FEVERY P (res_var fm (nm, FLOOKUP fm2 nm))
Proof
  Cases_on `FLOOKUP fm2 nm`
  \\ simp [FEVERY_ALL_FLOOKUP, res_var_def, FLOOKUP_UPDATE, DOMSUB_FLOOKUP_THM]
  \\ rw []
  \\ every_case_tac
  \\ simp []
QED

Theorem lookup_code_wf_shape_invariant_step:
  OPT_MMAP (eval s) argexps = SOME args ∧
  lookup_code s.code fname args = SOME (prog,newlocals) ∧
  FEVERY (λ(nm,v). is_wf_shape_v s.structs v) s.locals ∧
  FEVERY (λ(nm,v). is_wf_shape_v s.structs v) s.globals ⇒
  FEVERY (λ(nm,v). is_wf_shape_v s.structs v) newlocals
Proof
  rw []
  >> gvs [lookup_code_def, option_case_eq, bool_case_eq, pair_case_eq]
  >> simp [FEVERY_ALL_FLOOKUP, alistTheory.flookup_fupdate_list, option_case_eq]
  >> rw []
  >> dxrule ALOOKUP_MEM
  >> fs [MEM_ZIP, LIST_REL_EL_EQN]
  >> rw []
  >> metis_tac [opt_mmap_length_eq, opt_mmap_el, eval_is_wf_shape_v]
QED

Theorem evaluate_is_wf_shape_invariant:
  ∀ p s res s'.
  evaluate (p, s) = (res, s') ∧
  FEVERY (λ(nm,v). is_wf_shape_v s.structs v) s.locals ∧
  FEVERY (λ(nm,v). is_wf_shape_v s.structs v) s.globals
  ⇒
  FEVERY (λ(nm,v). is_wf_shape_v s'.structs v) s'.locals ∧
  FEVERY (λ(nm,v). is_wf_shape_v s'.structs v) s'.globals ∧
  (case res of
      SOME (Exception eid exn) => is_wf_shape_v s.structs exn
    | SOME (Return retv) => is_wf_shape_v s.structs retv
    | _ => T)
Proof
  recInduct (name_ind_cases [] evaluate_ind) >> rpt conj_tac
  >> rpt (gen_tac ORELSE disch_tac)
  >> fs [structs_simps]
  >> rpt (qpat_x_assum `!x. _` (assume_named_tac "forall_IH"))
  >~ [`While`]
  >- (
    qpat_x_assum `evaluate _ = _` mp_tac
    >> ONCE_REWRITE_TAC [evaluate_def]
    >> strip_tac
    >> fs [AllCaseEqs(), UNCURRY_EQ, structs_simps, LET_THM, FEVERY_FEMPTY]
    >> imp_res_tac evaluate_structs_invariant
    >> gvs [structs_simps, markerTheory.label_def, FEVERY_FEMPTY]
  )
  >~ [`Call`]
  >- (
    gvs [evaluate_def, option_case_eq, pair_case_eq,
        structs_simps, FEVERY_FEMPTY]
    >> gvs [bool_case_eq, pair_case_eq, structs_simps, FEVERY_FEMPTY]
    >> imp_res_tac lookup_code_wf_shape_invariant_step
    >> gvs [AllCaseEqs (), structs_simps, FEVERY_FEMPTY]
    >> simp [set_kvar_def, set_var_def, set_global_def] >> every_case_tac
    >> imp_res_tac evaluate_structs_invariant
    >> gs [markerTheory.label_def, set_var_def, FEVERY_FUPDATE, fevery_to_drestrict, structs_simps]
  )
  >~ [`DecCall`]
  >- (
    (* sigh @ copy-pasting the Call case *)
    gvs [evaluate_def, option_case_eq, pair_case_eq,
        structs_simps, FEVERY_FEMPTY]
    >> gvs [bool_case_eq, pair_case_eq, structs_simps, FEVERY_FEMPTY]
    >> imp_res_tac lookup_code_wf_shape_invariant_step
    >> gvs [AllCaseEqs (), structs_simps, FEVERY_FEMPTY, UNCURRY_EQ]
    >> imp_res_tac evaluate_structs_invariant
    >> gs [markerTheory.label_def, set_var_def, FEVERY_res_var_FLOOKUP, FEVERY_FUPDATE,
        fevery_to_drestrict, structs_simps]
  )
  >> gvs [evaluate_def, sh_mem_load_def, sh_mem_store_def, AllCaseEqs(),
        UNCURRY_EQ, structs_simps, FEVERY_FUPDATE, FEVERY_FEMPTY]
  >> TRY (rename [`set_kvar _ _`] >> simp [set_kvar_def, set_var_def, set_global_def]
        >> every_case_tac)
  >> imp_res_tac evaluate_structs_invariant
  >> imp_res_tac eval_is_wf_shape_v
  >> imp_res_tac pan_primop_is_wf_shape_v
  >> gs [is_wf_shape_v_def, markerTheory.label_def, set_var_def,
       fevery_to_drestrict, FEVERY_FUPDATE, FEVERY_res_var_FLOOKUP]
  >> metis_tac [pan_primop_is_wf_shape_v]
QED

Definition every_exp_def:
  (every_exp P (panLang$Const w) = P(Const w)) ∧
  (every_exp P (Var vk v) = P(Var vk v)) ∧
  (every_exp P (RStruct es) = (P(RStruct es) ∧ EVERY (every_exp P) es)) ∧
  (every_exp P (RField i e) = (P(RField i e) ∧ every_exp P e)) ∧
  (every_exp P (NStruct nm nm_es) = (P(NStruct nm nm_es) ∧
    EVERY (every_exp P) (MAP SND nm_es))) ∧
  (every_exp P (NField i e) = (P(NField i e) ∧ every_exp P e)) ∧
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
  rw [] >>
  fs [MEM_MAP, EXISTS_PROD] >>
  fs [MEM_SPLIT, list_size_append]
End

Definition exps_of_def:
  (exps_of (Raise _ e) = [e]) ∧
  (exps_of (Dec _ _ e p) = e::exps_of p) ∧
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
  (exps_of (Primitive _ _ es) = es) ∧
  (exps_of (ShMemLoad _ _ _ e) = [e]) ∧
  (exps_of (ShMemStore _ e1 e2) = [e1;e2]) ∧
  (exps_of _ = [])
End

val exp_cons_patterns = panLangTheory.exp_nchotomy |> concl
  |> strip_forall |> snd
  |> strip_disj |> map (rhs o snd o strip_exists)

Definition localised_exp_real_def:
  localised_exp = every_exp (\e. case e of Var tp _ => tp = Local | _ => T)
End

Theorem localised_exp_simps = exp_cons_patterns
  |> map (Lib.curry mk_icomb ``localised_exp``)
  |> map EVAL |> map (REWRITE_RULE [GSYM localised_exp_real_def])
  |> LIST_CONJ

Definition nameless_exp_real_def:
  nameless_exp = every_exp (\e. case e of NStruct _ _ => F | NField _ _ => F | _ => T)
End

Theorem nameless_exp_simps = exp_cons_patterns
  |> map (Lib.curry mk_icomb ``nameless_exp``)
  |> map EVAL |> map (REWRITE_RULE [GSYM nameless_exp_real_def])
  |> LIST_CONJ

Definition localised_prog_def:
  (localised_prog (Raise _ e) ⇔ localised_exp e) ∧
  (localised_prog (Dec _ _ e p) ⇔ localised_exp e ∧ localised_prog p) ∧
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
    | _ => T) ∧
   (case hdl of
    | SOME(SOME(Global,_),_) => F
    | _ => T)) ∧
  (localised_prog (DecCall vn sh fn args p) ⇔
   EVERY localised_exp args ∧ localised_prog p) ∧
  (localised_prog(Assign Local _ e) ⇔ localised_exp e) ∧
  (localised_prog(Assign Global _ _) ⇔ F) ∧
  (localised_prog (Primitive _ _ es) ⇔ EVERY localised_exp es) ∧
  (localised_prog _ ⇔ T)
End

Theorem evaluate_decl_commute:
  evaluate_decls s (Function fi::Decl sh v' e::ds) =
  evaluate_decls s (Decl sh v' e::Function fi::ds)
Proof
  rw[evaluate_decls_def]
  >- (
    irule option_case_cong >> simp[] >>
    PURE_REWRITE_TAC[Once $ GSYM state_fupdcanon] >>
    irule eval_upd_code_eq
  )
  >- (
    TOP_CASE_TAC >> simp []
  )
QED

Theorem functions_eq_FILTER:
  functions prog =
  MAP (λx. case x of Function fi => (fi.name,fi.params,fi.body) | _ => ARB)
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

Theorem opt_mmap_eq_some_helper[local]:
  !xs zs. OPT_MMAP f xs = SOME zs /\
  (!x. MEM x xs ==> !y. f x = SOME y ==> g x = SOME y) ==>
  OPT_MMAP g xs = SOME zs
Proof
  Induct_on `xs`
  \\ rw []
QED

Theorem eval_empty_locals_IMP:
  ∀s e v.
    eval (s with locals := FEMPTY) e = SOME v ⇒
    eval s e = SOME v
Proof
  recInduct eval_ind >>
  rw[eval_def,AllCaseEqs(),PULL_EXISTS,UNZIP_MAP] >>
  res_tac >> gvs[] >>
  dxrule_then (irule_at Any) opt_mmap_eq_some_helper >>
  simp []
QED

Theorem decs_stcnames_only_functions:
  !ctxt code. EVERY (\d. is_function d \/ is_decl d) code ==>
  decs_stcnames ctxt code = SOME ctxt
Proof
  recInduct decs_stcnames_ind
  >> simp [decs_stcnames_def, is_function_def, is_decl_def]
QED

Theorem decs_stcnames_only_functions2:
  !ctxt code. EVERY is_function code ==>
  decs_stcnames ctxt code = SOME ctxt
Proof
  simp [EVERY_MEM, decs_stcnames_only_functions]
QED

Theorem semantics_decls_has_main:
  semantics_decls s start code <> Fail ⇒
  ∃body.
    FLOOKUP (s.code |++ functions code) start = SOME ([],body)
Proof
  rw[semantics_decls_def] >>
  rpt (PURE_FULL_CASE_TAC >> gvs[]) >>
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
  rpt (PURE_FULL_CASE_TAC >> gvs[]) >>
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
  (∀sh (addr:'a word) addrs memory1 stcs v memory2.
    mem_load sh addr addrs memory1 stcs = SOME v ∧
    (∀addr. addr ∈ addrs ⇒ memory1 addr = memory2 addr)
    ⇒
    mem_load sh addr addrs memory2 stcs = SOME v) ∧
  (∀shs (addr:'a word) addrs memory1 stcs v memory2.
    mem_loads shs addr addrs memory1 stcs = SOME v ∧
    (∀addr. addr ∈ addrs ⇒ memory1 addr = memory2 addr)
    ⇒
    mem_loads shs addr addrs memory2 stcs = SOME v) ∧
  (∀flds (addr:'a word) addrs memory1 stcs vs memory2.
   mem_load_flds flds addr addrs memory1 stcs = SOME vs ∧
    (∀addr. addr ∈ addrs ⇒ memory1 addr = memory2 addr)
    ⇒
    mem_load_flds flds addr addrs memory2 stcs = SOME vs)
Proof
  ho_match_mp_tac mem_load_ind >>
  rw [mem_load_def] >>
  fs [AllCaseEqs()] >>
  gvs []
QED

Theorem mem_load_swap_memaddrs:
  (∀sh (addr:'a word) addrs memory stcs v addrs2.
    mem_load sh addr addrs memory stcs = SOME v ∧
    addrs ⊆ addrs2
    ⇒
    mem_load sh addr addrs2 memory stcs = SOME v) ∧
  (∀shs (addr:'a word) addrs memory stcs v addrs2.
    mem_loads shs addr addrs memory stcs = SOME v ∧
    addrs ⊆ addrs2
    ⇒
    mem_loads shs addr addrs2 memory stcs = SOME v) ∧
  (∀flds (addr:'a word) addrs memory stcs vs addrs2.
   mem_load_flds flds addr addrs memory stcs = SOME vs ∧
    addrs ⊆ addrs2
    ⇒
    mem_load_flds flds addr addrs2 memory stcs = SOME vs)
Proof
  ho_match_mp_tac mem_load_ind >>
  rw [mem_load_def] >>
  fs [AllCaseEqs()] >>
  gvs [] >>
  imp_res_tac SUBSET_IMP
QED

Theorem eval_swap_memaddrs:
  ∀s exp v memaddrs.
    eval s exp = SOME v ∧
    s.memaddrs ⊆ memaddrs
    ⇒
    eval (s with memaddrs := memaddrs) exp = SOME v
Proof
  recInduct eval_ind >>
  rw[eval_def,AllCaseEqs(),PULL_EXISTS,UNZIP_MAP,mem_load_byte_def,mem_load_32_alt] >>
  res_tac >> simp [] >>
  imp_res_tac SUBSET_IMP >>
  imp_res_tac mem_load_swap_memaddrs >>
  dxrule_then (irule_at Any) opt_mmap_eq_some_helper >> simp []
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
  rw[eval_def,AllCaseEqs(),PULL_EXISTS,UNZIP_MAP,mem_load_byte_def,mem_load_32_alt] >>
  res_tac >> simp [] >>
  imp_res_tac SUBSET_IMP >>
  imp_res_tac mem_load_swap_memory >>
  fs [] >>
  dxrule_then (irule_at Any) opt_mmap_eq_some_helper >> simp []
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

(**** divergence ****)

Theorem evaluate_io_events_lprefix_chain:
  lprefix_chain
  (IMAGE
   (λk. fromList (SND (evaluate (p,s with clock := k))).ffi.io_events)
   𝕌(:num))
Proof
  ‘∀x. x ∈ UNIV ⇒ (λk. llist$fromList (SND (evaluate (p,s with clock := k))).ffi.io_events) x =
                  (fromList o (λk. (SND (evaluate (p,s with clock := k))).ffi.io_events)) x’
    by simp[o_DEF]>>
  ‘(UNIV:num->bool)=UNIV’ by simp[]>>
  drule_then drule IMAGE_CONG>>strip_tac>>
  pop_assum (fn h => pure_rewrite_tac[h])>>
  simp[IMAGE_COMPOSE]>>
  irule prefix_chain_lprefix_chain>>
  simp[prefix_chain_def]>>
  rpt (pop_assum kall_tac)>>
  rw[]>>
  Cases_on ‘k < k'’>>fs[NOT_LESS]
  >- (imp_res_tac (GSYM LESS_ADD)>>
      simp[]>>
      irule OR_INTRO_THM1>>
      irule IS_PREFIX_TRANS>>
      irule_at Any evaluate_add_clock_io_events_mono>>
      qexists ‘p'’>>simp[])>>
  imp_res_tac LESS_EQUAL_ADD>>
  simp[]>>
  irule OR_INTRO_THM2>>
  irule IS_PREFIX_TRANS>>
  irule_at Any evaluate_add_clock_io_events_mono>>
  qexists ‘p'’>>simp[]
QED

(* FIXME: port this or something like it to CakeML more broadly. *)

Datatype:
  semantics_run_res =
    RunError | CompleteResult 'a | Incomplete
End


Definition semantics_wrapper_def:
  semantics_wrapper f = (if ?k v. f k = (RunError, v) then Fail
    else case some res. ?k r ev. f k = (CompleteResult r, ev) /\ res = Terminate r ev
      of SOME res => res
        | NONE => Diverge (LUB (IMAGE (fromList o SND o f) (UNIV : num set))))
End

Theorem semantics_wrapper_eq:
  semantics_wrapper absf <> Fail ==>
  (! k r ev. absf k = (r, ev) /\ r <> RunError ==>
    ?k'. concf (k + k') = (r, ev)) ==>
  (!k k' r ev. concf k = (r, ev) ==>
    r <> Incomplete ==>
    concf (k + k') = (r, ev)) ==>
  (!k k' r ev. absf k = (r, ev) ==>
    r <> Incomplete ==>
    absf (k + k') = (r, ev)) ==>
  (!k k' ev. absf (k + k') = (Incomplete, ev) ==>
    ?r' ev'. absf k = (r', ev') /\ IS_PREFIX ev ev') ==>
  (!k k' ev. concf (k + k') = (Incomplete, ev) ==>
    ?r' ev'. concf k = (r', ev') /\ IS_PREFIX ev ev') ==>
  semantics_wrapper concf = semantics_wrapper absf
Proof
  rw []
  \\ Cases_on `semantics_wrapper absf` \\ fs []
  >- (
    fs [semantics_wrapper_def, CaseEq "bool"]
    \\ pop_assum mp_tac
    \\ DEEP_INTRO_TAC some_intro \\ simp []
    \\ disch_tac
    \\ reverse (qsuff_tac `?abs2. absf = (\k. (Incomplete, abs2 k))`)
    >- (
      qexists_tac `SND o absf`
      \\ rw [FUN_EQ_THM]
      \\ Cases_on `FST (absf k)` \\ Cases_on `absf k` \\ gs []
    )
    \\ strip_tac \\ fs []
    \\ reverse (qsuff_tac `?conc2. concf = (\k. (Incomplete, conc2 k))`)
    >- (
      qexists_tac `SND o concf`
      \\ rw [FUN_EQ_THM]
      \\ last_x_assum (qspec_then `k` mp_tac)
      \\ strip_tac
      \\ last_x_assum (qspecl_then [`k`, `k'`] mp_tac)
      \\ simp []
      \\ simp [PAIR_FST_SND_EQ]
    )
    \\ rw [] \\ fs []
    \\ qmatch_abbrev_tac `build_lprefix_lub l1 = build_lprefix_lub l2`
    \\ `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
      suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_new_chain,unique_lprefix_lub]
    \\ conj_asm1_tac
    >- (
      UNABBREV_ALL_TAC
      \\ conj_tac
      \\ REWRITE_TAC[IMAGE_COMPOSE]
      \\ match_mp_tac prefix_chain_lprefix_chain
      \\ simp [prefix_chain_def, PULL_EXISTS]
      \\ qx_genl_tac [‘k1’, ‘k2’]
      \\ qspecl_then [‘k1’, ‘k2’] mp_tac LESS_EQ_CASES
      \\ simp[LESS_EQ_EXISTS]
      \\ rw []
      \\ metis_tac [ADD_COMM]
    )
    \\ simp [equiv_lprefix_chain_thm]
    \\ UNABBREV_ALL_TAC
    \\ simp[LNTH_fromList,PULL_EXISTS]
    \\ conj_tac
    >- (
      rw []
      \\ last_x_assum (qspec_then `x'` mp_tac)
      \\ strip_tac
      \\ pop_assum (assume_tac o GSYM)
      \\ qexists_tac `x'`
      \\ fs []
      \\ metis_tac [IS_PREFIX_THM, LESS_LESS_EQ_TRANS, ADD_COMM]
    )
    >- (
      rw []
      \\ metis_tac []
    )
  )
  \\ fs [semantics_wrapper_def, CaseEq "bool", CaseEq "option"]
  \\ pop_assum mp_tac
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ strip_tac
  \\ last_x_assum drule
  \\ simp [] \\ strip_tac
  \\ rename [`concf a_k = _`]
  \\ qsuff_tac `!k2 r v. concf k2 = (r, v) ==> (r, v) = concf a_k \/ (r = Incomplete)`
  >- (
    simp []
    \\ disch_tac
    \\ DEEP_INTRO_TAC some_intro \\ simp []
    \\ rw [] \\ fsrw_tac [SATISFY_ss] []
    \\ CCONTR_TAC \\ fs [] \\ res_tac \\ fs []
  )
  \\ rw []
  \\ qspecl_then [`a_k`, `k2`] mp_tac LESS_EQ_CASES
  \\ simp [LESS_EQ_EXISTS] \\ strip_tac \\ fs []
  \\ res_tac \\ fs []
  \\ rw [] \\ res_tac \\ fs []
  \\ CCONTR_TAC \\ fs []
  \\ res_tac \\ full_simp_tac bool_ss []
  \\ gs []
QED

Theorem pan_sem_is_wrapper:
  panSem$semantics s start =
  let prog = TailCall start [] in
  semantics_wrapper (((\res. case res of
    | SOME TimeOut => Incomplete
    | SOME (FinalFFI e) => CompleteResult (FFI_outcome e)
    | SOME (Return _) => CompleteResult Success
    | _ => RunError) ## (\s. s.ffi.io_events)) o
    (\k. evaluate (prog, s with clock := k)))
Proof
  simp [panSemTheory.semantics_def, semantics_wrapper_def]
  \\ irule COND_CONG
  \\ rw []
  >- (
    ho_match_mp_tac ConseqConvTheory.exists_eq_thm>>
    strip_tac>>
    simp[totoTheory.SPLIT_PAIRS,AllCasePreds()]>>
    simp[AllCaseEqs()]
  )
  >- (
    irule optionTheory.option_case_cong
    \\ simp [o_DEF]
    \\ (* both "some" *) AP_TERM_TAC
    \\ rw [FUN_EQ_THM]
    \\ ho_match_mp_tac ConseqConvTheory.exists_eq_thm
    \\ rw [] \\ EQ_TAC \\ rw []
    \\ every_case_tac \\ fs []
  )
QED

