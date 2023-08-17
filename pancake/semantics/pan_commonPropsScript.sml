(*
  Common Properties for Pancake ILS
*)

open preamble pan_commonTheory;

val _ = new_theory "pan_commonProps";


Definition ctxt_max_def:
  ctxt_max (n:num) fm <=>
    0 <= n ∧
    (!v a xs.
       FLOOKUP fm v = SOME (a,xs) ==> !x. MEM x xs ==> x <= n)
End

Definition no_overlap_def:
  no_overlap fm <=>
    (!x a xs.
       FLOOKUP fm x = SOME (a,xs) ==> ALL_DISTINCT xs) /\
    (!x y a b xs ys.
       FLOOKUP fm x = SOME (a,xs) /\
       FLOOKUP fm y = SOME (b,ys) /\
       ~DISJOINT (set xs) (set ys) ==> x = y)
End

Theorem opt_mmap_eq_some:
  ∀xs f ys.
  OPT_MMAP f xs = SOME ys <=>
   MAP f xs = MAP SOME ys
Proof
  Induct >> rw [OPT_MMAP_def] >>
  eq_tac >> rw [] >> fs [] >>
  cases_on ‘ys’ >> fs []
QED


Theorem map_append_eq_drop:
  !xs ys zs f.
   MAP f xs = ys ++ zs ==>
     MAP f (DROP (LENGTH ys) xs) = zs
Proof
  Induct >> rw [] >>
  cases_on ‘ys’ >> fs [DROP]
QED


Theorem opt_mmap_mem_func:
  ∀l f n g.
  OPT_MMAP f l = SOME n ∧ MEM g l ==>
  ?m. f g = SOME m
Proof
  Induct >>
  rw [OPT_MMAP_def] >>
  res_tac >> fs []
QED

Theorem opt_mmap_mem_defined:
  !l f m e n.
   OPT_MMAP f l = SOME m ∧
   MEM e l ∧ f e = SOME n ==>
    MEM n m
Proof
  Induct >> rw [] >>
  fs [OPT_MMAP_def] >> rveq >>
  res_tac >> fs []
QED


Theorem opt_mmap_el:
  ∀l f x n.
  OPT_MMAP f l = SOME x ∧
  n < LENGTH l ==>
  f (EL n l) = SOME (EL n x)
Proof
  Induct >>
  rw [OPT_MMAP_def] >>
  cases_on ‘n’ >> fs []
QED

Theorem opt_mmap_length_eq:
  ∀l f n.
  OPT_MMAP f l = SOME n ==>
  LENGTH l = LENGTH n
Proof
  Induct >>
  rw [OPT_MMAP_def] >>
  res_tac >> fs []
QED

Theorem opt_mmap_opt_map:
  !l f n g.
  OPT_MMAP f l = SOME n ==>
  OPT_MMAP (λa. OPTION_MAP g (f a)) l = SOME (MAP g n)
Proof
  Induct >> rw [] >>
  fs [OPT_MMAP_def] >> rveq >>
  res_tac >> fs []
QED

Theorem distinct_lists_append:
  ALL_DISTINCT (xs ++ ys)  ==>
  distinct_lists xs ys
Proof
  rw [] >>
  fs [ALL_DISTINCT_APPEND, distinct_lists_def, EVERY_MEM]
QED

Theorem distinct_lists_commutes:
  distinct_lists xs ys = distinct_lists ys xs
Proof
  EQ_TAC >>
  rw [] >>
  fs [distinct_lists_def, EVERY_MEM] >>
  metis_tac []
QED

Theorem distinct_lists_cons:
  distinct_lists (ns ++ xs) (ys ++ zs) ==>
  distinct_lists xs zs
Proof
  rw [] >>
  fs [ALL_DISTINCT_APPEND, distinct_lists_def, EVERY_MEM]
QED

Theorem distinct_lists_simp_cons:
  distinct_lists xs (y :: ys) ==>
  distinct_lists xs ys
Proof
  rw [] >>
  fs [ALL_DISTINCT_APPEND, distinct_lists_def, EVERY_MEM]
QED

Theorem distinct_lists_append_intro:
  distinct_lists xs ys /\
  distinct_lists xs zs ==>
  distinct_lists xs (ys ++ zs)
Proof
  rw [] >>
  fs [ALL_DISTINCT_APPEND, distinct_lists_def, EVERY_MEM]
QED

Theorem opt_mmap_flookup_update:
  OPT_MMAP (FLOOKUP fm) xs = SOME ys /\
  ~MEM x xs ==>
  OPT_MMAP (FLOOKUP (fm |+ (x,y))) xs = SOME ys
Proof
  rw [] >>
  fs [opt_mmap_eq_some, MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  rw [] >>
  fs [FLOOKUP_UPDATE, MEM_EL] >>
  metis_tac []
QED



Theorem opt_mmap_some_eq_zip_flookup:
  ∀xs f ys.
  ALL_DISTINCT xs /\
  LENGTH xs = LENGTH ys ⇒
  OPT_MMAP (FLOOKUP (f |++ ZIP (xs,ys))) xs =
  SOME ys
Proof
  Induct >> rw [OPT_MMAP_def] >>
  fs [] >>
  cases_on ‘ys’ >> fs [] >>
  fs [FUPDATE_LIST_THM] >>
  ‘~MEM h (MAP FST (ZIP (xs,t)))’ by
    metis_tac [MEM_MAP, MEM_ZIP,FST, MEM_EL] >>
  drule FUPDATE_FUPDATE_LIST_COMMUTES >>
  disch_then (qspecl_then [‘h'’, ‘f’] assume_tac) >>
  fs [FLOOKUP_DEF]
QED

Theorem opt_mmap_disj_zip_flookup:
  ∀xs f ys zs.
  distinct_lists xs ys /\
  LENGTH xs = LENGTH zs ⇒
  OPT_MMAP (FLOOKUP (f |++ ZIP (xs,zs))) ys =
  OPT_MMAP (FLOOKUP f) ys
Proof
  Induct >> rw [] >>
  fs [distinct_lists_def]
  >- fs [FUPDATE_LIST_THM] >>
  cases_on ‘zs’ >> fs [] >>
  fs [FUPDATE_LIST_THM] >>
  ho_match_mp_tac IMP_OPT_MMAP_EQ >>
  ho_match_mp_tac MAP_CONG >> fs [] >>
  rw [] >>
  fs [FLOOKUP_UPDATE] >>
  metis_tac []
QED


Theorem genlist_distinct_max:
  !n ys m.
   (!y. MEM y ys ==> y <= m) ==>
   distinct_lists (GENLIST (λx. SUC x + m) n) ys
Proof
  rw [] >>
  fs [distinct_lists_def, EVERY_GENLIST] >>
  rw [] >>
  CCONTR_TAC >> fs [] >>
  first_x_assum drule >>
  DECIDE_TAC
QED

Theorem genlist_distinct_max':
  !n ys m p.
   (!y. MEM y ys ==> y <= m) ==>
   distinct_lists (GENLIST (λx. SUC x + (m + p)) n) ys
Proof
  rw [] >>
  fs [distinct_lists_def, EVERY_GENLIST] >>
  rw [] >>
  CCONTR_TAC >> fs [] >>
  first_x_assum drule >>
  DECIDE_TAC
QED

Theorem update_eq_zip_flookup:
  ∀xs f ys n.
  ALL_DISTINCT xs /\
  LENGTH xs = LENGTH ys /\
  n < LENGTH xs ⇒
  FLOOKUP (f |++ ZIP (xs,ys)) (EL n xs) =
        SOME (EL n ys)
Proof
  Induct >> rw [FUPDATE_LIST_THM] >>
  cases_on ‘ys’ >>
  fs [FUPDATE_LIST_THM] >>
  ‘~MEM h (MAP FST (ZIP (xs,t)))’ by
    metis_tac [MEM_MAP, MEM_ZIP,FST, MEM_EL] >>
  cases_on ‘n’ >> fs [] >>
  drule FUPDATE_FUPDATE_LIST_COMMUTES >>
  disch_then (qspecl_then [‘h'’, ‘f’] assume_tac) >>
  fs [FLOOKUP_DEF]
QED

Theorem update_eq_zip_map_flookup:
  ∀xs f n m.
  n < LENGTH xs ⇒
    FLOOKUP (f |++ ZIP (xs,MAP (λx. m) xs)) (EL n xs) =
    SOME m
Proof
  Induct >> rw [FUPDATE_LIST_THM] >>
  cases_on ‘n’ >>
  fs [] >>
  cases_on ‘~MEM h (MAP FST (ZIP (xs,MAP (λx. m) xs)))’
  >- (
    drule FUPDATE_FUPDATE_LIST_COMMUTES >>
    disch_then (qspecl_then [‘m’, ‘f’] assume_tac) >>
    fs [FLOOKUP_DEF]) >>
  fs [] >>
  fs [MEM_MAP] >> rveq >> fs [] >>
  cases_on ‘y’ >> fs [] >>
  ‘LENGTH xs = LENGTH (MAP (λx. m) xs)’ by fs [] >>
  drule MEM_ZIP >>
  disch_then (qspec_then ‘(q,r)’ mp_tac) >>
  fs [] >>
  strip_tac >> rveq >> fs []
QED



Theorem flookup_fupdate_zip_not_mem:
  ∀xs ys f n.
  LENGTH xs = LENGTH ys /\
  ~MEM n xs ⇒
  FLOOKUP (f |++ ZIP (xs,ys)) n =
  FLOOKUP f n
Proof
  Induct >> rw [FUPDATE_LIST_THM] >>
  cases_on ‘ys’ >>
  fs [FUPDATE_LIST_THM] >>
  metis_tac [FLOOKUP_UPDATE]
QED

Theorem map_flookup_fupdate_zip_not_mem:
  ∀xs ys f n.
  distinct_lists xs ys /\
  LENGTH xs = LENGTH zs ⇒
  MAP (FLOOKUP (f |++ ZIP (xs,zs))) ys =
  MAP (FLOOKUP f) ys
Proof
  rw [] >>
  fs [MAP_EQ_EVERY2] >>
  ho_match_mp_tac EVERY2_refl >>
  rw [] >>
  fs [distinct_lists_def, EVERY_MEM] >>
  ho_match_mp_tac flookup_fupdate_zip_not_mem >>
  metis_tac []
QED


Theorem domsub_commutes_fupdate:
  !xs ys fm x.
   ~MEM x xs ∧ LENGTH xs = LENGTH ys ==>
    (fm |++ ZIP (xs,ys)) \\ x = (fm \\ x) |++ ZIP (xs,ys)
Proof
  Induct >> rw []
  >- fs [FUPDATE_LIST_THM] >>
  cases_on ‘ys’ >> fs [] >>
  fs [FUPDATE_LIST_THM] >>
  metis_tac [DOMSUB_FUPDATE_NEQ]
QED


Theorem map_the_some_cancel:
  !xs. MAP (THE ∘ SOME) xs = xs
Proof
  Induct >> rw []
QED

Triviality FUPDATE_LIST_APPLY_NOT_MEM_ZIP:
  ∀l1 l2 f k.
  LENGTH l1 = LENGTH l2 ∧ ¬MEM k l1 ⇒ (f |++ ZIP (l1, l2)) ' k = f ' k
Proof
 metis_tac [FUPDATE_LIST_APPLY_NOT_MEM, MAP_ZIP]
QED

Theorem fm_multi_update:
  !xs ys a b c d fm.
  ~MEM a xs ∧ ~MEM c xs ∧ a ≠ c ∧ LENGTH xs = LENGTH ys ==>
   fm |++ ((a,b)::(c,d)::ZIP (xs,ys)) |++ ((a,b)::ZIP (xs,ys)) =
   fm |++ ((a,b)::(c,d)::ZIP (xs,ys))
Proof
  fs [FUPDATE_LIST_THM, GSYM fmap_EQ_THM, FDOM_FUPDATE, FDOM_FUPDATE_LIST] >>
  rpt strip_tac
  >- (fs [pred_setTheory.EXTENSION] >> metis_tac []) >>
  fs [FUPDATE_LIST_APPLY_NOT_MEM_ZIP, FAPPLY_FUPDATE_THM] >>
  (Cases_on ‘MEM x xs’
   >- (match_mp_tac FUPDATE_SAME_LIST_APPLY >> simp [MAP_ZIP])
   >- rw [FUPDATE_LIST_APPLY_NOT_MEM_ZIP, FAPPLY_FUPDATE_THM])
QED

Theorem el_reduc_tl:
  !l n. 0 < n ∧ n < LENGTH l ==> EL n l = EL (n-1) (TL l)
Proof
  Induct >> rw [] >>
  cases_on ‘n’ >> fs []
QED

Theorem zero_not_mem_genlist_offset:
  !t. LENGTH t <= 31 ==>
  ~MEM 0w (MAP (n2w:num -> word5) (GENLIST (λi. i + 1) (LENGTH t)))
Proof
  Induct >> rw [] >>
  CCONTR_TAC >> fs [MEM_MAP, MEM_GENLIST] >> rveq >>
  fs [ADD1] >>
  ‘(i + 1) MOD 32 = i + 1’ by (
    match_mp_tac LESS_MOD >> DECIDE_TAC) >>
  fs []
QED

Theorem all_distinct_take:
  !ns n.
  ALL_DISTINCT ns /\ n <= LENGTH ns  ==>
  ALL_DISTINCT (TAKE n ns)
Proof
  Induct >> rw [] >> fs [] >>
  cases_on ‘n’ >> fs [TAKE] >>
   metis_tac [MEM_TAKE]
QED

Theorem all_distinct_drop:
  !ns n.
  ALL_DISTINCT ns /\ n <= LENGTH ns  ==>
  ALL_DISTINCT (DROP n ns)
Proof
  Induct >> rw [] >> fs [] >>
  cases_on ‘n’ >> fs [DROP] >>
   metis_tac [MEM_DROP]
QED

Theorem disjoint_take_drop_sum:
  !n m p ns.
   ALL_DISTINCT ns ==>
   DISJOINT (set (TAKE n ns)) (set (TAKE p (DROP (n + m) ns)))
Proof
  Induct >> rw [] >>
  cases_on ‘ns’ >> fs [LESS_EQ_ADD_SUB, SUC_SUB1] >>
  CCONTR_TAC >> fs [] >>
  drule MEM_TAKE >>
  strip_tac >>
  drule MEM_DROP_IMP >> fs []
QED


Theorem disjoint_drop_take_sum:
  !n m p ns.
   ALL_DISTINCT ns ==>
   DISJOINT (set (TAKE p (DROP (n + m) ns))) (set (TAKE n ns))
Proof
  Induct >> rw [] >>
  cases_on ‘ns’ >> fs [LESS_EQ_ADD_SUB, SUC_SUB1] >>
  CCONTR_TAC >> fs [] >>
  drule MEM_TAKE >>
  strip_tac >>
  drule MEM_DROP_IMP >> fs []
QED

Theorem fm_empty_zip_alist:
  !xs ys. LENGTH xs = LENGTH ys /\
  ALL_DISTINCT xs ==>
  FEMPTY |++ ZIP (xs,ys) =
  alist_to_fmap (ZIP (xs,ys))
Proof
  Induct >> rw []
  >- fs [FUPDATE_LIST_THM] >>
  cases_on ‘ys’ >> fs [] >>
  fs [FUPDATE_LIST_THM] >>
  last_x_assum (qspecl_then [‘t’] assume_tac) >>
  fs [] >>
  pop_assum (assume_tac o GSYM) >>
  fs [] >>
  match_mp_tac FUPDATE_FUPDATE_LIST_COMMUTES >>
  CCONTR_TAC >> fs [MEM_MAP] >> rveq >>
  drule MEM_ZIP >>
  disch_then (qspec_then ‘y’ mp_tac) >>
  strip_tac >> fs [] >> rveq >> fs [FST] >>
  fs [MEM_EL] >> metis_tac  []
QED

Theorem fm_empty_zip_flookup:
  !xs ys x y.
  LENGTH xs = LENGTH ys /\ ALL_DISTINCT xs /\
  FLOOKUP (FEMPTY |++ ZIP (xs,ys)) x = SOME y ==>
  ?n. n < LENGTH xs /\ EL n (ZIP (xs,ys)) = (x,y)
Proof
  Induct >> rw []
  >-  fs [FUPDATE_LIST_THM] >>
  cases_on ‘ys’ >> fs [] >>
  fs [FUPDATE_LIST_THM] >>
  cases_on ‘x = h’ >> fs [] >> rveq
  >- (
   qexists_tac ‘0’ >> fs [] >>
   ‘~MEM h (MAP FST (ZIP (xs,t)))’ by
     metis_tac [MEM_MAP, MEM_ZIP,FST, MEM_EL] >>
   drule FUPDATE_FUPDATE_LIST_COMMUTES >>
   disch_then (qspecl_then [‘h'’, ‘FEMPTY’] assume_tac) >>
   fs [FLOOKUP_DEF]) >>
  ‘~MEM h (MAP FST (ZIP (xs,t)))’ by
    metis_tac [MEM_MAP, MEM_ZIP,FST, MEM_EL] >>
  drule FUPDATE_FUPDATE_LIST_COMMUTES >>
  disch_then (qspecl_then [‘h'’, ‘FEMPTY’] assume_tac) >>
  fs [] >>
  fs [FLOOKUP_UPDATE] >>
  last_x_assum (qspec_then ‘t’ mp_tac) >>
  fs [] >>
  disch_then drule >>
  strip_tac >> fs [] >>
  qexists_tac ‘SUC n’ >> fs []
QED

Theorem fm_empty_zip_flookup_el:
  !xs ys zs n x.
   ALL_DISTINCT xs /\ LENGTH xs = LENGTH ys /\ LENGTH ys = LENGTH zs /\
   n < LENGTH xs /\ EL n xs = x ==>
    FLOOKUP (FEMPTY |++ ZIP (xs,ZIP (ys,zs))) x = SOME (EL n ys,EL n zs)
Proof
  Induct >> rw [] >>
  cases_on ‘ys’ >> cases_on ‘zs’ >> fs [] >>
  fs [FUPDATE_LIST_THM] >>
  cases_on ‘n’ >> fs []
  >- (
   ‘~MEM h (MAP FST (ZIP (xs,ZIP (t,t'))))’ by (
     ‘LENGTH xs = LENGTH (ZIP (t,t'))’ by fs [] >>
     metis_tac [MEM_MAP, MEM_ZIP,FST, MEM_EL]) >>
   drule FUPDATE_FUPDATE_LIST_COMMUTES >>
   disch_then (qspecl_then [‘(h', h'')’, ‘FEMPTY’] assume_tac) >>
   fs [FLOOKUP_DEF]) >>
  ‘~MEM h (MAP FST (ZIP (xs,ZIP (t,t'))))’ by (
    ‘LENGTH xs = LENGTH (ZIP (t,t'))’ by fs [] >>
    metis_tac [MEM_MAP, MEM_ZIP,FST, MEM_EL]) >>
  drule FUPDATE_FUPDATE_LIST_COMMUTES >>
  disch_then (qspecl_then [‘(h', h'')’, ‘FEMPTY’] assume_tac) >>
  fs [] >>
  fs [FLOOKUP_UPDATE] >>
  TOP_CASE_TAC >> fs [] >>
  rveq >> drule EL_MEM >> fs []
QED




Theorem all_distinct_flookup_all_distinct:
  no_overlap fm /\
   FLOOKUP fm x = SOME (y,zs) ==>
  ALL_DISTINCT zs
Proof
  rw [] >>
  fs [no_overlap_def] >>
  metis_tac []
QED

Theorem no_overlap_flookup_distinct:
  no_overlap fm /\
  x ≠ y /\
  FLOOKUP fm x = SOME (a,xs) /\
  FLOOKUP fm y = SOME (b,ys) ==>
  distinct_lists xs ys
Proof
  rw [] >>
  match_mp_tac distinct_lists_append >>
  fs [no_overlap_def, ALL_DISTINCT_APPEND, DISJOINT_ALT] >>
  metis_tac []
QED


Theorem all_distinct_take_frop_disjoint:
  !ns n.
   ALL_DISTINCT ns ∧ n <= LENGTH ns ==>
  DISJOINT (set (TAKE n ns)) (set (DROP n ns))
Proof
  Induct >> rw [] >>
  cases_on ‘n’ >> fs [] >>
  CCONTR_TAC >> fs [] >>
  fs[MEM_DROP, MEM_EL] >>
  metis_tac []
QED

Theorem fupdate_flookup_zip_elim:
  !xs ys zs as x.
   FLOOKUP (FEMPTY |++ ZIP (xs, ys)) x = NONE ∧
   LENGTH zs = LENGTH as ∧ LENGTH xs = LENGTH ys /\
   ALL_DISTINCT xs ==>
   FLOOKUP (FEMPTY |++ ZIP (xs, ys) |++ ZIP (zs, as)) x =  FLOOKUP (FEMPTY |++ ZIP (zs, as)) x
Proof
  Induct >> rw []
  >- (fs [FUPDATE_LIST_THM]) >>
  cases_on ‘ys’ >> fs [] >>
  fs [FUPDATE_LIST_THM] >>
  ‘FLOOKUP (FEMPTY |++ ZIP (xs,t)) x = NONE’ by (
    ‘~MEM h (MAP FST (ZIP (xs,t)))’ by (
      CCONTR_TAC >> fs [MAP_ZIP, MEM_MAP] >> drule MEM_ZIP >>
      disch_then (qspec_then ‘y’ assume_tac) >> fs [] >> rveq >> rfs [MEM_EL] >>
      metis_tac []) >>
    drule FUPDATE_FUPDATE_LIST_COMMUTES >>
    disch_then (qspecl_then [‘h'’, ‘FEMPTY’] assume_tac) >>
    fs [FLOOKUP_UPDATE] >>
    FULL_CASE_TAC >> fs []) >>
  ‘FLOOKUP (FEMPTY |+ (h,h') |++ ZIP (xs,t) |++ ZIP (zs,as)) x =
   FLOOKUP (FEMPTY |++ ZIP (xs,t) |++ ZIP (zs,as)) x’ by (
    cases_on ‘FLOOKUP (FEMPTY |++ ZIP (xs,t) |++ ZIP (zs,as)) x’ >> fs []
    >- fs [flookup_update_list_none] >>
    fs [flookup_update_list_some]) >>
  fs [] >>
  last_x_assum match_mp_tac >> fs []
QED

Theorem not_mem_fst_zip_flookup_empty:
  !xs ys x.
   ~MEM x xs ∧ ALL_DISTINCT xs ∧
   LENGTH xs = LENGTH ys ==>
   FLOOKUP (FEMPTY |++ ZIP (xs, ys)) x = NONE
Proof
  Induct >> rw []
  >- (fs [FUPDATE_LIST_THM]) >>
  cases_on ‘ys’ >> fs [] >>
  fs [FUPDATE_LIST_THM] >>
  ‘~MEM h (MAP FST (ZIP (xs,t)))’ by (
    CCONTR_TAC >> fs [MAP_ZIP, MEM_MAP] >> drule MEM_ZIP >>
    disch_then (qspec_then ‘y’ assume_tac) >> fs [] >> rveq >> rfs [MEM_EL] >>
    metis_tac []) >>
  drule FUPDATE_FUPDATE_LIST_COMMUTES >>
  disch_then (qspecl_then [‘h'’, ‘FEMPTY’] assume_tac) >>
  fs [FLOOKUP_UPDATE]
QED


Theorem fm_zip_append_take_drop:
  !xs ys zs f.
   ALL_DISTINCT xs ∧ LENGTH xs = LENGTH (ys ++ zs) ==>
   f |++ ZIP (xs,ys ++ zs) = f |++ ZIP (TAKE (LENGTH ys) xs,ys)
                               |++ ZIP (DROP (LENGTH ys) xs,zs)
Proof
  Induct >> rw []
  >- fs [FUPDATE_LIST_THM] >>
  cases_on ‘ys’ >> fs [FUPDATE_LIST_THM]
QED

Theorem disjoint_not_mem_el:
  !xs ys n.
   DISJOINT (set xs) (set ys) ∧ n < LENGTH xs ==>
   ~MEM (EL n xs) ys
Proof
  Induct >> rw [] >>
  cases_on ‘n’ >> fs []
QED

Theorem map_some_the_map:
  !xs ys f.
  MAP f xs = MAP SOME ys ==>
  MAP (λn. THE (f n)) xs = ys
Proof
  Induct >> rw [] >>
  cases_on ‘ys’ >> fs []
QED

Theorem set_eq_membership:
  a = b ∧ x ∈ a ==> x ∈ b
Proof
  rw [] >> fs []
QED


Theorem max_set_list_max:
  !xs. MAX_SET (set xs) = list_max xs
Proof
  Induct >> rw [] >> fs [list_max_def] >>
  ‘FINITE (set xs)’ by fs [] >>
  drule (MAX_SET_THM |> CONJUNCT2) >>
  disch_then (qspec_then ‘h’ assume_tac) >>
  fs [] >>
  TOP_CASE_TAC >>fs [MAX_DEF]
QED

Theorem list_max_add_not_mem:
  !xs. ~MEM (list_max xs + 1) xs
Proof
  Induct >> rw [] >> fs [list_max_def] >>
  CCONTR_TAC >> fs [] >>
  every_case_tac >> fs [list_max_def] >>
  ntac 2 (pop_assum mp_tac) >> pop_assum kall_tac >>
  qid_spec_tac ‘xs’ >>
  Induct >> rw [] >> fs [list_max_def]
QED

Theorem subspt_same_insert_subspt:
  !p q n.
   subspt p q ==>
   subspt (insert n () p) (insert n () q)
Proof
  rw [] >>
  fs [subspt_lookup] >>
  rw [] >>
  fs [lookup_insert] >>
  FULL_CASE_TAC >> fs []
QED

Theorem subspt_insert:
  !p n. subspt p (insert n () p)
Proof
  rw [] >>
  fs [subspt_lookup] >>
  rw [] >>
  fs [lookup_insert]
QED

Theorem subspt_right_insert_subspt:
  !p q n.
   subspt p q ==>
   subspt p (insert n () q)
Proof
  rw [] >>
  fs [subspt_lookup] >>
  rw [] >>
  fs [lookup_insert]
QED

Theorem subspt_same_insert_cancel:
  !p q n m.
   subspt p q ==>
   subspt (insert n () (insert m () (insert n () p)))
          (insert m () (insert n () q))
Proof
  rw [] >>
  fs [subspt_lookup] >>
  rw [] >>
  fs [lookup_insert] >>
  every_case_tac >> fs []
QED


Theorem max_set_count_length:
  !n. MAX_SET (count n) = n − 1
Proof
  Induct >> rw [] >>
  fs [COUNT_SUC] >>
  ‘MAX_SET (n INSERT count n) =
   MAX n (MAX_SET (count n))’ by (
    ‘FINITE (count n)’ by fs [] >>
    metis_tac [MAX_SET_THM]) >>
  fs [MAX_DEF]
QED


Theorem list_max_i_genlist:
  !n. list_max (GENLIST I n) = n − 1
Proof
  rw [] >>
  fs [GSYM COUNT_LIST_GENLIST] >>
  fs [GSYM max_set_list_max] >>
  fs [COUNT_LIST_COUNT] >>
  metis_tac [max_set_count_length]
QED

Theorem el_pair_map_fst_el:
  !xs n x y z.
   n < LENGTH xs /\ EL n xs = (x,y,z) ==>
   x = EL n (MAP FST xs)
Proof
  Induct >> rw [] >>
  cases_on ‘n’ >> fs []
QED


Theorem all_distinct_el_fst_same_eq:
  !xs n n' x y y'.
   ALL_DISTINCT (MAP FST xs) ∧
   n < LENGTH xs ∧ n' < LENGTH xs ∧
   EL n xs = (x,y) ∧
   EL n' xs = (x,y') ==>
   n = n'
Proof
  Induct >> rw [] >>
  fs [] >>
  cases_on ‘n’ >> cases_on ‘n'’ >>
  fs [] >> rveq >> fs []
  >- (
   fs [MEM_MAP] >>
   first_x_assum (qspec_then ‘(x,y')’ mp_tac) >>
   fs [] >>
   drule EL_MEM >>
   strip_tac >> rfs []) >>
  fs [MEM_MAP] >>
  first_x_assum (qspec_then ‘(x,y)’ mp_tac) >>
  fs [] >>
  drule EL_MEM >>
  strip_tac >> rfs []
QED


Theorem lookup_some_el:
  ∀xs n x. lookup n (fromAList xs) = SOME x ==>
   ∃m. m < LENGTH xs ∧ EL m xs = (n,x)
Proof
  rw [lookup_fromAList]
  \\ imp_res_tac ALOOKUP_MEM
  \\ gvs [MEM_EL]
  \\ first_x_assum $ irule_at Any \\ fs []
QED

Theorem max_foldr_lt:
  !xs x n m.
    MEM x xs ∧ n ≤ x ∧ 0 < m ⇒
    x < FOLDR MAX n xs + m
Proof
  Induct >> rw [] >> fs []
  >- fs [MAX_DEF] >>
  last_x_assum drule_all >>
  strip_tac >>
  fs [MAX_DEF]
QED

Theorem fm_update_diff_vars:
  a ≠ b ==>
  fm
  |+ (a ,a')
  |+ (b ,b')
  |+ (a ,a')
  |+ (b ,b'') =
  fm
  |+ (a ,a')
  |+ (b ,b'')
Proof
  rw [] >>
  ‘fm
  |+ (a ,a')
  |+ (b ,b')
  |+ (a ,a')
  |+ (b ,b'') =
  fm
  |+ (a ,a')
  |+ (b ,b')
  |+ (b ,b'')
  |+ (a ,a')’ by (
    match_mp_tac FUPDATE_COMMUTES >>
    fs []) >>
  fs [] >>
  ‘fm |+ (a,a') |+ (b,b'') |+ (a,a') =
   fm |+ (a,a') |+ (a,a') |+ (b,b'')’ by (
    match_mp_tac FUPDATE_COMMUTES >>
    fs []) >>
  fs []
QED


Theorem fmap_to_alist_eq_fm:
  ∀fm.
    FEMPTY |++ MAP (λ(x,y). (x,y)) (fmap_to_alist fm) = fm
Proof
  rw [] >>
  gs [MAP_values_fmap_to_alist] >>
  gs [FUPDATE_LIST_EQ_APPEND_REVERSE] >>
  ‘alist_to_fmap (REVERSE (fmap_to_alist fm)) =
   alist_to_fmap (fmap_to_alist fm)’ by (
    match_mp_tac ALL_DISTINCT_alist_to_fmap_REVERSE >>
    fs [ALL_DISTINCT_fmap_to_alist_keys]) >>
  gs []
QED


val _ = export_theory();
