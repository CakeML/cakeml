(*
  Set up cv translation of fmaps
*)
Theory fmap_cv
Libs
  preamble cv_transLib
Ancestors
  mllist cv_std finite_map list alist string

(* -- string as domain -- *)

Definition from_str_fmap_def:
  from_str_fmap (f_a:'a -> cv) (m:string |-> 'a) =
    from_list (from_pair (from_list from_char) f_a)
      (MAP (λk. (k, m ' k)) (sort string_le (SET_TO_LIST (FDOM m))))
End

Definition to_str_fmap_def:
  to_str_fmap (t_a:cv -> 'a) (v:cv) =
    FEMPTY |++ (to_list (to_pair (to_list to_char) t_a) v)
End

Theorem from_to_imp:
  from_to f t ⇒
  t (f x) = x
Proof
  rw[cv_typeTheory.from_to_def]
QED

Theorem ALL_DISTINCT_SORT_string_le[simp]:
  FINITE xs ⇒
  ALL_DISTINCT (sort string_le (SET_TO_LIST xs))
Proof
  simp[GSYM (MATCH_MP ALL_DISTINCT_PERM (SPEC_ALL sort_PERM))]
QED

Theorem SORT_SORTED_string_le[simp]:
  SORTED string_le (sort string_le xs)
Proof
  match_mp_tac sort_SORTED>>
  simp[transitive_def,total_def,string_le_def]>>
  metis_tac[string_lt_trans,string_lt_cases]
QED

Theorem fmap_eq_rep:
  FEMPTY |++ MAP (λk. (k,x ' k)) (sort string_le (SET_TO_LIST (FDOM x))) = x
Proof
  rw[fmap_eq_flookup]>>
  Cases_on`FLOOKUP x x'`>>
  rw[FLOOKUP_FUPDATE_LIST,AllCaseEqs()]
  >- fs[ALOOKUP_FAILS,MEM_MAP,flookup_thm] >>
  DEP_REWRITE_TAC[alookup_distinct_reverse] >>
  simp[MAP_MAP_o,o_DEF]>>
  DEP_REWRITE_TAC[ALOOKUP_TABULATE]>>
  fs[flookup_thm]
QED

Theorem from_to_str_fmap[cv_from_to]:
  from_to f_a t_a ⇒
  from_to (from_str_fmap (f_a:'a -> cv)) (to_str_fmap (t_a:cv -> 'a))
Proof
  strip_tac>>
  rw[cv_typeTheory.from_to_def,to_str_fmap_def,from_str_fmap_def]>>
  qmatch_goalsub_abbrev_tac`from_list _ ls`>>
  qmatch_goalsub_abbrev_tac`FEMPTY |++ lss`>>
  `lss = ls` by (
    unabbrev_all_tac>>
    metis_tac[cv_typeTheory.from_to_def,
      cv_typeTheory.from_to_list,
      cv_typeTheory.from_to_pair,
      cv_typeTheory.from_to_char])>>
  rw[Abbr`ls`]>>
  metis_tac[fmap_eq_rep]
QED

(* lookup *)

Theorem FLOOKUP_cv_rep[cv_rep]:
  from_option (f_a:'a -> cv) (FLOOKUP m k) =
  cv_ALOOKUP (from_str_fmap f_a m) (from_list from_char k)
Proof
  simp[from_str_fmap_def]>>
  DEP_REWRITE_TAC [GSYM (GEN_ALL (DISCH_ALL cv_stdTheory.cv_ALOOKUP_thm))]>>
  rw[]
  >-
    metis_tac[cv_typeTheory.from_to_list, cv_typeTheory.from_to_char]>>
  AP_TERM_TAC>>
  simp[Once (GSYM fmap_eq_rep)]>>
  simp[FLOOKUP_FUPDATE_LIST]>>
  DEP_REWRITE_TAC[alookup_distinct_reverse] >>
  CONJ_TAC >-
    simp[MAP_MAP_o,o_DEF,GSYM (MATCH_MP ALL_DISTINCT_PERM (SPEC_ALL sort_PERM))]>>
  simp[MAP_MAP_o,o_DEF]>>
  every_case_tac>>gvs[]
QED

(* update *)

val _ = cv_trans char_lt_def;
val _ = cv_trans string_lt_def;

Definition str_insert_def:
  str_insert [] k v = [(k,v)] ∧
  str_insert ((a,b)::rest) k v =
    if string_lt a k then (a,b)::str_insert rest k v else
    if k = a then (k,v)::rest else (k,v)::(a,b)::rest
End

val _ = cv_trans str_insert_def;
val str_insert_cv_thm = fetch "-" "cv_str_insert_thm";

Theorem SORTED_string_le_string_lt:
  SORTED string_le ls ∧
  ALL_DISTINCT ls ⇒
  SORTED string_lt ls
Proof
  rw[]>>
  drule_at Any ALL_DISTINCT_SORTED_WEAKEN>>
  disch_then (drule_at Any)>>
  disch_then match_mp_tac>>
  simp[string_le_def]
QED

Theorem SORT_SORTED_string_lt[simp]:
  FINITE s ⇒
  SORTED string_lt (sort string_le (SET_TO_LIST s))
Proof
  rw[]>>match_mp_tac SORTED_string_le_string_lt>>
  simp[]
QED

Theorem MEM_MAP_FST_str_insert:
  ∀ls k v.
  MEM x (MAP FST (str_insert ls k v)) ⇔
  x = k ∨ MEM x (MAP FST ls)
Proof
  ho_match_mp_tac str_insert_ind>>rw[str_insert_def]>>
  metis_tac[]
QED

Theorem MEM_str_insert:
  ∀ls k v.
  SORTED string_lt (MAP FST ls) ⇒
  (MEM (x,y) (str_insert ls k v) ⇔
  if x = k
  then y = v
  else MEM (x,y) ls)
Proof
  ho_match_mp_tac str_insert_ind>>rw[str_insert_def]>>
  `transitive string_lt` by
    (gvs[transitive_def]>>metis_tac[string_lt_trans])>>
  gvs[SORTED_EQ,MEM_MAP,FORALL_PROD,PULL_EXISTS]>>
  metis_tac[string_lt_nonrefl,FST]
QED

Theorem str_insert_string_lt:
  ∀ls k v.
  SORTED string_lt (MAP FST ls) ⇒
  SORTED string_lt (MAP FST (str_insert ls k v))
Proof
  ho_match_mp_tac str_insert_ind>>rw[str_insert_def]
  >- (
    DEP_REWRITE_TAC[SORTED_EQ]>>
    CONJ_ASM1_TAC
    >-
      (gvs[transitive_def]>>metis_tac[string_lt_trans])>>
    gvs[SORTED_EQ,MEM_MAP_FST_str_insert]>>
    metis_tac[])
  >-
    metis_tac[string_lt_cases]
QED

Theorem SORTED_string_lt_ALL_DISTINCT:
  SORTED string_lt ls ⇒
  ALL_DISTINCT ls
Proof
  match_mp_tac SORTED_ALL_DISTINCT>>
  rw[irreflexive_def,transitive_def]>>
  metis_tac[string_lt_trans,string_lt_nonrefl]
QED

Theorem FUPDATE_cv_rep[cv_rep]:
  from_str_fmap f_a (m |+ (k,v:'a)) =
  cv_str_insert (from_str_fmap f_a m) (from_list from_char k) (f_a v)
Proof
  simp[from_str_fmap_def]>>
  simp[GSYM str_insert_cv_thm ]>>
  AP_TERM_TAC>>
  qmatch_goalsub_abbrev_tac`l1 = l2`>>
  `SORTED string_lt (MAP FST l1)` by
    simp[Abbr`l1`,MAP_MAP_o,o_DEF,ETA_AX]>>
  `SORTED string_lt (MAP FST l2)` by (
    simp[Abbr`l2`]>>
    match_mp_tac str_insert_string_lt>>
    simp[MAP_MAP_o,o_DEF,ETA_AX])>>
  `ALL_DISTINCT l1 ∧ ALL_DISTINCT l2` by
    metis_tac[ALL_DISTINCT_MAP,SORTED_string_lt_ALL_DISTINCT]>>
  gvs[sorted_map,inv_image_def]>>
  irule SORTED_PERM_EQ>>
  first_assum (irule_at Any)>>
  gvs[]>>
  CONJ_TAC >- (
    match_mp_tac PERM_ALL_DISTINCT>>
    simp[FORALL_PROD]>>
    unabbrev_all_tac>>
    simp[MEM_MAP]>>
    rw[]>>
    DEP_REWRITE_TAC [MEM_str_insert]>>
    simp[MAP_MAP_o,o_DEF,MEM_MAP]>>
    IF_CASES_TAC>>rw[NOT_EQ_FAPPLY])>>
  CONJ_TAC >-
    simp[antisymmetric_def,string_lt_antisym]>>
  simp[transitive_def]>>
  metis_tac[string_lt_trans]
QED

(* test *)

Definition test_def:
  test m = (FLOOKUP m "hi", m |+ ("ho",5:num))
End

val _ = cv_trans test_def;
val res = fetch "-" "cv_test_thm";
