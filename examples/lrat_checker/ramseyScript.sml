(*
   Defining the Ramsey number and SAT encoding
*)
open preamble miscTheory lratTheory;

val _ = new_theory "ramsey";

(* Definition of the Ramsey numbers *)

Type edges = ``:num -> num -> bool``;

val is_clique_def = Define`
  is_clique e t b <=>
  ∀x y.
    (*
      t is a clique (b=true)
      if all vertices x y are connected by an edge (b=true)

      (accordingly, t is an independent set (b=false)
      if all vertices are not connected
    *)
    x ∈ t ∧ y ∈ t ∧ x ≠ y ⇒
    e x y = b`

val is_ramsey_def = Define`
  is_ramsey k n =
  ∀(e:edges). symmetric e ⇒
    ∃t b. t ⊆ count n ∧ CARD t = k ∧ is_clique e t b`

val ramsey_number_def = Define`
  ramsey_number k =
  LEAST n. is_ramsey k n`

Theorem ramsey_number_0:
  ramsey_number 0 = 0
Proof
  rw[ramsey_number_def,is_ramsey_def]>>
  match_mp_tac bitTheory.LEAST_THM>>rw[is_clique_def]
QED

Theorem ramsey_number_1:
  ramsey_number 1 = 1
Proof
  rw[ramsey_number_def,is_ramsey_def]>>
  match_mp_tac bitTheory.LEAST_THM>>
  rw[]
  >-
    metis_tac[symmetric_EQC]>>
  EVAL_TAC>>
  qexists_tac`{0}`>>simp[]
QED

Theorem is_ramsey_SUC:
  is_ramsey k n ⇒ is_ramsey k (SUC n)
Proof
  rw[is_ramsey_def]>>
  first_x_assum drule>>strip_tac>>
  qexists_tac`t`>>qexists_tac`b`>>
  fs[SUBSET_DEF]>>rw[]>>
  first_x_assum drule>>fs[]
QED

Theorem is_ramsey_mono:
  ∀m.
  n <= m ⇒
  is_ramsey k n ⇒ is_ramsey k m
Proof
  Induct>>rw[]>>
  Cases_on`n ≤ m`>>fs[]
  >-
    metis_tac[is_ramsey_SUC]
  >>
    `n = SUC m` by fs[]>>
    metis_tac[]
QED

Theorem is_clique_INSERT:
  is_clique e (x INSERT t) b ⇒
  is_clique e t b
Proof
  rw[is_clique_def]
QED

Theorem is_ramsey_SUC_k:
  is_ramsey (SUC k) n ⇒ is_ramsey k n
Proof
  rw[is_ramsey_def]>>
  first_x_assum drule>>strip_tac>>
  `FINITE t` by
     metis_tac[FINITE_COUNT,SUBSET_FINITE_I]>>
  Cases_on`t`>>fs[]>>
  qexists_tac`t'`>>simp[]>>
  metis_tac[is_clique_INSERT]
QED

Theorem ramsey_eq:
  is_ramsey k n ∧ ¬is_ramsey k (n-1) ⇒
  ramsey_number k = n
Proof
  rw[ramsey_number_def]>>
  match_mp_tac bitTheory.LEAST_THM>>
  rw[]>>CCONTR_TAC>>
  fs[]>>
  `m ≤ n-1` by fs[]>>
  metis_tac[is_ramsey_mono]
QED

Theorem ramsey_number_2:
  ramsey_number 2 = 2
Proof
  match_mp_tac ramsey_eq>>rw[]
  >-
    (rw[is_ramsey_def]>>
    qexists_tac`count 2`>>fs[]>>
    qexists_tac`e 0 1`>>rw[is_clique_def]>>
    `(x = 0 ∨ x = 1) ∧ (y = 0 ∨ y = 1)` by fs[]>>
    fs[symmetric_def])
  >>
    rw[is_ramsey_def]>>
    qexists_tac`λx y. T`>>rw[]
    >-
      simp[symmetric_def]
    >>
    CCONTR_TAC>>fs[]>>
    `FINITE (count 1)` by
      fs[FINITE_COUNT]>>
    drule CARD_SUBSET>>
    disch_then drule>>
    fs[]
QED

(* all lists of choosing k items from first n *)
val choose_def = Define`
  (choose n 0 cur = [cur]) ∧
  (choose 0 k cur = []) ∧
  (choose (SUC n) (SUC k) cur =
    choose n (SUC k) cur ++
    choose n k (n::cur))`

Theorem choose_correct:
  ∀n k cur s.
    CARD s = k ∧ s ⊆ count n ⇒
    ∃ls'.
      ls' ∈ set (choose n k cur) ∧
      set ls' = s ∪ set cur
Proof
  ho_match_mp_tac (fetch "-" "choose_ind")>>
  rw[choose_def]
  >-
    (`FINITE s` by
       metis_tac[FINITE_COUNT,SUBSET_FINITE_I]>>
    fs[CARD_EMPTY])
  >-
    (CCONTR_TAC>>rfs[]>>
    `CARD s = 0` by fs[]>>
    fs[])
  >>
  Cases_on`n ∈ s`
  >- (
    last_x_assum(qspec_then `s DIFF {n}` mp_tac)>>
    impl_tac >-
      (`FINITE s` by
         metis_tac[FINITE_COUNT,SUBSET_FINITE_I]>>
      drule CARD_DIFF_EQN>>
      disch_then (qspec_then`{n}` assume_tac)>>simp[]>>
      `s ∩ {n} = {n}` by
        (fs[EXTENSION]>>metis_tac[])>>
      fs[SUBSET_DEF]>>
      rw[]>>first_x_assum drule>>
      fs[])>>
    rw[]>>
    qexists_tac`ls'`>>
    simp[EXTENSION]>>
    metis_tac[])
  >>
    first_x_assum drule>>
    impl_tac>-
      (fs[SUBSET_DEF]>>rw[]>>
      first_x_assum drule>>
      `x ≠ n` by metis_tac[]>>
      fs[])>>
    rw[]>>
    metis_tac[]
QED

Theorem choose_correct2:
  ∀n k cur x.
  MEM x (choose n k cur) ∧
  (∀m. MEM m cur ⇒ m ≥ n) ⇒
  set x ⊆ count n ∪ set cur ∧ CARD (set x) = k + CARD (set cur)
Proof
  ho_match_mp_tac (fetch "-" "choose_ind")>>
  simp[choose_def]>>
  ntac 6 strip_tac
  >-
    (first_x_assum drule>>fs[]>>
    impl_tac >-
      (rw[]>>first_x_assum drule>>fs[])>>
    rw[]>>simp[]>>
    fs[SUBSET_DEF]>>rw[]>>
    first_x_assum drule>>
    rw[]>>fs[])
  >>
  first_x_assum drule>>fs[]>>
  impl_tac >-
    (rw[]>>fs[]>>
    first_x_assum drule>>fs[])>>
  `~MEM n cur` by
    (CCONTR_TAC>>fs[]>>first_x_assum drule>>fs[])>>
  rw[]>>
  fs[SUBSET_DEF]>>rw[]>>
  first_x_assum drule>>
  rw[]>>fs[]
QED

Theorem choose_ALL_DISTINCT:
  ∀n k cur x.
  MEM x (choose n k cur) ∧
  ALL_DISTINCT cur ∧
  (∀m. MEM m cur ⇒ m ≥ n) ⇒
  ALL_DISTINCT x
Proof
  ho_match_mp_tac (fetch "-" "choose_ind")>>
  simp[choose_def]>>
  ntac 6 strip_tac
  >-
    (first_x_assum drule>>fs[]>>
    impl_tac >-
      (rw[]>>first_x_assum drule>>fs[])>>
    simp[])
  >>
  first_x_assum drule>>fs[]>>
  `~MEM n cur` by
    (CCONTR_TAC>>fs[]>>first_x_assum drule>>fs[])>>
  simp[]>>
  impl_tac >-
    (rw[]>>fs[]>>
    first_x_assum drule>>fs[])>>
  simp[]
QED

val index_edge_def = Define`
  index_edge n x y =
    n * x + (y:num)`

val clique_edges_def = Define`
  (clique_edges n [] = []) ∧
  (clique_edges n (x::xs) =
  MAP (index_edge n x) xs ++ clique_edges n xs)`

val build_fml_def = Define`
  (build_fml (id:num) [] (acc:ccnf) = acc) ∧
  (build_fml id (cl::cls) acc =
  build_fml (id+1) cls (insert id (QSORT $<= cl) acc))`

val ramsey_lrat_def = Define`
  ramsey_lrat k n =
  let ls = choose n k [] in
  let cli = MAP (clique_edges n) ls in
  build_fml 1 (MAP (λns. MAP (λn. &n:int) ns) cli ++ MAP (λns. MAP (λn. -&n:int) ns) cli) LN`

val decode_edge_def = Define`
  decode_edge n m =
  (m DIV n, m MOD n)`

Theorem values_insert_notin_domain:
  n ∉ domain fml ⇒
  values(insert n l fml) = l INSERT values fml
Proof
  rw[values_def,lookup_insert,EXTENSION,EQ_IMP_THM]
  >-
    (every_case_tac>>fs[]>>
    metis_tac[])
  >-
    metis_tac[]
  >>
    `n ≠ n'` by metis_tac[domain_lookup]>>
    metis_tac[]
QED

Theorem interp_insert_notin_domain:
  n ∉ domain fml ⇒
  interp (insert n p fml) = interp_cclause p INSERT interp fml
Proof
  rw[]>>
  `interp_cclause p INSERT interp fml ⊆ interp (insert n p fml)` by
    (rw[interp_def,SUBSET_DEF,PULL_FORALL]>>
    drule values_insert_notin_domain>>rw[]>>
    metis_tac[])>>
  fs[SET_EQ_SUBSET,interp_insert]
QED

Theorem interp_cclause_QSORT[simp]:
  interp_cclause (QSORT $<= x) = interp_cclause x
Proof
  rw[interp_cclause_def]>>
  AP_TERM_TAC>>
  simp[EXTENSION,QSORT_MEM]
QED

Theorem interp_build_fml:
  ∀ls id acc.
  (∀m. id ≤ m ⇒ m ∉ domain acc) ⇒
  interp (build_fml id ls acc) =
  interp acc ∪ set (MAP interp_cclause ls)
Proof
  Induct>>fs[build_fml_def]>>rw[]>>
  pop_assum(qspec_then`id` assume_tac)>>fs[]>>
  simp[interp_insert_notin_domain]>>
  metis_tac[UNION_COMM,UNION_ASSOC,INSERT_SING_UNION]
QED

Theorem interp_LN[simp]:
  interp LN = {}
Proof
  rw[interp_def,values_def,lookup_def]
QED

Theorem clique_edges_MEM:
  ∀ls n a b.
  MEM a ls ∧ MEM b ls ∧ a ≠ b ⇒
  MEM (index_edge n a b) (clique_edges n ls) ∨
  MEM (index_edge n b a) (clique_edges n ls)
Proof
  Induct>>rw[clique_edges_def]>>
  fs[MEM_MAP]>>
  metis_tac[]
QED

Theorem index_edge_neq_0:
  a ≠ b ∧ a < n ⇒
  index_edge n a b > 0
Proof
  rw[]>>
  `index_edge n a b <> 0` by
    fs[index_edge_def]>>
  fs[]
QED

Theorem pos_imp_int_pos:
  x:num > 0 ⇒
  &x > 0:int ∧
  ¬(-&x > 0:int)
Proof
  intLib.ARITH_TAC
QED

Theorem decode_edge_index_edge:
  b < n ⇒
  decode_edge n (index_edge n a b) = (a,b)
Proof
  rw[decode_edge_def,index_edge_def]>>
  drule DIV_MULT>>
  disch_then(qspec_then`a` assume_tac)>>fs[]
QED

Theorem ramsey_lrat_correct:
  unsatisfiable (interp (ramsey_lrat k n)) ⇒
  is_ramsey k n
Proof
  rw[is_ramsey_def,unsatisfiable_def,satisfiable_def]>>
  CCONTR_TAC>>fs[]>>
  last_x_assum mp_tac>>simp[]>>
  simp[ramsey_lrat_def]>>
  dep_rewrite.DEP_REWRITE_TAC[interp_build_fml]>>
  simp[]>>
  simp[satisfies_union,MAP_MAP_o]>>
  simp[LIST_TO_SET_MAP,satisfies_def,PULL_EXISTS]>>
  qexists_tac`λm. (UNCURRY e) (decode_edge n m)`>>rw[]
  >-
    (drule choose_correct2 >>fs[]>>rw[]>>
    first_x_assum(qspec_then `set x` assume_tac)>>rfs[]>>
    simp[interp_cclause_def,LIST_TO_SET_MAP,satisfies_clause_def,PULL_EXISTS]>>
    pop_assum(qspec_then`F` assume_tac)>>fs[]>>
    fs[is_clique_def]>>
    drule clique_edges_MEM>>
    disch_then(qspecl_then [`n`,`x'`] assume_tac)>>rfs[]>>
    asm_exists_tac>>fs[]
    >-
      (`index_edge n y x' > 0` by
        (match_mp_tac index_edge_neq_0>>fs[SUBSET_DEF])>>
      simp[satisfies_literal_def,interp_lit_def,pos_imp_int_pos]>>
      dep_rewrite.DEP_REWRITE_TAC[decode_edge_index_edge]>>
      fs[SUBSET_DEF,symmetric_def])
    >>
      (`index_edge n x' y > 0` by
        (match_mp_tac index_edge_neq_0>>fs[SUBSET_DEF])>>
      simp[satisfies_literal_def,interp_lit_def,pos_imp_int_pos]>>
      dep_rewrite.DEP_REWRITE_TAC[decode_edge_index_edge]>>
      fs[SUBSET_DEF,symmetric_def]))
  >>
    (drule choose_correct2 >>fs[]>>rw[]>>
    first_x_assum(qspec_then `set x` assume_tac)>>rfs[]>>
    simp[interp_cclause_def,LIST_TO_SET_MAP,satisfies_clause_def,PULL_EXISTS]>>
    pop_assum(qspec_then`T` assume_tac)>>fs[]>>
    fs[is_clique_def]>>
    drule clique_edges_MEM>>
    disch_then(qspecl_then [`n`,`x'`] assume_tac)>>rfs[]>>
    asm_exists_tac>>fs[]
    >-
      (`index_edge n y x' > 0` by
        (match_mp_tac index_edge_neq_0>>fs[SUBSET_DEF])>>
      simp[satisfies_literal_def,interp_lit_def,pos_imp_int_pos]>>
      dep_rewrite.DEP_REWRITE_TAC[decode_edge_index_edge]>>
      fs[SUBSET_DEF,symmetric_def])
    >>
      (`index_edge n x' y > 0` by
        (match_mp_tac index_edge_neq_0>>fs[SUBSET_DEF])>>
      simp[satisfies_literal_def,interp_lit_def,pos_imp_int_pos]>>
      dep_rewrite.DEP_REWRITE_TAC[decode_edge_index_edge]>>
      fs[SUBSET_DEF,symmetric_def]))
QED

Theorem build_fml_wf:
  ∀ls id acc.
  wf_fml acc ∧ (∀x. MEM x ls ⇒ ¬MEM 0 x) ⇒
  wf_fml (build_fml id ls acc)
Proof
  Induct>>fs[build_fml_def]>>rw[]>>
  first_x_assum match_mp_tac>>
  fs[]>>
  match_mp_tac wf_fml_insert>>
  simp[wf_clause_def,QSORT_MEM]>>
  match_mp_tac QSORT_SORTED>>
  fs[transitive_def,total_def]>>
  intLib.ARITH_TAC
QED

Theorem clique_edges_nonzero:
  ∀ls.
  (∀m. MEM m ls ⇒ m < n) ∧
  ALL_DISTINCT ls ⇒
  ¬MEM 0 (clique_edges n ls)
Proof
  Induct>>rw[clique_edges_def]>>
  rw[MEM_MAP]>>
  Cases_on`MEM y ls`>>fs[]>>
  `h ≠ y` by metis_tac[]>>
  drule index_edge_neq_0>>
  disch_then(qspec_then`n` mp_tac)>>fs[]
QED

Theorem ramsey_lrat_wf:
  wf_fml (ramsey_lrat k n)
Proof
  rw[ramsey_lrat_def]>>
  match_mp_tac build_fml_wf>>fs[MEM_MAP,PULL_EXISTS]>>
  simp[wf_fml_def,values_def,lookup_def]>>
  rw[]>>simp[MEM_MAP]>>
  match_mp_tac clique_edges_nonzero>>
  drule choose_ALL_DISTINCT>>fs[]>>
  drule choose_correct2>>fs[SUBSET_DEF]
QED

(*
Theorem not_is_ramsey_3_5:
  ¬is_ramsey 3 5
Proof
  cheat
QED

Theorem is_ramsey_3_6:
  is_ramsey 3 6
Proof
  rw[is_ramsey_def]>>
  cheat
QED

Theorem is_ramsey_4_18:
  is_ramsey 4 18
Proof
  rw[is_ramsey_def]>>
  cheat
QED
*)

val _ = export_theory ();
