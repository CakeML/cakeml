(*
   Defining the Ramsey number and SAT encoding
*)
open preamble miscTheory lratTheory satSemTheory;

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

(* all lists of choosing k items from a list slowly *)
val choose_def = Define`
  (choose _ 0 = [[]]) ∧
  (choose [] k = []) ∧
  (choose (x::xs) (SUC k) =
    (MAP (λls. x::ls) (choose xs k)) ++ choose xs (SUC k))`

val choose_ind = (fetch "-" "choose_ind")

Theorem choose_MEM:
  ∀ls k x y.
  MEM x y ∧ MEM y (choose ls k) ⇒ MEM x ls
Proof
  ho_match_mp_tac choose_ind>>rw[choose_def]>>fs[MEM_MAP]
  >-
    (Cases_on`x'=x`>>fs[]>>
    last_x_assum match_mp_tac>>
    metis_tac[])
  >>
  metis_tac[]
QED

Theorem SORTED_PRE:
  ∀ls.
  EVERY (λx. x > 0n) ls ∧
  SORTED $< ls ⇒
  SORTED $< (MAP PRE ls)
Proof
  rw[]>>dep_rewrite.DEP_REWRITE_TAC[sorted_map]>>
  simp[transitive_def,inv_image_def]>>
  match_mp_tac SORTED_weaken>>
  asm_exists_tac>>fs[]>>
  rw[]>>fs[EVERY_MEM]>>
  res_tac>>fs[INV_PRE_LESS]
QED

Theorem choose_complete:
  ∀ls k indices.
  SORTED $< indices ∧
  LENGTH indices = k ∧
  EVERY (λi. i < LENGTH ls) indices ⇒
  MEM (MAP (λi. EL i ls) indices) (choose ls k)
Proof
  ho_match_mp_tac choose_ind>>
  rw[choose_def]>>
  Cases_on`indices`>>fs[]>>
  fs[MEM_MAP]>>
  qpat_x_assum`SORTED _ (_::_)` mp_tac>>
  dep_rewrite.DEP_REWRITE_TAC [SORTED_EQ]>>
  simp[transitive_def]>>
  strip_tac>>
  Cases_on`h=0`>>
  fs[]
  >-
    (last_x_assum(qspec_then`MAP PRE t` mp_tac)>>
    impl_tac>-
      (simp[]>>
      CONJ_TAC >-
        (match_mp_tac SORTED_PRE>>rw[EVERY_MEM]>>
        first_x_assum drule>>fs[])>>
      fs[EVERY_MAP,EVERY_MEM]>>rw[]>>
      rpt(first_x_assum drule)>>fs[])>>
    simp[MAP_MAP_o,o_DEF]>>
    qmatch_goalsub_abbrev_tac`MEM a (choose ls k) ⇒ MEM b (choose ls k) ∨ _`>>
    `a = b` by
      (unabbrev_all_tac>>fs[MAP_EQ_f,ADD1]>>
      rw[]>>
      simp[EL_CONS_IF]>>
      first_x_assum drule>>simp[])>>
    simp[])
  >>
    first_x_assum(qspec_then`MAP PRE (h::t)` mp_tac)>>
    impl_tac>-
      (CONJ_TAC >-
        (match_mp_tac SORTED_PRE>>fs[]>>
        dep_rewrite.DEP_REWRITE_TAC [SORTED_EQ]>>
        simp[transitive_def,EVERY_MEM]>>
        rw[]>>
        first_x_assum drule>>fs[])>>
      fs[EVERY_MAP,EVERY_MEM,ADD1]>>
      rw[]>>
      rpt(first_x_assum drule)>>fs[])>>
    simp[MAP_MAP_o,o_DEF]>>
    qmatch_goalsub_abbrev_tac`MEM a (choose ls _) ⇒ _  ∨ MEM b (choose ls _)`>>
    `a = b` by
      (unabbrev_all_tac>>fs[MAP_EQ_f,ADD1]>>
      rw[]>>
      simp[EL_CONS_IF]>>
      first_x_assum drule>>simp[PRE_SUB1])>>
    simp[]
QED

Theorem choose_LENGTH:
  ∀ls k x.
  MEM x (choose ls k) ⇒ LENGTH x = k
Proof
  ho_match_mp_tac choose_ind>>rw[choose_def]>>fs[MEM_MAP]
QED

Theorem choose_ALL_DISTINCT:
  ∀ls k x.
  ALL_DISTINCT ls ∧
  MEM x (choose ls k) ⇒ ALL_DISTINCT x
Proof
  ho_match_mp_tac choose_ind>>rw[choose_def]>>fs[MEM_MAP]>>
  metis_tac[choose_MEM]
QED

Theorem choose_ALL_DISTINCT2:
  ∀ls k.
  ALL_DISTINCT ls ==>
  ALL_DISTINCT (choose ls k)
Proof
  ho_match_mp_tac choose_ind>>rw[choose_def]>>
  fs[ALL_DISTINCT_APPEND]>>
  CONJ_TAC >-
    (match_mp_tac ALL_DISTINCT_MAP_INJ>>fs[])>>
  simp[MEM_MAP,PULL_EXISTS]>>rw[]>>
  CCONTR_TAC>>fs[]>>
  imp_res_tac choose_MEM>>fs[]
QED

Theorem choose_sorted:
  ∀ls k x.
  SORTED $<= (ls:num list) ∧
  MEM x (choose ls k) ⇒ SORTED $<= x
Proof
  ho_match_mp_tac choose_ind>>rw[choose_def]>>fs[MEM_MAP]>>
  qpat_x_assum`SORTED _ (_::_)` mp_tac>>
  dep_rewrite.DEP_REWRITE_TAC [SORTED_EQ]>>
  simp[transitive_def]>>
  rw[]>>last_x_assum drule>>
  disch_then drule>>fs[]>>
  metis_tac[choose_MEM]
QED

Theorem choose_count_correct:
  MEM x (choose (COUNT_LIST n) k) ⇒
  set x ⊆ count n ∧ CARD (set x) = k ∧
  SORTED $<= x ∧ ALL_DISTINCT x
Proof
  rw[]
  >-
    (simp[SUBSET_DEF]>>
    metis_tac[MEM_COUNT_LIST,choose_MEM])
  >-
    (dep_rewrite.DEP_REWRITE_TAC [ALL_DISTINCT_CARD_LIST_TO_SET]>>
    metis_tac[choose_LENGTH,all_distinct_count_list,choose_ALL_DISTINCT])
  >-
    (`SORTED $<= (COUNT_LIST n)` by fs[sorted_count_list]>>
    metis_tac[choose_sorted])
  >>
    metis_tac[all_distinct_count_list,choose_ALL_DISTINCT]
QED

(*
  construct index in and out

  0 1 2 3
0   1 2 3
1     4 5
2       6
3

*)

val transpose_def = Define`
  transpose ls = MAP (λ(a,b).(b,a)) ls`

Theorem MEM_transpose:
   MEM (y,x) (transpose ls) ⇔ MEM (x,y) ls
Proof
  rw[transpose_def,MEM_MAP,EXISTS_PROD]
QED

Theorem MAP_transpose:
  MAP FST (transpose ls) = MAP SND ls ∧
  MAP SND (transpose ls) = MAP FST ls
Proof
  rw[transpose_def,MAP_MAP_o,o_DEF,MAP_EQ_f]>>
  pairarg_tac>>fs[]
QED

Theorem ALOOKUP_transpose:
  ALL_DISTINCT (MAP FST ls) ∧ ALL_DISTINCT (MAP SND ls) ⇒
  (ALOOKUP ls x = SOME v ⇔ ALOOKUP (transpose ls) v = SOME x)
Proof
  rw[EQ_IMP_THM]
  >-
    (`MEM (x,v) ls` by
      metis_tac[MEM_ALOOKUP]>>
    fs[MEM_transpose]>>
    fs[Once (GSYM MEM_transpose)]>>
    match_mp_tac ALOOKUP_ALL_DISTINCT_MEM>>
    simp[MAP_transpose])
  >>
    (`MEM (v,x) (transpose ls)` by
        (dep_rewrite.DEP_REWRITE_TAC[MEM_ALOOKUP]>>
        fs[MAP_transpose])>>
    fs[MEM_transpose]>>
    match_mp_tac ALOOKUP_ALL_DISTINCT_MEM>>
    fs[])
QED

val encoder_def = Define`
  encoder ls = λa b.
  case ALOOKUP ls [a;b] of NONE => 1n | SOME v => v`

val clique_edges_def = Define`
  (clique_edges (f:num->num->num) [] = []) ∧
  (clique_edges f (x::xs) =
  MAP (f x) xs ++ clique_edges f xs)`

val build_fml_def = Define`
  (build_fml (id:num) [] (acc:ccnf) = acc) ∧
  (build_fml id (cl::cls) acc =
  build_fml (id+1) cls (insert id cl acc))`

val ramsey_lrat_def = Define`
  ramsey_lrat k n =
  let ls = choose (COUNT_LIST n) k in
  let pairs = transpose (enumerate 1n (choose (COUNT_LIST n) 2)) in
  let enc = encoder pairs in
  let cli = MAP (clique_edges enc) ls in
  build_fml 1 (MAP (λns. MAP (λn. &n:int) ns) cli ++ MAP (λns. MAP (λn. -&n:int) ns) cli) LN`

val decoder_def = Define`
  decoder ls = λn.
  case ALOOKUP ls n of NONE => (0n,0n) | SOME [a;b] => (a,b) | _ => (0,0)`

Theorem decoder_encoder:
  MEM [a;b] (MAP FST ls) ∧ ALL_DISTINCT (MAP FST ls) ∧ ALL_DISTINCT (MAP SND ls) ⇒
  decoder (transpose ls) (encoder ls a b) = (a,b)
Proof
  rw[encoder_def,decoder_def]>>
  `∃v. MEM ([a;b],v) ls` by
    (fs[MEM_MAP]>>Cases_on`y`>>fs[]>>
    metis_tac[])>>
  `MEM (v,[a;b]) (transpose ls)` by
    fs[MEM_transpose]>>
  rfs[MEM_ALOOKUP]>>
  `ALL_DISTINCT (MAP FST (transpose ls))` by
    fs[MAP_transpose]>>
  fs[MEM_ALOOKUP]
QED

Theorem transpose_transpose:
  transpose(transpose ls) = ls
Proof
  rw[transpose_def,MAP_MAP_o,o_DEF,MAP_EQ_ID]>>
  Cases_on`x`>>simp[]
QED

Theorem decoder_encoder2:
  MEM [a;b] (MAP SND ls) ∧ ALL_DISTINCT (MAP FST ls) ∧ ALL_DISTINCT (MAP SND ls) ⇒
  decoder ls (encoder (transpose ls) a b) = (a,b)
Proof
  rw[]>>
  simp[Once (GSYM transpose_transpose)]>>
  match_mp_tac decoder_encoder>>
  fs[MAP_transpose]
QED

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
  ∀ls f a b.
  MEM a ls ∧ MEM b ls ∧ a ≠ b ⇒
  MEM (f a b) (clique_edges f ls) ∨
  MEM (f b a) (clique_edges f ls)
Proof
  Induct>>rw[clique_edges_def]>>
  fs[MEM_MAP]>>
  metis_tac[]
QED

Theorem clique_edges_SORTED_MEM:
  ∀ls f a b.
  SORTED $<= ls ∧ a < b ∧
  MEM a ls ∧ MEM b ls ⇒
  MEM (f a b) (clique_edges f ls)
Proof
  Induct>>rw[clique_edges_def]>>
  fs[MEM_MAP]
  >- metis_tac[]>>
  qpat_x_assum`SORTED _ (_::_)` mp_tac>>
  dep_rewrite.DEP_REWRITE_TAC [SORTED_EQ]>>
  simp[transitive_def]>>
  rw[]>>fs[]>>
  first_x_assum drule >>
  fs[]
QED

Theorem clique_edges_complete:
  ∀ls f n.
  MEM n (clique_edges f ls) ∧
  ALL_DISTINCT ls ==>
  ∃a b.
  MEM a ls ∧ MEM b ls ∧ a ≠ b ∧
  n = f a b
Proof
  Induct>>rw[clique_edges_def]>>
  fs[MEM_MAP]>>
  metis_tac[]
QED

Theorem clique_edges_SORTED_complete:
  ∀ls f n.
  SORTED $< ls ∧
  MEM n (clique_edges f ls) ==>
  ∃a b.
  MEM a ls ∧ MEM b ls ∧ a < b ∧
  n = f a b
Proof
  Induct>>rw[clique_edges_def]>>
  fs[MEM_MAP]>>
  qpat_x_assum`SORTED _ (_::_)` mp_tac>>
  dep_rewrite.DEP_REWRITE_TAC [SORTED_EQ]>>
  simp[transitive_def]>>
  rw[]>>fs[]>>
  first_x_assum drule >> rw[]>>
  metis_tac[]
QED

Theorem pos_imp_int_pos:
  x:num > 0 ⇒
  &x > 0:int ∧
  ¬(-&x > 0:int)
Proof
  intLib.ARITH_TAC
QED

Theorem ALL_DISTINCT_MAP_FST_enumerate:
  ∀ls n.
  ALL_DISTINCT (MAP FST (enumerate n ls))
Proof
  Induct>>rw[enumerate_def]>>
  CCONTR_TAC>>fs[MEM_MAP]>>
  Cases_on`y`>>fs[MEM_EL]>>
  fs[LENGTH_enumerate]>>
  rfs[EL_enumerate]
QED

Theorem MAP_FST_enumerate:
  ∀ls.
  MAP FST (enumerate n ls) = MAP (λm. m + n) (COUNT_LIST (LENGTH ls))
Proof
  rw[LIST_EQ_REWRITE]>>fs[LENGTH_enumerate,LENGTH_COUNT_LIST]>>
  fs[EL_MAP,LENGTH_enumerate,LENGTH_COUNT_LIST]>>
  simp[EL_COUNT_LIST,EL_enumerate]
QED

Theorem MAP_SND_enumerate:
  ∀ls n.
  MAP SND (enumerate n ls) = ls
Proof
  Induct>>rw[enumerate_def]
QED

Theorem encoder_pos:
  EVERY (λx. x ≠ 0) (MAP SND ls) ⇒
  encoder ls a b > 0n
Proof
  rw[encoder_def]>>fs[EVERY_MAP,EVERY_MEM]>>
  TOP_CASE_TAC>>fs[]>>
  drule ALOOKUP_MEM>>
  rw[]>>first_x_assum drule>>
  fs[]
QED

Theorem choose_pairs_correct:
  b < n ∧ a < b ⇒
  MEM [a;b] (choose (COUNT_LIST n) 2)
Proof
  rw[]>>
  qspecl_then [`COUNT_LIST n`,`2`,`[a;b]`] mp_tac choose_complete>>
  simp[EL_COUNT_LIST]>>
  disch_then match_mp_tac>>
  fs[SORTED_DEF,LENGTH_COUNT_LIST]
QED

Theorem ramsey_lrat_correct:
  unsatisfiable (interp (ramsey_lrat k n)) ⇒
  is_ramsey k n
Proof
  rw[is_ramsey_def,unsatisfiable_def,satisfiable_def]>>
  CCONTR_TAC>>fs[]>>
  last_x_assum mp_tac>>simp[]>>
  simp[ramsey_lrat_def]>>
  qmatch_goalsub_abbrev_tac`encoder (transpose ls)`>>
  `ALL_DISTINCT (MAP FST ls)` by
    simp[Abbr`ls`,ALL_DISTINCT_MAP_FST_enumerate]>>
  `ALL_DISTINCT (MAP SND ls)` by
    (simp[Abbr`ls`,MAP_SND_enumerate]>>
    match_mp_tac choose_ALL_DISTINCT2>>
    metis_tac[all_distinct_count_list])>>
  `!a b. encoder (transpose ls) a b > 0` by
    (rw[]>>match_mp_tac encoder_pos>>
    fs[MAP_transpose,Abbr`ls`,MAP_FST_enumerate]>>
    simp[EVERY_MEM,MEM_MAP])>>
  `!a b. b < n ∧ a < b ⇒ MEM [a;b] (MAP SND ls)` by
    (fs[Abbr`ls`,MAP_SND_enumerate]>>
    metis_tac[choose_pairs_correct])>>
  dep_rewrite.DEP_REWRITE_TAC[interp_build_fml]>>
  simp[]>>
  simp[satisfies_union,MAP_MAP_o]>>
  simp[LIST_TO_SET_MAP,satisfies_def,PULL_EXISTS]>>
  qexists_tac`λm. (UNCURRY e) (decoder ls m)`>>
  rw[]
  >- (
    drule choose_count_correct>>fs[]>>rw[]>>
    first_x_assum(qspec_then `set x` assume_tac)>>rfs[]>>
    simp[interp_cclause_def,LIST_TO_SET_MAP,satisfies_clause_def,PULL_EXISTS]>>
    pop_assum(qspec_then`F` assume_tac)>>fs[]>>
    fs[is_clique_def]>>
    `x' < y ∨ y < x'` by fs[]>>
    drule clique_edges_SORTED_MEM>>
    rpt(disch_then drule)>>
    disch_then (qspec_then `encoder (transpose ls)` assume_tac)>>
    asm_exists_tac>>fs[]
    >-
      (`encoder (transpose ls) x' y > 0` by metis_tac[]>>
      simp[satisfies_literal_def,interp_lit_def,pos_imp_int_pos]>>
      dep_rewrite.DEP_REWRITE_TAC [decoder_encoder2]>>
      simp[]>>
      fs[SUBSET_DEF])
    >>
      `encoder (transpose ls) y x' > 0` by metis_tac[]>>
      simp[satisfies_literal_def,interp_lit_def,pos_imp_int_pos]>>
      dep_rewrite.DEP_REWRITE_TAC [decoder_encoder2]>>
      simp[]>>fs[symmetric_def]>>
      fs[SUBSET_DEF])
  >>
    drule choose_count_correct>>fs[]>>rw[]>>
    first_x_assum(qspec_then `set x` assume_tac)>>rfs[]>>
    simp[interp_cclause_def,LIST_TO_SET_MAP,satisfies_clause_def,PULL_EXISTS]>>
    pop_assum(qspec_then`T` assume_tac)>>fs[]>>
    fs[is_clique_def]>>
    `x' < y ∨ y < x'` by fs[]>>
    drule clique_edges_SORTED_MEM>>
    rpt(disch_then drule)>>
    disch_then (qspec_then `encoder (transpose ls)` assume_tac)>>
    asm_exists_tac>>fs[]
    >-
      (`encoder (transpose ls) x' y > 0` by metis_tac[]>>
      simp[satisfies_literal_def,interp_lit_def,pos_imp_int_pos]>>
      dep_rewrite.DEP_REWRITE_TAC [decoder_encoder2]>>
      fs[SUBSET_DEF])
    >>
      (`encoder (transpose ls) y x' > 0` by metis_tac[]>>
      simp[satisfies_literal_def,interp_lit_def,pos_imp_int_pos]>>
      dep_rewrite.DEP_REWRITE_TAC [decoder_encoder2]>>
      simp[]>>fs[symmetric_def]>>
      fs[SUBSET_DEF])
QED

Theorem build_fml_wf:
  ∀ls id acc.
  wf_fml acc ∧ EVERY wf_clause ls ⇒
  wf_fml (build_fml id ls acc)
Proof
  Induct>>fs[build_fml_def]>>rw[]>>
  first_x_assum match_mp_tac>>
  fs[]>>
  match_mp_tac wf_fml_insert>>
  simp[wf_clause_def]
QED

Theorem clique_edges_nonzero:
  ∀ls.
  EVERY (λx. x ≠ 0) (MAP SND x) ⇒
  ¬MEM 0 (clique_edges (encoder x) ls)
Proof
  Induct>>rw[clique_edges_def]>>
  rw[MEM_MAP]>>
  `encoder x h y > 0` by
    metis_tac[encoder_pos]>>
  fs[]
QED

Theorem ramsey_lrat_wf:
  wf_fml (ramsey_lrat k n)
Proof
  rw[ramsey_lrat_def]>>
  match_mp_tac build_fml_wf>>fs[MEM_MAP,PULL_EXISTS]>>
  simp[wf_fml_def,values_def,lookup_def,EVERY_MEM,MEM_MAP,PULL_EXISTS]>>
  rw[]>>simp[wf_clause_def,MEM_MAP]>>
  match_mp_tac clique_edges_nonzero>>
  simp[MAP_transpose,MAP_FST_enumerate]>>
  simp[EVERY_MAP]
QED

(*
  Check that ramsey number 4 is not 17
*)
val index_edge_def = Define`
  index_edge n x y =
    n * x + (y:num)`

val fast_ramsey_lrat_def = Define`
  fast_ramsey_lrat k n =
  let ls = choose (COUNT_LIST n) k in
  let enc = index_edge n in
  let cli = MAP (clique_edges enc) ls in
  build_fml 1 (MAP (λns. MAP (λn. &n:int) ns) cli ++ MAP (λns. MAP (λn. -&n:int) ns) cli) LN`

Theorem fast_ramsey_lrat_correct:
  satisfiable (interp (fast_ramsey_lrat k n)) ⇒
  ¬(is_ramsey k n)
Proof
  rw[is_ramsey_def,satisfiable_def]>>
  qexists_tac`λa b. if a < b then w (index_edge n a b) else w (index_edge n b a)`>>
  CONJ_TAC >-
    (simp[symmetric_def]>>rw[EQ_IMP_THM]>>
    `a = b` by fs[]>>fs[])>>
  rw[]>>
  CCONTR_TAC>>fs[]>>
  last_x_assum mp_tac>>simp[fast_ramsey_lrat_def]>>
  dep_rewrite.DEP_REWRITE_TAC[interp_build_fml]>>
  simp[satisfies_union,MAP_MAP_o]>>
  simp[LIST_TO_SET_MAP,satisfies_def,PULL_EXISTS]>>
  `FINITE (count n)` by fs[]>>
  `FINITE t` by metis_tac[ SUBSET_FINITE]>>
  `PERM (SET_TO_LIST t) (QSORT $<= (SET_TO_LIST t))` by
        metis_tac[QSORT_PERM]>>
  `ALL_DISTINCT (QSORT $<= (SET_TO_LIST t))` by
     (pop_assum (assume_tac o GSYM o MATCH_MP ALL_DISTINCT_PERM)>>
     fs[])>>
  `LENGTH (SET_TO_LIST t) = k` by fs[SET_TO_LIST_CARD]>>
  `SORTED $< (QSORT $<= (SET_TO_LIST t))` by
    (`SORTED $<= (QSORT $<= (SET_TO_LIST t))` by
          (match_mp_tac QSORT_SORTED>>
          simp[transitive_def,total_def])>>
        match_mp_tac ALL_DISTINCT_SORTED_WEAKEN>>simp[]>>
        qexists_tac`$<=`>>simp[])>>
  `MEM (QSORT $<= (SET_TO_LIST t)) (choose (COUNT_LIST n) k)` by
    (qspecl_then [`COUNT_LIST n`,`k`,`QSORT $<= (SET_TO_LIST t)`] mp_tac choose_complete>>
    simp[]>>impl_tac>-
      (CONJ_TAC >-
        metis_tac[PERM_LENGTH]>>
      simp[EVERY_MEM,QSORT_MEM]>>
      fs[SUBSET_DEF,LENGTH_COUNT_LIST])>>
    qmatch_goalsub_abbrev_tac`MEM aa _ ⇒ MEM bb _`>>
    `aa=bb` by
      (unabbrev_all_tac>>fs[MAP_EQ_ID,QSORT_MEM]>>
      rw[]>>
      match_mp_tac EL_COUNT_LIST>>fs[SUBSET_DEF])>>
    simp[])>>
  simp[GSYM EXISTS_OR_THM]>>
  qexists_tac`QSORT $<= (SET_TO_LIST t)`>>simp[]>>
  Cases_on`b`>>fs[]
  >-
    (DISJ2_TAC>>
    fs[is_clique_def]>>
    simp[satisfies_clause_def]>>rw[]>>
    simp[interp_cclause_def]>>CCONTR_TAC>>
    fs[MEM_MAP]>>
    rw[]>>
    fs[interp_lit_def]>>
    `n' > 0` by fs[]>>
    drule pos_imp_int_pos>>
    strip_tac>>fs[satisfies_literal_def]>>
    drule clique_edges_SORTED_complete>>
    disch_then drule>>
    strip_tac>>rfs[]>>
    fs[QSORT_MEM]>>
    rfs[MEM_SET_TO_LIST]>>
    `a ≠ b` by fs[]>>
    metis_tac[])
  >>
    DISJ1_TAC>>
    fs[is_clique_def]>>
    simp[satisfies_clause_def]>>rw[]>>
    simp[interp_cclause_def]>>CCONTR_TAC>>
    fs[MEM_MAP]>>
    rw[]>>
    fs[interp_lit_def]>>
    `n' > 0` by fs[]>>
    drule pos_imp_int_pos>>
    strip_tac>>fs[satisfies_literal_def]>>
    drule clique_edges_SORTED_complete>>
    disch_then drule>>
    strip_tac>>rfs[]>>
    fs[QSORT_MEM]>>
    rfs[MEM_SET_TO_LIST]>>
    `a ≠ b` by fs[]>>
    metis_tac[]
QED

val check_lit_def = Define`
  check_lit (asg:num->bool) lit =
  if lit < 0:int then
    ¬ asg (Num (-lit))
  else
    asg (Num lit)`

val check_clause_def = Define`
  (check_clause asg [] = F) ∧
  (check_clause asg (x::xs) =
    if x = 0 then check_clause asg xs else
    (check_lit asg x ∨ check_clause asg xs))`

val check_sat_def = Define`
  check_sat asg fml =
  let ls = MAP SND (toAList fml) in
  EVERY (check_clause asg) ls`

Theorem check_lit_satisfies_literal:
  check_lit asg h ∧ h ≠ 0 ⇒
  satisfies_literal asg (interp_lit h)
Proof
  rw[check_lit_def,satisfies_literal_def,interp_lit_def]
  >- `F` by intLib.ARITH_TAC
  >- (`-h = ABS h` by intLib.ARITH_TAC>>
    metis_tac[])
  >-
    (`h = ABS h` by intLib.ARITH_TAC>>
    metis_tac[])
  >>
    `h=0` by intLib.ARITH_TAC>>fs[]
QED

Theorem check_clause_satisfies_clause:
  ∀c.
  check_clause asg c ⇒
  satisfies_clause asg (interp_cclause c)
Proof
  Induct>>rw[check_clause_def]>>fs[]>>
  simp[Once interp_cclause_cons,satisfies_clause_union]>>
  DISJ1_TAC>>
  simp[satisfies_clause_def,interp_cclause_def]>>
  metis_tac[check_lit_satisfies_literal]
QED

Theorem check_sat_satisfies:
  check_sat asg fml ⇒
  satisfies asg (interp fml)
Proof
  rw[check_sat_def,satisfies_def,interp_def,values_def]>>
  fs[EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD,MEM_toAList]>>
  first_x_assum drule>>fs[]>>
  metis_tac[check_clause_satisfies_clause]
QED

(* Ramsey number 3 is not 5 *)

val sol = rconc (EVAL ``
  FOLDR (λn t. insert n () t) LN
  [1; 3; 5; 6; 7; 10; 11; 12; 14; 15; 16; 17; 18; 19]``)

val solf_def = Define`
  solf n = case lookup n ^sol of NONE => F | _ => T`

val thm = EVAL ``check_sat solf (fast_ramsey_lrat 3 5)``;

Theorem not_is_ramsey_3_5:
  ¬(is_ramsey 3 5)
Proof
  match_mp_tac fast_ramsey_lrat_correct>>
  simp[satisfiable_def]>>
  qexists_tac`solf`>>match_mp_tac check_sat_satisfies>>
  simp[thm]
QED

(* Ramsey number 3 is 6 *)

val lrat = ``[
  Delete []; PR 41 [-12; -14; -15] NONE [39; 38; 40; 17] LN; Delete [17];
  PR 42 [-9; -14; -15] NONE [35; 36; 40; 14] LN; Delete [14];
  PR 43 [-5; -14; -15] NONE [30; 29; 40; 8] LN; Delete [40; 8];
  PR 44 [-14; -15] NONE [43; 42; 4; 41; 13; 7; 21] LN;
  Delete [43; 42; 41; 21]; PR 45 [9; 5; 14] NONE [15; 4; 9; 22] LN;
  Delete [22]; PR 46 [12; 5; 14] NONE [18; 7; 9; 25] LN; Delete [25];
  PR 47 [5; -15] NONE [44; 45; 36; 46; 39; 33; 12] LN; Delete [45; 46; 12];
  PR 48 [-12; -15] NONE [47; 30; 27; 39; 6] LN; Delete [39; 6];
  PR 49 [-9; -15] NONE [36; 47; 24; 30; 3] LN; Delete [36; 47; 30; 3];
  PR 50 [-15] NONE [49; 48; 13; 44; 15; 18; 31] LN;
  Delete [49; 48; 44; 31]; PR 51 [12; 9] NONE [50; 19; 16; 13; 32] LN;
  Delete [13; 32]; PR 52 [14; 9] NONE [50; 20; 16; 15; 34] LN;
  Delete [15; 34]; PR 53 [-5; -12; -14] NONE [27; 29; 38; 5] LN;
  Delete [5]; PR 54 [9] NONE [50; 51; 52; 16; 53; 10; 23; 4] LN;
  Delete [51; 52; 16; 53; 23; 4];
  PR 55 [-12; -14] NONE [54; 33; 35; 38; 11] LN; Delete [38; 11];
  PR 56 [5; 12] NONE [50; 10; 19; 7; 26] LN; Delete [7; 26];
  PR 57 [-14] NONE [54; 55; 35; 56; 24; 29; 2] LN;
  Delete [55; 35; 56; 29; 2]; PR 59 [12] NONE [50; 57; 20; 18; 19; 37] LN;
  Delete [18; 19; 37]; PR 61 [-5] NONE [54; 59; 33; 24; 27; 1] LN;
  Delete [33; 24; 27; 1]; PR 65 [] NONE [50; 57; 20; 61; 9; 10; 28] LN
  ]``;

val thm = EVAL ``check_lrat_unsat ^lrat (ramsey_lrat 3 6)``
val thm2 = EVAL ``EVERY wf_lrat ^lrat``

Theorem ramsey_number_3:
  ramsey_number 3 = 6
Proof
  match_mp_tac ramsey_eq>>simp[not_is_ramsey_3_5]>>
  match_mp_tac ramsey_lrat_correct>>
  match_mp_tac (check_lrat_unsat_sound |> SIMP_RULE std_ss [AND_IMP_INTRO])>>
  metis_tac[ramsey_lrat_wf,thm,thm2]
QED

(* Ramsey number 4 is not 17 *)
val sol = rconc (EVAL ``
    FOLDR (λn t. insert n () t) LN [1; 4; 8; 9; 10; 11; 12; 13; 17; 18; 19; 23; 25; 28; 30; 32; 33; 34; 35;
      36; 37; 38; 40; 41; 44; 45; 49; 51; 52; 53; 54; 55; 56; 57; 60; 63; 64;
      66; 68; 69; 70; 71; 72; 73; 78; 79; 81; 82; 85; 86; 87; 88; 89; 90; 91;
      93; 96; 97; 99; 101; 102; 103; 104; 105; 106; 107; 108; 110; 111; 112;
      118; 119; 120; 121; 122; 123; 124; 125; 126; 128; 129; 130; 131; 133;
      134; 135; 136; 137; 138; 139; 140; 141; 142; 143; 144; 146; 148; 150;
      151; 153; 154; 155; 156; 157; 158; 159; 160; 161; 162; 163; 165; 166;
      169; 170; 171; 172; 173; 174; 175; 176; 177; 178; 179; 180; 184; 187;
      188; 189; 190; 191; 192; 193; 194; 195; 196; 197; 198; 199; 203; 204;
      205; 206; 207; 208; 209; 210; 211; 212; 213; 214; 215; 216; 219; 221;
      222; 223; 224; 225; 226; 227; 228; 229; 230; 231; 232; 233; 234; 235;
      236; 237; 238; 239; 240; 241; 242; 243; 244; 245; 246; 247; 248; 249;
      250; 251; 252; 253; 254; 255; 256; 257; 258; 259; 260; 261; 262; 263;
      264; 265; 266; 267; 268; 269; 270]``);

val solf_def = Define`
  solf n = case lookup n ^sol of NONE => F | _ => T`

val thm = EVAL ``check_sat solf (fast_ramsey_lrat 4 17)``;

Theorem not_is_ramsey_4_17:
  ¬(is_ramsey 4 17)
Proof
  match_mp_tac fast_ramsey_lrat_correct>>
  simp[satisfiable_def]>>
  qexists_tac`solf`>>match_mp_tac check_sat_satisfies>>
  simp[thm]
QED

val _ = export_theory ();
