(*
  Packing chromatic number
*)
open preamble satSemTheory lprTheory balanced_mapTheory;

val _ = new_theory "packing";

Definition l1_dist_def:
  l1_dist (x1,y1) (x2,y2) =
    Num (ABS (x1-x2) + ABS (y1-y2))
End

(*
  f is a packing coloring on the set of points D
  - f assigns colors 1 ≤ f p ≤ k
  - Inside the domain D, distinct points with
    the same color c have L1 distance > c
*)
Definition is_dom_packing_col_def:
  is_dom_packing_col f D k ⇔
  (∀p. f p ≥ 1 ∧ f p ≤ k) ∧
  ∀p1 p2.
    p1 ∈ D ∧ p2 ∈ D ∧ p1 ≠ p2 ∧
    f p1 = f p2 ⇒
    l1_dist p1 p2 > f p1
End

(* f is a plane packing coloring iff D is the entire plane *)
Definition is_plane_packing_col_def:
  is_plane_packing_col f k ⇔
  is_dom_packing_col f UNIV k
End

(* ball centered at C of radius r ≥ 1 *)
Definition ball_def:
  ball C r = {p | l1_dist p C ≤ r}
End

Theorem in_ball_translate:
  (a,b) ∈ ball (0,0) r ⇒
  (a+Cx,b+Cy) ∈ ball (Cx,Cy) r
Proof
  rw[ball_def,l1_dist_def]>>
  intLib.ARITH_TAC
QED

Theorem is_dom_packing_translate:
  is_dom_packing_col f (ball C r) k ⇒
  is_dom_packing_col (λ(a,b). f (a + FST C,b + SND C)) (ball (0,0) r) k
Proof
  Cases_on`C`>>rename1`(Cx,Cy)`>>
  simp[is_dom_packing_col_def]>>
  simp[FORALL_PROD]>>
  rw[]>>
  first_x_assum(qspecl_then
    [`p_1 + Cx`,`p_2 + Cy`,
     `p_1' + Cx`,`p_2' + Cy`] mp_tac)>>
  impl_tac>-
    (simp[]>>
    metis_tac[in_ball_translate])>>
  simp[l1_dist_def]>>
  rpt(pop_assum kall_tac)>>
  intLib.ARITH_TAC
QED

Theorem is_dom_packing_subset:
  A ⊆ B ⇒
  is_dom_packing_col f B k ⇒
  is_dom_packing_col f A k
Proof
  rw[is_dom_packing_col_def,SUBSET_DEF]
QED

Theorem is_plane_packing_dom_packing:
  is_plane_packing_col f k ∧ c ≥ 1 ∧ c ≤ k ⇒
  ∃g.
    is_dom_packing_col g (ball (0,0) r) k ∧ g (0,0) = c
Proof
  rw[is_plane_packing_col_def]>>
  Cases_on`∃x y. f (x,y) = c`>>fs[]
  >- (
    (* c is already used *)
    `is_dom_packing_col f (ball (x,y) r) k` by
      (last_x_assum mp_tac>>
      match_mp_tac is_dom_packing_subset>>
      simp[])>>
    imp_res_tac is_dom_packing_translate>>
    asm_exists_tac>>simp[])>>
  Cases_on`∃x y. f (x,y) > c`>>fs[]
  >- (
    (* higher than c *)
    `is_dom_packing_col f (ball (x,y) r) k` by
      (last_x_assum mp_tac>>
      match_mp_tac is_dom_packing_subset>>
      simp[])>>
    imp_res_tac is_dom_packing_translate>>
    qmatch_asmsub_abbrev_tac` _ g (ball _ _) k`>>
    qexists_tac`λp. if g p = f (x,y) then c else g p`>>
    simp[Abbr`g`]>>
    pop_assum mp_tac>>
    qpat_x_assum`is_dom_packing_col _ _ _` kall_tac>>
    qpat_x_assum`is_dom_packing_col _ _ _` kall_tac>>
    fs[is_dom_packing_col_def]>>
    strip_tac>>CONJ_TAC >- rw[]>>
    rw[]
    >- (
      first_x_assum(qspecl_then[`p`,`p'`] mp_tac)>>
      simp[]>>
      qpat_x_assum`_ > _` mp_tac>>
      rpt(pop_assum kall_tac)>> intLib.ARITH_TAC)
    >- (
      Cases_on`p'`>>fs[]>>
      metis_tac[PAIR])
    >- (
      Cases_on`p`>>fs[]>>
      metis_tac[]))>>
  qexists_tac`λp. if p = (0,0) then c else f p`>>
  fs[is_dom_packing_col_def]>>
  rw[]>>
  metis_tac[PAIR]
QED

Definition in_ball_def:
  in_ball r (x,y) <=>
    Num (ABS x + ABS y) ≤ (r:num)
End

(* All vertices within radius r as a list *)
Definition vertices_def:
  vertices r =
  FILTER (in_ball r)
  (FLAT (GENLIST (λi.
    GENLIST (λj. (&i-&r):int,(&j-&r):int) (2*r+1)
    ) (2*r+1)))
End

Theorem in_ball_iff:
  in_ball r p <=> p ∈ ball (0,0) r
Proof
  Cases_on`p`>>EVAL_TAC
QED

Theorem set_vertices:
  set (vertices r) =
  ball (0,0) r
Proof
  rw[vertices_def,ball_def,EXTENSION,MEM_FILTER,MEM_FLAT,MEM_GENLIST,PULL_EXISTS]>>
  Cases_on`x`>>EVAL_TAC>>
  intLib.ARITH_TAC
QED

Theorem MEM_vertices:
  MEM p (vertices r) ⇔
  p ∈ ball (0,0) r
Proof
  rw[set_vertices]
QED

(* x_{c,i,j} means vertex at (i,j) gets color c *)
Definition fix_col_def:
  fix_col k (i,j) =
    GENLIST (λc. INL (c+1,i,j)) k
End

Definition fix_cols_def:
  fix_cols r k =
    MAP (fix_col k) (vertices r)
End

(* Restrict vertices with distance ≤ c in a square from a vertex
  (i,j) to not share color c *)
Definition restrict_col_def:
  restrict_col r c (i,j) =
  let vs =
    GENLIST (λjj. (i,j+ &jj +1:int)) c in
  let rs =
    (FLAT
      (GENLIST (λii.
       (i + &ii + 1:int,j)::
       FLAT (
       GENLIST (λjj.
        [(i + &ii + 1:int,j + &jj + 1);(i + &ii + 1,j - &jj -1)]) (c-ii-1))
    ) c)) in
  let fil = FILTER (in_ball r) (vs ++ rs) in
  MAP (λp. [INR (c,i,j); INR (c,p)]) fil
End

Definition restrict_cols_def:
  restrict_cols r c =
    FLAT (MAP (restrict_col r c) (vertices r))
End

Definition full_restrict_def:
  full_restrict r k =
  FLAT (GENLIST (λc. restrict_cols r (c+1)) k)
End

Definition encode_def:
  encode r k c = fix_cols r k ++ full_restrict r k ++ [[INL (c,0:int,0:int)]]
End

(* Turn a packing coloring into an assignment *)
Definition assg_of_def:
  assg_of f =
  (λ(c,p). f p = c)
End

Theorem satisfies_clause_assg_of_fix_col:
  f p ≥ 1 ∧ f p ≤ k ⇒
  satisfies_clause (assg_of f) (set (fix_col k p ))
Proof
  Cases_on`p`>>
  rw[satisfies_clause_def,assg_of_def,fix_col_def,PULL_EXISTS,MEM_GENLIST,satisfies_literal_def]>>
  qexists_tac`f(q,r)-1`>>fs[]
QED

Theorem satifies_assg_of_fix_cols:
  (∀p. f p ≥ 1 ∧ f p ≤ k) ⇒
  satisfies (assg_of f) (set (MAP set (fix_cols r k)))
Proof
  rw[satisfies_def,MEM_MAP,fix_cols_def]>>
  match_mp_tac satisfies_clause_assg_of_fix_col>>
  metis_tac[]
QED

Theorem satisfies_assg_of_restrict_col:
  g p ≠ c ∨
  (∀p'. p' ∈ ball (0,0) r ∧ p ≠ p' ∧ l1_dist p p' ≤ c ⇒ g p' ≠ c) ⇒
  satisfies (assg_of g) (set (MAP set (restrict_col r c p)))
Proof
  Cases_on`g p = c`>>
  strip_tac>>fs[]>>
  rw[satisfies_def,MEM_MAP]>>
  Cases_on`p`>>
  gvs[restrict_col_def,MEM_MAP,MEM_FILTER,MEM_FLAT,MEM_GENLIST,satisfies_clause_def,assg_of_def,in_ball_iff]>>
  simp[RIGHT_AND_OVER_OR,PULL_EXISTS,EXISTS_OR_THM,satisfies_literal_def]>>
  first_x_assum match_mp_tac>>fs[l1_dist_def]>>
  intLib.ARITH_TAC
QED

Theorem satisfies_set_FLAT:
  satisfies w (set (FLAT ls)) =
  (∀x. MEM x ls ⇒ satisfies w (set x))
Proof
  rw[satisfies_def,MEM_FLAT]>>
  metis_tac[]
QED

Theorem satisfies_assg_of_encode:
  is_dom_packing_col g (ball (0,0) r) k ∧ g (0,0) = c ⇒
  satisfies (assg_of g) (set (MAP set (encode r k c)))
Proof
  rw[encode_def,is_dom_packing_col_def]>>
  simp[satisfies_union]>>rw[]
  >-
    metis_tac[satifies_assg_of_fix_cols]
  >- (
    simp[full_restrict_def,MAP_FLAT,satisfies_set_FLAT,MEM_MAP,PULL_EXISTS,restrict_cols_def,MEM_GENLIST]>>
    rw[]>>
    match_mp_tac (GEN_ALL satisfies_assg_of_restrict_col)>>
    rw[]>>
    CCONTR_TAC>>fs[MEM_vertices]>>
    metis_tac[NOT_GREATER])>>
  simp[satisfies_def,satisfies_clause_def,satisfies_literal_def,assg_of_def]
QED

(* Turn an encoded CNF into numbers *)
Definition remap_var_def:
  remap_var cmp v (next:num,mv) =
  case lookup cmp v mv of
    NONE =>
      (next, (next+1, insert cmp v next mv))
  | SOME n => (n, (next,mv))
End

Definition remap_lit_def:
  (remap_lit cmp (INL v) nmv =
    let (v', nmv') = remap_var cmp v nmv in
    (&v':int, nmv')) ∧
  (remap_lit cmp (INR v) nmv =
    let (v', nmv') = remap_var cmp v nmv in
    (-&v', nmv'))
End

Definition remap_clause_def:
  (remap_clause cmp [] nmv = ([],nmv)) ∧
  (remap_clause cmp (l::ls) nmv =
    let (l',nmv') = remap_lit cmp l nmv in
    let (ls',nmv'') = remap_clause cmp ls nmv' in
    (l'::ls',nmv''))
End

Definition remap_fml_def:
  (remap_fml cmp [] nmv = ([],nmv)) ∧
  (remap_fml cmp (c::cs) nmv =
    let (c',nmv') = remap_clause cmp c nmv in
    let (cs',nmv'') = remap_fml cmp cs nmv' in
    (c'::cs',nmv''))
End

Definition inj_map_def:
  inj_map cmp (n:num) mv ⇔
  1 ≤ n ∧
  (∀v m. lookup cmp v mv = SOME m ⇒ 1 ≤ m ∧ m < n) ∧
  (∀v v'.
    lookup cmp v mv = lookup cmp v' mv ⇒
    lookup cmp v mv = NONE ∨ v = v')
End

Definition submap_def:
  submap cmp mv mv' ⇔
  (∀x v. lookup cmp x mv = SOME v ⇒ lookup cmp x mv' = SOME v)
End

Theorem remap_var_lookup:
  TotOrd cmp ∧ invariant cmp mv ∧
  inj_map cmp n mv ∧
  remap_var cmp v (n,mv) = (v',n',mv') ⇒
  invariant cmp mv' ∧
  inj_map cmp n' mv' ∧
  lookup cmp v mv' = SOME v' ∧
  submap cmp mv mv'
Proof
  rw[remap_var_def]>>
  imp_res_tac comparisonTheory.TotOrder_imp_good_cmp >>
  every_case_tac>>fs[]>>
  rw[]
  >-
    metis_tac[insert_thm]
  >- (
    fs[inj_map_def]>>rw[]
    >- (
      pop_assum mp_tac>>
      DEP_REWRITE_TAC[lookup_insert]>>
      rw[]>>fs[]>>
      first_x_assum drule>>fs[])
    >- (
      pop_assum mp_tac>>
      DEP_REWRITE_TAC[lookup_insert]>>
      rw[]>>fs[]>>
      first_x_assum drule>>fs[])>>
    pop_assum mp_tac>>
    DEP_REWRITE_TAC[lookup_insert]>>
    fs[]>>rw[]
    >-
      metis_tac[totoTheory.TotOrd]
    >- (
      pop_assum (assume_tac o SYM)>>
      first_x_assum drule>>fs[])>>
    first_x_assum drule>>fs[])
  >- (
    DEP_REWRITE_TAC[lookup_insert]>>
    fs[]>>
    metis_tac[comparisonTheory.good_cmp_def])
  >- (
    rw[submap_def]>>
    DEP_REWRITE_TAC[lookup_insert]>>
    fs[]>>
    rw[]>>
    metis_tac[totoTheory.TotOrd,option_CLAUSES])>>
  rw[submap_def]
QED

Theorem inj_map_select_lookup:
  inj_map cmp n mv ∧
  lookup cmp x mv = SOME v ⇒
  (@x. lookup cmp x mv = SOME v) = x
Proof
  rw[inj_map_def]>>
  `lookup cmp (@x. lookup cmp x mv = SOME v) mv = SOME v` by
    metis_tac[SELECT_THM]>>
  metis_tac[option_CLAUSES]
QED

Theorem ge_1:
  1 ≤ v ⇒ (&v > 0:int) ∧ ¬(-&v' > 0:int)
Proof
  rw[integerTheory.int_gt]
QED

Theorem remap_lit_satisfies_literal:
  ∀l n mv l' n' mv'.
  TotOrd cmp ∧ invariant cmp mv ∧
  inj_map cmp n mv ∧
  remap_lit cmp l (n,mv) = (l',n',mv') ⇒
  invariant cmp mv' ∧
  inj_map cmp n' mv' ∧
  l' ≠ 0 ∧
  (∀r nn. inj_map cmp nn r ∧ submap cmp mv' r ⇒
    (satisfies_literal w l ⇔
    satisfies_literal
     (w o (λv'. @v. lookup cmp v r = SOME v')) (interp_lit l'))) ∧
  submap cmp mv mv'
Proof
  Cases>>simp[remap_lit_def]>>
  ntac 6 strip_tac>>
  pairarg_tac>>gvs[]>>
  drule_all remap_var_lookup>>
  simp[satisfies_literal_def,interp_lit_def]>>
  strip_tac>>
  (CONJ_TAC >- (
    fs[inj_map_def,submap_def]>>
    first_x_assum drule>>
    fs[]))>>
  rw[]>>fs[submap_def]>>
  first_x_assum drule>>
  metis_tac[inj_map_select_lookup,ge_1,inj_map_def]
QED

Theorem submap_trans:
  submap cmp x y ∧ submap cmp y z ⇒ submap cmp x z
Proof
  rw[submap_def]
QED

Theorem remap_clause_satisfies_clause:
  ∀cl n mv cl' n' mv'.
  TotOrd cmp ∧ invariant cmp mv ∧
  inj_map cmp n mv ∧
  remap_clause cmp cl (n,mv) = (cl',n',mv') ⇒
  invariant cmp mv' ∧
  inj_map cmp n' mv' ∧
  wf_clause cl' ∧
  (∀r nn. inj_map cmp nn r ∧ submap cmp mv' r ⇒
    (satisfies_clause w (set cl) ⇔
    satisfies_clause
     (w o (λv'. @v. lookup cmp v r = SOME v')) (interp_cclause cl'))) ∧
  submap cmp mv mv'
Proof
  Induct>>simp[remap_clause_def]
  >-
    simp[satisfies_clause_def,submap_def]>>
  ntac 7 strip_tac>>
  rpt (pairarg_tac>>gvs[])>>
  Cases_on`nmv'`>>
  drule_all remap_lit_satisfies_literal>>
  strip_tac>>gs[GSYM PULL_FORALL]>>
  first_x_assum drule_all>>
  strip_tac>>
  rw[]
  >-
    fs[wf_clause_def]
  >- (
    simp[satisfies_clause_INSERT,Once interp_cclause_cons,Once interp_cclause_def,satisfies_clause_union]>>
    first_x_assum drule_all>>
    simp[]>>
    disch_then kall_tac>>
    first_x_assum drule>>
    impl_tac>-
      metis_tac[submap_trans]>>
    simp[satisfies_clause_def])>>
  metis_tac[submap_trans]
QED

Theorem remap_fml_satisfies:
  ∀fml n mv fml' n' mv'.
  TotOrd cmp ∧ invariant cmp mv ∧
  inj_map cmp n mv ∧
  remap_fml cmp fml (n,mv) = (fml',n',mv') ⇒
  invariant cmp mv' ∧
  inj_map cmp n' mv' ∧
  EVERY wf_clause fml' ∧
  (∀r nn. inj_map cmp nn r ∧ submap cmp mv' r ⇒
    (satisfies w (set (MAP set fml)) ⇔
    satisfies
     (w o (λv'. @v. lookup cmp v r = SOME v')) (interp fml'))) ∧
  submap cmp mv mv'
Proof
  Induct>>simp[remap_fml_def]
  >-
    rw[submap_def,satisfies_def,interp_def]>>
  ntac 7 strip_tac>>
  rpt (pairarg_tac>>gvs[])>>
  Cases_on`nmv'`>>
  drule_all remap_clause_satisfies_clause>>
  strip_tac>>gs[GSYM PULL_FORALL]>>
  first_x_assum drule_all>>
  strip_tac>>
  rw[]
  >- (
    fs[satisfies_INSERT,interp_def]>>
    first_x_assum drule_all>>
    simp[]>>
    disch_then kall_tac>>
    first_x_assum drule>>
    impl_tac>-
      metis_tac[submap_trans]>>
    simp[])>>
  metis_tac[submap_trans]
QED

Definition cmp_num_def:
  cmp_num (n:num) n' =
  if n < n' then Less
  else if n > n' then Greater
  else Equal
End

Definition cmp_int_def:
  cmp_int (i:int) i' =
  if i < i' then Less
  else if i > i' then Greater
  else Equal
End

Definition cmp_pair_def:
  cmp_pair cmpx cmpy (x,y) (x',y') =
  case cmpx x x' of
    Equal => cmpy y y'
  | res => res
End

Definition cmp_nii_def:
  cmp_nii =
  cmp_pair cmp_num (cmp_pair cmp_int cmp_int)
End

Theorem TotOrd_cmp_num:
  TotOrd cmp_num
Proof
  rw[totoTheory.TotOrd,cmp_num_def]>>
  rw[]>>fs[]>>
  every_case_tac>>fs[]
QED

Theorem TotOrd_cmp_int:
  TotOrd cmp_int
Proof
  rw[totoTheory.TotOrd,cmp_int_def]>>
  rw[]>>fs[]>>
  every_case_tac>>fs[]>>
  intLib.ARITH_TAC
QED

Theorem TotOrd_cmp_pair:
  TotOrd cmpx ∧ TotOrd cmpy ⇒
  TotOrd (cmp_pair cmpx cmpy)
Proof
  rw[]>>
  simp[totoTheory.TotOrd]>>reverse (rw[])
  >- (
    Cases_on`x`>>Cases_on`y`>>Cases_on`z`>>
    fs[cmp_pair_def]>>
    every_case_tac>>fs[]>>
    fs[totoTheory.TotOrd]>>
    metis_tac[totoTheory.all_cpn_distinct])>>
  Cases_on`x`>>Cases_on`y`>>simp[cmp_pair_def]>>
  every_case_tac>>
  fs[totoTheory.TotOrd]>>
  metis_tac[totoTheory.all_cpn_distinct]
QED

Definition remap_nii_def:
  remap_nii fml =
  FST (remap_fml cmp_nii fml (1,empty))
End

(* Can prove stronger theorem but not needed here *)
Theorem remap_nii_correct:
  remap_nii fml = fml' ⇒
  EVERY wf_clause fml' ∧
  (satisfiable (set (MAP set fml)) ==> satisfiable (interp fml'))
Proof
  strip_tac>>
  fs[satisfiable_def,remap_nii_def]>>
  `∃a b c. remap_fml cmp_nii fml (1,empty) = (a,b,c)` by
    metis_tac[PAIR]>>
  (drule_at Any) remap_fml_satisfies>>
  simp[GSYM PULL_FORALL]>>
  impl_tac >- (
    simp[inj_map_def,empty_thm]>>
    simp[empty_def,lookup_def,cmp_nii_def]>>
    metis_tac[TotOrd_cmp_pair,TotOrd_cmp_int,TotOrd_cmp_num] )>>
  rw[]>>
  first_x_assum drule>>
  simp[submap_def]>>
  metis_tac[]
QED

Definition full_encode_def:
  full_encode r k c = remap_nii (encode r k c)
End

Theorem unsat_is_plane_packing:
  c ≥ 1 ∧ c ≤ k ∧
  unsatisfiable (interp (full_encode r k c)) ⇒
  ¬ is_plane_packing_col f k
Proof
  rw[]>>CCONTR_TAC>>fs[]>>
  drule_all is_plane_packing_dom_packing>>
  fs[unsatisfiable_def,full_encode_def]>>
  `¬ satisfiable (set (MAP set (encode r k c)))` by
    metis_tac[remap_nii_correct]>>
  fs[satisfiable_def]>>
  metis_tac[satisfies_assg_of_encode]
QED

val _ = export_theory();
