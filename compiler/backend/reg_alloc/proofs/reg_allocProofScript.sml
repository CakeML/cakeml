open preamble state_transformerTheory reg_allocTheory
open sortingTheory;
open ml_monadBaseTheory ml_monadBaseLib;

val _ = new_theory "reg_allocProof"

val _ = ParseExtras.temp_tight_equality();
val _ = monadsyntax.temp_add_monadsyntax()

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

(* Edge from node x to node y, in terms of an adjacency list *)
val has_edge_def = Define`
  has_edge adjls x y ⇔
  x < LENGTH adjls ∧
  y < LENGTH adjls ∧
  MEM y (EL x adjls)`

val undirected_def = Define`
  undirected adjls ⇔
  ∀x y.
    has_edge adjls x y ⇒
    has_edge adjls y x`

(* --- some side properties on the state --- *)
val good_ra_state_def = Define`
  good_ra_state s ⇔
  LENGTH s.adj_ls = s.dim ∧
  LENGTH s.node_tag = s.dim ∧
  LENGTH s.degrees = s.dim ∧
  EVERY (λls. EVERY (λv. v < s.dim) ls) s.adj_ls ∧
  undirected s.adj_ls`

(* --- invariant: no two adjacent nodes have the same colour --- *)
val no_clash_def = Define`
  no_clash adj_ls node_tag ⇔
  ∀x y.
    has_edge adj_ls x y ⇒
    case (EL x node_tag,EL y node_tag) of
      (Fixed n,Fixed m) =>
        n = m ⇒ x = y
    | _ => T`

(* Good preference oracle may only inspect, but not touch the state
   Moreover, it must always select a member of the input list
*)
val good_pref_def = Define`
  good_pref pref ⇔
  ∀n ks s. ?res.
    pref n ks s = (Success res,s) ∧
    case res of
      NONE => T
    | SOME k => MEM k ks`

val msimps = [st_ex_bind_def,st_ex_return_def];

(* Success conditions *)

fun get_thms ty = { case_def = TypeBase.case_def_of ty, nchotomy = TypeBase.nchotomy_of ty };
val case_eq_thms = pair_case_eq::
  List.map (prove_case_eq_thm o get_thms) [``:('a,'b) exc``,``:tag``,``:'a list``,``:'a option``]
  |> LIST_CONJ |> curry save_thm "case_eq_thms"

val tag_case_st = Q.store_thm("tag_case_st",`
  !t.
  (tag_CASE t a b c) f = (tag_CASE t (λn. a n f) (b f) (c f))`,
  Cases>>fs[]);

val list_case_st = Q.store_thm("list_case_st",`
  !t.
  (list_CASE t a b) f = (list_CASE t (a f) (λx y.b x y f))`,
  Cases>>fs[]);

(* TODO: These equational lemmas one ought to be automatic *)
val Msub_eqn = Q.store_thm("Msub_eqn[simp]",`
  ∀e n ls v.
  Msub e n ls =
  if n < LENGTH ls then Success (EL n ls)
                   else Failure e`,
  ho_match_mp_tac Msub_ind>>rw[]>>
  simp[Once Msub_def]>>
  Cases_on`ls`>>fs[]>>
  IF_CASES_TAC>>fs[]>>
  Cases_on`n`>>fs[]);

val node_tag_sub_eqn= Q.store_thm("node_tag_sub_eqn[simp]",`
  node_tag_sub n s =
  if n < LENGTH s.node_tag then
    (Success (EL n s.node_tag),s)
  else
    (Failure (Subscript),s)`,
  rw[node_tag_sub_def]>>
  fs[Marray_sub_def]);

val adj_ls_sub_eqn= Q.store_thm("adj_ls_sub_eqn[simp]",`
  adj_ls_sub n s =
  if n < LENGTH s.adj_ls then
    (Success (EL n s.adj_ls),s)
  else
    (Failure (Subscript),s)`,
  rw[adj_ls_sub_def]>>
  fs[Marray_sub_def]);

val Mupdate_eqn = Q.store_thm("Mupdate_eqn[simp]",`
  ∀e x n ls.
  Mupdate e x n ls =
  if n < LENGTH ls then
    Success (LUPDATE x n ls)
  else
    Failure e`,
  ho_match_mp_tac Mupdate_ind>>rw[]>>
  simp[Once Mupdate_def]>>
  Cases_on`ls`>>fs[]>>
  IF_CASES_TAC>>fs[LUPDATE_def]>>
  Cases_on`n`>>fs[LUPDATE_def]);

val update_node_tag_eqn = Q.store_thm("update_node_tag_eqn[simp]",`
  update_node_tag n t s =
  if n < LENGTH s.node_tag then
     (Success (),s with node_tag := LUPDATE t n s.node_tag)
  else
     (Failure (Subscript),s)`,
  rw[update_node_tag_def]>>
  fs[Marray_update_def]);

val update_adj_ls_eqn = Q.store_thm("update_adj_ls_eqn[simp]",`
  update_adj_ls n t s =
  if n < LENGTH s.adj_ls then
     (Success (),s with adj_ls := LUPDATE t n s.adj_ls)
  else
     (Failure (Subscript),s)`,
  rw[update_adj_ls_def]>>
  fs[Marray_update_def]);

val update_degrees_eqn = Q.store_thm("update_degrees_eqn[simp]",`
  update_degrees n t s =
  if n < LENGTH s.degrees then
     (Success (),s with degrees := LUPDATE t n s.degrees)
  else
     (Failure (Subscript),s)`,
  rw[update_degrees_def]>>
  fs[Marray_update_def]);

val remove_colours_frame = Q.store_thm("remove_colours_frame",`
  ∀adjs ks s res s'.
  remove_colours adjs ks s = (res,s') ⇒
  s = s'`,
  ho_match_mp_tac remove_colours_ind>>rw[remove_colours_def]>>
  fs msimps>>
  pop_assum mp_tac >> IF_CASES_TAC>> simp[]>>
  rw[]>>fs [case_eq_thms,tag_case_st]>>
  rw[]>>fs[]>>
  metis_tac[]);

val remove_colours_success = Q.store_thm("remove_colorus_success",`
  ∀adjs ks s ls s'.
  remove_colours adjs ks s = (Success ls,s') ⇒
  Abbrev(set ls ⊆ set ks ∧
  ∀n. MEM n adjs ∧ n < LENGTH s'.node_tag ⇒
    case EL n s.node_tag of
      Fixed c => ¬MEM c ls
    | _ => T)`,
  ho_match_mp_tac remove_colours_ind>>rw[remove_colours_def]>>
  fs msimps
  >-
    (rw[markerTheory.Abbrev_def]>>TOP_CASE_TAC>>fs[])
  >-
    rw[markerTheory.Abbrev_def,SUBSET_DEF]
  >>
  pop_assum mp_tac>>IF_CASES_TAC>>fs[]>>
  strip_tac>>
  fs[case_eq_thms,tag_case_st]>>rw[]>>
  first_x_assum drule>>
  strip_tac>>
  fs[markerTheory.Abbrev_def]>>
  rw[]>>fs[]
  >-
    (fs[SUBSET_DEF]>>
    rw[]>>first_x_assum drule>>
    IF_CASES_TAC>>rw[]>>fs[MEM_FILTER])
  >>
    CCONTR_TAC>>
    fs[SUBSET_DEF]>>
    first_x_assum drule>>
    IF_CASES_TAC>>rw[]>>fs[MEM_FILTER]);

val no_clash_LUPDATE_Stemp = Q.prove(`
  no_clash adjls tags ⇒
  no_clash adjls (LUPDATE Stemp n tags)`,
  rw[no_clash_def]>>
  fs[EL_LUPDATE]>>
  rw[]>>every_case_tac>>rw[]>>fs[]>>
  first_x_assum drule>>
  disch_then drule>>fs[]>>
  fs[]);

val no_clash_LUPDATE_Fixed = Q.prove(`
  undirected adjls ∧
  EVERY (λls. EVERY (λv. v < LENGTH tags) ls) adjls ∧
  n < LENGTH adjls ∧
  (∀m. MEM m (EL n adjls) ∧ m < LENGTH tags ⇒
    EL m tags ≠ Fixed x) ∧
  no_clash adjls tags ⇒
  no_clash adjls (LUPDATE (Fixed x) n tags)`,
  rw[no_clash_def]>>
  fs[EL_LUPDATE]>>
  rw[]
  >-
    (fs[has_edge_def]>>
    last_x_assum drule>>
    impl_tac>-
      (fs[EVERY_MEM,MEM_EL]>>
      metis_tac[])>>
    rw[]>>
    TOP_CASE_TAC>>simp[]>>
    CCONTR_TAC>>fs[])
  >>
    `has_edge adjls n x'` by
      metis_tac[undirected_def]>>
    fs[has_edge_def]>>
    qpat_x_assum`MEM n _` kall_tac>>
    last_x_assum drule>>
    impl_tac>-
      (fs[EVERY_MEM,MEM_EL]>>
      metis_tac[])>>
    rw[]>>
    TOP_CASE_TAC>>simp[]>>
    CCONTR_TAC>>fs[]);

val remove_colours_succeeds = Q.prove(`
  ∀adj ks s s.
  EVERY (\v. v < LENGTH s.node_tag) adj ⇒
  ∃ls. remove_colours adj ks s = (Success ls,s)`,
  ho_match_mp_tac remove_colours_ind>>rw[remove_colours_def]>>
  simp msimps>>
  Cases_on`EL x s.node_tag`>>fs[]>>
  rpt (first_x_assum drule)>>rw[]>>fs[]>>
  first_x_assum(qspec_then`n` assume_tac)>>fs[]>>
  rfs[]);

val assign_Atemp_tag_correct = Q.store_thm("assign_Atemp_tag_correct",`
  good_ra_state s ∧
  no_clash s.adj_ls s.node_tag ∧
  good_pref pref ∧
  n < s.dim ⇒
  ∃s'.
  assign_Atemp_tag ks pref n s = (Success (),s') ∧
  (∀m.
    if n = m ∧ EL n s.node_tag = Atemp
      then EL n s'.node_tag ≠ Atemp
      else EL m s'.node_tag = EL m s.node_tag) ∧
  no_clash s'.adj_ls s'.node_tag ∧
  good_ra_state s' ∧
  s' = s with node_tag := s'.node_tag`,
  rw[assign_Atemp_tag_def]>>
  pop_assum mp_tac>>
  simp msimps>>
  fs[good_ra_state_def]>>
  strip_tac>>
  simp[Once markerTheory.Abbrev_def]>>
  TOP_CASE_TAC>> simp[]>>
  `EVERY (\v. v < LENGTH s.node_tag) (EL n s.adj_ls)` by
    fs[EVERY_MEM,MEM_EL,PULL_EXISTS]>>
  drule remove_colours_succeeds>>
  disch_then(qspec_then`ks` assume_tac)>>fs[]>>
  simp[ra_state_component_equality]>>
  TOP_CASE_TAC>> simp[EL_LUPDATE]
  >-
    simp[no_clash_LUPDATE_Stemp]
  >>
  qpat_abbrev_tac`ls = h::t`>>
  fs[good_pref_def]>>
  first_x_assum(qspecl_then [`n`,`ls`,`s`] assume_tac)>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  simp[EL_LUPDATE,Abbr`ls`]>>
  imp_res_tac remove_colours_success>>
  match_mp_tac no_clash_LUPDATE_Fixed>>
  fs[markerTheory.Abbrev_def]>>
  rw[]>>first_x_assum drule>>
  fs[]>>
  TOP_CASE_TAC>>fs[]>>
  metis_tac[]);

val assign_Atemps_FOREACH_lem = Q.prove(`
  ∀ls s ks prefs.
  good_ra_state s ∧
  no_clash s.adj_ls s.node_tag ∧
  good_pref prefs ∧
  EVERY (\v. v < s.dim) ls ==>
  ∃s'.
    st_ex_FOREACH ls (assign_Atemp_tag ks prefs) s = (Success (),s') ∧
    no_clash s'.adj_ls s'.node_tag ∧
    good_ra_state s' ∧
    s' = s with node_tag := s'.node_tag ∧
    (∀m.
      if MEM m ls ∧ EL m s.node_tag = Atemp
        then EL m s'.node_tag ≠ Atemp
        else EL m s'.node_tag = EL m s.node_tag)`,
  Induct>>rw[st_ex_FOREACH_def]>>
  fs msimps>-
    simp[ra_state_component_equality]>>
  drule (GEN_ALL assign_Atemp_tag_correct)>>
  rpt(disch_then drule)>>
  disch_then(qspec_then`ks` assume_tac)>>fs[]>>
  first_x_assum drule>>
  rpt (disch_then drule)>>
  fs[]>>simp[]>>
  disch_then(qspec_then`ks` assume_tac)>>fs[]>>
  qpat_x_assum`s' = _` SUBST_ALL_TAC>>rfs[]>>
  rw[]
  >-
    (rpt(first_x_assum (qspec_then`h` mp_tac))>>
    simp[]>>
    strip_tac>>IF_CASES_TAC>>fs[])
  >-
    metis_tac[]
  >>
    fs[]>>(
    rpt(first_x_assum (qspec_then`m` mp_tac))>>
    simp[]>>
    strip_tac>>IF_CASES_TAC>>fs[]>>
    metis_tac[]));

val assign_Atemps_correct = Q.store_thm("assign_Atemps_correct",`
  ∀k ls prefs s.
  good_ra_state s ∧
  good_pref prefs ∧
  no_clash s.adj_ls s.node_tag ==>
  ∃s'.
  assign_Atemps k ls prefs s = (Success (),s') ∧
  no_clash s'.adj_ls s'.node_tag ∧
  good_ra_state s' ∧
  s' = s with node_tag := s'.node_tag ∧
  EVERY (λn. n ≠ Atemp) s'.node_tag ∧
  (* The next one is probably necessary for coloring correctness *)
  !m.
    m < LENGTH s.node_tag ∧ EL m s.node_tag ≠ Atemp ⇒
    EL m s'.node_tag = EL m s.node_tag`,
  rw[assign_Atemps_def,get_dim_def]>>
  simp msimps>>
  qmatch_goalsub_abbrev_tac`st_ex_FOREACH lsf`>>
  qpat_abbrev_tac`ks = (GENLIST _ k)`>>
  (* The heuristic step *)
  drule assign_Atemps_FOREACH_lem>>
  rpt(disch_then drule)>>
  disch_then(qspecl_then[`lsf`,`ks`] assume_tac)>>
  fs[EVERY_FILTER,Abbr`lsf`]>>
  (* The "real" step *)
  drule assign_Atemps_FOREACH_lem>>
  rpt(disch_then drule)>>
  qpat_x_assum`s' = _` SUBST_ALL_TAC>>
  qmatch_goalsub_abbrev_tac`st_ex_FOREACH lsg`>>
  disch_then(qspecl_then[`lsg`,`ks`] assume_tac)>>
  fs[EVERY_GENLIST,Abbr`lsg`]>>
  CONJ_TAC
  >- (
    fs[EVERY_MEM,MEM_GENLIST,good_ra_state_def]>>
    CCONTR_TAC>>
    fs[MEM_EL]>>
    first_x_assum(qspec_then`n` assume_tac)>>
    rfs[]>>fs[ra_state_component_equality])
  >>
    fs[MEM_GENLIST,MEM_FILTER,good_ra_state_def]>>
    rw[]>>
    rpt(first_x_assum(qspec_then`m` assume_tac))>>rfs[]>>
    fs[ra_state_component_equality]>>
    rfs[]);

val SORTED_HEAD_LT = Q.prove(`
  ∀ls.
  (col:num) < h ∧ SORTED (λx y. x≤y) (h::ls) ⇒
  ¬MEM col ls`,
  Induct>>srw_tac[][SORTED_DEF]
  >-
    DECIDE_TAC
  >>
    last_x_assum mp_tac>>impl_tac>>
    Cases_on`ls`>>full_simp_tac(srw_ss())[SORTED_DEF]>>DECIDE_TAC);

(* Correctness for the second step *)
val unbound_colour_correct = Q.store_thm("unbound_colour_correct",`
  ∀ls k k'.
  SORTED (λx y.x ≤ y) ls  ==>
  k ≤ unbound_colour k ls ∧
  ~MEM (unbound_colour k ls) ls`,
  Induct>>fs[unbound_colour_def]>>rw[]>>
  fs[]>>
  imp_res_tac SORTED_TL>>
  first_x_assum drule>>rw[]
  >-
    metis_tac[SORTED_HEAD_LT]
  >-
    (first_x_assum(qspec_then`h+1` assume_tac)>>fs[])
  >-
    (first_x_assum(qspec_then`h+1` assume_tac)>>fs[])
  >>
    first_x_assum(qspec_then`k` assume_tac)>>fs[]);

val st_ex_MAP_node_tag_sub = Q.store_thm("st_ex_MAP_node_tag_sub",`
  ∀ls s.
  EVERY (λv. v < LENGTH s.node_tag) ls ⇒
  st_ex_MAP (\i.node_tag_sub i) ls s = (Success (MAP (λi. EL i s.node_tag) ls),s)`,
  Induct>>fs[st_ex_MAP_def]>>fs msimps)

val assign_Stemp_tag_correct = Q.store_thm("assign_Stemp_tag_correct",`
  good_ra_state s ∧
  no_clash s.adj_ls s.node_tag ∧
  n < s.dim ⇒
  ∃s'.
  assign_Stemp_tag k n s = (Success (),s') ∧
  (∀m.
    if n = m ∧ EL n s.node_tag = Stemp
      then ∃k'. EL n s'.node_tag = Fixed k' ∧ k ≤ k'
      else EL m s'.node_tag = EL m s.node_tag) ∧
  no_clash s'.adj_ls s'.node_tag ∧
  good_ra_state s' ∧
  s' = s with node_tag := s'.node_tag`,
  rw[assign_Stemp_tag_def]>>simp msimps>>
  reverse IF_CASES_TAC >- fs[good_ra_state_def]>>
  simp[]>>
  TOP_CASE_TAC>>simp msimps>>
  simp[ra_state_component_equality]>>
  reverse IF_CASES_TAC >- fs[good_ra_state_def]>>
  simp[]>>
  `EVERY (λv. v< LENGTH s.node_tag) (EL n s.adj_ls)` by
    fs[good_ra_state_def,EVERY_MEM,MEM_EL,PULL_EXISTS]>>
  imp_res_tac st_ex_MAP_node_tag_sub>>
  simp[]>>
  qmatch_goalsub_abbrev_tac`unbound_colour k ls`>>
  simp[EL_LUPDATE]>>
  fs[good_ra_state_def]>>
  `SORTED (\ x y. x ≤ y) ls` by
    (fs[Abbr`ls`]>>
    match_mp_tac QSORT_SORTED>>
    fs[relationTheory.transitive_def,relationTheory.total_def])>>
  drule unbound_colour_correct>>
  strip_tac>>fs[]>>
  match_mp_tac no_clash_LUPDATE_Fixed>>
  simp[MEM_EL,PULL_EXISTS]>>
  rw[]>>
  first_x_assum(qspec_then`k` assume_tac)>>
  qabbrev_tac`k' = unbound_colour k ls`>>
  fs[Abbr`ls`,QSORT_MEM,MEM_MAP]>>
  first_x_assum(qspec_then`Fixed k'` assume_tac)>>fs[tag_col_def]>>
  pop_assum(qspec_then`EL n' (EL n s.adj_ls)` assume_tac)>>fs[]>>
  metis_tac[MEM_EL]);

(* Almost exactly the same as the FOREACH for Atemps *)
val assign_Stemps_FOREACH_lem = Q.prove(`
  ∀ls s k.
  good_ra_state s ∧
  no_clash s.adj_ls s.node_tag ∧
  EVERY (\v. v < s.dim) ls ==>
  ∃s'.
    st_ex_FOREACH ls (assign_Stemp_tag k) s = (Success (),s') ∧
    no_clash s'.adj_ls s'.node_tag ∧
    good_ra_state s' ∧
    (∀m.
      if MEM m ls ∧ EL m s.node_tag = Stemp
        then ∃k'. EL m s'.node_tag = Fixed k' ∧ k ≤ k'
        else EL m s'.node_tag = EL m s.node_tag) ∧
    s' = s with node_tag := s'.node_tag`,
  Induct>>rw[st_ex_FOREACH_def]>>
  fs msimps>- simp[ra_state_component_equality]>>
  drule (GEN_ALL assign_Stemp_tag_correct)>>
  rpt(disch_then drule)>>
  disch_then(qspec_then`k` assume_tac)>>fs[]>>
  first_x_assum drule>>
  rpt (disch_then drule)>>
  fs[]>>simp[]>>
  disch_then(qspec_then`k` assume_tac)>>fs[]>>
  qpat_x_assum`s' = _` SUBST_ALL_TAC>>rfs[]>>
  rw[]
  >-
    (rpt(first_x_assum (qspec_then`h` mp_tac))>>
    simp[]>>
    strip_tac>>IF_CASES_TAC>>fs[])
  >-
    metis_tac[]
  >>
    fs[]>>(
    rpt(first_x_assum (qspec_then`m` mp_tac))>>
    simp[]>>
    strip_tac>>IF_CASES_TAC>>fs[]>>
    metis_tac[]));

val assign_Stemps_correct = Q.store_thm("assign_Stemps_correct",`
  good_ra_state s ∧
  no_clash s.adj_ls s.node_tag ⇒
  ∃s'.
    assign_Stemps k s = (Success (),s') ∧
    no_clash s'.adj_ls s'.node_tag ∧
    good_ra_state s' ∧
    s' = s with node_tag := s'.node_tag ∧
    ∀m.
      m < LENGTH s.node_tag ==>
      if EL m s.node_tag = Stemp then
        ∃k'. EL m s'.node_tag = Fixed k' ∧ k ≤ k'
      else
      EL m s'.node_tag = EL m s.node_tag`,
  rw[assign_Stemps_def]>>
  simp msimps>>
  simp [get_dim_def]>>
  drule assign_Stemps_FOREACH_lem>>
  simp[]>>
  qmatch_goalsub_abbrev_tac`st_ex_FOREACH ls _`>>
  disch_then (qspecl_then [`ls`,`k`] mp_tac)>>
  impl_tac>-
    fs[Abbr`ls`,EVERY_GENLIST]>>
  strip_tac>>
  fs[Abbr`ls`,MEM_GENLIST]>>
  fs[good_ra_state_def]>>
  metis_tac[]);

(* --  Random sanity checks that will be needed at some point -- *)

(* Checking that biased_pref satisfies good_pref *)
val first_match_col_correct = Q.prove(`
  ∀x ks s.
  ∃res. first_match_col ks x s = (res,s) ∧
  case res of
    Failure v => v = Subscript
  | Success (SOME k) => MEM k ks
  | _ => T`,
  Induct>>fs[first_match_col_def]>>fs msimps>>
  rw[]>>
  TOP_CASE_TAC>>fs[]>>
  IF_CASES_TAC>>fs[]);

val good_pref_biased_pref = Q.store_thm("good_pref_biased_pref",`
  ∀t. good_pref (biased_pref t)`,
  rw[good_pref_def,biased_pref_def]>>
  TOP_CASE_TAC>>simp msimps>>
  (first_match_col_correct |> SPEC_ALL |> assume_tac)>>
  fs[]>>
  EVERY_CASE_TAC>>fs[handle_Subscript_def]);

(* -- *)

(* Checking that the bijection produced is correct *)

val in_clash_tree_def = Define`
  (in_clash_tree (Delta w r) x ⇔ MEM x w ∨ MEM x r) ∧
  (in_clash_tree (Set names) x ⇔ x ∈ domain names) ∧
  (in_clash_tree (Branch name_opt t1 t2) x ⇔
    in_clash_tree t1 x ∨
    in_clash_tree t2 x ∨
    case name_opt of
      SOME names => x ∈ domain names
    | NONE => F) ∧
  (in_clash_tree (Seq t t') x ⇔ in_clash_tree t x ∨ in_clash_tree t' x)`

(*g inverts f as an sptree *)
val sp_inverts_def = Define`
  sp_inverts f g ⇔
  ∀m fm.
    lookup m f = SOME fm ⇒
    lookup fm g = SOME m`

val sp_inverts_insert = Q.prove(`
  sp_inverts f g ∧
  x ∉ domain f ∧
  y ∉ domain g ⇒
  sp_inverts (insert x y f) (insert y x g)`,
  rw[sp_inverts_def,lookup_insert]>>
  pop_assum mp_tac>> IF_CASES_TAC>> rw[]>>
  CCONTR_TAC >> fs[]>> first_x_assum drule>>
  fs[domain_lookup]);

val list_remap_domain = Q.prove(`
  ∀ls ta fa n ta' fa' n'.
  list_remap ls (ta,fa,n) = (ta',fa',n') ⇒
  domain ta' = domain ta ∪ set ls`,
  Induct>>rw[list_remap_def]>>
  EVERY_CASE_TAC>>
  first_x_assum drule>>fs[domain_insert]>>
  fs[EXTENSION]>>
  metis_tac[domain_lookup]);

val list_remap_bij = Q.prove(`
  ∀ls ta fa n ta' fa' n'.
  list_remap ls (ta,fa,n) = (ta',fa',n') ∧
  sp_inverts ta fa ∧
  sp_inverts fa ta ∧
  domain fa = count n ==>
  Abbrev(sp_inverts ta' fa' ∧
  sp_inverts fa' ta' ∧
  domain fa' = count n')`,
  Induct>>rw[list_remap_def]>>fs[markerTheory.Abbrev_def]>>
  reverse EVERY_CASE_TAC>>
  first_x_assum drule
  >-
    metis_tac[]
  >>
    impl_tac >-
      (rw[]>>
      TRY(match_mp_tac sp_inverts_insert>>
        fs[]>>
        CCONTR_TAC>>rfs[domain_lookup])>>
      fs[domain_insert,EXTENSION])>>
    metis_tac[])|>SIMP_RULE std_ss [markerTheory.Abbrev_def];

val mk_bij_aux_domain = Q.prove(`
  ∀ct ta fa n ta' fa' n'.
  mk_bij_aux ct (ta,fa,n) = (ta',fa',n') ⇒
  domain ta' = domain ta ∪ {x | in_clash_tree ct x}`,
  Induct>>rw[mk_bij_aux_def]>>fs[in_clash_tree_def]
  >- (
    Cases_on`list_remap l0 (ta,fa,n)`>>Cases_on`r`>>
    imp_res_tac list_remap_domain>>
    fs[EXTENSION]>>
    metis_tac[])
  >- (
    imp_res_tac list_remap_domain>>
    fs[EXTENSION,toAList_domain])
  >- (
    `∃ta1 fa1 n1. mk_bij_aux ct (ta,fa,n) = (ta1,fa1,n1) ∧
     ∃ta2 fa2 n2. mk_bij_aux ct' (ta1,fa1,n1) = (ta2,fa2,n2)` by
       metis_tac[PAIR]>>
    last_x_assum drule>> simp[markerTheory.Abbrev_def]>>
    strip_tac>>
    last_x_assum drule >> simp[markerTheory.Abbrev_def]>>
    strip_tac>>
    qpat_x_assum`_= (_,_,n')` mp_tac>> TOP_CASE_TAC>> fs[]
    >-
      (rw[]>>
      simp[EXTENSION]>>metis_tac[])
    >>
      strip_tac>> drule list_remap_domain>>
      rw[]>>simp[EXTENSION,toAList_domain]>>
      metis_tac[])
  >>
    `∃ta1 fa1 n1. mk_bij_aux ct' (ta,fa,n) = (ta1,fa1,n1) ∧
     ∃ta2 fa2 n2. mk_bij_aux ct (ta1,fa1,n1) = (ta2,fa2,n2)` by
       metis_tac[PAIR]>>
    fs[]>>
    last_x_assum drule>> simp[markerTheory.Abbrev_def]>>
    strip_tac>>
    last_x_assum drule >> simp[markerTheory.Abbrev_def]>>
    rw[]>>simp[EXTENSION]>>
    metis_tac[]);

val mk_bij_aux_bij = Q.prove(`
  ∀ct ta fa n ta' fa' n'.
  mk_bij_aux ct (ta,fa,n) = (ta',fa',n') ∧
  sp_inverts ta fa ∧
  sp_inverts fa ta ∧
  domain fa = count n ==>
  Abbrev(sp_inverts ta' fa' ∧
  sp_inverts fa' ta' ∧
  domain fa' = count n')`,
  Induct>>rw[mk_bij_aux_def]>>
  simp[markerTheory.Abbrev_def]
  >- (
    Cases_on`list_remap l0 (ta,fa,n)`>>Cases_on`r`>>
    match_mp_tac list_remap_bij>>
    asm_exists_tac>> simp[]>>
    match_mp_tac list_remap_bij>>
    metis_tac[])
  >- (
    match_mp_tac list_remap_bij>>
    asm_exists_tac>> fs[])
  >- (
    `∃ta1 fa1 n1. mk_bij_aux ct (ta,fa,n) = (ta1,fa1,n1) ∧
     ∃ta2 fa2 n2. mk_bij_aux ct' (ta1,fa1,n1) = (ta2,fa2,n2)` by
       metis_tac[PAIR]>>
    last_x_assum drule>> simp[markerTheory.Abbrev_def]>>
    strip_tac>>
    last_x_assum drule >> simp[markerTheory.Abbrev_def]>>
    strip_tac>>
    qpat_x_assum`_= (_,_,n')` mp_tac>> TOP_CASE_TAC>> fs[]
    >-
      metis_tac[]
    >>
      strip_tac>> metis_tac[list_remap_bij])
  >>
    `∃ta1 fa1 n1. mk_bij_aux ct' (ta,fa,n) = (ta1,fa1,n1) ∧
     ∃ta2 fa2 n2. mk_bij_aux ct (ta1,fa1,n1) = (ta2,fa2,n2)` by
       metis_tac[PAIR]>>
    fs[]>>
    last_x_assum drule>> simp[markerTheory.Abbrev_def]>>
    strip_tac>>
    last_x_assum drule >> simp[markerTheory.Abbrev_def]) |> SIMP_RULE std_ss [markerTheory.Abbrev_def];

val list_remap_wf = Q.prove(`
  ∀l ta fa n ta' fa' n'.
  list_remap l (ta,fa,n) = (ta',fa',n') /\
  wf ta ∧ wf fa ==>
  wf ta' ∧ wf fa'`,
  Induct>>fs[list_remap_def,FORALL_PROD]>>
  rw[]>>
  EVERY_CASE_TAC>>fs[]>>
  first_x_assum drule>>
  rpt (disch_then drule)>>
  fs[wf_insert]);

val mk_bij_aux_wf = Q.store_thm("mk_bij_aux_wf",`
  ∀ct ta fa n ta' fa' n'.
  mk_bij_aux ct (ta,fa,n) = (ta',fa',n') /\
  wf ta ∧ wf fa ⇒
  Abbrev(wf ta' ∧ wf fa')`,
  Induct>>rw[mk_bij_aux_def]
  >-
    (Cases_on`list_remap l0 (ta,fa,n)`>>Cases_on`r`>>
    simp[markerTheory.Abbrev_def]>>
    drule list_remap_wf>>fs[]>>strip_tac>>
    metis_tac[PAIR_EQ,PAIR,list_remap_wf,FST,SND])
  >-
    (simp[markerTheory.Abbrev_def]>>
    drule list_remap_wf>>fs[])
  >-
    (
    `∃ta1 fa1 n1. mk_bij_aux ct (ta,fa,n) = (ta1,fa1,n1) ∧
     ∃ta2 fa2 n2. mk_bij_aux ct' (ta1,fa1,n1) = (ta2,fa2,n2)` by
       metis_tac[PAIR]>>
    last_x_assum drule>> simp[markerTheory.Abbrev_def]>>
    strip_tac>>
    last_x_assum drule >> simp[markerTheory.Abbrev_def]>>
    strip_tac>>
    qpat_x_assum`_= (_,_,n')` mp_tac>> TOP_CASE_TAC>> fs[]
    >-
      metis_tac[]
    >>
      strip_tac>>
      metis_tac[list_remap_wf])
  >>
    `∃ta1 fa1 n1. mk_bij_aux ct' (ta,fa,n) = (ta1,fa1,n1) ∧
     ∃ta2 fa2 n2. mk_bij_aux ct (ta1,fa1,n1) = (ta2,fa2,n2)` by
       metis_tac[PAIR]>>
    fs[]>>
    last_x_assum drule>> simp[markerTheory.Abbrev_def]>>
    strip_tac>>
    last_x_assum drule >> simp[markerTheory.Abbrev_def]);

(* Properties of the graph manipulating functions
   All of these simultaneously prove success
   together with the correctness properties.

   One could also imagine proving the success separately from
   the correctness
*)
(* the list represents a clique *)
val is_clique_def = Define`
  is_clique ls adjls ⇔
  ∀x y. MEM x ls ∧ MEM y ls ∧ x ≠ y ⇒
    has_edge adjls x y`

val is_subgraph_def = Define`
  is_subgraph g h ⇔
  ∀x y.
    has_edge g x y ⇒ has_edge h x y`

val insert_edge_succeeds = Q.store_thm("insert_edge_succeeds",`
  good_ra_state s ∧
  y < s.dim ∧
  x < s.dim ⇒
  ∃s'. insert_edge x y s = (Success (),s') ∧
  good_ra_state s' ∧
  s' = s with adj_ls := s'.adj_ls ∧
  ∀a b.
  (has_edge s'.adj_ls a b ⇔
    (a = x ∧ b = y) ∨ (a = y ∧ b = x) ∨ (has_edge s.adj_ls a b))`,
  rw[good_ra_state_def,insert_edge_def]>>fs msimps>>
  IF_CASES_TAC >> fs[]
  >- (
    fs[ra_state_component_equality,has_edge_def,undirected_def]>>
    rfs[]>>
    res_tac>>
    rw[]>>metis_tac[])>>
  CONJ_TAC>- (
    match_mp_tac IMP_EVERY_LUPDATE>>
    rw[] >- metis_tac[EVERY_EL]>>
    match_mp_tac IMP_EVERY_LUPDATE>>
    rw[] >- metis_tac[EVERY_EL])>>
  CONJ_ASM2_TAC>- (
    fs[undirected_def]>>
    metis_tac[])>>
  rw[has_edge_def]>>
  simp[EL_LUPDATE] >>rw[]>>metis_tac[]);

val list_insert_edge_succeeds = Q.store_thm("list_insert_edge_succeeds",`
  ∀ys x s.
  good_ra_state s ∧
  x < s.dim ∧
  EVERY ( λy. y < s.dim) ys ⇒
  ∃s'. list_insert_edge x ys s = (Success (),s') ∧
  good_ra_state s' ∧
  s' = s with adj_ls := s'.adj_ls ∧
  ∀a b.
  (has_edge s'.adj_ls a b ⇔
    (a = x ∧ MEM b ys) ∨
    (b = x ∧ MEM a ys) ∨
    (has_edge s.adj_ls a b))`,
  Induct>>rw[list_insert_edge_def]>>fs msimps
  >-
    fs[ra_state_component_equality]>>
  drule (GEN_ALL insert_edge_succeeds)>>
  disch_then (qspecl_then [`h`,`x`] assume_tac)>>rfs[]>>
  last_x_assum drule>>
  qpat_x_assum`s' = _` SUBST_ALL_TAC>>fs[]>>
  disch_then (qspec_then`x` strip_assume_tac)>>rfs[]>>
  rw[]>>metis_tac[]);

val is_subgraph_trans = Q.store_thm("is_subgraph_trans",`
  is_subgraph s s' ∧
  is_subgraph s' s'' ==>
  is_subgraph s s''`,
  rw[is_subgraph_def]);

(* From here onwards we stop characterizing s'.adj_ls exactly
   although it could be done
 *)
val clique_insert_edge_succeeds = Q.store_thm("clique_insert_edge_succeeds",`
  ∀ls s.
  good_ra_state s ∧
  EVERY ( λy. y < s.dim) ls ==>
  ∃s'. clique_insert_edge ls s = (Success (),s') ∧
  good_ra_state s' ∧
  s' = s with adj_ls := s'.adj_ls ∧
  is_clique ls s'.adj_ls ∧
  is_subgraph s.adj_ls s'.adj_ls`,
  Induct>>rw[clique_insert_edge_def]>>fs msimps
  >-
    fs[ra_state_component_equality,is_subgraph_def,is_clique_def]>>
  drule list_insert_edge_succeeds>>
  rpt (disch_then drule)>>
  strip_tac>>simp[]>>
  last_x_assum drule>>
  qpat_x_assum`s' = _` SUBST_ALL_TAC>>fs[]>>
  strip_tac>>fs[]>>
  CONJ_TAC>-
    (fs[is_clique_def,is_subgraph_def]>>
    reverse (rw[]) >- metis_tac[] >>
    fs[EVERY_MEM])
  >>
  match_mp_tac (GEN_ALL is_subgraph_trans)>>
  qexists_tac`s'.adj_ls`>>fs[is_subgraph_def]);

val extend_clique_succeeds = Q.store_thm("extend_clique_succeeds",`
  ∀ls cli s.
  good_ra_state s ∧
  is_clique cli s.adj_ls ∧
  EVERY ( λy. y < s.dim) ls ∧
  ALL_DISTINCT cli ∧
  EVERY ( λy. y < s.dim) cli ⇒
  ∃cli' s'. extend_clique ls cli s = (Success cli', s') ∧
  good_ra_state s' ∧
  ALL_DISTINCT cli' ∧
  s' = s with adj_ls := s'.adj_ls ∧
  set cli' = set (cli++ls) ∧
  is_clique cli' s'.adj_ls ∧
  is_subgraph s.adj_ls s'.adj_ls`,
  Induct>>rw[extend_clique_def]>>fs msimps
  >-
    simp[ra_state_component_equality,is_subgraph_def]
  >-
    (first_x_assum drule>> disch_then drule>> simp[]>> strip_tac>>
    fs[EXTENSION]>>
    metis_tac[])
  >>
    drule list_insert_edge_succeeds>>
    disch_then drule>> disch_then drule>> strip_tac>> fs[]>>
    first_x_assum(qspecl_then [`h::cli`,`s'`] mp_tac)>>
    qpat_x_assum`s' = _` SUBST_ALL_TAC>>
    impl_tac>-
      (fs[is_clique_def]>>
      metis_tac[])>>
    fs[]>> strip_tac>>
    fs[]>>
    CONJ_TAC>-
      (simp[EXTENSION]>>metis_tac[])>>
    fs[is_subgraph_def]);

(* The col needed to get colouring satisfactory can be generated
   from the node tags
   The correctness should be a consequence of no_clash *)
val colouring_satisfactory_def = Define `
  colouring_satisfactory col adjls =
  ∀x. x < LENGTH adjls ⇒
   (∀y. y < LENGTH adjls ∧ MEM y (EL x adjls) ⇒
   col x = col y ==> x = y)`

(*TODO: this is in word_allocProof*)
val INJ_less = Q.prove(`
  ∀f s' t s.
  INJ f s' t ∧ s ⊆ s'
  ⇒
  INJ f s t`,
  metis_tac[INJ_DEF,SUBSET_DEF]);

val check_partial_col_success = Q.prove(`
  ∀ls live flive col.
  domain flive = IMAGE col (domain live) ∧
  INJ col (set ls ∪ domain live) UNIV
  ⇒
  ∃livein flivein.
  check_partial_col col ls live flive = SOME (livein,flivein) ∧
  domain flivein = IMAGE col (domain livein)`,
  Induct>>fs[check_partial_col_def]>>rw[]>>
  TOP_CASE_TAC>>fs[]
  >-
    (`h ∉ domain live` by fs[domain_lookup]>>
    `lookup (col h) flive = NONE` by
      (
      (*TOO LONG*)
      CCONTR_TAC>>
      `∃s. lookup(col h) flive = SOME s` by
        (Cases_on`lookup (col h) flive`>>fs[]) >>
      last_x_assum kall_tac>>
      fs[EXTENSION,domain_lookup]>>
      first_x_assum(qspec_then`col h` mp_tac)>>
      rw[EQ_IMP_THM]>>
      Cases_on`h=x'`>>fs[]>>
      Cases_on`lookup x' live = SOME ()`>>fs[]>>
      FULL_SIMP_TAC bool_ss[INJ_DEF]>>
      first_x_assum(qspecl_then[`h`,`x'`] assume_tac)>>
      fs[domain_lookup]>>
      metis_tac[])>>
    fs[]>>
    first_x_assum(qspecl_then[`insert h () live`,`insert (col h) () flive`,`col`] mp_tac)>>
    impl_tac>-
      (fs[]>>match_mp_tac INJ_less>>
      HINT_EXISTS_TAC>>fs[SUBSET_DEF])>>
    rw[]>>fs[EXTENSION]>>
    metis_tac[])>>
  res_tac>>pop_assum mp_tac>>
  impl_tac>-
    (match_mp_tac INJ_less>>
    HINT_EXISTS_TAC>>fs[SUBSET_DEF])>>
  rw[]>>fs[EXTENSION]);

val INJ_COMPOSE_IMAGE = Q.store_thm("INJ_COMPOSE_IMAGE",`
  ∀a b u.
  INJ f a b ∧
  INJ g (IMAGE f a) u ⇒
  INJ (g o f) a u`,
  rw[]>>
  match_mp_tac INJ_COMPOSE>>
  metis_tac[INJ_IMAGE]);

val colouring_satisfactory_cliques = Q.store_thm("colouring_satisfactory_cliques",`
  ∀ls g (f:num->num).
  ALL_DISTINCT ls ∧
  EVERY (λx. x < LENGTH g) ls ∧
  colouring_satisfactory f g ∧ is_clique ls g
  ⇒
  ALL_DISTINCT (MAP f ls)`,
  Induct>>fs[is_clique_def,colouring_satisfactory_def]>>
  rw[]
  >-
    (fs[MEM_MAP]>>rw[]>>
    first_x_assum(qspecl_then [`h`,`y`] assume_tac)>>rfs[]>>
    Cases_on`MEM y ls`>>Cases_on`h=y`>>fs[]>>
    fs[has_edge_def]>>
    metis_tac[])
  >>
    first_x_assum(qspecl_then [`g`,`f`] mp_tac)>>rev_full_simp_tac(srw_ss())[]);

val domain_eq_IMAGE = Q.prove(`
  domain s = IMAGE FST (set(toAList s))`,
  fs[EXTENSION,EXISTS_PROD]>>
  fs[MEM_toAList,domain_lookup]);

val is_clique_FILTER = Q.prove(`
  ∀ls.
  is_clique ls G ⇒
  is_clique (FILTER P ls) G`,
  Induct>>fs[is_clique_def]>>
  strip_tac>>
  cases_on`P h`>>
  fs[MEM_FILTER]>>
  metis_tac[]);

val is_clique_subgraph = Q.prove(`
  is_clique ls s ∧
  is_subgraph s s' ⇒
  is_clique ls s'`,
  fs[is_clique_def,is_subgraph_def]);

val domain_numset_list_delete = Q.store_thm("domain_numset_list_delete",`
  ∀l live.
  domain (numset_list_delete l live) =
  domain live DIFF set l`,
  Induct>>fs[numset_list_delete_def]>>rw[]>>
  fs[EXTENSION]>>
  metis_tac[]);

(* The success theorem is separated here *)
val mk_graph_succeeds = Q.store_thm("mk_graph_succeeds",`
  ∀ct ta liveout s.
  good_ra_state s ∧
  (∀x. in_clash_tree ct x ⇒ ta x < s.dim) ∧
  INJ ta ({x | in_clash_tree ct x}) (count (LENGTH s.adj_ls)) ∧
  (is_clique liveout s.adj_ls) ∧
  ALL_DISTINCT liveout ∧
  (EVERY (λy.y < s.dim) liveout) ⇒
  ∃livein s'. mk_graph ta ct liveout s = (Success livein, s') ∧
  good_ra_state s' ∧
  is_clique livein s'.adj_ls ∧
  s' = s with adj_ls := s'.adj_ls ∧
  (EVERY (λy.y < s.dim) livein) ∧
  ALL_DISTINCT livein ∧
  set livein SUBSET set liveout ∪ IMAGE ta {x | in_clash_tree ct x} ∧
  is_subgraph s.adj_ls s'.adj_ls`,
  Induct>>
  rw[in_clash_tree_def,mk_graph_def]>>fs msimps
  >-
    (drule extend_clique_succeeds>>
    disch_then drule>>simp[]>>
    disch_then(qspec_then`MAP ta l` mp_tac)>>
    impl_tac>-
      simp[EVERY_MAP,EVERY_MEM]>>
    rw[]>>
    simp[]>>
    qpat_x_assum`s' = _` SUBST_ALL_TAC>>fs[EVERY_MEM,MEM_MAP]>>
    qmatch_goalsub_abbrev_tac`extend_clique x xs _`>>
    drule extend_clique_succeeds>>
    disch_then (qspecl_then [`x`,`xs`] mp_tac)>>
    impl_keep_tac>-
      (unabbrev_all_tac>>simp[is_clique_FILTER]>>
      simp[EVERY_MAP,EVERY_MEM,FILTER_ALL_DISTINCT,MEM_FILTER]>>
      fs[MEM_MAP]>>
      metis_tac[])>>
    rw[]>>
    simp[]>>
    unabbrev_all_tac>>
    fs[EVERY_MEM,SUBSET_DEF,EXTENSION,MEM_FILTER,MEM_MAP]>>
    metis_tac[is_subgraph_trans])
  >-
    (drule clique_insert_edge_succeeds>>
    qmatch_goalsub_abbrev_tac`_ ls  s'`>>
    disch_then (qspec_then`ls` mp_tac)>>
    impl_keep_tac>-
      (simp[Abbr`ls`,EVERY_MEM,Once MEM_MAP,toAList_domain]>>
      metis_tac[])>>
    strip_tac>>simp[Abbr`ls`]>>
    CONJ_TAC>-(
      match_mp_tac ALL_DISTINCT_MAP_INJ>>fs[ALL_DISTINCT_MAP_FST_toAList,toAList_domain]>>
      FULL_SIMP_TAC std_ss [INJ_DEF])>>
    fs[Once LIST_TO_SET_MAP,SUBSET_DEF,toAList_domain])
  >-
    (last_x_assum drule>>
    disch_then(qspecl_then[`ta`,`liveout`] mp_tac)>>simp[]>>
    impl_tac>-
      (match_mp_tac INJ_less>> asm_exists_tac>>fs[SUBSET_DEF])>>
    strip_tac>>simp[]>>
    last_x_assum drule>>
    disch_then(qspecl_then[`ta`,`liveout`] mp_tac)>>simp[]>>
    qpat_x_assum`s' = _` SUBST_ALL_TAC>>fs[]>>
    impl_tac>- (
      reverse(rw[])>- metis_tac[is_clique_subgraph]>>
      fs[good_ra_state_def]>>rfs[]>>
      match_mp_tac INJ_less>> asm_exists_tac>>
      fs[SUBSET_DEF])>>
    strip_tac>>simp[]>>
    qpat_x_assum`s'' = _` SUBST_ALL_TAC>>
    Cases_on`o'`>>simp[]
    >-
      (drule extend_clique_succeeds>>
      disch_then(qspecl_then[`livein`,`livein'`] mp_tac)>>simp[]>>
      simp[]>>strip_tac>>
      simp[]>>
      fs[EVERY_MEM,SUBSET_DEF,EXTENSION,MEM_FILTER,MEM_MAP]>>
      metis_tac[is_subgraph_trans])
    >>
      drule clique_insert_edge_succeeds>>
      qmatch_goalsub_abbrev_tac`clique_insert_edge ls _`>>
      disch_then(qspec_then`ls` mp_tac)>>
      impl_keep_tac>-
        (fs[Abbr`ls`,EVERY_MEM,Once MEM_MAP,toAList_domain]>>
        metis_tac[])>>
      strip_tac>>fs[Abbr`ls`]>>
      rw[]
      >-
        (match_mp_tac ALL_DISTINCT_MAP_INJ>>fs[ALL_DISTINCT_MAP_FST_toAList,toAList_domain]>>
        FULL_SIMP_TAC std_ss [INJ_DEF]>>
        rw[])
      >-
        (fs[Once LIST_TO_SET_MAP,SUBSET_DEF,toAList_domain]>>
        metis_tac[])
      >>
      metis_tac[is_subgraph_trans])
  >>
    first_x_assum drule>>
    simp[Once CONJ_COMM,GSYM CONJ_ASSOC]>>
    disch_then(qspecl_then[`ta`,`liveout`] mp_tac)>>
    simp[]>>
    impl_tac>-
      (match_mp_tac INJ_less>>asm_exists_tac>>fs[SUBSET_DEF])>>
    rw[]>>simp[]>>
    first_x_assum drule>>
    simp[Once CONJ_COMM,GSYM CONJ_ASSOC]>>
    disch_then(qspecl_then[`ta`,`livein`] mp_tac)>>
    simp[]>>
    impl_tac>-
      (qpat_x_assum`s'=_` SUBST_ALL_TAC>>
      fs[good_ra_state_def]>>rfs[]>>
      match_mp_tac INJ_less>>asm_exists_tac>>fs[SUBSET_DEF])>>
    strip_tac>>fs[]>>
    qpat_x_assum`s' = _` SUBST_ALL_TAC>>fs[]>>
    CONJ_TAC>-
      (fs[SUBSET_DEF]>>metis_tac[])>>
    metis_tac[is_subgraph_trans]);

val colouring_satisfactory_subgraph = Q.store_thm("colouring_satisfactory_subgraph",`
  colouring_satisfactory f h ∧
  is_subgraph g h ⇒
  colouring_satisfactory f g`,
  fs[colouring_satisfactory_def,is_subgraph_def]>>rw[]>>
  fs[has_edge_def]>>
  metis_tac[]);

val ALL_DISTINCT_set_INJ = Q.prove(`
  ∀ls col.
  ALL_DISTINCT (MAP col ls) ⇒
  INJ col (set ls) UNIV`,
  Induct>>fs[INJ_DEF]>>rw[]>>
  fs[MEM_MAP]>>
  metis_tac[]);

val IMAGE_DIFF = Q.prove(`
  INJ f (s ∪ t) UNIV ⇒
  IMAGE f (s DIFF t) =
  (IMAGE f s DIFF IMAGE f t)`,
  rw[EXTENSION,INJ_DEF]>>
  metis_tac[]);

val set_FILTER = Q.prove(`
  set (FILTER P live) =
  set live DIFF (λx. ¬P x)`,
  rw[EXTENSION,MEM_FILTER]>>
  metis_tac[]);

val MEM_MAP_IMAGE = Q.prove(`
   (λx. MEM x (MAP f l)) = IMAGE f (set l)`,
   rw[EXTENSION,MEM_MAP]);

val domain_difference = Q.prove(`
  domain(difference s t) = domain s DIFF domain t`,
  fs[EXTENSION,domain_lookup,lookup_difference]>>
  rw[EQ_IMP_THM]>>fs[]>>
  metis_tac[option_nchotomy]);

val UNION_DIFF_3 = Q.prove(`
 s DIFF t ∪ t = s ∪ t`,
 rw[EXTENSION]>>
 metis_tac[]);

val check_partial_col_domain = Q.store_thm("check_partial_col_domain",`
  ∀ls f live flive v.
  check_partial_col f ls live flive = SOME v ⇒
  domain (FST v) = set ls ∪ domain live`,
  Induct>>fs[check_partial_col_def]>>rw[]>>EVERY_CASE_TAC>>fs[]>>
  first_x_assum drule>>
  fs[EXTENSION]>>
  metis_tac[domain_lookup]);

val check_clash_tree_domain = Q.store_thm("check_clash_tree_domain",`
  ∀ct f live flive live' flive'.
  check_clash_tree f ct live flive = SOME (live',flive') ⇒
  domain live' ⊆ domain live ∪ {x | in_clash_tree ct x}`,
  Induct>>fs[check_clash_tree_def,in_clash_tree_def]>>
  rw[]>>fs[case_eq_thms,FORALL_PROD,check_col_def]>>
  rw[]>>imp_res_tac check_partial_col_domain>>
  fs[SUBSET_DEF,domain_numset_list_delete,toAList_domain,domain_difference]>>
  metis_tac[]);

(* the correctness theorem for mk_graph *)
val mk_graph_check_clash_tree = Q.store_thm("mk_graph_check_clash_tree",`
  ∀ct ta livelist s livelist' s' col live flive.
  mk_graph ta ct livelist s = (Success livelist',s') ∧
  colouring_satisfactory col s'.adj_ls ∧
  INJ ta ({x | in_clash_tree ct x} ∪ domain live) (count (LENGTH s.adj_ls)) ∧
  IMAGE ta (domain live) = set livelist ∧
  ALL_DISTINCT livelist ∧
  EVERY (λy.y < s.dim) livelist ∧
  is_clique livelist s.adj_ls ∧
  good_ra_state s ∧
  domain flive = IMAGE (col o ta) (domain live) ==>
  ∃livein flivein.
  check_clash_tree (col o ta) ct live flive = SOME (livein,flivein) ∧
  IMAGE ta (domain livein) = set livelist' ∧
  domain flivein = IMAGE (col o ta) (domain livein)`,
  Induct>>rw[mk_graph_def,check_clash_tree_def]>>fs msimps>>
  fs[case_eq_thms,in_clash_tree_def]>>rw[]
  >- (
    drule extend_clique_succeeds>> disch_then drule>>
    disch_then(qspec_then`MAP ta l` mp_tac)>>
    simp[AND_IMP_INTRO]>>
    impl_tac>- (
      fs[EVERY_MEM,MEM_MAP,good_ra_state_def]>>
      FULL_SIMP_TAC std_ss [INJ_DEF,IN_COUNT,EXTENSION,IN_IMAGE]>>
      rw[]>>
      last_x_assum match_mp_tac>>simp[])>>
    rw[]>>
    drule extend_clique_succeeds>>
    qmatch_asmsub_abbrev_tac`extend_clique ls cli _`>>
    disch_then (qspecl_then[`ls`,`cli`] mp_tac)>>
    impl_tac>-(
      unabbrev_all_tac>>fs[good_ra_state_def]>>rw[]
      >-
        metis_tac[is_clique_FILTER]
      >-
        (fs[INJ_DEF,EVERY_MEM]>>
        fs[ra_state_component_equality]>>
        metis_tac[MEM_MAP])
      >-
        fs[FILTER_ALL_DISTINCT]
      >>
        fs[EVERY_MEM,EXTENSION,MEM_FILTER,MEM_MAP]>>
        fs[ra_state_component_equality]>>
        metis_tac[])>>
    rw[]>>fs[]>>
    drule check_partial_col_success>>
    disch_then(qspec_then `l` mp_tac)>>
    impl_keep_tac>-(
      match_mp_tac INJ_COMPOSE_IMAGE>>
      qexists_tac`count (LENGTH s.adj_ls)`>>
      CONJ_TAC>-
        (match_mp_tac INJ_less>>asm_exists_tac>>fs[SUBSET_DEF])>>
      fs[IMAGE_UNION,LIST_TO_SET_MAP]>>
      simp[Once UNION_COMM]>>
      qpat_assum`set live' = _`(SUBST1_TAC o SYM)>>
      match_mp_tac ALL_DISTINCT_set_INJ>>
      match_mp_tac colouring_satisfactory_cliques>>
      fs[]>>
      HINT_EXISTS_TAC>>fs[good_ra_state_def]>>rfs[]>>
      fs[EXTENSION,EVERY_MEM]>>
      CONJ_TAC>-
        (fs[ra_state_component_equality]>>
        FULL_SIMP_TAC std_ss [INJ_DEF]>>
        rw[]>-metis_tac[IN_UNION,EXTENSION]>>
        fs[IN_COUNT])>>
      metis_tac[is_clique_subgraph])>>
    rw[]>>simp[]>>
    qmatch_goalsub_abbrev_tac`_ _ a b c`>>
    qspecl_then [`a`,`b`,`c`,`col o ta`] mp_tac check_partial_col_success>>
    unabbrev_all_tac>>
    fs[domain_numset_list_delete]>>
    impl_keep_tac >-
      (rw[LIST_TO_SET_MAP] >-(
        match_mp_tac (GSYM IMAGE_DIFF)>>
        metis_tac[UNION_COMM])>>
      match_mp_tac INJ_COMPOSE_IMAGE>>
      qexists_tac`count (LENGTH s.adj_ls)`>>
      CONJ_TAC>-
        (match_mp_tac INJ_less>>asm_exists_tac>>fs[SUBSET_DEF])>>
      fs[set_FILTER,MEM_MAP_IMAGE]>>
      qmatch_goalsub_abbrev_tac`_ _ ss _`>>
      `ss = set livelist'` by
        (unabbrev_all_tac>>fs[]>>
        qpat_x_assum`_ = set livelist` sym_sub_tac>>
        fs[LIST_TO_SET_MAP]>>
        simp[DIFF_SAME_UNION,UNION_COMM]>>
        AP_TERM_TAC>>
        match_mp_tac IMAGE_DIFF>>
        match_mp_tac INJ_SUBSET >> asm_exists_tac>> simp[SUBSET_DEF])>>
      pop_assum SUBST1_TAC>>
      match_mp_tac ALL_DISTINCT_set_INJ>>
      match_mp_tac colouring_satisfactory_cliques>>fs[]>>
      HINT_EXISTS_TAC>>fs[good_ra_state_def]>>rfs[]>>
      fs[EXTENSION,EVERY_MEM,IN_COUNT]>>
      fs[ra_state_component_equality,MEM_MAP]>>
      FULL_SIMP_TAC std_ss [INJ_DEF,IN_COUNT]>>
      strip_tac>> strip_tac
      >- metis_tac[]
      >- metis_tac[] >>
      simp[])>>
    rw[]>>
    simp[set_FILTER]>>
    imp_res_tac check_partial_col_domain>>fs[]>>
    simp[MEM_MAP_IMAGE,LIST_TO_SET_MAP,DIFF_SAME_UNION,UNION_COMM]>>
    AP_TERM_TAC>>
    qpat_x_assum`_ = set livelist` sym_sub_tac>>
    fs[domain_numset_list_delete]>>
    match_mp_tac IMAGE_DIFF>>
    match_mp_tac INJ_SUBSET>>
    asm_exists_tac>>fs[SUBSET_DEF])
  >- (
    fs[check_col_def]>>
    fs[LIST_TO_SET_MAP]>>
    CONJ_TAC>-
      (simp[GSYM MAP_MAP_o]>>
      qpat_abbrev_tac`tas = MAP ta _`>>
      match_mp_tac colouring_satisfactory_cliques>>
      qexists_tac`s''.adj_ls`>>fs[]>>
      drule clique_insert_edge_succeeds>>
      disch_then (qspec_then`tas` mp_tac)>>
      impl_keep_tac>- (
        unabbrev_all_tac>>
        rw[EVERY_MEM]>>
        fs[Once MEM_MAP,toAList_domain]>>
        FULL_SIMP_TAC std_ss [good_ra_state_def]>>
        FULL_SIMP_TAC std_ss [MEM_MAP,INJ_DEF,AND_IMP_INTRO,IN_COUNT]>>
        first_x_assum match_mp_tac>>
        metis_tac[IN_UNION])>>
      strip_tac>>rfs[]>>
      rw[]>>
      fs[good_ra_state_def]>>
      qpat_x_assum`s'' = _` SUBST_ALL_TAC>>
      fs[Abbr`tas`]>>
      match_mp_tac ALL_DISTINCT_MAP_INJ>>
      fs[ALL_DISTINCT_MAP_FST_toAList,toAList_domain]>>
      rw[]>>
      FULL_SIMP_TAC std_ss [INJ_DEF]>>
      first_x_assum(qspecl_then[`x`,`y`] mp_tac)>>
      simp[])>>
    simp[GSYM domain_eq_IMAGE]>>
    simp[domain_fromAList,EXTENSION,MEM_MAP,EXISTS_PROD,MEM_toAList]>>
    simp[PULL_EXISTS,domain_lookup])
  >- (
    drule mk_graph_succeeds>>
    disch_then(qspecl_then[`ct`,`ta`,`livelist`] mp_tac)>>
    impl_tac>- (
      simp[]>>
      ntac 2 (last_x_assum kall_tac)>>
      CONJ_TAC>-
        fs[INJ_DEF,EVERY_MEM,EXTENSION,good_ra_state_def]>>
      match_mp_tac INJ_less>> asm_exists_tac>> simp[SUBSET_DEF])>>
    strip_tac>>fs[]>>rw[]>>
    drule mk_graph_succeeds>>
    disch_then(qspecl_then[`ct'`,`ta`,`livelist`] mp_tac)>>
    impl_tac>- (
      ntac 2 (last_x_assum kall_tac)>>fs[good_ra_state_def]>>
      qpat_x_assum`s''=_` SUBST_ALL_TAC>>fs[]>>
      CONJ_TAC>- fs[INJ_DEF,EVERY_MEM,EXTENSION]>>
      CONJ_TAC>-
        (match_mp_tac INJ_less >> asm_exists_tac>>fs[SUBSET_DEF])>>
      metis_tac[is_clique_subgraph])>>
    strip_tac>>fs[]>>rw[]>>
    Cases_on`o'`>>fs[]
    >-(
      drule extend_clique_succeeds>>
      disch_then(qspecl_then[`livein`,`livein'`] mp_tac)>>fs[AND_IMP_INTRO]>>
      impl_tac>-
        (fs[ra_state_component_equality]>>rfs[])>>
      strip_tac>>
      fs[]>>rw[]>>
      last_x_assum drule>>simp[]>>
      disch_then(qspecl_then[`col`,`live`,`flive`] mp_tac)>>
      impl_keep_tac>-(
        rw[]
        >-
          metis_tac[colouring_satisfactory_subgraph]
        >>
          match_mp_tac INJ_less>>
          asm_exists_tac>>fs[SUBSET_DEF])>>
      strip_tac>>fs[]>>
      last_x_assum drule>>simp[]>>
      disch_then(qspecl_then[`col`,`live`,`flive`] mp_tac)>>
      impl_keep_tac>-(
        rw[]
        >- metis_tac[colouring_satisfactory_subgraph]
        >-
          (match_mp_tac INJ_less>>
          fs[good_ra_state_def]>>
          qpat_x_assum`s''=_` SUBST_ALL_TAC>>fs[]>>
          asm_exists_tac>>fs[SUBSET_DEF])
        >-
          fs[ra_state_component_equality]>>
        metis_tac[is_clique_subgraph])>>
      strip_tac>>simp[]>>
      imp_res_tac check_clash_tree_domain>>fs[]>>
      qmatch_goalsub_abbrev_tac`_ _ a b c`>>
      qspecl_then [`a`,`b`,`c`,`col o ta`] mp_tac check_partial_col_success>>
      impl_tac>- (
        unabbrev_all_tac>>
        fs[]>>match_mp_tac INJ_COMPOSE_IMAGE>>
        simp[LIST_TO_SET_MAP]>>
        simp[GSYM domain_eq_IMAGE]>>
        qpat_x_assum`_=set livein` sym_sub_tac>>
        SIMP_TAC std_ss [Once (GSYM IMAGE_UNION),domain_difference]>>
        SIMP_TAC std_ss [UNION_DIFF_3]>>
        qexists_tac`count (LENGTH s.adj_ls)`>>
        CONJ_TAC>-(
          match_mp_tac INJ_less>>
          last_assum (match_exists_tac o concl)>>
          fs[SUBSET_DEF]>>
          metis_tac[])>>
        simp[]>>
        qpat_assum`set cli' = _` (SUBST1_TAC o SYM)>>
        match_mp_tac ALL_DISTINCT_set_INJ>>
        match_mp_tac colouring_satisfactory_cliques>>fs[]>>
        qexists_tac`s'.adj_ls`>>simp[]>>
        fs[EXTENSION,EVERY_MEM,IN_COUNT]>>
        fs[ra_state_component_equality,MEM_MAP]>>
        strip_tac>> strip_tac
        >-
          (first_x_assum drule>>
          fs[good_ra_state_def])
        >>
        qpat_x_assum`INJ ta _ _` kall_tac>>
        qpat_x_assum`INJ ta _ _` mp_tac>>
        fs[good_ra_state_def]>>
        qmatch_goalsub_abbrev_tac`INJ ta ss _`>>
        `x' ∈ ss` by
          (fs[Abbr`ss`,SUBSET_DEF]>>
          metis_tac[])>>
        pop_assum mp_tac>>
        rpt (pop_assum kall_tac)>> simp[INJ_DEF,IN_COUNT])>>
      strip_tac>>
      unabbrev_all_tac>>simp[]>>
      imp_res_tac check_partial_col_domain>>fs[]>>
      qmatch_goalsub_abbrev_tac`set (MAP FST ls)`>>
      `set (MAP FST ls) = domain livein''' DIFF domain livein''` by
        fs[Abbr`ls`,EXTENSION,toAList_domain,domain_difference]>>
      fs[]>>rw[]>>
      fs[SUBSET_DEF,EXTENSION]>>
      metis_tac[])
    >>
      drule clique_insert_edge_succeeds>>
      disch_then(qspec_then`MAP ta (MAP FST (toAList x))` mp_tac)>>
      impl_tac>-
        (simp[Once EVERY_MAP,EVERY_MEM,toAList_domain]>>
        fs[ra_state_component_equality]>>
        FULL_SIMP_TAC std_ss [INJ_DEF,IN_COUNT,good_ra_state_def]>>
        ntac 2 strip_tac>>last_x_assum match_mp_tac>>
        simp[])>>
      strip_tac>>fs[]>>
      last_x_assum drule>>simp[]>>
      disch_then(qspecl_then[`col`,`live`,`flive`] mp_tac)>>
      impl_keep_tac>-(
        rw[]
        >-
          metis_tac[colouring_satisfactory_subgraph]
        >>
          match_mp_tac INJ_less>>
          asm_exists_tac>>fs[SUBSET_DEF])>>
      strip_tac>>fs[]>>
      imp_res_tac check_clash_tree_domain>>
      last_x_assum drule>>simp[]>>
      disch_then(qspecl_then[`col`,`live`,`flive`] mp_tac)>>
      impl_keep_tac>-(
        rw[]
        >- metis_tac[colouring_satisfactory_subgraph]
        >-
          (match_mp_tac INJ_less>>
          fs[good_ra_state_def]>>
          qpat_x_assum`s''=_` SUBST_ALL_TAC>>fs[]>>
          asm_exists_tac>>fs[SUBSET_DEF])
        >-
          fs[ra_state_component_equality]>>
        metis_tac[is_clique_subgraph])>>
      strip_tac>>simp[]>>
      imp_res_tac check_clash_tree_domain>>
      simp[check_col_def]>>
      fs[LIST_TO_SET_MAP]>>
      CONJ_TAC>-
        (simp[GSYM MAP_MAP_o]>>
        match_mp_tac colouring_satisfactory_cliques>>
        rw[]>>
        qexists_tac`s'.adj_ls`>>fs[]>>
        CONJ_TAC>-
          (fs[good_ra_state_def]>>
          match_mp_tac ALL_DISTINCT_MAP_INJ>>
          fs[ALL_DISTINCT_MAP_FST_toAList,toAList_domain]>>
          rw[]>>
          ntac 3 (pop_assum mp_tac)>>
          ntac 30 (pop_assum kall_tac)>>
          FULL_SIMP_TAC std_ss [INJ_DEF,AND_IMP_INTRO]>>
          strip_tac>>
          first_x_assum(qspecl_then[`x'`,`y`] match_mp_tac)>>
          simp[])>>
        fs[Once EVERY_MAP,EVERY_MEM,toAList_domain,ra_state_component_equality,good_ra_state_def]>>
        rw[]>>
        FULL_SIMP_TAC std_ss [INJ_DEF,IN_COUNT]>>
        last_x_assum match_mp_tac>>
        simp[])>>
      rw[]
      >-
        (simp[Once LIST_TO_SET_MAP]>>AP_TERM_TAC>>
        metis_tac[EXTENSION,toAList_domain])
      >>
        simp[EXTENSION,domain_fromAList,MEM_MAP,EXISTS_PROD,MEM_toAList]>>
        simp[domain_lookup])
  >>
    drule mk_graph_succeeds>>
    disch_then(qspecl_then[`ct'`,`ta`,`livelist`] mp_tac)>>
    impl_tac>- (
      ntac 2 (last_x_assum kall_tac)>> simp[]>>
      CONJ_TAC>-
        fs[INJ_DEF,EVERY_MEM,EXTENSION,good_ra_state_def]>>
      match_mp_tac INJ_less>>asm_exists_tac>>fs[SUBSET_DEF])>>
    strip_tac>>fs[]>>rw[]>>
    drule mk_graph_succeeds>>
    disch_then(qspecl_then[`ct`,`ta`,`live'`] mp_tac)>>
    impl_tac>- (
      ntac 2 (last_x_assum kall_tac)>>
      fs[good_ra_state_def]>>
      qpat_x_assum`s''=_` SUBST_ALL_TAC>>fs[]>>
      CONJ_TAC>-
        (fs[INJ_DEF,EVERY_MEM,EXTENSION,good_ra_state_def]>>
        metis_tac[is_clique_subgraph])>>
      match_mp_tac INJ_less>>asm_exists_tac>>fs[SUBSET_DEF])>>
    strip_tac>>fs[]>>rw[]>>
    first_x_assum drule>>
    disch_then(qspecl_then[`col`,`live`,`flive`] mp_tac)>>
    impl_keep_tac>-(
      rw[]
      >-
        metis_tac[colouring_satisfactory_subgraph]
      >>
        match_mp_tac INJ_less>>
        asm_exists_tac>>fs[SUBSET_DEF])>>
    strip_tac>>fs[]>>
    imp_res_tac check_clash_tree_domain>>
    last_x_assum drule>>simp[]>>
    disch_then(qspecl_then[`col`,`livein'`,`flivein`] mp_tac)>>
    impl_keep_tac>-(
      simp[]>>
      rw[]
      >-
        (fs[good_ra_state_def]>>rfs[]>>
        match_mp_tac INJ_less>>
        qpat_x_assum`s''=_` SUBST_ALL_TAC>>fs[]>>
        last_assum (match_exists_tac o concl)>> fs[SUBSET_DEF]>>
        metis_tac[])
      >>
        fs[EVERY_MEM,SUBSET_DEF,good_ra_state_def]>>
        qpat_x_assum`s''=_` SUBST_ALL_TAC>>fs[])>>
    strip_tac>>fs[SUBSET_DEF]>>
    metis_tac[]);

(* This precise characterization is needed to show that the forced edges
   correctly force any two to be distinct *)
val extend_graph_succeeds = Q.store_thm("extend_graph_succeeds",`
  ∀forced:(num,num)alist f s.
  good_ra_state s ∧
  EVERY (λx,y.f x < s.dim ∧ f y < s.dim) forced ==>
  ∃s'.
    extend_graph f forced s = (Success (),s') ∧
    good_ra_state s' ∧
    s' = s with adj_ls := s'.adj_ls ∧
    ∀a b.
    (has_edge s'.adj_ls a b ⇔
    (∃x y. f x = a ∧ f y = b ∧ MEM (y,x) forced) ∨
    (∃x y. f x = a ∧ f y = b ∧ MEM (x,y) forced) ∨ (has_edge s.adj_ls a b))`,
  Induct>>fs[extend_graph_def]>>fs msimps
  >-
    rw[ra_state_component_equality]
  >>
    Cases>>fs[extend_graph_def]>>rw[]>>fs msimps>>
    drule (GEN_ALL insert_edge_succeeds)>>
    disch_then (qspecl_then [`f r`,`f q`] assume_tac)>>rfs[]>>
    simp[]>>
    first_x_assum (qspecl_then [`f`,`s'`] assume_tac)>>rfs[]>>
    fs[ra_state_component_equality]>>rfs[]>>
    fs[good_ra_state_def]>>
    metis_tac[]);

(* Again, this characterization is only needed for the conventions,
   but not for the correctness theorem *)
val mk_tags_st_ex_FOREACH_lem = Q.prove(`
  ∀ls s fa.
  good_ra_state s ∧
  EVERY (\v. v < s.dim) ls ⇒
  ∃s'.
    st_ex_FOREACH ls
       (λi.
       if fa i MOD 4 = 1 then update_node_tag i Atemp
       else if fa i MOD 4 = 3 then update_node_tag i Stemp
       else update_node_tag i (Fixed (fa i DIV 2))) s = (Success (),s') ∧
    good_ra_state s' ∧
    s' = s with node_tag := s'.node_tag ∧
    (∀x.
    x < s.dim ⇒
    if MEM x ls then
      (if is_phy_var (fa x) then EL x s'.node_tag = Fixed ((fa x) DIV 2)
      else if is_stack_var (fa x) then EL x s'.node_tag = Stemp
      else EL x s'.node_tag = Atemp)
    else
       EL x s'.node_tag = EL x s.node_tag)`,
  Induct>>fs[st_ex_FOREACH_def]>>fs msimps
  >-
    simp[ra_state_component_equality]>>
  rw[]>>
  (reverse IF_CASES_TAC >- fs[good_ra_state_def])>>
  simp[]>>
  qmatch_goalsub_abbrev_tac`st_ex_FOREACH _ _ ss` >>
  first_x_assum(qspecl_then [`ss`,`fa`] mp_tac)>>
  (impl_tac>-
    fs[Abbr`ss`,good_ra_state_def])>>
  rw[]>> fs[Abbr`ss`]>>
  ntac 2 strip_tac>>
  first_x_assum drule>>
  IF_CASES_TAC>> simp[]>>
  fs[EL_LUPDATE]
  >-
    (`is_alloc_var (fa h)` by fs[is_alloc_var_def]>>
    rw[]>>fs[Once convention_partitions])
  >-
    (`is_stack_var (fa h)` by fs[is_stack_var_def]>>
    rw[]>>fs[Once convention_partitions])
  >-
    (`¬is_alloc_var (fa h) ∧ ¬ is_stack_var (fa h)` by fs[is_stack_var_def,is_alloc_var_def]>>
    metis_tac[convention_partitions]));

val mk_tags_succeeds = Q.store_thm("mk_tags_succeeds",`
  good_ra_state s ∧
  n = s.dim ⇒
  ∃s'.
    mk_tags n fa s = (Success (),s') ∧
    good_ra_state s' ∧
    s' = s with node_tag := s'.node_tag ∧
    ∀x y.
    x < n ∧ y = fa x ⇒
    if is_phy_var y then EL x s'.node_tag = Fixed (y DIV 2)
    else if is_stack_var y then EL x s'.node_tag = Stemp
    else EL x s'.node_tag = Atemp`,
  rw[mk_tags_def]>>fs msimps>>
  drule mk_tags_st_ex_FOREACH_lem>>
  qpat_abbrev_tac`ls = GENLIST _ _`>>
  disch_then(qspecl_then[`ls`,`fa`] mp_tac)>>impl_tac>>
  unabbrev_all_tac>>fs[EVERY_GENLIST]>>rw[]>>simp[]>>
  fs[MEM_GENLIST]);

(* copied from word-to-stack proof*)
val TWOxDIV2 = Q.store_thm("TWOxDIV2",
  `2 * x DIV 2 = x`,
  ONCE_REWRITE_TAC[MULT_COMM]
  \\ simp[MULT_DIV]);

val extract_color_st_ex_MAP_lem = Q.prove(`
  ∀ls s.
  EVERY (λ(k,v). v < LENGTH s.node_tag) ls ⇒
  st_ex_MAP (λ(k,v). do t <- node_tag_sub v; return (k,extract_tag t) od) ls s =
  (Success(MAP (λ(k,v). (k,extract_tag (EL v s.node_tag))) ls),s)`,
  Induct>>fs[st_ex_MAP_def]>>fs msimps>>rw[]>>
  Cases_on`h`>>fs[]);

val extract_color_succeeds = Q.store_thm("extract_color_succeeds",`
  good_ra_state s ∧
  (∀x y. lookup x ta = SOME y ==> y < s.dim) /\
  wf ta ==>
  extract_color ta s =
  (Success (map (λv. extract_tag (EL v s.node_tag)) ta ),s)`,
  rw[extract_color_def]>>
  simp[Once st_ex_bind_def,Once st_ex_return_def]>>
  simp[Once st_ex_bind_def]>>
  Q.ISPECL_THEN [`toAList ta`,`s`] mp_tac extract_color_st_ex_MAP_lem>>
  impl_tac>-
    (fs[EVERY_MEM,MEM_toAList,FORALL_PROD,good_ra_state_def]>>
    metis_tac[])>>
  rw[]>>simp msimps>>
  simp[GSYM map_fromAList]>>
  drule fromAList_toAList>>
  simp[]);

(* Minimal proofs about the heuristic steps *)

val st_ex_PARTITION_split_degree = Q.prove(`
  ∀atemps k lss lss' s.
  good_ra_state s ⇒
  ?ts fs. st_ex_PARTITION (split_degree s.dim k) atemps lss lss' s =
    (Success (ts,fs),s)`,
  Induct_on`atemps`>>fs[st_ex_PARTITION_def,EXISTS_PROD]>>fs msimps>>
  rw[split_degree_def]>>rfs msimps>>
  fs[degrees_accessor,Marray_sub_def]>>
  first_x_assum drule>>
  fs[good_ra_state_def]>>
  rw[]);

(* This is currently more general than necessary because it doesn't
   do any coalescing (yet) *)
val dec_deg_success = Q.prove(`
  ∀ls s.
  EVERY (λv. v < s.dim) ls ∧
  good_ra_state s ⇒
  ∃d. st_ex_FOREACH ls dec_deg s = (Success (),s with degrees :=d) ∧
  LENGTH d = LENGTH s.degrees
  `,
  Induct>>fs[st_ex_FOREACH_def]>>fs msimps >- fs[ra_state_component_equality]>>
  rw[dec_deg_def]>>fs msimps>>fs[degrees_accessor,Marray_sub_def]>>
  reverse IF_CASES_TAC>- fs[good_ra_state_def]>> simp[]>>
  qmatch_goalsub_abbrev_tac`st_ex_FOREACH _ _ ss`>>
  first_x_assum(qspec_then`ss` assume_tac)>>rfs[Abbr`ss`,good_ra_state_def]>>
  simp[ra_state_component_equality]);

val dec_degree_success = Q.prove(`
  ∀ls s.
  good_ra_state s ⇒
  ∃d.
  st_ex_FOREACH ls dec_degree s = (Success (),s with degrees :=d)∧
  LENGTH d = LENGTH s.degrees`,
  Induct>>fs[st_ex_FOREACH_def]>>fs msimps >- fs[ra_state_component_equality]>>
  rw[dec_degree_def]>>fs msimps>>
  fs[get_dim_def]>>
  reverse IF_CASES_TAC>>fs[]>>
  reverse IF_CASES_TAC>-fs[good_ra_state_def]>>
  fs[]>>
  `EVERY (\v. v < s.dim) (EL h s.adj_ls)` by
    fs[good_ra_state_def,EVERY_EL]>>
  drule dec_deg_success>>rw[]>>simp[]>>
  first_x_assum (qspec_then `s with degrees := d` assume_tac)>>
  rfs[good_ra_state_def]>>fs[]>>
  metis_tac[]);

val unspill_success = Q.prove(`
  ∀k s.
  good_ra_state s ⇒
  ∃s' b.
  unspill k s = (Success (),s') ∧
  good_ra_state s' ∧
  is_subgraph s.adj_ls s'.adj_ls ∧
  s.dim = s'.dim ∧
  s.node_tag = s'.node_tag`,
  rw[unspill_def]>> fs msimps>>
  simp[get_dim_def,get_spill_wl_def]>>
  drule st_ex_PARTITION_split_degree>>
  disch_then(qspecl_then[`s.spill_wl`,`k`,`[]:num list`,`[]:num list`] assume_tac)>>
  fs[]>>
  simp[set_spill_wl_def,add_simp_wl_def]>>simp msimps>>
  simp[get_simp_wl_def,set_simp_wl_def]>>
  fs[good_ra_state_def,is_subgraph_def]);

val do_simplify_success = Q.prove(`
  ∀s.
  good_ra_state s ⇒
  ∃s' b.
  do_simplify k s = (Success b,s') ∧
  good_ra_state s' ∧
  is_subgraph s.adj_ls s'.adj_ls ∧
  s.dim = s'.dim ∧
  s.node_tag = s'.node_tag`,
  rw[do_simplify_def]>>fs msimps>>fs[get_simp_wl_def]>>
  rw[]>- fs[is_subgraph_def]>>
  drule dec_degree_success>>
  disch_then(qspec_then`s.simp_wl` assume_tac)>>fs[]>>
  simp([add_stack_def,get_stack_def,set_stack_def,set_simp_wl_def] @msimps)>>
  qmatch_goalsub_abbrev_tac`unspill k ss`>>
  qspecl_then [`k`,`ss`] assume_tac unspill_success >> rfs[Abbr`ss`,good_ra_state_def]);

val st_ex_list_MAX_deg_success = Q.prove(`
  ∀ls s k v acc.
  good_ra_state s ∧
  k < s.dim ⇒
  ∃x y.
  st_ex_list_MAX_deg ls (s.dim) k v acc s = (Success (x,y),s) ∧
  x < s.dim`,
  Induct>>fs[st_ex_list_MAX_deg_def]>>simp msimps>>rw[]>>
  fs[degrees_accessor,Marray_sub_def]>>
  reverse (rw[])>- fs[good_ra_state_def]>>
  rw[]);

val do_spill_success = Q.prove(`
  ∀s.
  good_ra_state s ⇒
  ∃s' b.
  do_spill k s = (Success b,s') ∧
  good_ra_state s' ∧
  is_subgraph s.adj_ls s'.adj_ls ∧
  s.dim = s'.dim ∧
  s.node_tag = s'.node_tag`,
  rw[do_spill_def]>>fs msimps>>fs[get_spill_wl_def]>>fs[get_dim_def]>>
  TOP_CASE_TAC>-fs[is_subgraph_def]>>
  IF_CASES_TAC>-fs[is_subgraph_def]>>
  fs[degrees_accessor,Marray_sub_def]>>
  reverse IF_CASES_TAC>-fs[good_ra_state_def]>>
  fs[]>>
  drule st_ex_list_MAX_deg_success>>
  rw[]>>fs[good_ra_state_def,degrees_accessor,Marray_sub_def]>>
  qmatch_goalsub_abbrev_tac`st_ex_list_MAX_deg ls _ kk vv acc _`>>
  first_x_assum(qspecl_then[`ls`,`kk`,`vv`,`acc`] assume_tac)>>rfs[]>>
  simp[dec_deg_def]>> simp msimps>> simp[degrees_accessor,Marray_sub_def]>>
  qmatch_goalsub_abbrev_tac`unspill k ss`>>
  qspecl_then [`k`,`ss`] mp_tac unspill_success>>
  impl_tac>-
    fs[Abbr`ss`,good_ra_state_def]>>
  rw[]>>simp[add_stack_def]>>simp msimps>>
  simp[get_stack_def,set_stack_def,set_spill_wl_def]>>
  fs[Abbr`ss`,good_ra_state_def]);

val do_step_success = Q.prove(`
  ∀k s.
  good_ra_state s ⇒
  ∃s'.
  do_step k s = (Success (),s') ∧
  good_ra_state s' ∧
  is_subgraph s.adj_ls s'.adj_ls ∧
  s.dim = s'.dim ∧
  s.node_tag = s'.node_tag`,
  rw[do_step_def]>>fs msimps>>
  drule do_simplify_success>>rw[]>>simp[]>>
  IF_CASES_TAC>>fs[]>>
  drule do_spill_success>>rw[]>>simp[]>>
  metis_tac[is_subgraph_trans]);

val rpt_do_step_success = Q.prove(`
  ∀n s k.
    good_ra_state s ⇒
    ∃s'.
      rpt_do_step k n s = (Success (),s') ∧
      good_ra_state s' ∧
      is_subgraph s.adj_ls s'.adj_ls ∧
      s.dim = s'.dim ∧
      s.node_tag = s'.node_tag`,
  Induct>>fs[rpt_do_step_def]>>fs msimps>-fs[is_subgraph_def]>>
  rw[]>>
  drule do_step_success>> disch_then(qspec_then`k` assume_tac)>>rfs[]>>
  metis_tac[is_subgraph_trans,do_step_success]);

val do_alloc1_success = Q.prove(`
  good_ra_state s ⇒
  ∃ls s'.
  do_alloc1 k s = (Success ls,s') ∧
  good_ra_state s' ∧
  is_subgraph s.adj_ls s'.adj_ls ∧
  (* This allows the coalescing phase to modify the adjacency list *)
  s'.dim = s.dim ∧
  s'.node_tag = s.node_tag`,
  rw[do_alloc1_def]>>simp msimps>>
  simp[get_dim_def,init_alloc1_heu_def]>> simp msimps>>
  qmatch_goalsub_abbrev_tac`st_ex_FOREACH ls f s`>>
  `EVERY (λv. v < s.dim) ls` by fs[Abbr`ls`,EVERY_GENLIST] >>
  `?s'. st_ex_FOREACH ls f s = (Success (),s') ∧
  s with degrees := s'.degrees = s' ∧
  good_ra_state s' ∧
  LENGTH s'.degrees = LENGTH s.degrees` by
    (pop_assum mp_tac>>
    pop_assum kall_tac>>
    fs[Abbr`f`]>>
    pop_assum mp_tac>>
    qid_spec_tac`s`>> Induct_on`ls`>>
    fs[st_ex_FOREACH_def]>>fs msimps>>fs[ra_state_component_equality]>>
    reverse (rw[])>-fs[good_ra_state_def]>>
    reverse (rw[])>-fs[good_ra_state_def]>>
    qpat_abbrev_tac`ss = s with degrees := _`>>
    `good_ra_state ss` by
      fs[Abbr`ss`,good_ra_state_def]>>
    first_x_assum drule>> fs[Abbr`ss`])>>
  fs[ra_state_component_equality]>>
  qmatch_goalsub_abbrev_tac`_ is_Atemp _ lss _`>>
  `EVERY (\v. v < s'.dim) lss` by fs[Abbr`lss`]>>
  `∃atemps. st_ex_FILTER is_Atemp ls lss s' = (Success atemps,s') ∧
    EVERY (λv. v < s'.dim) atemps` by
    (qpat_x_assum`EVERY _ ls` mp_tac>>
    qpat_x_assum`good_ra_state s'` mp_tac>>
    qpat_x_assum`EVERY _ lss` mp_tac>>
    qid_spec_tac`lss`>>qid_spec_tac`s'`>>
    rpt (pop_assum kall_tac)>>
    Induct_on`ls`>>fs[st_ex_FILTER_def]>>fs msimps>>
    rw[]>>rfs[is_Atemp_def]>>fs msimps>>
    fs[good_ra_state_def]>>
    rw[])>>
  simp[]>>
  drule st_ex_PARTITION_split_degree >>
  disch_then(qspecl_then[`atemps`,`k`,`lss`,`lss`] assume_tac)>>fs[]>>
  simp[set_simp_wl_def,set_spill_wl_def]>>
  qmatch_goalsub_abbrev_tac`rpt_do_step _ _ ss`>>
  qspecl_then [`LENGTH atemps`,`ss`,`k`] mp_tac rpt_do_step_success>>
  impl_tac>- fs[Abbr`ss`,good_ra_state_def]>>
  rw[]>>simp[get_stack_def]>>
  fs[Abbr`ss`]);

val no_clash_colouring_satisfactory = Q.store_thm("no_clash_colouring_satisfactory",`
  no_clash adjls node_tag ∧
  LENGTH adjls = LENGTH node_tag ∧
  EVERY (λn. n ≠ Stemp ∧ n ≠ Atemp) node_tag
  ⇒
  colouring_satisfactory
    (λf. if f < LENGTH node_tag
    then extract_tag (EL f node_tag)
    else 0) adjls`,
  rw[no_clash_def,colouring_satisfactory_def]>>
  fs[has_edge_def]>>
  first_x_assum (qspecl_then[`f`,`f'`] mp_tac)>>simp[]>>
  fs[EVERY_EL]>>
  TOP_CASE_TAC>>rfs[]>>
  TOP_CASE_TAC>>rfs[]>>
  fs[extract_tag_def]);

val check_partial_col_same_dom = Q.store_thm("check_partial_col_same_dom",`
  ∀ls f g t ft.
  (∀x. MEM x ls ⇒ f x = g x) ⇒
  check_partial_col f ls t ft = check_partial_col g ls t ft`,
  Induct>>fs[check_partial_col_def]>>rw[]>>
  metis_tac[]);

val check_clash_tree_same_dom = Q.store_thm("check_clash_tree_same_dom",`
  ∀ct f g live flive.
  (∀x. in_clash_tree ct x ∨ x ∈ domain live ⇒ f x = g x) ⇒
  check_clash_tree f ct live flive =
  check_clash_tree g ct live flive`,
  Induct>>fs[in_clash_tree_def,check_clash_tree_def]>>rw[]
  >-
    metis_tac[check_partial_col_same_dom,MAP_EQ_f]
  >-
    (fs[check_col_def]>>
    qpat_abbrev_tac`lsf= MAP _ (toAList s)`>>
    qpat_abbrev_tac`lsg= MAP _ (toAList s)`>>
    `lsf = lsg` by
      (unabbrev_all_tac>>fs[MAP_EQ_f,FORALL_PROD,MEM_toAList,domain_lookup])>>
    metis_tac[])
  >-
    (fs[DISJ_IMP_THM,FORALL_AND_THM]>>
    rpt (first_x_assum drule)>>
    rw[]>>EVERY_CASE_TAC>>fs[check_col_def]
    >-
      (imp_res_tac check_clash_tree_domain>>
      match_mp_tac check_partial_col_same_dom>>
      simp[toAList_domain,domain_difference]>>
      fs[SUBSET_DEF]>>
      metis_tac[SUBSET_DEF,IN_UNION])
    >>
      qpat_abbrev_tac`lsf= MAP _ (toAList s)`>>
      qpat_abbrev_tac`lsg= MAP _ (toAList s)`>>
      `lsf = lsg` by
        (unabbrev_all_tac>>fs[MAP_EQ_f,FORALL_PROD,MEM_toAList,domain_lookup])>>
      metis_tac[])
  >>
    fs[DISJ_IMP_THM,FORALL_AND_THM]>>
    rpt (first_x_assum drule)>> rw[]>>
    EVERY_CASE_TAC>>fs[]>>
    first_x_assum match_mp_tac>>
    drule check_clash_tree_domain>>
    fs[SUBSET_DEF]>>
    metis_tac[]);

val opt_split = Q.prove(`
  a ≠ NONE ⇔ a = SOME ()`,
  Cases_on`a`>>fs[]);

val INJ_IMG_lookup = Q.store_thm("INJ_IMG_lookup",`
  ∀x. INJ g UNIV UNIV ∧
  domain (gt:num_set) = IMAGE g (domain ft) ⇒
  lookup (g x) gt = lookup x ft`,
  fs[EXTENSION,domain_lookup,INJ_DEF]>>rw[]>>
  Cases_on`lookup x ft`>>
  CCONTR_TAC>>fs[opt_split]>>
  metis_tac[NOT_SOME_NONE])

val check_partial_col_INJ = Q.store_thm("check_partial_col_INJ",`
  ∀ls t ft gt.
  INJ g UNIV UNIV ∧
  domain gt = IMAGE g (domain ft) ⇒
  case check_partial_col f ls t ft of
    NONE => check_partial_col (g o f) ls t gt = NONE
  | SOME (tt,ftt) =>
    ∃gtt. check_partial_col (g o f) ls t gt = SOME(tt,gtt) ∧
    domain gtt = IMAGE g (domain ftt)`,
  Induct>>fs[check_partial_col_def]>>rw[]>>
  Cases_on`lookup h t`>>fs[]>>
  drule INJ_IMG_lookup>>rfs[]>>
  FULL_CASE_TAC>>fs[]);

val check_col_INJ = Q.store_thm("check_col_INJ",`
  INJ g UNIV UNIV ==>
  case check_col f (s:num_set) of
    NONE => check_col (g o f) s = NONE
  | SOME (t,ft) =>
    ∃gt. check_col (g o f) s = SOME (t,gt) ∧
    domain gt = IMAGE g (domain ft)`,
  fs[check_col_def]>>
  strip_tac>>
  fs[GSYM MAP_MAP_o]>>
  qpat_abbrev_tac`ls = MAP f _`>>
  `ALL_DISTINCT ls ⇔ ALL_DISTINCT (MAP g ls)` by
    (rw[EQ_IMP_THM]>-
      (match_mp_tac ALL_DISTINCT_MAP_INJ>>fs[INJ_DEF])
    >>
    metis_tac[ALL_DISTINCT_MAP])>>
  IF_CASES_TAC>>fs[]>>
  simp[domain_fromAList,MAP_MAP_o]>>
  simp[LIST_TO_SET_MAP,IMAGE_IMAGE]>>
  AP_THM_TAC>>
  AP_TERM_TAC>>
  simp[FUN_EQ_THM]);

val check_clash_tree_INJ = Q.store_thm("check_clash_tree_INJ",`
  ∀ct f g live flive glive.
  INJ g UNIV UNIV ∧
  domain glive = IMAGE g (domain flive)
  ==>
  case check_clash_tree f ct live flive of
    NONE => check_clash_tree (g o f) ct live glive = NONE
  | SOME (liveout,fliveout) =>
    ∃gliveout.
    check_clash_tree (g o f) ct live glive = SOME(liveout,gliveout) ∧
    domain gliveout = IMAGE g (domain fliveout)`,
  Induct>>fs[check_clash_tree_def]>>rw[]
  >-
    (drule check_partial_col_INJ>> disch_then drule>>
    disch_then(qspecl_then[`l`,`live`] mp_tac)>>
    TOP_CASE_TAC>>
    TOP_CASE_TAC>>rw[]>>simp[]>>
    match_mp_tac check_partial_col_INJ>>simp[domain_numset_list_delete]>>
    simp[LIST_TO_SET_MAP,IMAGE_COMPOSE]>>
    match_mp_tac (GSYM IMAGE_DIFF)>>
    match_mp_tac INJ_SUBSET>>
    asm_exists_tac>>fs[])
  >-
    metis_tac[check_col_INJ]
  >-
    (last_x_assum drule>>
    disch_then drule>>
    disch_then (qspecl_then[`f`,`live`] mp_tac)>>
    TOP_CASE_TAC>>simp[]>>
    TOP_CASE_TAC>>simp[]>>rw[]>>
    simp[]>>
    first_x_assum drule>>
    disch_then(qspecl_then[`f`,`live`,`flive`] mp_tac)>>simp[]>>
    disch_then drule>>
    TOP_CASE_TAC>>simp[]>>
    TOP_CASE_TAC>>simp[]>>rw[]>>
    simp[]>>
    Cases_on`o'`>>simp[]
    >-
      (match_mp_tac check_partial_col_INJ>>fs[])
    >>
      metis_tac[check_col_INJ])
  >>
    first_x_assum drule>>
    disch_then drule>>
    disch_then (qspecl_then[`f`,`live`] mp_tac)>>
    TOP_CASE_TAC>>simp[]>>
    TOP_CASE_TAC>>simp[]>>rw[]>>
    first_x_assum drule>>
    disch_then drule>>
    disch_then (qspecl_then[`f`,`q`] mp_tac)>>
    TOP_CASE_TAC>>simp[])

(* The top-most correctness theorem --
*)
val do_reg_alloc_correct = Q.store_thm("do_reg_alloc_correct",`
  ∀k moves ct forced st ta fa n.
  mk_bij ct = (ta,fa,n)==>
  st.adj_ls = REPLICATE n [] ==>
  st.node_tag = REPLICATE n Atemp ==>
  st.degrees = REPLICATE n 0 ==>
  st.dim = n ==>
  (* Needs to be proved in wordLang *)
  EVERY (λx,y.in_clash_tree ct x ∧ in_clash_tree ct y) forced ==>
  ∃spcol st' livein flivein.
    do_reg_alloc k moves ct forced (ta,fa,n) st = (Success spcol,st') ∧
    check_clash_tree (sp_default spcol) ct LN LN = SOME(livein,flivein) ∧
    (∀x. in_clash_tree ct x ⇒
    x ∈ domain spcol ∧
    if is_phy_var x then
      sp_default spcol x = x DIV 2
    else if is_stack_var x then
      k ≤ (sp_default spcol x)
    else
      T) ∧
    (!x. x ∈ domain spcol ⇒ in_clash_tree ct x) ∧
    EVERY (λ(x,y). (sp_default spcol) x = (sp_default spcol) y ⇒ x=y) forced`,
  rw[do_reg_alloc_def,init_ra_state_def,mk_bij_def]>>fs msimps>>
  `(λ(ta,fa,n). (ta,fa,n)) (mk_bij_aux ct (LN,LN,0)) = (mk_bij_aux ct (LN,LN,0))` by (Cases_on `mk_bij_aux ct (LN,LN,0)`>>Cases_on `r`>>fs[])>>
  first_x_assum(fn x => fs[x])>>
  drule mk_bij_aux_domain>>rw[]>>
  drule mk_bij_aux_bij>> impl_tac>-
    simp[sp_inverts_def,lookup_def]>>
  strip_tac>>
  fs[set_dim_def,adj_ls_accessor,Marray_alloc_def,node_tag_accessor,degrees_accessor]>>
  `good_ra_state st` by
    (fs[good_ra_state_def,EVERY_REPLICATE,undirected_def,has_edge_def]>>
    rw[]>>
    `EL x (REPLICATE st.dim []) = []:num list` by fs[EL_REPLICATE]>>fs[])>>
  drule mk_graph_succeeds>>
  disch_then(qspecl_then [`ct`,`sp_default ta`,`[]`] mp_tac)>>simp[is_clique_def]>>
  impl_keep_tac>-(
    CONJ_ASM1_TAC>-
      (rw[]>>fs[sp_inverts_def,EXTENSION,domain_lookup,sp_default_def]>>
      TOP_CASE_TAC>>fs[]>>
      metis_tac[option_nchotomy])>>
    rw[INJ_DEF] >>
    fs[sp_default_def]>>
    pop_assum mp_tac>>
    fs[domain_lookup,EXTENSION]>>
    TOP_CASE_TAC>>fs[]>- metis_tac[option_CLAUSES]>>
    TOP_CASE_TAC>>fs[]>- metis_tac[option_CLAUSES]>>
    fs[sp_inverts_def]>>
    metis_tac[SOME_11])>>
  strip_tac>>fs[]>>
  drule extend_graph_succeeds>>
  disch_then(qspecl_then[`forced`,`sp_default ta`] mp_tac)>>
  impl_tac>- (
    fs[EVERY_MEM,sp_inverts_def,FORALL_PROD]>>ntac 3 strip_tac>>
    first_x_assum drule>>fs[EXTENSION,domain_lookup,sp_default_def]>>
    strip_tac>>
    last_assum(qspec_then `p_1` assume_tac)>>
    last_x_assum(qspec_then `p_2` assume_tac)>>
    rfs[]>>
    fs[good_ra_state_def,ra_state_component_equality]>>
    metis_tac[])>>
  rw[]>>simp[]>>
  `is_subgraph s'.adj_ls s''.adj_ls` by
    fs[is_subgraph_def]>>
  qpat_x_assum`!a b. _`mp_tac>>
  qmatch_goalsub_abbrev_tac`hide ⇒ _`>>
  drule (GEN_ALL mk_tags_succeeds)>>
  disch_then(qspecl_then[`st.dim`,`sp_default fa`] mp_tac)>>
  impl_tac>-
    fs[ra_state_component_equality]>>
  rw[]>>simp[]>>
  drule do_alloc1_success>>rw[]>>simp[]>>
  `no_clash s''''.adj_ls s''''.node_tag` by
    (fs[no_clash_def,has_edge_def]>>rw[]>>
    rfs[good_ra_state_def,ra_state_component_equality]>>
    res_tac>>
    qpat_x_assum(`!x. _`) kall_tac>>
    ntac 2 (pop_assum mp_tac)>>
    reverse (rpt (IF_CASES_TAC >> simp[]))>>
    rw[]>>
    fs[sp_default_def,sp_inverts_def,domain_lookup,EXTENSION]>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>- metis_tac[option_CLAUSES]>>
    TOP_CASE_TAC>- metis_tac[option_CLAUSES]>>
    fs[is_phy_var_def]>>
    rw[]>>
    `x' = x''` by
      (fs[GSYM EVEN_MOD2,EVEN_EXISTS]>>rw[]>>
      fs[TWOxDIV2])>>
    metis_tac[option_CLAUSES])>>
  drule assign_Atemps_correct>>simp[]>>
  qmatch_goalsub_abbrev_tac`assign_Atemps _ _ (biased_pref mov)`>>
  disch_then (qspecl_then[`k`,`ls`,`biased_pref mov`] assume_tac)>>
  fs[good_pref_biased_pref]>>
  drule assign_Stemps_correct>>rw[]>>simp[]>>
  drule (GEN_ALL extract_color_succeeds)>>
  disch_then(qspec_then`ta` mp_tac)>>
  impl_tac>-
    (rw[]
    >-
      (fs[ra_state_component_equality]>>
      fs[sp_inverts_def,EXTENSION,domain_lookup]>>
      metis_tac[])
    >>
      drule mk_bij_aux_wf>>fs[wf_def,markerTheory.Abbrev_def])>>
  rw[]>>simp[]>>
  drule no_clash_colouring_satisfactory >>
  impl_keep_tac>- (
    fs[good_ra_state_def,EVERY_EL,ra_state_component_equality]>>
    rfs[]>>
    ntac 2 strip_tac>>
    first_x_assum drule>> IF_CASES_TAC>> fs[]>> strip_tac>>
    rfs[])>>
  qmatch_goalsub_abbrev_tac`colouring_satisfactory col _`>>
  rw[]>>
  drule mk_graph_check_clash_tree>>
  disch_then(qspecl_then[`col`,`LN`,`LN`] mp_tac)>>
  impl_tac>-
    (fs[is_clique_def]>>
    fs[ra_state_component_equality]>>
    metis_tac[colouring_satisfactory_subgraph,is_subgraph_trans])>>
  strip_tac>>fs[]>>
  qexists_tac`livein'`>>
  qexists_tac`flivein`>>
  qpat_x_assum`_ = SOME _` sym_sub_tac>>
  CONJ_TAC>-
    (match_mp_tac check_clash_tree_same_dom>>rw[]>>
    simp[sp_default_def,lookup_map,Abbr`col`]>>
    fs[EXTENSION,domain_lookup]>>
    last_x_assum (qspec_then `x` assume_tac)>>rfs[]>>
    fs[sp_inverts_def,ra_state_component_equality,good_ra_state_def]>>
    rfs[]>>
    metis_tac[])>>
  CONJ_TAC>- (
    ntac 2 strip_tac>>
    fs[domain_lookup,EXTENSION]>>
    last_x_assum (qspec_then `x` assume_tac)>>rfs[]>>
    fs[sp_inverts_def]>> first_x_assum drule>>
    simp[sp_default_def,lookup_map]>>
    rfs[ra_state_component_equality,good_ra_state_def]>>
    fs[good_ra_state_def]>>
    strip_tac>>
    (qpat_x_assum`!x. x < n ⇒ if is_phy_var _ then _ else _` (qspec_then`v` assume_tac))>>rfs[]>>
    `sp_default fa v = x` by
      (fs[sp_default_def]>>
      res_tac>>fs[])>>
    fs[]>>
    IF_CASES_TAC>>fs[]
    >-
      (`EL v s'''.node_tag ≠ Atemp ∧ EL v s'''.node_tag ≠ Stemp` by fs[]>>
      res_tac>>fs[]>>
      rfs[extract_tag_def])
    >>
      strip_tac>>fs[]>>
      (`EL v s'''.node_tag ≠ Atemp` by fs[]>>
      res_tac>>fs[]>>
      rfs[extract_tag_def]))>>
  CONJ_TAC>-
    fs[domain_map]>>
  fs[EVERY_MEM,FORALL_PROD]>>rw[]>>
  last_x_assum drule>>
  strip_tac>>
  fs[sp_default_def,lookup_map]>>
  `p_1 ∈ domain ta ∧ p_2 ∈ domain ta` by fs[EXTENSION]>>
  fs[domain_lookup]>>fs[]>>
  fs[no_clash_def]>>
  first_x_assum(qspecl_then [`v`,`v'`] mp_tac)>>
  impl_tac>-
    (fs[markerTheory.Abbrev_def]>>
    `is_subgraph s''.adj_ls s''''''.adj_ls` by
      (fs[ra_state_component_equality]>>
      metis_tac[])>>
    qsuff_tac`has_edge s''.adj_ls v v'`>-
      fs[is_subgraph_def]>>
    simp[]>>
    DISJ2_TAC>>DISJ1_TAC>>
    qexists_tac`p_1`>>qexists_tac`p_2`>>simp[])>>
  strip_tac>>
  qsuff_tac`v=v'`
  >-
    (qpat_x_assum`INJ _ _ _` mp_tac>>
    simp[INJ_DEF,sp_default_def])
  >>
  pop_assum mp_tac>>
  fs[MEM_EL,PULL_EXISTS]>>
  `LENGTH s''''''.node_tag = st.dim` by
    fs[ra_state_component_equality,good_ra_state_def]>>
  first_assum(qspec_then`v` mp_tac)>>
  impl_tac>-
    (fs[sp_inverts_def]>>
    metis_tac[domain_lookup,IN_COUNT,good_ra_state_def])>>
  first_x_assum(qspec_then`v'` mp_tac)>>
  impl_tac>-
    (fs[sp_inverts_def]>>
    metis_tac[domain_lookup,IN_COUNT,good_ra_state_def])>>
  qpat_x_assum`extract_tag _ = _ ` mp_tac>>
  rpt(pop_assum kall_tac)>>
  fs[extract_tag_def]>>
  every_case_tac>>simp[]);

fun first_prove_imp thms =
  (first_assum(fn x => sg `^(fst(dest_imp(concl x)))`) >- (fs thms) >>
  POP_ASSUM(fn x  => fs[x]));

(* The top-most correctness theorem --
*)
val reg_alloc_correct = Q.store_thm("reg_alloc_correct",`
  ∀k moves ct forced.
  (* Needs to be proved in wordLang *)
  EVERY (λx,y.in_clash_tree ct x ∧ in_clash_tree ct y) forced ==>
  ∃spcol livein flivein.
    reg_alloc k moves ct forced = Success spcol ∧
    check_clash_tree (sp_default spcol) ct LN LN = SOME(livein,flivein) ∧
    (∀x. in_clash_tree ct x ⇒
    x ∈ domain spcol ∧
    if is_phy_var x then
      sp_default spcol x = x DIV 2
    else if is_stack_var x then
      k ≤ (sp_default spcol x)
    else
      T) ∧
    (!x. x ∈ domain spcol ⇒ in_clash_tree ct x) ∧
    EVERY (λ(x,y). (sp_default spcol) x = (sp_default spcol) y ⇒ x=y) forced`,
  rw[reg_alloc_def]>>
  Cases_on `mk_bij ct`>>Cases_on`r`>>rw[]>>
  rw[reg_alloc_aux_def,run_ira_state_def,run_def]>>
  qmatch_goalsub_abbrev_tac `do_reg_alloc _ _ _ _ _ st` >>
  qmatch_goalsub_abbrev_tac `(ta,fa,n)` >>
  ASSUME_TAC (Q.SPECL [`k`,`moves`,`ct`,`forced`,`st`,`ta`,`fa`,`n`] do_reg_alloc_correct)>>
  first_x_assum drule >> rw[] >>
  first_prove_imp [Abbr `st`,ra_state_component_equality] >>
  first_prove_imp [Abbr `st`,ra_state_component_equality] >>
  first_prove_imp [Abbr `st`,ra_state_component_equality] >>
  first_prove_imp [Abbr `st`,ra_state_component_equality] >>
  first_x_assum drule);
(* --- --- *)

val _ = export_theory ();

