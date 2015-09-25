open preamble
open monadsyntax state_transformerTheory
open reg_allocTheory 

val _ = ParseExtras.temp_tight_equality ();

val _ = new_theory "reg_allocProof";

val convention_partitions = store_thm("convention_partitions",``
  ∀n. (is_stack_var n ⇔ (¬is_phy_var n) ∧ ¬(is_alloc_var n)) ∧
      (is_phy_var n ⇔ (¬is_stack_var n) ∧ ¬(is_alloc_var n)) ∧
      (is_alloc_var n ⇔ (¬is_phy_var n) ∧ ¬(is_stack_var n))``,
  rw[is_stack_var_def,is_phy_var_def,is_alloc_var_def,EQ_IMP_THM]
  \\ `n MOD 2 = (n MOD 4) MOD 2` by
   (ONCE_REWRITE_TAC [GSYM (EVAL ``2*2:num``)]
    \\ fs [arithmeticTheory.MOD_MULT_MOD])
  \\ fs []
  \\ `n MOD 4 < 4` by fs []
  \\ IMP_RES_TAC (DECIDE
       ``n < 4 ==> (n = 0) \/ (n = 1) \/ (n = 2) \/ (n = 3:num)``)
  \\ fs []);

val in_clash_sets_def = Define`
  in_clash_sets (ls: ('a num_map) list) x = ∃y. MEM y ls ∧ x ∈ domain y`

(* 
  Clash sets always appear as cliques in the graph
  colouring_satisfactory guarantees that cliques have all distinct colours
*)

val lookup_dir_g_insert_correct = prove(``
  ∀x y g.
  let g' = dir_g_insert x y g in
  lookup_g x y g' = T ∧
  ∀x' y'.
    x' ≠ x ∨ y' ≠ y ⇒
    lookup_g x' y' g' = lookup_g x' y' g``,
  fs[dir_g_insert_def,LET_THM,lookup_g_def]>>
  ntac 3 strip_tac>>CONJ_ASM1_TAC
  >-
    (every_case_tac>>fs[domain_insert])
  >>
    rw[]>>fs[lookup_insert]>>
    Cases_on`x'=x`>>fs[]>>
    full_case_tac>>
    fs[domain_insert,lookup_insert,lookup_def])

val list_g_insert_correct = prove(``
  ∀ls x g.
  let g' = list_g_insert x ls g in
    ∀u v.
      lookup_g u v g' = ((u = x ∧ MEM v ls)
                      ∨ (v = x ∧ MEM u ls)
                      ∨ lookup_g u v g)``,
  Induct>>rw[list_g_insert_def,undir_g_insert_def]>>
  unabbrev_all_tac>>fs[]>-
    (fs[lookup_g_def]>>every_case_tac>>fs[lookup_insert]>>
    every_case_tac>>fs[]>>qpat_assum`LN = x'` (SUBST_ALL_TAC o SYM)>>
    fs[lookup_def])>>
  metis_tac[lookup_dir_g_insert_correct])

val clique_g_insert_correct = prove(``
  !ls x g.
  ALL_DISTINCT ls ⇒
  let g' = clique_g_insert ls g in
    ∀u v.
      lookup_g u v g' = ((MEM u ls ∧ MEM v ls ∧ u ≠ v)
                      ∨ lookup_g u v g)``,
  Induct>>rw[clique_g_insert_def]>>
  unabbrev_all_tac>>metis_tac[list_g_insert_correct])

(*Cliques in sp_g*)
val sp_g_is_clique_def = Define`
  (sp_g_is_clique ls g =
    !x y. MEM x ls ∧ MEM y ls ∧ x ≠ y⇒
      lookup_g x y g ∧ lookup_g y x g)`

(*colouring_satisfactory for sp_graphs*)
val colouring_satisfactory_def = Define `
  (colouring_satisfactory col (G:sp_graph) =
  ∀v. v ∈ domain G ⇒
    let edges = lookup v G in
    case edges of NONE => F
                | SOME edges => ∀e. e ∈ domain edges ⇒ col e ≠ col v)`

val clique_g_insert_is_clique = prove(``
  !ls g.
  sp_g_is_clique ls (clique_g_insert ls g)``,
  Induct>>
  rw[clique_g_insert_def,sp_g_is_clique_def]>>
  TRY (metis_tac[list_g_insert_correct])
  >>
    fs[sp_g_is_clique_def]>>
    metis_tac[list_g_insert_correct])

val clique_g_insert_preserves_clique = prove(``
  !ls g ls'.
  ALL_DISTINCT ls' ∧
  sp_g_is_clique ls g ⇒
  sp_g_is_clique ls (clique_g_insert ls' g)``,
  Induct>>
  rw[clique_g_insert_def,sp_g_is_clique_def]>>
  metis_tac[clique_g_insert_correct])

val clash_sets_clique = store_thm("clash_sets_clique",``
  ∀ls x.
  MEM x ls ⇒
  sp_g_is_clique (MAP FST (toAList x)) (clash_sets_to_sp_g ls)``,
  Induct>>fs[clash_sets_to_sp_g_def]>>rw[]>>
  unabbrev_all_tac>>
  metis_tac[clique_g_insert_is_clique
           ,clique_g_insert_preserves_clique,ALL_DISTINCT_MAP_FST_toAList])

val colouring_satisfactory_cliques = store_thm("colouring_satisfactory_cliques",``
  ∀ls g (f:num->num).
  ALL_DISTINCT ls ∧
  colouring_satisfactory f g ∧ sp_g_is_clique ls g
  ⇒
  ALL_DISTINCT (MAP f ls)``,
  Induct>>
  fs[sp_g_is_clique_def,colouring_satisfactory_def]>>
  rw[]
  >-
    (fs[MEM_MAP]>>rw[]>>
    first_x_assum(qspecl_then [`h`,`y`] assume_tac)>>rfs[]>>
    Cases_on`MEM y ls`>>Cases_on`h=y`>>fs[]>>
    fs[lookup_g_def]>>every_case_tac>>fs[]>>
    imp_res_tac domain_lookup>>
    res_tac>>fs[LET_THM]>>
    Cases_on`lookup y g`>>fs[])
  >>
    first_x_assum(qspecl_then [`g`,`f`] mp_tac)>>rfs[])

(*Final colouring conventions*)
val colouring_conventional_def = Define`
  colouring_conventional (G:sp_graph) k col ⇔
  let vertices = domain G in
  ∀x. x ∈ vertices ⇒
    if is_phy_var x then col x = x
    else
    let y = col x in
    if is_stack_var x then
       is_phy_var y ∧ y ≥ 2*k
    else
    (*x must be an alloc var and it must go to some y*)
       is_phy_var y`

(*Undirected irreflexive (simple) graph*)
val undir_graph_def = Define`
  undir_graph (G:sp_graph) =
    ∀x.
    case lookup x G of
      NONE => T
    | SOME es =>
      x ∉ domain es ∧
      ∀y. y ∈ domain es ⇒
      ∃z. lookup y G = SOME z ∧ x ∈ domain z`

(*Property of preference function, it only chooses a colour it is given*)
val satisfactory_pref_def = Define`
  satisfactory_pref prefs ⇔
    ∀h ls col v. prefs h ls col = SOME v ⇒ MEM v ls`

(*
  We need to show 2 things:
  1) The total colouring generated is satisfactory
  2) The total colouring generated is conventional
*)

val aux_pref_satisfactory = prove(``
  ∀prefs.
  satisfactory_pref (aux_pref prefs)``,
  fs[satisfactory_pref_def,aux_pref_def,LET_THM]>>rw[]>>
  every_case_tac>>
  Cases_on`ls`>>fs[]>>
  metis_tac[])

val first_match_col_mem = prove(``
  ∀ls.
  first_match_col cand col ls = SOME x
  ⇒ MEM x cand``,
  Induct>>rw[first_match_col_def]>>
  Cases_on`h`>>fs[first_match_col_def,LET_THM]>>
  every_case_tac>>rfs[])

val move_pref_satisfactory = prove(``
  ∀moves.
  satisfactory_pref (move_pref moves)``,
  fs[satisfactory_pref_def,move_pref_def,LET_THM]>>rw[]>>
  every_case_tac>>Cases_on`ls`>>fs[]>>
  imp_res_tac first_match_col_mem>>
  fs[])

val aux_move_pref_satisfactory = prove(``
  ∀prefs moves.
  satisfactory_pref (aux_move_pref prefs moves)``,
  fs[satisfactory_pref_def,aux_move_pref_def,LET_THM]>>rw[]>>
  every_case_tac>>
  metis_tac[aux_pref_satisfactory,move_pref_satisfactory,satisfactory_pref_def])

val id_colour_lemma = prove(``
  ∀ls.
  let t = id_colour ls in
  domain t = set ls ∧
  ∀x. (MEM x ls ⇒ lookup x t = SOME x)``,
  Induct>>fs[id_colour_def,LET_THM,lookup_insert]>>rw[])

(*alloc_colouring_aux never overwrites an old colouring*)
val alloc_colouring_aux_never_overwrites_col = prove(``
  ∀xs spill col spill' col'.
  lookup x col = SOME y ∧
  alloc_colouring_aux G k prefs xs col spill = (col',spill')
  ⇒
  lookup x col' = SOME y``,
  Induct>>fs[alloc_colouring_aux_def,assign_colour_def]>>rw[]>>fs[LET_THM]>>
  Cases_on`x = h`>>fs[]>>rfs[]
  >-
    metis_tac[]
  >>
  every_case_tac>>fs[]>>TRY(metis_tac[])>>
  res_tac>>fs[lookup_insert])

val alloc_colouring_aux_never_overwrites_spill = prove(``
  ∀xs spill col spill' col'.
  MEM x spill ∧
  alloc_colouring_aux G k prefs xs col spill = (col',spill')
  ⇒
  MEM x spill'``,
  Induct>>fs[alloc_colouring_aux_def,assign_colour_def]>>rw[]>>fs[LET_THM]>>
  every_case_tac>>fs[]>>
  TRY(`MEM x (h::spill')` by (fs[]>>NO_TAC))>>
  metis_tac[])

(*Coloring satisfactory but restricted to a partial colouring
  i.e. only talk about the subgraph induced by the vertices
  in the domain of the colouring
*)
val partial_colouring_satisfactory_def = Define`
  partial_colouring_satisfactory col (G:sp_graph) ⇔
  domain col ⊆ domain G ∧
  ∀v.
    v ∈ domain G ∧ v ∈ domain col ⇒
    let edges = THE (lookup v G) in
    ∀v'. v' ∈ domain edges ∧ v' ∈ domain col ⇒ lookup v col ≠ lookup v' col`

val remove_colours_removes = prove(``
  ∀ls col k ls'.
  remove_colours col ls k = ls'
  ⇒
  ∀x. MEM x ls' ⇒
  MEM x k ∧
  (∀y c. MEM y ls ∧ lookup y col = SOME c ⇒ c ≠ x)``,
  Induct>>fs[]>>rw[]>>
  Cases_on`k`>>
  fs[remove_colours_def,LET_THM]
  >-
    (full_case_tac>>fs[]>-
    (res_tac>>pop_assum(qspec_then `y` assume_tac)>>fs[])>>
    Cases_on`h'=x'`>>fs[]>>res_tac>>
    fs[MEM_FILTER])
  >>
    full_case_tac>>fs[]>-
      (res_tac>>pop_assum(qspec_then`y` assume_tac)>>
      Cases_on`y=h`>>fs[])>>
    res_tac>>
    Cases_on`h'=x'`>>fs[]>>
    first_x_assum(qspec_then`y` assume_tac)>>
    Cases_on`y=h`>>fs[MEM_FILTER]>>metis_tac[])

val partial_colouring_satisfactory_extend = prove(``
  partial_colouring_satisfactory col G ∧
  undir_graph G ∧
  h ∉ domain col ∧
  lookup h G = SOME x ∧
  (∀y. y ∈ domain x ∧
       y ∈ domain col ⇒
       THE (lookup y col) ≠ (v:num))
  ⇒
  partial_colouring_satisfactory (insert h v col) G``,
  fs[partial_colouring_satisfactory_def]>>rpt strip_tac
  >-
    fs[domain_lookup]
  >-
    (fs[domain_lookup,LET_THM,lookup_insert,undir_graph_def]>>rw[]
    >-
      (ntac 2 (last_x_assum(qspec_then`h`mp_tac))>>fs[])
    >>
      rfs[]>>
      first_x_assum(qspec_then`v'''`mp_tac)>>discharge_hyps>>fs[])
  >>
    fs[domain_lookup,LET_THM,lookup_insert,undir_graph_def]>>rw[]
    >-
      (ntac 2 (last_x_assum(qspec_then`h`mp_tac))>>fs[])
    >-
      (rfs[]>>
      first_x_assum(qspec_then`v'''`mp_tac)>>discharge_hyps>>fs[])
    >-
      (
      qsuff_tac`lookup v' x = SOME ()`>-
      (rw[]>>
      first_x_assum(qspec_then`v'` assume_tac)>>
      rfs[])>>
      last_x_assum(qspec_then`v'`mp_tac)>>discharge_hyps>>fs[]>>rw[]>>
      last_x_assum(qspec_then`v'`assume_tac)>>rfs[]>>
      first_x_assum(qspec_then`h`assume_tac)>>rfs[])
    >>
      fs[]>>
      last_x_assum(qspec_then`v'`mp_tac)>>discharge_hyps>>fs[]>>rw[]>>
      pop_assum(qspec_then`v''''`assume_tac)>>rfs[])

(*Coloring produced after each alloc_colouring_aux_step is
  partial_colouring_satisfactory*)
val alloc_colouring_aux_satisfactory = prove(``
  ∀G k prefs ls col spill.
  undir_graph G ∧
  satisfactory_pref prefs ∧
  partial_colouring_satisfactory col G
  ⇒
  let (col',spill') = alloc_colouring_aux G k prefs ls col spill in
    partial_colouring_satisfactory col' G``,
  Induct_on`ls`>>fs[alloc_colouring_aux_def,assign_colour_def,LET_THM]>>rw[]>>
  every_case_tac>>fs[]>>
  TRY
  (first_x_assum(qspecl_then
    [`G`,`k`,`prefs`,`insert h h' col`,`spill'`] mp_tac)>>
  discharge_hyps>>fs[]>>
  match_mp_tac partial_colouring_satisfactory_extend>>rw[]>>
  fs[domain_lookup]>>
  imp_res_tac remove_colours_removes>>
  fs[satisfactory_pref_def]>>
  first_x_assum(qspecl_then[`h`,`h'::t`,`col`] assume_tac))>>
  TRY
  (first_x_assum(qspecl_then
    [`G`,`k`,`prefs`,`insert h x' col`,`spill'`] mp_tac)>>
  discharge_hyps>>fs[]>>
  match_mp_tac partial_colouring_satisfactory_extend>>rw[]>>
  fs[domain_lookup]>>
  imp_res_tac remove_colours_removes>>
  imp_res_tac satisfactory_pref_def>>
  first_x_assum(qspecl_then[`x'`] assume_tac))>>
  rfs[]>>
  `MEM y (MAP FST (toAList x))` by
    fs[MEM_MAP,MEM_toAList,EXISTS_PROD,domain_lookup]>>
  rfs[]>>res_tac>>
  metis_tac[])

(*Domains of the colouring and spills are disjoint*)
val alloc_colouring_aux_domain_1 = prove(``
  ∀G k prefs ls col spill col' spill'.
  domain col ∩ set spill = {} ∧
  alloc_colouring_aux G k prefs ls col spill = (col',spill')
  ⇒
  domain col' ∩ set spill' = {}``,
  Induct_on`ls`>>fs[alloc_colouring_aux_def,LET_THM,assign_colour_def]>>rw[]
  >-(every_case_tac>>fs[]>>metis_tac[])
  >>
  Cases_on`lookup h col`>>fs[]
  >-
    (Cases_on`lookup h G`>>fs[]
    >- metis_tac[]
    >>
    `h ∉ domain col` by fs[domain_lookup]>>
    `domain col ∩ set (h::spill') = {}` by
      (fs[EXTENSION]>>rw[]>>Cases_on`x'=h`>>fs[])>>
    Cases_on`is_alloc_var h`>>fs[]
    >-
      (full_case_tac>>fs[]
      >-
        (res_tac>>fs[])
      >>
        res_tac>>pop_assum mp_tac>>discharge_hyps>>
        fs[domain_insert,EXTENSION]>>rw[]>>
        Cases_on`x'=h`>>fs[])
    >>
      res_tac>>fs[])
  >>
    metis_tac[domain_lookup])

(*Coloring and spills contain everything in the list*)
val alloc_colouring_aux_domain_2 = prove(``
  ∀G k prefs ls col spill col' spill'.
  alloc_colouring_aux G k prefs ls col spill = (col',spill')
  ⇒
  ∀x. MEM x ls ∧ x ∈ domain G ⇒
    x ∈ domain col' ∨ MEM x spill'``,
  Induct_on`ls`>>reverse (rw[alloc_colouring_aux_def,UNCURRY,LET_THM])>>fs[]
  >- metis_tac[]
  >>
  fs[assign_colour_def,LET_THM]>>every_case_tac>>
  imp_res_tac alloc_colouring_aux_never_overwrites_col>>
  imp_res_tac alloc_colouring_aux_never_overwrites_spill>>
  fs[domain_lookup]>>
  metis_tac[lookup_insert])

val assign_colour_props = prove(``
  h ∉ domain col ∧
  ¬MEM h spill' ∧
  h ∈ domain G ∧
  (∀x. MEM x k ⇒ is_phy_var x) ∧
  domain col ∩ set spill' = {} ∧
  satisfactory_pref prefs
  ⇒
  let (col',spill'') = assign_colour G k prefs h col spill' in
    (if is_alloc_var h then
      if h ∈ domain col' then
        spill'' = spill' ∧
        ∃y. col' = insert h y col ∧ is_phy_var y
      else col = col' ∧ MEM h spill''
    else col = col' ∧ MEM h spill'') ∧
    domain col' ∩ set spill'' = {}``,
  rpt strip_tac>>
  fs[assign_colour_def]>>
  `lookup h col = NONE` by
    metis_tac[domain_lookup,optionTheory.option_CLAUSES]>>
  fs[domain_lookup]>>
  IF_CASES_TAC>>fs[LET_THM]>>
  qabbrev_tac `lss = MAP FST (toAList v)`>>
  Cases_on`remove_colours col lss k`>>fs[]>>
  imp_res_tac remove_colours_removes>>
  every_case_tac>>
  imp_res_tac satisfactory_pref_def>>
  TRY(`h ∉ domain col` by fs[domain_lookup]>>
  fs[EXTENSION,INTER_DEF]>>metis_tac[]))

(*Conventions over the extension domain*)
val alloc_colouring_aux_domain_3 = prove(``
  ∀G:sp_graph k prefs ls col spill col' spill'.
  (∀x. MEM x k ⇒ is_phy_var x) ∧
  (domain col ∩ set spill = {}) ∧
  (satisfactory_pref prefs) ∧
  alloc_colouring_aux G k prefs ls col spill = (col',spill')
  ⇒
  ∀x. MEM x ls ∧ x ∉ domain col ∧ ¬MEM x spill ∧ x ∈ domain G ⇒
    (if is_alloc_var x then
      if x ∈ domain col' then
        ∃y. lookup x col' = SOME y ∧ is_phy_var y
      else MEM x spill'
    else MEM x spill')``,
  Induct_on`ls`>>rw[alloc_colouring_aux_def,LET_THM]
  >-
    (imp_res_tac assign_colour_props>>fs[LET_THM]>>
    IF_CASES_TAC>>
    Cases_on`assign_colour G k prefs h col spill'`>>fs[]>>
    Cases_on`h ∈ domain q`>>fs[]
    >-
      (fs[domain_lookup]>>
      metis_tac[lookup_insert,alloc_colouring_aux_never_overwrites_col])
    >>
    imp_res_tac alloc_colouring_aux_never_overwrites_spill>>
    imp_res_tac alloc_colouring_aux_domain_1>>
    `h ∉ domain col'` by
        (fs[INTER_DEF,EXTENSION]>>
        metis_tac[])>>
    fs[])
  >>
    Cases_on`x=h`>>fs[]
    >-
    (imp_res_tac assign_colour_props>>fs[LET_THM]>>
    IF_CASES_TAC>>
    Cases_on`assign_colour G k prefs h col spill'`>>fs[]>>
    Cases_on`h ∈ domain q`>>fs[]
    >-
      (fs[domain_lookup]>>
      metis_tac[lookup_insert,alloc_colouring_aux_never_overwrites_col])
    >>
    imp_res_tac alloc_colouring_aux_never_overwrites_spill>>
    imp_res_tac alloc_colouring_aux_domain_1>>
    `h ∉ domain col'` by
        (fs[INTER_DEF,EXTENSION]>>
        metis_tac[])>>
    fs[])
    >>
    fs[assign_colour_def]>>
    Cases_on`lookup h col`>>
    Cases_on`MEM h spill'`>>
    Cases_on`lookup h G` >>
    Cases_on`is_alloc_var h`>>fs[]>>
    TRY(res_tac>>NO_TAC)>>
    `¬MEM x (h::spill')` by fs[]>>
    `domain col ∩ set (h::spill') = {}` by
      (fs[EXTENSION,INTER_DEF]>>rw[]>>
      Cases_on`x''=h`>>fs[domain_lookup])
    >-
      (fs[LET_THM]>>
      Cases_on`remove_colours col(MAP FST (toAList x')) k`>>
      fs[]
      >-
        (first_x_assum(qspecl_then [`G`,`k`,`prefs`,`col`,`(h::spill')`
                     ,`col'`,`spill''`] mp_tac)>>
        discharge_hyps>>fs[])
      >>
        qpat_assum `A = (col',spill'')` mp_tac>>
        qpat_abbrev_tac `coln = insert h A col`>>
        `x ∉ domain coln` by
          fs[Abbr`coln`]>>
        strip_tac>>
        first_x_assum(qspecl_then [`G`,`k`,`prefs`,`coln`,`spill'`
                     ,`col'`,`spill''`] mp_tac)>>
        discharge_hyps>>fs[EXTENSION,INTER_DEF]>>
        rw[Abbr`coln`]>>Cases_on`x''=h`>>fs[])
    >>
    res_tac)

val list_mem = prove(``
  ∀ls ls'.
    MEM x ls ∧ (h::ls') = ls ∧ x ≠ h
    ⇒
    MEM x ls'``,
  rw[]>>fs[])

(*If not the assigned colour then it must have come from before*)
val assign_colour_reverse = prove(``
  ∀G:sp_graph k prefs h col spill col' spill'.
  assign_colour G k prefs h col spill = (col',spill')
  ⇒
  (∀x. x ≠ h ⇒
  (x ∈ domain col' ⇒ x ∈ domain col) ∧
  (MEM x spill' ⇒ MEM x spill))``,
  rw[assign_colour_def]>>every_case_tac>>fs[LET_THM]>>
  every_case_tac>>fs[]>>
  qpat_assum `A = col'` (SUBST_ALL_TAC o SYM)>>
  fs[domain_insert]>>metis_tac[list_mem])

(*Not in the final state means it must have come from before*)
val alloc_colouring_aux_domain_4 = prove(``
  ∀G:sp_graph k prefs ls col spill col' spill'.
  alloc_colouring_aux G k prefs ls col spill = (col',spill')
  ⇒
  ∀x. ¬MEM x ls ⇒
  (x ∈ domain col' ⇒ x ∈ domain col) ∧
  (MEM x spill' ⇒ MEM x spill)``,
  Induct_on`ls`>>rw[alloc_colouring_aux_def,LET_THM]>>
  Cases_on`assign_colour G k prefs h col spill'`>>fs[]>>
  metis_tac[assign_colour_reverse])

(*Everything appearing in the spills was already in G*)
val alloc_colouring_aux_domain_5 = prove(``
  ∀G:sp_graph k prefs ls col spill col' spill'.
  alloc_colouring_aux G k prefs ls col spill = (col',spill')
  ⇒
  ∀x. MEM x spill' ⇒
  x ∈ domain G ∨ MEM x spill``,
  Induct_on`ls`>>rw[alloc_colouring_aux_def,LET_THM]>>
  Cases_on`assign_colour G k prefs h col spill'`>>
  fs[]>>
  res_tac>>
  fs[assign_colour_def]>>
  every_case_tac>>fs[LET_THM]>>
  every_case_tac>>fs[]>>
  qpat_assum`A=r` (SUBST_ALL_TAC o SYM)>>
  fs[domain_lookup])

val id_colour_always_sat = prove(``
  undir_graph G ∧
  (∀x. MEM x ls ⇒ x ∈ domain G)
  ⇒
  partial_colouring_satisfactory (id_colour ls) G``,
  Q.ISPEC_THEN `ls` assume_tac id_colour_lemma>>
  rw[undir_graph_def,partial_colouring_satisfactory_def]>>
  fs[LET_THM]>-
    fs[SUBSET_DEF]
  >>
  qsuff_tac `v ≠ v'`
  >-
    (`MEM v ls ∧ MEM v' ls` by metis_tac[EXTENSION]>>
    res_tac>>
    fs[])
  >>
    first_x_assum(qspec_then `v` assume_tac)>>
    first_x_assum(qspec_then `v` assume_tac)>>
    fs[domain_lookup]>>rfs[]>>
    metis_tac[])

(*The first colouring should produce a partial colouring such that:
  Phy vars are mapped to themselves
  Stack vars are all in spills
  Alloc vars are either spilled (exclusive)OR in the colouring
*)
val alloc_colouring_success = prove(``
  undir_graph G ∧ satisfactory_pref prefs ⇒
  let (col,spills) = alloc_colouring G k prefs ls in
  partial_colouring_satisfactory col G ∧
  domain col ∩ set spills = {} ∧
  ∀x. x ∈ domain G ⇒
    if is_phy_var x then lookup x col = SOME x
    else if is_stack_var x then MEM x spills
    else (*is_alloc_var x*)
      if x ∈ domain col then
        ∃y. lookup x col = SOME y ∧ is_phy_var y
      else MEM x spills``,
  fs[alloc_colouring_def]>>rw[]
  >-
    (imp_res_tac alloc_colouring_aux_satisfactory>>
    ntac 2 (pop_assum kall_tac)>>
    first_assum(qspec_then`col` mp_tac)>>
    discharge_hyps
    >-
      (fs[Abbr`col`]>>
      match_mp_tac id_colour_always_sat>>
      fs[PARTITION_DEF]>>
      rw[]>>
      `MEM x vertices` by
        (qpat_assum `A=(phy_var,others)` (assume_tac o SYM)>>
        imp_res_tac PART_MEM>>
        fs[])>>
      unabbrev_all_tac>>
      fs[MEM_MAP]>>Cases_on`y`>>fs[MEM_toAList,domain_lookup])
    >>
    strip_tac>>
    pop_assum(qspecl_then [`[]`,`ls`,`colours`] assume_tac)>>
    rfs[LET_THM]>>
    first_x_assum(qspec_then`col'` assume_tac)>>rfs[]>>
    pop_assum(qspecl_then [`spills`,`others`,`colours`] assume_tac)>>
    rfs[])
  >-
    (imp_res_tac alloc_colouring_aux_domain_1>>
    rfs[])
  >>
    imp_res_tac alloc_colouring_aux_domain_2>>
    `MEM x vertices` by
      fs[Abbr`vertices`,MEM_toAList,MEM_MAP,EXISTS_PROD,domain_lookup]>>
    fs[PARTITION_DEF]>>
    Q.ISPECL_THEN [`is_phy_var`,`vertices`,`phy_var`,`others`,`[]:num list`
      ,`[]:num list`]assume_tac PARTs_HAVE_PROP>>
    Q.ISPECL_THEN [`is_phy_var`,`vertices`,`phy_var`,`others`,`[]:num list`
      ,`[]:num list`]assume_tac PART_MEM>>
    rfs[]>>
    `∀x. MEM x colours ⇒ is_phy_var x` by
      (rw[Abbr`colours`,MEM_GENLIST,is_phy_var_def]>>
      `0<2:num` by DECIDE_TAC>>
      `(2:num)*x''=x''*2` by DECIDE_TAC>>
      metis_tac[arithmeticTheory.MOD_EQ_0])>>
    IF_CASES_TAC
    >-
      (`lookup x col = SOME x` by metis_tac[id_colour_lemma]>>
      metis_tac[alloc_colouring_aux_never_overwrites_col])
    >>
    `x ∉ domain col` by (qspec_then `phy_var` assume_tac id_colour_lemma>>
          rfs[LET_THM]>>metis_tac[])>>
    IF_CASES_TAC
    >-
      (`MEM x others` by metis_tac[]>>
      `¬is_alloc_var x` by metis_tac[convention_partitions]>>
      Q.SPECL_THEN [`G`,`colours`,`prefs`,`ls`,`col`,`[]`,`col'`,`spills`]
        assume_tac alloc_colouring_aux_domain_3>>rfs[]>>
      rw[]>>
      Cases_on`MEM x ls`>>fs[]
      >-
        (first_x_assum(qspec_then`x` mp_tac)>>fs[]>>
        metis_tac[alloc_colouring_aux_never_overwrites_spill])
      >>
        imp_res_tac alloc_colouring_aux_domain_4>>
        fs[]>>rfs[]>>
        imp_res_tac alloc_colouring_aux_domain_1>>
        Q.SPECL_THEN [`G`,`colours`,`prefs`,`others`,`col'`,`spills`
          ,`col''`,`spills'`] assume_tac alloc_colouring_aux_domain_3>>
        rfs[]>>metis_tac[])
    >>
      `is_alloc_var x ∧ MEM x others` by metis_tac[convention_partitions]>>
      Q.SPECL_THEN [`G`,`colours`,`prefs`,`ls`,`col`,`[]`,`col'`,`spills`]
        assume_tac alloc_colouring_aux_domain_3>>
      rfs[]>>
      Cases_on`MEM x ls`>>fs[]
      >-
        (first_x_assum(qspec_then`x` mp_tac)>>fs[]
        >>
        Cases_on`x ∈ domain col'`>>fs[]
        >- metis_tac[alloc_colouring_aux_never_overwrites_col]
        >>
        (*In spills so in spills'*)
        `MEM x spills'` by
          metis_tac[alloc_colouring_aux_never_overwrites_spill]>>
        (*But we always kept everything disjoint*)
        imp_res_tac alloc_colouring_aux_domain_1>>
        fs[INTER_DEF,EXTENSION]>>rw[]>>
        metis_tac[])
      >>
        imp_res_tac alloc_colouring_aux_domain_4>>
        fs[]>>rfs[]>>
        imp_res_tac alloc_colouring_aux_domain_1>>
        Q.SPECL_THEN [`G`,`colours`,`prefs`,`others`,`col'`,`spills`
          ,`col''`,`spills'`] assume_tac alloc_colouring_aux_domain_3>>
        fs[]>>metis_tac[])

val alloc_colouring_success_2 = prove(``
  let (col,spills) = alloc_colouring G k prefs ls in
  ∀x. MEM x spills ⇒ x ∈ domain G``,
  fs[alloc_colouring_def]>>rw[]>>
  imp_res_tac alloc_colouring_aux_domain_5>>fs[])

val spill_colouring_never_overwrites = prove(``
  ∀ls col col'.
  lookup x col = SOME y ∧
  spill_colouring G k prefs ls col = col'
  ⇒
  lookup x col' = SOME y``,
  Induct>>fs[spill_colouring_def,assign_colour2_def]>>rw[]>>
  Cases_on`x=h`>>fs[]>>rfs[]
  >-
    metis_tac[]
  >>
  every_case_tac>>fs[LET_THM]>>
  metis_tac[lookup_insert])

val spill_colouring_domain_subset = prove(``
  ∀ls col col'.
  domain col ⊆ domain (spill_colouring G k prefs ls col)``,
  rw[SUBSET_DEF]>>fs[domain_lookup]>>
  metis_tac[domain_lookup,spill_colouring_never_overwrites])

val SORTED_TAIL = prove(``
  SORTED R (x::xs) ⇒ SORTED R xs``,
  Cases_on`xs`>>fs[SORTED_DEF])

val SORTED_HEAD_LT = prove(``
  ∀ls.
  (col:num) < h ∧ SORTED (λx y. x≤y) (h::ls) ⇒
  ¬MEM col ls``,
  Induct>>rw[SORTED_DEF]
  >-
    DECIDE_TAC
  >>
    last_x_assum mp_tac>>discharge_hyps>>
    Cases_on`ls`>>fs[SORTED_DEF]>>DECIDE_TAC)

(*prove multiple properties in one go*)
val unbound_colours_props = prove(``
  ∀col ls col'.
    is_phy_var col ∧
    SORTED (λx y.x≤y) ls ∧
    unbound_colours col ls = col'
    ⇒
    is_phy_var col' ∧ col' ≥ col ∧
    ¬MEM col' ls``,
  Induct_on`ls`>>rw[unbound_colours_def]>>
  imp_res_tac SORTED_TAIL>>
  `is_phy_var (col+2)` by
    (qspec_then `2` assume_tac arithmeticTheory.MOD_PLUS>>fs[]>>
    pop_assum (qspecl_then [`col`,`2`] assume_tac)>>rfs[is_phy_var_def])>>
  fs[]
  >-
    DECIDE_TAC
  >-
    metis_tac[SORTED_HEAD_LT]
  >>
    (res_tac>>DECIDE_TAC))

val SORTED_TAC =
    `SORTED (λx y. x≤y) lss` by
    (unabbrev_all_tac>>match_mp_tac QSORT_SORTED>>
    fs[relationTheory.transitive_def,relationTheory.total_def]>>
    rw[]>>DECIDE_TAC);

val is_phy_var_tac =
   `is_phy_var (2*k)` by
    (fs[is_phy_var_def]>>
    `0<2:num` by DECIDE_TAC>>
    `(2:num)*k=k*2` by DECIDE_TAC>>
    metis_tac[arithmeticTheory.MOD_EQ_0]);

val option_filter_eq = prove(``
  ∀ls. option_filter ls = MAP THE (FILTER IS_SOME ls)``,
  Induct>>rw[option_filter_def]>>every_case_tac>>fs[])

val assign_colour2_satisfactory = prove(``
  undir_graph G ∧
  partial_colouring_satisfactory col G ⇒
  partial_colouring_satisfactory (assign_colour2 G k prefs h col) G``,
  rw[assign_colour2_def]>>
  fs[LET_THM]>>
  every_case_tac>>fs[]>>
  match_mp_tac (GEN_ALL partial_colouring_satisfactory_extend)>>rw[]>>
  fs[domain_lookup]>>
  TRY(
  qpat_abbrev_tac`lss = QSORT (λx:num y:num. x≤y)  B`>>
  SORTED_TAC>>
  `MEM v lss` by
    (unabbrev_all_tac>>
    fs[QSORT_MEM,option_filter_eq,MEM_MAP,MEM_FILTER,EXISTS_PROD
      ,MEM_toAList,PULL_EXISTS]>>
    TRY(Q.EXISTS_TAC`y`>>fs[])>>
    HINT_EXISTS_TAC>>fs[])>>
  is_phy_var_tac>>
  metis_tac[unbound_colours_props])>>
  qpat_assum `¬A` mp_tac >>
  qpat_abbrev_tac`lss = option_filter (MAP (λx. lookup x col) A)` >>
  qsuff_tac `MEM v lss`>-metis_tac[]>>
  unabbrev_all_tac>>
  fs[option_filter_eq,MEM_MAP,MEM_FILTER,EXISTS_PROD
    ,PULL_EXISTS,MEM_toAList]>>
  HINT_EXISTS_TAC>>fs[])

val assign_colour2_conventional = prove(``
  v ∈ domain G ∧
  v ∉ domain col ∧
  assign_colour2 G k prefs v col  = col'
  ⇒
  ∃y. lookup v col' = SOME y ∧ y≥2*k ∧ is_phy_var y``,
  rw[assign_colour2_def]>>
  fs[LET_THM,domain_lookup]>>
  every_case_tac>>fs[]>>
  is_phy_var_tac>>
  qpat_abbrev_tac`lss = QSORT (λx:num y:num. x≤y)  B`>>
  SORTED_TAC>>
  metis_tac[unbound_colours_props])

(*Coloring produced after each spill_colouring step is
  partial_colouring_satisfactory*)
val spill_colouring_satisfactory = prove(``
  ∀G k prefs ls col.
  undir_graph G ∧
  partial_colouring_satisfactory col G
  ⇒
  let col' = spill_colouring G k prefs ls col in
    partial_colouring_satisfactory col' G``,
  Induct_on`ls`>>fs[spill_colouring_def,LET_THM]>>rw[]>>
  every_case_tac>>fs[]>>
  metis_tac[assign_colour2_satisfactory])

(*Domain is extended*)
val spill_colouring_domain_1 = prove(``
  ∀G k prefs ls col.
  let col' = spill_colouring G k prefs ls col in
  ∀x. MEM x ls ∧ x ∈ domain G ⇒
      x ∈ domain col'``,
  Induct_on`ls`>>fs[spill_colouring_def,LET_THM]>>rw[]
  >-
    (fs[assign_colour2_def,domain_lookup,LET_THM]>>
    every_case_tac>>fs[]
    >>
    TRY(qpat_abbrev_tac `col' = insert h A col`>>
    qsuff_tac `∃y. lookup h col' = SOME y ∧ is_phy_var y`
    >-
      metis_tac[spill_colouring_never_overwrites]
    >>
      unabbrev_all_tac>>fs[lookup_insert]>>
      is_phy_var_tac>>
      qpat_abbrev_tac `lss = QSORT (λx:num y. x≤y) A`>>
      SORTED_TAC>>
      imp_res_tac unbound_colours_props>>
      metis_tac[])
    >>
    metis_tac[spill_colouring_never_overwrites])
  >>
    metis_tac[])

(*Coloring is extended on the list according to conventions*)
val spill_colouring_domain_2 = prove(``
  ∀G k prefs ls col.
  let col' = spill_colouring G k prefs ls col in
  ∀x. MEM x ls ∧ x ∈ domain G ∧ x ∉ domain col ⇒
      ∃y. lookup x col' = SOME y ∧ y ≥ 2*k ∧ is_phy_var y``,
  Induct_on`ls`>>fs[spill_colouring_def,LET_THM]>>rw[]
  >-
    (imp_res_tac assign_colour2_conventional>>fs[]>>
    metis_tac[spill_colouring_never_overwrites])
  >>
    Cases_on`x=h`>>fs[]
    >-
      (imp_res_tac assign_colour2_conventional>>fs[]>>
      metis_tac[spill_colouring_never_overwrites])
    >>
      fs[assign_colour2_def]>>every_case_tac>>
      fs[LET_THM]>>
      metis_tac[])

val assign_colour2_reverse = prove(``
  ∀G:sp_graph k prefs h col col'.
  assign_colour2 G k prefs h col = col'
  ⇒
  ∀x. x ≠ h ⇒
  (x ∈ domain col' ⇒ x ∈ domain col)``,
  rw[assign_colour2_def]>>every_case_tac>>fs[LET_THM]>>
  metis_tac[])

val spill_colouring_domain_3 = prove(``
  ∀G k prefs ls col.
  let col' = spill_colouring G k prefs ls col in
  ∀x. ¬MEM x ls ⇒
  (x ∈ domain col' ⇒ x ∈ domain col)``,
  Induct_on`ls`>>rw[spill_colouring_def,LET_THM]>>
  Cases_on`assign_colour2 G k prefs h col`>>fs[]>>
  metis_tac[assign_colour2_reverse])

val is_subgraph_edges_def = Define`
  is_subgraph_edges G H ⇔
    domain G = domain H  ∧  (*We never change the vertex set*)
   (∀x y. lookup_g x y G ⇒ lookup_g x y H)`

val partial_colouring_satisfactory_subgraph_edges = prove(``
  ∀G H col.
  (*Every edge in G is in H*)
  undir_graph G ∧
  is_subgraph_edges G H ∧
  (partial_colouring_satisfactory col H) ⇒
  partial_colouring_satisfactory col G``,
  fs[partial_colouring_satisfactory_def,lookup_g_def,is_subgraph_edges_def]>>
  rw[]>>
  `v ∈ domain G` by fs[]>>
  fs[domain_lookup,undir_graph_def]>>
  last_x_assum(qspec_then`v` assume_tac)>>rfs[]>>
  first_x_assum(qspec_then`v'` assume_tac)>>rfs[]>>
  last_assum(qspec_then`v` assume_tac)>>
  pop_assum(qspec_then`v'` assume_tac)>>
  last_x_assum(qspec_then`v'` assume_tac)>>
  pop_assum(qspec_then`v` assume_tac)>>
  rfs[]>>
  every_case_tac>>fs[]>>
  first_x_assum(qspec_then`v` assume_tac)>>fs[LET_THM]>>
  rfs[]>>
  pop_assum(qspec_then`v'` assume_tac)>>
  rfs[])

val undir_g_preserve = prove(``
  undir_graph G ∧
  x ≠ y ⇒
  undir_graph (undir_g_insert x y G)``,
  fs[undir_graph_def,undir_g_insert_def,dir_g_insert_def]>>rw[]>>
  fs[lookup_insert]>>
  IF_CASES_TAC >-
    (rfs[]>>Cases_on`lookup x G`>>fs[Abbr`tree'`,Abbr`tree`]>>
    first_x_assum(qspec_then`x`assume_tac)>>rfs[]>>rw[]>>
    Cases_on`lookup y G`>>fs[])>>
  IF_CASES_TAC >-
    (rfs[]>>Cases_on`lookup y G`>>fs[Abbr`tree'`,Abbr`tree`]>>
    first_x_assum(qspec_then`y`assume_tac)>>rfs[]>>rw[]>>
    Cases_on`lookup x G`>>fs[])>>
  rfs[]>>full_case_tac>>
  first_x_assum(qspec_then`x'`assume_tac)>>rfs[]>>
  rw[]>>fs[]
  >-
    (first_x_assum(qspec_then`x` assume_tac)>>rfs[]>>
    fs[Abbr`tree'`])
  >>
    (first_x_assum(qspec_then`y` assume_tac)>>rfs[]>>
    fs[Abbr`tree`]))

val undir_g_insert_domain = prove(``
  domain (undir_g_insert x y G) =
  {x;y} ∪ domain G``,
  rw[undir_g_insert_def,dir_g_insert_def]>>
  fs[domain_insert,EXTENSION]>>
  metis_tac[])

val list_g_insert_domain = prove(``
  ∀ls.
  domain(list_g_insert q ls G) =
  domain G ∪ set ls ∪ {q}``,
  Induct>>fs[list_g_insert_def]>>rw[]>>
  fs[EXTENSION,undir_g_insert_domain]>>
  every_case_tac>>fs[domain_insert,domain_lookup,lookup_insert]>>
  metis_tac[])

val finish_tac =
  last_x_assum(qspec_then`v` assume_tac)>>rfs[]>>
  first_x_assum(qspec_then`v'` assume_tac)>>rfs[domain_lookup]>>
  last_x_assum(qspec_then `v'` assume_tac)>>rfs[]>>
  pop_assum(qspec_then`v` assume_tac)>>rfs[];

val partial_colouring_satisfactory_extend_2 = prove(``
  undir_graph G ∧
  partial_colouring_satisfactory col G ∧
  (x ∉ domain col ∨ y ∉ domain col ∧
  x ∈ domain G ∧ y ∈ domain G) ⇒
  partial_colouring_satisfactory col (undir_g_insert x y G)``,
  fs[undir_g_insert_def,dir_g_insert_def
    ,partial_colouring_satisfactory_def]>>rw[]>>
  fs[domain_lookup,LET_THM]>>
  rfs[lookup_insert]
  >>
    TRY(fs[SUBSET_DEF]>>NO_TAC)
  >>
  Cases_on`v=x`>>
  Cases_on`x=y`>>
  fs[undir_graph_def]>>
  unabbrev_all_tac>>
  TRY(finish_tac>>NO_TAC)>>
  TRY(Cases_on`v=y`>>
  Cases_on`lookup y G`>>fs[]>>
  TRY(qpat_assum`A=v''` (SUBST_ALL_TAC o SYM)>>
  fs[lookup_insert]>>
  Cases_on`v'=x`>>fs[lookup_def])>>finish_tac)>>
  Cases_on`lookup x G`>>
  qpat_assum`A=v''` (SUBST_ALL_TAC o SYM)>>
  fs[lookup_insert]>>
  Cases_on`v'=y`>>fs[lookup_def]>>
  finish_tac)

val list_g_insert_undir = prove(``
  ∀ls G col.
  undir_graph G ∧
  ¬MEM q ls ⇒
  let G' = list_g_insert q ls G in
  undir_graph G'``,
  Induct>>rw[list_g_insert_def]>>
  fs[Abbr`G'`]
  >-
    (every_case_tac>>fs[undir_graph_def,lookup_insert]>>
    rw[]>>fs[]>>full_case_tac>>
    last_x_assum(qspec_then`x` assume_tac)>>fs[domain_lookup]>>rfs[]>>
    rw[]>>
    first_x_assum(qspec_then`q` assume_tac)>>
    rfs[])
  >>
    metis_tac[undir_g_preserve])

val list_g_insert_lemma = prove(``
  ∀ls G col.
  undir_graph G ∧
  ¬ MEM q ls ∧
  q ∈ domain G ∧
  (∀x. MEM x ls ⇒ x ∈ domain G ∧ x ∉ domain col) ∧
  partial_colouring_satisfactory col G
  ⇒
  let G' = list_g_insert q ls G in
  is_subgraph_edges G G' ∧
  undir_graph G' ∧
  partial_colouring_satisfactory col G'``,
  Induct
  >-
    (rw[list_g_insert_def,is_subgraph_edges_def]>>
    every_case_tac>>unabbrev_all_tac>>
    fs[domain_insert,SUBSET_DEF,lookup_g_def,lookup_insert,undir_graph_def
      ,partial_colouring_satisfactory_def,domain_empty]>>
    rw[]>>fs[]>- (fs[EXTENSION]>>metis_tac[]) 
    >-
    (full_case_tac>>
    last_x_assum(qspec_then`x` assume_tac)>>fs[domain_lookup]>>rfs[])
    >>
    unabbrev_all_tac>>fs[domain_empty])
  >>
  rw[list_g_insert_def,is_subgraph_edges_def]>>
  fs[]>>
  first_x_assum(qspecl_then[`G`,`col`] mp_tac)>>discharge_hyps>>
  fs[LET_THM,Abbr`G'`]>>rw[]
  >-
    (fs[is_subgraph_edges_def,undir_g_insert_def]>>
    fs[EXTENSION,domain_lookup]>>rw[]>>
    fs[dir_g_insert_def,LET_THM]>>every_case_tac>>
    fs[lookup_insert]>>
    rpt(IF_CASES_TAC>>fs[]))
  >-
    (fs[undir_g_insert_def]>>
    metis_tac[lookup_dir_g_insert_correct,list_g_insert_correct])
  >-
    metis_tac[undir_g_preserve]
  >>
    match_mp_tac partial_colouring_satisfactory_extend_2>>
    rfs[list_g_insert_domain])

val is_subgraph_edges_trans = prove(``
  is_subgraph_edges A B ∧
  is_subgraph_edges B C ⇒
  is_subgraph_edges A C``,
  fs[is_subgraph_edges_def]>>rw[SUBSET_DEF])

val full_coalesce_aux_extends = prove(``
  ∀(G:sp_graph) (ls:(num,num#num) alist) spills col.
  partial_colouring_satisfactory col G ∧
  (∀x. MEM x spills ⇒ x ∈ domain G ∧  x ∉ domain col) ∧   
  undir_graph G ⇒
  let (G',ls') = full_coalesce_aux G spills ls in
  is_subgraph_edges G G' ∧
  undir_graph G' ∧
  partial_colouring_satisfactory col G'``,
  Induct_on`ls`>-fs[full_coalesce_aux_def,LET_THM,is_subgraph_edges_def]>>
  ntac 4 strip_tac>>
  PairCases_on`h`>>
  fs[full_coalesce_aux_def,LET_THM]>>
  IF_CASES_TAC>-
    (fs[]>>metis_tac[])>>
  fs[]>>every_case_tac>>fs[]>>
  qpat_abbrev_tac `G'=list_g_insert h1 A G`>>
  first_x_assum(qspecl_then[`G'`,`spills`,`col`] mp_tac)>>
  rfs[]>>
  rw[Abbr`G'`]>>
  qpat_abbrev_tac`lss = FILTER P (MAP FST (toAList A))`>>
  Q.ISPECL_THEN [`h1`,`lss`,`G`,`col`] mp_tac (GEN_ALL list_g_insert_lemma)>>
  rfs[]>>
  discharge_hyps_keep>-
    (
    rw[]
    >-
      (CCONTR_TAC>>
      fs[MEM_FILTER,Abbr`lss`,MEM_toAList,FORALL_PROD,MEM_MAP,EXISTS_PROD]>>
      rfs[undir_graph_def,lookup_g_def]>>
      Cases_on`lookup h1 G`>>fs[]>>
      first_x_assum(qspec_then`h2` assume_tac)>>rfs[]>>
      `h2 ∉ domain x'` by 
        fs[domain_lookup]>>
      first_x_assum(qspec_then`h1` mp_tac)>>fs[domain_lookup])
    >-
      metis_tac[domain_lookup,optionTheory.option_CLAUSES]
    >>
      fs[Abbr`lss`,MEM_FILTER]>>metis_tac[])
  >>
  fs[LET_THM,UNCURRY]>>strip_tac>>
  qpat_assum `A ⇒ B` mp_tac>>
  discharge_hyps>-
    (`h1 ∈ domain G` by fs[FORALL_PROD]>>
    fs[EXTENSION,list_g_insert_domain])>>
  metis_tac[is_subgraph_edges_trans])

val full_coalesce_lemma = prove(``
  undir_graph G ∧
  partial_colouring_satisfactory col G ∧
  (∀x. MEM x ls ⇒ x ∉ domain col ∧ x ∈ domain G) ∧
  full_coalesce G k moves ls = (G',spills,coalesce_map)
  ⇒
  is_subgraph_edges G G' ∧
  undir_graph G' ∧
  partial_colouring_satisfactory col G'``,
  fs[full_coalesce_def,LET_THM]>>
  qpat_abbrev_tac `lss = QSORT g (FILTER f moves)`>>
  Cases_on`full_coalesce_aux G ls lss`>>
  strip_tac>>fs[]>>
  imp_res_tac full_coalesce_aux_extends>>
  ntac 2 (pop_assum kall_tac)>>
  pop_assum (Q.ISPEC_THEN `ls` mp_tac)>>discharge_hyps>>fs[]>>
  strip_tac>>
  pop_assum (Q.ISPEC_THEN `lss` mp_tac)>>
  fs[FORALL_PROD,MEM_FILTER,Abbr`lss`,LET_THM,QSORT_MEM])

fun fsm ls = fs (ls@[BIND_DEF,UNIT_DEF,IGNORE_BIND_DEF,FOREACH_def]);

val foreach_graph = prove(``
  ∀ls s.
    ∃s'.
    FOREACH (ls,dec_one) s = ((),s') ∧
    s'.graph = s.graph ∧
    s'.clock = s.clock``,
    Induct>>rw[]>>fsm[dec_one_def,get_deg_def,set_deg_def]>>
    every_case_tac>>fsm[]>>
    first_x_assum(qspec_then`s with degs := insert h (x-1) s.degs` assume_tac)>>
    rw[]>>metis_tac[])

val foreach_graph2 = prove(``
  ∀ls s.
    ∃s'.
    FOREACH (ls,revive_moves) s = ((),s') ∧
    s'.graph = s.graph ∧
    s'.clock = s.clock``,
    Induct>>rw[]>>
    fsm[revive_moves_def,get_graph_def,LET_THM,get_unavail_moves_def,
        set_unavail_moves_def,add_avail_moves_def,add_avail_moves_pri_def]>>
    every_case_tac>>fsm[]>>
    qpat_abbrev_tac`lsrs = PARTITION P s.unavail_moves`>>
    Cases_on`lsrs`>>rw[]>>
    Cases_on`split_priority q`>>rw[]>>
    qpat_abbrev_tac`sfin = s with <|avail_moves_pri:=A;avail_moves:=B;unavail_moves:=C|>`>>
    first_x_assum(qspec_then`sfin` assume_tac)>>
    rw[]>>
    unabbrev_all_tac>>fs[])

val rest_tac =
  Q.ISPECL_THEN [`MAP FST (toAList x)`,`sopt`] assume_tac foreach_graph>>
  fsm[]>>
  qpat_assum `A = ((),s'')` SUBST_ALL_TAC>>
  fsm[]>>
  TRY(qpat_abbrev_tac`lsrs = PARTITION P s.spill_worklist`)>>
  TRY(qpat_abbrev_tac`lsrs = PARTITION P s''.spill_worklist`)>>
  TRY(qpat_abbrev_tac`lsrs = PARTITION P r`)>>
  Cases_on`lsrs`>>fsm[]>>
  TRY(qpat_abbrev_tac`lsrs = PARTITION P q`)>>
  TRY(qpat_abbrev_tac`lsrs = PARTITION P q'`)>>
  Cases_on`lsrs`>>fsm[set_spill_worklist_def,add_freeze_worklist_def,add_simp_worklist_def]>>
  TRY(Q.ISPECL_THEN [`q`,`sopt`] assume_tac foreach_graph2)>>
  TRY(Q.ISPECL_THEN [`q`,`s''`] assume_tac foreach_graph2)>>
  TRY(Q.ISPECL_THEN [`q'`,`sopt`] assume_tac foreach_graph2)>>
  TRY(Q.ISPECL_THEN [`q'`,`s''`] assume_tac foreach_graph2)>>
  fsm[]>>
  qpat_assum `A = ((),s''')` SUBST_ALL_TAC>>
  rw[Abbr`sopt`]>>fs[ra_state_nchotomy]

(*Simplify neverchanges the graph*)
val simplify_graph = prove(``
  ∀s G s' opt.
    simplify s = (opt,s') ⇒
    s'.graph = s.graph ∧
    s'.clock = s.clock``,
  rw[]>>
  fsm[simplify_def,get_simp_worklist_def]>>
  Cases_on`s.simp_worklist`>>fsm[set_simp_worklist_def]>>
  rw[]>>every_case_tac>>
  fsm[dec_deg_def,get_graph_def]>>rw[]>>
  every_case_tac>>
  fsm[unspill_def,get_spill_worklist_def,get_degs_def,get_colours_def,get_move_rel_def,LET_THM]>>
  pop_assum mp_tac>>
  qpat_abbrev_tac`sopt = s with simp_worklist := A`>>
  rest_tac)

val freeze_graph = prove(``
∀s G s' opt.
    freeze s = (opt,s') ⇒
    s'.graph = s.graph ∧
    s'.clock = s.clock``,
  rw[]>>
  fsm[freeze_def,get_coalesced_def,get_freeze_worklist_def,freeze_node_def,get_unavail_moves_def,get_graph_def,get_degs_def,set_move_rel_def,set_unavail_moves_def,LET_THM]>>
  pop_assum mp_tac>>
  qpat_abbrev_tac`ls = PARTITION P (FILTER Q s.freeze_worklist)`>>
  Cases_on`ls`>>fsm[]>>
  rw[]>>every_case_tac>>
  fsm[dec_deg_def,get_graph_def]>>rw[]>>
  every_case_tac>>
  fsm[unspill_def,get_spill_worklist_def,get_degs_def,get_colours_def,get_move_rel_def,LET_THM,add_simp_worklist_def,set_freeze_worklist_def]>>
  every_case_tac>>fs[]>>
  pop_assum mp_tac>>
  TRY(qpat_abbrev_tac`sopt = s with <|simp_worklist:=A;freeze_worklist:=B;move_related:=C;unavail_moves:=D|>`)>>
  TRY(qpat_abbrev_tac`sopt = s with <|freeze_worklist:=A;move_related:=B;unavail_moves:=C|>`)>>
  rest_tac)

val spill_graph = prove(``
∀s G s' opt.
    spill s = (opt,s') ⇒
    s'.graph = s.graph ∧
    s'.clock = s.clock``,
  rw[]>>
  fsm[spill_def,get_coalesced_def,get_spill_worklist_def]>>
  Cases_on`s.spill_worklist`>>fsm[set_spill_worklist_def]>>
  rw[]>>every_case_tac>>
  fsm[dec_deg_def,get_graph_def]>>rw[]>>
  every_case_tac>>
  fsm[unspill_def,get_spill_worklist_def,get_degs_def,get_colours_def,get_move_rel_def,LET_THM]>>
  ntac 2 (pop_assum mp_tac)>>
  qpat_abbrev_tac`A = max_non_coalesced B C D E G`>>
  Cases_on`A`>>fs[]>>
  TRY(full_case_tac)>>fs[]>>
  qpat_abbrev_tac`sopt = s with spill_worklist :=A`>>
  rest_tac)

val rest_tac2 =
    first_x_assum(qspec_then`sopt`mp_tac)>>
    unabbrev_all_tac>>fs[]>>
    discharge_hyps>-
    (rw[]>-
      (match_mp_tac undir_g_preserve>>rfs[])
    >>
    fs[undir_g_insert_domain])>>
    rw[]>>HINT_EXISTS_TAC >>rfs[]>>
    fs[undir_g_insert_domain]>>
    fs[undir_g_insert_def]>>
    rw[]>>fs[EXTENSION]>>
    metis_tac[lookup_dir_g_insert_correct]

val foreach_graph_extend = prove(``
  ∀ls s.
  undir_graph s.graph ∧
  x ∈ domain s.graph ∧
  (∀y. MEM y ls ⇒ x ≠ y ∧ y ∈ domain s.graph) ⇒
  ∃s'.
  FOREACH (ls,
          (λv.
            if lookup v x_edges = NONE then
              do
                inc_one x;
                force_add x v
              od
            else
              dec_one v)) s = ((),s') ∧
   is_subgraph_edges s.graph s'.graph ∧
   undir_graph s'.graph``,
  Induct>>rw[]>>fsm[is_subgraph_edges_def]>>
  IF_CASES_TAC>>fsm[force_add_def,inc_one_def,get_deg_def]>>
  every_case_tac>>
  fsm[set_deg_def,dec_one_def,get_deg_def]>>every_case_tac>>
  fsm[]>>rw[]
  >-
    (qpat_abbrev_tac`sopt = s with graph:=undir_g_insert x h s.graph`>>
    rest_tac2)
  >-
    (qpat_abbrev_tac`sopt = s with <|graph:=A;degs:=B|>`>>
    rest_tac2)
  >>
    (qpat_abbrev_tac`sopt = s with degs:=insert h (x'-1) s.degs`>>
    first_x_assum(qspec_then`sopt`mp_tac)>>
    unabbrev_all_tac>>fs[]))

val foreach_graph_extend_2 = prove(``
  ∀ls s s'.
  FOREACH (ls,
          (λv.
           if lookup v x_edges = NONE then
              do
                inc_one x;
                force_add x v
              od
            else
              dec_one v)) s = ((),s') ⇒
   s'.clock = s.clock``,
  Induct>>rw[]>>fsm[is_subgraph_edges_def]>>
  fsm[force_add_def,inc_one_def,get_deg_def]>>
  every_case_tac>>fsm[set_deg_def,dec_one_def,get_deg_def]>>
  every_case_tac>>fs[]>>
  res_tac>>fs[])

val split_avail_filter = prove(``
  ∀ls acc B C.
  split_avail (is_valid_move G A) Q ls acc = (SOME (p,x,y),B,C)
  ⇒
  ¬ lookup_g x y G``,
  Induct>>
  rw[split_avail_def,LET_THM]
  >-
  fs[is_valid_move_def,LET_THM]
  >>
  metis_tac[])

val unspill_lem = GEN_ALL (prove(``
  unspill s = (q,r) ⇒
  r.graph = s.graph ∧
  r.clock = s.clock``,
  fsm[unspill_def,get_spill_worklist_def,get_degs_def,get_colours_def,get_move_rel_def,LET_THM]>>
  qpat_abbrev_tac`sopt = s`>>
  rest_tac))

val do_coalesce_lem = prove(``
  undir_graph s.graph ∧
  is_subgraph_edges G s.graph ∧
  ¬lookup_g q r s.graph ∧
  do_coalesce (q,r) s = ((),s') ⇒
  undir_graph s'.graph ∧
  is_subgraph_edges G s'.graph``,
  fsm[do_coalesce_def,add_coalesce_def,get_edges_def,get_degs_def
     ,get_colours_def,LET_THM]>>
  every_case_tac>>fs[]>>
  TRY(rw[]>>fs[]>>NO_TAC)>>
  fsm[LET_THM]>>
  qpat_abbrev_tac `ls = FILTER P (MAP FST (toAList x'))`>>
  qpat_abbrev_tac `sopt = (s with coalesced:= A)`>>
  strip_tac>>
  Q.ISPECL_THEN [`x`,`q`,`ls`,`sopt`] mp_tac (GEN_ALL foreach_graph_extend)>>
  discharge_hyps>-
   (`∀x. MEM x (MAP FST (toAList x')) ⇒ x ∈ domain sopt.graph` by
     (rw[]>>fs[MEM_MAP]>>Cases_on`y`>>fs[MEM_toAList,Abbr`sopt`]>>
     fs[undir_graph_def]>>
     first_x_assum(qspec_then`r` assume_tac)>>rfs[domain_lookup]>>
     first_x_assum(qspec_then`q'` assume_tac)>>rfs[])>>
   unabbrev_all_tac>>fs[MEM_FILTER]>>
   CONJ_ASM1_TAC>- fs[domain_lookup]>>
   DISJ2_TAC>>
   fs[lookup_g_def,undir_graph_def]>>rw[]>>
   first_x_assum(qspec_then`q` assume_tac)>>rfs[]>>
   CCONTR_TAC>>fs[]>>
   `lookup q x' = SOME ()` by
     (fs[MEM_MAP]>>Cases_on`y`>>fs[MEM_toAList])>>
   first_x_assum(qspec_then`r` assume_tac)>>rfs[domain_lookup]>>
   first_x_assum(qspec_then`q` assume_tac)>>rfs[])
  >>
  rw[]>>fsm[Abbr`sopt`]>>
  metis_tac[is_subgraph_edges_trans])

val do_coalesce_clock_lem=prove(``
  do_coalesce (q,r) s = ((),s') ⇒
  s'.clock = s.clock``,
  fsm[do_coalesce_def,add_coalesce_def,get_edges_def,get_degs_def
     ,get_colours_def,LET_THM]>>
  every_case_tac>>fs[]>>
  TRY(rw[]>>fs[]>>NO_TAC)>>
  fsm[LET_THM]>>
  qpat_abbrev_tac `ls = FILTER P (MAP FST (toAList x'))`>>
  qpat_abbrev_tac `sopt = (s with coalesced:= A)`>>
  strip_tac>>
  Q.ISPECL_THEN [`x`,`q`,`ls`,`sopt`,`s'`] assume_tac (GEN_ALL foreach_graph_extend_2)>>
  fsm[]>>rfs[Abbr`sopt`])

val respill_lem = prove(``
  ∀s v r. respill v s = ((),r) ⇒
  r.graph = s.graph ∧ r.clock = s.clock``,
  rw[respill_def]>>
  fsm[get_colours_def,get_deg_def,get_freeze_worklist_def
     ,add_spill_worklist_def,set_freeze_worklist_def]>>
  every_case_tac>>fs[]>>
  Cases_on`MEM v s.freeze_worklist`>>fs[]>>
  qpat_assum`A=r` (SUBST_ALL_TAC o SYM)>>
  fs[])

val coalesce_graph = prove(``
∀s G s' opt.
    undir_graph s.graph ∧
    is_subgraph_edges G s.graph ∧
    coalesce s = (opt,s') ⇒
    undir_graph s'.graph ∧
    is_subgraph_edges G s'.graph``,
  ntac 5 strip_tac>>
  fsm[coalesce_def,get_avail_moves_pri_def,get_avail_moves_def,get_graph_def,get_colours_def,get_degs_def,get_move_rel_def]>>
  every_case_tac>>
  fsm[set_avail_moves_pri_def,set_avail_moves_def,add_unavail_moves_def]>>
  every_case_tac>>fs[]>>
  every_case_tac>>fs[]>>
  every_case_tac>>fs[]>-
    (rw[]>>fs[])>>
  pop_assum mp_tac>>
  TRY(qpat_abbrev_tac`s' = s with <|avail_moves_pri:=B;avail_moves:=C;unavail_moves:=D|>`>>Cases_on`do_coalesce (q''',r''') s''`)>>
  TRY(qpat_abbrev_tac`s' = s with <|avail_moves_pri:=B;unavail_moves:=D|>`>>
  Cases_on`do_coalesce (q'',r'') s''`)>>
  fsm[get_unavail_moves_def,LET_THM,set_unavail_moves_def]>>
  qpat_abbrev_tac`sopt = r with <|avail_moves_pri:=B;avail_moves:=C;unavail_moves:=D|>`>>
  Cases_on`unspill sopt`>>fs[]>>
  TRY(Cases_on`respill q''' r''''`)>>
  TRY(Cases_on`respill q'' r'''`)>>
  strip_tac>>fs[]>>
  `s''.graph = s.graph ∧ s''.clock = s.clock` by fs[Abbr`s''`]>>
  `undir_graph s''.graph ∧ is_subgraph_edges G s''.graph` by fs[]>>
  imp_res_tac split_avail_filter>>
  qpat_assum`A = s.graph` (SUBST_ALL_TAC o SYM)>>
  imp_res_tac do_coalesce_lem>>
  imp_res_tac respill_lem>>
  imp_res_tac unspill_lem>>
  unabbrev_all_tac>>fs[]>>
  rfs[])

val coalesce_graph_2 = prove(``
∀s G s' opt.
    coalesce s = (opt,s') ⇒
    s'.clock = s.clock``,
  ntac 5 strip_tac>>
  fsm[coalesce_def,get_avail_moves_pri_def,get_avail_moves_def,get_graph_def,get_colours_def,get_degs_def,get_move_rel_def]>>
  every_case_tac>>
  fsm[set_avail_moves_pri_def,set_avail_moves_def,add_unavail_moves_def]>>
  every_case_tac>>fs[]>>
  every_case_tac>>fs[]>>
  every_case_tac>>fs[]>-
    (rw[]>>fs[])>>
  pop_assum mp_tac>>
  TRY(qpat_abbrev_tac`s' = s with <|avail_moves_pri:=B;avail_moves:=C;unavail_moves:=D|>`>>Cases_on`do_coalesce (q''',r''') s''`)>>
  TRY(qpat_abbrev_tac`s' = s with <|avail_moves_pri:=B;unavail_moves:=D|>`>>
  Cases_on`do_coalesce (q'',r'') s''`)>>
  fsm[get_unavail_moves_def,LET_THM,set_unavail_moves_def]>>
  qpat_abbrev_tac`sopt = r with <|avail_moves_pri:=B;avail_moves:=C;unavail_moves:=D|>`>>
  Cases_on`unspill sopt`>>fs[]>>
  TRY(Cases_on`respill q''' r''''`)>>
  TRY(Cases_on`respill q'' r'''`)>>
  strip_tac>>fs[]>>
  imp_res_tac do_coalesce_clock_lem>>
  imp_res_tac respill_lem>>
  imp_res_tac unspill_lem>>
  unabbrev_all_tac>>fs[])

val do_step_graph_lemma = store_thm("do_step_graph_lemma",``
  ∀s G s'.
    undir_graph s.graph ∧
    is_subgraph_edges G s.graph ∧
    s.clock ≠ 0 ∧
    do_step s = ((),s') ⇒
    undir_graph s'.graph ∧
    is_subgraph_edges G s'.graph``,
    rw[]>>
    fsm[do_step_def,dec_clock_def]>>
    qabbrev_tac`sopt = (s with clock:=s.clock-1)`>>
    `sopt.graph = s.graph` by fs[Abbr`sopt`]>>
    `sopt.clock < s.clock` by (fs[Abbr`sopt`]>>DECIDE_TAC)>>
    Cases_on`simplify sopt`>>Cases_on`q`>>fs[]>>
    Cases_on`coalesce r`>>Cases_on`q`>>fs[]>>
    Cases_on`freeze r'`>>Cases_on`q`>>fs[]>>
    Cases_on`spill r''`>>Cases_on`q`>>fs[]>>
    fsm[push_stack_def]>>
    TRY(qpat_assum`A=s'` (SUBST_ALL_TAC o SYM))>>fs[]>>
    metis_tac[spill_graph,coalesce_graph,freeze_graph,simplify_graph,coalesce_graph_2])

val do_step_clock_lemma = store_thm("do_step_clock_lemma",``
  ∀s G s'.
    s.clock ≠ 0 ∧
    do_step s = ((),s') ⇒
    s'.clock < s.clock``,
    rw[]>>
    fsm[do_step_def,dec_clock_def]>>
    qabbrev_tac`sopt = (s with clock:=s.clock-1)`>>
    `sopt.graph = s.graph` by fs[Abbr`sopt`]>>
    `sopt.clock < s.clock` by (fs[Abbr`sopt`]>>DECIDE_TAC)>>
    Cases_on`simplify sopt`>>Cases_on`q`>>fs[]>>
    Cases_on`coalesce r`>>Cases_on`q`>>fs[]>>
    Cases_on`freeze r'`>>Cases_on`q`>>fs[]>>
    Cases_on`spill r''`>>Cases_on`q`>>fs[]>>
    fsm[push_stack_def]>>
    TRY(qpat_assum`A=s'` (SUBST_ALL_TAC o SYM))>>fs[]>>
    metis_tac[spill_graph,coalesce_graph,freeze_graph,simplify_graph,coalesce_graph_2])

val rpt_do_step_graph_lemma = store_thm("rpt_do_step_graph_lemma",``
  ∀s.
    undir_graph s.graph
    ⇒
    let ((),s') = rpt_do_step s in
    undir_graph s'.graph ∧
    is_subgraph_edges s.graph s'.graph``,
  fs[rpt_do_step_def]>>
  completeInduct_on`s.clock`>>
  rw[]>>
  pop_assum mp_tac>>
  Q.ISPECL_THEN [`has_work`,`do_step`] assume_tac MWHILE_DEF>>
  pop_assum (SUBST1_TAC)>>
  fsm[has_work_def,get_clock_def]>>
  pop_assum mp_tac>>IF_CASES_TAC>>
  rw[]>>fsm[]>>
  TRY(fs[is_subgraph_edges_def]>>NO_TAC)>>
  Cases_on`do_step s`>>
  first_x_assum(qspec_then`r.clock` mp_tac)>>
  Q.ISPECL_THEN [`s`,`s.graph`,`r`] mp_tac do_step_graph_lemma>>
  (discharge_hyps>-
    (rfs[is_subgraph_edges_def]>>
    DECIDE_TAC))>>
  Q.ISPECL_THEN[`s`,`s.graph`,`r`] mp_tac do_step_clock_lemma>>
  (discharge_hyps>-
    (fs[]>>DECIDE_TAC))>>
  rw[]>>
  pop_assum(qspec_then`r` mp_tac)>>rfs[LET_THM]>>
  metis_tac[is_subgraph_edges_trans])

val do_step2_clock_lemma = store_thm("do_step2_clock_lemma",``
  ∀s G s'.
    s.clock ≠ 0 ∧
    do_step2 s = ((),s') ⇒
    s'.clock < s.clock``,
  rw[]>>fsm[do_step2_def,dec_clock_def,full_simplify_def,get_simp_worklist_def,get_degs_def]>>full_case_tac>>
  fsm[dec_deg_def,set_simp_worklist_def,get_graph_def,push_stack_def]>>
  TRY(full_case_tac)>>fs[]>>
  TRY(pop_assum (SUBST_ALL_TAC o SYM)>>fs[]>>DECIDE_TAC)>>
  pop_assum mp_tac>>
  qpat_abbrev_tac`ls = MAP FST (toAList x)`>>
  qpat_abbrev_tac`sopt = s with <|simp_worklist:=A;clock:=B|>`>>
  Q.ISPECL_THEN [`ls`,`sopt`] assume_tac foreach_graph>>fs[LET_THM]>>
  rw[Abbr`sopt`]>>
  fsm[]>>
  DECIDE_TAC)

(*Note:Briggs clock is not pulled out since it isn't used (yet)*)
val do_briggs_step_graph_lemma = prove(``
  ∀s G s'.
    undir_graph s.graph ∧
    is_subgraph_edges G s.graph ∧
    s.clock ≠ 0 ∧
    do_briggs_step s = ((),s') ⇒
    undir_graph s'.graph ∧
    is_subgraph_edges G s'.graph ∧
    s'.clock < s.clock``,
  rw[]>>
  fsm[do_briggs_step_def,dec_clock_def]>>
  qabbrev_tac`sopt = (s with clock:=s.clock-1)`>>
  `sopt.graph = s.graph` by fs[Abbr`sopt`]>>
  `sopt.clock < s.clock` by (fs[Abbr`sopt`]>>DECIDE_TAC)>>
  Cases_on`coalesce sopt`>>Cases_on`q`>>fs[]>>
  fsm[push_stack_def]>>
  TRY(qpat_assum`A=s'` (SUBST_ALL_TAC o SYM))>>fs[]>>
  metis_tac[coalesce_graph,coalesce_graph_2])

val briggs_coalesce_lemma = prove(``
  ∀s.
    undir_graph s.graph
    ⇒
    let ((),s') = briggs_coalesce s in
    undir_graph s'.graph ∧
    is_subgraph_edges s.graph s'.graph``,
  fs[briggs_coalesce_def]>>
  completeInduct_on`s.clock`>>
  rw[]>>
  pop_assum mp_tac>>
  Q.ISPECL_THEN [`briggs_has_work`,`do_briggs_step`] assume_tac MWHILE_DEF>>
  pop_assum (SUBST1_TAC)>>
  fsm[briggs_has_work_def,get_clock_def,get_avail_moves_pri_def,get_avail_moves_def]>>
  pop_assum mp_tac>>Cases_on`s.clock>0`>>
  rw[]>>fsm[set_unavail_moves_def,set_move_rel_def]>>
  TRY(qpat_assum`A=s'` (SUBST_ALL_TAC o SYM)>>fs[is_subgraph_edges_def]>>NO_TAC)>>
  Cases_on`do_briggs_step s`>>
  first_x_assum(qspec_then`r.clock` mp_tac)>>
  Q.ISPECL_THEN [`s`,`s.graph`,`r`] mp_tac do_briggs_step_graph_lemma>>
  (discharge_hyps>-
    (rfs[is_subgraph_edges_def]>>
    DECIDE_TAC))>>
  rw[]>>
  pop_assum(qspec_then`r` mp_tac)>>rfs[LET_THM]>>
  metis_tac[is_subgraph_edges_trans])

val reg_alloc_satisfactory = store_thm ("reg_alloc_satisfactory",``
  ∀G k moves alg.
  undir_graph G ⇒
  let col = reg_alloc alg G k moves in
  (domain G ⊆ domain col ∧
  partial_colouring_satisfactory col G)``,
  rpt strip_tac>>fs[reg_alloc_def]>>BasicProvers.LET_ELIM_TAC>>
  `satisfactory_pref pref` by
    (every_case_tac>>fs[Abbr`pref`,aux_pref_satisfactory,move_pref_satisfactory,aux_move_pref_satisfactory])>>
  `undir_graph s''.graph ∧ is_subgraph_edges G s''.graph` by
    (every_case_tac>>fs[]>>
    TRY(`s'.graph = G` by
      (unabbrev_all_tac>>fs[init_ra_state_def,LET_THM,UNCURRY]>>NO_TAC))>>
    Q.ISPEC_THEN`init_ra_state G k moves'` assume_tac briggs_coalesce_lemma>>
    rfs[LET_THM,init_ra_state_def,UNCURRY]>>
    Q.ISPEC_THEN `s'` assume_tac rpt_do_step_graph_lemma>>
    rfs[LET_THM]>>metis_tac[is_subgraph_edges_trans])>>
  imp_res_tac alloc_colouring_success>>
  pop_assum kall_tac>>
  pop_assum(qspecl_then [`s''.stack`,`k`] assume_tac)>>rfs[LET_THM]>>
  `∀x. MEM x ls ⇒ x ∈ domain s''.graph` by
    (Q.ISPECL_THEN [`pref`,`s''.stack`,`k`,`s''.graph`] assume_tac
      (GEN_ALL alloc_colouring_success_2)>>
    rfs[LET_THM])>>
  `partial_colouring_satisfactory col G` by
    metis_tac[partial_colouring_satisfactory_subgraph_edges]>>
  `is_subgraph_edges s''.graph G' ∧ undir_graph G' ∧
   partial_colouring_satisfactory col G'` by
     (match_mp_tac (GEN_ALL full_coalesce_lemma)>>
     rw[]>>
     fs[INTER_DEF,EXTENSION]>>
     metis_tac[])>>
  `is_subgraph_edges G G'` by metis_tac[is_subgraph_edges_trans]
  >>
    TRY(fs[is_subgraph_edges_def]>>
    `domain col ⊆ domain col''` by
      metis_tac[spill_colouring_domain_subset,SUBSET_DEF]>>
    Q.ISPECL_THEN [`G'`,`k`,`LN:num num_map`,`ls`,`col'`] assume_tac spill_colouring_domain_1>>
    rfs[LET_THM]>>
    fs[SUBSET_DEF,EXTENSION]>>rw[]>>res_tac>>
    res_tac>>
    pop_assum mp_tac>>
    rpt (IF_CASES_TAC>-metis_tac[domain_lookup])>>
    fs[]>>NO_TAC)
  >>
    match_mp_tac partial_colouring_satisfactory_subgraph_edges>>
    Q.EXISTS_TAC`G'`>>fs[]>>
    metis_tac[spill_colouring_satisfactory])

val reg_alloc_total_satisfactory = store_thm ("reg_alloc_total_satisfactory",``
  ∀alg G k moves.
  undir_graph G ⇒
  let col = reg_alloc alg G k moves in
  colouring_satisfactory (total_colour col) G``,
  rw[]>>imp_res_tac reg_alloc_satisfactory>>
  pop_assum(qspecl_then[`moves`,`k`]assume_tac)>>rfs[LET_THM]>>
  fs[colouring_satisfactory_def,partial_colouring_satisfactory_def
      ,total_colour_def,undir_graph_def]>>
  rw[]>>
  last_x_assum(qspec_then`v` assume_tac)>>
  rfs[Abbr`edges'`,domain_lookup]>>rfs[]>>
  rw[]>>res_tac>>
  `e ∈ domain G ∧ v ∈ domain col ∧ e ∈ domain col` by
    fs[domain_lookup,SUBSET_DEF]>>
  fs[domain_lookup]>>
  first_x_assum(qspec_then`v'''` assume_tac)>>rfs[LET_THM]>>
  metis_tac[])

val reg_alloc_conventional = store_thm("reg_alloc_conventional" ,``
  ∀alg G k moves.
  undir_graph G ⇒
  let col = reg_alloc alg G k moves in
  colouring_conventional G k (total_colour col)``,
  rw[]>>imp_res_tac reg_alloc_satisfactory>>
  pop_assum(qspecl_then[`moves`,`k`,`alg`] assume_tac)>>rfs[LET_THM]>>
  rw[total_colour_def,reg_alloc_def,colouring_conventional_def]>>
  `x ∈ domain col` by
    fs[SUBSET_DEF]>>
  fs[domain_lookup]>>rfs[]>>unabbrev_all_tac>>
  fs[reg_alloc_def]>>pop_assum mp_tac>>
  BasicProvers.LET_ELIM_TAC>>
  rfs[LET_THM]>>
  `undir_graph s''.graph ∧ is_subgraph_edges G s''.graph` by
    (every_case_tac>>fs[]>>
    TRY(`s'.graph = G` by
      (unabbrev_all_tac>>fs[init_ra_state_def,LET_THM,UNCURRY]>>NO_TAC))>>
    Q.ISPEC_THEN`init_ra_state G k moves'` assume_tac briggs_coalesce_lemma>>
    rfs[LET_THM,init_ra_state_def,UNCURRY]>>
    Q.ISPEC_THEN `s'` assume_tac rpt_do_step_graph_lemma>>
    rfs[LET_THM]>>metis_tac[is_subgraph_edges_trans])>>
  imp_res_tac alloc_colouring_success>>
  pop_assum kall_tac>>
  pop_assum(qspec_then `pref` mp_tac)>>discharge_hyps
  >-
    (every_case_tac>>fs[Abbr`pref`,aux_pref_satisfactory,move_pref_satisfactory,aux_move_pref_satisfactory])>>
  fs[]>>strip_tac>>
  pop_assum(qspecl_then[`s''.stack`,`k`] assume_tac)>>rfs[LET_THM]>>
  `partial_colouring_satisfactory col G` by
    metis_tac[partial_colouring_satisfactory_subgraph_edges]>>
  `is_subgraph_edges s''.graph G' ∧ undir_graph G' ∧
   partial_colouring_satisfactory col G'` by
     (`∀x. MEM x ls ⇒ x ∈ domain s''.graph` by
       (Q.ISPECL_THEN [`pref`,`s''.stack`,`k`,`s''.graph`] assume_tac
         (GEN_ALL alloc_colouring_success_2)>>
       rfs[LET_THM])>>
     match_mp_tac (GEN_ALL full_coalesce_lemma)>>
     rw[]>>
     fs[INTER_DEF,EXTENSION]>>
     metis_tac[])>>
  `x ∈ domain G' ∧ x ∈ domain s''.graph` by
    fs[is_subgraph_edges_def,SUBSET_DEF]>>
  IF_CASES_TAC>-
    (first_x_assum(qspec_then`x`assume_tac)>>rfs[]>>
    metis_tac[spill_colouring_never_overwrites,optionTheory.option_CLAUSES])
  >>
  IF_CASES_TAC>-
    (`MEM x ls` by metis_tac[]>>
    `x ∉ domain col` by
      (fs[INTER_DEF,EXTENSION]>>metis_tac[])>>
    Cases_on`MEM x s''''.stack`>>fs[]
    >-
      (Q.ISPECL_THEN [`G'`,`k`,`coalesce_map`,`s''''.stack`,`col`] assume_tac
        spill_colouring_domain_2>> rfs[LET_THM,is_subgraph_edges_def]>>
      metis_tac[spill_colouring_never_overwrites,optionTheory.option_CLAUSES])
    >>
      Q.ISPECL_THEN [`G'`,`k`,`LN:num num_map`,`ls`,`col'`] assume_tac
        spill_colouring_domain_2>> rfs[LET_THM,is_subgraph_edges_def]>>
      metis_tac[spill_colouring_domain_3,optionTheory.option_CLAUSES])
  >>
  first_x_assum(qspec_then`x`assume_tac)>>rfs[]>>
  Cases_on`x ∈ domain col`
  >-
    metis_tac[spill_colouring_never_overwrites,optionTheory.option_CLAUSES]
  >>
  fs[]>>
  Cases_on`MEM x s''''.stack`>>fs[]
    >-
      (Q.ISPECL_THEN [`G'`,`k`,`coalesce_map`,`s''''.stack`,`col`] assume_tac
        spill_colouring_domain_2>> rfs[LET_THM,is_subgraph_edges_def]>>
      metis_tac[spill_colouring_never_overwrites,optionTheory.option_CLAUSES])
    >>
      Q.ISPECL_THEN [`G'`,`k`,`LN:num num_map`,`ls`,`col'`] assume_tac
        spill_colouring_domain_2>> rfs[LET_THM,is_subgraph_edges_def]>>
      metis_tac[spill_colouring_domain_3,optionTheory.option_CLAUSES])

(*strengthen case of the above*)
val reg_alloc_conventional_phy_var = store_thm("reg_alloc_conventional_phy_var",``
  ∀alg G k moves.
  undir_graph G ⇒
  let col = reg_alloc alg G k moves in
  ∀x. is_phy_var x ⇒ (total_colour col) x = x``,
  rw[]>>Cases_on`x ∈ domain col`
  >-
  (imp_res_tac reg_alloc_satisfactory >>
  pop_assum(qspecl_then[`moves`,`k`,`alg`] assume_tac)>>rfs[LET_THM]>>
  imp_res_tac reg_alloc_conventional>>
  pop_assum(qspecl_then[`moves`,`k`,`alg`] assume_tac)>>rfs[LET_THM]>>
  fs[colouring_conventional_def]>>
  fs[LET_THM,partial_colouring_satisfactory_def]>>
  fs[SUBSET_DEF]>>
  metis_tac[])
  >>
  (fs[total_colour_def]>>
  full_case_tac>>fs[domain_lookup]))

(*Various side theorems necessary to link up proofs:
  - clash_sets_to_sp_g captures everything appearing in the clashsets
  - clash_sets_to_sp_g produces undirected graphs
*)

val clique_g_insert_undir = prove(``
  ∀ls G.
  undir_graph G ∧
  ALL_DISTINCT ls
  ⇒
  undir_graph (clique_g_insert ls G)``,
  Induct>>fs[clique_g_insert_def]>>rw[]>>
  metis_tac[list_g_insert_undir])

val clash_sets_to_sp_g_undir = store_thm("clash_sets_to_sp_g_undir",``
∀ls.
  undir_graph (clash_sets_to_sp_g ls)``,
  Induct>-rw[clash_sets_to_sp_g_def,undir_graph_def,lookup_def]>>
  rw[clash_sets_to_sp_g_def]>>
  match_mp_tac clique_g_insert_undir>>
  unabbrev_all_tac>>
  fs[ALL_DISTINCT_MAP_FST_toAList])

val clique_g_insert_domain = prove(``
  ∀ls.
  domain (clique_g_insert ls G) =
  domain G ∪ set ls``,
  Induct>>fs[clique_g_insert_def]>>rw[]>>
  fs[list_g_insert_domain]>>
  rw[EXTENSION]>>metis_tac[])

val clash_sets_to_sp_g_domain = store_thm("clash_sets_to_sp_g_domain",``
∀ls x.
  in_clash_sets ls x ⇒ 
  x ∈ domain (clash_sets_to_sp_g ls)``,
  Induct>>fs[in_clash_sets_def,clash_sets_to_sp_g_def,LET_THM]>>rw[]>>res_tac>>
  fs[clique_g_insert_domain]>>
  fs[domain_lookup,MEM_MAP,MEM_toAList,EXISTS_PROD])
 
val _ = export_theory()
