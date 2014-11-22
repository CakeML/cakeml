open HolKernel Parse boolLib bossLib miscLib
open listTheory sptreeTheory pred_setTheory pairTheory
open rich_listTheory
open alistTheory
open BasicProvers
open word_liveTheory
open word_langTheory

val _ = new_theory "reg_alloc";

(*Defines a graph coloring algorithm*)

(*Graph representation is sptree of unit sptrees*)
val _ = type_abbrev("sp_graph",
  ``:(num_set) num_map``);

(*Lookup edge in spgraph*)
val lookup_g_def = Define`
  lookup_g x y (g:sp_graph) =
    case lookup x g of NONE => F
                     | SOME t => lookup y t = SOME ()` 

(*Insert an edge x->y in spgraph*)
val dir_g_insert_def = Define`
  dir_g_insert x y g = 
  let tree = 
    case lookup x g of
      NONE => insert y () LN 
    | SOME t => insert y () t
  in
    insert x tree g`

val undir_g_insert_def = Define`
  (undir_g_insert x y g =
    dir_g_insert x y (dir_g_insert y x g))`

val list_g_insert_def = Define`
  (list_g_insert x [] g = g) ∧ 
  (list_g_insert x (y::ys) g =
    undir_g_insert x y (list_g_insert x ys g))`

(*Every clash-set should form a clique*)
val clique_g_insert_def = Define`
  (clique_g_insert [] g = g) ∧ 
  (clique_g_insert (x::xs) g =
    list_g_insert x xs (clique_g_insert xs g))`

val clash_sets_to_sp_g_def = Define`
  (clash_sets_to_sp_g [] = LN) ∧ 
  (clash_sets_to_sp_g (x::xs) =
    (*I think nub probably makes it easier*)
    let subgraph = clash_sets_to_sp_g xs in
    let clashes = nub (MAP FST (toAList x)) in
    clique_g_insert clashes subgraph)`

(*
  Link up coloring_satisfactory to coloring_ok
  Proof idea:
  Show that clash sets always appear as cliques in the graph
  and coloring_satisfactory guarantees that cliques have all
  distinct colors
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
    (EVERY_CASE_TAC>>fs[domain_insert])
  >>
    rw[]>>fs[lookup_insert]>>
    Cases_on`x'=x`>>fs[]>>
    FULL_CASE_TAC>>
    fs[domain_insert,lookup_insert,lookup_def])

val list_g_insert_correct = prove(``
  !ls x g.
  let g' = list_g_insert x ls g in
    ∀u v.
      lookup_g u v g' = ((u = x ∧ MEM v ls) 
                      ∨ (v = x ∧ MEM u ls) 
                      ∨ lookup_g u v g)``,
  Induct>>rw[list_g_insert_def,undir_g_insert_def]>>
  unabbrev_all_tac>>fs[]>>
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

(*coloring_satisfactory for sp_graphs*)
val coloring_satisfactory_def = Define `
  (coloring_satisfactory col (G:sp_graph) =
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

val clash_sets_clique = prove(``
  !ls x. 
  MEM x ls ⇒ 
  sp_g_is_clique (nub (MAP FST (toAList x))) (clash_sets_to_sp_g ls)``,
  Induct>>fs[clash_sets_to_sp_g_def]>>rw[]>>
  unabbrev_all_tac>>
  metis_tac[clique_g_insert_is_clique
           ,clique_g_insert_preserves_clique,all_distinct_nub])

val get_spg_def = Define`
  get_spg prog live = 
    let (hd,clash_sets) = get_clash_sets prog live in
      (clash_sets_to_sp_g (hd::clash_sets))`

val coloring_satisfactory_cliques = prove(``
  ∀ls g (f:num->num).
  ALL_DISTINCT ls ∧ 
  coloring_satisfactory f g ∧ sp_g_is_clique ls g
  ⇒ 
  ALL_DISTINCT (MAP f ls)``,
  Induct>>
  fs[sp_g_is_clique_def,coloring_satisfactory_def]>>
  rw[]
  >-
    (fs[MEM_MAP]>>rw[]>>
    first_x_assum(qspecl_then [`h`,`y`] assume_tac)>>rfs[]>>
    Cases_on`MEM y ls`>>Cases_on`h=y`>>fs[]>>
    fs[lookup_g_def]>>EVERY_CASE_TAC>>fs[]>>
    imp_res_tac domain_lookup>>
    res_tac>>fs[LET_THM]>>
    Cases_on`lookup y g`>>fs[])
  >>
    first_x_assum(qspecl_then [`g`,`f`] mp_tac)>>rfs[])

val MEM_nub = prove(``
  ∀ls x. MEM x ls ⇒ MEM x (nub ls)``,
  rw[])

val coloring_satisfactory_coloring_ok_alt = prove(``
  ∀prog f live.
  let spg = get_spg prog live in
  coloring_satisfactory (f:num->num) spg
  ⇒ 
  coloring_ok_alt f prog live``,
  rpt strip_tac>>
  fs[LET_THM,coloring_ok_alt_def,coloring_satisfactory_def,get_spg_def]>>
  Cases_on`get_clash_sets prog live`>>fs[]>>
  strip_tac>>
  qabbrev_tac `ls = q::r`>>
  qsuff_tac `EVERY (λs. INJ f (domain s) UNIV) ls`
  >-
    fs[Abbr`ls`]
  >>
  rw[EVERY_MEM]>>
  imp_res_tac clash_sets_clique>>
  imp_res_tac coloring_satisfactory_cliques>>
  pop_assum(qspec_then`f`mp_tac)>>
  discharge_hyps
  >- fs[coloring_satisfactory_def,LET_THM]>>
  discharge_hyps
  >- fs[all_distinct_nub]>>
  fs[INJ_DEF,all_distinct_nub]>>rw[]>>
  fs[domain_lookup]>>
  `MEM x (MAP FST (toAList s)) ∧
   MEM y (MAP FST (toAList s))` by 
    (fs[MEM_MAP,EXISTS_PROD]>>
    metis_tac[domain_lookup,MEM_MAP,EXISTS_PROD,MEM_toAList])>>
  `ALL_DISTINCT (nub (MAP FST (toAList s)))` by 
    metis_tac[all_distinct_nub]>>
  fs[EL_ALL_DISTINCT_EL_EQ]>>
  imp_res_tac MEM_nub>>
  fs[MEM_EL]>>pop_assum (SUBST1_TAC o SYM)>>
  simp[]>>
  metis_tac[EL_MAP])

(*Conventions of wordLang*)

(*Distinguish 3 kinds of variables:
  Evens are physical registers
  4n+1 are allocatable registers
  4n+3 are stack registers*)

val is_stack_var_def = Define`
  is_stack_var (n:num) = (n MOD 4 = 3)`
val is_phy_var_def = Define`
  is_phy_var (n:num) = (n MOD 2 = 0)`
val is_alloc_var_def = Define`
  is_alloc_var (n:num) = (n MOD 4 = 1)`

val convention_partitions = prove(``
  ∀n. (is_stack_var n ⇔ (¬is_phy_var n) ∧ ¬(is_alloc_var n)) ∧
      (is_phy_var n ⇔ (¬is_stack_var n) ∧ ¬(is_alloc_var n)) ∧
      (is_alloc_var n ⇔ (¬is_phy_var n) ∧ ¬(is_stack_var n))``,
  rw[is_stack_var_def,is_phy_var_def,is_alloc_var_def,EQ_IMP_THM]>>
  cheat)

val coloring_conventional_def = Define`
  coloring_conventional (G:sp_graph) k col ⇔
  let vertices = domain G in
  ∀x. x ∈ vertices ⇒
    if is_phy_var x then col x = x 
    else 
    if is_stack_var x then is_stack_var (col x)
    else 
    (*x must be an alloc var, although that must be proved*)
    let y = col x in
      if is_phy_var y then y < 2*k
      else 
         is_stack_var y`

(*Define the coloring step:
  Takes arguments:
  G = spgraph (possibly augmented e.g. in coalescing),
  k = number of registers to use,
  prefs = num-> num list -> num (selects a color from the list)
  nsv = next spill var
  ls = heuristic order to color vertices,

  Result: a num sptree where looking up a vertex gives its coloring

  TODO: Decide if this should be monadic
*)

(*Not sure if already in HOL*)
val split_list_def = Define`
  (split_list P [] = ([],[])) ∧
  (split_list P (x::xs) = 
    let (L,R) = split_list P xs in
      if P x then (x::L,R) else (L,x::R))` 

(*
Acc version
val split_list_def = Define`
  (split_list P [] acc = acc) ∧ 
  (split_list P (x::xs) (L,R) = 
    if P x then split_list P xs (x::L,R)
    else split_list P xs (L,x::R))`
*)    

(*Deletes unavailable colors by looking up the current coloring function*)
(*k is usually small --> just use a list, eventually a bitset*)
val remove_colors_def = Define`
  (*No more available colors*)
  (remove_colors (col:num num_map) ls [] = []) ∧
  (*Some available color after checking*) 
  (remove_colors (col:num num_map) [] k = k) ∧
  (*Do the checks*)
  (remove_colors col (x::xs) k =
    let c = lookup x col in
    case c of NONE => remove_colors col xs k
            | SOME c => remove_colors col xs 
                        (FILTER (λx.x ≠ c) k))`

(*EVAL``remove_colors (list_insert [1;2;3] [1;1;1] LN) [1;2;3;4] [1;2;3;4]``*)

(*Assigns a color or spills
  If assigning a color, use prefs to choose the color
  Constrain prefs to always choose from the list of available colors
*)  
(*NOTE: If we used redundancy in the graph representations,
 then we would use adj lists here*)
(*TODO: Make monadic on the last 2 arguments*)

val assign_color_def = Define`
  assign_color G k prefs v (nsv:num) col =
  case lookup v col of 
    SOME x => (nsv,col) (*Actually redundant but less constraining*)
  | NONE => 
  case lookup v G of
    (*Vertex wasn't even in the graph -- ignore*)
    NONE => (nsv,col)
  | SOME x =>
    let xs = MAP FST (toAList x) in
    let k = remove_colors col xs k in
    case k of 
      [] => (*Spill*) (nsv+4,insert v nsv col) 
    | xs => (*Choose a preferred color*) (nsv,insert v (prefs v xs col) col)` 

(*Auxiliary that colors according to the heuristic order (first list arg).

  The second list arg contains all the vertices which should actually 
  be colored. 
  Putting this here allows me to simplify the assumptions about 
  the heuristic list --> it does not need to generate a complete list

*)

(*TODO: Make monadic on the last 2 arguments*)
val find_coloring_aux = Define`
  (find_coloring_aux G k prefs [] nsv col = (nsv,col)) ∧ 
  (find_coloring_aux G k prefs (x::xs) nsv col = 
    let (nsv,col) = assign_color G k prefs x nsv col in
      find_coloring_aux G k prefs xs nsv col)`

val id_color_def = Define`
  id_color ls = FOLDR (λx y. insert x x y) LN ls` 

val list_max_def = Define`
  (list_max [] (lim:num) = lim) ∧
  (list_max (x::xs) lim = if x > lim then x else lim)` 

(*Main coloring step*)
val find_coloring_def = Define`
  find_coloring (G:sp_graph) k prefs ls =
    (*Setting up*)
    let vertices = MAP FST (toAList G) in 
    let (alloc,others) = split_list is_alloc_var vertices in
    let nsv_cand =  MAX (list_max vertices 0) k in
    let nsv = 4*nsv_cand+3 in
    (*Everything that cannot be allocated is identity colored*)
    let col = id_color others in
    let colors = GENLIST (λx:num.2*x) k in 
    let (nsv,col) = find_coloring_aux G colors prefs ls nsv col in
    (*Do the rest -- unnecessary if ls contains all of alloc*)
    find_coloring_aux G colors prefs alloc nsv col`
    
(*Extract a coloring function from the generated sptree*)
val total_color_def = Define`
  total_color col = 
    (λx. case lookup x col of NONE => x | SOME x => x)`

(*Property of an undirected (simple) graph*)
val undir_graph_def = Define`
  undir_graph (G:sp_graph) =
    ∀x. 
    case lookup x G of 
      NONE => T
    | SOME es =>
      x ∉ domain es ∧ 
      ∀y. y ∈ domain es ⇒ 
      ∃z. lookup y G = SOME z ∧ x ∈ domain z`

(*Property of preference function, it only chooses a color it is given*)
val satisfactory_pref_def = Define`
  satisfactory_pref prefs ⇔
    ∀h ls col v. prefs h ls col = v ⇒ MEM v ls`

(*VERY rough statement of the two theorems that must be proved 
  about find_coloring. Missing many assumptions:
  e.g. prefs must only select something from its input list
  *)
val split_list_splits = prove(``
  ∀ls P. 
  let (L,R) = split_list P ls in
    (∀x. MEM x ls ⇒ 
    (P x ∧ MEM x L) ∨ 
    (¬P x ∧ MEM x R))``,
  Induct>>
  fs[split_list_def,LET_THM]>> rw[]>>
  pop_assum (qspec_then `P` assume_tac)>>fs[]>>
  Cases_on`split_list P ls`>>fs[]>>
  Cases_on`P h` >>fs[]>>rw[]>>
  metis_tac[])

val id_color_lemma = prove(``
  ∀ls.
  let t = id_color ls in 
  domain t = set ls ∧ 
  ∀x. (MEM x ls ⇒ lookup x t = SOME x)``,
  Induct>>fs[id_color_def,LET_THM,lookup_insert]>>rw[])

val find_coloring_aux_never_overwrites = prove(``
  ∀xs nsv col nsv' col'.
  lookup x col = SOME y ∧ 
  find_coloring_aux G k prefs xs nsv col = (nsv',col')
  ⇒ 
  lookup x col' = SOME y``,
  Induct>>fs[find_coloring_aux,assign_color_def]>>rw[]>>fs[LET_THM]>>
  Cases_on`x = h`>>fs[]>>rfs[]
  >-
    metis_tac[]
  >>
  EVERY_CASE_TAC>>fs[]>>TRY(metis_tac[])>>
  res_tac>>fs[lookup_insert])

val find_coloring_conventional = store_thm ("find_coloring_conventional",``
  ∀G k prefs nsv ls.
  let (nsv',col) = find_coloring G k prefs nsv ls in
  let col = total_color col in 
  coloring_conventional G k col``,
  fs[coloring_conventional_def,find_coloring_def]>>rw[]>>
  unabbrev_all_tac>>
  IF_CASES_TAC>>
  TRY (IF_CASES_TAC)>>
  TRY (`¬is_alloc_var x` by metis_tac[convention_partitions]>>
  Q.ISPECL_THEN [`G`] assume_tac split_vertices_lemma>>
  rfs[LET_THM]>>res_tac>>
  Q.SPECL_THEN [`others`] assume_tac id_color_lemma>>
  rfs[LET_THM]>>res_tac>>
  imp_res_tac find_coloring_aux_never_overwrites>>
  fs[total_color_def])>>
  `is_alloc_var x` by metis_tac[convention_partitions]>>
  Q.ISPECL_THEN [`G`] assume_tac split_vertices_lemma>>
  rfs[LET_THM]>>res_tac>>
  (*Show that aux picks a conventonal color*)
  cheat); 

(*Restricted to a partial coloring*)
val partial_coloring_satisfactory_def = Define`
  partial_coloring_satisfactory col (G:sp_graph) ⇔ 
  ∀v.
    v ∈ domain G ∧ v ∈ domain col ⇒ 
    let edges = THE (lookup v G) in
    ∀v'. v' ∈ domain edges ∧ v' ∈ domain col ⇒ lookup v col ≠ lookup v' col`

val remove_colors_removes = prove(``
  ∀ls col k ls'.
  remove_colors col ls k = ls'
  ⇒ 
  ∀x. MEM x ls' ⇒
  MEM x k ∧  
  (∀y c. MEM y ls ∧ lookup y col = SOME c ⇒ c ≠ x)``,
  Induct>>fs[]>>rw[]>>
  Cases_on`k`>>
  fs[remove_colors_def,LET_THM]
  >-
    (FULL_CASE_TAC>>fs[]>-
    (res_tac>>pop_assum(qspec_then `y` assume_tac)>>fs[])>>
    Cases_on`h'=x'`>>fs[]>>res_tac>>
    fs[MEM_FILTER])
  >>
    FULL_CASE_TAC>>fs[]>-
      (res_tac>>pop_assum(qspec_then`y` assume_tac)>>
      Cases_on`y=h`>>fs[])>>
    res_tac>>
    Cases_on`h'=x'`>>fs[]>>
    first_x_assum(qspec_then`y` assume_tac)>>
    Cases_on`y=h`>>fs[MEM_FILTER]>>metis_tac[])

val partial_coloring_satisfactory_extend = prove(``
  partial_coloring_satisfactory col G ∧
  undir_graph G ∧ 
  h ∉ domain col ∧
  lookup h G = SOME x ∧
  (∀y. y ∈ domain x ∧ 
       y ∈ domain col ⇒ 
       THE (lookup y col) ≠ (v:num)) 
  ⇒ 
  partial_coloring_satisfactory (insert h v col) G``,
  fs[partial_coloring_satisfactory_def]>>rpt strip_tac
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
      (last_x_assum(qspec_then`v'`mp_tac)>>discharge_hyps>>fs[]>>rw[]>>
      last_x_assum(qspec_then`v'`assume_tac)>>rfs[]>>
      first_x_assum(qspec_then`h`assume_tac)>>rfs[]>>
      last_x_assum kall_tac>>
      last_x_assum(qspec_then`v'` assume_tac)>>rfs[])
    >>
      fs[]>>
      last_x_assum(qspec_then`v'`mp_tac)>>discharge_hyps>>fs[]>>rw[]>>
      pop_assum(qspec_then`v''''`assume_tac)>>rfs[])

(*nsv is greater than any color assigned so far*)
val nsv_gt_def = Define`
  nsv_gt (nsv:num) col =
  ∀x y. x ∈ domain col ∧ lookup x col = SOME y ⇒ 
        y < nsv`

val find_coloring_aux_satisfactory = prove(``
  ∀G k prefs nsv ls col.
  undir_graph G ∧ 
  satisfactory_pref prefs ∧ 
  partial_coloring_satisfactory col G ∧
  (∀x. MEM x k ⇒ x < nsv) ∧  
  nsv_gt nsv col 
  ⇒ 
  let (nsv,col') = find_coloring_aux G k prefs ls nsv col in
    partial_coloring_satisfactory col' G ∧
    nsv_gt nsv col'``,
  Induct_on`ls`>>fs[find_coloring_aux,assign_color_def,LET_THM]>>rw[]>>
  EVERY_CASE_TAC>>fs[]
  >-
    (first_x_assum(qspecl_then 
      [`G`,`k`,`prefs`,`nsv+4`,`insert h nsv col`] mp_tac)>>
      discharge_hyps>>fs[]>>rw[]
    >-
      (match_mp_tac partial_coloring_satisfactory_extend>>rw[]>>
      fs[domain_lookup,nsv_gt_def]>>
      last_x_assum(qspecl_then[`y`,`v`] assume_tac)>>rfs[]>>
      DECIDE_TAC)
    >-
      (rw[]>>res_tac>>DECIDE_TAC)
    >>
      (fs[nsv_gt_def,lookup_insert,domain_lookup]>>rw[]>>rfs[]>>
      last_x_assum(qspecl_then[`x'`,`v`] assume_tac)>>rfs[]>>
      DECIDE_TAC))
  >>
    (first_x_assum(qspecl_then 
      [`G`,`k`,`prefs`,`nsv`,`insert h (prefs h (h'::t) col) col`] mp_tac)>>
    discharge_hyps>>fs[]>>CONJ_TAC
    >-
      (match_mp_tac partial_coloring_satisfactory_extend>>rw[]>>
      fs[domain_lookup]>>
      imp_res_tac remove_colors_removes>>
      fs[satisfactory_pref_def]>>
      first_x_assum(qspecl_then[`h`,`h'::t`,`col`] assume_tac)>>
      `MEM y (MAP FST (toAList x))` by 
        fs[MEM_MAP,MEM_toAList,EXISTS_PROD,domain_lookup]>>
      rfs[]>>res_tac>>
      metis_tac[])
    >>
      fs[nsv_gt_def,lookup_insert]>>rw[]
      >-
       (imp_res_tac remove_colors_removes>>
       fs[satisfactory_pref_def]>>
       first_x_assum(qspecl_then[`h`,`h'::t`,`col`] assume_tac)>>
       fs[])
      >>
        metis_tac[]))

val find_coloring_aux_domain = prove(``
  ∀G k prefs nsv ls col nsv' col'.
  find_coloring_aux G k prefs ls nsv col = (nsv',col')
  ⇒ 
  ∀x. MEM x ls ∧ x ∈ domain G ⇒ x ∈ domain col'``,
  Induct_on`ls`>>fs[find_coloring_aux,LET_THM,assign_color_def]>>
  rw[]>>EVERY_CASE_TAC>>fs[domain_lookup]>>
  imp_res_tac find_coloring_aux_never_overwrites>>
  metis_tac[lookup_insert])

val find_coloring_satisfactory = store_thm ("find_coloring_satisfactory",``
  ∀G k prefs nsv ls.
  satisfactory_pref prefs ∧
  undir_graph G
  ⇒  
  let (nsv',col) = find_coloring G k prefs ls in
  let col = total_color col in
  coloring_satisfactory col G``,
  fs[coloring_satisfactory_def,find_coloring_def]>>rw[]>>
  fs[domain_lookup,total_color_def]>>
  Q.ISPECL_THEN [`G`,`colors`,`prefs`,`nsv`,`ls`,`col`] mp_tac
    find_coloring_aux_satisfactory>>
  discharge_hyps_keep>-
    (rfs[]>>cheat)>>
  rw[LET_THM]>>
  Q.ISPECL_THEN [`G`,`colors`,`prefs`,`nsv'`,`alloc`,`col'`] mp_tac
    find_coloring_aux_satisfactory>>
  discharge_hyps>-
    (rfs[]>>cheat)>>
  rw[LET_THM]>>
  fs[partial_coloring_satisfactory_def,undir_graph_def]>>
  last_x_assum(qspec_then`v` assume_tac)>>rfs[]>>
  `e ∈ domain v'` by fs[domain_lookup]>>
  first_x_assum(qspec_then`e`assume_tac)>>rfs[]>>
  first_x_assum(qspec_then`e` mp_tac)>> discharge_hyps
  >- cheat
  >>
  fs[LET_THM]>>rw[]>>
  `e ∈ domain G ∧ v ∈ domain G` by fs[domain_lookup]>>
  (*By construction, we must have colored everything*)
  `e ∈ domain col'' ∧ v ∈ domain col''` by
    (imp_res_tac find_coloring_aux_domain>>
    cheat)>>
  first_x_assum(qspec_then`v` mp_tac)>>
  discharge_hyps
  >-
    rfs[]
  >>
    rw[Abbr`col'''`]>>fs[domain_lookup]>>
    metis_tac[])
    

(*Defining the register allocator monad*)

val _ = Hol_datatype `
  ra_state = <| graph : sp_graph;
                degs : num num_map;(*maybe should become a 2 step O(1)lookup*)
                simp_worklist : num list;
                spill_worklist : num list;
                (*TODO: the other work lists*)
                coalesced : num num_map;
                next_spill_var : num;
                coloring : num num_map |>`;

(*Identity monad*)
val id_bind_def = Define`
  id_bind f = λs. f s`
  
val id_return_def = Define`
  id_return = I`

open monadsyntax;

val _ = temp_overload_on ("monad_bind", ``id_bind``);
(*
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_bind x (\z. y)``);
*)
val _ = temp_overload_on ("return", ``id_return``);



(*
(*Simplify
  Takes a graph G,
  The current working degree list deg_list,
  The number of colors k

  Returns a tuple (remaining vertices,stack)
*)

(*SPLITP in rich_listTheory doesn't have many theories with it
  split_deg splits list into those less than degree and those >=
*)

val split_deg_def = Define`
  split_deg k ls = SPLITP (λx,y:num. y<k) ls` 

(*EVAL ``split_deg 2 [1,2;2,3;3,1]``*) 

val decrement_def = Define`
  (decrement (es:num_set) [] = []) ∧ 
  (decrement es ((v,deg:num)::xs) =
    let rest = decrement es xs in 
    if lookup v es = SOME () then (v,deg-1)::rest else (v,deg)::rest)`

val dec_deg_def = Define`
  (dec_deg G [] ls = []) ∧ 
  (dec_deg G (x::xs) ls) =
    let es = lookup x G in
    case es of NONE => dec_deg G xs ls
            |  SOME es => dec_deg G xs (decrement es ls)`

(*Single step simplification*)
val simplify_def = Define `
  simplify k G deg_list =
  let (non_simp,simp) = split_deg k deg_list in
    case simp of 
      [] => (non_simp,[])
    | simp => 
      let simp = MAP FST simp in (*Discard degree information*)
      (dec_deg G simp non_simp,simp)`

(*Single step spill, arbitrarily pick x to be spilled for now*)
val spill_def = Define `
  spill ((x,y)::xs) = (x,xs)`

(*Main loop that calls the steps WITH the recursion builtin:
  Result should be a stack*)
val reg_alloc_loop_def = tDefine "reg_alloc_loop" `
  (reg_alloc_loop k G [] stack = stack) ∧ 
  (reg_alloc_loop k G deglist stack =
    let (deglist,newstack) = simplify k G deglist in
    case newstack of
      [] => (*Spilling*)
      let (v,deglist) = spill deglist in
        reg_alloc_loop k G deglist (v::stack)
    | xs => reg_alloc_loop k G deglist (xs++stack))` cheat


(*TODO:WF_REL_TAC on the size of deg_list
  WF_REL_TAC `measure LENGTH`*)

(*EVAL ``is_stack_var 7``*)

(*Generate list of vertices and associated degree from spgraph
  NOTE: 
  1) only need to do  registers
  2) Ignore stack registers in degree counts
*)
val gen_worklist_aux_def = Define`
  (gen_worklist_aux [] = []) ∧
  (gen_worklist_aux ((v,es)::xs) =
    let rest = gen_worklist_aux xs in
    if is_alloc_var v then
      let edges = FILTER (λv. ¬ (is_stack_var v)) (MAP FST (toAList es)) in  
      (v,LENGTH edges)::rest
    else rest)`

val gen_worklist_def = Define`
  gen_worklist (G:sp_graph) =
  gen_worklist_aux (toAList G)` 

EVAL ``gen_worklist (get_spg
  (Seq (Move [1,2;3,4;5,6]) 
  (Call (SOME (3, list_insert [1;3;5;7;9] [();();();();()] LN,Skip)) (SOME 400) [7;9] NONE)) LN)``


(*Graph representation is a list of pairs (v,edgelist)
  Graph is undirected
  [
   v1, (u1 u2 ...);
   v2, (...);
   ...
  ]
*)

(*Convert clash_sets to a clash graph with David's conventions

First do a conversion to (numset) sptrees
Then flatten the sets
*)

(*Convert to clash graph representation*)
val sp_g_to_cg_def = Define`
  sp_g_to_cg g = 
    MAP (λx,y. x,nub (MAP FST (toAList y))) (toAList g)`

val get_cg_def = Define`
  get_cg prog live = 
    let (hd,clash_sets) = get_clash_sets prog live in
      sp_g_to_cg (clash_sets_to_sp_g (hd::clash_sets))`


(*Cliques in cg*)
val cg_is_clique_def = Define`
  (cg_is_clique ls g = 
    !x y. MEM x ls ∧ MEM y ls ∧ x ≠ y ⇒ 
      (?t. ALOOKUP g x = SOME t ∧ MEM y t) ∧
      (?t. ALOOKUP g y = SOME t ∧ MEM x t))` 

val num_set_domain = prove(``
  !x (t:num_set) v.
  x ∈ domain t ⇒ lookup x t = SOME ()``,
  rw[]>>
  fs[domain_lookup])

(*Clique preservation*)
val sp_clique_to_cg_clique = prove(``
  !ls g.
  sp_g_is_clique ls g ⇒ 
  cg_is_clique ls (sp_g_to_cg g)``,
  rw[sp_g_is_clique_def,cg_is_clique_def,sp_g_to_cg_def,lookup_g_def]>>
  fs[ALOOKUP_MAP]>>
  first_x_assum(qspecl_then [`x`,`y`] assume_tac)>>rfs[]>>
  EVERY_CASE_TAC>>
  fs[ALOOKUP_toAList,MEM_MAP,MEM_toAList,EXISTS_PROD]>>
  metis_tac[num_set_domain,MEM_MAP])

(*Defs from David*)
(* Coloring satisfies constraints *)
val coloring_satisfactory_alt = prove(``
  !g f.
  coloring_satisfactory f g ⇒ 
  ∀x ls. ALOOKUP g x= SOME ls ⇒ ¬(MEM (f x) (MAP f ls))``,
  Induct>>rw[]>>
  Cases_on`h`>>fs[coloring_satisfactory_def]>>
  Cases_on`x=q`>>fs[])

val coloring_satisfactory_cliques = prove(``
  !ls g f.
  ALL_DISTINCT ls ∧ 
  coloring_satisfactory f g ∧ cg_is_clique ls g
  ⇒ 
  ALL_DISTINCT (MAP f ls)``,
  Induct>>
  fs[cg_is_clique_def]>>
  rw[coloring_satisfactory_def]
  >-
    (fs[MEM_MAP]>>rw[]>>
    first_x_assum(qspecl_then [`h`,`y`] assume_tac)>>rfs[]>>
    metis_tac[coloring_satisfactory_alt,MEM_MAP])
  >>
    first_x_assum(qspecl_then [`g`,`f`] mp_tac)>>rfs[])

val coloring_satisfactory_coloring_ok_alt = prove(``
  ∀prog f live.
  let cg = get_cg prog live in
  coloring_satisfactory f cg
  ⇒ 
  coloring_ok_alt f prog live``,
  rpt strip_tac>>
  fs[LET_THM,coloring_ok_alt_def,coloring_satisfactory_def,get_cg_def]>>
  Cases_on`get_clash_sets prog live`>>fs[]>>
  strip_tac>>
  qabbrev_tac `ls = q::r`>>
  qsuff_tac `EVERY (λs. INJ f (domain s) UNIV) ls`
  >-
    fs[Abbr`ls`]
  >>
  rw[EVERY_MEM]>>
  imp_res_tac clash_sets_clique>>
  imp_res_tac sp_clique_to_cg_clique>>
  imp_res_tac coloring_satisfactory_cliques>>
  fs[INJ_DEF,all_distinct_nub]>>rw[]>>
  fs[domain_lookup]>>
  `MEM x (MAP FST (toAList s)) ∧
   MEM y (MAP FST (toAList s))` by 
    (fs[MEM_MAP,EXISTS_PROD]>>
    metis_tac[domain_lookup,MEM_MAP,EXISTS_PROD,MEM_toAList])>>
  `ALL_DISTINCT (nub (MAP FST (toAList s)))` by 
    metis_tac[all_distinct_nub]>>
  fs[EL_ALL_DISTINCT_EL_EQ]>>
  imp_res_tac MEM_nub>>
  fs[MEM_EL]>>pop_assum (SUBST1_TAC o SYM)>>
  simp[]>>
  metis_tac[EL_MAP])


(* 
EVAL ``get_cg
  (Seq (Move [1,2;3,4;5,6]) 
  (Call (SOME (3, list_insert [1;3;5;7;9] [();();();();()] LN,Skip)) (SOME 400) [7;9] NONE)) LN``
*)

*)

