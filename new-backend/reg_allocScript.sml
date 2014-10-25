open HolKernel Parse boolLib bossLib miscLib
open listTheory sptreeTheory pred_setTheory pairTheory
open alistTheory
open BasicProvers
open word_liveTheory
open word_langTheory

val _ = new_theory "reg_alloc";

(*Defines the register allocator*)

(*Graph representation is a list of pairs (v,edgelist)
  [
   v1, (u1 u2 ...);
   v2, (...);
   ...
  ]
*)

(*Convert live_sets to a clash graph with David's conventions

First do a conversion to (numset) sptrees
Then flatten the sets
*)

(*Lookup edge in spgraph*)
val lookup_g_def = Define`
  lookup_g x y (g:num_set num_map) =
    case lookup x g of NONE => F
                     | SOME t => y ∈ (domain t)` 

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

(*Every live-set should form a clique*)
val clique_g_insert_def = Define`
  (clique_g_insert [] g = g) ∧ 
  (clique_g_insert (x::xs) g =
    list_g_insert x xs (clique_g_insert xs g))`

val live_sets_to_sp_g_def = Define`
  (live_sets_to_sp_g [] = LN) ∧ 
  (live_sets_to_sp_g (x::xs) =
    (*I think nub probably makes it easier*)
    let subgraph = live_sets_to_sp_g xs in
    let clashes = nub (MAP FST (toAList x)) in
    clique_g_insert clashes subgraph)`

(*Convert to clash graph representation*)
val sp_g_to_cg_def = Define`
  sp_g_to_cg g = 
    MAP (λx,y. x,nub (MAP FST (toAList y))) (toAList g)`

val get_cg_def = Define`
  get_cg prog = sp_g_to_cg (live_sets_to_sp_g (merge_pair(get_live_sets prog LN)))`

(*Proof idea:
  Show that livesets always appear as cliques in the graph
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
    fs[domain_insert])

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

val live_sets_clique = prove(``
  !ls x. 
  MEM x ls ⇒ 
  sp_g_is_clique (nub (MAP FST (toAList x))) (live_sets_to_sp_g ls)``,
  Induct>>fs[live_sets_to_sp_g_def]>>rw[]>>
  unabbrev_all_tac>>
  metis_tac[clique_g_insert_is_clique
           ,clique_g_insert_preserves_clique,all_distinct_nub])

(*Defs from David*)
(* Coloring satisfies constraints *)
val coloring_satisfactory_def = Define `
    (coloring_satisfactory col [] = T) /\
    (coloring_satisfactory col ((r, rs)::cs) = 
      (~(MEM (col r) (MAP col rs)) ∧ (coloring_satisfactory col cs)))`

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

val MEM_nub = prove(``
  ∀ls x. MEM x ls ⇒ MEM x (nub ls)``,
  rw[])

val coloring_satisfactory_coloring_ok_alt = prove(``
  ∀prog f.
  let ls = merge_pair (get_live_sets prog LN) in
  let cg = sp_g_to_cg (live_sets_to_sp_g ls) in 
  coloring_satisfactory f cg
  ⇒ 
  coloring_ok_alt f prog LN``,
  rw[coloring_ok_alt_def,coloring_satisfactory_def]>>
  fs[EVERY_MEM,Abbr`cg`]>>rw[]>>
  imp_res_tac live_sets_clique>>
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
  
EVAL ``get_cg
  (Seq (Move [1,2;3,4;5,6]) 
  (Call (SOME (3, list_insert [1;3;5;7;9] [();();();();()] LN,Skip)) (SOME 400) [7;9] NONE))``


