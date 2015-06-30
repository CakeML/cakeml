open HolKernel Parse boolLib bossLib miscLib
open listTheory sptreeTheory pred_setTheory pairTheory rich_listTheory alistTheory
open BasicProvers
open sortingTheory
open monadsyntax state_transformerTheory

val _ = ParseExtras.tight_equality ();

val _ = new_theory "reg_alloc";

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

(*Defines a graph colouring algorithm*)

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
  (list_g_insert x [] g =
    (*Single node with no adjacent edges*)
    case lookup x g of NONE => insert x LN g
                     | SOME y => g) ∧
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
    let subgraph = clash_sets_to_sp_g xs in
    let clashes = (MAP FST (toAList x)) in
    clique_g_insert clashes subgraph)`

(*
  Link up colouring_satisfactory to colouring_ok
  Proof idea:
  Show that clash sets always appear as cliques in the graph
  and colouring_satisfactory guarantees that cliques have all
  distinct colours
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
  ∀ls x g.
  let g' = list_g_insert x ls g in
    ∀u v.
      lookup_g u v g' = ((u = x ∧ MEM v ls)
                      ∨ (v = x ∧ MEM u ls)
                      ∨ lookup_g u v g)``,
  Induct>>rw[list_g_insert_def,undir_g_insert_def]>>
  unabbrev_all_tac>>fs[]>-
    (fs[lookup_g_def]>>EVERY_CASE_TAC>>fs[lookup_insert]>>
    EVERY_CASE_TAC>>fs[]>>qpat_assum`LN = x'` (SUBST_ALL_TAC o SYM)>>
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
    fs[lookup_g_def]>>EVERY_CASE_TAC>>fs[]>>
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

(*---
Start colouring algorithms
First phase (alloc_colouring): Produces a bounded colouring (< 2k)
Second phase (spill_colouring): Produces unbounded colouring (≥ 2k)
---*)

(*Define the first colouring step:
  Takes arguments:
  G = spgraph (possibly augmented e.g. in coalescing),
  k = number of registers to use,
  prefs = num-> num list -> num (selects a colour from the list),
  ls = heuristic order to colour vertices,
  Result: a num sptree where looking up a vertex gives its colouring
      and a num list of spilled vertices
  TODO: Decide if this should be monadic
*)

(*Deletes unavailable colours by looking up the current colouring function*)
(*This terminates early when k becomes empty so that we do not need to lookup every single neighbor... maybe the other way is equally efficient?*)
(*k is usually small --> just use a list, eventually a bitset*)
val remove_colours_def = Define`
  (*No more available colours*)
  (remove_colours (col:num num_map) ls [] = []) ∧
  (*Some available colour after checking*)
  (remove_colours (col:num num_map) [] k = k) ∧
  (*Do the checks*)
  (remove_colours col (x::xs) k =
    let c = lookup x col in
    case c of NONE => remove_colours col xs k
            | SOME c => remove_colours col xs
                        (FILTER (λx.x ≠ c) k))`

(*Assigns a colour or spills
  If assigning a colour, use prefs to choose the colour
  Constrain prefs to always choose from the list of available colours

  Returns a new colouring and spill list
*)
(*NOTE: If we used redundancy in the graph representations,
 then we would use adj lists here*)

val assign_colour_def = Define`
  assign_colour G k prefs v col spills =
  case lookup v col of
    SOME x => (col,spills) (*Actually redundant but less constraining*)
  | NONE =>
  if MEM v spills then (col,spills) (*Another redundant check*)
  else
  case lookup v G of
    (*Vertex wasn't even in the graph -- ignore*)
    NONE => (col,spills)
  | SOME x =>
    if is_alloc_var v then
      let xs = MAP FST (toAList x) in
      let k = remove_colours col xs k in
      case k of
        [] =>
        (*Spill*) (col,v::spills)
      | (x::xs) =>
        (*Choose a preferred colour*)
        let colour = case prefs v (x::xs) col of NONE => x | SOME y => y in
        (insert v colour col,spills)
    else
      (*Spill if it was not an alloc_var*)
      (col,v::spills)`

(*Auxiliary that colours vertices in the order of the input list*)
(*TODO: Make monadic on the last 2 arguments?*)
val alloc_colouring_aux = Define`
  (alloc_colouring_aux G k prefs [] col spills = (col,spills)) ∧
  (alloc_colouring_aux G k prefs (x::xs) col spills =
    let (col,spills) = assign_colour G k prefs x col spills in
      alloc_colouring_aux G k prefs xs col spills)`

val id_colour_def = Define`
  id_colour ls = FOLDR (λx y. insert x x y) LN ls`

(*First colouring step:
  End result should be a colouring that sends
  phy_vars to phy_vars,
  alloc_vars which were properly allocated to phy_vars
  Everything else should be in the resulting spill list
  (unallocated alloc_vars and stack_vars)
*)
val alloc_colouring_def = Define`
  alloc_colouring (G:sp_graph) k prefs ls =
    (*Setting up*)
    let vertices = MAP FST (toAList G) in
    let (phy_var,others) = PARTITION is_phy_var vertices in
    (*Everything that cannot be allocated is identity coloured*)
    let col = id_colour phy_var in
    let colours = GENLIST (λx:num.2*x) k in
    (*First do the ones given in the input list*)
    let (col,spills) = alloc_colouring_aux G colours prefs ls col [] in
    (*Do the rest -- this automatically spills everything is_stack_var
      as well*)
    alloc_colouring_aux G colours prefs others col spills`

(*Unbounded colouring*)
val unbound_colours_def = Define `
  (unbound_colours col [] = col) ∧
  (unbound_colours col ((x:num)::xs) =
    if col < x then
      col
    else if x = col then
      unbound_colours (col+2) xs
    else
      unbound_colours col xs)`

(*EVAL``unbound_colours 2 [2;4;8]``*)

(*Probably already in HOL*)
val option_filter_def = Define`
  (option_filter [] = []) ∧
  (option_filter (x::xs) =
    case x of NONE => option_filter xs | SOME y => y :: (option_filter xs))`

val assign_colour2_def = Define`
  assign_colour2 G k prefs v col =
  case lookup v col of
    SOME x => col
  | NONE =>
  case lookup v G of
    NONE => col (*Vertex wasn't even in the graph -- ignore*)
  | SOME x =>
    let xs = MAP FST (toAList x) in
    (*Get all the nightbor colours*)
    let cols = option_filter (MAP (λx. lookup x col) xs) in
    let pref_col =
      case lookup v prefs of
        NONE => NONE
      | SOME u =>
        case lookup u col of
          NONE => NONE (*Should never occur if coalesces are properly done*)
        | SOME c =>
          if MEM c cols ∨
             (¬(is_phy_var c ∧ c≥2*k))
             (*unnecessary check because the prefs might contain "false"
               coalesces -- which never occurs if implemented properly*)
          then NONE else SOME c in
    let c =
    case pref_col of
      NONE => unbound_colours (2*k) (QSORT (λx y. x≤y) cols)
    | SOME c => c in
      insert v c col`

(*ls is a spill list,
  prefs is a coalescing oracle
*)
val spill_colouring_def = Define`
  (spill_colouring (G:sp_graph) k prefs [] col = col) ∧
  (spill_colouring G k prefs (x::xs) col =
    let col = assign_colour2 G k prefs x col in
    spill_colouring G k prefs xs col)`

(*End colouring definitions*)

(*Define register allocation*)

val _ = Hol_datatype `
  ra_state = <| graph : sp_graph;
                colours : num;
                degs : num num_map;(*keeps track of vertex degrees maybe should become a 2 step O(1)lookup*)
                simp_worklist : num list; (*Non-move related vertices of low degree*)
                freeze_worklist : num list; (*Move related vertices of low degree*)
                spill_worklist : num list; (*Vertices with degree ≥ k*)
                stack : num list; (*Coloring stack*)
                coalesced : num num_map; (*coalesced nodes*)
                move_related : num_set; (*move_related nodes fast lookup*)
                avail_moves_pri : (num # num # num) list; (*track prioritized available moves*)
                avail_moves : (num # num # num) list; (*Normal priority moves*)
                unavail_moves : (num # num # num) list; (*track diabled moves which can be re-enabled*)
                clock : num (*Termination counter*)
             |>`

(*Parameterized by P because we only count certain types of adjacency in each colouring step*)
val count_degrees_def = Define`
  count_degrees P (e:num_set) =
  LENGTH (FILTER P (MAP FST (toAList e)))`

val in_moves_def = Define`
  (in_moves [] x = F) ∧
  (in_moves ((pri,x,y)::xs) z = ((x = z) ∨ (y = z) ∨ in_moves xs z))`

val in_moves_set_def = Define`
  (in_moves_set moves [] = LN) ∧
  (in_moves_set moves (x::xs) =
    let rest = in_moves_set moves xs in
      if in_moves moves x
      then insert x () rest
      else rest)`

(*For the first phase, we only care about alloc_var or <2*k phy_vars*)
val considered_var_def = Define`
  considered_var k x = (is_alloc_var x ∨ (is_phy_var x ∧ x <2*k))`

val split_priority_def = Define`
  split_priority ls = PARTITION (λp,x,y. p > 0:num) ls`

(*Initialize state for the first phase*)
val init_ra_state_def = Define`
  (init_ra_state (G:sp_graph) (k:num) moves =
  let moves =
    FILTER (λp,x,y. (considered_var k) x ∧ (considered_var k) y) moves in
  let vertices = FILTER is_alloc_var (MAP FST (toAList G)) in (*Only care about allocatable vars*)
  let vdegs = MAP (λv. v,count_degrees (considered_var k)
              (THE(lookup v G))) vertices in
  let tdegs = fromAList vdegs in (*Initial degree set*)
  let (simp_freeze,spill) = PARTITION (λx,(y:num). y<k) vdegs in
  (*Degrees < k can be frozen or simplified, otherwise they go into spill*)
  (*Distinguish move and non-move vertices*)
  let move_rel = in_moves_set moves vertices in
  let (pri_moves,moves) =
    PARTITION (λp,x,y. p > 0) moves in
  let (freeze,simp) = PARTITION (λx,y. lookup x move_rel = SOME ()) simp_freeze in
  <|graph := G ; colours := k ; degs := tdegs;
    simp_worklist := MAP FST simp;
    freeze_worklist := MAP FST freeze;
    spill_worklist := MAP FST spill;
    stack:=[];
    coalesced:=LN;
    move_related:= move_rel;
    avail_moves_pri := pri_moves;
    avail_moves:=moves;
    unavail_moves:=[];
    clock:=LENGTH vertices
  |>)`

val get_stack_def = Define`
  get_stack = \s. (return s.stack) s`

val get_graph_def = Define`
  get_graph = \s. (return s.graph) s`

(*When we push things onto the colouring stack,
  1) Delete from the degs list -->
     makes checking the briggs criterion neater
  2) Disable all moves related to it
*)
val push_stack_def = Define`
  push_stack v =
    λs. ((), s with <|stack:= v::s.stack; degs:=delete v s.degs;
                      move_related := delete v s.move_related|>)`

val get_degs_def = Define`
  get_degs = \s. (return s.degs) s`

val get_deg_def = Define`
  get_deg v = \s. (return (lookup v s.degs)) s`

val set_deg_def = Define`
  set_deg k v = \s. ((), s with degs := insert k v s.degs)`

val add_simp_worklist_def = Define`
  add_simp_worklist ls = \s. ((), s with simp_worklist := ls++s.simp_worklist )`

val add_spill_worklist_def = Define`
  add_spill_worklist ls = \s. ((), s with spill_worklist := ls++s.spill_worklist )`

val add_freeze_worklist_def = Define`
  add_freeze_worklist ls = \s. ((), s with freeze_worklist := ls++s.freeze_worklist )`

val set_spill_worklist_def = Define`
  set_spill_worklist ls = \s. ((), s with spill_worklist := ls)`

val get_spill_worklist_def = Define`
  get_spill_worklist = \s. return s.spill_worklist s`

val get_simp_worklist_def = Define`
  get_simp_worklist = \s. return s.simp_worklist s`

val set_simp_worklist_def = Define`
  set_simp_worklist ls = \s. ((), s with simp_worklist := ls)`

val get_freeze_worklist_def = Define`
  get_freeze_worklist = \s. return s.freeze_worklist s`

val set_freeze_worklist_def = Define`
  set_freeze_worklist ls = \s. ((), s with freeze_worklist := ls)`

val get_colours_def = Define`
  get_colours = \s. return s.colours s`

val get_move_rel_def = Define`
  get_move_rel = \s. return s.move_related s`

val set_move_rel_def = Define`
  set_move_rel move_rel = \s. ((), s with move_related := move_rel)`

val get_coalesced_def = Define`
  get_coalesced = \s. return s.coalesced s`

val set_coalesced_def = Define`
  set_coalesced coalesce = \s. ((), s with coalesced := coalesce)`

val get_avail_moves_pri_def = Define`
  get_avail_moves_pri = \s. return s.avail_moves_pri s`

val get_avail_moves_def = Define`
  get_avail_moves = \s. return s.avail_moves s`

val set_avail_moves_pri_def = Define`
  set_avail_moves_pri moves = \s. ((), s with avail_moves_pri := moves)`

val set_avail_moves_def = Define`
  set_avail_moves moves = \s. ((), s with avail_moves := moves)`

val add_avail_moves_pri_def = Define`
  add_avail_moves_pri moves = \s. ((), s with avail_moves_pri := moves++s.avail_moves_pri)`

val add_avail_moves_def = Define`
  add_avail_moves moves = \s. ((), s with avail_moves := moves++s.avail_moves)`

val get_unavail_moves_def = Define`
  get_unavail_moves = \s. return s.unavail_moves s`

val set_unavail_moves_def = Define`
  set_unavail_moves moves = \s. ((), s with unavail_moves := moves)`

val add_unavail_moves_def = Define`
  add_unavail_moves moves = \s. ((), s with unavail_moves := moves++s.unavail_moves)`

val freeze_node_def = Define`
  freeze_node x = \s. ((), s with move_related := delete x s.move_related)`

val add_coalesce_def = Define`
  add_coalesce x y = \s. ((), s with coalesced := insert y x s.coalesced)`

val get_edges_def = Define`
  get_edges v = \s. return (lookup v s.graph) s`

(*Increment the degree of a single vertex by 1*)
val inc_one_def = Define`
  inc_one v =
  do
    optd <- get_deg v;
    case optd of
      NONE => return ()
    | SOME (d:num) => set_deg v (d+1)
  od`

(*Decrement the degree of a single vertex by 1*)
val dec_one_def = Define`
  dec_one v =
  do
    optd <- get_deg v;
    case optd of
      NONE => return ()
    | SOME (d:num) => set_deg v (d-1)
  od`

(*Update the degree sptree with the deletion of v*)
val dec_deg_def = Define`
  dec_deg v =
  do
    g <- get_graph ;
    case lookup v g of
    | NONE => return ()
    | SOME es =>
      let edges = MAP FST(toAList es) in
        FOREACH (edges,dec_one)
  od`

(*Revive all the moves that might have been previously stopped by v because
  v is now a low degree vertex
  Also, split into prioritized ones and unprioritized ones
  *)
val revive_moves_def = Define`
  revive_moves v =
  do
    g <- get_graph;
    case lookup v g of
      NONE => return ()
    | SOME es =>
      let edges = (v::MAP FST(toAList es)) in (*We also revive v itself*)
      do
        unavail_moves <- get_unavail_moves;
        let(rev,unavail) = PARTITION
          (λp,x,y. MEM x edges ∨ MEM y edges) unavail_moves in
        let(rev_pri,rev) = split_priority rev in
        do
          add_avail_moves_pri rev_pri;
          add_avail_moves rev;
          set_unavail_moves unavail
        od
      od
  od`

(*Move currently spilled vertices of degree < k into freeze or simp*)
val unspill_def = Define`
  unspill =
  do
    swl <- get_spill_worklist ;
    degs <- get_degs ;
    colours <- get_colours ;
    move_rel <- get_move_rel ;
    let (ltk,gtk) = PARTITION
      (λv. case lookup v degs of
          NONE => F
        | SOME x => x < colours) swl in
    let (ltk_freeze,ltk_simp) = PARTITION
      (λv. lookup v move_rel = SOME ()) ltk in (*Consistency: TODO!*)
    do
      FOREACH (ltk,revive_moves);
      set_spill_worklist gtk ;
      add_simp_worklist ltk_simp ;
      add_freeze_worklist ltk_freeze
    od
  od`

val simplify_def = Define`
  simplify =
  do
    simps <- get_simp_worklist;
    case simps of
      [] =>
        return NONE
    | (x::xs) =>
      do
        set_simp_worklist xs;
        dec_deg x;
        unspill;
        return (SOME x)
      od
  od`

(*Spill the vertex that has maximal degree
  - The idea here is that it reduces the degree of adjacent vertices
    as much as possible
*)
val max_non_coalesced_def = Define`
  (max_non_coalesced (coalesced:num num_map) (degs:num num_map) [] acc (v,deg) = (v,acc)) ∧
  (max_non_coalesced coalesced degs (x::xs) acc (v,deg) =
    if lookup x coalesced = NONE then
      case lookup x degs of
        NONE =>  max_non_coalesced coalesced degs xs acc (v,deg)
      | SOME d =>
        if d > deg then max_non_coalesced coalesced degs xs (v::acc) (x,d)
                   else max_non_coalesced coalesced degs xs (x::acc) (v,deg)
    else
      max_non_coalesced coalesced degs xs acc (v,deg))`

val spill_def = Define`
  spill =
  do
    spills <- get_spill_worklist;
    coalesced <- get_coalesced;
    degs <- get_degs;
    (case spills of
      [] => return NONE
    | (x::xs) =>
     do
        deg <- return (case lookup x degs of NONE => 0 | SOME d => d);
        (x,xs) <- return(max_non_coalesced coalesced degs xs [] (x,deg));
        set_spill_worklist xs;
        dec_deg x;
        unspill;
        return (SOME x)
      od)
  od`

(*This differs slightly from the standard algorithm:
  We immediately simplify instead of moving the frozen node into the simp worklist
  This makes the termination clock easier since the number of vertices under consideration strictly decreases by 1

  A new trick: we push fixing up move_related into freeze
  There are corner cases where coalescing might have made invalid, resulting in vertices being marked move_related when they really should be simplified already.
*)

val freeze_def = Define`
  freeze =
  do
     freezes <- get_freeze_worklist;
     unavail_moves <- get_unavail_moves;
     graph <- get_graph;
     moves <- return (FILTER (λp,x,y. x ≠ y ∧ ¬lookup_g x y graph) unavail_moves);
     degs <- get_degs;
     move_rel <- return (in_moves_set moves (MAP FST (toAList degs)));
     coalesced <- get_coalesced;
     freezes <- return (FILTER (λx. lookup x coalesced = NONE) freezes);
     () <- set_move_rel move_rel;
     () <- set_unavail_moves moves;
     ox <- (
       let (freeze,simp) =
         PARTITION (λx. lookup x move_rel = SOME ()) freezes in
       (case simp of
         (x::xs) =>
         do
           add_simp_worklist xs;
           set_freeze_worklist freeze;
           return (SOME x)
         od
       | [] =>
       (case freeze of
         (x::xs) =>
         do
           set_freeze_worklist xs;
           return (SOME x)
         od
       | [] => return NONE)));
    (case ox of
       SOME x =>
         do
           dec_deg x;
           unspill;
           return (SOME x)
         od
     | NONE => return NONE)
  od`

(*Briggs criterion:
  The combined node xy should have less than k neighbors of significant degree
*)
val briggs_ok_def = Define`
  briggs_ok (G:sp_graph) (k:num) degs move =
  let (x,y) = move in
  case lookup x G of NONE => F
  | SOME x_edges =>
  case lookup y G of NONE => F
  | SOME y_edges =>
  let edges = union x_edges y_edges in
  let odegs = MAP (λx,y. lookup x degs) (toAList edges) in
  let degs = option_filter odegs in
    (LENGTH (FILTER (λx. x ≥ k) degs)) < k`

(*George criterion:
  Every neighbor of y is already a neighbor of x or else has insignificant degree
  In this application of the criterion,
  x should be a phy_var
*)
val george_ok_def = Define`
  george_ok (G:sp_graph) (k:num) degs move =
  let (x,y) = move in
  case lookup x G of NONE => F
  | SOME x_edges =>
  case lookup y G of NONE => F
  | SOME y_edges =>
  let edges = difference y_edges x_edges in (*Delete everything in y's neighbors already in x*)
  (*This also deletes phy_vars since they should never be in the deg set*)
  let odegs = MAP (λx,y. lookup x degs) (toAList edges) in
  let degs = option_filter odegs in
    EVERY (λx. x < k) degs`

(*A move (x,y) is still valid if
  1) at least one of x,y is not a phy_var
  2) the appropriate move_related conditions are fulfilled i.e. none of them are frozen
  3) they do not already clash in the graph -- maybe coalescing might make some new clashes
  4) x≠y (which might be caused by coalescing)
  Note that a node is move_related ⇒ it is still under consideration
*)

val is_valid_move_def = Define`
  is_valid_move G move_related move =
  let (p,x,y) = move in
  (x ≠ y ∧
  ¬ lookup_g x y G ∧
  if is_phy_var x then
    (lookup y move_related = SOME ())
  else
    ¬is_phy_var y ∧
    (lookup y move_related = SOME ()) ∧
    (lookup x move_related = SOME ()))`

(*A move is coalesceable if:
  1) x is a phy_var then use george criterion
  2) otherwise, use briggs criterion*)

val is_coalesceable_move_def = Define`
  is_coalesceable_move G (k:num) degs move =
  let (p,x,y) = move in
    if is_phy_var x then george_ok G k degs (x,y)
    else briggs_ok G k degs(x,y)`

(*3 way split of the available moves:
  An available move might be
  1) invalidated (P false) ⇒ can be discarded entirely
  2) still valid but not coalesceable (Q false) ⇒ keep in unavail_moves
  3) the rest ⇒ keep in avail_moves
*)
val split_avail_def = Define`
  (split_avail P Q [] acc = (NONE,acc,[])) ∧
  (split_avail P Q (x::xs) acc =
    if P x then
      if Q x then
        (SOME x,acc,xs)
      else
        split_avail P Q xs (x::acc)
    else
      split_avail P Q xs acc)`

val force_add_def = Define`
  force_add x y = \s. ((), s with graph:=undir_g_insert x y s.graph)`

(*TODO: All the coalescing code has to be carefully checked*)
(*We uniformly force the second half to be coalesced into the first*)
val do_coalesce_def = Define`
  do_coalesce move =
  let (x,y) = move in
  do
    add_coalesce x y;
    y_edges <- get_edges y;
    x_edges <- get_edges x;
    degs <- get_degs;
    k <- get_colours;
    case y_edges of NONE => return () (*Should never happen*)
    |  SOME y_edges =>
    case x_edges of NONE => return () (*Should never happen*)
    |  SOME x_edges =>
    (*Add only edges that need to be considered
      TODO: Need to be careful here!
      I think this is okay because at anytime we only need to consider the subgraph
      induced by the domain of degs (and the pre-coloured phy_vars)
    *)
    let edges = FILTER (λx. (lookup x degs ≠ NONE) ∨ (is_phy_var x ∧ x < 2*k))
                (MAP FST (toAList y_edges)) in
    FOREACH (edges,
          (λv.
            if lookup v x_edges = NONE then
              do
                inc_one x;
                force_add x v
              od
            else
              dec_one v))
  od`

val pair_rename_def = Define`
  pair_rename x y move =
  let (p,a,b) = move in
    let a = if a=y then x else a in
    let b = if b=y then x else b in
      (p,a,b)`

val respill_def = Define`
  respill x =
  do
    k <- get_colours;
    optd <- get_deg x;
    case optd of NONE => return ()
    | SOME d =>
    if d < k then return ()
    else
    do
      freeze <- get_freeze_worklist;
      if MEM x freeze then
      do
        add_spill_worklist [x];
        set_freeze_worklist (FILTER (λy.y≠x) freeze)
      od
      else return ()
    od
  od`

val coalesce_def = Define`
  coalesce =
  do
    G <- get_graph;
    k <- get_colours;
    degs <- get_degs;
    move_related <- get_move_rel;
    ls_pri <- get_avail_moves_pri;
    ores <-
    (case split_avail (is_valid_move G move_related)
      (is_coalesceable_move G k degs) ls_pri [] of (ores,nc,rest) =>
    do
      set_avail_moves_pri rest;
      add_unavail_moves nc;
      return ores
    od);
    ores <- (case ores of
      SOME (p,x,y) => return ores
    | NONE =>
      do
        ls <- get_avail_moves;
        (case split_avail (is_valid_move G move_related)
        (is_coalesceable_move G k degs) ls [] of (ores,nc,rest) =>
        do
          set_avail_moves rest;
          add_unavail_moves nc;
          return ores
        od)
      od);
    (case ores of
      SOME (p,x,y) =>
      do
        do_coalesce (x,y);
        avail_pri <- get_avail_moves_pri;
        avail <- get_avail_moves;
        unavail <- get_unavail_moves;
        let avail_pri = MAP (pair_rename x y) avail_pri in
        let avail = MAP (pair_rename x y) avail in
        let unavail = MAP (pair_rename x y) unavail in
        do
          set_avail_moves_pri avail_pri;
          set_avail_moves avail;
          set_unavail_moves unavail;
          unspill;
          respill x;
          return (SOME y)
        od
      od
    | NONE =>
      return NONE)
  od`

val dec_clock_def = Define`
  dec_clock = \s. ((), s with clock := s.clock-1)`

val get_clock_def = Define`
  get_clock = \s. (return s.clock) s`

(*TODO:I think there's an neater way to express this monadically*)
val do_step_def = Define`
  do_step =
  do
    dec_clock;
    optx <- simplify;
    case optx of
      SOME x => push_stack x
    | NONE =>
  do
    optx <- coalesce;
    case optx of
      SOME x => push_stack x
    | NONE =>
  do
    optx <- freeze;
    case optx of
      SOME x => push_stack x
    | NONE =>
  do
    optx <- spill;
    case optx of
      SOME x => push_stack x
    | NONE => return ()
  od
  od
  od
  od`

val has_work_def = Define`
  has_work =
  do
    clock <- get_clock;
    return (clock > 0)
  od`

val rpt_do_step_def = Define`
  rpt_do_step =
  MWHILE (has_work) do_step`

(*TODO: It seems like using the same monad for the second phase isn't very useful
  because the tasks involved is very different*)
(*Initialize state for the second phase, here we are given a list of
  vertices to consider
  and the map corresponding to already coalesced nodes
  *)
val sec_ra_state_def = Define`
  (sec_ra_state (G:sp_graph) (k:num) vertices coalesce_map =
  (*In the second stage, we care about the degree w.r.t. to other spilled
    temporaries or phy variables ≥ 2*k*)
  (*Simplify the preconditions*)
  let vertices = FILTER (λv. lookup v G ≠ NONE) vertices in
  let vdegs = MAP (λv. v,count_degrees
  (*The first check corresponds to the pre-allocated spill variables*)
    (λx. (is_phy_var x ∧ x ≥ 2*k) ∨ MEM x vertices)
              (THE(lookup v G))) vertices in
  let tdegs = fromAList vdegs in
  let st = MAP FST (toAList coalesce_map) in
  <|graph := G ; colours := k ; degs := tdegs;
    simp_worklist := vertices;
    stack:=st;
    (*unused parts follow*)
    spill_worklist := []; (*unused*)
    freeze_worklist := []; (*unused*)
    coalesced:=LN;
    move_related:=LN;
    avail_moves:=[];
    avail_moves_pri:=[];
    unavail_moves:=[];
    clock:=LENGTH vertices
  |>)`

(*Simplifies by removing the smallest degree node...
  worklist should ideally be a heap structure...*)
val deg_comparator_def = Define`
  deg_comparator (deg:num num_map) x y =
    case lookup x deg of
      NONE => T (*Never happens*)
    | SOME dx =>
      case lookup y deg of
      NONE => T (*Never happens*)
    | SOME dy => dx ≤ dy`

(*This is the simplified coalesce in the second phase which does
  not need to update the degrees in the graph
  It simply merges y into x
  Returns the new graph and a coalescing function
*)

val full_coalesce_aux = Define`
  (full_coalesce_aux G spills [] = (G,LN)) ∧
  (full_coalesce_aux G spills (move::xs) =
    (*Edge List for y*)
    let (p,x,y) = move in
    if (lookup_g x y G ∨ lookup x G = NONE)
    then full_coalesce_aux G spills xs
    else
    case lookup y G of NONE => full_coalesce_aux G spills xs 
    | SOME e =>
      (*For each adjacent vertex to y, make it adjacent to x*)
      let edges = FILTER (λx.MEM x spills) (MAP FST (toAList e)) in
      let G = list_g_insert x edges G in
      (*A way to work around having to use union find for coalesced aliasing
        is to completely rename the moves
        This is an additional O(m) a.k.a. horribly inefficient...
        But it means termination is not conditional on a wellformedness
        condition on the produced aliases
        TODO: If this turns out to be a bottleneck, maybe check out the
        implementation in the inferencer
        *)
      let r_xs = MAP (pair_rename x y) xs in
      let (G,t) = full_coalesce_aux G spills xs in
        (G,insert y x t))`

val full_coalesce_def = Define`
  full_coalesce G k moves spills =
  let coalesceable =
    FILTER (λp,x,y. (MEM x spills ∨ (is_phy_var x ∧ x ≥ 2*k)) ∧ MEM y spills) moves in
  let coalesceable = QSORT (λp:num,x,y p',x',y'. p>p') coalesceable in
  (*Maybe more efficient impl possible*)
  let (G,coalesce_map) =
    full_coalesce_aux G spills coalesceable in
    G, FILTER (λx. lookup x coalesce_map = NONE) spills, coalesce_map`

(*TODO: Maybe change this to use a minheap to get slightly better performance...
  Or rewrite in a way that allows quick re-sorts?
*)
val full_simplify_def = Define`
  full_simplify =
  do
    ls <- get_simp_worklist;
    degs <- get_degs;
    case QSORT (deg_comparator degs) ls of
      [] => return NONE
    | (x::xs) =>
      do
        set_simp_worklist xs;
        dec_deg x;
        return (SOME x)
      od
  od`

val do_step2_def = Define`
  do_step2 =
  do
    dec_clock;
    optx <- full_simplify;
    case optx of
      NONE => return ()
    | SOME x => push_stack x
  od`

val rpt_do_step_2_def = Define`
  rpt_do_step2 =
    MWHILE (has_work) do_step2`

(*Coalesce, no biased selection*)
val aux_pref_def = Define`
  aux_pref prefs (v:num) (ls:num list) (col:num num_map) =
  case lookup v prefs of
    NONE => NONE
  | SOME u =>
    case lookup u col of
      NONE => NONE (*Should never occur if coalesces are properly done*)
    | SOME c => if MEM c ls then SOME c else NONE`

(*For the naive algorithm, we now maintain an sptree of
  lists of edges
  Note: the naive method is actually able to take advantage of
  the full range of priorities

  This implements biased selection
*)

val pri_move_insert_def = Define`
  pri_move_insert p x y acc =
  case lookup x acc of
    NONE =>
      insert x [(p,y)] acc
  | SOME ls =>
      insert x ((p,y)::ls) acc`

val undir_move_insert_def = Define`
  undir_move_insert p x y acc =
    pri_move_insert p x y (pri_move_insert p y x acc)`

val moves_to_sp_def = Define`
  (moves_to_sp [] acc = acc) ∧
  (moves_to_sp (move::xs) acc =
    let (p,x,y) = move in
    moves_to_sp xs (undir_move_insert p x y acc))`

(*Do a consistency sort after setting up the sptree of moves*)
val resort_moves_def = Define`
  resort_moves acc =
  let ts = toAList acc in
  let sort_ts = MAP (λv,ls. v, QSORT (λp:num,x p',x'. p>p') ls) ts in
    fromAList sort_ts`

(*EVAL``resort_moves (moves_to_sp [(1,2,3);(6,3,4);(2,2,4);(5,3,1)] LN)``*)

val first_match_col_def = Define`
  (first_match_col ls col [] = NONE) ∧
  (first_match_col ls col (x::xs) =
    let (p,x) = x in
    case lookup x col of
      NONE => first_match_col ls col xs
    | SOME c => if MEM c ls then SOME c else first_match_col ls col xs)`

val move_pref_def = Define`
  move_pref prefs (v:num) (ls:num list) (col:num num_map) =
  case lookup v prefs of
    NONE => NONE
  | SOME es =>
      first_match_col ls col es`

(*Combine coalescing with biased selector
  This should be used for Briggs, and possibly for IRC as well
  It makes IRC slightly more costly in the colouring phase
*)
val aux_move_pref_def = Define`
  aux_move_pref cprefs mprefs (v:num) (ls:num list) (col:num num_map) =
  case aux_pref cprefs v ls col of
    NONE =>
      move_pref mprefs v ls col
  | SOME c => SOME c`

(*Extract a colouring function from the generated sptree*)
val total_colour_def = Define`
  total_colour col =
    (λx. case lookup x col of NONE => x | SOME x => x)`

(*alg chooses the allocator to use in the first phase
  0: Naive allocator + biased selection
  1: Briggs allocator + coalesce&biased selection
  2: IRC allocator with coalesce select
  ≥3: IRC allocator + coalesce&biased selection


  The second phase is unaffected (for now?)
*)
val briggs_has_work_def = Define`
  briggs_has_work =
  do
    clock <- get_clock;
    avail_moves <- get_avail_moves;
    avail_moves_pri <- get_avail_moves_pri;
    return ((clock > 0) ∧ (avail_moves ≠ [] ∨ avail_moves_pri ≠ []))
  od`

val do_briggs_step_def = Define`
  do_briggs_step =
  do
    dec_clock;
    optx <- coalesce;
    (case optx of
      NONE => return ()
    | SOME x => push_stack x)
  od`

val briggs_coalesce_def = Define`
  briggs_coalesce =
  do
    MWHILE briggs_has_work do_briggs_step;
    set_move_rel LN;
    set_unavail_moves []
  od`

val maybe_flip_def = Define`
  maybe_flip move =
  let (p,x:num,y:num) = move in
  (if is_phy_var x then (p,x,y) else (p,y,x))`

val reg_alloc_def =  Define`
  reg_alloc (alg:num) G k moves =
  (*Rotate all the moves so that if there is a phy_var
    then it always appears on the left*)
  let moves = MAP maybe_flip moves in
  (*First phase*)
  let s =
  (if alg =
    0 then init_ra_state G k [] (*Don't do any coalescing*)
  else if alg =
    1 then (let ((),s) = briggs_coalesce (init_ra_state G k moves) in s)
  else if alg =
    2 then init_ra_state G k moves
  else init_ra_state G k moves) in
  let ((),s) = rpt_do_step s in
  let pref =
  (if alg =
    0 then move_pref (resort_moves (moves_to_sp moves LN))
  else if alg =
    1 then aux_move_pref s.coalesced (resort_moves (moves_to_sp moves LN))
  else if alg =
    2 then aux_pref s.coalesced
  else aux_move_pref s.coalesced (resort_moves(moves_to_sp moves LN))) in
  let (col,ls) = alloc_colouring s.graph k pref s.stack in
  (*Second phase is much easier because we do not have a fixed number of
    colours*)
  (*I think using s.graph here is fine because any coalesced nodes are
  necessarily colourable under both conditions.
  We are really only concerned when spilled nodes get coalesced
  It makes the proof easier -- 1 less assum on rpt_do_step*)
  let (G,spills,coalesce_map) = full_coalesce s.graph k moves ls in
  let s = sec_ra_state G k spills coalesce_map in
  let ((),s) = rpt_do_step2 s in
  let col = spill_colouring G k coalesce_map s.stack col in
  (*NOTE:
    This second step is not necessary but nice for proof as usual
    Notice that it does NOT need to use the coalescing_map colour oracle
    *)
  let col = spill_colouring G k LN ls col in
    col`
(*End reg alloc def*)

(*Start reg_alloc proofs
  We need to show 2 things:
  1) The total colouring generated is satisfactory
  2) The total colouring generated is conventional
*)

(*Property of an undirected irreflexive (simple) graph*)
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

val aux_pref_satisfactory = prove(``
  ∀prefs.
  satisfactory_pref (aux_pref prefs)``,
  fs[satisfactory_pref_def,aux_pref_def,LET_THM]>>rw[]>>
  EVERY_CASE_TAC>>
  Cases_on`ls`>>fs[]>>
  metis_tac[])

val first_match_col_mem = prove(``
  ∀ls.
  first_match_col cand col ls = SOME x
  ⇒ MEM x cand``,
  Induct>>rw[first_match_col_def]>>
  Cases_on`h`>>fs[first_match_col_def,LET_THM]>>
  EVERY_CASE_TAC>>rfs[])

val move_pref_satisfactory = prove(``
  ∀moves.
  satisfactory_pref (move_pref moves)``,
  fs[satisfactory_pref_def,move_pref_def,LET_THM]>>rw[]>>
  EVERY_CASE_TAC>>Cases_on`ls`>>fs[]>>
  imp_res_tac first_match_col_mem>>
  fs[])

val aux_move_pref_satisfactory = prove(``
  ∀prefs moves.
  satisfactory_pref (aux_move_pref prefs moves)``,
  fs[satisfactory_pref_def,aux_move_pref_def,LET_THM]>>rw[]>>
  EVERY_CASE_TAC>>
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
  Induct>>fs[alloc_colouring_aux,assign_colour_def]>>rw[]>>fs[LET_THM]>>
  Cases_on`x = h`>>fs[]>>rfs[]
  >-
    metis_tac[]
  >>
  EVERY_CASE_TAC>>fs[]>>TRY(metis_tac[])>>
  res_tac>>fs[lookup_insert])

val alloc_colouring_aux_never_overwrites_spill = prove(``
  ∀xs spill col spill' col'.
  MEM x spill ∧
  alloc_colouring_aux G k prefs xs col spill = (col',spill')
  ⇒
  MEM x spill'``,
  Induct>>fs[alloc_colouring_aux,assign_colour_def]>>rw[]>>fs[LET_THM]>>
  EVERY_CASE_TAC>>fs[]>>
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
  Induct_on`ls`>>fs[alloc_colouring_aux,assign_colour_def,LET_THM]>>rw[]>>
  EVERY_CASE_TAC>>fs[]>>
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

(*Domains of the colouring and spills are disjoin*)
val alloc_colouring_aux_domain_1 = prove(``
  ∀G k prefs ls col spill col' spill'.
  domain col ∩ set spill = {} ∧
  alloc_colouring_aux G k prefs ls col spill = (col',spill')
  ⇒
  domain col' ∩ set spill' = {}``,
  Induct_on`ls`>>fs[alloc_colouring_aux,LET_THM,assign_colour_def]>>rw[]
  >-(EVERY_CASE_TAC>>fs[]>>metis_tac[])
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
      (FULL_CASE_TAC>>fs[]
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
  Induct_on`ls`>>reverse (rw[alloc_colouring_aux,UNCURRY,LET_THM])>>fs[]
  >- metis_tac[]
  >>
  fs[assign_colour_def,LET_THM]>>EVERY_CASE_TAC>>
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
  EVERY_CASE_TAC>>
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
  Induct_on`ls`>>rw[alloc_colouring_aux,LET_THM]
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
  rw[assign_colour_def]>>EVERY_CASE_TAC>>fs[LET_THM]>>
  EVERY_CASE_TAC>>fs[]>>
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
  Induct_on`ls`>>rw[alloc_colouring_aux,LET_THM]>>
  Cases_on`assign_colour G k prefs h col spill'`>>fs[]>>
  metis_tac[assign_colour_reverse])

(*Everything appearing in the spills was already in G*)
val alloc_colouring_aux_domain_5 = prove(``
  ∀G:sp_graph k prefs ls col spill col' spill'.
  alloc_colouring_aux G k prefs ls col spill = (col',spill')
  ⇒
  ∀x. MEM x spill' ⇒
  x ∈ domain G ∨ MEM x spill``,
  Induct_on`ls`>>rw[alloc_colouring_aux,LET_THM]>>
  Cases_on`assign_colour G k prefs h col spill'`>>
  fs[]>>
  res_tac>>
  fs[assign_colour_def]>>
  EVERY_CASE_TAC>>fs[LET_THM]>>
  EVERY_CASE_TAC>>fs[]>>
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
  EVERY_CASE_TAC>>fs[LET_THM]>>
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
  Induct>>rw[option_filter_def]>>EVERY_CASE_TAC>>fs[])

val assign_colour2_satisfactory = prove(``
  undir_graph G ∧
  partial_colouring_satisfactory col G ⇒
  partial_colouring_satisfactory (assign_colour2 G k prefs h col) G``,
  rw[assign_colour2_def]>>
  fs[LET_THM]>>
  EVERY_CASE_TAC>>fs[]>>
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
  EVERY_CASE_TAC>>fs[]>>
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
  EVERY_CASE_TAC>>fs[]>>
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
    EVERY_CASE_TAC>>fs[]
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
      fs[assign_colour2_def]>>EVERY_CASE_TAC>>
      fs[LET_THM]>>
      metis_tac[])

val assign_colour2_reverse = prove(``
  ∀G:sp_graph k prefs h col col'.
  assign_colour2 G k prefs h col = col'
  ⇒
  ∀x. x ≠ h ⇒
  (x ∈ domain col' ⇒ x ∈ domain col)``,
  rw[assign_colour2_def]>>EVERY_CASE_TAC>>fs[LET_THM]>>
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
  EVERY_CASE_TAC>>fs[]>>
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
  rfs[]>>FULL_CASE_TAC>>
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
  EVERY_CASE_TAC>>fs[domain_insert,domain_lookup,lookup_insert]>>
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
    (EVERY_CASE_TAC>>fs[undir_graph_def,lookup_insert]>>
    rw[]>>fs[]>>FULL_CASE_TAC>>
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
    EVERY_CASE_TAC>>unabbrev_all_tac>>
    fs[domain_insert,SUBSET_DEF,lookup_g_def,lookup_insert,undir_graph_def
      ,partial_colouring_satisfactory_def,domain_empty]>>
    rw[]>>fs[]>- (fs[EXTENSION]>>metis_tac[]) 
    >-
    (FULL_CASE_TAC>>
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
    fs[dir_g_insert_def,LET_THM]>>EVERY_CASE_TAC>>
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
  Induct_on`ls`>-fs[full_coalesce_aux,LET_THM,is_subgraph_edges_def]>>
  ntac 4 strip_tac>>
  PairCases_on`h`>>
  fs[full_coalesce_aux,LET_THM]>>
  IF_CASES_TAC>-
    (fs[]>>metis_tac[])>>
  fs[]>>EVERY_CASE_TAC>>fs[]>>
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
    EVERY_CASE_TAC>>fsm[]>>
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
    EVERY_CASE_TAC>>fsm[]>>
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
  rw[Abbr`sopt`]>>fs[fetch "-" "ra_state_nchotomy"]

(*Simplify neverchanges the graph*)
val simplify_graph = prove(``
  ∀s G s' opt.
    simplify s = (opt,s') ⇒
    s'.graph = s.graph ∧
    s'.clock = s.clock``,
  rw[]>>
  fsm[simplify_def,get_simp_worklist_def]>>
  Cases_on`s.simp_worklist`>>fsm[set_simp_worklist_def]>>
  rw[]>>EVERY_CASE_TAC>>
  fsm[dec_deg_def,get_graph_def]>>rw[]>>
  EVERY_CASE_TAC>>
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
  rw[]>>EVERY_CASE_TAC>>
  fsm[dec_deg_def,get_graph_def]>>rw[]>>
  EVERY_CASE_TAC>>
  fsm[unspill_def,get_spill_worklist_def,get_degs_def,get_colours_def,get_move_rel_def,LET_THM,add_simp_worklist_def,set_freeze_worklist_def]>>
  EVERY_CASE_TAC>>fs[]>>
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
  rw[]>>EVERY_CASE_TAC>>
  fsm[dec_deg_def,get_graph_def]>>rw[]>>
  EVERY_CASE_TAC>>
  fsm[unspill_def,get_spill_worklist_def,get_degs_def,get_colours_def,get_move_rel_def,LET_THM]>>
  ntac 2 (pop_assum mp_tac)>>
  qpat_abbrev_tac`A = max_non_coalesced B C D E G`>>
  Cases_on`A`>>fs[]>>
  TRY(FULL_CASE_TAC)>>fs[]>>
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
  EVERY_CASE_TAC>>
  fsm[set_deg_def,dec_one_def,get_deg_def]>>EVERY_CASE_TAC>>
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
  EVERY_CASE_TAC>>fsm[set_deg_def,dec_one_def,get_deg_def]>>
  EVERY_CASE_TAC>>fs[]>>
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
  EVERY_CASE_TAC>>fs[]>>
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
  EVERY_CASE_TAC>>fs[]>>
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
  EVERY_CASE_TAC>>fs[]>>
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
  EVERY_CASE_TAC>>
  fsm[set_avail_moves_pri_def,set_avail_moves_def,add_unavail_moves_def]>>
  EVERY_CASE_TAC>>fs[]>>
  EVERY_CASE_TAC>>fs[]>>
  EVERY_CASE_TAC>>fs[]>-
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
  EVERY_CASE_TAC>>
  fsm[set_avail_moves_pri_def,set_avail_moves_def,add_unavail_moves_def]>>
  EVERY_CASE_TAC>>fs[]>>
  EVERY_CASE_TAC>>fs[]>>
  EVERY_CASE_TAC>>fs[]>-
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
  rw[]>>fsm[do_step2_def,dec_clock_def,full_simplify_def,get_simp_worklist_def,get_degs_def]>>FULL_CASE_TAC>>
  fsm[dec_deg_def,set_simp_worklist_def,get_graph_def,push_stack_def]>>
  TRY(FULL_CASE_TAC)>>fs[]>>
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
  rpt strip_tac>>fs[reg_alloc_def]>>LET_ELIM_TAC>>
  `satisfactory_pref pref` by
    (EVERY_CASE_TAC>>fs[Abbr`pref`,aux_pref_satisfactory,move_pref_satisfactory,aux_move_pref_satisfactory])>>
  `undir_graph s''.graph ∧ is_subgraph_edges G s''.graph` by
    (EVERY_CASE_TAC>>fs[]>>
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
  LET_ELIM_TAC>>
  rfs[LET_THM]>>
  `undir_graph s''.graph ∧ is_subgraph_edges G s''.graph` by
    (EVERY_CASE_TAC>>fs[]>>
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
    (EVERY_CASE_TAC>>fs[Abbr`pref`,aux_pref_satisfactory,move_pref_satisfactory,aux_move_pref_satisfactory])>>
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
  FULL_CASE_TAC>>fs[domain_lookup]))

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

val _ = export_theory()
