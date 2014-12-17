open HolKernel Parse boolLib bossLib miscLib
open listTheory sptreeTheory pred_setTheory pairTheory rich_listTheory alistTheory
open BasicProvers
open word_liveTheory word_langTheory
open sortingTheory
open monadsyntax state_transformerTheory

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

(*TODO: maybe insert an empty tree in the list*)
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

(*Create a list of preferences from input program
  Some of these will be invalid preferences (e.g. 0<-2) *)

val get_prefs_def = Define`
  (get_prefs (Move ls) acc = ls ++ acc) ∧ 
  (get_prefs (Seq s1 s2) acc =
    get_prefs s1 (get_prefs s2 acc)) ∧
  (get_prefs (If e1 num e2 e3) acc =
    get_prefs e1 (get_prefs e2 (get_prefs e3 acc))) ∧
  (get_prefs (Call (SOME (v,cutset,ret_handler)) dest args h) acc =
    case h of 
      NONE => get_prefs ret_handler acc
    | SOME (v,prog) => get_prefs prog (get_prefs ret_handler acc)) ∧ 
  (get_prefs prog acc = acc)`

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
  rw[is_stack_var_def,is_phy_var_def,is_alloc_var_def,EQ_IMP_THM]
  \\ `n MOD 2 = (n MOD 4) MOD 2` by
   (ONCE_REWRITE_TAC [GSYM (EVAL ``2*2:num``)]
    \\ fs [arithmeticTheory.MOD_MULT_MOD])
  \\ fs []
  \\ `n MOD 4 < 4` by fs []
  \\ IMP_RES_TAC (DECIDE
       ``n < 4 ==> (n = 0) \/ (n = 1) \/ (n = 2) \/ (n = 3:num)``)
  \\ fs []);

(*Final coloring conventions*)
val coloring_conventional_def = Define`
  coloring_conventional (G:sp_graph) k col ⇔
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
Start coloring algorithms
First phase (alloc_coloring): Produces a bounded coloring (< 2k)
Second phase (spill_coloring): Produces unbounded coloring (≥ 2k)
---*)

(*Define the first coloring step:
  Takes arguments:
  G = spgraph (possibly augmented e.g. in coalescing),
  k = number of registers to use,
  prefs = num-> num list -> num (selects a color from the list),
  ls = heuristic order to color vertices,
  Result: a num sptree where looking up a vertex gives its coloring
      and a num list of spilled vertices
  TODO: Decide if this should be monadic
*)

(*Deletes unavailable colors by looking up the current coloring function*)
(*This terminates early when k becomes empty so that we do not need to lookup every single neighbor... maybe the other way is equally efficient?*)
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

(*EVAL``remove_colors(list_insert [1;2;3] [1;1;1] LN) [1;2;3;4] [1;2;3;4]``*)

(*Assigns a color or spills
  If assigning a color, use prefs to choose the color
  Constrain prefs to always choose from the list of available colors

  Returns a new coloring and spill list
*)
(*NOTE: If we used redundancy in the graph representations,
 then we would use adj lists here*)
(*TODO: Make monadic on the last 2 arguments*)

val assign_color_def = Define`
  assign_color G k prefs v col spills =
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
      let k = remove_colors col xs k in
      case k of
        [] => 
        (*Spill*) (col,v::spills)
      | xs => 
        (*Choose a preferred color*) (insert v (prefs v xs col) col,spills)
    else
      (*Spill if it was not an alloc_var*)
      (col,v::spills)`

(*Auxiliary that colors vertices in the order of the input list*)
(*TODO: Make monadic on the last 2 arguments*)
val alloc_coloring_aux = Define`
  (alloc_coloring_aux G k prefs [] col spills = (col,spills)) ∧
  (alloc_coloring_aux G k prefs (x::xs) col spills =
    let (col,spills) = assign_color G k prefs x col spills in
      alloc_coloring_aux G k prefs xs col spills)`

val id_color_def = Define`
  id_color ls = FOLDR (λx y. insert x x y) LN ls`

(*First coloring step:
  End result should be a coloring that sends 
  phy_vars to phy_vars,
  alloc_vars which were properly allocated to phy_vars
  Everything else should be in the resulting spill list
  (unallocated alloc_vars and stack_vars)
*)
val alloc_coloring_def = Define`
  alloc_coloring (G:sp_graph) k prefs ls =
    (*Setting up*)
    let vertices = MAP FST (toAList G) in
    let (phy_var,others) = PARTITION is_phy_var vertices in
    (*Everything that cannot be allocated is identity colored*)
    let col = id_color phy_var in
    let colors = GENLIST (λx:num.2*x) k in
    (*First do the ones given in the input list*)
    let (col,spills) = alloc_coloring_aux G colors prefs ls col [] in
    (*Do the rest -- this automatically spills everything is_stack_var
      as well*)
    alloc_coloring_aux G colors prefs others col spills`

(*Unbounded coloring
TODO: Add the preference function here
-- Need to think about exactly what type it should take
-- The easiest one will be a single lookup that tests for coloring ok-ness
*)
val unbound_colors_def = Define `
  (unbound_colors col [] = col) ∧
  (unbound_colors col ((x:num)::xs) = 
    if col < x then 
      col 
    else if x = col then
      unbound_colors (col+2) xs 
    else
      unbound_colors col xs)`
      
(*EVAL``unbound_colors 2 [2;4;8]``*)

(*Probably already in HOL
  TODO: Maybe use this in the other coloring def as well?
*)
val option_filter_def = Define`
  option_filter ls = 
  MAP THE (FILTER IS_SOME ls)`

val assign_color2_def = Define`
  assign_color2 G k prefs v col =
  case lookup v col of
    SOME x => col 
  | NONE =>
  case lookup v G of
    NONE => col (*Vertex wasn't even in the graph -- ignore*)
  | SOME x =>
    let xs = MAP FST (toAList x) in
    (*Get all the nightbor colors*)
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
      NONE => unbound_colors (2*k) (QSORT (λx y. x≤y) cols)
    | SOME c => c in
      insert v c col` 

(*ls is a spill list,
  prefs is a coalescing oracle
*)
val spill_coloring_def = Define`
  (spill_coloring (G:sp_graph) k prefs [] col = col) ∧
  (spill_coloring G k prefs (x::xs) col =
    let col = assign_color2 G k prefs x col in 
    spill_coloring G k prefs xs col)`

(*End coloring definitions*)

(*Define register allocation*)

val _ = Hol_datatype `
  ra_state = <| graph : sp_graph;
                colors : num;
                degs : num num_map;(*maybe should become a 2 step O(1)lookup*)
                simp_worklist : num list;
                spill_worklist : num list;
                stack : num list |>`;
                (*TODO: the other work lists
                coalesced : num num_map;*)
(*val _ = temp_overload_on ("monad_bind", ``BIND``);
val _ = temp_overload_on ("return", ``id_return``);*)

(*Parameterized by P because we only count certain types of adjacency in each coloring step*)
val count_degrees_def = Define`
  count_degrees P (e:num_set) =
  LENGTH (FILTER P (MAP FST (toAList e)))`

(*Initialize state for the first phase*)
val init_ra_state_def = Define`
  (init_ra_state (G:sp_graph) (k:num) = 
  let vertices = FILTER is_alloc_var (MAP FST (toAList G)) in
  let vdegs = MAP (λv. v,count_degrees (λx. ¬(is_stack_var x)) 
              (THE(lookup v G))) vertices in
  let tdegs = fromAList vdegs in
  let (simp,spill) = PARTITION (λx,(y:num). y<k) vdegs in
  <|graph := G ; colors := k ; degs := tdegs; 
    simp_worklist := MAP FST simp ;
    spill_worklist := MAP FST spill;
    stack:=[]|>)`

val get_stack_def = Define`
  get_stack = \s. (return s.stack) s`

val get_graph_def = Define`
  get_graph = \s. (return s.graph) s`

val push_stack_def = Define`
  push_stack v =
    λs. ((), s with stack:= v::s.stack)`

val get_degs_def = Define`
  get_degs = \s. (return s.degs) s` 

val get_deg_def = Define`
  get_deg v = \s. (return (lookup v s.degs)) s` 

val set_deg_def = Define`
  set_deg k v = \s. ((), s with degs := insert k v s.degs)`

val add_simp_worklist_def = Define`
  add_simp_worklist ls = \s. ((), s with simp_worklist := ls++s.simp_worklist )`

val set_spill_worklist_def = Define`
  set_spill_worklist ls = \s. ((), s with spill_worklist := ls)`

val get_spill_worklist_def = Define`
  get_spill_worklist = \s. return s.spill_worklist s`

val get_simp_worklist_def = Define`
  get_simp_worklist = \s. return s.simp_worklist s`

val set_simp_worklist_def = Define`
  set_simp_worklist ls = \s. ((), s with simp_worklist := ls)`

val get_colors_def = Define`
  get_colors = \s. return s.colors s`

val dec_deg_def = Define`
  dec_deg v =
  do
    g <- get_graph ;
    case lookup v g of
    | NONE => return ()
    | SOME es =>
      let edges = MAP FST(toAList es) in
        FOREACH (edges,
          (λv. 
            do
              optd <- get_deg v ;
              case optd of
              | NONE => return ()
              | SOME (d:num) => set_deg v  (d-1)
            od) )
  od`

(*Move vertiecs of suitable degree back*)
val unspill_def = Define`
  unspill = 
  do
    swl <- get_spill_worklist ;
    degs <- get_degs ;
    colors <- get_colors ;
    let (ltk,gtk) = PARTITION 
      (λv. case lookup v degs of 
          NONE => F
        | SOME x => x < colors) swl in
      do
        add_simp_worklist ltk ;
        set_spill_worklist gtk
      od
  od`
 
val simplify_def = Define`
  simplify =
  do
    simps <- get_simp_worklist;
    case simps of
      [] => return NONE
    | (x::xs) =>
      do
        set_simp_worklist xs;
        dec_deg x;
        unspill;
        return (SOME x)
      od
  od`

val spill_def = Define`
  spill =
  do
    spills <- get_spill_worklist;
    case spills of
      [] => return NONE
    | (x::xs) =>
      do
        set_spill_worklist xs;
        dec_deg x;
        unspill;
        return (SOME x)
      od
  od`

val do_step_def = Define`
  do_step =
  do
    optx <- simplify;
    case optx of 
      NONE =>
        do
          optx <- spill;
          (case optx of
            NONE =>
              return ()
          | SOME x =>
              push_stack x)
        od
    | SOME x =>
        push_stack x
  od`

val has_work_def = Define`
  has_work = 
  do
    simp <- get_simp_worklist;
    spill <- get_spill_worklist;
    return (simp ≠ [] ∨ spill ≠ [])
  od`

val rpt_do_step_def = Define`
  rpt_do_step =
  MWHILE (has_work) do_step`  

(*Initialize state for the second phase, here we are given a list of
  vertices to consider
  and the map corresponding to already coalesced nodes
  *)
val sec_ra_state_def = Define`
  (sec_ra_state (G:sp_graph) (k:num) vertices coalesce_map = 
  (*In this instance, we care about the degree w.r.t. to other spilled
    temporaries or phy variables ≥ 2*k*)
  let vdegs = MAP (λv. v,count_degrees 
  (*The first check corresponds to the pre-allocated spill variables*)
    (λx. (is_phy_var x ∧ x ≥ 2*k) ∨ MEM x vertices)
              (THE(lookup v G))) vertices in
  let tdegs = fromAList vdegs in
  let st = MAP FST (toAList coalesce_map) in
  <|graph := G ; colors := k ; degs := tdegs; 
    simp_worklist := vertices;
    spill_worklist := [];
    stack:=st|>)`

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

(*TODO:This is the simplified coalesce in the second phase which does 
  not need to update the degrees in the graph
  It simply merges y into x
  Returns the new graph and a coalescing function
  *)
val pair_rename_def = Define`
  pair_rename x y (a,b) =
    let a = if a=y then x else a in
    let b = if b=y then x else b in
      a,b`
       
val full_coalesce_aux = Define`
  (full_coalesce_aux G [] = (G,LN)) ∧ 
  (full_coalesce_aux G ((x,y)::xs) =
    (*Edge List for y*)
    if lookup_g x y G 
    then full_coalesce_aux G xs 
    else  
    let e = THE (lookup y G) in
      (*For each adjacent vertex to y, make it adjacent to x*)
      let edges = MAP FST (toAList e) in
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
      let (G,t) = full_coalesce_aux G xs in 
        (G,insert y x t))`
      
(*Given a list of moves and spills,
  The coalesceable moves are those spilled and not already clashing
  This is tricky -- the graph should be ideally edited monadically
  *)
val full_coalesce_def = Define`
  full_coalesce G moves spills =
  let coalesceable = 
    FILTER (λx,y. MEM x spills ∧ MEM y spills) moves in
  (*Maybe more efficient impl possible*)
  let (G,coalesce_map) = 
    full_coalesce_aux G coalesceable in
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
    optx <- full_simplify;
    case optx of
      NONE => return ()
    | SOME x => push_stack x
  od`

val rpt_do_step_2_def = Define`
  rpt_do_step2 =
    MWHILE (has_work) do_step2`  

(*No preferences until we get to coalescing*) 
val aux_pref_def = Define`
  aux_pref (h:num) (ls:num list) (col:num num_map) = HD ls`

(*Extract a coloring function from the generated sptree*)
val total_color_def = Define`
  total_color col =
    (λx. case lookup x col of NONE => x | SOME x => x)`

(*TODO: 
  Need to use the state's graph instead of G when calling the coloring
  if we add coalescing
  Currently, the graph does not actually change in the first phase*)
val reg_alloc_def =  Define`
  reg_alloc G k moves =
  (*First phase*)
  let s = init_ra_state G k in
  let ((),s) = rpt_do_step s in
  let (col,ls) = alloc_coloring G k aux_pref s.stack in
  (*Second phase is much easier because we do not have a fixed number of 
    colors*)
  let (G,spills,coalesce_map) = full_coalesce G moves ls in
  let s = sec_ra_state G k spills coalesce_map in
  let ((),s) = rpt_do_step2 s in
  let col = spill_coloring G k coalesce_map s.stack col in
  (*NOTE:
    The second step is not necessary but nice for proof as usual
    Notice that it does not use the coalescing_map color oracle
    *)
  let col = spill_coloring G k LN ls col in
    col`

(*
open sptreeSyntax
sptreeSyntax.temp_add_sptree_printer();
sptreeSyntax.remove_sptree_printer();

val _ = computeLib.add_funs[MWHILE_DEF]
val rhsThm = rhs o concl;

val _ = Globals.max_print_depth := ~1

val prog = ``
Seq
(Move [15,19])
(Seq
(Move [23,15])
(Seq
(Move [7,11;13,17;19,23])
(Seq (Move [1,2;3,4;5,6])
  (Call (SOME (3, list_insert [1;3;5;7;9] [();();();();()] LN,Skip)) (SOME 400) [7;9] NONE)
  )))``

val prog_prefs = rhsThm (EVAL ``get_prefs ^(prog) []``)

val init_state = rhsThm (EVAL``(init_ra_state (get_spg ^(prog) LN) 3)``)

val st = rhsThm (EVAL ``SND (rpt_do_step ^(init_state))``)

val G = rhsThm (EVAL ``^(st).graph``)
val k = rhsThm (EVAL ``^(st).colors``)
val ls = rhsThm (EVAL ``^(st).stack``)
val prefs = ``λ(h:num) (ls:num list) (col:num num_map). HD ls``

val col = rhsThm (EVAL ``(SND(alloc_coloring ^(G) ^(k) ^(prefs) ^(ls)))``)

val st2= rhsThm (EVAL ``sec_ra_state ^(G) ^(k) ^(col) ``)

val it = EVAL ``rpt_do_step2 ^(st2)``

val ra = EVAL ``reg_alloc (get_spg ^(prog) LN) 3 ^(prog_prefs)``;

(*Read a large, generated graph*)

val graph = rhsThm(
EVAL``

``)

val init_state = rhsThm (EVAL``init_ra_state ^(graph) 6``)
val t1 = Time.now();
val p1 = EVAL ``reg_alloc ^(graph) 32``;
val t2 = Time.now() -t1;


*)

(*End reg alloc def*)


(*Start reg_alloc proofs
  We need to show 2 things:
  1) The total coloring generated is satisfactory
  2) The total coloring generated is conventional
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

(*Property of preference function, it only chooses a color it is given*)
val satisfactory_pref_def = Define`
  satisfactory_pref prefs ⇔
    ∀h ls col v. ls ≠ [] ∧ prefs h ls col = v ⇒ MEM v ls`

val aux_pref_satisfactory = prove(``
  satisfactory_pref aux_pref``,
  fs[satisfactory_pref_def,aux_pref_def]>>
  Cases_on`ls`>>fs
  [])

val id_color_lemma = prove(``
  ∀ls.
  let t = id_color ls in
  domain t = set ls ∧
  ∀x. (MEM x ls ⇒ lookup x t = SOME x)``,
  Induct>>fs[id_color_def,LET_THM,lookup_insert]>>rw[])

(*alloc_coloring_aux never overwrites an old coloring*)
val alloc_coloring_aux_never_overwrites_col = prove(``
  ∀xs spill col spill' col'.
  lookup x col = SOME y ∧
  alloc_coloring_aux G k prefs xs col spill = (col',spill')
  ⇒
  lookup x col' = SOME y``,
  Induct>>fs[alloc_coloring_aux,assign_color_def]>>rw[]>>fs[LET_THM]>>
  Cases_on`x = h`>>fs[]>>rfs[]
  >-
    metis_tac[]
  >>
  EVERY_CASE_TAC>>fs[]>>TRY(metis_tac[])>>
  res_tac>>fs[lookup_insert])

val alloc_coloring_aux_never_overwrites_spill = prove(``
  ∀xs spill col spill' col'.
  MEM x spill ∧
  alloc_coloring_aux G k prefs xs col spill = (col',spill')
  ⇒
  MEM x spill'``,
  Induct>>fs[alloc_coloring_aux,assign_color_def]>>rw[]>>fs[LET_THM]>>
  EVERY_CASE_TAC>>fs[]>>
  TRY(`MEM x (h::spill')` by (fs[]>>NO_TAC))>>
  metis_tac[])

(*Coloring satisfactory but restricted to a partial coloring
  i.e. only talk about the subgraph induced by the vertices 
  in the domain of the coloring
*)
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

(*Coloring produced after each alloc_coloring_aux_step is
  partial_coloring_satisfactory*)
val alloc_coloring_aux_satisfactory = prove(``
  ∀G k prefs ls col spill.
  undir_graph G ∧
  satisfactory_pref prefs ∧
  partial_coloring_satisfactory col G
  ⇒
  let (col',spill') = alloc_coloring_aux G k prefs ls col spill in
    partial_coloring_satisfactory col' G``,
  Induct_on`ls`>>fs[alloc_coloring_aux,assign_color_def,LET_THM]>>rw[]>>
  EVERY_CASE_TAC>>fs[]>>
  first_x_assum(qspecl_then
    [`G`,`k`,`prefs`,`insert h (prefs h (h'::t) col) col`,`spill'`] mp_tac)>>
  discharge_hyps>>fs[]>>
  match_mp_tac partial_coloring_satisfactory_extend>>rw[]>>
  fs[domain_lookup]>>
  imp_res_tac remove_colors_removes>>
  fs[satisfactory_pref_def]>>
  first_x_assum(qspecl_then[`h`,`h'::t`,`col`] assume_tac)>>
  `MEM y (MAP FST (toAList x))` by
    fs[MEM_MAP,MEM_toAList,EXISTS_PROD,domain_lookup]>>
  rfs[]>>res_tac>>
  metis_tac[])

(*Domains of the coloring and spills are disjoin*)
val alloc_coloring_aux_domain_1 = prove(``
  ∀G k prefs ls col spill col' spill'.
  domain col ∩ set spill = {} ∧ 
  alloc_coloring_aux G k prefs ls col spill = (col',spill')
  ⇒
  domain col' ∩ set spill' = {}``,
  Induct_on`ls`>>fs[alloc_coloring_aux,LET_THM,assign_color_def]>>rw[]
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
val alloc_coloring_aux_domain_2 = prove(``
  ∀G k prefs ls col spill col' spill'.
  alloc_coloring_aux G k prefs ls col spill = (col',spill')
  ⇒
  ∀x. MEM x ls ∧ x ∈ domain G ⇒ 
    x ∈ domain col' ∨ MEM x spill'``,
  Induct_on`ls`>>reverse (rw[alloc_coloring_aux,UNCURRY,LET_THM])>>fs[]
  >- metis_tac[]
  >>
  fs[assign_color_def,LET_THM]>>EVERY_CASE_TAC>>
  imp_res_tac alloc_coloring_aux_never_overwrites_col>>
  imp_res_tac alloc_coloring_aux_never_overwrites_spill>>
  fs[domain_lookup]>>
  metis_tac[lookup_insert])

val assign_color_props = prove(``
  h ∉ domain col ∧
  ¬MEM h spill' ∧ 
  h ∈ domain G ∧ 
  (∀x. MEM x k ⇒ is_phy_var x) ∧
  domain col ∩ set spill' = {} ∧ 
  satisfactory_pref prefs 
  ⇒
  let (col',spill'') = assign_color G k prefs h col spill' in
    (if is_alloc_var h then 
      if h ∈ domain col' then
        spill'' = spill' ∧
        ∃y. col' = insert h y col ∧ is_phy_var y 
      else col = col' ∧ MEM h spill''
    else col = col' ∧ MEM h spill'') ∧
    domain col' ∩ set spill'' = {}``,
  rpt strip_tac>>
  fs[assign_color_def]>>
  `lookup h col = NONE` by 
    metis_tac[domain_lookup,optionTheory.option_CLAUSES]>>
  fs[domain_lookup]>>
  IF_CASES_TAC>>fs[LET_THM]>>
  qabbrev_tac `lss = MAP FST (toAList v)`>>
  Cases_on`remove_colors col lss k`>>fs[]>>
  imp_res_tac remove_colors_removes>>
  fs[satisfactory_pref_def]>>
  first_x_assum(qspecl_then[`h`,`h'::t`,`col`] assume_tac)>>rfs[]>>
  TRY(`h ∉ domain col` by fs[domain_lookup]>>
  fs[EXTENSION,INTER_DEF]>>metis_tac[]))

(*Conventions over the extension domain*)
val alloc_coloring_aux_domain_3 = prove(``
  ∀G:sp_graph k prefs ls col spill col' spill'.
  (∀x. MEM x k ⇒ is_phy_var x) ∧
  (domain col ∩ set spill = {}) ∧  
  (satisfactory_pref prefs) ∧ 
  alloc_coloring_aux G k prefs ls col spill = (col',spill')
  ⇒
  ∀x. MEM x ls ∧ x ∉ domain col ∧ ¬MEM x spill ∧ x ∈ domain G ⇒ 
    (if is_alloc_var x then 
      if x ∈ domain col' then
        ∃y. lookup x col' = SOME y ∧ is_phy_var y
      else MEM x spill'
    else MEM x spill')``,
  Induct_on`ls`>>rw[alloc_coloring_aux,LET_THM]
  >-
    (imp_res_tac assign_color_props>>fs[LET_THM]>>
    IF_CASES_TAC>>
    Cases_on`assign_color G k prefs h col spill'`>>fs[]>>
    Cases_on`h ∈ domain q`>>fs[]
    >-
      (fs[domain_lookup]>>
      metis_tac[lookup_insert,alloc_coloring_aux_never_overwrites_col])
    >>
    imp_res_tac alloc_coloring_aux_never_overwrites_spill>>
    imp_res_tac alloc_coloring_aux_domain_1>>
    `h ∉ domain col'` by 
        (fs[INTER_DEF,EXTENSION]>>
        metis_tac[])>>
    fs[])
  >>
    Cases_on`x=h`>>fs[]
    >-
    (imp_res_tac assign_color_props>>fs[LET_THM]>>
    IF_CASES_TAC>>
    Cases_on`assign_color G k prefs h col spill'`>>fs[]>>
    Cases_on`h ∈ domain q`>>fs[]
    >-
      (fs[domain_lookup]>>
      metis_tac[lookup_insert,alloc_coloring_aux_never_overwrites_col])
    >>
    imp_res_tac alloc_coloring_aux_never_overwrites_spill>>
    imp_res_tac alloc_coloring_aux_domain_1>>
    `h ∉ domain col'` by 
        (fs[INTER_DEF,EXTENSION]>>
        metis_tac[])>>
    fs[])
    >>
    fs[assign_color_def]>>
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
      Cases_on`remove_colors col(MAP FST (toAList x')) k`>>
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

(*If not the assigned color then it must have come from before*)
val assign_color_reverse = prove(``
  ∀G:sp_graph k prefs h col spill col' spill'.
  assign_color G k prefs h col spill = (col',spill')
  ⇒ 
  (∀x. x ≠ h ⇒ 
  (x ∈ domain col' ⇒ x ∈ domain col) ∧ 
  (MEM x spill' ⇒ MEM x spill))``,
  rw[assign_color_def]>>EVERY_CASE_TAC>>fs[LET_THM]>>
  EVERY_CASE_TAC>>fs[]>>
  qpat_assum `A = col'` (SUBST_ALL_TAC o SYM)>>
  fs[domain_insert]>>metis_tac[list_mem])
  
(*Not in the final state means it must have come from before*)
val alloc_coloring_aux_domain_4 = prove(``
  ∀G:sp_graph k prefs ls col spill col' spill'.
  alloc_coloring_aux G k prefs ls col spill = (col',spill')
  ⇒
  ∀x. ¬MEM x ls ⇒ 
  (x ∈ domain col' ⇒ x ∈ domain col) ∧ 
  (MEM x spill' ⇒ MEM x spill)``,
  Induct_on`ls`>>rw[alloc_coloring_aux,LET_THM]>>
  Cases_on`assign_color G k prefs h col spill'`>>fs[]>>
  metis_tac[assign_color_reverse])

(*Everything appearing in the spills was already in G*)
val alloc_coloring_aux_domain_5 = prove(``
  ∀G:sp_graph k prefs ls col spill col' spill'.
  alloc_coloring_aux G k prefs ls col spill = (col',spill')
  ⇒
  ∀x. MEM x spill' ⇒ 
  x ∈ domain G ∨ MEM x spill``,
  Induct_on`ls`>>rw[alloc_coloring_aux,LET_THM]>>
  Cases_on`assign_color G k prefs h col spill'`>>
  fs[]>>
  res_tac>>
  fs[assign_color_def]>>
  EVERY_CASE_TAC>>fs[LET_THM]>>
  EVERY_CASE_TAC>>fs[]>>
  qpat_assum`A=r` (SUBST_ALL_TAC o SYM)>>
  fs[domain_lookup])

val id_color_always_sat = prove(``
  undir_graph G ⇒ 
  partial_coloring_satisfactory (id_color ls) G``,
  Q.ISPEC_THEN `ls` assume_tac id_color_lemma>>
  rw[undir_graph_def,partial_coloring_satisfactory_def]>>
  fs[LET_THM]>>
  qsuff_tac `v ≠ v'`
  >-
    (`MEM v ls ∧ MEM v' ls` by metis_tac[EXTENSION]>>
    res_tac>>
    fs[])
  >>
    first_x_assum(qspec_then `v` assume_tac)>>
    fs[domain_lookup]>>rfs[]>>
    metis_tac[])

(*The first coloring should produce a partial coloring such that:
  Phy vars are mapped to themselves
  Stack vars are all in spills
  Alloc vars are either spilled (exclusive)OR in the coloring 
*)
val alloc_coloring_success = prove(``
  undir_graph G ∧ satisfactory_pref prefs ⇒ 
  let (col,spills) = alloc_coloring G k prefs ls in
  partial_coloring_satisfactory col G ∧
  domain col ∩ set spills = {} ∧ 
  ∀x. x ∈ domain G ⇒
    if is_phy_var x then lookup x col = SOME x
    else if is_stack_var x then MEM x spills
    else (*is_alloc_var x*)
      if x ∈ domain col then
        ∃y. lookup x col = SOME y ∧ is_phy_var y
      else MEM x spills``,
  fs[alloc_coloring_def]>>rw[]
  >-
    (imp_res_tac alloc_coloring_aux_satisfactory>>
    ntac 2 (pop_assum kall_tac)>>
    first_assum(qspec_then`col` mp_tac)>>
    discharge_hyps
    >-
      metis_tac[id_color_always_sat]
    >>
    strip_tac>>
    pop_assum(qspecl_then [`[]`,`ls`,`colors`] assume_tac)>>
    rfs[LET_THM]>>
    first_x_assum(qspec_then`col'` assume_tac)>>rfs[]>>
    pop_assum(qspecl_then [`spills`,`others`,`colors`] assume_tac)>>
    rfs[])
  >-
    (imp_res_tac alloc_coloring_aux_domain_1>>
    rfs[])
  >>
    imp_res_tac alloc_coloring_aux_domain_2>>
    `MEM x vertices` by 
      fs[Abbr`vertices`,MEM_toAList,MEM_MAP,EXISTS_PROD,domain_lookup]>>
    fs[PARTITION_DEF]>>
    Q.ISPECL_THEN [`is_phy_var`,`vertices`,`phy_var`,`others`,`[]:num list`
      ,`[]:num list`]assume_tac PARTs_HAVE_PROP>>
    Q.ISPECL_THEN [`is_phy_var`,`vertices`,`phy_var`,`others`,`[]:num list`
      ,`[]:num list`]assume_tac PART_MEM>>
    rfs[]>>
    `∀x. MEM x colors ⇒ is_phy_var x` by 
      (rw[Abbr`colors`,MEM_GENLIST,is_phy_var_def]>>
      `0<2:num` by DECIDE_TAC>>
      `(2:num)*x''=x''*2` by DECIDE_TAC>>
      metis_tac[arithmeticTheory.MOD_EQ_0])>>
    IF_CASES_TAC
    >-
      (`lookup x col = SOME x` by metis_tac[id_color_lemma]>>
      metis_tac[alloc_coloring_aux_never_overwrites_col])
    >>
    `x ∉ domain col` by (qspec_then `phy_var` assume_tac id_color_lemma>>
          rfs[LET_THM]>>metis_tac[])>>
    IF_CASES_TAC
    >-
      (`MEM x others` by metis_tac[]>>
      `¬is_alloc_var x` by metis_tac[convention_partitions]>>
      Q.SPECL_THEN [`G`,`colors`,`prefs`,`ls`,`col`,`[]`,`col'`,`spills`]
        assume_tac alloc_coloring_aux_domain_3>>rfs[]>>
      rw[]>>
      Cases_on`MEM x ls`>>fs[]
      >-
        (first_x_assum(qspec_then`x` mp_tac)>>fs[]>>
        metis_tac[alloc_coloring_aux_never_overwrites_spill])
      >>
        imp_res_tac alloc_coloring_aux_domain_4>>
        fs[]>>rfs[]>>
        imp_res_tac alloc_coloring_aux_domain_1>>
        Q.SPECL_THEN [`G`,`colors`,`prefs`,`others`,`col'`,`spills`
          ,`col''`,`spills'`] assume_tac alloc_coloring_aux_domain_3>>
        rfs[]>>metis_tac[])
    >>
      `is_alloc_var x ∧ MEM x others` by metis_tac[convention_partitions]>>
      Q.SPECL_THEN [`G`,`colors`,`prefs`,`ls`,`col`,`[]`,`col'`,`spills`]
        assume_tac alloc_coloring_aux_domain_3>>
      rfs[]>>
      Cases_on`MEM x ls`>>fs[]
      >-
        (first_x_assum(qspec_then`x` mp_tac)>>fs[]
        >>
        Cases_on`x ∈ domain col'`>>fs[]
        >- metis_tac[alloc_coloring_aux_never_overwrites_col]
        >>
        (*In spills so in spills'*)
        `MEM x spills'` by 
          metis_tac[alloc_coloring_aux_never_overwrites_spill]>>
        (*But we always kept everything disjoint*)
        imp_res_tac alloc_coloring_aux_domain_1>>
        fs[INTER_DEF,EXTENSION]>>rw[]>>
        metis_tac[])
      >>
        imp_res_tac alloc_coloring_aux_domain_4>>
        fs[]>>rfs[]>>
        imp_res_tac alloc_coloring_aux_domain_1>>
        Q.SPECL_THEN [`G`,`colors`,`prefs`,`others`,`col'`,`spills`
          ,`col''`,`spills'`] assume_tac alloc_coloring_aux_domain_3>>
        fs[]>>metis_tac[])

val alloc_coloring_success_2 = prove(``
  let (col,spills) = alloc_coloring G k prefs ls in
  ∀x. MEM x spills ⇒ x ∈ domain G``,
  fs[alloc_coloring_def]>>rw[]>>
  imp_res_tac alloc_coloring_aux_domain_5>>fs[])

val spill_coloring_never_overwrites = prove(``
  ∀ls col col'.
  lookup x col = SOME y ∧ 
  spill_coloring G k prefs ls col = col'
  ⇒ 
  lookup x col' = SOME y``,
  Induct>>fs[spill_coloring_def,assign_color2_def]>>rw[]>>
  Cases_on`x=h`>>fs[]>>rfs[]
  >-
    metis_tac[]
  >>
  EVERY_CASE_TAC>>fs[LET_THM]>>
  metis_tac[lookup_insert])

val spill_coloring_domain_subset = prove(``
  ∀ls col col'.
  domain col ⊆ domain (spill_coloring G k prefs ls col)``,
  rw[SUBSET_DEF]>>fs[domain_lookup]>>
  metis_tac[domain_lookup,spill_coloring_never_overwrites])

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
val unbound_colors_props = prove(``
  ∀col ls col'.
    is_phy_var col ∧
    SORTED (λx y.x≤y) ls ∧ 
    unbound_colors col ls = col'
    ⇒
    is_phy_var col' ∧ col' ≥ col ∧
    ¬MEM col' ls``,
  Induct_on`ls`>>rw[unbound_colors_def]>>
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
  
val assign_color2_satisfactory = prove(``
  undir_graph G ∧ 
  partial_coloring_satisfactory col G ⇒ 
  partial_coloring_satisfactory (assign_color2 G k prefs h col) G``,
  rw[assign_color2_def]>>
  fs[LET_THM]>>
  EVERY_CASE_TAC>>fs[]>>
  match_mp_tac (GEN_ALL partial_coloring_satisfactory_extend)>>rw[]>>
  fs[domain_lookup]>>
  TRY(
  qpat_abbrev_tac`lss = QSORT (λx:num y:num. x≤y)  B`>>
  SORTED_TAC>>
  `MEM v lss` by
    (unabbrev_all_tac>>
    fs[QSORT_MEM,option_filter_def,MEM_MAP,MEM_FILTER,EXISTS_PROD
      ,MEM_toAList,PULL_EXISTS]>>
    TRY(Q.EXISTS_TAC`y`>>fs[])>>
    HINT_EXISTS_TAC>>fs[])>>
  is_phy_var_tac>>
  metis_tac[unbound_colors_props])>>
  qpat_assum `¬A` mp_tac >>
  qpat_abbrev_tac`lss = option_filter (MAP (λx. lookup x col) A)` >>
  qsuff_tac `MEM v lss`>-metis_tac[]>>
  unabbrev_all_tac>>
  fs[option_filter_def,MEM_MAP,MEM_FILTER,EXISTS_PROD
    ,PULL_EXISTS,MEM_toAList]>>
  HINT_EXISTS_TAC>>fs[])

val assign_color2_conventional = prove(``
  v ∈ domain G ∧ 
  v ∉ domain col ∧ 
  assign_color2 G k prefs v col  = col'
  ⇒ 
  ∃y. lookup v col' = SOME y ∧ y≥2*k ∧ is_phy_var y``,
  rw[assign_color2_def]>>
  fs[LET_THM,domain_lookup]>>
  EVERY_CASE_TAC>>fs[]>>
  is_phy_var_tac>>
  qpat_abbrev_tac`lss = QSORT (λx:num y:num. x≤y)  B`>>
  SORTED_TAC>>
  metis_tac[unbound_colors_props])
  
(*Coloring produced after each spill_coloring step is
  partial_coloring_satisfactory*)
val spill_coloring_satisfactory = prove(``
  ∀G k prefs ls col.
  undir_graph G ∧
  partial_coloring_satisfactory col G
  ⇒
  let col' = spill_coloring G k prefs ls col in
    partial_coloring_satisfactory col' G``,
  Induct_on`ls`>>fs[spill_coloring_def,LET_THM]>>rw[]>>
  EVERY_CASE_TAC>>fs[]>>
  metis_tac[assign_color2_satisfactory])

(*Domain is extended*)
val spill_coloring_domain_1 = prove(``
  ∀G k prefs ls col.
  let col' = spill_coloring G k prefs ls col in 
  ∀x. MEM x ls ∧ x ∈ domain G ⇒ 
      x ∈ domain col'``,
  Induct_on`ls`>>fs[spill_coloring_def,LET_THM]>>rw[]
  >-
    (fs[assign_color2_def,domain_lookup,LET_THM]>>
    EVERY_CASE_TAC>>fs[]
    >>
    TRY(qpat_abbrev_tac `col' = insert h A col`>>
    qsuff_tac `∃y. lookup h col' = SOME y ∧ is_phy_var y`
    >-
      metis_tac[spill_coloring_never_overwrites]
    >>
      unabbrev_all_tac>>fs[lookup_insert]>>
      is_phy_var_tac>>
      qpat_abbrev_tac `lss = QSORT (λx:num y. x≤y) A`>>
      SORTED_TAC>>
      imp_res_tac unbound_colors_props>>
      metis_tac[])
    >>
    metis_tac[spill_coloring_never_overwrites])
  >>
    metis_tac[])

(*Coloring is extended on the list according to conventions*)
val spill_coloring_domain_2 = prove(``
  ∀G k prefs ls col.
  let col' = spill_coloring G k prefs ls col in 
  ∀x. MEM x ls ∧ x ∈ domain G ∧ x ∉ domain col ⇒ 
      ∃y. lookup x col' = SOME y ∧ y ≥ 2*k ∧ is_phy_var y``,
  Induct_on`ls`>>fs[spill_coloring_def,LET_THM]>>rw[]
  >-
    (imp_res_tac assign_color2_conventional>>fs[]>>
    metis_tac[spill_coloring_never_overwrites])
  >>
    Cases_on`x=h`>>fs[]
    >-
      (imp_res_tac assign_color2_conventional>>fs[]>>
      metis_tac[spill_coloring_never_overwrites])
    >>
      fs[assign_color2_def]>>EVERY_CASE_TAC>>
      fs[LET_THM]>>
      metis_tac[])

val assign_color2_reverse = prove(``
  ∀G:sp_graph k prefs h col col'.
  assign_color2 G k prefs h col = col'
  ⇒ 
  ∀x. x ≠ h ⇒ 
  (x ∈ domain col' ⇒ x ∈ domain col)``,
  rw[assign_color2_def]>>EVERY_CASE_TAC>>fs[LET_THM]>>
  metis_tac[])

val spill_coloring_domain_3 = prove(``
  ∀G k prefs ls col.
  let col' = spill_coloring G k prefs ls col in 
  ∀x. ¬MEM x ls ⇒ 
  (x ∈ domain col' ⇒ x ∈ domain col)``,
  Induct_on`ls`>>rw[spill_coloring_def,LET_THM]>>
  Cases_on`assign_color2 G k prefs h col`>>fs[]>>
  metis_tac[assign_color2_reverse])

val is_subgraph_edges_def = Define`
  is_subgraph_edges G H ⇔
    domain G ⊆ domain H  ∧  (*We never change the vertex set*)
   (∀x y. lookup_g x y G ⇒ lookup_g x y H)` 

val partial_coloring_satisfactory_subgraph_edges = prove(``
  ∀G H col.
  (*Every edge in G is in H*)
  undir_graph G ∧ 
  is_subgraph_edges G H ∧ 
  (partial_coloring_satisfactory col H) ⇒ 
  partial_coloring_satisfactory col G``,
  fs[partial_coloring_satisfactory_def,lookup_g_def,is_subgraph_edges_def]>>
  rw[]>>fs[domain_lookup,undir_graph_def]>>
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
  q ∈ domain G ⇒ 
  domain(list_g_insert q ls G) = 
  domain G ∪ set ls``,
  Induct>>fs[list_g_insert_def]>>rw[]>>
  fs[EXTENSION,undir_g_insert_domain]>>
  metis_tac[])

val finish_tac = 
  last_x_assum(qspec_then`v` assume_tac)>>rfs[]>>
  first_x_assum(qspec_then`v'` assume_tac)>>rfs[domain_lookup]>>
  last_x_assum(qspec_then `v'` assume_tac)>>rfs[]>>
  pop_assum(qspec_then`v` assume_tac)>>rfs[];

val partial_coloring_satisfactory_extend_2 = prove(``
  undir_graph G ∧ 
  partial_coloring_satisfactory col G ∧
  (x ∉ domain col ∨ y ∉ domain col) ⇒  
  partial_coloring_satisfactory col (undir_g_insert x y G)``,
  fs[undir_g_insert_def,dir_g_insert_def
    ,partial_coloring_satisfactory_def]>>rw[]>>
  fs[domain_lookup,LET_THM]>>
  rfs[lookup_insert]>>
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
 
val list_g_insert_lemma = prove(``
  ∀ls G col.
  undir_graph G ∧ 
  q ∉ domain col ∧ 
  ¬ MEM q ls ∧
  partial_coloring_satisfactory col G
  ⇒ 
  let G' = list_g_insert q ls G in 
  is_subgraph_edges G G' ∧ 
  undir_graph G' ∧ 
  partial_coloring_satisfactory col G'``,
  Induct>>rw[list_g_insert_def,is_subgraph_edges_def]>>fs[]>>
  first_x_assum(qspecl_then[`G`,`col`] mp_tac)>>discharge_hyps>>
  fs[LET_THM,Abbr`G'`]>>rw[]
  >-
    (fs[is_subgraph_edges_def,undir_g_insert_def]>>
    fs[SUBSET_DEF,domain_lookup]>>rw[]>>
    fs[dir_g_insert_def,LET_THM]>>EVERY_CASE_TAC>>
    fs[lookup_insert]>>
    rpt(IF_CASES_TAC>>fs[]))
  >-
    (fs[undir_g_insert_def]>>
    metis_tac[lookup_dir_g_insert_correct,list_g_insert_correct])
  >-
    metis_tac[undir_g_preserve]
  >>
    match_mp_tac partial_coloring_satisfactory_extend_2>>rfs[])

val is_subgraph_edges_trans = prove(``
  is_subgraph_edges A B ∧ 
  is_subgraph_edges B C ⇒ 
  is_subgraph_edges A C``,
  fs[is_subgraph_edges_def]>>rw[SUBSET_DEF])

val full_coalesce_aux_extends = prove(``
  ∀(G:sp_graph) ls col.
  partial_coloring_satisfactory col G ∧ 
  (∀p. MEM p ls ⇒ FST p ∉ domain col ∧ SND p ∉ domain col ∧ 
                  FST p ∈ domain G ∧ SND p ∈ domain G) ∧ 
  undir_graph G ⇒ 
  let (G',ls') = full_coalesce_aux G ls in
  is_subgraph_edges G G' ∧ 
  undir_graph G' ∧ 
  partial_coloring_satisfactory col G'``,
  Induct_on`ls`>-fs[full_coalesce_aux,LET_THM,is_subgraph_edges_def]>>
  ntac 4 strip_tac>>
  Cases_on`h`>>
  fs[full_coalesce_aux]>>
  IF_CASES_TAC>- 
    (fs[]>>metis_tac[])>>
  fs[LET_THM]>>
  qpat_abbrev_tac `G'=list_g_insert q A G`>>
  first_x_assum(qspecl_then[`G'`,`col`] mp_tac)>>
  rfs[]>>
  rw[Abbr`G'`]>>
  qpat_abbrev_tac`lss = MAP FST (toAList A)`>>
  Q.ISPECL_THEN [`q`,`lss`,`G`,`col`] mp_tac (GEN_ALL list_g_insert_lemma)>>
  rfs[]>>
  discharge_hyps_keep>-
    (rfs[FORALL_PROD,Abbr`lss`,undir_graph_def,lookup_g_def]>>
    `r ∈ domain G` by fs[]>>
      CCONTR_TAC>>fs[MEM_MAP,MEM_toAList,domain_lookup]>>
      rfs[]>>
      ntac 2 (last_x_assum(qspec_then`r` assume_tac))>>
      rfs[]>>
      first_x_assum(qspec_then`q` mp_tac)>>
      Cases_on`y`>>fs[MEM_toAList]>>
      Cases_on`lookup q' G`>>fs[])>>
  fs[LET_THM,UNCURRY]>>strip_tac>>
  qpat_assum `A ⇒ B` mp_tac>>
  discharge_hyps>-
    (`q ∈ domain G` by fs[FORALL_PROD]>>
    fs[EXTENSION,list_g_insert_domain])>>
  metis_tac[is_subgraph_edges_trans])

val full_coalesce_lemma = prove(``
  undir_graph G ∧ 
  partial_coloring_satisfactory col G ∧
  (∀x. MEM x ls ⇒ x ∉ domain col ∧ x ∈ domain G) ∧ 
  full_coalesce G moves ls = (G',spills,coalesce_map)
  ⇒ 
  is_subgraph_edges G G' ∧ 
  undir_graph G' ∧ 
  partial_coloring_satisfactory col G'``,
  fs[full_coalesce_def,LET_THM]>>
  qpat_abbrev_tac `lss = FILTER f moves`>>
  Cases_on`full_coalesce_aux G lss`>>
  strip_tac>>fs[]>>
  imp_res_tac full_coalesce_aux_extends>>
  ntac 2 (pop_assum kall_tac)>>
  pop_assum (qspec_then `lss` mp_tac)>>discharge_hyps>>
  fs[FORALL_PROD,MEM_FILTER,Abbr`lss`,LET_THM])

val reg_alloc_satisfactory = store_thm ("reg_alloc_satisfactory",``
  ∀G k moves.
  undir_graph G ⇒  
  let col = reg_alloc G k moves in
  (domain G ⊆ domain col ∧ 
  partial_coloring_satisfactory col G)``,
  rw[reg_alloc_def]>>
  `satisfactory_pref aux_pref` by fs[aux_pref_satisfactory]>>
  imp_res_tac alloc_coloring_success>>
  pop_assum(qspecl_then [`s'.stack`,`k`] assume_tac)>>rfs[LET_THM]>>
  `∀x. MEM x ls ⇒ x ∈ domain G` by 
    (Q.ISPECL_THEN [`aux_pref`,`s'.stack`,`k`,`G`] assume_tac
      (GEN_ALL alloc_coloring_success_2)>>
    rfs[LET_THM])>>
  `is_subgraph_edges G G' ∧ undir_graph G' ∧ 
   partial_coloring_satisfactory col G'` by 
     (match_mp_tac full_coalesce_lemma>>
     rw[]>>
     fs[INTER_DEF,EXTENSION]>>
     metis_tac[])
  >-
    (fs[is_subgraph_edges_def]>>
    `domain col ⊆ domain col''` by
      metis_tac[spill_coloring_domain_subset,SUBSET_DEF]>>
    Q.ISPECL_THEN [`G'`,`k`,`LN:num num_map`,`ls`,`col'`] assume_tac spill_coloring_domain_1>>
    rfs[LET_THM]>>
    fs[SUBSET_DEF,EXTENSION]>>rw[]>>res_tac>>
    pop_assum mp_tac>>
    rpt (IF_CASES_TAC>-metis_tac[domain_lookup])>>
    fs[])
  >>
    match_mp_tac partial_coloring_satisfactory_subgraph_edges>>
    Q.EXISTS_TAC`G'`>>fs[]>>
    metis_tac[spill_coloring_satisfactory])

val reg_alloc_total_satisfactory = store_thm ("reg_alloc_total_satisfactory",``
  ∀G k moves.
  undir_graph G ⇒ 
  let col = reg_alloc G k moves in 
  coloring_satisfactory (total_color col) G``,
  rw[]>>imp_res_tac reg_alloc_satisfactory>>
  pop_assum(qspecl_then[`moves`,`k`]assume_tac)>>rfs[LET_THM]>>
  fs[coloring_satisfactory_def,partial_coloring_satisfactory_def
      ,total_color_def,undir_graph_def]>>
  rw[]>>
  last_x_assum(qspec_then`v` assume_tac)>>
  rfs[Abbr`edges'`,domain_lookup]>>rfs[]>>
  rw[]>>res_tac>>
  `e ∈ domain G ∧ v ∈ domain col ∧ e ∈ domain col` by 
    fs[domain_lookup,SUBSET_DEF]>>
  fs[domain_lookup]>>
  first_x_assum(qspec_then`v'''` assume_tac)>>rfs[LET_THM]>>
  metis_tac[])

val reg_alloc_conventional = store_thm("reg_alloc_conventional" ,
``
  ∀G k moves.
  undir_graph G ⇒
  let col = reg_alloc G k moves in
  coloring_conventional G k (total_color col)``,
  rw[]>>imp_res_tac reg_alloc_satisfactory>>
  pop_assum(qspecl_then[`moves`,`k`] assume_tac)>>rfs[LET_THM]>>
  rw[total_color_def,reg_alloc_def,coloring_conventional_def]>>
  `x ∈ domain col` by 
    fs[SUBSET_DEF]>>
  fs[domain_lookup]>>rfs[]>>unabbrev_all_tac>>
  fs[reg_alloc_def]>>pop_assum mp_tac>>
  LET_ELIM_TAC>>
  rfs[LET_THM]>>
  imp_res_tac alloc_coloring_success>>
  pop_assum(qspec_then `aux_pref` mp_tac)>>discharge_hyps>>
  fs[aux_pref_satisfactory]>>strip_tac>>
  pop_assum(qspecl_then[`s'.stack`,`k`] assume_tac)>>rfs[LET_THM]>>
  `is_subgraph_edges G G' ∧ undir_graph G' ∧ 
   partial_coloring_satisfactory col G'` by 
     (`∀x. MEM x ls ⇒ x ∈ domain G` by 
       (Q.ISPECL_THEN [`aux_pref`,`s'.stack`,`k`,`G`] assume_tac
         (GEN_ALL alloc_coloring_success_2)>>
       rfs[LET_THM])>>
     match_mp_tac full_coalesce_lemma>>
     rw[]>>
     fs[INTER_DEF,EXTENSION]>>
     metis_tac[])>>
  `x ∈ domain G'` by 
    fs[is_subgraph_edges_def,SUBSET_DEF]>>
  IF_CASES_TAC>-
    (first_x_assum(qspec_then`x`assume_tac)>>rfs[]>>
    metis_tac[spill_coloring_never_overwrites,optionTheory.option_CLAUSES])
  >>
  IF_CASES_TAC>-
    (`MEM x ls` by metis_tac[]>>
    `x ∉ domain col` by 
      (fs[INTER_DEF,EXTENSION]>>metis_tac[])>>
    Cases_on`MEM x s'''.stack`>>fs[]
    >-
      (Q.ISPECL_THEN [`G'`,`k`,`coalesce_map`,`s'''.stack`,`col`] assume_tac
        spill_coloring_domain_2>> rfs[LET_THM,is_subgraph_edges_def]>>
      metis_tac[spill_coloring_never_overwrites,optionTheory.option_CLAUSES])
    >>
      Q.ISPECL_THEN [`G'`,`k`,`LN:num num_map`,`ls`,`col'`] assume_tac
        spill_coloring_domain_2>> rfs[LET_THM,is_subgraph_edges_def]>>
      metis_tac[spill_coloring_domain_3,optionTheory.option_CLAUSES])
  >>
  first_x_assum(qspec_then`x`assume_tac)>>rfs[]>>
  Cases_on`x ∈ domain col`
  >-
    metis_tac[spill_coloring_never_overwrites,optionTheory.option_CLAUSES]
  >>
  fs[]>>
  Cases_on`MEM x s'''.stack`>>fs[]
    >-
      (Q.ISPECL_THEN [`G'`,`k`,`coalesce_map`,`s'''.stack`,`col`] assume_tac
        spill_coloring_domain_2>> rfs[LET_THM,is_subgraph_edges_def]>>
      metis_tac[spill_coloring_never_overwrites,optionTheory.option_CLAUSES])
    >>
      Q.ISPECL_THEN [`G'`,`k`,`LN:num num_map`,`ls`,`col'`] assume_tac
        spill_coloring_domain_2>> rfs[LET_THM,is_subgraph_edges_def]>>
      metis_tac[spill_coloring_domain_3,optionTheory.option_CLAUSES])
      
val _ = export_theory()

