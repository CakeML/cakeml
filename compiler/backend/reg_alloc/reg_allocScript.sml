open preamble monadsyntax state_transformerTheory

val _ = new_theory "reg_alloc";
val _ = ParseExtras.tight_equality ();

(*--Start Initial Definitions--*)

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

(*--End Initial Definitions--*)


(*--Start Colouring Definitions--*)
(*
First phase (alloc_colouring): Produces a bounded colouring (< 2k)
Second phase (spill_colouring): Produces unbounded colouring (≥ 2k)
*)

(*
  First step:
  G = spgraph (possibly augmented e.g. in coalescing),
  k = number of registers to use,
  prefs = num-> num list -> num (selects a colour from the list),
  ls = heuristic order to colour vertices,
  Result: a num sptree where looking up a vertex gives its colouring
      and a num list of spilled vertices
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
val alloc_colouring_aux_def = Define`
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

(*--End Colouring Definitions--*)

(*--Start Analysis Definitions--*)

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

val full_coalesce_aux_def = Define`
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
        unification implementation in the inferencer
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

val _ = export_theory()
