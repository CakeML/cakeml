open HolKernel Parse boolLib bossLib miscLib
open listTheory sptreeTheory pred_setTheory pairTheory
open rich_listTheory
open alistTheory
open BasicProvers
open word_liveTheory
open word_langTheory
open whileTheory
open sortingTheory

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
  assign_color2 G k (*prefs*) v col =
  case lookup v col of
    SOME x => col (*Actually redundant, may make proof harder?*)
  | NONE =>
  case lookup v G of
    (*Vertex wasn't even in the graph -- ignore*)
    NONE => col 
  | SOME x =>
    let xs = MAP FST (toAList x) in
    (*Get all the nightbor colors*)
    let cols = option_filter (MAP (λx. lookup x col) xs) in
    let c = unbound_colors (2*k) (QSORT (λx y. x≤y) cols) in 
      insert v c col` 

(*ls is a spill list*)
val spill_coloring_def = Define`
  (spill_coloring (G:sp_graph) k [] col = col) ∧
  (spill_coloring G k (x::xs) col =
    let col = assign_color2 G k x col in 
    spill_coloring G k xs col)`

(*End coloring definitions*)

(*Define register allocation*)
(*open monadsyntax
open state_transformerTheory*)

val _ = Hol_datatype `
  ra_state = <| graph : sp_graph;
                colors : num;
                degs : num num_map;(*maybe should become a 2 step O(1)lookup*)
                simp_worklist : num list;
                spill_worklist : num list;
                stack : num list |>`;
                (*TODO: the other work lists
                coalesced : num num_map;
                next_spill_var : num;*)
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

val push_stack_def = Define`
  push_stack v =
    λs. s with stack:= v::s.stack`

val dec_deg_def = Define`
  dec_deg v =
  λs.
  let es = lookup v s.graph in
  case es of 
    NONE => s (*(NONE,s)*)
  | SOME es =>
    let edges = MAP FST(toAList es) in
    let degs = FOLDR 
      (λv degs. 
      case lookup v degs of
        NONE => degs
      | SOME (d:num) => insert v (d-1) degs) s.degs edges in
    (*Not the best way to do it...*)
    let (ltk,gtk) = PARTITION 
      (λv. case lookup v degs of 
        NONE => F
      | SOME x => x < s.colors)  s.spill_worklist in
    s with <|simp_worklist:= ltk++s.simp_worklist;spill_worklist:= gtk;
             degs := degs|>`
      
val simplify_def = Define`
  simplify =
    λs.
    case s.simp_worklist of
      [] => (NONE,s)
    | (x::xs) => 
      (SOME x,(dec_deg x (s with simp_worklist:= xs)))`
     
val spill_def = Define`
  spill =
    λs.
    case s.spill_worklist of
      [] => (NONE,s)
    | (x::xs) =>
      (SOME x,(dec_deg x (s with spill_worklist:= xs)))`

val do_step_def = Define`
  do_step =
    λs.
    let (res,s) = simplify s in
    case res of
    NONE => 
      (let (res,s) = spill s in
      case res of 
        NONE => s
      | SOME x => push_stack x s)
    | SOME x => push_stack x s`

val rpt_do_step_def = Define`
  rpt_do_step =
    λs. 
    WHILE (λs. s.simp_worklist ≠ [] ∨ s.spill_worklist ≠ []) do_step s` 

(*
open sptreeSyntax
sptreeSyntax.temp_add_sptree_printer();

val rhsThm = rhs o concl;
val st = rhsThm (EVAL ``rpt_do_step (init_ra_state (get_spg
  (Seq (Move [1,2;3,4;5,6])
  (Call (SOME (3, list_insert [1;3;5;7;9] [();();();();()] LN,Skip)) (SOME 400) [7;9] NONE)) LN) 3)``)

val G = rhsThm (EVAL ``^(st).graph``)
val k = rhsThm (EVAL ``^(st).colors``)
val ls = rhsThm (EVAL ``^(st).stack``)
val prefs = ``λ(h:num) (ls:num list) (col:num num_map). HD ls``
EVAL ``alloc_coloring ^(G) ^(k) ^(prefs) ^(ls)``
*)

(*Initialize state for the second phase, here we are given an ls =
  vertices to consider*)
val sec_ra_state_def = Define`
  (sec_ra_state (G:sp_graph) (k:num) vertices = 
  (*In this instance, we care about the degree w.r.t. to spilled variables*)
  let vdegs = MAP (λv. v,count_degrees (λx. ¬(is_phy_var x) ∨ x ≥ 2*k)
              (THE(lookup v G))) vertices in
  let tdegs = fromAList vdegs in
  <|graph := G ; colors := k ; degs := tdegs; 
    simp_worklist := vertices;
    spill_worklist := [];
    stack:=[]|>)`

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

val full_simplify_def = Define`
  full_simplify =
    λs.
    let ls = QSORT (deg_comparator s.degs) s.simp_worklist in
    case ls of
      [] => (NONE,s)
    | (x::xs) => 
      (SOME x,(dec_deg x (s with simp_worklist:= xs)))`

val do_step2_def = Define`
  do_step2 =
    λs.
    let (res,s) = simplify s in
    case res of
      NONE => s
    | SOME x => push_stack x s`

val rpt_do_step_2_def = Define`
  rpt_do_step2 =
    λs. 
    WHILE (λs. s.simp_worklist ≠ []) do_step2 s` 

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
  Currently, the graph does not actually change*)
val reg_alloc_def =  Define`
  reg_alloc G k =
  (*Initialize*)
  let s = init_ra_state G k in
  (*First phase*)
  let s = rpt_do_step s in
  let (col,ls) = alloc_coloring G k aux_pref s.stack in
  let s = sec_ra_state G k ls in
  let s = rpt_do_step2 s in
  let col = spill_coloring G k s.stack col in
  let col = spill_coloring G k ls col in
    col`
    (*2nd call Unnecessary extra call to spill_coloring
     if we instead prove that the vertices are
      maintained by the register allocator*)

(*
val rhsThm = rhs o concl;
val st = rhsThm (EVAL ``rpt_do_step (init_ra_state (get_spg
  (Seq (Move [1,2;3,4;5,6])
  (Call (SOME (3, list_insert [1;3;5;7;9] [();();();();()] LN,Skip)) (SOME 400) [7;9] NONE)) LN) 3)``)

val G = rhsThm (EVAL ``^(st).graph``)
val k = rhsThm (EVAL ``^(st).colors``)
val ls = rhsThm (EVAL ``^(st).stack``)
val prefs = ``λ(h:num) (ls:num list) (col:num num_map). HD ls``

EVAL ``find_coloring ^(G) ^(k) ^(prefs) ^(ls)``

val p1 = EVAL ``reg_alloc (get_spg
  (Seq (Move [1,2;3,4;5,6])
  (Call (SOME (3, list_insert [1;3;5;7;9] [();();();();()] LN,Skip)) (SOME 400) [7;9] NONE)) LN) 3``
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
  Cases_on`ls`>>fs[])

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
        
val spill_coloring_never_overwrites = prove(``
  ∀ls col col'.
  lookup x col = SOME y ∧ 
  spill_coloring G k ls col = col'
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
  domain col ⊆ domain (spill_coloring G k ls col)``,
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
  partial_coloring_satisfactory (assign_color2 G k h col) G``,
  rw[assign_color2_def]>>
  EVERY_CASE_TAC>>fs[LET_THM]>>
  match_mp_tac partial_coloring_satisfactory_extend>>rw[]>>
  fs[domain_lookup]>>
  qpat_abbrev_tac`lss = QSORT (λx:num y:num. x≤y)  B`>>
  SORTED_TAC>>
  `MEM v lss` by
    (unabbrev_all_tac>>
    fs[QSORT_MEM,option_filter_def,MEM_MAP,MEM_FILTER,EXISTS_PROD
      ,MEM_toAList,PULL_EXISTS]>>
    HINT_EXISTS_TAC>>fs[])>>
  is_phy_var_tac>>
  metis_tac[unbound_colors_props])
 
val assign_color2_conventional = prove(``
  v ∈ domain G ∧ 
  v ∉ domain col ∧ 
  assign_color2 G k v col  = col'
  ⇒ 
  ∃y. lookup v col' = SOME y ∧ y≥2*k ∧ is_phy_var y``,
  rw[assign_color2_def]>>
  EVERY_CASE_TAC>>fs[LET_THM,domain_lookup]>>
  is_phy_var_tac>>
  qpat_abbrev_tac`lss = QSORT (λx:num y:num. x≤y)  B`>>
  SORTED_TAC>>
  metis_tac[unbound_colors_props])
  
(*Coloring produced after each spill_coloring step is
  partial_coloring_satisfactory*)
val spill_coloring_satisfactory = prove(``
  ∀G k ls col.
  undir_graph G ∧
  partial_coloring_satisfactory col G
  ⇒
  let col' = spill_coloring G k ls col in
    partial_coloring_satisfactory col' G``,
  Induct_on`ls`>>fs[spill_coloring_def,LET_THM]>>rw[]>>
  EVERY_CASE_TAC>>fs[]>>
  first_x_assum(qspecl_then
    [`G`,`k`,`assign_color2 G k h col`] mp_tac)>>
  discharge_hyps>>
    metis_tac[assign_color2_satisfactory])

(*Domain is extended*)
val spill_coloring_domain_1 = prove(``
  ∀G k ls col.
  let col' = spill_coloring G k ls col in 
  ∀x. MEM x ls ∧ x ∈ domain G ⇒ 
      x ∈ domain col'``,
  Induct_on`ls`>>fs[spill_coloring_def,LET_THM]>>rw[]
  >-
    (fs[assign_color2_def]>>EVERY_CASE_TAC>>fs[domain_lookup,LET_THM]
    >-
    (qpat_abbrev_tac `col' = insert h A col`>>
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
  ∀G k ls col.
  let col' = spill_coloring G k ls col in 
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
  ∀G:sp_graph k h col col'.
  assign_color2 G k h col = col'
  ⇒ 
  ∀x. x ≠ h ⇒ 
  (x ∈ domain col' ⇒ x ∈ domain col)``,
  rw[assign_color2_def]>>EVERY_CASE_TAC>>fs[LET_THM]>>
  metis_tac[])

val spill_coloring_domain_3 = prove(``
  ∀G k ls col.
  let col' = spill_coloring G k ls col in 
  ∀x. ¬MEM x ls ⇒ 
  (x ∈ domain col' ⇒ x ∈ domain col)``,
  Induct_on`ls`>>rw[spill_coloring_def,LET_THM]>>
  Cases_on`assign_color2 G k h col`>>fs[]>>
  metis_tac[assign_color2_reverse])

val reg_alloc_satisfactory = store_thm ("reg_alloc_satisfactory",``
  ∀G k.
  undir_graph G ⇒  
  let col = reg_alloc G k in
  (domain G ⊆ domain col ∧ 
  partial_coloring_satisfactory col G)``,
  rw[reg_alloc_def]>>
  `satisfactory_pref aux_pref` by fs[aux_pref_satisfactory]>>
  imp_res_tac alloc_coloring_success>>
  pop_assum(qspecl_then [`s'.stack`,`k`] assume_tac)>>rfs[LET_THM]
  >-
    (`domain col ⊆ domain col''` by
      metis_tac[spill_coloring_domain_subset,SUBSET_DEF]>>
    Q.ISPECL_THEN [`G`,`k`,`ls`,`col'`] assume_tac spill_coloring_domain_1>>
    rfs[LET_THM]>>
    fs[SUBSET_DEF,EXTENSION]>>rw[]>>res_tac>>
    pop_assum mp_tac>>
    rpt (IF_CASES_TAC>-metis_tac[domain_lookup])>>
    fs[])
  >>
    metis_tac[spill_coloring_satisfactory])

val reg_alloc_total_satisfactory = store_thm ("reg_alloc_total_satisfactory",``
  ∀G k.
  undir_graph G ⇒ 
  let col = reg_alloc G k in 
  coloring_satisfactory (total_color col) G``,
  rw[]>>imp_res_tac reg_alloc_satisfactory>>
  pop_assum(qspec_then`k` assume_tac)>>rfs[LET_THM]>>
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
  ∀G k.
  undir_graph G ⇒
  let col = reg_alloc G k in
  coloring_conventional G k (total_color col)``,
  rw[]>>imp_res_tac reg_alloc_satisfactory>>
  pop_assum(qspec_then`k` assume_tac)>>rfs[LET_THM]>>
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
      (Q.ISPECL_THEN [`G`,`k`,`s'''.stack`,`col`] assume_tac
        spill_coloring_domain_2>> rfs[LET_THM]>>
      metis_tac[spill_coloring_never_overwrites,optionTheory.option_CLAUSES])
    >>
      metis_tac[spill_coloring_domain_3,
        spill_coloring_domain_2,optionTheory.option_CLAUSES])
  >>
  first_x_assum(qspec_then`x`assume_tac)>>rfs[]>>
  Cases_on`x ∈ domain col`
  >-
    metis_tac[spill_coloring_never_overwrites,optionTheory.option_CLAUSES]
  >>
  fs[]>>
  Cases_on`MEM x s'''.stack`>>fs[]
    >-
      (Q.ISPECL_THEN [`G`,`k`,`s'''.stack`,`col`] assume_tac
        spill_coloring_domain_2>> rfs[LET_THM]>>
      metis_tac[spill_coloring_never_overwrites,optionTheory.option_CLAUSES])
    >>
      metis_tac[spill_coloring_domain_3,
        spill_coloring_domain_2,optionTheory.option_CLAUSES])


val _ = export_theory()


(*Takes the worklist and simplifies it, 
  returning something to put on the stack*)

(*

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

*)
