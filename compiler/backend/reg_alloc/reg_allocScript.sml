(*
 * A monadic graph coloring register allocator
 *)

open preamble state_transformerTheory
open ml_monadBaseLib ml_monadBaseTheory
open sortingTheory

val _ = new_theory "reg_alloc"
val _ = ParseExtras.temp_tight_equality();
val _ = monadsyntax.temp_add_monadsyntax()

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

val _ = hide "state";

(* The graph-coloring register allocator *)

(* Datatype representing the state of nodes
  Fixed n : means it is fixed to color n
  Atemp   : means that the node is allowed to be allocated to any register or stack pos
  Stemp   : only allowed to be mapped to k, k+1, ...
*)
val _ = Datatype`
  tag = Fixed num | Atemp | Stemp`

(*
  Inputs are tagged with Fixed, Atemp , Stemp

  At all times, maintain invariant that adjacent nodes cannot be both Fixed
  to the same number

  First pass changes all Atemps to either Fixed or Stemp
  - Proofs: Fixed/Stemp stays unchanged

  Second pass changes all Stemps to Fixed with argument ≥ k
  - Proof: No remaining Stemp, every input node is mapped to Fixed
*)

(* Coloring state
  Notes
  - Invariant: all the arrays have dimension = dim
  - adj_ls represents the graph as an adj list
  - node_tag is the tag for each node
  - degrees represents the graph degree of each node.
    it should probably be implemented as a functional min heap instead

*)
val _ = Hol_datatype `
  ra_state = <| adj_ls   : (num list) list
              ; node_tag : tag list
              ; degrees  : num list
              ; dim      : num
              (* TODO: should these be kept as a separate record in
                       the state? *)
              ; simp_wl  : num list
              ; spill_wl : num list
              ; stack    : num list
              |>`;

val accessors = define_monad_access_funs ``:ra_state``;

val adj_ls_accessors = el 1 accessors;
val (adj_ls,get_adj_ls_def,set_adj_ls_def) = adj_ls_accessors;

val node_tag_accessors = el 2 accessors;
val (node_tag,get_node_tag_def,set_node_tag_def) = node_tag_accessors;

val degrees_accessors = el 3 accessors;
val (degrees,get_degrees_def,set_degrees_def) = degrees_accessors;

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail of string | Subscript`;

(* Monadic functions to handle the exceptions *)
val exn_functions = define_monad_exception_functions ``:state_exn`` ``:ra_state``;
val _ = temp_overload_on ("failwith", ``raise_Fail``);

val sub_exn = ``Subscript``;
val update_exn = ``Subscript``;
val arr_manip = define_MFarray_manip_funs [adj_ls_accessors,node_tag_accessors,degrees_accessors] sub_exn update_exn;

fun accessor_thm (a,b,c,d,e,f) = LIST_CONJ [b,c,d,e,f]

val adj_ls_manip = el 1 arr_manip;
val node_tag_manip = el 2 arr_manip;
val degrees_manip = el 3 arr_manip;

val adj_ls_accessor = save_thm("adj_ls_accessor",accessor_thm adj_ls_manip);
val node_tag_accessor = save_thm("node_tag_accessor",accessor_thm node_tag_manip);
val degrees_accessor = save_thm("degrees_accessor",accessor_thm degrees_manip);

(* Helper functions for defining the allocator *)

(* Monadic list functions -- doesn't care about order *)
val st_ex_FOREACH_def = Define `
  (st_ex_FOREACH [] a = return ()) ∧
  (st_ex_FOREACH (x::xs) a =
  do
    a x;
    st_ex_FOREACH xs a
  od)`

val st_ex_MAP_def = Define `
  (st_ex_MAP f [] = return []) ∧
  (st_ex_MAP f (x::xs) =
  do
    fx <- f x;
    fxs <- st_ex_MAP f xs;
    return (fx::fxs)
  od)`

val st_ex_PARTITION_def = Define`
  (st_ex_PARTITION P [] tt ff = return (tt,ff)) ∧
  (st_ex_PARTITION P (x::xs) tt ff =
  do
    Px <- P x;
    if Px then
      st_ex_PARTITION P xs (x::tt) ff
    else
      st_ex_PARTITION P xs tt (x::ff)
  od)`

val st_ex_FILTER_def = Define`
  (st_ex_FILTER P [] acc = return acc) ∧
  (st_ex_FILTER P (x::xs) acc =
  do
    Px <- P x;
    if Px then
      st_ex_FILTER P xs (x::acc)
    else
      st_ex_FILTER P xs acc
  od)`

(* The allocator heuristics, designed to minimize proof at the
   cost of some extra computation *)

(* (Safely) decrement the degree of all adjacent vertices by 1 *)
val dec_deg_def = Define`
  dec_deg n =
  do
    cd <- degrees_sub n;
    update_degrees n (cd+1)
  od`

val dec_degree_def = Define`
  dec_degree n =
  do
    d <- get_dim;
    if n < d then
    do
      adjs <- adj_ls_sub n;
      st_ex_FOREACH adjs dec_deg
    od
    else
      return ()
  od`

val add_simp_wl_def = Define`
  add_simp_wl ls =
  do
    swl <- get_simp_wl;
    set_simp_wl (ls ++ swl)
  od`

val add_stack_def = Define`
  add_stack ls =
  do
    swl <- get_stack;
    set_stack (ls ++ swl)
  od`

(* Move any vertices in the spill list that has
   degree < k into the simplify worklist
   TODO: could redefine a monadic PARTITION instead of

*)
val split_degree_def = Define`
  split_degree d k v =
  if v < d then
  do
    vd <- degrees_sub v;
    return (vd < k)
  od
  else
    return T`

val unspill_def = Define`
  unspill (k:num) =
  do
    d <- get_dim;
    swl <- get_spill_wl ;
    (ltk,gtk) <- st_ex_PARTITION (split_degree d k) swl [] [];
    set_spill_wl gtk;
    add_simp_wl ltk
  od`

(* Directly simplifies the entire list
   instead of doing it 1-by-1
   T = successful simplification
   F = no simplification
*)
val do_simplify_def = Define`
  do_simplify k =
  do
    simps <- get_simp_wl;
    if NULL simps then
      return F
    else
    do
      st_ex_FOREACH simps dec_degree;
      add_stack simps;
      set_simp_wl [];
      unspill k;
      return T
    od
  od`

val st_ex_list_MAX_deg_def = Define`
  (st_ex_list_MAX_deg [] d k v acc = return (k,acc)) ∧
  (st_ex_list_MAX_deg (x::xs) d k v acc =
  if x < d then
    do
      xv <- degrees_sub x;
      if v < xv then
        st_ex_list_MAX_deg xs d x xv (k::acc)
      else
        st_ex_list_MAX_deg xs d k v (x::acc)
    od
  else
    st_ex_list_MAX_deg xs d k v acc)`

val do_spill_def = Define`
  do_spill k =
  do
    spills <- get_spill_wl;
    d <- get_dim;
    case spills of
      [] => return F
    | (x::xs) =>
      if x >= d then return T else
      do
        xv <- degrees_sub x;
        (y,ys) <- st_ex_list_MAX_deg xs d x xv [];
        dec_deg y;
        unspill k;
        add_stack [y];
        set_spill_wl ys;
        return T
      od
  od`

val do_step_def = Define`
  do_step k =
  do
    b <- do_simplify k;
    if b then
      return ()
    else
  do
    b <- do_spill k;
    return ()
  od
  od`

val rpt_do_step_def = Define`
  (rpt_do_step k 0 = return ()) ∧
  (rpt_do_step k (SUC c) =
  do
    do_step k;
    rpt_do_step k c
  od)`

(*
  The coloring functions
*)

(* Removing adjacent colours from ks *)
val remove_colours_def = Define`
  (*No more available colours*)
  (remove_colours (ls:num list) [] = return []) ∧
  (*Some available colour after checking*)
  (remove_colours [] (ks:num list) = return ks) ∧
  (*Do the check for vertex x*)
  (remove_colours (x::xs) ks =
    do
      cx <- node_tag_sub x;
      r <-
      (case cx of
        Fixed c =>
          remove_colours xs (FILTER (λx.x ≠ c) ks)
      | _ =>
          remove_colours xs ks);
      return r
    od)`

(* First colouring -- turns all Atemps into Fixeds or Stemps drawing from colors in ks *)
(* Assign a tag to an Atemp node, skipping if it is not actually an Atemp *)

val assign_Atemp_tag_def = Define`
  assign_Atemp_tag ks prefs n =
  do
    ntag <- node_tag_sub n;
    case ntag of
      Atemp =>
      do
        adjs <- adj_ls_sub n;
        ks <- remove_colours adjs ks;
        case ks of
          [] => update_node_tag n Stemp
        | (x::_) =>
          do
            c <- prefs n ks; (* Apply monadic preference oracle *)
            case c of
              NONE =>
              update_node_tag n (Fixed x)
            | SOME y =>
              update_node_tag n (Fixed y)
          od
      od
    | _ => return ()
  od`

(* The first allocation step *)
(* k = num registers, ls = heuristic list, prefs = coloring preference *)
val assign_Atemps_def = Define`
  assign_Atemps k ls prefs =
  do
    d <- get_dim;
    ls <- return (FILTER (λn. n < d) ls);
    ks <- return (GENLIST (\x.x) k);
    cs <- return (GENLIST (\x.x) d); (* actually, only need to do those not already in ls *)
    (* Assign all the ones that the ls tells us to *)
    st_ex_FOREACH ls (assign_Atemp_tag ks prefs);
    (* actually, assign_Atemp_tag already filters for Atemps, so just pass it all the nodes *)
    st_ex_FOREACH cs (assign_Atemp_tag ks prefs)
  od`

(* Default makes it easier to translate, doesn't matter for our purposes what
   the default is *)
val tag_col_def = Define`
  (tag_col (Fixed n) = n) ∧
  (tag_col _ = 0n)`

(* Find the first available in k,k+1,...
   assuming input is sorted
*)
val unbound_colour_def = Define `
  (unbound_colour col [] = col) ∧
  (unbound_colour col ((x:num)::xs) =
    if col < x then
      col
    else if x = col then
      unbound_colour (col+1) xs
    else
      unbound_colour col xs)`

(* Second colouring -- turns all Stemps into Fixed ≥ k *)
val assign_Stemp_tag_def = Define`
  assign_Stemp_tag k n =
  do
    ntag <- node_tag_sub n;
    case ntag of
      Stemp =>
      do
        adjs <- adj_ls_sub n;
        tags <- st_ex_MAP (λi. node_tag_sub i) adjs;
        col <- return (unbound_colour k (QSORT (λx y. x≤y) (MAP tag_col tags)));
        update_node_tag n (Fixed col)
      od
    | _ => return ()
  od`

(* The second allocation step *)
val assign_Stemps_def = Define`
  assign_Stemps k =
  do
    d <- get_dim;
    cs <- return (GENLIST (\x.x) d);
    st_ex_FOREACH cs (assign_Stemp_tag k)
  od`

(* Monadic biased selection oracle, finds the first matching color *)
val first_match_col_def = Define`
  (first_match_col ks [] = return NONE) ∧
  (first_match_col ks (x::xs) =
    do
      c <- node_tag_sub x;
      case c of
        Fixed m =>
          if MEM m ks then return (SOME m) else first_match_col ks xs
      | _ => first_match_col ks xs
    od)`

(* mtable is an sptree lookup for the moves *)
val biased_pref_def = Define`
  biased_pref mtable n ks =
  do
    case lookup n mtable of
      NONE => return NONE
    | SOME vs =>
      handle_Subscript (first_match_col ks vs) (return NONE)
  od`

(* Clash tree representation of a program -- this is designed as an interface:
  wordLang program -> clash tree -> reg alloc

  It only represents wordLang programs, which do not have back-edges
  The allocator itself is more general, and supports arbitrary graphs
  It serves two purposes:
  1) slightly more efficient checking of coloring oracles
  2) it gets compiled in to the clash graphs for the allocator

  TODO: probably want to move the clash tree representation up and separate it
  from the allocator
*)

val _ = Datatype`
  clash_tree = Delta (num list) (num list) (* (Writes list, Reads list) *)
             | Set num_set (* Fixed set *)
             | Branch (num_set option) clash_tree clash_tree
             | Seq clash_tree clash_tree`
             (* Binary branch, with an optional liveset at the head*)

(* --- clash_tree oracle checks --- *)
val numset_list_delete_def = Define`
  (numset_list_delete [] (t:'a num_map) = t) ∧
  (numset_list_delete (x::xs) t = numset_list_delete xs (delete x t))`

(*Check that a numset is injective over the clash sets in an interpreted tree*)
val check_col_def = Define`
  check_col f t =
    let names = MAP (f o FST) (toAList t) in
    if ALL_DISTINCT names then
      SOME (t,fromAList (MAP (λx. (x,())) names))
    else NONE`

val check_partial_col_def = Define`
  (check_partial_col f [] t ft = SOME (t,ft)) ∧
  (check_partial_col f (x::xs) t ft =
    case lookup x t of
      SOME () => check_partial_col f xs t ft
    | NONE =>
    case lookup (f x) ft of
      NONE => check_partial_col f xs (insert x () t) (insert (f x) () ft)
    | SOME () => NONE)`

(* The checking function, used by oracle, and also used as part of the correctness proof *)
(* live = the liveset, flive = the liveset with f applied over it*)
val check_clash_tree_def = Define`
  (check_clash_tree f (Delta w r) live flive =
    case check_partial_col f w live flive of
      NONE => NONE
    | SOME _ =>
    let del_w = (numset_list_delete w live) in
    let fdel_w = (numset_list_delete (MAP f w) flive) in
    check_partial_col f r del_w fdel_w) ∧
  (check_clash_tree f (Set t) live flive = check_col f t) ∧
  (check_clash_tree f (Branch topt t1 t2) live flive =
    case check_clash_tree f t1 live flive of
      NONE => NONE
    | SOME (t1_out,ft1_out) =>
    case check_clash_tree f t2 live flive of
      NONE => NONE
    | SOME (t2_out,ft2_out) =>
    case topt of
      NONE =>
        (* This check can be done in either direction *)
        check_partial_col f (MAP FST (toAList (difference t2_out t1_out))) t1_out ft1_out
    | SOME t => check_col f t) ∧
  (check_clash_tree f (Seq t1 t2) live flive =
    case check_clash_tree f t2 live flive of
      NONE => NONE
    | SOME (t2_out,ft2_out) =>
      check_clash_tree f t1 t2_out ft2_out)`

(* --
compile clash_trees into a register allocator state
This produces two sptrees that re-map clash_tree variables
into the register allocator state, and vice versa
The second remap is probably not necessary?
-- *)

(* Map clash tree variables into allocator nodes, also computes the
  size of the array required
  ta = to allocator
  fa = from allocator
  nv = next fresh name
*)
val list_remap_def = Define`
  (list_remap [] (ta,fa,nv) = (ta,fa,nv)) ∧
  (list_remap (x::xs) (ta,fa,nv) =
    case lookup x ta of
      SOME v => list_remap xs (ta,fa,nv)
    | NONE =>
      list_remap xs (insert x nv ta,insert nv x fa,nv+1))`

val mk_bij_aux_def = Define`
  (mk_bij_aux (Delta writes reads) tfn =
    list_remap writes (list_remap reads tfn)) ∧
  (mk_bij_aux (Set t) tfn =
    list_remap (MAP FST (toAList t)) tfn) ∧
  (mk_bij_aux (Branch topt t1 t2) tfn =
     let tfn' = mk_bij_aux t2 (mk_bij_aux t1 tfn) in
     case topt of
       NONE => tfn'
     | SOME ts => list_remap (MAP FST (toAList ts)) tfn') ∧
  (mk_bij_aux (Seq t1 t2) tfn =
    mk_bij_aux t1 (mk_bij_aux t2 tfn))`

val mk_bij_def = Define`
  mk_bij t =
    let (ta,fa,n) = mk_bij_aux t (LN,LN,0n) in
    (ta,fa,n)`
    (* Hide the sptree impl
    ((λi. lookup_any i ta 0),(λi. lookup_any i fa 0), n)` *)

(*Distinguish 3 kinds of variables:
  Evens are physical registers
  4n+1 are allocatable registers
  4n+3 are stack registers*)

val is_stack_var_def = Define`
  is_stack_var (n:num) = (n MOD 4 = 3)`;
val is_phy_var_def = Define`
  is_phy_var (n:num) = (n MOD 2 = 0)`;
val is_alloc_var_def = Define`
  is_alloc_var (n:num) = (n MOD 4 = 1)`;

val convention_partitions = Q.store_thm("convention_partitions",`
  ∀n. (is_stack_var n ⇔ (¬is_phy_var n) ∧ ¬(is_alloc_var n)) ∧
      (is_phy_var n ⇔ (¬is_stack_var n) ∧ ¬(is_alloc_var n)) ∧
      (is_alloc_var n ⇔ (¬is_phy_var n) ∧ ¬(is_stack_var n))`,
  rw[is_stack_var_def,is_phy_var_def,is_alloc_var_def,EQ_IMP_THM]
  \\ `n MOD 2 = (n MOD 4) MOD 2` by
   (ONCE_REWRITE_TAC [GSYM (EVAL ``2*2:num``)]
    \\ fs [arithmeticTheory.MOD_MULT_MOD])
  \\ fs []
  \\ `n MOD 4 < 4` by fs []
  \\ IMP_RES_TAC (DECIDE
       ``n < 4 ==> (n = 0) \/ (n = 1) \/ (n = 2) \/ (n = 3:num)``)
  \\ fs []);

(* Set the tags according to wordLang conventions *)
val mk_tags_def = Define`
  mk_tags n fa =
  do
    inds <- return (GENLIST (\x.x) n);
    st_ex_FOREACH inds
    (λi.
      let v = fa i in
      let remainder = v MOD 4 in
      if remainder = 1 then
        update_node_tag i Atemp
      else if remainder = 3 then
        update_node_tag i Stemp
      else
        update_node_tag i (Fixed (v DIV 2)))
  od`;

(* Insert an undirect edge into the adj list representation
  -- This is VERY lightly optimized to remove duplicates
  -- alternative: maintain an "invisible" invariant that
     all the adj_lists are sorted
*)

val insert_edge_def = Define`
  insert_edge x y =
  do
    adjx <- adj_ls_sub x;
    adjy <- adj_ls_sub y;
    if MEM y adjx then return ()
    else
    do
      update_adj_ls x (y::adjx);
      update_adj_ls y (x::adjy)
    od
  od`;

(* insert a list of edges all adjacent to one node *)
val list_insert_edge_def = Define`
  (list_insert_edge x [] = return ()) ∧
  (list_insert_edge x (y::ys) =
    do
      insert_edge x y;
      list_insert_edge x ys
    od)`;

val clique_insert_edge_def = Define`
  (clique_insert_edge [] = return ()) ∧
  (clique_insert_edge (x::xs) =
  do
    list_insert_edge x xs;
    clique_insert_edge xs
  od)`;

(* assuming vertices in cli already forms a clique,
   extend it with new members
*)
val extend_clique_def = Define`
  (extend_clique [] cli = return cli) ∧
  (extend_clique (x::xs) cli =
    if MEM x cli
    then
      extend_clique xs cli
    else
    do
      list_insert_edge x cli;
      extend_clique xs (x::cli)
    od)`;

(* Initializes the clash_graph using a clash_tree and a remapping bijection *)
val mk_graph_def = Define`
  (mk_graph ta (Delta w r) liveout =
    do
      wta  <- return(MAP ta w);
      rta  <- return(MAP ta r);
      live <- extend_clique wta liveout;
      live <- return (FILTER (λx. ¬MEM x wta) live);
      livein <- extend_clique rta live;
      return livein
    od) ∧
  (mk_graph ta (Set t) liveout =
    do
      live <- return(MAP ta (MAP FST (toAList t)));
      clique_insert_edge live;
      return live
    od) ∧
  (mk_graph ta (Branch topt t1 t2) liveout =
    do
      t1_live <- mk_graph ta t1 liveout;
      t2_live <- mk_graph ta t2 liveout;
      (case topt of
        NONE =>
        do
          livein <- extend_clique t1_live t2_live;
          return livein
        od
      | SOME t =>
        do
          clashes <- return (MAP ta (MAP FST (toAList t)));
          clique_insert_edge clashes;
          return clashes
        od)
    od) ∧
  (mk_graph ta (Seq t1 t2) liveout =
    do
      live <- mk_graph ta t2 liveout;
      mk_graph ta t1 live
    od)`;


val sp_default_def = Define`
  sp_default t i =
  (case lookup i t of NONE => if is_phy_var i then i DIV 2 else i | SOME x => x)`

val extend_graph_def = Define`
  (extend_graph ta [] = return ()) ∧
  (extend_graph ta ((x,y)::xs) =
  do
    insert_edge (ta x) (ta y);
    extend_graph ta xs
  od)`

(* sets up the register allocator init state with the clash_tree input
  TODO: should the sptrees be hidden right away?
  It might be easier to transfer an sptree directly for the oracle register
  allocator

  ct = clash_tree
  forced = forced edges -- will need new proof that all forced edges are in the tree
*)
val init_ra_state_def = Define`
  init_ra_state ct forced (ta,fa,n) =
  do
    mk_graph (sp_default ta) ct []; (* Put in the usual edges *)
    extend_graph (sp_default ta) forced;
    mk_tags n (sp_default fa);
  od`;

val is_Atemp_def = Define`
  is_Atemp d =
  do
    dt <- node_tag_sub d;
    return (dt = Atemp)
  od`

(* Initializer for the first allocation step *)
val init_alloc1_heu_def = Define`
  init_alloc1_heu d k =
  do
    ds <- return (GENLIST (\x.x) d);
    st_ex_FOREACH ds (* Set the degree for each node *)
      (λi.
      do
        adjls <- adj_ls_sub i;
        update_degrees i (LENGTH adjls)
      od
      );
    allocs <- st_ex_FILTER is_Atemp ds [];
    (ltk,gtk) <- st_ex_PARTITION (split_degree d k) allocs [] [];
    set_simp_wl ltk;
    set_spill_wl gtk;
    return (LENGTH allocs)
  od`

val do_alloc1_def = Define`
  do_alloc1 k =
  do
    d <- get_dim;
    l <- init_alloc1_heu d k;
    rpt_do_step k l;
    st <- get_stack;
    return st
  od`

val extract_tag_def = Define`
  (extract_tag t = case t of
    Fixed m => m
  | _ => 0)` (* never happens*)

(* return the final coloring as an sptree *)
val extract_color_def = Define`
  extract_color ta =
  do
    taa <- return (toAList ta);
    itags <- st_ex_MAP (λ(k,v).
      do
        t <- node_tag_sub v;
        return (k,extract_tag t)
      od) taa; (* can make the sptree directly *)
    return (fromAList itags)
  od`

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
  map (λls. MAP SND (QSORT (λp:num,x p',x'. p>p') ls )) acc`

(* Putting everything together in one call *)
val do_reg_alloc_def = Define`
  do_reg_alloc k moves ct forced (ta,fa,n) =
  do
    init_ra_state ct forced (ta,fa,n);
    ls <- do_alloc1 k;
    assign_Atemps k ls (biased_pref (resort_moves (moves_to_sp moves LN)));
    assign_Stemps k;
    spcol <- extract_color ta;
    return spcol (* return the composed from wordLang into the graph + the allocation *)
  od`

(* As we are using fixed-size array, we need to define a different record type for the initialization *)
val array_fields_names = ["adj_ls", "node_tag", "degrees"];
val run_ira_state_def = define_run ``:ra_state``
                                       array_fields_names
                                      "ira_state";

(* The top-level (non-monadic) reg_alloc call which should be modified to fit
   the translator's requirements *)

val reg_alloc_aux_def = Define`
  reg_alloc_aux k moves ct forced (ta,fa,n) =
    run_ira_state (do_reg_alloc k moves ct forced (ta,fa,n))
                      <| adj_ls   := (n, [])
                       ; node_tag := (n, Atemp)
		       ; degrees  := (n, 0)
		       ; dim      := n
		       ; simp_wl  := []
		       ; spill_wl := []
		       ; stack    := [] |>`;

val reg_alloc_def = Define `
reg_alloc k moves ct forced =
    reg_alloc_aux k moves ct forced (mk_bij ct)`;

val _ = export_theory();
