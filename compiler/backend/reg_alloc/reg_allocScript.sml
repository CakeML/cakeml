(*
  A monadic graph-coloring register allocator
*)
Theory reg_alloc
Libs
  preamble ml_monadBaseLib
Ancestors
  mllist state_transformer ml_monadBase sorting


val _ = ParseExtras.temp_tight_equality();
val _ = monadsyntax.temp_add_monadsyntax()

Overload monad_bind[local] = ``st_ex_bind``
Overload monad_unitbind[local] = ``\x y. st_ex_bind x (\z. y)``
Overload monad_ignore_bind[local] = ``\x y. st_ex_bind x (\z. y)``
Overload return[local] = ``st_ex_return``

val _ = hide "state";

(*
  The graph-coloring register allocator

  It currently uses several ``secret'' invariants that are important for
  performance but are not verified.

  This is an attempt at listing them:

  1) In ra_state.coalesced, if coalesced[x] ≥ x it is not coalesced
     i.e., coalesces only happen ``downwards''

  2) adjacency lists are ALWAYS sorted
*)

(*
  The tag datatype representing the state of nodes:

  Fixed n : means it is fixed to color n
  Atemp   : means that the node is allowed to be allocated to any register or stack pos
  Stemp   : only allowed to be mapped to k, k+1, ... (stack positions)
*)
Datatype:
  tag = Fixed num | Atemp | Stemp
End

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
  - Invariant: all the arrays have dimension = dim
*)
Datatype:
  ra_state = <|
     (* Info about the graph *)
       adj_ls   : (num list) list (* adjacency list -- arr of lists *)
     ; node_tag : tag list        (* tags for each node -- arr *)
     ; degrees  : num list        (* degrees for each node -- arr *)
     ; dim      : num             (* num vertices in the graph *)

     (* worklists *)
     ; simp_wl  : num list        (* simp worklist -- list, non-move related deg < k *)
     ; spill_wl : num list        (* spill worklist -- list, deg >= k *)
     ; freeze_wl : num list       (* freeze worklist -- list, move related deg < k *)
     ; avail_moves_wl : (num,(num # num)) alist   (* active moves -- list, sorted by pri *)
     ; unavail_moves_wl : (num,(num # num)) alist (* inactive moves -- list *)

     (* book keeping *)
     ; coalesced : num list       (* keep track of coalesce target for each node -- arr *)
     ; move_related : bool list   (* fast check if a node is still move related -- arr *)
     ; stack    : num list
     |>
End

val accessors = define_monad_access_funs ``:ra_state``;

val adj_ls_accessors = el 1 accessors;
val (adj_ls,get_adj_ls_def,set_adj_ls_def) = adj_ls_accessors;

val node_tag_accessors = el 2 accessors;
val (node_tag,get_node_tag_def,set_node_tag_def) = node_tag_accessors;

val degrees_accessors = el 3 accessors;
val (degrees,get_degrees_def,set_degrees_def) = degrees_accessors;

val coalesced_accessors = el 10 accessors;
val (coalesced, get_coalesced_def, set_coalesced_def) = coalesced_accessors;

val move_related_accessors = el 11 accessors;
val (move_related, get_move_related_def, set_move_related_def) = move_related_accessors;

(* Data type for the exceptions *)
Datatype:
  state_exn = Fail string | Subscript
End

(* Monadic functions to handle the exceptions *)
val exn_functions = define_monad_exception_functions ``:state_exn`` ``:ra_state``;
Overload failwith[local] = ``raise_Fail``

val sub_exn = ``Subscript``;
val update_exn = ``Subscript``;

(* Fixed-size array manipulators *)
val arr_manip = define_MFarray_manip_funs
  [adj_ls_accessors,node_tag_accessors,degrees_accessors,
   coalesced_accessors, move_related_accessors] sub_exn update_exn;

fun accessor_thm (a,b,c,d,e,f) = LIST_CONJ [b,c,d,e,f]

val adj_ls_manip = el 1 arr_manip;
val node_tag_manip = el 2 arr_manip;
val degrees_manip = el 3 arr_manip;
val coalesced_manip = el 4 arr_manip;
val move_related_manip = el 5 arr_manip;

Theorem adj_ls_accessor =
  accessor_thm adj_ls_manip
Theorem node_tag_accessor =
  accessor_thm node_tag_manip
Theorem degrees_accessor =
  accessor_thm degrees_manip
Theorem coalesced_accessor =
  accessor_thm coalesced_manip
Theorem move_related_accessor =
  accessor_thm move_related_manip

(* Helper functions for defining the allocator *)

(* Monadic list functions -- doesn't care about order *)
Definition st_ex_FOREACH_def:
  (st_ex_FOREACH [] a = return ()) ∧
  (st_ex_FOREACH (x::xs) a =
  do
    a x;
    st_ex_FOREACH xs a
  od)
End

Definition st_ex_MAP_def:
  (st_ex_MAP f [] = return []) ∧
  (st_ex_MAP f (x::xs) =
  do
    fx <- f x;
    fxs <- st_ex_MAP f xs;
    return (fx::fxs)
  od)
End

Definition st_ex_PARTITION_def:
  (st_ex_PARTITION P [] tt ff = return (tt,ff)) ∧
  (st_ex_PARTITION P (x::xs) tt ff =
  do
    Px <- P x;
    if Px then
      st_ex_PARTITION P xs (x::tt) ff
    else
      st_ex_PARTITION P xs tt (x::ff)
  od)
End

Definition st_ex_FILTER_def:
  (st_ex_FILTER P [] acc = return acc) ∧
  (st_ex_FILTER P (x::xs) acc =
  do
    Px <- P x;
    if Px then
      st_ex_FILTER P xs (x::acc)
    else
      st_ex_FILTER P xs acc
  od)
End

(* Keep adjacency lists sorted by > *)

(* Insert an undirect edge into the adj list representation *)
Definition sorted_insert_def:
  (sorted_insert (x:num) acc [] = REVERSE (x::acc)) ∧
  (sorted_insert x acc (y::ys) =
    if x = y then REVERSE acc ++ y::ys
    else if x > y then REVERSE acc ++ x::y::ys
    else sorted_insert x (y::acc) ys)
End

Definition sorted_mem_def:
  (sorted_mem (x:num) [] = F) ∧
  (sorted_mem x (y::ys) =
    if x = y then T
    else if x > y then F
    else sorted_mem x ys)
End

Definition insert_edge_def:
  insert_edge x y =
  do
    adjx <- adj_ls_sub x;
    adjy <- adj_ls_sub y;
    do
      update_adj_ls x (sorted_insert y [] adjx);
      update_adj_ls y (sorted_insert x [] adjy)
    od
  od
End

(* insert a list of edges all adjacent to one node *)
Definition list_insert_edge_def:
  (list_insert_edge x [] = return ()) ∧
  (list_insert_edge x (y::ys) =
    do
      insert_edge x y;
      list_insert_edge x ys
    od)
End

Definition clique_insert_edge_def:
  (clique_insert_edge [] = return ()) ∧
  (clique_insert_edge (x::xs) =
  do
    list_insert_edge x xs;
    clique_insert_edge xs
  od)
End

(* assuming vertices in cli already forms a clique,
   extend it with new members
*)
Definition extend_clique_def:
  (extend_clique [] cli = return cli) ∧
  (extend_clique (x::xs) cli =
    if MEM x cli
    then
      extend_clique xs cli
    else
    do
      list_insert_edge x cli;
      extend_clique xs (x::cli)
    od)
End

(* The allocator heuristics, designed to minimize proof at the
   cost of some extra computation *)

(* (Safely) decrement the degree of all vertices adjacent to n by 1 *)
Definition dec_deg_def:
  dec_deg n =
  do
    cd <- degrees_sub n;
    update_degrees n (cd-1)
  od
End

Definition dec_degree_def:
  dec_degree n =
  do
    d <- get_dim; (* TODO: check unnecessary *)
    if n < d then
    do
      adjs <- adj_ls_sub n;
      st_ex_FOREACH adjs dec_deg
    od
    else
      return ()
  od
End

Definition add_simp_wl_def:
  add_simp_wl ls =
  do
    swl <- get_simp_wl;
    set_simp_wl (ls ++ swl)
  od
End

Definition add_spill_wl_def:
  add_spill_wl ls =
  do
    swl <- get_spill_wl;
    set_spill_wl (ls ++ swl)
  od
End

Definition add_freeze_wl_def:
  add_freeze_wl ls =
  do
    fwl <- get_freeze_wl;
    set_freeze_wl (ls ++ fwl)
  od
End

(* push x onto the stack, deleting it from "existence" *)
Definition push_stack_def:
  push_stack x =
  do
    swl <- get_stack;
    update_degrees x 0;
    update_move_related x F;
    set_stack (x::swl)
  od
End

Definition add_unavail_moves_wl_def:
  add_unavail_moves_wl ls =
  do
    swl <- get_unavail_moves_wl;
    set_unavail_moves_wl (ls ++ swl)
  od
End

(* unspill:
   Move any vertices in the spill list that has
   degree < k into the simplify or freeze worklist
   Revive all neighboring moves of these nodes
*)
Definition is_not_coalesced_def:
  is_not_coalesced d =
  do
    dt <- coalesced_sub d;
    return (d <= dt)
  od
End

Definition split_degree_def:
  split_degree d k v =
  if v < d then (* TODO: unnecessary *)
  do
    vd <- degrees_sub v;
    b <- is_not_coalesced v;
    return (vd < k ∧ b)
  od
  else
    return T
End

(* sort moves by priority *)
Definition sort_moves_def:
  sort_moves ls =
    sort (λp:num,x p',x'. p>p') ls
End

(* merge two sorted lists *)
Definition smerge_def:
  (smerge [] ys = ys) ∧
  (smerge xs [] = xs) ∧
  (smerge ((p:num,m)::xs) ((p',m')::ys) =
    if p>=p' then
      (p,m) :: smerge xs ((p',m')::ys)
    else
      (p',m') :: smerge ((p,m)::xs) ys
  )
End

(*
  revive the unavailable moves that touch each neighbor
*)
Definition revive_moves_def:
  revive_moves vs =
  do
    nbs <- st_ex_MAP adj_ls_sub vs;
    uam <- get_unavail_moves_wl;
    am <- get_avail_moves_wl;
    let fnbs = FLAT nbs in
    let (rev,unavail) = PARTITION
      (λ(_,(x,y)). sorted_mem x fnbs ∨ sorted_mem y fnbs) uam in
    let sorted = smerge (sort_moves rev) am in
    do
      set_avail_moves_wl sorted;
      set_unavail_moves_wl unavail
    od
  od
End

Definition unspill_def:
  unspill (k:num) =
  do
    d <- get_dim;
    swl <- get_spill_wl ;
    (ltk,gtk) <- st_ex_PARTITION (split_degree d k) swl [] [];
    (* The nodes in ltk have turned into low degree nodes *)
    revive_moves ltk;
    (ltkfreeze,ltksimp) <- st_ex_PARTITION (move_related_sub) ltk [] [];
    set_spill_wl gtk;
    add_simp_wl ltksimp;
    add_freeze_wl ltkfreeze
  od
End

(* simplify:
  Directly simplifies the entire list
  instead of doing it 1-by-1
  T = successful simplification
  F = no simplification
*)
Definition do_simplify_def:
  do_simplify k =
  do
    simps <- get_simp_wl;
    if NULL simps then
      return F
    else
    do
      st_ex_FOREACH simps dec_degree;
      st_ex_FOREACH simps push_stack;
      set_simp_wl [];
      unspill k;
      return T
    od
  od
End

(* increment degree of n by d *)
Definition inc_deg_def:
  inc_deg n d =
  do
    cd <- degrees_sub n;
    update_degrees n (cd+d)
  od
End

(*
  Within the allocator, we will assume that all moves
  have the form:

  1) x:=y where x is Fixed (<k) or Atemp, and y is Atemp
  2) x < y
*)

(*
  do coalesce for real :
  perform a coalesce of (x,y) by merging y into x
  - this assumes y is Atemp
  - we only "pretend" to delete y from the graph
  Case 1:
  x -> v <- y, then the degree of v is reduced by 1
  Case 2:
  x -/-> v <- y, then the degree of x is increased by 1
  Case 3:
  x -> v <-/- y, no change
  In both cases, we leave the v-y edge dangling
*)

(* An actual register *)
Definition is_Fixed_def:
  is_Fixed x =
  do
    xt <- node_tag_sub x;
    return (case xt of Fixed n => T | _ => F)
  od
End

Definition do_coalesce_real_def:
  do_coalesce_real x y case1 case2 =
  do
    (* mark y as coalesced to x *)
    update_coalesced y x;
    (*
      increment degree of x by new vertices
    *)
    bx <- is_Fixed x;
    if bx then return () else inc_deg x (LENGTH case2);
    (* add corresponding edges *)
    list_insert_edge x case2;
    st_ex_FOREACH case1 dec_deg;
    push_stack y
  od
End

(* The coalesceable criterion, Briggs and George *)

(*
  Briggs:
  the result of combining x,y should have fewer than k neighbors
  of significant degree (i.e. degree ≥ k)

  George:
  assume that x is a high degree node (typically a "Fixed" node)
  then coalescing y into x is allowed if every neighbor of y not already
  a neighbor of x (i.e. case 2) has degree < k

  TODO: The implementation here isn't super great,
  because the George check is only
  really efficient if one has a true adjacency matrix representation
*)
Definition is_Atemp_def:
  is_Atemp d =
  do
    dt <- node_tag_sub d;
    return (dt = Atemp)
  od
End

Definition is_Fixed_k_def:
  is_Fixed_k k x =
  do
    xt <- node_tag_sub x;
    return (case xt of Fixed n => n < k | _ => F)
  od
End

Definition considered_var_def:
  considered_var k x =
  do
    bx <- is_Atemp x;
    fx <- is_Fixed_k k x;
    return (bx ∨ fx)
  od
End

(* Fixed vars are treated as having infinite degree *)
Definition deg_or_inf_def:
  deg_or_inf k x =
  do
    bx <- is_Fixed_k k x;
    if bx then return k else degrees_sub x
  od
End

Definition bg_ok_def:
  bg_ok k x y =
  do
    adjx <- adj_ls_sub x;
    adjy <- adj_ls_sub y;
    (* see do_coalesce_real for the cases *)
    let (case1,case2) = PARTITION (λv. sorted_mem v adjx) adjy in
    do
      (* the "true" case1 and 2s *)
      case1 <- st_ex_FILTER (considered_var k) case1 [];
      case2 <- st_ex_FILTER (considered_var k) case2 [];
      (* Check the George criterion *)
      case2degs <- st_ex_MAP (deg_or_inf k) case2;
      let c2len = LENGTH (FILTER (λx. x >= k) case2degs) in
      if c2len = 0 then return (SOME (case1,case2)) (* george criterion*)
      else
      let case3 = FILTER (λv. ¬sorted_mem v adjy) adjx in
      do
        case3 <- st_ex_FILTER (considered_var k) case3 [];
        case1degs <- st_ex_MAP (deg_or_inf (k+1)) case1; (*k+1 is infinity here..*)
        case3degs <- st_ex_MAP (deg_or_inf k) case3;
        c1len <- return (LENGTH (FILTER (λx. x-1 >= k) case1degs));
        c3len <- return (LENGTH (FILTER (λx. x >= k) case3degs));
        if c1len+c2len+c3len < k then
          return (SOME(case1,case2))
        else
          return NONE
      od
    od
  od
End

(*
  Consistency check for moves
  Any moves failing this check can be directly discarded
  1) x ≠ y
  2) x,y must not already clash

  3) x,y either fixed or atemps and not both fixed
*)

Definition consistency_ok_def:
  consistency_ok x y =
  if x = y then
    return F (* check 1 *)
  else
  do
    adjy <- adj_ls_sub y; (* check 2 *)
    if sorted_mem x adjy then return F
    else
    do
      bx <- is_Fixed x;
      by <- is_Fixed y;
      movrelx <- move_related_sub x;
      movrely <- move_related_sub y;
      return ((bx ∨ movrelx) ∧ (by ∨ movrely) ∧ ¬(bx ∧ by) );
    od
  od
End

(*
  find the ancestor
  and collapse along the way

*)
Definition coalesce_parent_def:
  coalesce_parent x =
  do
    xt <- coalesced_sub x;
    bx <- is_Fixed xt;
    (* Special case where x is coalesced to a fixed color already *)
    if bx then
      return xt
    else
      if x <= xt then
        return x
      else
      do
        anc <- coalesce_parent xt;
        update_coalesced x anc;
        return anc
      od
  od
End

Definition canonize_move_def:
  canonize_move x y =
  do
    bx <- is_Fixed x;
    by <- is_Fixed y;
    if by then return (y,x)
    else if bx then return (x,y)
    else
      if x < y then return (x,y)
      else return (y,x)
  od
End

(*
  Picks apart the available moves worklist
  1) If we find any inconsistent ones -> throw them away
  not necessary? -- 2) canonize the move to put fixed register in front
  3) returns the first bg_ok move that is also consistent
*)
Definition st_ex_FIRST_def:
  (st_ex_FIRST P Q [] unavail = return (NONE,unavail)) ∧
  (st_ex_FIRST P Q (m::ms) unavail =
    let (p,(x,y)) = m in
    do
      x <- coalesce_parent x;
      y <- coalesce_parent y;
      b1 <- P x y;
      if ¬b1 then
        st_ex_FIRST P Q ms unavail
      else
      do
        (x,y) <- canonize_move x y;
        optb2 <- Q x y;
        case optb2 of
          NONE => st_ex_FIRST P Q ms ((p,(x,y))::unavail)
        | SOME pr =>
          return (SOME ((x,y),pr,ms),unavail)
      od
    od)
End

Definition respill_def:
  respill k x =
  do
    xd <- degrees_sub x;
    if xd < k then return ()
    else
    do
      freeze <- get_freeze_wl;
      if MEM x freeze then
      do
        add_spill_wl [x];
        set_freeze_wl (FILTER (λy. y≠x) freeze)
      od
      else return ()
    od
  od
End

Definition do_coalesce_def:
  do_coalesce k =
  do
    am <- get_avail_moves_wl;
    (ores,unavail) <- st_ex_FIRST consistency_ok (bg_ok k) am [];
    add_unavail_moves_wl unavail;
    case ores of
      NONE =>
        do
          set_avail_moves_wl [];
          return F
        od
    | SOME ((x,y),(case1,case2),ms) =>
    do
      set_avail_moves_wl ms;
      (* coalesce y into x *)
      do_coalesce_real x y case1 case2;
      unspill k;
      respill k x;
      return T
    od
  od
End

(*
  prefreeze: make the freeze and spill worklists consistent.

  If this makes a node simplifiable, then we skip freezing

  If we got here, it means coalescing failed, i.e. everything is
  an "unavailable" move now

  Here, we cleanup any potential mess in the coalescing phase
  1) Filter out all nodes y that have been coalesced
  2) delete any moves in the unavailable list, that are actually invalid
  3) mark only nodes involved in the remaining moves as "move related"
  4) simplify any resulting non-move-related nodes

*)

Definition reset_move_related_def:
  reset_move_related ls =
  do
    d <- get_dim;
    (* zero out move_related *)
    st_ex_FOREACH (COUNT_LIST d) (λx. update_move_related x F);
    (* reset to correct values *)
    st_ex_FOREACH ls (λ(_,(x,y)).
        do
          (* make sure fixed are kept as NOT move_related *)
          bx <- is_Fixed x;
          by <- is_Fixed y;
          update_move_related x (~bx);
          update_move_related y (~by)
        od)
  od
End

Definition do_prefreeze_def:
  do_prefreeze k =
  do
    fwl_pre <- get_freeze_wl;
    fwl <- st_ex_FILTER is_not_coalesced fwl_pre [];

    swl_pre <- get_spill_wl;
    swl <- st_ex_FILTER is_not_coalesced swl_pre [];
    set_spill_wl swl;

    uam_pre <- get_unavail_moves_wl;
    uam <- st_ex_FILTER (λ(_,(x,y)).consistency_ok x y) uam_pre [];
    reset_move_related uam;
    uam <- set_unavail_moves_wl uam;

    (ltkfreeze,ltksimp) <- st_ex_PARTITION (move_related_sub) fwl [] [];
    add_simp_wl ltksimp;
    set_freeze_wl ltkfreeze;
    do_simplify k
  od
End

(* if prefreeze failed, then just freeze *)

Definition do_freeze_def:
  do_freeze k =
  do
    freeze <- get_freeze_wl;
    case freeze of
      [] => return F
    | x::xs =>
      do
        dec_degree x;
        push_stack x;
        set_freeze_wl xs;
        unspill k;
        return T
      od
  od
End

(* spill:
  If given a spill cost,
    picks the cheapest node in the spill worklist,
    based on spill cost / degree
  Otherwise,
    picks highest degree node
*)
Definition safe_div_def:
  safe_div x v = if v = 0 then 0 else x DIV v
End

Definition st_ex_list_MIN_cost_def:
  (st_ex_list_MIN_cost scost [] d k v acc = return (k,acc)) ∧
  (st_ex_list_MIN_cost scost (x::xs) d k v acc =
  if x < d then
    do
      xv <- degrees_sub x;
      cost <- return (safe_div (lookup_any x scost 0n) xv);
      if v > cost then
        st_ex_list_MIN_cost scost xs d x cost (k::acc)
      else
        st_ex_list_MIN_cost scost xs d k v (x::acc)
    od
  else
    st_ex_list_MIN_cost scost xs d k v acc)
End

Definition st_ex_list_MAX_deg_def:
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
  st_ex_list_MAX_deg xs d k v acc)
End

Definition do_spill_def:
  do_spill scostopt k =
  do
    spills <- get_spill_wl;
    d <- get_dim;
    case spills of
      [] => return F
    | (x::xs) =>
      do
        xv <- degrees_sub x;
        (y,ys) <- case scostopt of
              NONE => st_ex_list_MAX_deg xs d x xv []
            | SOME scost => st_ex_list_MIN_cost scost xs d x (safe_div (lookup_any x scost 0n) xv) [];
        dec_deg y;
        push_stack y;
        set_spill_wl ys;
        unspill k;
        return T
      od
  od
End

Definition do_step_def:
  do_step scost k =
  do
    b <- do_simplify k;
    if b then return b
    else
    do
      b <- do_coalesce k;
      if b then return b
      else
      do
        b <- do_prefreeze k;
        if b then return b
        else
        do
          b <- do_freeze k;
          if b then
            return b
          else
            do
              b <- do_spill scost k;
              return b
            od
        od
      od
    od
  od
End

Definition rpt_do_step_def:
  (rpt_do_step scost k 0 = return ()) ∧
  (rpt_do_step scost k (SUC c) =
  do
    b <- do_step scost k;
    if b then rpt_do_step scost k c else return ()
  od)
End

(*
  The coloring functions
*)

(* Removing adjacent colours from ks *)
Definition remove_colours_def:
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
    od)
End

(* First colouring -- turns all Atemps into Fixeds or Stemps drawing from colors in ks *)
(* Assign a tag to an Atemp node, skipping if it is not actually an Atemp *)

Definition assign_Atemp_tag_def:
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
  od
End

(* The first allocation step *)
(* k = num registers, ls = heuristic list, prefs = coloring preference *)
Definition assign_Atemps_def:
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
  od
End

(* Default makes it easier to translate, doesn't matter for our purposes what
   the default is *)
Definition tag_col_def:
  (tag_col (Fixed n) = n) ∧
  (tag_col _ = 0n)
End

(* Find the first available in k,k+1,...
   assuming input is sorted
*)
Definition unbound_colour_def:
  (unbound_colour col [] = col) ∧
  (unbound_colour col ((x:num)::xs) =
    if col < x then
      col
    else if x = col then
      unbound_colour (col+1) xs
    else
      unbound_colour col xs)
End

(* Second colouring -- turns all Stemps into Fixed ≥ k *)
Definition assign_Stemp_tag_def:
  assign_Stemp_tag k prefs n =
  do
    ntag <- node_tag_sub n;
    case ntag of
      Stemp =>
      do
        adjs <- adj_ls_sub n;
        tags <- st_ex_MAP node_tag_sub adjs;
        let bads = sort (λx y. x≤y) (MAP tag_col tags) in
        do
          c <- prefs n bads;
          case c of
            NONE =>
              update_node_tag n (Fixed (unbound_colour k bads))
          | SOME y =>
              update_node_tag n (Fixed y)
        od
      od
    | _ => return ()
  od
End


(* The second allocation step *)
Definition assign_Stemps_def:
  assign_Stemps k prefs =
  do
    d <- get_dim;
    cs <- return (GENLIST (\x.x) d);
    st_ex_FOREACH cs (assign_Stemp_tag k prefs)
  od
End

(* Monadic biased selection oracle, finds the first matching color *)
Definition first_match_col_def:
  (first_match_col ks [] = return NONE) ∧
  (first_match_col ks (x::xs) =
    do
      c <- node_tag_sub x;
      case c of
        Fixed m =>
          if MEM m ks then return (SOME m) else first_match_col ks xs
      | _ => first_match_col ks xs
    od)
End

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

Datatype:
  clash_tree = Delta (num list) (num list) (* (Writes list, Reads list) *)
             | Set num_set (* Fixed set *)
             | Branch (num_set option) clash_tree clash_tree
             | Seq clash_tree clash_tree
             (* Binary branch, with an optional liveset at the head*)
End

(* --- clash_tree oracle checks --- *)
Definition numset_list_delete_def:
  (numset_list_delete [] (t:'a num_map) = t) ∧
  (numset_list_delete (x::xs) t = numset_list_delete xs (delete x t))
End

(*Check that a numset is injective over the clash sets in an interpreted tree*)
Definition check_col_def:
  check_col f t =
    let names = MAP (f o FST) (toAList t) in
    if ALL_DISTINCT names then
      SOME (t,fromAList (MAP (λx. (x,())) names))
    else NONE
End

Definition check_partial_col_def:
  (check_partial_col f [] t ft = SOME (t,ft)) ∧
  (check_partial_col f (x::xs) t ft =
    case lookup x t of
      SOME () => check_partial_col f xs t ft
    | NONE =>
    case lookup (f x) ft of
      NONE => check_partial_col f xs (insert x () t) (insert (f x) () ft)
    | SOME () => NONE)
End

(* The checking function, used by oracle, and also used as part of the correctness proof *)
(* live = the liveset, flive = the liveset with f applied over it*)
Definition check_clash_tree_def:
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
      check_clash_tree f t1 t2_out ft2_out)
End

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
Definition list_remap_def:
  (list_remap [] (ta,fa,nv) = (ta,fa,nv)) ∧
  (list_remap (x::xs) (ta,fa,nv) =
    case lookup x ta of
      SOME v => list_remap xs (ta,fa,nv)
    | NONE =>
      list_remap xs (insert x nv ta,insert nv x fa,nv+1))
End

Definition mk_bij_aux_def:
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
    mk_bij_aux t1 (mk_bij_aux t2 tfn))
End

Definition mk_bij_def:
  mk_bij t =
    let (ta,fa,n) = mk_bij_aux t (LN,LN,0n) in
    (ta,fa,n)
End
    (* Hide the sptree impl
    ((λi. lookup_any i ta 0),(λi. lookup_any i fa 0), n)` *)

(*Distinguish 3 kinds of variables:
  Evens are physical registers
  4n+1 are allocatable registers
  4n+3 are stack registers*)

Definition is_stack_var_def:
  is_stack_var (n:num) = (n MOD 4 = 3)
End
Definition is_phy_var_def:
  is_phy_var (n:num) = (n MOD 2 = 0)
End
Definition is_alloc_var_def:
  is_alloc_var (n:num) = (n MOD 4 = 1)
End

Theorem convention_partitions:
    ∀n. (is_stack_var n ⇔ (¬is_phy_var n) ∧ ¬(is_alloc_var n)) ∧
      (is_phy_var n ⇔ (¬is_stack_var n) ∧ ¬(is_alloc_var n)) ∧
      (is_alloc_var n ⇔ (¬is_phy_var n) ∧ ¬(is_stack_var n))
Proof
  rw[is_stack_var_def,is_phy_var_def,is_alloc_var_def,EQ_IMP_THM]
  \\ `n MOD 2 = (n MOD 4) MOD 2` by
   (ONCE_REWRITE_TAC [GSYM (EVAL ``2*2:num``)]
    \\ fs [arithmeticTheory.MOD_MULT_MOD])
  \\ fs []
  \\ `n MOD 4 < 4` by fs []
  \\ IMP_RES_TAC (DECIDE
       ``n < 4 ==> (n = 0) \/ (n = 1) \/ (n = 2) \/ (n = 3:num)``)
  \\ fs []
QED

(* Set the tags according to wordLang conventions *)
Definition mk_tags_def:
  mk_tags n fs fa =
  do
    inds <- return (GENLIST (\x.x) n);
    st_ex_FOREACH inds
    (λi.
      let v = fa i in
      let remainder = v MOD 4 in
      if remainder = 1 then
        (case lookup v fs of
          NONE => update_node_tag i Atemp
        | SOME () => update_node_tag i Stemp)
      else if remainder = 3 then
        update_node_tag i Stemp
      else
        update_node_tag i (Fixed (v DIV 2)))
  od
End

(* Initializes the clash_graph using a clash_tree and a remapping bijection *)
Definition mk_graph_def:
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
    od)
End

Definition sp_default_def:
  sp_default t i =
  (case lookup i t of NONE => if is_phy_var i then i DIV 2 else 0 | SOME x => x)
End

Definition extend_graph_def:
  (extend_graph ta [] = return ()) ∧
  (extend_graph ta ((x,y)::xs) =
  do
    insert_edge (ta x) (ta y);
    extend_graph ta xs
  od)
End

(* sets up the register allocator init state with the clash_tree input
  TODO: should the sptrees be hidden right away?
  It might be easier to transfer an sptree directly for the oracle register
  allocator

  ct = clash_tree
  forced = forced edges -- will need new proof that all forced edges are in the tree
*)
Definition init_ra_state_def:
  init_ra_state ct forced fs (ta,fa,n) =
  do
    mk_graph (sp_default ta) ct []; (* Put in the usual edges *)
    extend_graph (sp_default ta) forced;
    mk_tags n fs (sp_default fa);
  od
End

(* work around translator bug *)
Definition do_upd_coalesce_def:
  do_upd_coalesce i =
  update_coalesced i (0+i)
End

(* Initializer for the first allocation step *)
Definition init_alloc1_heu_def:
  init_alloc1_heu moves d k =
  do
    ds <- return (COUNT_LIST d);

    (* make sure move_related is correct *)
    allocs <- st_ex_FILTER is_Atemp ds []; (* only need to allocate Atemps *)

    st_ex_FOREACH ds (* Set the degree for each node *)
      (λi.
      do
        adjls <- adj_ls_sub i;
        fills <- st_ex_FILTER (λv. considered_var k v) adjls [];
        update_degrees i (LENGTH fills);
      od
      );

    st_ex_FOREACH ds do_upd_coalesce;
    set_avail_moves_wl (sort_moves moves);
    reset_move_related moves;

    (ltk,gtk) <- st_ex_PARTITION (split_degree d k) allocs [] [];
    (ltkfreeze,ltksimp) <- st_ex_PARTITION (move_related_sub) ltk [] [];
    set_spill_wl gtk;
    set_simp_wl ltksimp;
    set_freeze_wl ltkfreeze;

    return (LENGTH allocs)
  od
End

Definition do_alloc1_def:
  do_alloc1 moves scost k =
  do
    d <- get_dim;
    l <- init_alloc1_heu moves d k;
    rpt_do_step scost k l;
    st <- get_stack;
    return st
  od
End

Definition extract_tag_def:
  (extract_tag t = case t of
    Fixed m => m
  | _ => 0)
End (* never happens*)

(* return the final coloring as an sptree *)
Definition extract_color_def:
  extract_color ta =
  do
    taa <- return (toAList ta);
    itags <- st_ex_MAP (λ(k,v).
      do
        t <- node_tag_sub v;
        return (k,extract_tag t)
      od) taa; (* can make the sptree directly *)
    return (fromAList itags)
  od
End

Definition pri_move_insert_def:
  pri_move_insert p x y acc =
  case lookup x acc of
    NONE =>
      insert x [(p,y)] acc
  | SOME ls =>
      insert x ((p,y)::ls) acc
End

Definition undir_move_insert_def:
  undir_move_insert p x y acc =
    pri_move_insert p x y (pri_move_insert p y x acc)
End

Definition moves_to_sp_def:
  (moves_to_sp [] acc = acc) ∧
  (moves_to_sp (move::xs) acc =
    let (p,x,y) = move in
    moves_to_sp xs (undir_move_insert p x y acc))
End

(*Do a consistency sort after setting up the sptree of moves*)
Definition resort_moves_def:
  resort_moves acc =
  map (λls. MAP SND (sort_moves ls)) acc
End

Datatype:
  algorithm = Simple | IRC
End

(* mtable is an sptree lookup for the moves *)
Definition biased_pref_def:
  biased_pref mtable n ks =
  do
    d <- get_dim;
    if n < d then
    do
      v <- coalesced_sub n;
      let vs = case lookup n mtable of NONE => [] | SOME vs => vs in
      handle_Subscript (first_match_col ks (v::vs)) (return NONE)
    od
    else
      return NONE
  od
End

(* very similar to consistency_ok, but for initializing *)
Definition full_consistency_ok_def:
  full_consistency_ok k x y =
  if x = y then
    return F (* check 1 *)
  else
  do
    d <- get_dim;
    if x ≥ d ∨ y ≥ d then return F
    else
    do
      adjy <- adj_ls_sub y; (* check 2 *)
      if sorted_mem x adjy then return F
      else
      do
        bx <- is_Fixed_k k x;
        by <- is_Fixed_k k y;
        ax <- is_Atemp x;
        ay <- is_Atemp y;
        return ((bx ∨ ax) ∧ (by ∨ ay) ∧ ¬(bx ∧ by) );
      od
    od
  od
End

Definition update_move_def:
  update_move spta (p:num,(x:num,y:num)) =
  let spx:num = spta x in
  let spy:num = spta y in
  if spx ≤ spy then
    (p, (spx,spy))
  else
    (p, (spy,spx))
End

(* These behave in reverse to their other versions *)
Definition neg_first_match_col_def:
  (neg_first_match_col k bads [] = return NONE) ∧
  (neg_first_match_col k bads (x::xs) =
    do
      c <- node_tag_sub x;
      case c of
        Fixed m =>
          if MEM m bads ∨ m < k
          then neg_first_match_col k bads xs
          else return (SOME m)
      | _ => neg_first_match_col k bads xs
    od)
End

Definition neg_biased_pref_def:
  neg_biased_pref k mtable n bads =
  do
    d <- get_dim;
    if n < d then
    do
      let vs = case lookup n mtable of NONE => [] | SOME vs => vs in
      handle_Subscript (neg_first_match_col k bads vs) (return NONE)
    od
    else
      return NONE
  od
End

(* Putting everything together in one call *)
Definition do_reg_alloc_def:
  do_reg_alloc alg scost k moves ct forced fs (ta,fa,n) =
  do
    init_ra_state ct forced fs (ta,fa,n);
    moves0 <- return (MAP (update_move (sp_default ta)) moves);
    moves <- st_ex_FILTER (λ(_,(x,y)).full_consistency_ok k x y) moves0 [];
    ls <- do_alloc1 (if alg = Simple then [] else moves) scost k;
    mvs <- return (resort_moves (moves_to_sp moves0 LN));
    assign_Atemps k ls (biased_pref mvs);
    assign_Stemps k (neg_biased_pref k mvs);
    spcol <- extract_color ta;
    return spcol (* return the composed from wordLang into the graph + the allocation *)
  od
End

(* As we are using fixed-size array, we need to define a different record type for the initialization *)
val array_fields_names = ["adj_ls", "node_tag", "degrees","coalesced","move_related"];
val run_ira_state_def = define_run ``:ra_state``
                                       array_fields_names
                                      "ira_state";

(* The top-level (non-monadic) reg_alloc call which should be modified to fit
   the translator's requirements *)

Definition reg_alloc_aux_def:
  reg_alloc_aux alg scost k moves ct forced fs (ta,fa,n) =
    run_ira_state (do_reg_alloc alg scost k moves ct forced fs (ta,fa,n))
                      <| adj_ls    := (n, [])
                       ; node_tag  := (n, Atemp)
                       ; degrees   := (n, 0)
                       ; dim       := n
                       ; simp_wl   := []
                       ; spill_wl  := []
                       ; freeze_wl := []
                       ; avail_moves_wl   := []
                       ; unavail_moves_wl := []
                       ; coalesced := (n,0)
                       ; move_related := (n,F)
                       ; stack     := [] |>
End

Definition reg_alloc_def:
  reg_alloc alg scost k moves ct forced fs =
    reg_alloc_aux alg scost k moves ct forced fs (mk_bij ct)
End
