(*
 * A graph coloring register allocator written monadically
 * TODO: update for CakeML interface
 *)

open preamble state_transformerTheory
open ml_monadBaseLib ml_monadBaseTheory
open ml_monadStoreLib ml_monad_translatorTheory ml_monad_translatorLib

val _ = new_theory "reg_allocStateProg"
val _ = ParseExtras.temp_tight_equality();
val _ = monadsyntax.temp_add_monadsyntax()

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

val _ = hide "state";

val _ = (use_full_type_names := false);

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
              ; dim      : num
              ; node_tag : tag list
              ; degrees  : num list
              |>`;

val accessors = define_monad_access_funs ``:ra_state``;

val adj_ls_accessors = el 1 accessors;
val (adj_ls,get_adj_ls_def,set_adj_ls_def) = adj_ls_accessors;

val dim_accessors = el 2 accessors;
val (dim,get_dim_def,set_dim_def) = dim_accessors;

val node_tag_accessors = el 3 accessors;
val (node_tag,get_node_tag_def,set_node_tag_def) = node_tag_accessors;

val degrees_accessors = el 4 accessors;
val (degrees,get_degrees_def,set_degrees_def) = degrees_accessors;

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail of string | ReadError of unit | WriteError of unit`;

(* Monadic functions to handle the exceptions *)
val exn_functions = define_monad_exception_functions ``:state_exn`` ``:ra_state``;
val _ = temp_overload_on ("failwith", ``raise_Fail``);

val sub_exn = ``ReadError ()``;
val update_exn = ``WriteError ()``;
val arr_manip = define_Marray_manip_funs [adj_ls_accessors,node_tag_accessors,degrees_accessors] sub_exn update_exn;

val adj_ls_manip = el 1 arr_manip;
val node_tag_manip = el 2 arr_manip;
val degrees_manip = el 3 arr_manip;

(* Defining the allocator *)

(* Monadic for and monadic map *)
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

(* Filter one of the state arrays, returns indices satisfying P in reversed order *)
val ifilter_aux_def = Define`
  (ifilter_aux P sub 0 = return []) ∧
  (ifilter_aux P sub (SUC i) =
  do
    v <- sub i;
    rec <- ifilter_aux P sub i;
    if P v
    then return (i::rec)
    else return rec
  od)`

(* ifilter specialised for node_tag, TODO: doesn't do a reverse, but maybe not necessary *)
val ifilter_node_tag_def = Define`
  ifilter_node_tag P =
  do
    d <- get_dim;
    ls <- ifilter_aux P (\x. node_tag_sub x) d;
    return ls
  od`

(*
TODO: allocation heuristic
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

(*
val res = translate FILTER;
val res = m_translate remove_colours_def;
*)

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
      handle_ReadError (first_match_col ks vs) (λ_. return NONE)
  od`

(* Putting everything together in one call, assuming the state is set up
   properly already
   Final state should have be all Fixed registers
*)
val do_reg_alloc_def = Define`
  do_reg_alloc k mtable =
  do
    assign_Atemps k [] (biased_pref mtable);
    assign_Stemps k
  od`

(* --
compile clash_trees into a register allocator state
This produces two sptrees that re-map clash_tree variables
into the register allocator state, and vice versa
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
    (* Hide the sptree impl *)
    ((λi. lookup_any i ta 0),(λi. lookup_any i fa 0), n)`

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
      if is_phy_var v then
        update_node_tag i (Fixed (v DIV 2))
      else if is_alloc_var v then
        update_node_tag i Atemp
      else
        update_node_tag i Stemp)
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

(* sets up the register allocator init state with the clash_tree input
  TODO: this probably needs to be changed to accomodate the translator
*)
val init_ra_state_def = Define`
  init_ra_state ct =
  do
    (ta,fa,n) <- return (mk_bij ct);
    set_dim n; (* Set the size correctly *)
    alloc_adj_ls n []; (* Initialize the adj list arr *)
    alloc_node_tag n Atemp; (* Same, but for tags*)
    alloc_degrees n 0; (* Currently unused, but need it to satisfy the state relation *)
    (* At this point we should have good_ra_state *)
    mk_graph ta ct []; (* Put in the edges *)
    mk_tags n fa;
    return (ta,fa) (* Not sure what to return, probably want the mapping functions *)
  od`;

(* return the final coloring as an sptree *)
val extract_color_def = Define`
  extract_color =
  do
    d <- get_dim; (* TODO: remove d, following Son's suggestion *)
    itags <- st_ex_MAP (λi.
      do
        s <- node_tag_sub i;
        return (i,s)
      od) (GENLIST (\x.x) d); (* can make the sptree directly *)
    return (fromAList itags)
  od`

(* The top-level (monadic) reg_alloc call *)
val reg_alloc_def = Define`
  reg_alloc k mtable ct =
  do
    (ta,fa) <- init_ra_state ct;
    do_reg_alloc k mtable;
    spcol <- extract_color;
    return (ta,spcol) (* return the map from wordLang into spcol, and the allocation *)
  od`

open sortingTheory

(* Edge from node x to node y, in terms of an adjacency list *)
val has_edge_def = Define`
  has_edge adjls x y ⇔
  MEM y (EL x adjls)`

val undirected_def = Define`
  undirected adjls ⇔
  ∀x y.
    x < LENGTH adjls ∧
    y < LENGTH adjls ∧
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
    x < LENGTH adj_ls ∧
    y < LENGTH adj_ls /\
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

fun get_thms ty = { case_def = TypeBase.case_def_of ty, nchotomy = TypeBase.nchotomy_of ty }
val case_eq_thms = pair_case_eq::map (prove_case_eq_thm o get_thms)
  [``:('a,'b) exc``,``:tag``,``:'a list``] |> LIST_CONJ |> curry save_thm "case_eq_thms"

val tag_case_st = Q.store_thm("tag_case_st",`
  !t.
  (tag_CASE t a b c) f = (tag_CASE t (λn. a n f) (b f) (c f))`,
  Cases>>fs[]);

val list_case_st = Q.store_thm("list_case_st",`
  !t.
  (list_CASE t a b) f = (list_CASE t (a f) (λx y.b x y f))`,
  Cases>>fs[]);

val node_tag_sub_def = fetch "-" "node_tag_sub_def"
val adj_ls_sub_def = fetch "-" "adj_ls_sub_def"

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
    (Failure (ReadError ()),s)`,
  rw[node_tag_sub_def]>>
  fs[Marray_sub_def]);

val adj_ls_sub_eqn= Q.store_thm("adj_ls_sub_eqn[simp]",`
  adj_ls_sub n s =
  if n < LENGTH s.adj_ls then
    (Success (EL n s.adj_ls),s)
  else
    (Failure (ReadError ()),s)`,
  rw[adj_ls_sub_def]>>
  fs[Marray_sub_def]);

val update_node_tag_def = fetch "-" "update_node_tag_def"
val update_adj_ls_def = fetch "-" "update_adj_ls_def"

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
     (Failure (WriteError ()),s)`,
  rw[update_node_tag_def]>>
  fs[Marray_update_def]);

val update_adj_ls_eqn = Q.store_thm("update_adj_ls_eqn[simp]",`
  update_adj_ls n t s =
  if n < LENGTH s.adj_ls then
     (Success (),s with adj_ls := LUPDATE t n s.adj_ls)
  else
     (Failure (WriteError ()),s)`,
  rw[update_adj_ls_def]>>
  fs[Marray_update_def]);

val remove_colours_ind = theorem "remove_colours_ind";

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
  s.dim = s'.dim`,
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
    (∀m.
      if MEM m ls ∧ EL m s.node_tag = Atemp
        then EL m s'.node_tag ≠ Atemp
        else EL m s'.node_tag = EL m s.node_tag) ∧
    s.dim = s'.dim`,
  Induct>>rw[st_ex_FOREACH_def]>>
  fs msimps>>
  drule (GEN_ALL assign_Atemp_tag_correct)>>
  rpt(disch_then drule)>>
  disch_then(qspec_then`ks` assume_tac)>>fs[]>>
  first_x_assum drule>>
  rpt (disch_then drule)>>
  fs[]>>simp[]>>
  disch_then(qspec_then`ks` assume_tac)>>fs[]>>
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
  qmatch_goalsub_abbrev_tac`st_ex_FOREACH lsg`>>
  disch_then(qspecl_then[`lsg`,`ks`] assume_tac)>>
  fs[EVERY_GENLIST,Abbr`lsg`]>>
  CONJ_TAC
  >- (
    fs[EVERY_MEM,MEM_GENLIST,good_ra_state_def]>>
    CCONTR_TAC>>
    fs[MEM_EL]>>
    first_x_assum(qspec_then`n` assume_tac)>>
    rfs[]>>fs[]>>
    metis_tac[])
  >>
    fs[MEM_GENLIST,MEM_FILTER,good_ra_state_def]>>
    rw[]>>
    rpt(first_x_assum(qspec_then`m` assume_tac))>>rfs[]>>
    fs[]>>
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
  s.dim = s'.dim`,
  rw[assign_Stemp_tag_def]>>simp msimps>>
  reverse IF_CASES_TAC >- fs[good_ra_state_def]>>
  simp[]>>
  TOP_CASE_TAC>>simp msimps>>
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
        then EL m s'.node_tag ≠ Stemp
        else EL m s'.node_tag = EL m s.node_tag) ∧
    s.dim = s'.dim`,
  Induct>>rw[st_ex_FOREACH_def]>>
  fs msimps>>
  drule (GEN_ALL assign_Stemp_tag_correct)>>
  rpt(disch_then drule)>>
  disch_then(qspec_then`k` assume_tac)>>fs[]>>
  first_x_assum drule>>
  rpt (disch_then drule)>>
  fs[]>>simp[]>>
  disch_then(qspec_then`k` assume_tac)>>fs[]>>
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

val assign_Stemps_def_correct = Q.store_thm("assign_Stemps_correct",`
  good_ra_state s ∧
  no_clash s.adj_ls s.node_tag ⇒
  ∃s'.
    assign_Stemps k s = (Success (),s') ∧
    no_clash s'.adj_ls s'.node_tag ∧
    good_ra_state s' ∧
    EVERY (λn. n ≠ Stemp) s'.node_tag ∧
    ∀m.
      m < LENGTH s.node_tag ∧ EL m s.node_tag ≠ Stemp ⇒
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
  CONJ_TAC
  >- (
    fs[EVERY_MEM,MEM_GENLIST,good_ra_state_def]>>
    CCONTR_TAC>>
    fs[MEM_EL]>>
    first_x_assum(qspec_then`n` assume_tac)>>
    rfs[]>>fs[]>>
    metis_tac[])
  >>
    fs[MEM_GENLIST,MEM_FILTER,good_ra_state_def]>>
    rw[]>>
    rpt(first_x_assum(qspec_then`m` assume_tac))>>rfs[]>>
    fs[]>>
    rfs[]);

(* --  Random sanity checks that will be needed at some point -- *)

(* Checking that biased_pref satisfies good_pref *)
val first_match_col_correct = Q.prove(`
  ∀x ks s.
  ∃res. first_match_col ks x s = (res,s) ∧
  case res of
    Failure v => v = ReadError ()
  | Success (SOME k) => MEM k ks
  | _ => T`,
  Induct>>fs[first_match_col_def]>>fs msimps>>
  rw[]>>
  TOP_CASE_TAC>>fs[]>>
  IF_CASES_TAC>>fs[]);

val handle_ReadError_def = definition"handle_ReadError_def";

val good_pref_biased_pref = Q.store_thm("good_pref_biased_pref",`
  ∀t. good_pref (biased_pref t)`,
  rw[good_pref_def,biased_pref_def]>>
  TOP_CASE_TAC>>simp msimps>>
  (first_match_col_correct |> SPEC_ALL |> assume_tac)>>
  fs[]>>
  EVERY_CASE_TAC>>fs[handle_ReadError_def]);

(**)

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

(* mk_bij produces a bijection *)
val mk_bij_bij = Q.prove(`
  mk_bij ct = (ta,fa,n) ⇒
  BIJ ta {x | in_clash_tree ct x} (count n) ∧
  fa = LINV ta {x | in_clash_tree ct x}`,cheat)

val ra_state_component_equality = theorem"ra_state_component_equality"

(* All of these probably need stronger concls *)
val insert_edge_succeeds = Q.store_thm("insert_edge_succeeds",`
  good_ra_state s ∧
  y < s.dim ∧
  x < s.dim ⇒
  ∃s'. insert_edge x y s = (Success (),s') ∧
  good_ra_state s' ∧
  s' = s with adj_ls := s'.adj_ls ∧
  ∀a b. a < s.dim ∧ b < s.dim ⇒
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
  s' = s with adj_ls := s'.adj_ls
  (* ∧ ... *)
  `,
  Induct>>rw[list_insert_edge_def]>>fs msimps
  >-
    fs[ra_state_component_equality]>>
  drule (GEN_ALL insert_edge_succeeds)>>
  disch_then (qspecl_then [`h`,`x`] assume_tac)>>rfs[]>>
  last_x_assum drule>>
  qpat_x_assum`s' = _` SUBST_ALL_TAC>>fs[]);

val clique_insert_edge_succeeds = Q.store_thm("clique_insert_edge_succeeds",`
  ∀ls s.
  good_ra_state s ∧
  EVERY ( λy. y < s.dim) ls ⇒
  ∃s'. clique_insert_edge ls s = (Success (),s') ∧
  good_ra_state s' ∧
  s' = s with adj_ls := s'.adj_ls
  (* ∧ ... *)
  `,
  Induct>>rw[clique_insert_edge_def]>>fs msimps
  >-
    fs[ra_state_component_equality]>>
  drule list_insert_edge_succeeds>>
  rpt (disch_then drule)>>
  strip_tac>>simp[]>>
  last_x_assum drule>>
  qpat_x_assum`s' = _` SUBST_ALL_TAC>>fs[]);

(* TODO more properties, e.g. that the graph actually does what
   we want it to do *)
val mk_graph_succeeds = Q.store_thm("mk_graph_succeeds",`
  ∀ct ta liveout s n.
  INJ ta {x | in_clash_tree ct x} (count (LENGTH s.adj_ls)) ==>
  ∃livein s'.
    mk_graph ta ct liveout s = (Success livein,s') ∧
    undirected s'.adj_ls`, cheat);

(* --- --- *)


(* --- Translation --- *)

(* Register the types used for the translation *)
val _ = register_type ``:'a # 'b``;
val _ = register_type ``:'a list``;
val _ = register_type ``:'a option``;
val _ = register_type ``:unit``;
val _ = register_type ``:tag``;

val _ = register_exn_type ``:state_exn``;
val STATE_EXN_TYPE_def = theorem"STATE_EXN_TYPE_def";

val store_hprop_name = "RA_STATE";
val state_type = ``:ra_state``;
(* val EXN_RI = ``STATE_EXN_TYPE``; *)

(* Initializing the state monad
  - Define an initializer for each stateful component of the state
  - Pass to translate_fixed_store
    - [list of ref inits]
    - [list of array inits, along with their manipulators]
*)

(* TODO: move? *)
fun mk_ref_init (name,get,set) init = (name,init,get,set);
fun mk_arr_init (name,get,set,len,sub,upd,alloc) init = (name,init,get,set,len,sub,upd,alloc);

(* Initializers for the references *)
val init_dim_def = Define`
  init_dim = 0:num`

val refs_init_list = [mk_ref_init dim_accessors init_dim_def]

(* Initializers for the arrays *)
val init_adj_ls_def = Define`
  init_adj_ls = []:(num list) list`

val init_node_tag_def = Define`
  init_node_tag = []:tag list`

val init_degrees_def = Define`
  init_degrees = []:num list`

val arrays_init_list = List.map (uncurry mk_arr_init)
  [(adj_ls_manip,init_adj_ls_def),
   (node_tag_manip,init_node_tag_def),
   (degrees_manip,init_degrees_def)
  ];

val (init_trans, store_translation) = translate_static_init_fixed_store refs_init_list arrays_init_list store_hprop_name state_type STATE_EXN_TYPE_def

(* Initialize the translation *)
val store_exists_thm = SOME(#store_pred_exists_thm store_translation);
val exn_ri_def = STATE_EXN_TYPE_def;
val _ = init_translation init_trans store_exists_thm exn_ri_def []

(* Prove the theorems necessary to handle the exceptions *)
val (raise_functions, handle_functions) = unzip exn_functions;
val exn_ri_def = STATE_EXN_TYPE_def;
val exn_thms = add_raise_handle_functions raise_functions handle_functions exn_ri_def;

(* Rest of the translation *)
val res = m_translate st_ex_FOREACH_def;
val res = m_translate st_ex_MAP_def;
val res = m_translate ifilter_aux_def;
val res = m_translate ifilter_node_tag_def;
val res = translate FILTER;

(* Doesn't work:
val res = m_translate remove_colours_def;
val res = m_translate assign_Atemp_tag_def;
val res = m_translate assign_Atemps_def; *)

val res = translate tag_col_def;
val res = translate unbound_colour_def;
(* TODO: automate *)
val res = translate APPEND
val res = translate PART_DEF
val res = translate PARTITION_DEF
val res = translate QSORT_DEF
val res = translate MAP
val res = translate SNOC
val res = translate GENLIST
val res = translate mk_comb_PMATCHI
val res = m_translate assign_Stemp_tag_def;
val res = m_translate assign_Stemps_def;

val _ = export_theory ();
