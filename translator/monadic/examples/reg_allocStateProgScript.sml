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
    () <- a x;
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
    () <- assign_Atemps k [] (biased_pref mtable);
    () <- assign_Stemps k
  od`

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

(* Checking that biased_pref satisfies *)
val good_pref_biased_pref = Q.store_thm("good_pref_biased_pref",`
  ∀t. good_pref (biased_pref t)`,
  rw[good_pref_def,biased_pref_def]>>
  TOP_CASE_TAC>>simp msimps>>
  (first_match_col_correct |> SPEC_ALL |> assume_tac)>>
  fs[]>>
  EVERY_CASE_TAC>>fs[handle_ReadError_def]);

(* Success conditions *)

val msimps = [st_ex_bind_def,st_ex_return_def];

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
    if n = m
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
      if MEM m ls
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
    fs[]>>
    (rpt(first_x_assum (qspec_then`m` mp_tac))>>
    simp[]>>
    strip_tac>>IF_CASES_TAC>>fs[]));

val assign_Atemps_correct = Q.store_thm("assign_Atemps_correct",`
  ∀k s.
  good_ra_state s ∧
  good_pref prefs ∧
  no_clash s.adj_ls s.node_tag ==>
  ∃s'.
  assign_Atemps k ls prefs s = (Success (),s') ∧
  no_clash s'.adj_ls s'.node_tag ∧
  good_ra_state s' ∧
  EVERY (λn. n ≠ Atemp) s'.node_tag`,
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
  fs[EVERY_MEM,MEM_GENLIST,good_ra_state_def]>>
  CCONTR_TAC>>
  fs[MEM_EL]>>
  first_x_assum(qspec_then`n` assume_tac)>>
  rfs[]>>fs[]>>
  metis_tac[]);

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
