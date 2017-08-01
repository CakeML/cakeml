(*
 * A graph coloring register allocator written monadically
 * TODO: update for CakeML interface
 *)

open preamble state_transformerTheory
open ml_monadBaseLib ml_monadBaseTheory
open ml_monadStoreLib ml_monad_translatorTheory ml_monad_translatorLib

val _ = new_theory "reg_allocStateProg"
val _ = ParseExtras.temp_loose_equality();
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
val EXN_RI = ``STATE_EXN_TYPE``;

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

val init_store = translate_fixed_store refs_init_list arrays_init_list store_hprop_name state_type STATE_EXN_TYPE_def

(* Initialize the translation *)
val _ = init_translation init_store EXN_RI []

(* Prove the theorems necessary to handle the exceptions *)
val (raise_functions, handle_functions) = unzip exn_functions;
val exn_ri_def = STATE_EXN_TYPE_def;
val exn_thms = add_raise_handle_functions raise_functions handle_functions exn_ri_def;

(* Filter one of the state arrays, returns indices satisfying P in reversed order
*)
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

(* Specialised for node_tag,
  TODO: doesn't do a reverse, but maybe not necessary *)
val ifilter_node_tag_def = Define`
  ifilter_node_tag P =
  do
    d <- get_dim;
    ls <- ifilter_aux P (\x. node_tag_sub x) d;
    return ls
  od`

(* Translation works:
val res = m_translate ifilter_aux_def;
val res = m_translate ifilter_node_tag_def;
*)

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
val assign_tag_def = Define`
  assign_tag ks n =
  do
    ntag <- node_tag_sub n;
    case ntag of
      Atemp =>
      do
        adjs <- adj_ls_sub n;
        ks <- remove_colours adjs ks;
        case ks of
          [] => update_node_tag n Stemp
        | (x::_) => update_node_tag n (Fixed x)
      od
    | _ => return ()
  od`

val st_ex_FOREACH_def = Define `
  (st_ex_FOREACH [] a = return ()) ∧
  (st_ex_FOREACH (x::xs) a =
  do
    () <- a x;
    st_ex_FOREACH xs a
  od)`

(* TODO: add a heuristic stack argument*)
val assign_Atemp_def = Define`
  assign_Atemp ks =
  do
    d <- get_dim;
    cs <- return (GENLIST I d); (* actually, assign_tag already filters for Atemps, so just pass it all the nodes *)
    st_ex_FOREACH cs (assign_tag ks)
  od`

val _ = export_theory ();
