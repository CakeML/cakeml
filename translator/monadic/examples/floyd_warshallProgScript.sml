(*
 * Trying out the monadic translator
 *)

open preamble state_transformerTheory
open ml_monadBaseLib ml_monadBaseTheory
open ml_monadStoreLib ml_monad_translatorTheory ml_monad_translatorLib

val _ = new_theory "floyd_warshallProg"
val _ = ParseExtras.temp_loose_equality();
val _ = monadsyntax.temp_add_monadsyntax()

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

val _ = hide "state";

val _ = (use_full_type_names := false);

(* An adjacency matrix represented as a 1D-array with a dimension var *)
val _ = Hol_datatype `
  graph = <| adj_mat : (num option) list
           ; dim     : num
           |>`;

val accessors = define_monad_access_funs ``:graph``;

val adj_mat_accessors = el 1 accessors;
val (adj_mat,get_adj_mat_def,set_adj_mat_def) = adj_mat_accessors;

val dim_accessors = el 2 accessors;
val (dim,get_dim_def,set_dim_def) = dim_accessors;

(* Create the data type to handle the references *)
(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail of string | Subscript`;

(* Monadic functions to handle the exceptions *)
val exn_functions = define_monad_exception_functions ``:state_exn`` ``:graph``;
val _ = temp_overload_on ("failwith", ``raise_Fail``);

val sub_exn = ``Subscript``;
val update_exn = ``Subscript``;
val arr_manip = define_MRarray_manip_funs [adj_mat_accessors] sub_exn update_exn;

val adj_mat_manip = el 1 arr_manip;

(* Register the types used for the translation *)
val _ = register_type ``:'a # 'b``;
val _ = register_type ``:'a list``;
val _ = register_type ``:'a option``;
val _ = register_type ``:unit``;

val _ = register_exn_type ``:state_exn``;
val STATE_EXN_TYPE_def = theorem"STATE_EXN_TYPE_def";

val store_hprop_name = "GRAPH";
val state_type = ``:graph``;
val EXN_RI = ``STATE_EXN_TYPE``;

(* Initializing the state monad
  - Define an initializer for each stateful component of the state
  - Pass to translate_fixed_store
    - [list of ref inits]
    - [list of array inits, along with their manipulators]
*)

(* TODO: move? *)
fun mk_ref_init (name,get,set) init = (name,init,get,set);
fun mk_rarr_init (name,get,set,len,sub,upd,alloc) init = (name,init,get,set,len,sub,upd,alloc);

(* Initializers for the references *)
val init_dim_def = Define`
  init_dim = 0:num`

val refs_init_list = [mk_ref_init dim_accessors init_dim_def]

(* Initializers for the arrays *)
val init_adj_mat_def = Define`
  init_adj_mat = []:(num option) list`

val rarrays_init_list = [mk_rarr_init adj_mat_manip init_adj_mat_def]
val farrays_init_list = [] : (string * (int * thm) * thm * thm * thm * thm * thm) list;

val (init_trans, store_translation, exn_thms) =
    start_static_init_fixed_store_translation refs_init_list
					      rarrays_init_list
					      farrays_init_list
					      store_hprop_name
					      state_type
					      STATE_EXN_TYPE_def
					      exn_functions
					      [] NONE NONE;

(* Interacting with the graph component of the state monad *)

(* allocate an n x n matrix *)
val mk_graph_def = Define`
  mk_graph n =
  do
    () <- set_dim n;
    alloc_adj_mat (n * n) NONE
  od`

(* Because we are using a 1D array to represent 2D*)
val reind_def = Define`
  reind (i:num) j =
  do
    d <- get_dim;
    return (i*d+j)
  od`

(* Make (i,j) adjacent with weight w *)
val set_weight_def = Define`
  set_weight i j w =
  do
    pij <- reind i j;
    update_adj_mat pij (SOME w)
  od`

(* Returns the weight of (i,j) *)
val get_weight_def = Define`
  get_weight i j =
  do
    pij <- reind i j;
    adj_mat_sub pij
  od`

val st_ex_FOR_def = tDefine "st_ex_FOR" `
  st_ex_FOR (i:num) j a =
  if i >= j then
    return ()
  else
    do
      () <- a i;
      st_ex_FOR (i+1) j a
    od`
  (WF_REL_TAC `measure (\(i, j:num, a).  j-i)`);

val st_ex_FOREACH_def = Define `
  (st_ex_FOREACH [] a = return ()) ∧
  (st_ex_FOREACH (x::xs) a =
  do
    () <- a x;
    st_ex_FOREACH xs a
  od)`

(* Initialize the diagonal to zero *)
val init_diag_def = Define`
  init_diag d =
  do
    st_ex_FOR 0n d (λi. set_weight i i 0n)
  od`

(* TODO: defining it as :
  init_diag =
  do
    d <- get_dim
    ...
  od
  fails

  Similarly,
  init_diag () = ...
  fails too (I think this was fixed on master's translator..)
*)

(* Floyd-Warshall algorithm *)

val relax_def = Define`
  relax i k j =
  do
    wik <- get_weight i k;
    wkj <- get_weight k j;
    wij <- get_weight i j;
    case (wik,wkj,wij) of
      (NONE,_,_) => return ()
    | (_,NONE,_) => return ()
    | (SOME wik,SOME wkj,NONE) => set_weight i j (wik+wkj) (* Infinity *)
    | (SOME wik,SOME wkj,SOME wij) =>
      if wik + wkj < wij
      then set_weight i j (wik+wkj)
      else return ()
 od`

(* TODO: same as init_diag *)
val floyd_warshall_def = Define`
  floyd_warshall d =
  do
    st_ex_FOR 0n d (λk.
    st_ex_FOR 0n d (λi.
    st_ex_FOR 0n d (λj.
      relax i k j
    )
    )
    )
  od`

val init_g_def = Define`
  init_g =  <|dim :=init_dim ; adj_mat := init_adj_mat |>`

val init_from_ls_def = Define`
  init_from_ls ls =
  do
    d <- get_dim;
    () <- init_diag d;
    st_ex_FOREACH ls (\(i,j,w). set_weight i j w)
  od`

val do_floyd_def = Define`
  do_floyd d ls =
  do
    () <- mk_graph d;
    () <- init_from_ls ls;
    () <- floyd_warshall d;
  od`

val alloc_adj_mat_def = definition "alloc_adj_mat_def";
val get_dim_def = definition "get_dim_def";
val st_ex_FOR_ind = theorem"st_ex_FOR_ind";

val msimps = [st_ex_bind_def,st_ex_FOR_def]

val _ = temp_tight_equality();

val mk_graph_SUCCESS = Q.store_thm("mk_graph_SUCCESS",`
  ∃res.
    (mk_graph d s = (Success ():(unit,state_exn) exc,res)) ∧
    d*d ≤ LENGTH res.adj_mat`,
  fs[mk_graph_def]>>
  fs(msimps)>>
  fs [alloc_adj_mat_def,set_dim_def,Marray_alloc_def,LENGTH_REPLICATE]);

(* Prove that the algorithm is always successful (?) *)
val do_floyd_SUCCESS = Q.store_thm("do_floyd_SUCCESS",`
  EVERY (λ (i,j,w). i < d ∧ j < d) ls ⇒
  ∃res.
  do_floyd d ls init_g = (Success (),res)`,
  rw[]>>
  simp[do_floyd_def,init_g_def]>>
  simp msimps>>
  TOP_CASE_TAC >>
  reverse TOP_CASE_TAC
  >-
    (qmatch_asmsub_abbrev_tac`mk_graph d s`>>
    assume_tac mk_graph_SUCCESS>>
    fs[]>>fs[])
  >>
  TOP_CASE_TAC>>
  cheat);

val res = m_translate mk_graph_def;
val res = m_translate reind_def;
val res = m_translate set_weight_def;
val res = m_translate get_weight_def;
val res = m_translate st_ex_FOR_def;
val res = m_translate st_ex_FOREACH_def;
val res = m_translate init_diag_def;
val res = m_translate relax_def;
val res = m_translate floyd_warshall_def;
val res = m_translate init_from_ls_def;
val res = m_translate do_floyd_def;

(* TODO: What to do from here onwards?
val ML_code(_,_,_,th) = (get_ml_prog_state());
val prog_with_snoc = th |> concl |> find_term listSyntax.is_snoc
val prog_rewrite = EVAL prog_with_snoc |> concl |> rhs

val _ = set_trace "pp_avoids_symbol_merges" 0
val _ = astPP.enable_astPP()
*)

val _ = export_theory ();
