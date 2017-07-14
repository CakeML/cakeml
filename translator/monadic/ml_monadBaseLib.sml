structure ml_monadBaseLib :> ml_monadBaseLib = struct

open preamble ml_monadBaseTheory TypeBase

fun define_monad_get_fun (name, get_fun) = let
  val return_type_aq = type_of get_fun |> dest_type |> snd |> List.tl |> List.hd |> ty_antiq
  val monad_get_fun = ``(\state. (Success (^get_fun state), state))``
  val monad_get_fun = (DEPTH_CONV BETA_CONV) monad_get_fun |> concl |> dest_eq |> snd
		      handle UNCHANGED => monad_get_fun
  val monad_get_fun_name = "get_" ^ name
  val monad_get_fun_var = mk_var(monad_get_fun_name, type_of monad_get_fun)
  val monad_get_fun_def = Define `^monad_get_fun_var = ^monad_get_fun`
in monad_get_fun_def end;

fun define_monad_set_fun (name, set_fun) = let
  val param_type = dest_abs set_fun |> fst |> type_of
  val set_fun1 = mk_comb(set_fun, mk_var("x", param_type)) |> BETA_CONV |> concl |> rhs
  val partial_set_fun = ``\state. (Success (), ^set_fun1 state)``
  val monad_set_fun_name = "set_" ^ name
  val monad_set_fun_var = mk_var(monad_set_fun_name,
                          mk_type("fun", [param_type, type_of partial_set_fun]))
  val monad_set_fun_eq = ``^monad_set_fun_var x = ^partial_set_fun``
  val monad_set_fun_def = Define `^monad_set_fun_eq`
in monad_set_fun_def end;

val K_tm = ``K : 'a -> 'a -> 'a``;
fun define_monad_access_funs data_type = let
    val accessors = List.map (rator o lhs o snd o strip_forall o concl) (accessors_of data_type)
    val updates = List.map (rator o rator o lhs o snd o strip_forall o concl) (updates_of data_type)

    fun abstract_update set_f = let
	val ty = dest_type (type_of set_f) |> snd |> List.hd |> dest_type |> snd |> List.hd
	val tyK = Term.inst [``:'a`` |-> ty] K_tm
	val var = mk_var("x", ty)
        val set_f' = mk_abs(var, mk_comb(set_f, mk_comb(tyK, var)))
    in set_f' end

    val abs_updates = List.map abstract_update updates

    val names = List.map fst (fields_of data_type)

    val get_info = zip names accessors
    val set_info = zip names abs_updates

    val get_funs = List.map define_monad_get_fun get_info
    val set_funs = List.map define_monad_set_fun set_info
  
    fun zip3 (x1::l1) (x2::l2) (x3::l3) = (x1, x2, x3)::(zip3 l1 l2 l3)
      | zip3 [] [] [] = []
in zip3 names get_funs set_funs end;

fun define_Marray_manip_funs_aux sub_exn update_exn (name, get_fun_def, set_fun_def) = let
    val state = concl get_fun_def |> rhs |> dest_abs |> fst
    val get_fun = concl get_fun_def |> rhs |> dest_abs |> snd |> dest_pair |> fst |> rand
    val get_fun = mk_abs(state, get_fun)

    val x = concl set_fun_def |> dest_forall |> fst
    val set_fun = concl set_fun_def |> strip_forall |> snd |> rhs
    val state = dest_abs set_fun |> fst
    val set_fun = dest_abs set_fun |> snd |> dest_pair |> snd
    val set_fun = mk_abs(x, mk_abs(state, set_fun))

    (* length *) 
    val length_f = ``Marray_length ^get_fun``
    val length_v = mk_var(name ^"_length", type_of length_f)
    val length_def = Define `^length_v = Marray_length ^get_fun`

    (* sub *)
    val sub_f = ``Marray_sub ^get_fun ^sub_exn``
    val sub_v = mk_var(name ^"_sub", type_of sub_f)
    val sub_def = Define `^sub_v = ^sub_f`

    (* update *)
    val update_f = ``Marray_update ^get_fun ^set_fun ^update_exn``
    val update_v = mk_var("update_" ^name, type_of update_f)
    val update_def = Define `^update_v = ^update_f`

    (* alloc *)
    val alloc_f = ``Marray_alloc ^set_fun``
    val alloc_v = mk_var("alloc_" ^name, type_of alloc_f)
    val alloc_def = Define `^alloc_v = ^alloc_f`

     (* TODO: resize *)
in (name, get_fun_def, set_fun_def, length_def, sub_def, update_def, alloc_def) end;

fun define_Marray_manip_funs array_access_funs sub_exn update_exn =
  List.map (define_Marray_manip_funs_aux sub_exn update_exn) array_access_funs;

end
