structure ml_monadBaseLib :> ml_monadBaseLib = struct

open preamble ml_monadBaseTheory TypeBase

fun mk_Mtype a b c = ``:^a -> (^b, ^c) exc # ^a``;

(* Creation of the raise/handle functions *)
fun define_monad_exception_functions exn_type state_type = let
    val exn_cons = TypeBase.constructors_of exn_type
    val state_var = mk_var("state", state_type)
    
    (* Raise functions *)
    fun mk_raise_fun ctor = let
	val ty = type_of ctor |> dest_type |> snd |> List.hd

	val var = mk_var("e", ty)
	val fun_body = ``\state. (Failure(^ctor ^var), state : ^(ty_antiq state_type))``

	val fun_type = mk_type("fun", [ty, type_of fun_body])
	val fun_name = "raise_" ^(dest_const ctor |> fst)
	val fun_var = mk_var(fun_name, fun_type)

	val fun_def = Define `^fun_var ^var= ^fun_body`
    in fun_def end
    val raise_funs = List.map mk_raise_fun exn_cons

    (* Handle functions *)
    fun mk_failure_success_fun ctor = let
	val ty = type_of ctor |> dest_type |> snd |> List.hd
	val ret_type = ``:('a, ^exn_type) exc``
	val ret_type_aq = ty_antiq ret_type
	val monad_ret_type = mk_type("fun", [state_type, mk_type("prod", [ret_type, state_type])])

	val var = mk_var("e", ty)
	val f_var = mk_var("f", mk_type("fun", [ty, monad_ret_type]))
	val success_fun_body = ``\^var. ^f_var ^var ^state_var``
	val failure_fun_body = ``\^var. ((Failure(^ctor ^var)) : ^ret_type_aq, ^state_var)``
    in (success_fun_body, failure_fun_body) end
    val cases_funs = List.map mk_failure_success_fun exn_cons

    val e_var = mk_var("e", exn_type)
    val case_const = mk_comb(case_const_of exn_type, e_var)

    fun mk_funs_list ((s, f)::funs) n = if n = 0 then s::(mk_funs_list funs (n-1))
				      else f::(mk_funs_list funs (n-1))
      | mk_funs_list [] n = []

    fun mk_int_list (i : int) n = if i = n then [] else i::(mk_int_list (i+1) n)
    val nl = mk_int_list 0 (List.length exn_cons)

    val funs_lists = List.map (mk_funs_list cases_funs) nl
    val funs_pairs = zip exn_cons funs_lists

    val r_var = mk_var("x", ``:('a, ^exn_type) exc``)
    val res_case_const = case_const_of ``:('a,'b) exc`` |> Term.inst [``:'b`` |-> exn_type, ``:'c`` |-> ``:('a, ^exn_type) exc # ^state_type``]
    val res_case_tm = mk_comb(res_case_const, r_var)
    val res_case_tm = mk_comb(res_case_tm, ``\x. ((Success x) : ('a, ^(ty_antiq exn_type)) exc, ^state_var)``)

    val monad_x_var = mk_var("x", mk_Mtype state_type ``:'a`` exn_type)
    val compos_param = mk_comb(monad_x_var, state_var)
    fun mk_handle_fun (ctor, funs) = let
	val ret_type = type_of ctor |> dest_type |> snd |> List.hd
	val case_tm = Term.inst [``:'a`` |-> ``:('a, ^exn_type) exc # ^state_type``] case_const

	val case_tm = list_mk_comb(case_tm, funs)
	val case_tm = mk_abs(e_var, case_tm)
	val case_tm = mk_comb(res_case_tm, case_tm)
	val case_tm = mk_abs(state_var, case_tm)
	val case_tm = mk_abs(r_var, case_tm)

	val pair_case_const = case_const_of ``:'a # 'b`` |> Term.inst [``:'b`` |-> ``:('a, ^exn_type) exc``, ``:'c`` |-> state_type, ``:'a`` |-> ``:('a, ^exn_type) exc # ^state_type``]
	val pair_case_tm = mk_comb(pair_case_const, compos_param)
	val fun_body = mk_comb(pair_case_tm, case_tm)
	val fun_body = mk_abs(state_var, fun_body)

	val ctor_name = dest_const ctor |> fst
	val fun_var_name = "handle_" ^ctor_name
	val Mtype = mk_Mtype state_type ``:'a`` exn_type
	val fun_type = ``:^Mtype -> (^ret_type -> ^Mtype) -> ^Mtype``
	val fun_var = mk_var(fun_var_name, fun_type)

	val fun_def = Define `^fun_var ^monad_x_var f = ^fun_body`
    in fun_def end
    val handle_funs = List.map mk_handle_fun funs_pairs
in zip raise_funs handle_funs end

(* Fixed stores : creation of the reference manipulation functions *)
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

(* Fixed store: creation of the array manipulation functions *)
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

(* Dynamic stores: creation of the ressource manipulation functions *)
fun create_dynamic_access_functions exn data_type = let
    val cons_list = TypeBase.constructors_of data_type
    val data_type_name = let val r = dest_thy_type data_type in #Tyop r end

    (* 'a -> data_type *)
    fun mk_create_fun ctor = let
	val ty = type_of ctor |> dest_type |> snd |> List.hd
	val type_name = let val r = dest_thy_type ty in #Tyop r end

	val var = mk_var("x", ty)
        val fun_body = mk_abs(var, mk_comb(ctor, var))

	val fun_name = data_type_name ^"_of_" ^type_name
	val fun_var = mk_var(fun_name, type_of fun_body)

	val fun_def = Define `^fun_var = ^fun_body`
    in fun_def end
    val create_funs = List.map mk_create_fun cons_list

    (* data_type -> 'a *)
    val cases_list = CONJUNCTS (case_def_of data_type) |> List.map (snd o strip_forall o concl)
    fun mk_destruct_fun case_tm = let
	val (lhs, rhs) = dest_eq case_tm
	val (case_tm, funs) = strip_comb lhs
	
	val funs = List.tl funs
	val var = mk_var("x", data_type)
	val ret_type = rand rhs |> type_of
	val ret_var = mk_var("x", ret_type)

	val res_type = ``:(^ret_type, ^(type_of exn)) exc``
        val case_tm = Term.inst [``:'a`` |-> res_type] case_tm

	val case_fun_var = rator rhs
	val case_fun = ``\x. ((Success x) : ^(ty_antiq res_type))``
	val case_tm = mk_comb(case_tm, var)

	fun add_fun (f, case_tm) =
	  if f = case_fun_var then mk_comb(case_tm, case_fun) else let
	      val param_type =
		  dest_type(dest_type (type_of case_tm) |> snd |> List.hd) |> snd |> List.hd
	      val error_fun =
                  ``\(x : ^(ty_antiq param_type)). ((Failure ^exn) : ^(ty_antiq res_type))``
          in mk_comb(case_tm, error_fun) end
	
	val case_tm = List.foldl add_fun case_tm funs
	val destruct_fun = mk_abs(var, case_tm)

	val type_name = let val r = dest_thy_type ret_type in #Tyop r end
	val destruct_fun_name = data_type_name ^"_to_" ^type_name
	val destruct_fun_var = mk_var(destruct_fun_name, type_of destruct_fun)
	val destruct_fun_def = Define `^destruct_fun_var = ^destruct_fun`
    in destruct_fun_def end

    val destruct_funs_defs = List.map mk_destruct_fun cases_list
in zip create_funs destruct_funs_defs end

end
