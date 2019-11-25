(*
  Proof automation for the state-and-exception monad that is supported by the
  proof-producing monadic translator.
*)

structure ml_monadBaseLib :> ml_monadBaseLib = struct

open preamble ml_monadBaseTheory TypeBase ParseDatatype Datatype packLib


(******************************************************************************

  Get constant terms and types from ml_monad_BaseTheory.
  Prevents parsing in the wrong context.

******************************************************************************)

val get_term =
  let
    val ys = unpack_list (unpack_pair unpack_string unpack_term)
               ml_monadBaseTheory.parsed_terms
  in
    fn s => snd (first (fn (n,_) => n = s) ys)
  end

val get_type =
  let
    val ys = unpack_list (unpack_pair unpack_string unpack_type)
               ml_monadBaseTheory.parsed_types
  in
    fn s => snd (first (fn (n,_) => n = s) ys)
  end

val exc_ty = get_type "exc"
val pair_ty = get_type "pair"
val a_ty = alpha
val b_ty = beta
val c_ty = gamma
val num_ty = get_type "num"
val M_ty = get_type "M"

val K_const = get_term "K"
val FST_const = get_term "FST"
val SND_const = get_term "SND"
val REPLICATE_const = get_term "REPLICATE"
val unit_const = get_term "unit"
val Failure_const = get_term "Failure"
val Success_const = get_term "Success"
val Marray_length_const = get_term "Marray_length"
val Marray_sub_const = get_term "Marray_sub"
val Marray_update_const = get_term "Marray_update"
val Marray_alloc_const = get_term "Marray_alloc"
val run_const = get_term "run"

(******************************************************************************

  Helper functions.

******************************************************************************)

fun mk_exc_type a b = Type.type_subst [a_ty |-> a, b_ty |-> b] exc_ty

(* TODO tidy *)
fun mk_Mtype a b c =
  let
    val ty = mk_exc_type b c
    val ty = mk_type ("fun", [a, mk_type ("prod", [ty, a])])
  in
    ty
  end

(* TODO tidy *)
fun mk_Failure exn x_ty =
  let
    val exn_ty = type_of exn
    val tm = Term.inst [a_ty |-> exn_ty, b_ty |-> x_ty] Failure_const
    val tm = mk_comb (tm, exn)
  in
    tm
  end

(* TODO tidy *)
fun mk_Success x exn_ty =
  let
    val x_ty = type_of x
    val tm = Term.inst [a_ty |-> x_ty, b_ty |-> exn_ty] Success_const
    val tm = mk_comb(tm, x)
  in
    tm
  end

(* TODO tidy *)
fun dest_fun_type ty =
  if can dest_type ty then
    let
      val (tys,tyl) = dest_type ty
    in
      if tys = "fun" then
        let
          val ty1 = el 1 tyl
          val ty2 = el 2 tyl
          val (params_ty, ret_ty) = dest_fun_type ty2
        in
          (ty1::params_ty, ret_ty)
        end
      else ([], ty)
    end
  else
    ([], ty)

fun mk_fun_type (tyl, ret_ty) =
  case tyl of
    ty::tyl => mk_type ("fun", [ty, mk_fun_type (tyl, ret_ty)])
  | [] => ret_ty

(*
  Like list_mk_comb, but first attempts to unify combinator/argument types.
  For combinator C and args a1, a2, a3, ... : attempts to apply
  C a1 a2 a3 ..., unifying types of expected inputs to C and types of args.
  Fails if unification fails.

  This is a very odd function in that it instantiates argument types
  "as one", rather than separately. Replacing with list_mk_ucomb fails
  however. To implement this quirk, the function creates a function type
  from all the n argument types, and does the same for the first n expected
  argument types. The two created function types are then unified to give
  the necessary substitutions.
*)
fun my_list_mk_comb (comb, []) = comb
  | my_list_mk_comb (comb, args) = let
      val comb_ty = type_of comb
      val (all_comb_arg_tys, comb_ret_ty) = dest_fun_type comb_ty
      val arg_tys = List.map type_of args
      val comb_arg_tys =
        if (length args <= length all_comb_arg_tys) then
          List.take (all_comb_arg_tys, (List.length args))
        else raise Fail "my_list_mk_comb - too many arguments"

      fun mk_fun_type [] = raise Fail "mk_fun_type" (* shouldn't happen *)
        | mk_fun_type [arg_ty] = arg_ty
        | mk_fun_type (arg_ty :: args_tys) =
            mk_type("fun", [arg_ty, mk_fun_type args_tys])

      val (f_sub, arg_sub) = sep_type_unify
                              (mk_fun_type comb_arg_tys) (mk_fun_type arg_tys)
    in
      list_mk_comb(Term.inst f_sub comb, List.map (Term.inst arg_sub) args)
    end
    handle HOL_ERR e => raise (mk_HOL_ERR "ml_monadBaseLib" "my_list_mk_comb"
                                          (#message e));

(* TODO tidy *)
fun mk_list_vars basename types =
  let
    fun mk_aux types i =
      case types of
        ty::types =>
          mk_var (basename ^ Int.toString i, ty)::(mk_aux types (i+1))
      | [] => []
  in
    mk_aux types 1
  end

(* TODO tidy *)
fun mk_list_vars_same basename ty n =
  let
    fun mk_aux i =
      if i > n then
        []
      else
        mk_var(basename ^ (Int.toString i), ty)::(mk_aux (i+1))
  in
    mk_aux 1
  end

(* TODO tidy *)
(* Creation of the raise/handle functions *)
fun define_monad_exception_functions exn_type state_type =
  let
    val exn_cons = TypeBase.constructors_of exn_type
    val state_var = mk_var("state", state_type)

    (* Raise functions *)
    fun mk_raise_fun ctor =
      let
        val (params_ty, ret_ty) = dest_fun_type (type_of ctor)
        val vars = mk_list_vars "e" params_ty
        val fun_body = list_mk_comb (ctor, vars)
        val fun_body = mk_pair(mk_Failure fun_body a_ty, state_var)
        val fun_body = mk_abs(state_var, fun_body)
        val fun_name = "raise_" ^(dest_const ctor |> fst)
        val fun_type = mk_fun_type(params_ty, type_of fun_body)
        val fun_var = mk_var(fun_name, fun_type)
        val def_lhs = list_mk_comb (fun_var, vars)
        val def_eq = mk_eq (def_lhs, fun_body)
        val fun_def = Define `^def_eq`
      in
        fun_def
      end
    val raise_funs = List.map mk_raise_fun exn_cons

    (* Handle functions *)
    fun mk_failure_success_fun ctor =
      let
        val (params_ty, ret_ty) = dest_fun_type (type_of ctor)
        val vars = mk_list_vars "e" params_ty
        val ret_type = mk_exc_type a_ty exn_type
        val monad_ret_type = mk_type ("fun", [state_type, mk_type("prod", [ret_type, state_type])])
        val f_type = mk_fun_type (params_ty, monad_ret_type)
        val f_var = mk_var("f", f_type)

        val success_fun_body = list_mk_comb(f_var,vars)
        val success_fun_body = mk_comb(success_fun_body, state_var)
        val success_fun_body = list_mk_abs(vars, success_fun_body)

        val failure_fun_body = mk_Failure (list_mk_comb (ctor, vars)) a_ty
        val failure_fun_body = mk_pair(failure_fun_body, state_var)
        val failure_fun_body = list_mk_abs(vars, failure_fun_body)
      in
        (success_fun_body, failure_fun_body)
      end
    val cases_funs = List.map mk_failure_success_fun exn_cons

    val e_var = mk_var("e", exn_type)
    val case_expr = mk_comb(case_const_of exn_type, e_var)

    fun mk_funs_list [] n = []
      | mk_funs_list ((s, f)::funs) n =
          if n = 0 then
            s::(mk_funs_list funs (n-1))
          else
            f::(mk_funs_list funs (n-1))

    fun mk_int_list (i : int) n = if i = n then [] else i::(mk_int_list (i+1) n)

    val nl = mk_int_list 0 (List.length exn_cons)
    val funs_lists = List.map (mk_funs_list cases_funs) nl
    val funs_pairs = zip exn_cons funs_lists

    (* x *)
    val exc_type = mk_exc_type a_ty exn_type
    val pair_exc_type = mk_type("prod", [exc_type, state_type])
    val monad_type = mk_type("fun", [state_type, pair_exc_type])

    val x_var = mk_var("x", monad_type)

    (* case x st of (res, st) => ... *)
    val x_st_tm = mk_comb(x_var, state_var)
    val case_x_st_tm = case_const_of pair_ty |>
        Term.inst [alpha |-> pair_exc_type, beta |-> exc_type, gamma |-> state_type]
    val case_x_st_tm = mk_comb(case_x_st_tm, x_st_tm)
    val res_var = mk_var("res", exc_type)

    (*
       case res of
         Success y => (Success y, st)
       | Failure e => ... *)
    val case_res_tm = case_const_of exc_type |>
        Term.inst [beta |-> exn_type, gamma |-> pair_exc_type]
    val y_var = mk_var ("y", a_ty)
    val success_tm = mk_abs(y_var, mk_pair((mk_Success y_var exn_type), state_var))
    val case_res_tm = mk_comb(case_res_tm, res_var)
    val case_res_tm = mk_comb(case_res_tm, success_tm)

    val e_var = mk_var("e", exn_type)

    (* case e of *)
    val exn_case_tm = case_const_of exn_type
                   |> Term.inst [alpha |-> pair_exc_type]
    val exn_case_tm = mk_comb(exn_case_tm, e_var)

    (* For every constructor, make the approriate case function *)
    fun mk_handle_fun (ctor, funs_list) =
      let
        val case_tm = list_mk_comb (exn_case_tm, funs_list)
        val case_tm = mk_comb(case_res_tm, mk_abs(e_var, case_tm))
        val case_tm = list_mk_abs([res_var,state_var], case_tm)
        val case_tm = mk_comb(case_x_st_tm, case_tm)
        val case_tm = mk_abs(state_var, case_tm)

        val Mtype = mk_Mtype state_type a_ty exn_type
        val params_types = fst(dest_fun_type (type_of ctor))
        val ftype = mk_fun_type(params_types, Mtype)
        val fvar = mk_var("f", ftype)

        val ctor_name = dest_const ctor |> fst
        val handle_fun_var_name = "handle_" ^ctor_name
        val handle_fun_type = mk_fun_type([Mtype, ftype], Mtype)
        val handle_fun_var = mk_var(handle_fun_var_name, handle_fun_type)

        val def_lhs = list_mk_comb(handle_fun_var, [x_var, fvar])
        val def_eq = mk_eq(def_lhs, case_tm)
        val def = Define `^def_eq`
      in
        def
      end
    val handle_funs = List.map mk_handle_fun funs_pairs
  in
    zip raise_funs handle_funs
  end

(* TODO tidy *)
(* Fixed stores : creation of the reference manipulation functions *)
fun define_monad_get_fun (name, get_fun) =
  let
    val state_var = mk_var("state", dest_type(type_of get_fun) |> snd |> hd)
    val monad_get_fun = mk_abs(state_var, mk_pair(mk_Success (mk_comb (get_fun, state_var)) c_ty, state_var))
    val monad_get_fun =
      (DEPTH_CONV BETA_CONV) monad_get_fun |> concl |> dest_eq |> snd
      handle UNCHANGED => monad_get_fun
    val monad_get_fun_name = "get_" ^ name
    val monad_get_fun_var = mk_var(monad_get_fun_name, type_of monad_get_fun)
    val monad_get_fun_def = Define `^monad_get_fun_var = ^monad_get_fun`
  in
    monad_get_fun_def
  end;

(* TODO tidy *)
fun define_monad_set_fun (name, set_fun) =
  let
    val param_type = dest_abs set_fun |> fst |> type_of
    val set_fun1 = mk_comb(set_fun, mk_var("x", param_type)) |> BETA_CONV |> concl |> rhs
    val state_ty = dest_type(type_of set_fun) |> snd |> last |> dest_type |> snd |> hd
    val state_var = mk_var("state", state_ty)
    val partial_set_fun = mk_abs(state_var, mk_pair(mk_Success unit_const c_ty, mk_comb(set_fun1, state_var)))
    val monad_set_fun_name = "set_" ^ name
    val monad_set_fun_var = mk_var(monad_set_fun_name,
                            mk_type("fun", [param_type, type_of partial_set_fun]))
    val x_var = mk_var("x", param_type)
    val monad_set_fun_eq = mk_eq(mk_comb(monad_set_fun_var, x_var), partial_set_fun)
    val monad_set_fun_def = Define `^monad_set_fun_eq`
  in
    monad_set_fun_def
  end;

(* TODO tidy *)
fun define_monad_access_funs data_type =
  let
    val accessors =
      List.map (rator o lhs o snd o strip_forall o concl)
        (accessors_of data_type)
    val updates =
      List.map (rator o rator o lhs o snd o strip_forall o concl)
        (updates_of data_type)
(*
    (* TODO check this works for all cases *)
    val ty_subst =
      match_type
        (accessors_of data_type |> hd |> SPEC_ALL |> concl |> lhs |>
         rator |> type_of |> dom_rng |> fst)
        data_type

    val accessors = List.map (Term.inst ty_subst) accessors
    val updates = List.map (Term.inst ty_subst) updates
*)
    fun abstract_update set_f =
      let
        val ty = dest_type (type_of set_f) |> snd |> List.hd |> dest_type |> snd |> List.hd
        val var = mk_var("x", ty)
        val app_K_var = mk_ucomb(K_const, var)
        val set_f_inp_ty = set_f |> type_of |> dom_rng |> fst
        val ty_subst = (match_type set_f_inp_ty (type_of(app_K_var))
          handle _ => [])
        val set_f' = inst ty_subst set_f
        val ty_subst = (match_type (type_of (app_K_var)) set_f_inp_ty
          handle _ => [])
        val app_K_var' = inst ty_subst app_K_var
      in
        mk_abs(inst ty_subst var, mk_comb(set_f', app_K_var'))
      end

    val abs_updates = List.map abstract_update updates

    val names = List.map fst (fields_of data_type)

    val get_info = zip names accessors
    val set_info = zip names abs_updates

    val get_funs = List.map define_monad_get_fun get_info
    val set_funs = List.map define_monad_set_fun set_info

    fun zip3 (x1::l1) (x2::l2) (x3::l3) = (x1, x2, x3)::(zip3 l1 l2 l3)
      | zip3 [] [] [] = []
      | zip3 _  _  _  = failwith "zip3 given lists of different lengths"
  in
    zip3 names get_funs set_funs
  end;

(* TODO tidy *)
(* Fixed store: creation of the fixed-size array manipulation functions *)
fun define_MFarray_manip_funs_aux sub_exn update_exn (name, get_fun_def, set_fun_def) =
  let
    val state = concl get_fun_def |> rhs |> dest_abs |> fst
    val get_fun = concl get_fun_def |> rhs |> dest_abs |> snd |> dest_pair |> fst |> rand
    val get_fun = mk_abs(state, get_fun)

    val x = concl set_fun_def |> dest_forall |> fst
    val set_fun = concl set_fun_def |> strip_forall |> snd |> rhs
    val state = dest_abs set_fun |> fst
    val set_fun = dest_abs set_fun |> snd |> dest_pair |> snd
    val set_fun = mk_abs(x, mk_abs(state, set_fun))

    (* length *)
    val length_f = my_list_mk_comb(Marray_length_const, [get_fun])
    val length_v = mk_var(name ^"_length", type_of length_f)
    val length_def = Define `^length_v = ^length_f`

    (* sub *)
    val sub_f = my_list_mk_comb(Marray_sub_const, [get_fun, sub_exn])
    val sub_v = mk_var(name ^"_sub", type_of sub_f)
    val sub_def = Define `^sub_v = ^sub_f`

    (* update *)
    val update_f = my_list_mk_comb(Marray_update_const, [get_fun, set_fun, update_exn])
    val update_v = mk_var("update_" ^name, type_of update_f)
    val update_def = Define `^update_v = ^update_f`

    (* TODO: resize *)
  in
    (name, get_fun_def, set_fun_def, length_def, sub_def, update_def)
  end;

(* TODO tidy *)
(* Fixed store: creation of the resizable array manipulation functions *)
fun define_MRarray_manip_funs_aux sub_exn update_exn (name, get_fun_def, set_fun_def) =
  let
    val x = concl set_fun_def |> dest_forall |> fst
    val set_fun = concl set_fun_def |> strip_forall |> snd |> rhs
    val state = dest_abs set_fun |> fst
    val set_fun = dest_abs set_fun |> snd |> dest_pair |> snd
    val set_fun = mk_abs(x, mk_abs(state, set_fun))

    val (name, get_fun_def, set_fun_def, length_def, sub_def, update_def) =
      define_MFarray_manip_funs_aux
        sub_exn update_exn (name, get_fun_def, set_fun_def)

    (* alloc *)
    val alloc_f = my_list_mk_comb(Marray_alloc_const, [set_fun])
    val alloc_v = mk_var("alloc_" ^name, type_of alloc_f)
    val alloc_def = Define `^alloc_v = ^alloc_f`

    (* TODO: resize *)
  in
    (name, get_fun_def, set_fun_def, length_def, sub_def, update_def, alloc_def)
  end;

fun define_MFarray_manip_funs array_access_funs sub_exn update_exn =
  List.map (define_MFarray_manip_funs_aux sub_exn update_exn) array_access_funs;

fun define_MRarray_manip_funs array_access_funs sub_exn update_exn =
  List.map (define_MRarray_manip_funs_aux sub_exn update_exn) array_access_funs;

(* TODO tidy *)
(*
 * With fixed-size, locally defined arrays, we define a new data-type for the
 * initialization, where the initialization values for the arrays are pairs
 * (initial_value, size), together with a dedicated run function.
 *)
fun define_run state array_fields new_state_name =
  let
    (*
      val (state, array_fields, new_state_name) = (state_type, ["farr"], "init_state")
    *)

    val fields = fields_of state
    val accessors = accessors_of state
    val type_info = zip fields accessors
    val ntype_var = mk_vartype ("'" ^ new_state_name)

    fun mk_field (field_name, {ty = field_type, ...}) =
      if mem field_name array_fields then
        let (* create a field (init_value, size) *)
          val (type_cons, elem_type) = dest_type field_type
          val _ = if type_cons <> "list" then failwith ("define_local_init_state : trying to define an array from a field which is not a list : " ^field_name) else ()
          val elem_type = hd elem_type
          val ty = mk_type ("prod", [num_ty, elem_type])
        in
          (field_name, dAQ ty)
        end
        (* keep the same field *)
      else
        (field_name, dAQ field_type)

    (* Define the new data_type *)
    val fields_info = List.map mk_field fields
    val type_info = (new_state_name, Record fields_info)
    val _ = astHol_datatype [type_info]

    (* Define the run function *)
    (* OLD:
    val new_state = mk_type(new_state_name, [])
    *)
    val new_state = mk_type(new_state_name, type_vars state)
    val state_cons = List.hd (constructors_of state)
    val new_fields = fields_of new_state
    val new_state_var = mk_var("state", new_state)

    fun mk_new_field (field_name, {ty = field_type, accessor, ...}) =
      if mem field_name array_fields then
        let
          val elem_type = dest_type field_type |> snd |> List.last
          val field_tm = mk_ucomb(accessor, new_state_var)
          val length_tm = mk_ucomb(FST_const, field_tm)
          val elem_tm = mk_ucomb(SND_const, field_tm)
          val tm = list_mk_ucomb (REPLICATE_const, [length_tm, elem_tm])
        in
          tm
        end
      else
        mk_ucomb(accessor, new_state_var)
    val new_fields = List.map mk_new_field new_fields
    val synth_state = list_mk_ucomb (state_cons, new_fields)
    val x_var = mk_var("x", type_subst [alpha |-> state] M_ty)
    val body = list_mk_ucomb(run_const, [x_var, synth_state])

    val new_run_type = list_mk_fun([type_of x_var, new_state], type_of body)
    val new_run_var = mk_var("run_" ^ new_state_name, new_run_type)
    val eq = mk_eq(list_mk_comb(new_run_var, [x_var, new_state_var]), body)
    val run_def = Define `^eq`
  in
    run_def
  end

(* Dynamic stores: creation of the ressource manipulation functions *)
fun create_dynamic_access_functions exn data_type =
  let
    val cons_list = TypeBase.constructors_of data_type
    val data_type_name = let val r = dest_thy_type data_type in #Tyop r end

    (* 'a -> data_type *)
    fun mk_create_fun ctor =
      let
        val ty = type_of ctor |> dest_type |> snd |> List.hd
        val type_name = let val r = dest_thy_type ty in #Tyop r end
        val var = mk_var("x", ty)
        val fun_body = mk_abs(var, mk_comb(ctor, var))
        val fun_name = data_type_name ^"_of_" ^type_name
        val fun_var = mk_var(fun_name, type_of fun_body)
        val fun_def = Define `^fun_var = ^fun_body`
      in
        fun_def
      end
    val create_funs = List.map mk_create_fun cons_list

    (* data_type -> 'a *)
    val cases_list = CONJUNCTS (case_def_of data_type) |> List.map (snd o strip_forall o concl)
    fun mk_destruct_fun case_tm =
      let
        val (lhs, rhs) = dest_eq case_tm
        val (case_tm, funs) = strip_comb lhs

        val funs = List.tl funs
        val var = mk_var("x", data_type)
        val ret_type = rand rhs |> type_of
        val ret_var = mk_var("x", ret_type)

        val res_type = mk_exc_type ret_type (type_of exn)
        val case_tm = Term.inst [a_ty |-> res_type] case_tm

        val case_fun_var = rator rhs
        val x_var = mk_var("x", ret_type)
        val case_fun = mk_abs(x_var, mk_Success x_var (type_of exn))
        val case_tm = mk_comb(case_tm, var)

        fun add_fun (f, case_tm) =
          if f ~~ case_fun_var then
            mk_comb(case_tm, case_fun)
          else
            let
              val param_type =
                  dest_type(dest_type (type_of case_tm) |> snd |> List.hd) |> snd |> List.hd
              val x_var = mk_var("x", param_type)
              val error_fun = mk_abs(x_var, mk_Failure exn ret_type)
            in
              mk_comb(case_tm, error_fun)
            end

        val case_tm = List.foldl add_fun case_tm funs
        val destruct_fun = mk_abs(var, case_tm)

        val type_name = let val r = dest_thy_type ret_type in #Tyop r end
        val destruct_fun_name = data_type_name ^"_to_" ^type_name
        val destruct_fun_var = mk_var(destruct_fun_name, type_of destruct_fun)
        val destruct_fun_def = Define `^destruct_fun_var = ^destruct_fun`
      in
        destruct_fun_def
      end

    val destruct_funs_defs = List.map mk_destruct_fun cases_list
  in
    zip create_funs destruct_funs_defs
  end

end

