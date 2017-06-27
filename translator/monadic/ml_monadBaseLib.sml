structure ml_monadBaseLib :> ml_monadBaseLib = struct

open preamble ml_monadBaseTheory

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
  val partial_set_fun = ``\state. (Success (), ^set_fun x state)``
  (* val exn_poly_type = type_of partial_set_fun |> dest_type |> snd |> List.last |> dest_type |> snd |> List.hd |> dest_type |> snd |> List.last *)
  
  val monad_set_fun_name = "set_" ^ name
  val monad_set_fun_var = mk_var(monad_set_fun_name,
                          mk_type("fun", [param_type, type_of partial_set_fun]))
  val monad_set_fun_eq = ``^monad_set_fun_var x = ^partial_set_fun``
  val monad_set_fun_def = Define `^monad_set_fun_eq`
in monad_set_fun_def end;

fun define_monad_access_funs (name, get_fun, set_fun) = let
    val get_fun_def = define_monad_get_fun (name, get_fun)
    val set_fun_def = define_monad_set_fun (name, set_fun)
in (get_fun_def, set_fun_def) end;

end
