(*
  The user-friendly interface to the monadic translator
*)

structure ml_monad_translator_interfaceLib :>
            ml_monad_translator_interfaceLib = struct

open preamble ml_monadBaseLib ml_monadStoreLib ml_monad_translatorLib


(******************************************************************************

  Preamble

******************************************************************************)

(* Add monadic syntax: do x <- f y; ... od *)
val _ = ParseExtras.temp_loose_equality();
val _ = monadsyntax.temp_add_monadsyntax()

(* Pattern matching - use `dtcase` instead of `case` from now on *)
(*val _ = patternMatchesLib.ENABLE_PMATCH_CASES(); TODO find better way of using this*)

(* Parser overloadings *)
val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

(* Hide "state" due to semanticPrimitives *)
val _ = hide "state";

val _ = (use_full_type_names := false);


(******************************************************************************

  Constants and helper functions

******************************************************************************)

fun toUppers(str) = String.implode (map Char.toUpper (String.explode str));
val unit_ty = type_of ``()``;


datatype translator_mode = GLOBAL | LOCAL;


(******************************************************************************

  Define the state of the translation interface

******************************************************************************)

(* Type definition of the user-visible configuration *)
type config = {
  mode :              translator_mode,
  state_type :        hol_type ref,
  exn_type :          hol_type ref,
  exn_access_funs :   (thm * thm) list ref,
                       (* (raise, handle) *)
  refs :              (string * thm * thm * thm) list ref,
                        (* (name, init, get, set) *)
  fixed_arrays :      (string * (int * thm) * thm * thm * thm * thm * thm) list ref,
  resizeable_arrays : (string*thm * thm * thm * thm * thm * thm * thm) list ref
                        (* (name, init, get, set, len, sub, update, alloc) *)
}

(* Local-mode translation base state *)
val local_state_config : config = {
  mode              = LOCAL,
  state_type        = ref unit_ty,
  exn_type          = ref unit_ty,
  exn_access_funs   = ref [],
  refs              = ref [],
  fixed_arrays      = ref [],
  resizeable_arrays = ref []
};

(* Global-mode translation base state *)
val global_state_config : config = {
  mode              = GLOBAL,
  state_type        = ref unit_ty,
  exn_type          = ref unit_ty,
  exn_access_funs   = ref [],
  refs              = ref [],
  fixed_arrays      = ref [],
  resizeable_arrays = ref []
};

(* Type definition of the internal state *)
type state = {
  state_access_funs :   (string * thm * thm) list ref,
                          (* (name, get, set) *)
  store_invariant_name : string ref,
  exn_type_def : thm ref,
  additional_type_theories : string list ref,
  store_pinv_opt : (thm * thm) option ref,
  extra_hprop : term option ref
};

(* Initial internal state *)
val internal_state : state = {
  state_access_funs = ref [],
  store_invariant_name = ref "",
  exn_type_def = ref ml_translatorTheory.UNIT_TYPE_def,
  additional_type_theories = ref [],
  store_pinv_opt = ref NONE,
  extra_hprop = ref NONE
};



(******************************************************************************

  Translator config setup functions

******************************************************************************)

(*
 *  Set the state store type, and get monadic access functions
 *)
fun with_state state_type (translator_config : config) =
  let val accessors = define_monad_access_funs state_type
  in
    #state_type translator_config := state_type;
    #store_invariant_name internal_state :=
      (state_type |> dest_type |> fst |> toUppers);
    #state_access_funs internal_state := accessors;
    translator_config
  end;

(*
 *  Register the exception type and return the type definition
 *)
fun register_exception_type exn_type =
  let val exn_type_def_name =
      (exn_type |> dest_type |> fst |> toUppers) ^ "_TYPE_def"
  in (
    register_type ``:unit``;
    register_type ``:'a # 'b``;
    register_type ``:'a list``;
    register_type ``:'a option``;
    register_exn_type exn_type;
    theorem exn_type_def_name
  ) end;

(*
 *  Set the exception type, and get monadic exception functions
 *)
fun with_exn exn_type (translator_config : config) =
  let val state_type = ( !(#state_type translator_config) )
      val exn_access_funs =
                    define_monad_exception_functions exn_type state_type
  in
    #exn_type translator_config := exn_type;
    #exn_access_funs translator_config := exn_access_funs;
    #exn_type_def internal_state := (register_exception_type exn_type);
    translator_config
  end;

(*
 *  Mark state fields as references.
 *  Define initial values for them.
 *)
fun mk_ref_init (state_name, init_value) =
  (* not visible to user *)
  let val init_type = type_of init_value
      val init_name = "init_" ^ state_name
      val init_var = mk_var(init_name, init_type)
      val init_eq = mk_eq(init_var, init_value)
      val (_, get, set) = first (fn a => state_name = #1 a)
                            (! (#state_access_funs internal_state) )
  in (state_name, Define `^init_eq`, get, set) end;

fun with_refs refs (translator_config : config) =
  let val refs_init_list = List.map mk_ref_init refs
  in
    #refs translator_config := refs_init_list;
    translator_config
  end

(*
 *  Mark state fields as fixed arrays.
 *  Define initial values for them.
 *)
(*fun with_fixed_arrays : (string * term) list -> config -> config*)


(*
 *  Mark state fields as resizeable arrays.
 *  Define initial values, and subscript/update exceptions for them.
 *)
fun mk_rarray_init (state_name, init_value, sub_exn, update_exn) =
  (* not visible to user *)
  let val init_type = type_of init_value
      val init_name = "init_" ^ state_name
      val init_var = mk_var(init_name, init_type)
      val init_eq = mk_eq(init_var, init_value)
      val accessors = first (fn a => state_name = #1 a)
                        (! (#state_access_funs internal_state) )
      val (_, get, set, len, sub, update, alloc) =
        define_MRarray_manip_funs [accessors] sub_exn update_exn |> hd
  in (state_name, Define `^init_eq`, get, set, len, sub, update, alloc) end;

fun with_resizeable_arrays rarrays (translator_config : config) =
  let val rarrays_init_list = List.map mk_rarray_init rarrays
  in
    #resizeable_arrays translator_config := rarrays_init_list;
    translator_config
  end;


(******************************************************************************

  Initialisation and translation functions

******************************************************************************)


fun start_translation (translator_config : config) =
  let val c = translator_config
      val s = internal_state in (
  case (#mode translator_config) of
    GLOBAL => let val _ =
      start_static_init_fixed_store_translation
          ( !(#refs                     c) )
          ( !(#resizeable_arrays        c) )
          ( !(#fixed_arrays             c) )
          ( !(#store_invariant_name     s) )
          ( !(#state_type               c) )
          ( !(#exn_type_def             s) )
          ( !(#exn_access_funs          c) )
          ( !(#additional_type_theories s) )
          ( !(#store_pinv_opt           s) )
          ( !(#extra_hprop              s) )
        in () end
  | LOCAL => ()
) end;

val m_translate = ml_monad_translatorLib.m_translate;

end (* end struct *)