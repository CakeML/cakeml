(*
  The user-friendly interface to the monadic translator
*)

structure ml_monad_translator_interfaceLib :>
            ml_monad_translator_interfaceLib = struct

open preamble ml_monadBaseLib ml_monadStoreLib ml_monad_translatorLib
     ml_translatorLib


(******************************************************************************

  Preamble

******************************************************************************)

(* Add monadic syntax: do x <- f y; ... od *)
val _ = ParseExtras.temp_loose_equality();
val _ = monadsyntax.temp_add_monadsyntax()

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
  mode              : translator_mode,
  state_type        : hol_type ref,
  exn_type          : hol_type ref,
  exn_access_funs   : (thm * thm) list ref,
                        (* (raise, handle) *)
  refs              : (string * thm * thm * thm) list ref,
                        (* (name, init, get, set) *)
  fixed_arrays      : (string * (int * thm) * thm * thm * thm * thm * thm)
                        list ref,
  resizeable_arrays : (string*thm * thm * thm * thm * thm * thm * thm) list ref,
                        (* (name, init, get, set, len, sub, update, alloc) *)
  extra_state_inv   : (thm * thm) option ref
                        (* state_inv_def, state_inv_valid *)
}

(* Local-mode translation base state *)
val local_state_config : config = {
  mode              = LOCAL,
  state_type        = ref unit_ty,
  exn_type          = ref unit_ty,
  exn_access_funs   = ref [],
  refs              = ref [],
  fixed_arrays      = ref [],
  resizeable_arrays = ref [],
  extra_state_inv   = ref NONE
};

(* Global-mode translation base state *)
val global_state_config : config = {
  mode              = GLOBAL,
  state_type        = ref unit_ty,
  exn_type          = ref unit_ty,
  exn_access_funs   = ref [],
  refs              = ref [],
  fixed_arrays      = ref [],
  resizeable_arrays = ref [],
  extra_state_inv   = ref NONE
};

(* Type definition of the internal state *)
type state = {
  state_access_funs         : (string * thm * thm) list ref,
                                (* (name, get, set) *)
  store_invariant_name      : string ref,
  exn_type_def              : thm ref,
  additional_type_theories  : string list ref,
  extra_hprop               : term option ref
};

(* Initial internal state *)
val internal_state : state = {
  state_access_funs        = ref [],
  store_invariant_name     = ref "STATE_STORE",
  exn_type_def             = ref ml_translatorTheory.UNIT_TYPE_def,
  additional_type_theories = ref [],
  extra_hprop              = ref NONE
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
fun with_exception exn_type (translator_config : config) =
  let val state_type = ( !(#state_type translator_config) )
      val exn_access_funs = if exn_type = unit_ty then [] else
                    define_monad_exception_functions exn_type state_type
  in
    #exn_type translator_config := exn_type;
    #exn_access_funs translator_config := exn_access_funs;
    #exn_type_def internal_state := (register_exception_type exn_type);
    (*register_type state_type; TODO FIND OUT WHERE THIS IS NECESSARY *)
    translator_config
  end;

(*
 *  Mark state fields as references.
 *  Define initial values for them.
 *)
fun mk_ref_init (field_name, init_value) =
  (* not visible to user *)
  let val init_type = type_of init_value
      val init_name = "ref_init_" ^ field_name
      val init_var = mk_var(init_name, init_type)
      val init_eq = mk_eq(init_var, init_value)
      val (_, get, set) = first (fn a => field_name = #1 a)
                            (! (#state_access_funs internal_state) )
  in (field_name, Define `^init_eq`, get, set) end;

fun with_refs refs (translator_config : config) =
  let val refs_init_list = List.map mk_ref_init refs
  in
    #refs translator_config := refs_init_list;
    translator_config
  end

(*
 *  Mark state fields as fixed arrays.
 *  Define initial values, info, and subscript/update exceptions for them.
 *)
fun mk_farray_init (field_name, init_value, init_info, sub_exn, update_exn) =
  (* not visible to user *)
  let val init_type = type_of init_value
      val init_name = "farray_init_" ^ field_name
      val init_var = mk_var(init_name, init_type)
      val init_eq = mk_eq(init_var, init_value)
      val accessors = first (fn a => field_name = #1 a)
                        (! (#state_access_funs internal_state) )
      val (_, get, set, len, sub, update) =
        define_MFarray_manip_funs [accessors] sub_exn update_exn |> hd
  in (field_name, (init_info : int, Define `^init_eq`),
      get, set, len, sub, update) end;

fun with_fixed_arrays farrays (translator_config : config) =
  let val farrays_init_list = List.map mk_farray_init farrays
  in
    #fixed_arrays translator_config := farrays_init_list;
    translator_config
  end;

(*
 *  Mark state fields as resizeable arrays.
 *  Define initial values, and subscript/update exceptions for them.
 *)
fun mk_rarray_init (field_name, init_value, sub_exn, update_exn) =
  (* not visible to user *)
  let val init_type = type_of init_value
      val init_name = "rarray_init_" ^ field_name
      val init_var = mk_var(init_name, init_type)
      val init_eq = mk_eq(init_var, init_value)
      val accessors = first (fn a => field_name = #1 a)
                        (! (#state_access_funs internal_state) )
      val (_, get, set, len, sub, update, alloc) =
        define_MRarray_manip_funs [accessors] sub_exn update_exn |> hd
  in (field_name, Define `^init_eq`, get, set, len, sub, update, alloc) end;

fun with_resizeable_arrays rarrays (translator_config : config) =
  let val rarrays_init_list = List.map mk_rarray_init rarrays
  in
    #resizeable_arrays translator_config := rarrays_init_list;
    translator_config
  end;

(*
 *  Mark state fields as stdio.
 *  Define initial values, and subscript/update exceptions for them.
 *)
fun with_stdio field_name (translator_config : config) =
  let val state_type = ( !(#state_type translator_config) )
      val state_var = mk_var("s", state_type)
      val stdio_field = (* s.stdio *)
        Term [ANTIQUOTE state_var, QUOTE ".", QUOTE field_name]
      val extra_hprop = ``MONAD_IO ^stdio_field``
  in
    #extra_hprop internal_state := (SOME extra_hprop);
    translator_config
  end

fun with_commandline commandline_name stdio_name (translator_config : config) =
  let val state_type = ( !(#state_type translator_config) )
      val state_var = mk_var("s", state_type)
      val stdio_field = (* s.stdio *)
        Term [ANTIQUOTE state_var, QUOTE ".", QUOTE stdio_name]
      val commandline_field = (* s.commandline *)
        Term [ANTIQUOTE state_var, QUOTE ".", QUOTE commandline_name];
      val extra_hprop =
        ``COMMANDLINE ^(commandline_field) * MONAD_IO ^(stdio_field)``
  in
    #extra_hprop internal_state := (SOME extra_hprop);
    translator_config
  end

(*
 * Use a user-defined additional state invariant.
 *)
fun with_state_invariant inv_def inv_valid (translator_config : config) =
  let val extra_state_inv = SOME(inv_def, inv_valid)
  in
    #extra_state_inv translator_config := extra_state_inv;
    translator_config
  end;

(******************************************************************************

  Initialisation and translation functions

******************************************************************************)

(* Filter out functions unecessary for LOCAL-mode translation *)
fun extract_refs_manip_funs (name, init, get, set) = (name, get, set);
fun extract_rarrays_manip_funs (name, init, get, set, len, sub, upd, alloc) =
      (name, get, set, len, sub, upd, alloc);
fun extract_farrays_manip_funs (name, init, get, set, len, sub, upd) =
      (name, get, set, len, sub, upd);

(* Initialise the translation *)
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
          ( !(#extra_state_inv          c) )
          ( !(#extra_hprop              s) )
        in () end
  | LOCAL => let val _ =
      start_dynamic_init_fixed_store_translation
          ((!(#refs                     c) ) |> map extract_refs_manip_funs)
          ((!(#resizeable_arrays        c) ) |> map extract_rarrays_manip_funs)
          ((!(#fixed_arrays             c) ) |> map extract_farrays_manip_funs)
          ( !(#store_invariant_name     s) )
          ( !(#state_type               c) )
          ( !(#exn_type_def             s) )
          ( !(#exn_access_funs          c) )
          ( !(#additional_type_theories s) )
          ((!(#extra_state_inv          c) ) |> Option.map fst)
        in () end
) end;

(* Translation functions from ml_translatorLib *)
val translate = ml_translatorLib.translate;
val translation_extends = ml_translatorLib.translation_extends;

(* Translation functions from ml_monad_translatorLib *)
val register_type = ml_monad_translatorLib.register_type;
val m_translate = ml_monad_translatorLib.m_translate;
val m_translate_run = ml_monad_translatorLib.m_translate_run;

(*
 * From ml_translatorLib
 *
 * Resume prior monadic translation.
 * Loads the state specific to the monadic translation from the specified
 * theory, followed by a call to translation_extends from the 'standard'
 * translator (i.e. fetching the rest of the translator state).
 *)
val m_translation_extends = ml_monad_translatorLib.m_translation_extends;

end (* end struct *)
