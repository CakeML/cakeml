(*
  The signature of the user-friendly interface to the monadic translator.

  Intended usage (omit config functions as necessary):

    open preamble ml_monad_translator_interfaceLib

    val config =
      {global_state_config | local_state_config} |>
      with_state ``:<state_type>`` |>
      with_exception ``:<exception_type>`` |>
      with_refs [
        ("ref1", ``<init_val_ref1> : <init_val_ref1_type>``),
        ...
      ] |>
      with_fixed_arrays [
        ("farray1,``<init_val_farray1> : <init_val_farray2_type>``,
            ``<subscript_exception>``, ``<update_exception>``),
        ...
      ] |>
      with_resizeable_arrays [
        ("rarray1,``<init_val_rarray1> : <init_val_rarray2_type>``,
            ``<subscript_exception>``, ``<update_exception>``),
        ...
      ] |>
      {
        with_stdio "stdio_name"    |
        with_commandline "commandline_name" "stdio_name"}
      } |>
      with_state_invariant invariant_def_thm invariant_valid_thm;

    val _ = start_translation config;

    ...

*)
signature ml_monad_translator_interfaceLib =
sig

  type term = Term.term
  type thm = Thm.thm
  type hol_type = Type.hol_type

  datatype translator_mode = GLOBAL | LOCAL;

  type config = {
    mode              : translator_mode,
    state_type        : hol_type ref,
    exn_type          : hol_type ref,
    exn_access_funs   : (thm * thm) list ref,
                         (* (raise, handle) *)
    refs              : (string * thm * thm * thm) list ref,
                          (* (name, init, get, set) *)
    fixed_arrays      : (string * (int * thm) * thm * thm * thm * thm * thm) list ref,
    resizeable_arrays : (string*thm * thm * thm * thm * thm * thm * thm) list ref,
                          (* (name, init, get, set, len, sub, update, alloc) *)
    extra_state_inv   : (thm * thm) option ref
                        (* state_inv_def, state_inv_valid *)
  }

  val local_state_config : config
  val global_state_config : config

(* TODO - remove internal state visibility *)
  type state = {
    state_access_funs :   (string * thm * thm) list ref,
                            (* (name, get, set) *)
    store_invariant_name : string ref,
    exn_type_def : thm ref,
    additional_type_theories : string list ref,
    extra_hprop : term option ref
  }
  val internal_state : state

    (* Choose a state type for the translation (optional) *)
    val with_state : hol_type -> config -> config

    (* Choose an exception type for the translation (optional) *)
    val with_exception : hol_type -> config -> config

    (* Choose reference fields from the state (optional) *)
    val with_refs : (string * term) list -> config -> config
      (* field name, initial value *)

    (* Choose fixed-length array fields from the state (optional) *)
    val with_fixed_arrays :
      (string * term * int * term * term) list -> config -> config
      (* field name, initial element value, length (?), subscript exception,
          update exception *)

    (* Choose resizeable array fields from the state (optional) *)
    val with_resizeable_arrays :
      (string * term * term * term) list -> config -> config
      (* field name, initial array, subscript exception, update exception *)

  (* NB: USE EITHER with_stdio OR with_commandline *)

    (* Choose stdio field from the state (optional) *)
    val with_stdio : string -> config -> config (* field name *)

    (* Choose commandline and stdio fields from the state (optional) *)
    val with_commandline : string -> string -> config -> config
      (* commandline field name, stdio field name *)

  (* Advanced: create your own additional state invariant *)
    val with_state_invariant : thm -> thm -> config -> config
      (* state invariant definition, state invariant validity theorem *)

  (* Translation initialisation *)
  val start_translation : config -> unit

  (* Translation functions *)
  val register_type : hol_type -> unit;
  val translate : thm -> thm
  val m_translate : thm -> thm
  val m_translate_run : thm -> thm

  (* From ml_translatorLib *)
  val translation_extends : string -> unit

  (* Resume prior monadic translation.
   * Loads the state specific to the monadic translation from the specified
   * theory, followed by a call to translation_extends from the 'standard'
   * translator (i.e. fetching the rest of the translator state).
   *)
  val m_translation_extends : string -> unit
end