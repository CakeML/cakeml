(*
  The signature of the user-friendly interface to the monadic translator
*)
signature ml_monad_translator_interfaceLib =
sig

  type term = Term.term
  type thm = Thm.thm
  type hol_type = Type.hol_type

  datatype translator_mode = GLOBAL | LOCAL;

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

  val local_state_config : config
  val global_state_config : config

  type state = {
    state_access_funs :   (string * thm * thm) list ref,
                            (* (name, get, set) *)
    store_invariant_name : string ref,
    exn_type_def : thm ref,
    additional_type_theories : string list ref,
    store_pinv_opt : (thm * thm) option ref,
    extra_hprop : term option ref
  }
  val internal_state : state

  val with_state : hol_type -> config -> config
  val with_exn : hol_type -> config -> config
  val with_refs : (string * term) list -> config -> config
  (*val with_fixed_arrays : (string * term) list -> config -> config*)
  val with_resizeable_arrays : (string * term * term * term) list -> config -> config
  val start_translation : config -> unit
  val m_translate : thm -> thm
end