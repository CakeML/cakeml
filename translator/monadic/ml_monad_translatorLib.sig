(*
  The signature of the monadic translator.
*)
signature ml_monad_translatorLib =
sig
    include ml_monadStoreLib

    (* Functions to initialize the translation *)
    val start_static_init_fixed_store_translation :
        (string * thm * thm * thm) list ->
        (string * thm * thm * thm * thm * thm * thm * thm) list ->
        (string * (int * thm) * thm * thm * thm * thm * thm) list ->
        string -> hol_type -> thm -> (thm * thm) list -> string list ->
        (thm * thm) option -> term option
      ->
        monadic_translation_parameters *
        store_translation_result * (thm * thm) list

    val start_dynamic_init_fixed_store_translation :
       (string * thm * thm) list ->
       (string * thm * thm * thm * thm * thm * thm) list ->
       (string * thm * thm * thm * thm * thm) list ->
        string -> hol_type -> thm -> (thm * thm) list -> string list ->
        thm option
      ->
        monadic_translation_parameters * (thm * thm) list

    (* Other functions to initialize the translation - the above ones should be preferred *)
    val init_translation :
        monadic_translation_parameters -> (thm * thm) list ->
        (thm * thm * thm * thm * thm * thm) list ->
        (thm * thm * thm * thm * thm) list ->
        (thm * thm) list ->
        thm option -> thm -> string list -> thm option
        -> unit

    val add_raise_handle_functions : (thm * thm) list -> thm -> (thm * thm) list

    val add_access_pattern : thm -> thm

    (* Translation functions *)
    val m_translate : thm -> thm
    val m_translate_run : thm -> thm
    val m2deep : term -> thm

    (* Update precondition for dynamic specifications *)
    val update_local_precondition : thm -> thm

    (* Resume prior monadic translation.

       Loads the state specific to the monadic translation from the specified
       theory, followed by a call to translation_extends from the 'standard'
       translator (i.e. fetching the rest of the translator state). *)
    val m_translation_extends : string -> unit

end
