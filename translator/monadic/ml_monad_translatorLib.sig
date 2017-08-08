signature ml_monad_translatorLib = 
sig
    include ml_translatorLib

    type monadic_translation_parameters = ml_monadStoreLib.monadic_translation_parameters

    val mem_derive_case_of : hol_type -> thm

    val init_translation :
        monadic_translation_parameters -> thm option -> thm -> string list -> unit

    val add_raise_handle_functions : thm list -> thm list -> thm -> (thm list * thm list)

    val m_translate : thm -> thm

    val m_translate_run : thm -> thm
end
