signature ml_monad_translatorLib = 
sig
    type term = Term.term
    type thm = Thm.thm
    type hol_type = Type.hol_type
    type store_translation_result = ml_monadStoreLib.store_translation_result

    val mem_derive_case_of : hol_type -> thm

    val init_translation :
        store_translation_result -> (thm list) -> term -> string list -> unit
    val m_translate : thm -> thm
end
