signature ml_monad_translatorLib = 
sig
    type thm = Thm.thm
    type hol_type = Type.hol_type

    val mem_derive_case_of : hol_type -> ((thm * ((hol_type * thm) list)) ref)
    val m_translate : thm -> thm
end
