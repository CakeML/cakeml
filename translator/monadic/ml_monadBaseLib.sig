signature ml_monadBaseLib =
sig
    type term = Term.term
    type thm = Thm.thm
    type hol_type = Type.hol_type

    val define_monad_exception_functions : hol_type -> hol_type -> (thm * thm) list

    val define_monad_get_fun : string * term -> thm
    val define_monad_set_fun : string * term -> thm

    val define_monad_access_funs : hol_type -> (string * thm * thm) list

    val define_Marray_manip_funs : (string * thm * thm) list -> term -> term ->
				   (string * thm * thm * thm * thm * thm * thm) list
end
