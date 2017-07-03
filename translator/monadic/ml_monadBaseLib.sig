signature ml_monadBaseLib =
sig
    type term = Term.term
    type thm = Thm.thm

    val define_monad_get_fun : string * term -> thm
    val define_monad_set_fun : string * term -> thm

    val define_monad_access_funs : string * term * term -> (thm * thm)
end
