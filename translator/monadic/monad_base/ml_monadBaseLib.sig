signature ml_monadBaseLib =
sig

    type term = Term.term
    type thm = Thm.thm
    type hol_type = Type.hol_type

    (*
     * Some general purpose functions
     *)

    val dest_fun_type : hol_type -> hol_type list * hol_type
    val mk_fun_type : hol_type list * hol_type -> hol_type
    val mk_list_vars : string -> hol_type list -> term list
    val mk_list_vars_same : string -> hol_type -> int -> term list
    val my_list_mk_comb : term * term list -> term

    (*
     * Functions used to mechanically define the manipulation functions for
     * the monadic states and exceptions
     *)
    val define_monad_exception_functions :
      hol_type -> hol_type -> (thm * thm) list

    val define_monad_get_fun : string * term -> thm
    val define_monad_set_fun : string * term -> thm

    val define_monad_access_funs : hol_type -> (string * thm * thm) list

    val define_MFarray_manip_funs :
      (string * thm * thm) list -> term -> term ->
      (string * thm * thm * thm * thm * thm) list

    val define_MRarray_manip_funs :
      (string * thm * thm) list -> term -> term ->
      (string * thm * thm * thm * thm * thm * thm) list

    val define_run : hol_type -> string list -> string -> thm

end

