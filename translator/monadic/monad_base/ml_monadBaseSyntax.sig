signature ml_monadBaseSyntax =
sig

    type term = Term.term
    type hol_type = Type.hol_type

    (* types *)
    val mk_exc_ty   : hol_type * hol_type -> hol_type
    val exc_ty      : hol_type
    val mk_M_ty     : hol_type * hol_type * hol_type -> hol_type
    val M_ty        : hol_type

    (* exc constructors *)
    val M_success_tm    : term
    val mk_M_success    : term -> term
    val dest_M_success  : term -> term
    val is_M_success    : term -> bool

    val M_failure_tm    : term
    val mk_M_failure    : term -> term
    val dest_M_failure  : term -> term
    val is_M_failure    : term -> bool

    (* monad operations *)
    val st_ex_bind_tm           : term
    val mk_st_ex_bind           : term * term -> term
    val dest_st_ex_bind         : term -> term * term
    val is_st_ex_bind           : term -> bool

    val st_ex_ignore_bind_tm    : term
    val mk_st_ex_ignore_bind    : term * term -> term
    val dest_st_ex_ignore_bind  : term -> term * term
    val is_st_ex_ignore_bind    : term -> bool

    val st_ex_return_tm         : term
    val mk_st_ex_return         : term -> term
    val dest_st_ex_return       : term -> term
    val is_st_ex_return         : term -> bool

    val otherwise_tm    : term
    val mk_otherwise    : term * term -> term
    val dest_otherwise  : term -> term * term
    val is_otherwise    : term -> bool

    val run_tm      : term
    val mk_run      : term * term -> term
    val dest_run    : term -> term * term
    val is_run      : term -> bool

    (* array operations *)
    val Marray_length_tm    : term
    val mk_Marray_length    : term -> term
    val dest_Marray_length  : term -> term
    val is_Marray_length    : term -> bool

    val Marray_sub_tm       : term
    val mk_Marray_sub       : term * term * term -> term
    val dest_Marray_sub     : term -> term * term * term
    val is_Marray_sub       : term -> bool

    val Marray_alloc_tm     : term
    val mk_Marray_alloc     : term * term * term -> term
    val dest_Marray_alloc   : term -> term * term * term
    val is_Marray_alloc     : term -> bool

    val Marray_update_tm    : term

end
