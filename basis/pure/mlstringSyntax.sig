signature mlstringSyntax =
sig
  include Abbrev

  val mlstring_ty         : hol_type

  val strlit_tm           : term
  val explode_tm          : term
  val implode_tm          : term
  val mlstring_case_tm    : term

  val mk_strlit           : term -> term
  val mk_explode          : term -> term
  val mk_implode          : term -> term
  val mk_mlstring_case    : term -> term

  val dest_strlit         : term -> term
  val dest_explode        : term -> term
  val dest_implode        : term -> term
  val dest_mlstring_case  : term -> term * term

  val is_strlit           : term -> bool
  val is_explode          : term -> bool
  val is_implode          : term -> bool
  val is_mlstring_case    : term -> bool

  val is_mlstring_literal : term -> bool
end
