signature mlstringSyntax =
sig
  include Abbrev

  val mlstring_ty         : hol_type

  val strlit_tm           : term
  val explode_tm          : term
  val implode_tm          : term
  val strlen_tm           : term
  val mlstring_case_tm    : term
  val strsub_tm           : term
  val strcat_tm           : term
  val concat_tm           : term
  val substring_tm        : term

  val mk_strlit           : term -> term
  val mk_explode          : term -> term
  val mk_implode          : term -> term
  val mk_strlen           : term -> term
  val mk_mlstring_case    : term -> term
  val mk_strsub           : term * term -> term
  val mk_strcat           : term * term -> term
  val mk_concat           : term -> term
  val mk_substring        : term * term * term -> term

  val dest_strlit         : term -> term
  val dest_explode        : term -> term
  val dest_implode        : term -> term
  val dest_strlen         : term -> term
  val dest_mlstring_case  : term -> term * term
  val dest_strsub         : term -> term * term
  val dest_strcat         : term -> term * term
  val dest_concat         : term -> term
  val dest_substring      : term -> term * term * term

  val is_strlit           : term -> bool
  val is_explode          : term -> bool
  val is_implode          : term -> bool
  val is_strlen           : term -> bool
  val is_mlstring_case    : term -> bool
  val is_strsub           : term -> bool
  val is_strcat           : term -> bool
  val is_concat           : term -> bool
  val is_substring        : term -> bool

  val is_mlstring_literal : term -> bool
end
