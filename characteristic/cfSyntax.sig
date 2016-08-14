signature cfSyntax = sig
  include Abbrev

  val cf_lit_tm   : term
  val mk_cf_lit   : term * term * term * term -> term
  val dest_cf_lit : term -> term * term * term * term
  val is_cf_lit   : term -> bool

  val cf_con_tm   : term
  val mk_cf_con   : term * term * term * term * term -> term
  val dest_cf_con : term -> term * term * term * term * term
  val is_cf_con   : term -> bool

  val cf_var_tm   : term
  val mk_cf_var   : term * term * term * term -> term
  val dest_cf_var : term -> term * term * term * term
  val is_cf_var   : term -> bool

end
