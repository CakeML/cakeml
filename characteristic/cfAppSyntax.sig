signature cfAppSyntax = sig
  include Abbrev

  val app_basic_tm   : term
  val mk_app_basic   : term * term * term * term * term -> term
  val dest_app_basic : term -> term * term * term * term * term
  val is_app_basic   : term -> bool

  val app_tm   : term
  val mk_app   : term * term * term * term * term -> term
  val dest_app : term -> term * term * term * term * term
  val is_app   : term -> bool

  val curried_tm   : term
  val mk_curried   : term * term * term -> term
  val dest_curried : term -> term * term * term
  val is_curried   : term -> bool

end
