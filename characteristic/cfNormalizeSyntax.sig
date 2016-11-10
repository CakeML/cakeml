signature cfNormalizeSyntax = sig
  include Abbrev

  val full_normalise_prog_tm   : term
  val mk_full_normalise_prog   : term -> term
  val dest_full_normalise_prog : term -> term
  val is_full_normalise_prog   : term -> bool

  val full_normalise_decl_tm   : term
  val mk_full_normalise_decl   : term -> term
  val dest_full_normalise_decl : term -> term
  val is_full_normalise_decl   : term -> bool

  val full_normalise_exp_tm   : term
  val mk_full_normalise_exp   : term -> term
  val dest_full_normalise_exp : term -> term
  val is_full_normalise_exp   : term -> bool

  val full_normalise_tm   : term
  val mk_full_normalise   : term * term -> term
  val dest_full_normalise : term -> term * term
  val is_full_normalise   : term -> bool
end
