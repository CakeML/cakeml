signature cv_repLib =
sig
  include Abbrev

  val cv_rep_for         : (term * thm) list -> term -> thm

  exception NeedsTranslation of term list * term;

end
