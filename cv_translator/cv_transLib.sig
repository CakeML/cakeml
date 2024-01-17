signature cv_transLib =
sig
  include Abbrev

  val cv_trans          : thm -> unit
  val cv_trans_pre      : thm -> thm
  val cv_trans_pre_rec  : thm -> tactic -> thm
  val cv_trans_rec      : thm -> tactic -> thm

  val cv_auto_trans          : thm -> unit
  val cv_auto_trans_pre      : thm -> thm
  val cv_auto_trans_pre_rec  : thm -> tactic -> thm
  val cv_auto_trans_rec      : thm -> tactic -> thm

  val cv_eval_raw    : term -> thm
  val cv_eval        : term -> thm

  val cv_termination_tac  : tactic

end
