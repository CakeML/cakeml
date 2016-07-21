signature cfTacticsLib =
sig
  include Abbrev

  val xpull : tactic
  val xcf : ml_progLib.ml_prog_state -> string -> tactic
  val xlet : term quotation -> term quotation -> tactic
  val xapply : thm -> tactic
  val xapp_prepare_goal : tactic (* for debugging *)
  val xapp : thm -> tactic
  val xret : tactic
end
