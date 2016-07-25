signature cfTacticsLib =
sig
  include Abbrev

  val xpull : tactic
  val xlocal : tactic
  val xcf : string -> ml_progLib.ml_prog_state -> tactic
  val xlet : term quotation -> term quotation -> tactic
  val xapply : thm -> tactic
  val xapp : tactic
  val xapp_spec : thm -> tactic
  val xret : tactic

  (* low level / debugging *)
  val xapp_prepare_goal : tactic
  val reduce_tac : tactic
end
