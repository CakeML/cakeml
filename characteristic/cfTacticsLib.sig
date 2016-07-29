signature cfTacticsLib =
sig
  include Abbrev

  val xsimpl : tactic
  val xpull : tactic
  val xlocal : tactic
  val xcf : string -> ml_progLib.ml_prog_state -> tactic
  val xlet : term quotation -> term quotation -> tactic
  val xlet_seq : term quotation -> tactic
  val xapply : thm -> tactic
  val xapp : tactic
  val xapp_spec : thm -> tactic
  val xret : tactic
  val xlog : tactic
  val xif : tactic
  val xmatch : tactic

  (* low level / debugging *)
  val xapp_prepare_goal : tactic
  val reduce_tac : tactic
end
