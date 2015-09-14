signature parsingPreamble =
sig

  include Abbrev
  val MAP_EQ_SING : thm
  val MAP_EQ_APPEND : thm
  val MAP_EQ_CONS : thm
  val APPEND_ASSOC : thm

  val loseC : term -> tactic
  val asm_match : term quotation -> tactic

  val kill_asm_guard : tactic
  val qispl_then : term quotation list -> thm_tactic -> thm_tactic
  val qxchl : term quotation list -> thm_tactic -> thm_tactic
  val rveq : tactic

  val erule : thm_tactic -> thm_tactic
  val print_tac : string -> tactic

end
