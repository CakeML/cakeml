(*
  Implementation of the xcf and xcfs tactics.
 *)
signature xcf =
sig
  include Abbrev
  val xcf_with_def : thm -> tactic
  val xcf_with_defs : thm list -> tactic
  val xcf : string -> ml_progLib.ml_prog_state -> tactic
  val xcfs : string list -> ml_progLib.ml_prog_state -> tactic
end (* sig *)
