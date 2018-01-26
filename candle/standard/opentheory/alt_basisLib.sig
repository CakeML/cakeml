signature alt_basisLib =
sig

  include Abbrev

  val set_user_heap_thm : thm -> unit
  val get_user_heap_thm : unit -> thm option

  val whole_prog_thm : ml_progLib.ml_prog_state -> string -> thm -> thm * term
  val whole_prog_term : ml_progLib.ml_prog_state -> string -> thm -> term
end

