signature basis_ffiLib = sig

  include Abbrev

  (* Set the optional store precondition *)
  val add_user_heap_thm : thm -> unit

  val whole_prog_spec_def : thm

  val whole_prog_thm : ml_progLib.ml_prog_state -> string -> thm -> thm * term

end
