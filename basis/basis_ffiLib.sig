signature basis_ffiLib = sig

  include Abbrev

  val add_basis_proj : thm -> thm

  val call_thm : ml_progLib.ml_prog_state -> string -> thm -> thm * term

end
