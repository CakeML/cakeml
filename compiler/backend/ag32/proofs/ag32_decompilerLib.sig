signature ag32_decompilerLib =
sig

  include Abbrev

  val derive_spec : string -> (thm * int * int option) *
                              (thm * int * int option) option

  val FUNPOW_Next_from_SPEC : thm -> thm -> thm

  val ag32_ffi_return_SPEC : thm

  val ag32_decompile : thm -> thm * thm

  val SPEC_COMPOSE_RULE : thm list -> thm

end
