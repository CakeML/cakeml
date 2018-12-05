(*
  Functions that aid building the CakeML code for the basis library.
*)
signature basisFunctionsLib =
sig

  include Abbrev

    val get_module_prefix : unit -> string
    val trans             : string -> term quotation -> thm
    val append_dec        : term -> unit
    val append_decs       : term -> unit
    val append_prog       : term -> unit
    val prove_ref_spec    : string -> goal -> goal list * (thm list -> thm)
    val process_topdecs   : string quotation -> term

end
