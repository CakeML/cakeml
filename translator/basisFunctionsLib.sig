signature basisFunctionsLib =
sig

  include Abbrev

    val get_module_prefix : unit -> string   
    val trans             : string -> term frag list -> thm
    val append_dec        : term -> unit
    val append_decs       : term -> unit
    val append_prog       : term -> unit
    val prove_ref_spec    : string -> goal -> goal list * (thm list -> thm)
  
end
