signature backend_asmLib =
sig

    include Abbrev

    val asm_spec_raw : thm list -> thm -> ((thm -> (thm * thm)) * (unit -> thm))
    val define_target_specific_backend : thm -> thm

end
