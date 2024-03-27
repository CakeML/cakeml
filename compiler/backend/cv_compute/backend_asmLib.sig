signature backend_asmLib =
sig

    include Abbrev

    val define_target_specific_backend : thm -> thm

end
