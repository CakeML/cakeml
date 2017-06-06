signature cfLetAutoLib = sig
    include Abbrev
    type ssfrag = simpLib.ssfrag

    val INTRO_REWRITE_CONV : thm list -> term list -> conv
    val INTRO_REWRITE_TAC : thm list -> tactic

    val add_frame_thms : thm list -> unit
    val get_frame_thms : unit -> thm list

    val add_refinement_invariants : thm list -> thm list -> unit
    val get_RI_desl : unit -> thm list
    val get_RI_expand_thms : unit -> thm list
    val get_RI_retract_thms : unit -> thm list
    val get_RI_equality_type_thms : unit -> thm list

    val add_match_thms : thm list -> unit
    val get_intro_rewrite_thms : unit -> thm list
    val get_rewrite_thms : unit -> thm list

    val add_simp_frag : ssfrag -> unit

    val set_heuristic_solver :
      (term list -> thm -> (term, term) subst * (hol_type, hol_type) subst) -> unit

    val use_heuristics : bool -> unit

    val match_heap_conditions : term -> term ->
      {redex: term, residue: term} list * term list * term list

    val xlet_find_auto : term list * term -> term
    val xlet_auto : tactic
end
