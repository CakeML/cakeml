signature cfLetAutoLib = sig
    include Abbrev
    type ssfrag = simpLib.ssfrag
    type simpset = simpLib.simpset

    (* REMARK: some get functions are present in this signature only for development purposes and should be eventually removed - example: get_heuristic_solver *)

    val INTRO_REWRITE_CONV : thm list -> term list -> conv
    val INTRO_REWRITE_TAC : thm list -> tactic

    val export_frame_thms : string list -> unit
    val get_frame_thms : unit -> thm list

    val export_equality_type_thms : string list -> unit
    val get_equality_type_thms : unit -> thm list

    (*
       export_equality_type_thms should be called with the appropriate theorems as
       arguments before any call to export_refinement invariants
       Example:
       > export_equality_type_thms["EqualityType_TYPE1"];
       > export_refinement_invariant["TYPE1_def"];
    *)
    val export_refinement_invariants : string list -> unit
    val get_RI_defs : unit -> thm list
    val get_expand_thms : unit -> thm list
    val get_retract_thms : unit -> thm list

    val export_match_thms : string list -> unit
    val get_intro_rewrite_thms : unit -> thm list
    val get_rewrite_thms : unit -> thm list

    (* Only works locally - TODO: fix that *)
    val add_simp_frag : ssfrag -> unit
    val get_default_simpset : unit -> simpset

    (* Heuristics *)
    (* A safe solver based on unification *)
    val unification_solver :
      term list -> thm -> (term, term) subst * (hol_type, hol_type) subst

    (* A not safe solver, also based on unification *)
    val unif_heuristic_solver :
      term list -> thm -> (term, term) subst * (hol_type, hol_type) subst

    val set_heuristic_solver :
      (term list -> thm -> (term, term) subst * (hol_type, hol_type) subst) -> unit
    val get_heuristic_solver :
      unit -> term list -> thm -> (term, term) subst * (hol_type, hol_type) subst
    val use_heuristics : bool -> unit
    val using_heuristics : unit -> bool

    (* A function to extract the frame from a heap condition,
       by matching it against a second heap predicate *)
    val match_heap_conditions : term -> term ->
      {redex: term, residue: term} list * term list * term list

    (* The xlet_auto function and its derivatives *)
    val xlet_auto_spec : thm option -> tactic
    val xlet_find_auto : term list * term -> term
    val xlet_auto : tactic
end
