signature cfLetAutoLib = sig
    include Abbrev
    type ssfrag = simpLib.ssfrag
    type simpset = simpLib.simpset

    (* REMARK: some functions are present in this signature only for development purposes and should eventually be removed - example: get_heuristic_solver *)

    (* INTRO_REWRITE uses rewrite rules of the form:
       h1 => ... => hn => t1 = t2
       where the variables free in t2 are not necessarily present in t1.

       Is mainly supposed to be used with rules of the form:
       TYPE x xv1 => (TYPE x xv2 <=> xv2 = xv1)
       *)
    val INTRO_REWRITE_CONV : thm list -> term list -> conv
    val INTRO_REWRITE_TAC : thm list -> tactic

    (* The frame theorems are theorems used to compare two heap conditions.
       They should be of the following form:
       VALID_HEAP s ==> (PRED x1 ... xn * H1) s /\ (PRED y1 ... yn * H2) s ==> CONCL
       For example:
       VALID_HEAP s ==> (REF r xv1 * H1) s /\ (REF r xv2 * H2) s ==> xv2 = xv1
       *)
    val export_frame_thms : string list -> unit
    val get_frame_thms : unit -> thm list

    val export_equality_type_thms : string list -> unit
    val get_equality_type_thms : unit -> thm list

    (* A function to extract the frame from a heap condition,
       by matching it against a second heap predicate.
       Uses the theorems provided by export_frame_thms
       *)
    val match_heap_conditions : term -> term ->
      {redex: term, residue: term} list * term list * term list

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

    (* Apply the expand and retract rewrite rules to the goal -
       useful when dealing with refinement invariants *)
    val EXPAND_TAC : tactic
    val RETRACT_TAC : tactic
    val REWRITE_RI_TAC : tactic

    val export_match_thms : string list -> unit
    val get_intro_rewrite_thms : unit -> thm list
    val get_rewrite_thms : unit -> thm list

    (* Only works locally - TODO: fix that *)
    val add_simp_frag : ssfrag -> unit
    val get_default_simpset : unit -> simpset

    (* Heuristics *)
    (* A safe solver based on unification *)
    val unification_solver :
      term list -> term -> thm ->
      (term, term) subst * (hol_type, hol_type) subst

    (* A not safe solver, also based on unification *)
    val unif_heuristic_solver :
      term list -> term -> thm ->
      (term, term) subst * (hol_type, hol_type) subst

    val set_heuristic_solver :
      (term list -> term -> thm ->
         (term, term) subst * (hol_type, hol_type) subst) -> unit
    val get_heuristic_solver :
      unit -> term list -> term -> thm ->
      (term, term) subst * (hol_type, hol_type) subst
    val use_heuristics : bool -> unit
    val using_heuristics : unit -> bool

    (*
     * The xlet_auto function and its derivatives
     *)

    (* xlet_auto_spec takes an optional app specification as argument *)
    val xlet_auto_spec : thm option -> tactic

    (* xlet_find_auto returns the appropriate post-condition *)
    val xlet_find_auto : term list * term -> term

    (* xlet_auto is the default function to use *)
    val xlet_auto : tactic

    (* xlet_autop tries to generate less side goals than xlet_auto *)
    val xlet_autop : tactic
    (* debug_get_app_spec returns the last iteration of the manipulated app_spec - very useful when trying to figure out why xlet_auto failed *)
    val debug_get_app_spec : unit -> thm
end
