(*
  Some proof tools, mostly quite experimental, used in some of
  the proofs in this directory
*)

open combinTheory HolKernel Tactical Drule bossLib;

structure experimentalLib = struct

(* a family of tools for instantiating forall quantifiers.

   the simplest interface is qsubterm_then: given a pattern, instantiate
   a theorem by finding a subterm of the theorem that matches the pattern,
   and a subterm of the goal or an assumption, and instantiating based on
   those subterms.
*)

fun PART_MATCH2 finder thm all_vs tm = let
    val thm2 = PART_MATCH finder thm tm
    val vs = Term.FVL [concl thm2] empty_varset
    val remaining_all_vs = filter (curry HOLset.member vs) all_vs
  in GENL remaining_all_vs thm2 end

fun fvl_disjoint tms tms2 = HOLset.isEmpty (HOLset.intersection
    (FVL tms empty_tmset, FVL tms2 empty_tmset))

fun subterm_then_gen check adj (cont : thm_tactic) thm pat
        (assums, goal) = let
    val all_vs = fst (boolSyntax.strip_forall (concl thm))
    val thm = SPEC_ALL thm
    fun finder check all_vs = gen_find_terms (fn (bvs, t) =>
        if can (match_term pat) t andalso fvl_disjoint bvs [t]
            andalso check (bvs @ all_vs, t)
        then SOME (adj t) else NONE)
    val xs = finder check all_vs (concl thm)
    val _ = not (null xs) orelse failwith "subterm_then_gen: no match in thm"
    val terms = List.concat (map (finder (K true) []) (goal :: assums))
    val (all_vs, xs, thm) = if fvl_disjoint all_vs terms then (all_vs, xs, thm)
      else let
        val terms_vs = Term.FVL terms empty_tmset |> HOLset.listItems
        val (new_all_vs, _) = quantHeuristicsTools.list_variant terms_vs all_vs 
        val thm = GENL all_vs thm |> SPECL new_all_vs
      in (new_all_vs, finder check new_all_vs (concl thm), thm) end
  in MAP_FIRST (fn goal_term => MAP_FIRST (fn thm_term =>
      if aconv thm_term goal_term then failwith "subterm_then_gen: same"
      else fn state =>
        cont (PART_MATCH2 (K thm_term) thm all_vs goal_term) state)
    xs) terms (assums, goal)
  end

val subterm_match_pat_then =
  subterm_then_gen (K true) I : thm_tactic -> thm -> term -> tactic

fun qsubterm_then q_pat (cont : thm_tactic) thm =
    Q_TAC (subterm_match_pat_then cont thm) q_pat

fun subterm_limited_inst cont thm pat = let
    val rr_nm = fst o dest_var o #redex
    fun check (bound_vars, t) = let
        val (subst, _) = match_term pat t
      in all (fn rr => if String.isPrefix "X" (rr_nm rr)
        then fvl_disjoint bound_vars [#residue rr] else true) subst end
    fun adj t = let
        val (substs, tsubsts) = match_term pat t
        val pat2 = inst tsubsts pat
        val substs2 = filter (not o String.isPrefix "Ig" o rr_nm) substs
      in subst substs2 pat2 end
    val adj2 = if exists (String.isPrefix "Ig" o fst o dest_var) (free_vars pat)
        then adj else I
  in
    subterm_then_gen check adj cont thm pat
  end

(* qsubterm_then with X* and Ig* components, which adjust how matching and
   instantiation are done. variables named X* identify parts of the theorem
   that must already be fixed (contain none of the forall-quantified variables)
   and so they must exactly match the discovered goal term. variables named
   Ig* will not be used in generating the instantiation, and do not have to
   match the discovered goal term. *)
fun qsubterm_x_ig_then q_pat (cont : thm_tactic) thm =
    Q_TAC (subterm_limited_inst cont thm) q_pat

(* the above used to instantiate one assumption from another *)
fun do_xig_inst q_pat = first_x_assum
    (qsubterm_x_ig_then q_pat Tactic.strip_assume_tac)

(* testing notes
val (assums, goal) = top_goal ()
val thm = ASSUME (first is_forall assums)
val pat = ...
*)

end (* struct *)



