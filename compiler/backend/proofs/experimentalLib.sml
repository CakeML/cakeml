(*
  Some proof tools, mostly quite experimental, used in some of
  the proofs in this directory
*)

open combinTheory;

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
    val all_vs = fst (strip_forall (concl thm))
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

fun pad_K_app_conv f = let
    val thm = ISPEC f K_THM |> ISPEC T |> GSYM
    val (ty, _) = Type.dom_rng (type_of f)
    val x = mk_var ("x", ty)
    val thm2 = AP_THM thm x
  in REWRITE_CONV [thm2] end

fun subterm_limited_inst cont thm pat = let
    fun check (bound_vars, t) = let
        val (subst, _) = match_term pat t
      in all (fn rr => if String.isPrefix "X" (fst (dest_var (#redex rr)))
        then fvl_disjoint bound_vars [#residue rr] else true) subst end
  in
    subterm_then_gen check I cont thm pat
  end

fun qsubterm_limited q_pat (cont : thm_tactic) thm =
    Q_TAC (subterm_limited_inst cont thm) q_pat

assume_tac (METIS_PROVE [] ``! ^s t. s_rel s t ==> (T, T) = (T, T)``)

first_x_assum (qsubterm_limited `s_rel X_s t` mp_tac)
(* next do the adj bit *)

first_x_assum (qsubterm_limited `s_rel X_s t` mp_tac)
first_x_assum (qsubterm_then `s_rel _ t` mp_tac)
disch_then (qsubterm_then `s_rel _ t` mp_tac)

first_x_assum (drule_then mp_tac)




  
(* drop 'K' inside matches of a pattern `some_rel X _` where the X instance
   disagrees with some other instance of the pattern *)
fun safety_pad f pat other_match = let
    val (other_subst, _) = match_term pat other_match
    fun is_mismatch rr = case subst_assoc (term_eq (#redex rr)) other_subst of
          NONE => true
        | SOME t2 => not (term_eq (#residue rr) t2)
    fun has_mismatch t = let
        val (t_subst, _) = match_term pat t
        val xs = filter (String.isPrefix "X" o fst o dest_var o #redex) t_subst
      in exists is_mismatch xs end
    fun safety_conv t = if has_mismatch t
        then pad_K_app_conv f t else raise UNCHANGED
  in DEPTH_CONV safety_conv end

(* testing
val pat = ``X < (y : num)``
val f = fst (strip_comb pat)
val other_match = ``x1 < (y1 : num)``;
val test_thm = ASSUME ``! z1 z2 z3. x1 < (z1 : num) /\ z2 < (z3 : num) ==> P z3``
CONV_RULE (safety_pad f pat other_match) test_thm

*)

(* given a pattern e.g. `some_rel X _`, find an assumption matching the
   pattern, and use it to instantiate forall quantifiers in the theorem to
   match up a `some_rel X _` premise, however, only if the X parts exactly
   match without doing any instantiation. (the X parts, more generally, are
   parts of the pattern with variables whose name starts with "X") *)
fun do_safe_inst_then pat thm cont (assums, goal) = let
    val t = find_term (fn t => is_comb t andalso is_const (rator t)) pat
        handle HOL_ERR _ => failwith ("do_safe_inst_then: "^
            "pattern must contain const applied to arg")
    val safety_const = rator t
    val _ = find_term (can (match_term pat)) (concl thm)
        handle HOL_ERR _ => failwith ("do_safe_inst_then: no match in thm")
    val inst_assums = filter (can (match_term pat)) assums
    val _ = not (null inst_assums)
        orelse failwith ("do_safe_inst_then: no match in assumptions")
    val avoid_vars = FVL inst_assums empty_tmset |> HOLset.listItems
    val thm = CONV_RULE (quantHeuristicsTools.VARIANT_CONV avoid_vars) thm
    fun asm_cont a = mp_then.mp_then (mp_then.Pat `^pat`)
        (cont o REWRITE_RULE [K_THM])
        (CONV_RULE (safety_pad safety_const pat a) thm)
        (ASSUME a)
  in MAP_FIRST asm_cont inst_assums (assums, goal) end

fun qdo_asm_inst qpat = first_x_assum (fn assum => Q_TAC (fn pat =>
    do_safe_inst_then pat assum strip_assume_tac) qpat)

end (* struct *)



