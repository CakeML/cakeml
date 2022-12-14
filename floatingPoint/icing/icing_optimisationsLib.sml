(*
  Library defining HOL4 automation that builds an optimiser
  correctness theorem for an optimisation plan.
*)
structure icing_optimisationsLib =
struct

open floatToRealProofsTheory icing_realIdProofsTheory source_to_source2ProofsTheory
     listTheory Portable;
open preamble;

local
  fun mk_single_rewriteFPexp_correct_thm th1 th2 =
    let
      val arglist =
        th1 |> concl
        |> dest_forall |> snd
        |> dest_forall |> snd
        |> dest_forall |> snd
        |> dest_forall |> snd
        |> dest_forall |> snd
        |> rator |> rator |> rator |> rator |> rator |> rand;
      val arg =
        th2 |> concl
        |> dest_forall |> snd
        |> dest_forall |> snd
        |> dest_forall |> snd
        |> dest_forall |> snd
        |> dest_forall |> snd
        |> rator |> rator |> rator |> rator |> rator |> rand
        |> listSyntax.dest_list |> fst |> hd (* TODO: Check length *);
      in
      SIMP_RULE std_ss [GSYM AND_IMP_INTRO] rewriteExp_compositional
      |> SPECL [arglist,arg]
      |> (fn th => MP th th1)
      |> (fn th => MP th th2)
      |> SIMP_RULE std_ss [APPEND]
      end;
    fun mk_rewriteFPexp_correct_thm_list thms correctthm =
    case thms of
     [] => correctthm
    | th1::thms =>
      mk_rewriteFPexp_correct_thm_list thms (mk_single_rewriteFPexp_correct_thm correctthm th1);
    fun mk_rewriteFPexp_list_correct_thm th1 =
      let
      val arglist =
        th1 |> concl
        |> dest_forall |> snd
        |> dest_forall |> snd
        |> dest_forall |> snd
        |> dest_forall |> snd
        |> dest_forall |> snd
        |> rator |> rator |> rator |> rator |> rator |> rand;
      in
        SPEC arglist lift_rewriteFPexp_correct_list
        |> (fn th => MP th th1)
      end;

val all_optimisation_proofs =
  map (fn ((a,(b,c,d))) => (a,(b,c))) (DB.thy "icing_optimisationProofs");

(* Automatically prove a is_perform_rewrites_correct theorem for the given plan *)
fun mk_plan_correct_thm plan_list :(term * thm)=
  case plan_list of
    (* Base case: Empty plan -> No plan used in correctness theorem *)
    [] => (“[]:opt_step list”, is_perform_rewrites_correct_empty_plan)
  | p1 :: ps => (* Cons case *)
      let
        (* Recursive call *)
        val (rec_plan, rec_thm) = mk_plan_correct_thm ps
        (* Result plan, used for instantiation of theorems *)
        val full_plan = Parse.Term ‘^p1 :: ^rec_plan’
        (* Get the Datatype constructor used, can be "Label", "Expected" or "Apply" *)
        val dtype_comb = rator p1
       in
        (* Simple case: "Label s" --> can be appended to the correctness theorem *)
        if (Term.compare(dtype_comb, “source_to_source2$Label”) = EQUAL)
        then
          (full_plan,
              MP (Q.SPECL [‘^(rand p1)’, ‘^rec_plan’] is_perform_rewrites_correct_label) rec_thm)
        (* Simple case: "Expected e" --> can be appended to the correctness theorem *)
        else if (Term.compare(dtype_comb, “source_to_source2$Expected”) = EQUAL)
        then (full_plan,
              MP (Q.SPECL [‘^(rand p1)’, ‘^rec_plan’] is_perform_rewrites_correct_expected) rec_thm)
        else (* Must be an Apply (path, rws) now *)
        let
          val _ = if (Term.compare(dtype_comb, “source_to_source2$Apply”) <> EQUAL)
                  then raise Feedback.mk_HOL_ERR "" "" "Internal err, expected Apply" else ()
          val (pth, rws) = rand p1 |> dest_pair
          (* corr_thms = list of is_rewriteFPexp_correct theorems *)
          val corr_thms:thm list = rand p1
            |> dest_pair |> #2 (* extract the rewrites *)
            |> listSyntax.dest_list |> #1
            |> map (fn t => (t, DB.apropos_in t  all_optimisation_proofs)) (* Look up correctness theorems *)
            |> map (fn (t, thms) =>
                (print_term t; print (" has thm :\n"); map (fn d => print_thm (#1 (#2 d))) thms; print ("\n\n"); thms))
            |> map (fn datas => if (length datas <> 1)
                      then if (length datas = 0)
                          then raise Feedback.mk_HOL_ERR "" "" "Not enough matching theorems"
                          else raise Feedback.mk_HOL_ERR "" "" "Too many matching theorems"
                      else #1 (#2 (hd datas)))
            (* |> (fn datas => if (length datas <> 1) then raise ERR "Too many matching theorems" ""
                            else datas)*)
          (* Join the theorems into a single theorem about each of them*)
          val all_rewrites_correct_thm = mk_rewriteFPexp_correct_thm_list corr_thms empty_rw_correct
          (* lift the theorem to is_rewriteFPexp_list_correct *)
          val all_rewrites_list_correct_thm = mk_rewriteFPexp_list_correct_thm all_rewrites_correct_thm
          (* Extract argument list from theorem *)
          val args = all_rewrites_list_correct_thm |> concl
                           |> dest_forall |> snd |> dest_forall |> snd
                           |> dest_forall |> snd |> dest_forall |> snd
                           |> dest_forall |> snd
                           |> rator |> rator |> rator |> rator |> rator |> rand
          (* build a single perform_rewrites_correct theorem using modus-ponens *)
          val perform_rw_correct_thm =
            MP (Q.SPEC ‘^args’ is_rewriteFPexp_correct_lift_perform_rewrites)
                 all_rewrites_list_correct_thm
                 |> Q.SPEC ‘^(rand p1 |> dest_pair |> #1)’
          (* finally, use the "CONS" theorem for plans to prepend the current Apply node *)
          val final_perform_rw_thm =
           let
            val th1 = MP (Q.SPECL [‘^args’, ‘^(rand p1 |> dest_pair |> #1)’, ‘^rec_plan’]
                     is_perform_rewrites_correct_cons)
                   perform_rw_correct_thm
                in
               MP th1 rec_thm end
        in (full_plan, final_perform_rw_thm)
        end
        end;
  in
  fun mk_stos_pass_correct_thm plan_list =
    let
      val (thePlan, plan_correct_perform_rewrites) = mk_plan_correct_thm plan_list;
      val plan_correct_optimise_with_plan =
        MP (Q.SPEC ‘^thePlan’ is_optimise_with_plan_correct_lift)
           plan_correct_perform_rewrites
      (* val stos_pass_correct_with_plan =
        MP (Q.SPEC ‘[^thePlan]’ stos_pass_with_plans_correct)
          (MP (Q.SPEC ‘^thePlan’ is_optimise_with_plan_correct_sing)
              plan_correct_optimise_with_plan)
    in stos_pass_correct_with_plan *)
    in plan_correct_optimise_with_plan
    end;
end;

(** Real-valued identity proof *)
local
  fun mk_single_real_id_thm th1 th2 =
    let
    val arglist =
      th1 |> concl
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> rator |> rator |> rator |> rator |> rator |> rand;
    val arg =
      th2 |> concl
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> rator |> rator |> rator |> rator |> rator |> rand
      |> listSyntax.dest_list |> fst |> hd (* TODO: Check length *);
    in
    SIMP_RULE std_ss [GSYM AND_IMP_INTRO] real_valued_id_compositional
    |> SPECL [arglist,arg]
    |> (fn th => MP th th1)
    |> (fn th => MP th th2)
    |> SIMP_RULE std_ss [APPEND]
    end;
  fun mk_real_id_thm_list thms correctthm =
  case thms of
   [] => correctthm
  | th1::thms =>
    mk_real_id_thm_list thms (mk_single_real_id_thm correctthm th1);
  fun mk_real_id_list_thm th1 =
    let
    val arglist =
      th1 |> concl
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> dest_forall |> snd
      |> rator |> rator |> rator |> rator |> rator |> rand;
    in
      SPEC arglist lift_real_id_exp_list_strong
      |> (fn th => MP th th1)
    end;

val all_realid_proofs =
  map (fn ((a,(b,c,d))) => (a,(b,c))) (DB.thy "icing_realIdProofs");

(* Automatically prove a is_perform_rewrites_correct theorem for the given plan *)
fun mk_plan_correct_thm plan_list :(term * thm)=
  case plan_list of
    (* Base case: Empty plan -> No plan used in correctness theorem *)
    [] => (“[]:opt_step list”, is_real_id_perform_rewrites_empty)
  | p1 :: ps => (* Cons case *)
      let
        (* Recursive call *)
        val (rec_plan, rec_thm) = mk_plan_correct_thm ps
        (* Result plan, used for instantiation of theorems *)
        val full_plan = Parse.Term ‘^p1 :: ^rec_plan’
        (* Get the Datatype constructor used, can be "Label", "Expected" or "Apply" *)
        val dtype_comb = rator p1
       in
        (* Simple case: "Label s" --> can be appended to the correctness theorem *)
        if (Term.compare(dtype_comb, “source_to_source2$Label”) = EQUAL)
        then
          (full_plan,
              MP (Q.SPECL [‘^(rand p1)’, ‘^rec_plan’] is_perform_rewrites_correct_label_real_id) rec_thm)
        (* Simple case: "Expected e" --> can be appended to the correctness theorem *)
        else if (Term.compare(dtype_comb, “source_to_source2$Expected”) = EQUAL)
        then (full_plan,
              MP (Q.SPECL [‘^(rand p1)’, ‘^rec_plan’] is_perform_rewrites_correct_expected_real_id) rec_thm)
        else (* Must be an Apply (path, rws) now *)
        let
          val _ = if (Term.compare(dtype_comb, “source_to_source2$Apply”) <> EQUAL)
                  then raise Feedback.mk_HOL_ERR "" "" "Internal err, expected Apply" else ()
          val (pth, rws) = rand p1 |> dest_pair
          (* corr_thms = list of is_rewriteFPexp_correct theorems *)
          val corr_thms:thm list = rand p1
            |> dest_pair |> #2 (* extract the rewrites *)
            |> listSyntax.dest_list |> #1
            |> map (fn t => (t, DB.apropos_in t all_realid_proofs)) (* Look up correctness theorems *)
            |> map (fn (t, thms) =>
                (print_term t; print (":\n"); map (fn d => print_thm (#1 (#2 d))) thms; thms))
            |> map (fn datas => if (length datas <> 1)
                      then if (length datas = 0)
                          then raise Feedback.mk_HOL_ERR "" "" "Not enough matching theorems"
                          else raise Feedback.mk_HOL_ERR "" "" "Too many matching theorems"
                      else #1 (#2 (hd datas)))
            (* |> (fn datas => if (length datas <> 1) then raise ERR "Too many matching theorems" ""
                            else datas)*)
          (* Join the theorems into a single theorem about each of them*)
          val all_rewrites_correct_thm = mk_real_id_thm_list corr_thms empty_rw_real_id
          (* lift the theorem to is_rewriteFPexp_list_correct *)
          val all_rewrites_list_correct_thm = mk_real_id_list_thm all_rewrites_correct_thm
          (* Extract argument list from theorem *)
          val args = all_rewrites_list_correct_thm |> concl
                           |> dest_forall |> snd |> dest_forall |> snd
                           |> dest_forall |> snd |> dest_forall |> snd
                           |> dest_forall |> snd
                           |> rator |> rator |> rator |> rator |> rator |> rand
          (* build a single perform_rewrites_correct theorem using modus-ponens *)
          val perform_rw_correct_thm =
            MP (Q.SPEC ‘^args’ is_real_id_list_perform_rewrites_lift)
                 all_rewrites_list_correct_thm
                 |> Q.SPEC ‘^(rand p1 |> dest_pair |> #1)’
          (* finally, use the "CONS" theorem for plans to prepend the current Apply node *)
          val final_perform_rw_thm =
           let
            val th1 = MP (Q.SPECL [‘^args’, ‘^(rand p1 |> dest_pair |> #1)’, ‘^rec_plan’]
                     is_perform_rewrites_correct_cons_real_id)
                   perform_rw_correct_thm
                in
               MP th1 rec_thm end
        in (full_plan, final_perform_rw_thm)
        end
        end;

  in
  fun mk_stos_pass_real_id_thm plan_list =
    let
      val (thePlan, plan_correct_perform_rewrites) = mk_plan_correct_thm plan_list;
      val plan_correct_optimise_with_plan =
        MP (Q.SPEC ‘^thePlan’ is_real_id_perform_rewrites_optimise_with_plan_lift)
           plan_correct_perform_rewrites
      (* val stos_pass_correct_with_plan =
        MP (Q.SPEC ‘[^thePlan]’ stos_pass_with_plans_real_id)
          (MP (Q.SPEC ‘^thePlan’ is_optimise_with_plan_correct_sing_real_id)
              plan_correct_optimise_with_plan)
    in stos_pass_correct_with_plan *)
    in plan_correct_optimise_with_plan
    end;
end;

end
