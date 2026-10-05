(*
  Bench / playground for prove_EvalPatRel and prove_EvalPatBind.

  This script performs a tiny PMATCH translation, which causes
  pmatch_hol2deep to invoke prove_EvalPatRel and prove_EvalPatBind once per
  arm. The (asms, goal) inputs are recorded into

      ml_translatorLib.per_captures   (* (term list * term) list *)
      ml_translatorLib.peb_captures   (* term list *)

  After the translation runs, this script saves each capture as a theorem
  in this theory so they survive theory boundaries:

      bench_per_goal_<n>     -- prove_EvalPatRel goal for the n-th call
      bench_per_asms_<n>     -- conjunction of its assumption list
      bench_peb_goal_<n>     -- prove_EvalPatBind goal for the n-th call

  Recover them in another Script with `concl o fetch "bench_per" "..."`.
*)

Theory bench_per

Ancestors
  list pair patternMatches ml_pmatch ml_optimise ml_translator

Libs
  preamble ml_translatorLib patternMatchesLib patternMatchesSyntax

val _ = patternMatchesSyntax.temp_enable_pmatch ();
val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"];

val _ = ml_translatorLib.register_type ``:'a list``;
val _ = ml_translatorLib.register_type ``:'a option``;

val _ = ml_translatorLib.reset_per_captures ();

(* Tiny PMATCH definition that exercises both prove_EvalPatRel (per arm)
   and prove_EvalPatBind (for arms whose RHS uses bound pattern variables). *)
Definition bench_pmatch_def:
  bench_pmatch xs =
    pmatch xs of
    | [] => 0n
    | x :: ys => x
End

val r = ml_translatorLib.translate bench_pmatch_def;

(* Persist captures (most-recent-first → reverse for ascending call order). *)
local
  fun save_per_one (n, (asms, goal)) = let
    val asms_tm = if null asms then T else list_mk_conj asms
    val _ = Theory.save_thm
              ("bench_per_goal_" ^ Int.toString n, ASSUME goal)
    val _ = Theory.save_thm
              ("bench_per_asms_" ^ Int.toString n, ASSUME asms_tm)
    in () end
  fun save_peb_one (n, goal) =
    (Theory.save_thm
        ("bench_peb_goal_" ^ Int.toString n, ASSUME goal); ())
in
  val () = let
    val pers = rev (!ml_translatorLib.per_captures)
    val pebs = rev (!ml_translatorLib.peb_captures)
    val _ = List.app save_per_one (Lib.enumerate 0 pers)
    val _ = List.app save_peb_one (Lib.enumerate 0 pebs)
    val _ = print ("\n[bench_per] captured "
                   ^ Int.toString (length pers) ^ " EvalPatRel input(s) and "
                   ^ Int.toString (length pebs) ^ " EvalPatBind input(s).\n")
    fun show_per (n, (asms, goal)) = (
        print ("\n--- per #" ^ Int.toString n ^ " ---\n");
        print "  goal:\n    "; print_term goal; print "\n";
        print "  asms:\n";
        List.app (fn a => (print "    "; print_term a; print "\n")) asms)
    fun show_peb (n, goal) = (
        print ("\n--- peb #" ^ Int.toString n ^ " ---\n");
        print "  goal:\n    "; print_term goal; print "\n")
    val _ = List.app show_per (Lib.enumerate 0 pers)
    val _ = List.app show_peb (Lib.enumerate 0 pebs)
  in () end
end

(* Quick sanity replay on the most recent capture. *)
val _ =
  case !ml_translatorLib.per_captures of
    [] => print "[bench_per] no EvalPatRel captures!\n"
  | (_, goal) :: _ => let
      val _ =
        ml_translatorLib.prove_EvalPatRel goal ml_translatorLib.hol2deep
      val _ = print "[bench_per] prove_EvalPatRel sanity replay ok\n"
    in () end
