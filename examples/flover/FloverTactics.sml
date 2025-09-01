(*
  Some tactics which ease proving goals
*)

structure FloverTactics =
struct

local open intLib wordsLib in end;
open set_relationTheory;
open BasicProvers Defn HolKernel Parse Tactic monadsyntax
     alistTheory arithmeticTheory bagTheory boolLib boolSimps bossLib
     combinTheory dep_rewrite finite_mapTheory indexedListsTheory
     listTheory llistTheory markerLib
     optionTheory pairLib pairTheory pred_setTheory
     quantHeuristicsLib relationTheory res_quanTheory rich_listTheory
     sortingTheory sptreeTheory stringTheory sumTheory wordsTheory simpLib;
open ExpressionsTheory CommandsTheory;

fun elim_conj thm =
  let val (hypl, concl) = dest_thm thm in
      if is_conj concl
      then
          let val (thm1, thm2) = CONJ_PAIR thm in
              elim_conj thm1 \\ elim_conj thm2
          end
      else
          ASSUME_TAC thm
  end;

fun elim_exist1 thm =
  let val (hypl, concl) = dest_thm thm in
      if is_exists concl
      then CHOOSE_THEN elim_exist thm
      else elim_conj thm
  end
and elim_exist thm =
  let val (hypl, concl) = dest_thm thm in
      if is_exists concl
      then CHOOSE_THEN elim_exist1 thm
      else elim_conj thm
  end;

fun inversion pattern cases_thm =
  qpat_x_assum pattern
    (fn thm => elim_exist (ONCE_REWRITE_RULE [cases_thm] thm));

fun qexistsl_tac termlist =
  case termlist of
      [] => ALL_TAC
    | t::tel => qexists_tac t \\ qexistsl_tac tel;

fun specialize pat_hyp pat_thm =
  qpat_x_assum pat_hyp
    (fn hyp =>
      (qspec_then pat_thm ASSUME_TAC hyp) ORELSE
      (qpat_assum pat_thm
         (fn asm => ASSUME_TAC (MP hyp asm))));

fun rw_asm pat_asm =
  qpat_x_assum pat_asm
    (fn asm =>
      (once_rewrite_tac [asm] \\ ASSUME_TAC asm));

fun rw_asm_star pat_asm =
  qpat_x_assum pat_asm
    (fn asm =>
        fs [Once asm] \\ ASSUME_TAC asm);

fun rw_sym_asm pat_asm =
  qpat_x_assum pat_asm
    (fn asm =>
      (once_rewrite_tac [GSYM asm] \\ ASSUME_TAC asm));

fun rw_thm_asm pat_asm thm =
  qpat_x_assum pat_asm
    (fn asm =>
      (ASSUME_TAC (ONCE_REWRITE_RULE[thm] asm)));


(* Destruct like tactic, by Michael Norrish, see HOL-info **)
(* Given theorem
  P x y z ==> ?w. Q w
  introduce P x y z as a subgoal and Q w for some w as hypothesis *)
fun destruct th =
  let
      val hyp_to_prove = lhand (concl th)
  in
      SUBGOAL_THEN hyp_to_prove (fn thm => STRIP_ASSUME_TAC (MP th thm))
  end

fun impl_subgoal_tac th =
  let
      val hyp_to_prove = lhand (concl th)
  in
      SUBGOAL_THEN hyp_to_prove (fn thm => assume_tac (MP th thm))
  end

val flover_eval_tac :tactic=
  let val _ =  computeLib.del_funs([sptreeTheory.lookup_def])
      val _ = computeLib.add_funs([sptreeTheory.lookup_compute]) in
    computeLib.EVAL_TAC
    \\ fs[sptreeTheory.lookup_def]
    \\ rpt strip_tac
    \\ fs[sptreeTheory.lookup_def]
    \\ EVAL_TAC
end;

fun iter_exists_tac ind n =
  fn tm =>
    if ind < n
    then
      (part_match_exists_tac
        (fn concl => List.nth (strip_conj concl, ind)) tm)
        ORELSE (iter_exists_tac (ind+1) n tm)
    else
      FAIL_TAC (concat ["No matching clause found for ", term_to_string tm]) ;

val try_all:term -> tactic =
  fn tm =>
    fn (asl, g) =>
      let
        val len = length (strip_conj (snd (dest_exists g))) in
        iter_exists_tac 0 len tm (asl, g)
     end;

val find_exists_tac =
  first_assum (try_all o concl);

val bool_simps = Q.prove (
  ‘(∀ P. (P ∧ F) = F) ∧
  (∀ P. (F ∨ P) = P) ∧
  (∀ P Q. (if P then Q else F) = (P ∧ Q))’, fs[]);

val cond_simp = Q.prove (
‘(if P then Q else R) = (P /\ Q \/ ~P /\ R)’,
  TOP_CASE_TAC);

val flover_ss =
  (mk_simpset ([DatatypeSimps.case_cong_ss [“:real expr”, “:real cmd”]]
              @ ssfrags_of bool_ss))
             && [option_case_eq |> GEN “v:'b” |> Q.ISPEC ‘T’ |> SIMP_RULE bool_ss [],
                 pair_case_eq |> GEN “v:'a” |> Q.ISPEC ‘T’ |> SIMP_RULE bool_ss [],
                 expr_case_eq |> GEN “v:'a” |> Q.ISPEC ‘T’ |> SIMP_RULE bool_ss [],
                 cmd_case_eq |> GEN “v:'a” |> Q.ISPEC ‘T’ |> SIMP_RULE bool_ss [],
                 bool_simps, cond_simp, PULL_EXISTS];

end
