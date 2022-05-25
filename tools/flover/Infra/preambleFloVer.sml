(*
   Proof tools (e.g. tactics) used throughout the development.
*)
structure preambleFloVer =
struct
local open intLib wordsLib in end;
open set_relationTheory; (* comes first so relationTheory takes precedence *)
open ASCIInumbersTheory BasicProvers Defn HolKernel Parse SatisfySimps Tactic
     monadsyntax alistTheory alignmentTheory arithmeticTheory bagTheory boolLib
     boolSimps bossLib containerTheory combinTheory dep_rewrite
     finite_mapTheory indexedListsTheory listTheory llistTheory
     markerLib mp_then optionTheory pairLib pairTheory pred_setTheory
     quantHeuristicsLib relationTheory res_quanTheory
     rich_listTheory sortingTheory sptreeTheory stringTheory sumTheory
     wordsTheory;
(* TOOD: move? *)
val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val full_case_tac = BasicProvers.FULL_CASE_TAC;
val sym_sub_tac = SUBST_ALL_TAC o SYM;
fun asm_match q = Q.MATCH_ASSUM_RENAME_TAC q
val match_exists_tac = part_match_exists_tac (hd o strip_conj)
val asm_exists_tac = first_assum(match_exists_tac o concl)
val has_pair_type = can dest_prod o type_of
fun impl_subgoal_tac th =
  let
    val hyp_to_prove = lhand (concl th)
  in
    SUBGOAL_THEN hyp_to_prove (fn thm => assume_tac (MP th thm))
  end;
val rveq = rpt BasicProvers.VAR_EQ_TAC

(* -- *)

fun check_tag t = Tag.isEmpty t orelse Tag.isDisk t
val check_thm = Lib.assert (check_tag o Thm.tag)

val option_bind_tm = prim_mk_const{Thy="option",Name="OPTION_BIND"};
val option_ignore_bind_tm = prim_mk_const{Thy="option",Name="OPTION_IGNORE_BIND"};
val option_guard_tm = prim_mk_const{Thy="option",Name="OPTION_GUARD"};

structure option_monadsyntax = struct
fun temp_add_option_monadsyntax() =
  let
    open monadsyntax
  in
    temp_enable_monadsyntax ();
    temp_enable_monad "option"
  end

fun add_option_monadsyntax() =
  let
    open monadsyntax
  in
    enable_monadsyntax();
    enable_monad "option"
  end
end

val _ = set_trace"Goalstack.print_goal_at_top"0 handle HOL_ERR _ => set_trace"goalstack print goal at top"0

(* treat the given eq_tms (list of equations) as rewrite thereoms,
   return the resulting term, note we can't return a theorem because
   the equations might not be theorems -- indeed, in many cases they
   won't be theorems.
*)
fun term_rewrite eq_tms tm =
  tm |> QCONV (PURE_REWRITE_CONV (map (curry mk_thm []) eq_tms))
     |> concl |> rhs

(* TODO: move to Lib (or Portable)? *)
fun itlist3 f L1 L2 L3 base_value =
  let
    fun itl ([], [], []) = base_value
      | itl (a :: rst1, b :: rst2, c :: rst3) = f a b c (itl (rst1, rst2, rst3))
      | itl _ = raise mk_HOL_ERR "Lib" "itlist3" "lists of different length"
    in
      itl (L1, L2, L3)
    end

fun zip3 ([],[],[]) = []
  | zip3 ((h1::t1),(h2::t2),(h3::t3)) = ((h1,h2,h3)::zip3(t1,t2,t3))
  | zip3 _ = raise mk_HOL_ERR "Lib" "zip3" "lists of different length"

infix 8 $
fun op $ (f,x) = f x

fun pad_to sz str =
  CharVector.tabulate(Int.max(0,sz-String.size str),K #" ")^str

val sum = foldl (op+) 0

fun println s = print (strcat s "\n");
(* -- *)

end
