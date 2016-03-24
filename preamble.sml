structure preamble =
struct
local open intLib wordsLib in end
open HolKernel bossLib boolLib boolSimps pairLib markerLib lcsymtacs
     Parse Defn Tactic res_quanTheory quantHeuristicsLib pairTheory
     optionTheory sumTheory combinTheory listTheory rich_listTheory
     alistTheory llistTheory lprefix_lubTheory arithmeticTheory
     finite_mapTheory sptreeTheory pred_setTheory set_relationTheory
     relationTheory sortingTheory stringTheory wordsTheory miscTheory
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
(* -- *)

val _ = set_trace"Goalstack.print_goal_at_top"0 handle HOL_ERR _ => set_trace"goalstack print goal at top"0

(* treat the given eq_tms (list of equations) as rewrite thereoms,
   return the resulting term, note we can't return a theorem because
   the equations might not be theorems -- indeed, in many cases they
   won't be theorems.
*)
fun term_rewrite eq_tms tm =
  tm |> QCONV (PURE_REWRITE_CONV (map (curry mk_thm []) eq_tms))
     |> concl |> rhs

(* replace (syntactically equal) subterms of one term by another *)
(* TODO: can Term.subst be used instead always? If so, delete. *)
fun replace_term from to =
  let
    fun f tm =
      if tm = from then to else
        case dest_term tm of
          COMB(t1,t2) => mk_comb(f t1, f t2)
        | LAMB(t1,t2) => mk_abs(f t1, f t2)
        | _ => tm
  in
    f
  end

(* TODO: replace these with qhdtm_assum etc. *)
local
  fun find t asl =
    case total (first (can (match_term t) o fst o strip_comb)) asl of SOME x => x
    | NONE => first (can (match_term t o fst o strip_comb o lhs)) asl
in
  fun RATOR_X_ASSUM t ttac (g as (asl,w)) = UNDISCH_THEN (find t asl) ttac g
  fun rator_x_assum q ttac = Q_TAC (C RATOR_X_ASSUM ttac) q

  fun RATOR_ASSUM t ttac (g as (asl,w)) = ttac (ASSUME (find t asl)) g
  fun rator_assum q ttac = Q_TAC (C RATOR_ASSUM ttac) q
end
(* -- *)

val preamble_ERR = mk_HOL_ERR"preamble"

fun subterm f = partial(preamble_ERR"subterm""not found") (bvk_find_term (K true) f)

fun drule th =
  first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))

val SWAP_IMP = PROVE[]``(P ==> Q ==> R) ==> (Q ==> P ==> R)``

(* TODO: this doesn't prove the hyps if there's more than one *)
fun prove_hyps_by tac th = PROVE_HYP (prove(list_mk_conj (hyp th),tac)) th

(* if the first conjunct under the goal's existential prefix matches the term
   except for some places where it has structure and the term just has variables,
   then pair split all those variables *)
fun split_pair_match tm (g as (_,w)) =
  let
    val (vs,b) = strip_exists w
    val cs = strip_conj b val c = hd cs
    val cs = op::(strip_comb c)
    val ts = op::(strip_comb tm)
    val ss = map2 (total o match_term) ts cs
    val vs = map ((fn x => map #redex (Option.valOf x) handle _ => []) o
                  (Option.map fst)) ss
    val vs = flatten vs
    val _ = assert(List.all (fn (x,y) => not (is_const x) orelse isSome y)) (zip cs ss)
  in
    map_every (TRY o PairCases_on) (map (C cons [] o ANTIQUOTE) vs)
  end g

(* the theorem is of the form [!x1 .. xn. P] and the goal contains a subterm
   [f v1 .. vn]. apply ttac to [P[vi/xi]]. *)
fun specl_args_of_then f th (ttac:thm_tactic) (g as (_,w)) =
  let
    val t = find_term (same_const f o fst o strip_comb) w
    val (_,vs) = strip_comb t
  in
    ttac (ISPECL vs th)
  end g

(* TODO: all the following might not be used? *)

(* the theorem is of the form [!x1 ... xn. P ==> ?y1 ... ym. Q /\ ...]
   the goal is of the form [?z1 ... zk. Q' /\ ...]
   instantiate the xs as necessary to make Q and Q' match as much as possible
   (complete match impossible if some of Q's variables are the ys) *)
fun exists_match_mp_then (ttac:thm_tactic) th (g as (_,w)) =
  let
    val (ws,b) = strip_exists w
    val cs = strip_conj b val c = hd cs
    val (vs,t) = strip_forall (concl th)
    val vs = map (fst o dest_var o variant (free_vars b)) vs
    val th = CONV_RULE (RENAME_VARS_CONV vs) th
    val (vs,t) = strip_forall (concl th)
    val (_,b) = dest_imp t
    val (_,b) = strip_exists b
    val ts = strip_conj b val t = hd ts
    val (tms,_) = match_term t c
    val tms = filter (C mem vs o #redex) tms
    val tms = filter (not o C mem ws o #residue) tms
    val xs = map #redex tms
    val ys = map #residue tms
    fun sorter ls = xs@(filter(not o C mem xs) ls)
    val th = SPECL ys (CONV_RULE (RESORT_FORALL_CONV sorter) th)
  in
    ttac th
  end g

(* the theorem is of the form [!x1..n. P ==> Q]
   the goal is of the form [?y1..n. Q' /\ ...]
   replace the goal with [?y1..n. P /\ ...] by
   making the Q and Q' match *)
fun exists_suff_tac th (g as (_,w)) =
  let
    val (ws,b) = strip_exists w
    val bs = strip_conj b
    val th = GEN_ALL(PART_MATCH (snd o dest_imp) th (hd bs))
    val (vs,c) = strip_forall (concl th)
    val (b',_) = dest_imp c
  in
    suff_tac(list_mk_exists(ws,list_mk_conj(b'::tl bs))) >- metis_tac[th]
  end g

(* the theorem is of the form [!x1..n. P ==> ?y1..m. Q /\ A]
   the goal is of the form [?z1..k. Q' /\ B]
   specialise the theorem to make Q and Q' match as much as possible then
   regeneralise then apply the theorem tactic *)
fun exists_suff_gen_then ttac th (g as (_,w)) =
  let
    val (ws,b) = strip_exists w
    val bs = strip_conj b
    val th = (GEN_ALL(PART_MATCH (hd o strip_conj o snd o strip_exists o snd o dest_imp) th (hd bs)))
  in ttac th end g

(* the theorem is of the form [!x1..n. P ==> ?y1..m. Q /\ A]
   the goal is of the form [?z1..k. Q' /\ B]
   specialise the theorem to make Q and Q' match as much as possible then
   apply the theorem tactic *)
fun exists_suff_then ttac th (g as (_,w)) =
  let
    val (ws,b) = strip_exists w
    val bs = strip_conj b
    val th = (PART_MATCH (hd o strip_conj o snd o strip_exists o snd o dest_imp) th (hd bs))
  in ttac th end g

fun loseC c =
    first_x_assum
      (K ALL_TAC o assert (can (find_term (same_const c)) o concl))

val kill_asm_guard =
    disch_then (fn th => SUBGOAL_THEN (lhand (concl th))
                                      (MP_TAC o MATCH_MP th)) >- simp[]

fun qispl_then [] ttac = ttac
  | qispl_then (q::qs) ttac = Q.ISPEC_THEN q (qispl_then qs ttac)
fun qxchl [] ttac = ttac
  | qxchl (q::qs) ttac = Q.X_CHOOSE_THEN q (qxchl qs ttac)
val rveq = rpt BasicProvers.VAR_EQ_TAC

fun erule k th = let
  fun c th = let
    val (vs, body) = strip_forall (concl th)
  in
    if is_imp body then
      first_assum (c o MATCH_MP th) ORELSE
      first_assum (c o MATCH_MP th o SYM)
    else k th
  end
  fun is_resolvable th = let
    val (vs, body) = strip_forall (concl th)
  in
    is_imp body
  end
in
  if is_resolvable th then c th else NO_TAC
end

fun print_tac s (g as (asl,w)) = let
  fun mmlnt_test t = is_const t andalso type_of t = ``:MMLnonT``
in
  case get_first (Lib.total (find_term mmlnt_test)) asl of
      NONE => raise Fail "No MMLnonT in goal"
    | SOME t => if term_to_string t = s then
                  (print ("print_tac: "^s^"\n"); ALL_TAC g)
                else raise Fail ("MMLnonT not "^s)
end

fun simple_match_mp th1 th2 = let
  val (x,y) = dest_imp (concl th1)
  val (i,t) = match_term x (concl th2)
  in MP (INST i (INST_TYPE t th1)) th2 end

end
