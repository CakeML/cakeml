structure miscLib = struct
open HolKernel boolLib bossLib lcsymtacs

val _ = set_trace"Goalstack.print_goal_at_top"0 handle HOL_ERR _ => set_trace"goalstack print goal at top"0

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

val IMP_IMP = METIS_PROVE[]``(P /\ (Q ==> R)) ==> ((P ==> Q) ==> R)``
val discharge_hyps = match_mp_tac IMP_IMP >> conj_tac
val discharge_hyps_keep = match_mp_tac IMP_IMP >> conj_asm1_tac
val SWAP_IMP = PROVE[]``(P ==> Q ==> R) ==> (Q ==> P ==> R)``

fun prove_hyps_by tac th = PROVE_HYP (prove(list_mk_conj (hyp th),tac)) th

(* from theorems of the form |- P x1, |- P x2, ..., produce |- EVERY P [x1,x2,...] *)

fun join_EVERY P =
  let
    val nilth = listTheory.EVERY_DEF |> CONJUNCT1 |> ISPEC P |> EQT_ELIM
    val consth = listTheory.EVERY_DEF |> CONJUNCT2 |> ISPEC P |> SPEC_ALL |> EQ_IMP_RULE |> snd
                 |> REWRITE_RULE[GSYM AND_IMP_INTRO]
    fun f [] = nilth
      | f (t::ts) = MATCH_MP (MATCH_MP consth t) (f ts)
  in
    f
  end

(* resort conjuncts so that one satisfying P appears first *)
local
  val finish = TRY_CONV (REWR_CONV (GSYM CONJ_ASSOC))
in
  fun lift_conjunct_conv P =
    let
      fun loop tm =
        if P tm handle HOL_ERR _ => false then ALL_CONV
        else
          let
            val (c1,c2) = dest_conj tm
          in
            (LAND_CONV (loop c1) THENC finish) ORELSEC
            (RAND_CONV (loop c2) THENC REWR_CONV CONJ_SYM THENC finish)
          end handle HOL_ERR _ => NO_CONV
    in
      W loop
    end
end

fun sort_vars [] l2 = l2
  | sort_vars (s::l1) l2 =
    let
      val (s,l2) = partition (equal s o fst o dest_var) l2
    in
      s @ (sort_vars l1 l2)
    end

(* provide witnesses to make the first conjunct under the goal's existential
   prefix match the given term *)
fun match_exists_tac tm (g as (_,w)) =
  let
    val (vs,b) = strip_exists w
    val vs = map (fst o dest_var o variant (free_vars tm)) vs
    fun k (g as (_,w)) =
      let
        val (_,b) = strip_exists w
        val cs = strip_conj b val c = hd cs
        val (tms,_) = match_term c tm
        val xs = map #redex tms
        val ys = map #residue tms
        fun sorter ls = xs@(List.filter(not o Lib.C Lib.mem xs)ls)
      in
        CONV_TAC(RESORT_EXISTS_CONV sorter) >>
        map_every exists_tac ys
      end g
  in
    CONV_TAC(RENAME_VARS_CONV vs) >> k
  end g

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

fun split_applied_pair_tac tm =
  let
    val (f,p) = dest_comb tm
    val (x,b) = pairSyntax.dest_pabs f
    val xs = pairSyntax.strip_pair x
    val g = list_mk_exists(xs,mk_eq(p,x))
    val th = prove(g, SIMP_TAC bool_ss [GSYM pairTheory.EXISTS_PROD])
  in
    strip_assume_tac th
  end

local
  val is_pair_case = same_const``pair_CASE``
  exception Not_pair_case
  fun loop tm vs =
    let
      val (f,x) = dest_comb tm
      val _ = assert is_pair_case (fst (strip_comb f))
    in
      let
        val (v,b) = dest_abs x
        val vs = v::vs
      in
        case total dest_abs b of
          NONE => (vs,tm)
        | SOME (v,tm) => loop tm vs
          handle Not_pair_case => (v::vs,tm)
      end handle HOL_ERR _ => (vs,tm)
    end handle HOL_ERR _ => raise Not_pair_case
in
  fun strip_pair_case tm =
    (case loop tm [] of (vs,b) => (rand(rator tm),rev vs,b))
    handle Not_pair_case => raise mk_HOL_ERR "" "strip_pair_case" "not a pair case"
end

fun split_pair_case_tac tm =
  let
    val (p,vs,b) = strip_pair_case tm
    val g = list_mk_exists(vs,mk_eq(p,pairSyntax.list_mk_pair vs))
    val th = prove(g, SIMP_TAC bool_ss [GSYM pairTheory.EXISTS_PROD])
  in
    strip_assume_tac th
  end

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

(* the theorem is of the form [!x1 .. xn. P] and the goal contains a subterm
   [f v1 .. vn]. apply ttac to [P[vi/xi]]. *)
fun specl_args_of_then f th (ttac:thm_tactic) (g as (_,w)) =
  let
    val t = find_term (same_const f o fst o strip_comb) w
    val (_,vs) = strip_comb t
  in
    ttac (ISPECL vs th)
  end g

end
