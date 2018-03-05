structure cfTacticsBaseLib :> cfTacticsBaseLib =
struct

open preamble
open set_sepTheory helperLib ConseqConv
open quantHeuristicsTools

structure Parse =
struct
  open Parse
  val (Type,Term) = parse_from_grammars
                      (merge_grammars ["cmlPtreeConversion", "cmlPEG",
                                       "pegexec",
                                       "semanticPrimitives", "lexer_fun"])
end
open Parse

fun find_map f [] = NONE
  | find_map f (x :: xs) =
    (case f x of
         NONE => find_map f xs
       | SOME y => SOME y)

(*----------------------------------------------------------------------------*)
(* Conv++ *)

fun NCONV 0 conv = REFL
  | NCONV 1 conv = conv
  | NCONV n conv = conv THENC (NCONV (n-1) conv)

fun UNCHANGED_CONV conv t =
  let val thm = conv t
      val (l,r) = dest_eq (concl thm) in
    if l ~~ r then raise UNCHANGED else thm
  end

(*------------------------------------------------------------------*)

fun gen_try_one_instantiate_tac () = let
  val already_tried_tms = ref []
  fun to_try_next body = let
    val conjs = strip_conj body
  in
    case List.find (fn tm => not (tmem tm (!already_tried_tms))) conjs of
        NONE => fail ()
      | SOME tm => tm
  end

  fun tac (g as (_, w)) = let
    val try_tm = to_try_next (snd (strip_exists w))
    fun register_tm_tac g =
      (already_tried_tms := try_tm :: !already_tried_tms;
       ALL_TAC g)
  in
    (TRY (first_assum ((part_match_exists_tac to_try_next) o concl))
     \\ register_tm_tac) g
  end
in tac end

fun rpt_until_change tac g = let
  val (gl, p) = tac g
in
  if goals_eq gl [g] then rpt_until_change tac g
  else (gl, p)
end

fun instantiate1 g = let
  val tac = gen_try_one_instantiate_tac ()
in (rpt_until_change tac \\ simp []) g end

val instantiate = CHANGED_TAC (rpt instantiate1)

fun progress_then thm_tac thm =
  drule thm \\ rpt (disch_then drule) \\ disch_then thm_tac

fun try_progress_then thm_tac thm =
  ((drule thm \\ rpt (disch_then drule)) ORELSE mp_tac thm) \\
  disch_then thm_tac
  handle HOL_ERR _ => thm_tac thm

fun progress thm = progress_then strip_assume_tac thm

fun progress_with_then thm_tac thm' thm =
  mp_tac (MATCH_MP thm thm') \\ rpt (disch_then drule) \\ disch_then thm_tac

fun progress_with thm' thm = progress_with_then strip_assume_tac thm' thm

fun sing x = [x]

fun try_finally tac = TRY (tac \\ NO_TAC)

fun EVAL_PAT pat tm =
  if can (match_term pat) tm then
    EVAL tm
  else
    NO_CONV tm

fun eval_pat_tac pat = CONV_TAC (DEPTH_CONV (EVAL_PAT pat))
val qeval_pat_tac = Q_TAC eval_pat_tac

fun compute_pat cs pat tm =
  if can (match_term pat) tm then
    (computeLib.CBV_CONV cs THENC EVAL) tm   (* TODO: remove EVAL *)
  else
    NO_CONV tm

fun compute_pat_tac cs pat = CONV_TAC (DEPTH_CONV (compute_pat cs pat))
fun qcompute_pat_tac cs = Q_TAC (compute_pat_tac cs)

fun hnf_conv tm =
    let val (f, xs) = strip_comb tm in
      if is_abs f then
        ((funpow (length xs - 1) RATOR_CONV) BETA_CONV
         THENC hnf_conv) tm
      else
        REFL tm
    end

val hnf =
    TRY (CONV_TAC hnf_conv)

(* ? *)
val cbv = TRY (CONV_TAC (REDEPTH_CONV BETA_CONV))

fun rewr_head_conv thm tm =
  let val (_, args) = strip_comb tm
      val (_, args') = strip_comb ((lhs o concl) (SPEC_ALL thm))
      val extra_args_nb = (length args) - (length args')
      val conv =
          if extra_args_nb < 0 then failwith "rewr_head_conv"
          else (funpow extra_args_nb RATOR_CONV) (REWR_CONV thm)
  in conv tm end

open cmlPEGTheory gramTheory cmlPtreeConversionTheory
     grammarTheory lexer_funTheory lexer_implTheory

val parse_t =
  Lib.with_flag (Feedback.MESG_outstream, (fn s => ()))
   Parse.Term
     `\inputnt sem s.
        case
          peg_exec cmlPEG (nt (mkNT inputnt) I) (lexer_fun s) [] done failed
        of
          Result (SOME([],[x])) => sem x : 'a
        | Result (SOME (toks, _)) =>
            ARB (ARB "Parse failed with remaining tokens" toks)
        | _ => ARB "Parse failed"`

fun string_of_q [] = ""
  | string_of_q (QUOTE s :: qs) = s ^ (string_of_q qs)
  | string_of_q (ANTIQUOTE s :: qs) = s ^ (string_of_q qs)

fun parse nt sem q =
  let
    val (_,r) = dom_rng (type_of sem)
  in
    EVAL (list_mk_comb(inst [alpha |-> r] parse_t,
                       [nt, sem, stringSyntax.fromMLstring (string_of_q q)]))
         |> concl |> rhs |> rand
  end

val parse_exp = parse ``nE`` ``ptree_Expr nE``
val parse_decl = parse ``nDecl`` ``ptree_Decl``
val parse_topdecs = parse ``nTopLevelDecs`` ``ptree_TopLevelDecs``

(* for debugging
val st = (basis_st())
val name = "Word8Array.array"
*)

val nEbase_t = ``nEbase``
val ptree_t = ``ptree_Expr nEbase``
fun fetch_v name st =
  let
      val env = ml_progLib.get_env st
      val ident_expr = parse nEbase_t ptree_t [QUOTE name]
      val ident_expr = find_term astSyntax.is_Var ident_expr
      val ident = astSyntax.dest_Var ident_expr
      val evalth = (REWRITE_CONV [ml_progTheory.nsLookup_merge_env] THENC EVAL)
                      ``nsLookup (^env).v ^ident``
  in (optionLib.dest_some o rhs o concl) evalth end

fun fetch_def name st =
  let val v = fetch_v name st
      val v_defs = ml_progLib.get_v_defs st
      val opt_thm = List.find (aconv v o (lhs o concl)) v_defs
  in valOf opt_thm end

(*------------------------------------------------------------------*)
(** ConseqConv++ *)

infixr 3 THEN_DCC
infixr 3 ORELSE_DCC

fun CONSEQ_CONV_WRAPPER___CONVERT_RESULT dir thm t =
let
   val thm_term	= concl	thm;
in
   if (aconv thm_term t) then
      CONSEQ_CONV_WRAPPER___CONVERT_RESULT dir (EQT_INTRO thm) t
   else if (is_imp_only thm_term) then
      let
         val (t1, t2) = dest_imp thm_term;
         val _ = if (aconv t1 t2) then raise UNCHANGED else ();

         val g' = if (aconv t2 t) then CONSEQ_CONV_STRENGTHEN_direction else
                  if (aconv t1 t) then CONSEQ_CONV_WEAKEN_direction else
                  raise UNCHANGED;
         val g'' = if (dir = CONSEQ_CONV_UNKNOWN_direction) then g' else dir;
         val _ = if not (g' = g'') then raise UNCHANGED else ();
      in
         (g'', thm)
      end
   else if (is_eq thm_term) then
      (dir,
        if ((lhs thm_term ~~ t) andalso not (rhs thm_term ~~ t)) then
           if (dir = CONSEQ_CONV_UNKNOWN_direction) then
              thm
           else if (dir = CONSEQ_CONV_STRENGTHEN_direction) then
              snd (EQ_IMP_RULE thm)
           else
              fst (EQ_IMP_RULE thm)
        else raise UNCHANGED)
   else
      raise UNCHANGED
end

fun CUSTOM_THEN_CONSEQ_CONV handler1 handler2 (c1:conv) c2 t =
    let
       val thm0_opt =
           SOME (c1 t) handle e => if handler1 e then NONE else raise e

       val t2 =
           if (isSome thm0_opt) then
             CONSEQ_CONV___GET_SIMPLIFIED_TERM (valOf thm0_opt) t
           else t;

       val thm1_opt =
           SOME (c2 t2) handle e => if handler2 e then NONE else raise e
    in
       if (isSome thm0_opt) andalso (isSome thm1_opt) then
         THEN_CONSEQ_CONV___combine (valOf thm0_opt) (valOf thm1_opt) t else
       if (isSome thm0_opt) then valOf thm0_opt else
       if (isSome thm1_opt) then valOf thm1_opt else
       raise UNCHANGED
    end

fun handle_none e = false
fun handle_UNCHANGED e = case e of UNCHANGED => true | _ => false

(* This has different semantics than [ConseqConv.THEN_CONSEQ_CONV], but I
   believe these are the right ones.

   Just like [Conv.THENC], it fails if either the first or the second conversion
   fails, while [ConseqConv.THEN_CONSEQ_CONV] handles a failure just like
   raising [UNCHANGED], which makes it impossible to make the first conversion
   abort a THEN_CONSEQ_CONV.
*)
val THEN_CONSEQ_CONV =
    CUSTOM_THEN_CONSEQ_CONV handle_UNCHANGED handle_UNCHANGED

fun ORELSE_CONSEQ_CONV (c1:conv) (c2:conv) t =
  c1 t handle HOL_ERR _ => c2 t

fun EVERY_CONSEQ_CONV [] t = raise UNCHANGED
  | EVERY_CONSEQ_CONV ((c1:conv)::L) t =
    (THEN_CONSEQ_CONV c1 (EVERY_CONSEQ_CONV L)) t

fun FIRST_CONSEQ_CONV [] t = raise UNCHANGED
  | FIRST_CONSEQ_CONV (c1::L) t =
    ORELSE_CONSEQ_CONV c1 (FIRST_CONSEQ_CONV L) t

fun CUSTOM_THEN_DCC THEN_CC DCC1 DCC2 direction =
  THEN_CC (DCC1 direction) (DCC2 direction)

fun (DCC1 THEN_DCC DCC2) =
  CUSTOM_THEN_DCC THEN_CONSEQ_CONV DCC1 DCC2

fun (DCC1 ORELSE_DCC DCC2) direction =
  ORELSE_CONSEQ_CONV (DCC1 direction) (DCC2 direction)

fun EVERY_DCC [] direction t = raise UNCHANGED
  | EVERY_DCC (c1::L) direction t =
    (c1 THEN_DCC (EVERY_DCC L)) direction t

fun CONV_DCC conv dir t =
let
   val _ = if (type_of t = bool) then () else raise UNCHANGED;
   val thm = conv t
in
  snd (CONSEQ_CONV_WRAPPER___CONVERT_RESULT dir thm t)
end

fun STRENGTHEN_CONSEQ_CONV conv dir =
  if dir = CONSEQ_CONV_WEAKEN_direction then raise UNCHANGED
  else CONV_DCC conv dir

fun WEAKEN_CONSEQ_CONV conv dir =
  if dir = CONSEQ_CONV_STRENGTHEN_direction then raise UNCHANGED
  else CONV_DCC conv dir

fun CHANGED_DCC dcc direction =
  CHANGED_CONSEQ_CONV (dcc direction)

fun QCHANGED_DCC dcc direction =
  QCHANGED_CONSEQ_CONV (dcc direction)

fun TOP_REDEPTH_CONSEQ_CONV dcc =
  let val STRICT_THEN = CUSTOM_THEN_CONSEQ_CONV handle_none handle_UNCHANGED
      val STRICT_THEN_DCC = CUSTOM_THEN_DCC STRICT_THEN
  in
    STRICT_THEN_DCC dcc (REDEPTH_CONSEQ_CONV dcc)
  end

fun mk_binop_conseq_conv mono_thm =
  let
    fun cc_l_r cc1 cc2 t =
      let val (l,r) = (rand (rator t), rand t)
          val thm_l_r = CONJ (cc1 l) (cc2 r)
          val thm = GEN_ALL mono_thm
      in
        HO_MATCH_MP thm thm_l_r
      end
    fun cc_l cc = cc_l_r cc REFL_CONSEQ_CONV
    fun cc_r cc = cc_l_r REFL_CONSEQ_CONV cc
    fun cc_list assoc_left ccL =
      let fun aux ccL =
            case ccL of
                [] => (fn t => raise UNCHANGED)
              | [cc] => cc
              | cc1::cc2::ccs =>
                if assoc_left then
                  cc_l_r (aux (cc2::ccs)) cc1
                else
                  cc_l_r cc1 (aux (cc2::ccs)) in
        if assoc_left then aux (List.rev ccL) else aux ccL
      end
  in
    (cc_l_r, cc_l, cc_r, cc_list)
  end

val (CONJ_CONSEQ_CONV, CONJ1_CONSEQ_CONV, CONJ2_CONSEQ_CONV,
     CONJ_LIST_CONSEQ_CONV) =
    mk_binop_conseq_conv boolTheory.MONO_AND
val CONJ_LIST_CONSEQ_CONV = CONJ_LIST_CONSEQ_CONV false

val (DISJ_CONSEQ_CONV, DISJ1_CONSEQ_CONV, DISJ2_CONSEQ_CONV,
     DISJ_LIST_CONSEQ_CONV) =
    mk_binop_conseq_conv boolTheory.MONO_OR
val DISJ_LIST_CONSEQ_CONV = DISJ_LIST_CONSEQ_CONV false

val (IMP_CONSEQ_CONV, IMP_ASSUM_CONSEQ_CONV, IMP_CONCL_CONSEQ_CONV,
     IMP_LIST_CONSEQ_CONV) =
    mk_binop_conseq_conv boolTheory.MONO_IMP
val IMP_LIST_CONSEQ_CONV = IMP_LIST_CONSEQ_CONV false

fun STRIP_FORALL_CONSEQ_CONV (cc: conseq_conv) t =
  if is_forall t then
    FORALL_CONSEQ_CONV (STRIP_FORALL_CONSEQ_CONV cc) t
  else
    cc t

fun STRIP_EXISTS_CONSEQ_CONV (cc: conseq_conv) t =
  if is_exists t then
    EXISTS_CONSEQ_CONV (STRIP_EXISTS_CONSEQ_CONV cc) t
  else
    cc t

fun print_cc t = (print_term t; print "\n\n"; REFL_CONSEQ_CONV t)
fun print_dcc direction t = (
  print_term t;
  print "\n\n";
  REFL_CONSEQ_CONV t
)

(*----------------------------------------------------------------------------*)
(* A conseq_conv that instantiate evars of the goal to match the conclusion
   of the rewriting theorem, using unification

   Written by Thomas Tuerk.
*)

(**************************************)
(* Some dummy definitions for testing *)
(**************************************)

(*
  val P_def = Define `P (x : num) (y : bool) = T`
  val Q_def = Define `Q (x : num) (y : num) = T`

  val dummy_imp = Q.prove (`
    !x y z (z' : num). Q x (z + y + z') ==> P (z + x) (y > x)`,
  REWRITE_TAC[P_def]);
*)


(**************************************)
(* Define new consequence conv        *)
(**************************************)

(*
  val rewr_thm = dummy_imp;
  val t = ``?(a:'a) x c y. P (5 + (x + 2)) ((c:num) > y)``

  MATCH_IMP_STRENGTHEN_CONSEQ_CONV rewr_thm t;
*)

(* Todo: be also able to unify types *)
fun MATCH_IMP_STRENGTHEN_CONSEQ_CONV (rewr_thm : thm) (t : term) : thm =
let
  (* destruct t *)
  val (t_ex_vars, t_body) = strip_exists t

  (* make sure variables are distinct, this is important for
     later unification *)
  val rewr_thm = CONV_RULE (VARIANT_CONV (t_ex_vars @ free_vars t)) rewr_thm

  (* destruct the rewr_thm *)
  val (quant_vars, rewr_concl, rewr_pre) = let
      val (vs, t0) = strip_forall (concl rewr_thm);
      val (t2, t1) = dest_imp_only t0
    in
      (vs, t1, t2)
    end;

  (* Try to unify *)
  val sub = Unify.simp_unify_terms [] rewr_concl t_body;

  (* figure out finally existentially quantified vars *)
  val new_ex_vars = let
    val t_vars' = List.map (Term.subst sub) (quant_vars @ t_ex_vars)
    val s0 = HOLset.listItems (FVL t_vars' empty_tmset)
    val s1 = Lib.filter (fn v => tmem v (quant_vars @ t_ex_vars)) s0
  in s1 end

  val thm0 = let
    val inst_l = List.map (Term.subst sub) quant_vars
    val thma = ISPECL inst_l rewr_thm
    val thmb = LIST_EXISTS_INTRO_IMP new_ex_vars thma
  in
    thmb
  end

  val thm1 = let
    val thm1a = ASSUME (Term.subst sub t_body)
    val (_, thm1b) = foldr (fn (v, (t, thm)) =>
       let val t' = mk_exists (v, t) in
       (t', EXISTS (Term.subst sub t', Term.subst sub v) thm) end)
        (t_body, thm1a) t_ex_vars
    val thm1c = foldr (fn (v, thm) =>
        SIMPLE_CHOOSE v thm) thm1b new_ex_vars
  in
    DISCH_ALL thm1c
  end
in
  IMP_TRANS thm0 thm1
end;

(*----------------------------------------------------------------------------*)
(* quantHeuristicsTools++ *)

fun LIST_IMP_FORALL_INTRO ([], thm) = thm
  | LIST_IMP_FORALL_INTRO (v::vs, thm) =
    IMP_FORALL_INTRO (v, LIST_IMP_FORALL_INTRO (vs, thm))

fun LIST_IMP_EXISTS_INTRO ([], thm) = thm
  | LIST_IMP_EXISTS_INTRO (v::vs, thm) =
    IMP_EXISTS_INTRO (v, LIST_IMP_EXISTS_INTRO (vs, thm))

(*----------------------------------------------------------------------------*)
(* Tactics to deal with goals of the form [?x1..xn. A1 /\ ... /\ Am], with a
   focus on A1, where most of the work is done.
 *)

type econj = {evars: term list,
              head_conj: term,
              rest: term list}

fun flat_strip_conj tm =
  let val l = spine_binop (total dest_conj) tm
      val _ = app (fn t => if is_conj t then fail() else ()) l
  in l end

fun dest_econj (tm: term): econj =
  let
    val (evars, conj) = strip_exists tm
    val conjs = flat_strip_conj conj
  in
    {evars = evars, head_conj = hd conjs, rest = tl conjs}
  end

fun mk_econj ({evars, head_conj, rest}: econj): term =
  let val rest_conj = list_mk_conj rest
      val conjs = mk_conj (head_conj, rest_conj)
      val t = list_mk_exists (evars, conjs)
  in t end

val is_econj = can dest_econj

val normalize_to_econj_conv =
  SIMP_CONV simpLib.empty_ss [PULL_EXISTS] THENC
  STRIP_BINDER_CONV (SOME existential)
    (fn tm => let val conjs = strip_conj tm
                  val tm' = list_mk_conj conjs
                  val thm = simpLib.SIMP_PROVE bool_ss [AC CONJ_ASSOC CONJ_COMM]
                                               (mk_eq (tm, tm'))
              in thm end)

val normalize_to_econj = CONV_TAC normalize_to_econj_conv

fun econj_head_conseq_conv (cc: conseq_conv) t =
  if is_econj t then
    STRIP_EXISTS_CONSEQ_CONV (CONJ1_CONSEQ_CONV cc) t
  else
    raise (ERR "is_econj" "econj_head_conseq_conv")


fun NTH_IMP_AND_CONG i n thm =
  let
    val _ = if i >= n orelse i < 0 then fail () else ()
    val thm_vars = free_vars (concl thm)
    fun newv name = variant thm_vars (mk_var (name, bool))
    val (pre, post) = dest_imp (concl thm)
    val acc = ref (
          if i = n - 1 then ([], thm) else
          let val y = newv "y"
              val thm' = SPECL [y, pre, post]
                               quantHeuristicsTheory.RIGHT_IMP_AND_INTRO
              val thm' = MP thm' thm
          in ([y], thm') end
        )
    val _ = for_se 0 (i - 1) (fn j =>
      let val (xs, thm) = !acc
          val (pre, post) = dest_imp (concl thm)
          val x = newv ("x" ^ Int.toString (i - 1 - j))
          val thm' = SPECL [x, pre, post]
                           quantHeuristicsTheory.LEFT_IMP_AND_INTRO
          val thm' = MP thm' thm
      in acc := (x :: xs, thm') end)
  in
    GENL (fst (!acc)) (snd (!acc))
  end

fun ECONJ_NTH_CONJ_CONG n thm t =
  let
    val econj = dest_econj t
    val (thm_vars, body) = strip_forall (concl thm)
    val thm_body = SPECL thm_vars thm
    val thm' = NTH_IMP_AND_CONG n (List.length (#rest econj) + 1) thm_body
    val thm' = GENL thm_vars thm'
  in
    thm'
  end

(*
  val A_def = Define `A (x: num) = T`

  val t' = ``?(a:'a) x c y. (P (5 + (x + 2)) ((c:num) > y)) /\ A y``
  val rewr_thm' = ECONJ_NTH_CONJ_CONG 0 dummy_imp t'

  MATCH_IMP_STRENGTHEN_CONSEQ_CONV rewr_thm' t';
*)

fun econj_nth_irule_conseq_conv n thm t =
  MATCH_IMP_STRENGTHEN_CONSEQ_CONV
    (ECONJ_NTH_CONJ_CONG n thm t)
    t

fun econj_nth_irule n thm =
  CONSEQ_CONV_TAC
    (STRENGTHEN_CONSEQ_CONV (econj_nth_irule_conseq_conv n thm))

val econj_head_irule_conseq_conv = econj_nth_irule_conseq_conv 0
val econj_head_irule = econj_nth_irule 0

end
