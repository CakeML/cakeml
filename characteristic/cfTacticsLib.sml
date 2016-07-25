structure cfTacticsLib :> cfTacticsLib =
struct

open HolKernel Parse boolLib bossLib preamble
open set_sepTheory helperLib ConseqConv ml_translatorTheory
open cfHeapsTheory cfHeapsBaseLib cfStoreTheory cfNormalizeTheory cfAppTheory
open cfHeapsLib cfTheory cfTacticsBaseLib cfTacticsTheory
open match_goal

(* todo: add a ref allowing the custom printer to be disabled *)
fun constant_printer s _ _ _ (ppfns:term_pp_types.ppstream_funs) _ _ _ =
  let
    open Portable term_pp_types smpp
    val str = #add_string ppfns
  in str s end

val _ = add_user_printer ("extend_env_ellipsis", ``extend_env _ _ _``,
                          constant_printer "(…)")

val _ = add_user_printer ("extend_env_rec_ellipsis",
                          ``extend_env_rec _ _ _ _ _``,
                          constant_printer "(…)")

val _ = add_user_printer ("extend_env_with_ellipsis",
                          ``extend_env _ _ _ with v := _``,
                          constant_printer "(…)")

val _ = add_user_printer ("extend_env_rec_with_ellipsis",
                          ``extend_env_rec _ _ _ _ _ with v := _``,
                          constant_printer "(…)")

(*------------------------------------------------------------------*)

fun head_unfold thm = hnf \\ conv_head thm \\ hnf

val reducible_pats = [
  `find_recfun _ _`,
  `is_bound_Fun _ _`,
  `dest_opapp _`,
  `exp2v _ _`,
  `exp2v_list _ _`,
  `do_con_check _ _ _`,
  `build_conv _ _ _`,
  `lookup_var_id _ _`
]

val reduce_tac =
  List.foldl (fn (pat, tac) => TRY (qeval_pat_tac pat) \\ tac)
    ALL_TAC reducible_pats \\
  fs []

fun fetch_v name st =
  let val env = ml_progLib.get_env st
      val name = stringLib.fromMLstring name
      val evalth = EVAL ``lookup_var_id (Short ^name) ^env``
  in (optionLib.dest_some o rhs o concl) evalth end

fun fetch_def name st =
  let val v = fetch_v name st
      val v_defs = ml_progLib.get_v_defs st
      val opt_thm = List.find (fn thm => (lhs o concl) thm = v) v_defs
  in valOf opt_thm end

(* [xpull] *)

(* xx have a proper cfSyntax? *)
fun cf_get_precondition t = rand (rator t)

(* xx *)
val cf_defs =
  [cf_lit_def, cf_con_def, cf_var_def, cf_let_def, cf_opn_def, cf_opb_def,
   cf_app_def, cf_fundecl_def, cf_fundecl_rec_def, cf_ref_def, cf_assign_def,
   cf_deref_def, cf_aalloc_def, cf_asub_def, cf_alength_def, cf_aupdate_def,
   cf_aw8alloc_def, cf_aw8sub_def, cf_aw8length_def, cf_aw8update_def,
   cf_mat_def]

val xlocal =
  FIRST [
    first_assum MATCH_ACCEPT_TAC,
    (HO_MATCH_MP_TAC app_local \\ fs [] \\ NO_TAC),
    (fs (local_is_local :: cf_defs) \\ NO_TAC)
  ] (* todo: is_local_pred *)

fun xpull_check_not_needed (g as (_, w)) =
  let val H = cf_get_precondition w
  in hpullable_rec H; ALL_TAC g end

fun xpull_core (g as (_, w)) =
  if is_sep_imp w orelse is_sep_imppost w then
    hpull g
  else
    hclean g

val xpull =
  xpull_core \\ rpt strip_tac THEN1 (TRY xlocal)

(* [xcf] *)

fun naryFun_repack_conv tm =
  let
    val (base_case, rec_case) = CONJ_PAIR (GSYM naryFun_def)
    val Fun_pat = ``Fun _ _``
    val conv =
        if can (match_term Fun_pat) tm then
          (RAND_CONV naryFun_repack_conv) THENC
          (REWR_CONV rec_case)
        else
          REWR_CONV base_case
  in conv tm
  end

val naryClosure_repack_conv =
  (RAND_CONV naryFun_repack_conv) THENC (REWR_CONV (GSYM naryClosure_def))

fun xcf name st =
  let
    val f_def = fetch_def name st
    fun Closure_tac _ =
      CONV_TAC (DEPTH_CONV naryClosure_repack_conv) \\
      irule app_of_cf THENL [
        EVAL_TAC,
        EVAL_TAC,
        fs [cf_def]
      ]
    fun Recclosure_tac _ =
      CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM letrec_pull_params_repack))) \\
      irule app_rec_of_cf THENL [
        EVAL_TAC,
        reduce_tac \\ fs [cf_def] \\ reduce_tac
      ]
  in
    rpt gen_tac \\ fs [f_def] \\
    first_match_tac [
      ([mg.c `app _ (Closure _ _ _) _ _ _`], Closure_tac),
      ([mg.c `app _ (Recclosure _ _ _) _ _ _`], Recclosure_tac)
    ]
  end

(* [xlet] *)

fun xlet_core cont0 cont1 cont2 =
  xpull_check_not_needed \\
  head_unfold cf_let_def \\
  irule local_elim \\ hnf \\
  fs [libTheory.opt_bind_def] \\
  cont0 \\
  CONJ_TAC THENL [all_tac, cont1 \\ cont2]

(* temporary basic wrapper until evars *)
fun xlet Q x =
  xlet_core
    (qexists_tac Q)
    (qx_gen_tac x \\ cbv)
    (TRY xpull)

(* [xapply] *)

fun xapply_core H cont1 cont2 =
(*  try_progress_then (fn K =>
    (* temp basic stuff until evars *)
    irule local_frame_gc THENL [xlocal, assume_tac K])
    H *) (* todo fixme *)
  irule local_frame_gc THENL [xlocal, assume_tac H]

fun xapply H =
  xpull_check_not_needed \\
  xapply_core H all_tac all_tac

(* [xspec] *)

fun concl_tm tm =
  let 
    val thm' = Drule.IRULE_CANON (ASSUME tm)
    val (_, body) = strip_forall (concl thm')
  in
    if is_imp body then
      (snd o dest_imp) body
    else
      body
  end

fun app_f_tm tm =
  let val (_, f_tm, _, _, _) = cfAppSyntax.dest_app tm
  in f_tm end

fun is_spec_for f tm =
  (concl_tm tm |> app_f_tm) = f
  handle HOL_ERR _ => false

fun xspec_in_asl f asl =
  List.find (is_spec_for f) asl

fun xspec_in_db f =
  case DB.matchp (fn thm => is_spec_for f (concl thm)) [] of
      data :: _ => SOME data
    | _ => NONE

(* todo: variants *)
fun xspec f (ttac: thm_tactic) (g as (asl, _)) =
  case xspec_in_asl f asl of
      SOME a => 
      (print "Using a specification from the assumptions\n";
       ttac (ASSUME a) g)
    | NONE =>
      case xspec_in_db f of
          SOME ((thy, name), (thm, _)) =>
          (print ("Using specification " ^ name ^
                  " from theory " ^ thy ^ "\n");
           ttac thm g)
        | NONE =>
          raise ERR "xspec" ("Could not find a specification for " ^
                             fst (dest_const f))

(* [xapp] *)

val xapp_prepare_goal =
  xpull_check_not_needed \\
  head_unfold cf_app_def \\
  irule local_elim \\ hnf \\
  reduce_tac

fun app_f_tac tmtac (g as (_, w)) =
  tmtac (app_f_tm w) g

fun xapp_common spec do_xapp =
  xapp_prepare_goal \\
  app_f_tac (fn f =>
    case spec of
        SOME thm => do_xapp thm
      | NONE => xspec f do_xapp)

fun xapp_xapply_no_simpl K =
  FIRST [irule K, xapply_core K all_tac all_tac]

fun xapp_core spec =
  xapp_common spec xapp_xapply_no_simpl

val xapp = xapp_core NONE
fun xapp_spec spec = xapp_core (SOME spec)

(* [xret] *)

val xret_irule_lemma =
  FIRST [irule xret_lemma_unify,
         irule xret_lemma]

val xret_no_gc_core =
    FIRST [irule xret_lemma_unify,
           (* todo evars *) irule xret_no_gc_lemma]

val xlit =
  head_unfold cf_lit_def \\ cbv

val xcon =
  head_unfold cf_con_def \\ reduce_tac

val xvar =
  head_unfold cf_var_def \\ reduce_tac

fun xret_pre cont1 cont2 =
  xpull_check_not_needed \\
  first_match_tac [
    ([mg.c `cf_lit _ _ _ _`], K xlit),
    ([mg.c `cf_con _ _ _ _ _`], K xcon),
    ([mg.c `cf_var _ _ _ _`], K xvar)
  ] \\
  cont1
  (* todo: also do stuff with lets *)

val xret = xret_pre xret_irule_lemma (TRY xpull)

(* todo: xrets *)


end
