structure cfTacticsLib :> cfTacticsLib =
struct

open preamble
open ConseqConv match_goal
open set_sepTheory cfAppTheory cfHeapsTheory cfTheory cfTacticsTheory
open helperLib cfHeapsBaseLib cfHeapsLib cfTacticsBaseLib evarsConseqConvLib

fun constant_printer s _ _ _ (ppfns:term_pp_types.ppstream_funs) _ _ _ =
  let
    open Portable term_pp_types smpp
    val str = #add_string ppfns
  in str s end

val ellipsis_pp = constant_printer "(…)"

val printers = [
  ("extend_env_ellipsis", ``extend_env _ _ _``, ellipsis_pp),
  ("extend_env_rec_ellipsis", ``extend_env_rec _ _ _ _ _``, ellipsis_pp),
  ("extend_env_with_ellipsis", ``extend_env _ _ _ with v := _``, ellipsis_pp),
  ("extend_env_rec_with_ellipsis", ``extend_env_rec _ _ _ _ _ with v := _``,
   ellipsis_pp)
]

fun hide_environments b =
  if b then app add_user_printer printers
  else app (ignore o remove_user_printer) (map #1 printers)

val _ = hide_environments true

(*------------------------------------------------------------------*)

val cs = computeLib.the_compset
val () = listLib.list_rws cs
val () = basicComputeLib.add_basic_compset cs
val () = semanticsComputeLib.add_semantics_compset cs
val () = cfComputeLib.add_cf_aux_compset cs
val () = cfComputeLib.add_cf_normalize_compset cs

val eval = computeLib.CBV_CONV cs
val eval_tac = CONV_TAC eval
val eval_pat = compute_pat cs
fun eval_pat_tac pat = CONV_TAC (DEPTH_CONV (eval_pat pat))

local
  (* from bossLib.sml *)
  open simpLib

  fun stateful f ssfl thm =
    let
      val	ss = List.foldl	(simpLib.++ o Lib.swap)	(srw_ss()) ssfl
    in
      f ss thm
    end

  val let_arith_list = [boolSimps.LET_ss, numSimps.ARITH_ss]
in
  val simp_conv = stateful SIMP_CONV let_arith_list
  val simp_rule = stateful SIMP_RULE let_arith_list
end

(*------------------------------------------------------------------*)

fun head_unfold_conv thm =
  TRY_CONV hnf_conv THENC
  rewr_head_conv thm THENC
  TRY_CONV hnf_conv

fun head_unfold thm = CONV_TAC (head_unfold_conv thm)

val reducible_pats = [
  ``find_recfun _ _``,
  ``is_bound_Fun _ _``,
  ``dest_opapp _``,
  ``exp2v _ _``,
  ``exp2v_list _ _``,
  ``do_con_check _ _ _``,
  ``build_conv _ _ _``,
  ``lookup_var_id _ _``,
  ``Fun_body _``
]

val reduce_conv =
    DEPTH_CONV (
      List.foldl (fn (pat, conv) => (eval_pat pat) ORELSEC conv)
                 ALL_CONV reducible_pats
    ) THENC
    (simp_conv [])

val reduce_tac = CONV_TAC reduce_conv

(* [xpull] *)

(* xx have a proper cfSyntax? *)
fun cf_get_precondition t = rand (rator t)

(* xx *)
val cf_defs =
  [cf_lit_def, cf_con_def, cf_var_def, cf_let_def, cf_opn_def, cf_opb_def,
   cf_app_def, cf_fun_def, cf_fun_rec_def, cf_ref_def, cf_assign_def,
   cf_deref_def, cf_aalloc_def, cf_asub_def, cf_alength_def, cf_aupdate_def,
   cf_aw8alloc_def, cf_aw8sub_def, cf_aw8length_def, cf_aw8update_def,
   cf_log_def, cf_if_def, cf_match_def]

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

(* [xsimpl] *)

val sep_imp_instantiate_tac =
  TRY (
    CONSEQ_CONV_TAC
      (STRENGTHEN_CONSEQ_CONV
         (ecc_conseq_conv sep_imp_instantiate_ecc))
  ) \\
  simp [SEP_IMP_REFL, cfHeapsBaseTheory.hsimpl_gc]

val xsimpl =
  simp [PULL_EXISTS] \\
  CHANGED_TAC (rpt (hsimpl \\ sep_imp_instantiate_tac))
  ORELSE sep_imp_instantiate_tac

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
        eval_tac,
        eval_tac,
        simp [cf_def]
      ]
    fun Recclosure_tac _ =
      CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM letrec_pull_params_repack))) \\
      irule app_rec_of_cf THENL [
        eval_tac,
        reduce_tac \\ simp [cf_def] \\ reduce_tac \\
        CONV_TAC (
          DEPTH_CONV (
            REWR_CONV letrec_pull_params_repack THENC
            REWR_CONV (GSYM f_def)))
      ]
  in
    rpt strip_tac \\ simp [f_def] \\
    first_match_tac [
      ([mg.c `app _ (Closure _ _ _) _ _ _`], Closure_tac),
      ([mg.c `app _ (Recclosure _ _ _) _ _ _`], Recclosure_tac)
    ] \\ simp []
  end

(* [xlet] *)

fun xlet_core cont0 cont1 cont2 =
  xpull_check_not_needed \\
  head_unfold cf_let_def \\
  irule local_elim \\ hnf \\
  simp [libTheory.opt_bind_def] \\
  cont0 \\
  CONJ_TAC THENL [all_tac, cont1 \\ cont2]

(* temporary basic wrapper until evars *)
fun xlet Q = let
  val name = (fst o dest_var o fst o dest_abs o Term) Q
  val qname = [QUOTE name]
in
  xlet_core
    (qexists_tac Q)
    (qx_gen_tac qname \\ cbv)
    (TRY xpull)
end

(* [xfun] *)

val reduce_spec_conv =
  STRIP_QUANT_CONV (LAND_CONV eval) THENC
  simp_conv [LENGTH_EQ_NUM_compute, PULL_EXISTS]

val reduce_curried_conv = RATOR_CONV (RAND_CONV eval)

val fun_reduce_conv =
  QUANT_CONV (
    LAND_CONV (
      LAND_CONV reduce_curried_conv THENC
      RAND_CONV reduce_spec_conv
    )
  )

fun fun_rec_aux_unfold_conv tm = let
  val base_case = fst (CONJ_PAIR fun_rec_aux_def)
  val ind_case = fst (CONJ_PAIR (snd (CONJ_PAIR fun_rec_aux_def)))
  val base_conv = REWR_CONV base_case
  val ind_conv =
    REWR_CONV ind_case THENC
    LAND_CONV (
      LAND_CONV reduce_curried_conv THENC
      RAND_CONV reduce_spec_conv
    ) THENC
    RAND_CONV (
      fun_rec_aux_unfold_conv
    )
in (base_conv ORELSEC ind_conv) tm end

val fun_rec_reduce_conv = let
  val reduce_length =
      eval THENC
      simp_conv [LENGTH_EQ_NUM_compute, PULL_EXISTS]
in
  simp_conv [] THENC
  QUANT_CONV (
    LAND_CONV reduce_length THENC
    RAND_CONV (
      LAND_CONV eval THENC
      RAND_CONV (
        DEPTH_CONV (eval_pat ``letrec_pull_params _``)
      )
    )
  ) THENC
  simp_conv [PULL_EXISTS] THENC
  QUANT_CONV fun_rec_aux_unfold_conv
end

val xfun_norec_core =
  head_unfold cf_fun_def \\
  irule local_elim \\ hnf \\
  CONV_TAC fun_reduce_conv

val xfun_rec_core =
  head_unfold cf_fun_rec_def \\
  irule local_elim \\ hnf \\
  CONV_TAC fun_rec_reduce_conv

val xfun_core =
  xpull_check_not_needed \\
  first_match_tac [
    ([mg.c `cf_fun _ _ _ _ _ _ _ _`], K xfun_norec_core),
    ([mg.c `cf_fun_rec _ _ _ _ _ _`], K xfun_rec_core)
  ]

val simp_spec = (CONV_RULE reduce_conv) o (simp_rule [cf_def])

fun xfun qname =
  xfun_core \\
  qx_gen_tac qname \\
  disch_then (fn th => assume_tac (simp_spec th))

fun xfun_spec qname qspec =
  xfun_core \\
  qx_gen_tac qname \\
  disch_then (fn th =>
    let val (curried_th, spec_th) = CONJ_PAIR th
        val spec_th = simp_spec spec_th
    in assume_tac curried_th \\
       Tactical.REVERSE (qsuff_tac qspec) THENL [
         assume_tac spec_th,
         strip_tac
       ]
    end
  ) ORELSE FAIL_TAC "invalid spec"

(* [xapply] *)

fun xapply_core H cont1 cont2 =
(*  try_progress_then (fn K =>
    (* temp basic stuff until evars *)
    irule local_frame_gc THENL [xlocal, assume_tac K])
    H *) (* todo fixme *)
  irule local_frame_gc THENL [
    xlocal,
    CONSEQ_CONV_TAC (K (
      ecc_conseq_conv (
        conj1_ecc (irule_ecc H)
      )
    )) \\
    CONV_TAC (DEPTH_CONV (REWR_CONV ConseqConvTheory.AND_CLAUSES_TX))
  ]

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

val unfold_cf_app =
  head_unfold cf_app_def \\
  irule local_elim \\ hnf \\
  reduce_tac

val xapp_prepare_goal =
  xpull_check_not_needed \\
  first_match_tac [
    ([mg.c `cf_app _ _ _ _ _ _`], K unfold_cf_app),
    ([mg.c `app _ _ _ _ _`], K all_tac)
  ]

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

val xlit_core =
  head_unfold cf_lit_def \\ cbv

val xcon_core =
  head_unfold cf_con_def \\ reduce_tac

val xvar_core =
  head_unfold cf_var_def \\ reduce_tac

fun xret_pre cont1 cont2 =
  xpull_check_not_needed \\
  first_match_tac [
    ([mg.c `cf_lit _ _ _ _`], K xlit_core),
    ([mg.c `cf_con _ _ _ _ _`], K xcon_core),
    ([mg.c `cf_var _ _ _ _`], K xvar_core)
  ] \\
  cont1
  (* todo: also do stuff with lets *)

val xret = xret_pre xret_irule_lemma (TRY xpull)
val xlit = xret
val xcon = xret
val xvar = xret

(* todo: xrets *)

(* [xlog] *)

val xlog_base =
  xpull_check_not_needed \\
  head_unfold cf_log_def \\
  irule local_elim \\ hnf \\
  reduce_tac \\
  TRY (asm_exists_tac \\ simp [])

val xlog = xlog_base

(* [xif] *)

val xif_base =
  xpull_check_not_needed \\
  head_unfold cf_if_def \\
  irule local_elim \\ hnf \\
  reduce_tac \\
  TRY (asm_exists_tac \\ simp [] \\ conj_tac \\ DISCH_TAC)

val xif = xif_base

(* [xmatch] *)

fun clean_cases_conv tm = let
  val cond_conv =
      HO_REWR_CONV exists_v_of_pat_norest_length THENC
      STRIP_QUANT_CONV (LAND_CONV (RHS_CONV eval)) THENC
      simp_conv [LENGTH_EQ_NUM_compute, PULL_EXISTS] THENC
      STRIP_QUANT_CONV
        (LHS_CONV eval THENC simp_conv [option_CLAUSES])
  val then_conv =
      HO_REWR_CONV forall_v_of_pat_norest_length THENC
      STRIP_QUANT_CONV (LAND_CONV (RHS_CONV eval)) THENC
      simp_conv [LENGTH_EQ_NUM_compute, PULL_EXISTS] THENC
      STRIP_QUANT_CONV
        (LAND_CONV (LHS_CONV eval) THENC
         simp_conv [option_CLAUSES])
  val else_conv =
      TRY_CONV (LAND_CONV clean_cases_conv ORELSEC
                simp_conv [cf_bottom_def])
in
  (RATOR_CONV (RATOR_CONV (RAND_CONV cond_conv)) THENC
   RATOR_CONV (RAND_CONV then_conv) THENC
   RAND_CONV else_conv) tm
end

val unfold_build_cases =
  simp [build_cases_def] \\
  CONV_TAC (LAND_CONV clean_cases_conv) \\
  simp []

fun validate_pat_conv tm = let
  val conv =
      REWR_CONV validate_pat_def THENC
      RAND_CONV eval THENC
      LAND_CONV (REWR_CONV pat_typechecks_def) THENC
      eval
  val conv' = (QUANT_CONV conv) THENC simp_conv []
  val th = conv' tm
in if (rhs o concl) th = boolSyntax.T then th else fail () end

val validate_pat_all_conv =
  REPEATC (
    RAND_CONV validate_pat_conv THENC RW.RW_CONV [boolTheory.AND_CLAUSES]
  )

val xmatch_base =
  xpull_check_not_needed \\
  head_unfold cf_match_def \\ irule local_elim \\ hnf \\
  reduce_tac \\
  unfold_build_cases \\
  CONV_TAC validate_pat_all_conv

val xmatch = xmatch_base

end
