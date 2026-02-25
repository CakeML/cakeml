(*
  Various tactics for reasoning about CF-based goals in HOL.
*)
structure cfTacticsLib (*:> cfTacticsLib*) =
struct

open preamble
open ConseqConv
open set_sepTheory cfAppTheory cfHeapsTheory cfTheory cfTacticsTheory
open helperLib cfHeapsBaseLib cfHeapsLib cfTacticsBaseLib evarsConseqConvLib
open cfAppLib cfSyntax semanticPrimitivesSyntax
open xcf;

val ERR = mk_HOL_ERR "cfTacticsLib";

local
  fun constant_printer s _ _ _ (ppfns:term_pp_types.ppstream_funs) _ _ _ = let
    open Portable term_pp_types smpp
    val str = #add_string ppfns
  in str s end
  val ellipsis_pp = constant_printer "(…)"
  val printers = [
    ("extend_env_ellipsis", ``extend_env _ _ _``, ellipsis_pp),
    ("extend_env_rec_ellipsis", ``extend_env_rec _ _ _ _ _``, ellipsis_pp),
    ("extend_env_with_ellipsis", ``extend_env _ _ _ with v := _``, ellipsis_pp),
    ("extend_env_rec_with_ellipsis",
     ``extend_env_rec _ _ _ _ _ with v := _``, ellipsis_pp)
  ]
in
fun hide_environments b =
  if b then app temp_add_user_printer printers
  else app (ignore o temp_remove_user_printer) (map #1 printers)
end

(*------------------------------------------------------------------*)

val cs = !(computeLib.the_compset)
  |> listLib.list_rws
  |> basicComputeLib.add_basic_compset
  |> semanticsComputeLib.add_semantics_compset
  |> ml_progComputeLib.add_env_compset
  |> cfComputeLib.add_cf_aux_compset
  |> computeLib.extend_compset [
       computeLib.Defs [
       (*  TS: it's quite unclear to me why CF does this, when ml_progScript is so
           careful to ensure that these definitions aren't in the compset. I've tried
           adjusting it, but it results in far too much work. *)
         ml_progTheory.merge_env_def,
         ml_progTheory.write_def,
         ml_progTheory.write_mod_def,
         ml_progTheory.write_cons_def,
         ml_progTheory.empty_env_def
         (*semanticPrimitivesTheory.merge_alist_mod_env_def*)
       ]
     ]

val _ = (max_print_depth := 15)

val eval = computeLib.CBV_CONV cs THENC EVAL (* TODO: remove EVAL *)
val eval_tac = CONV_TAC eval
fun eval_pat t = (compute_pat cs t) THENC EVAL (* TODO: same *)
fun eval_pat_tac pat = CONV_TAC (DEPTH_CONV (eval_pat pat))

local
  (* from bossLib.sml *)
  open simpLib

  fun stateful f ssfl thm =
    let
      val       ss = List.foldl (simpLib.++ o Lib.swap) (srw_ss()) ssfl
    in
      f ss thm
    end

  val let_arith_list = [boolSimps.LET_ss, numSimps.ARITH_ss]
in
  val simp_conv = stateful SIMP_CONV let_arith_list
  val simp_rule = stateful SIMP_RULE let_arith_list
end

(*------------------------------------------------------------------*)

fun process_topdecs q = cfNormaliseLib.normalise_prog (parse_topdecs q)

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
  ``nsLookup _ _``,
  ``nsLookup_Short _ _``,
  ``nsLookup_Mod1 _ _``,
  ``Fun_body _``
]

val reduce_conv =
    (DEPTH_CONV (
      List.foldl (fn (pat, conv) => (eval_pat pat) ORELSEC conv)
                 ALL_CONV reducible_pats))
    (* It seems that the next line makes npbc_arrayProg around 29s faster; it would
       be good to confirm this, though. Maybe doing basic simplifications first
       results in a smaller term, meaning less work is done in the following
       SIMP_CONV? *)
    THENC (STRIP_QUANT_CONV (SIMP_CONV pure_ss []))
    (* We probably do not use all of srw_ss, so there may be potential for a
       smaller simpset. Some of the things we use, though:
       - simpLib.type_ssfrag for at least ast$op
       - pair_CASE_def *)
    THENC (SIMP_CONV (srw_ss()) [])

val reduce_tac = CONV_TAC reduce_conv

fun err_tac orig msg : tactic =
  fn _ => raise ERR orig msg

(* [xpull] *)

(* xx have a proper cfSyntax? *)
fun cf_get_precondition t = rand (rator t)

(* xx *)
val cf_defs =
  [cf_lit_def, cf_con_def, cf_var_def, cf_let_def, cf_arith_def,
   cf_int_cmp_def,
   cf_app_def, cf_fun_def, cf_fun_rec_def, cf_ref_def, cf_assign_def,
   cf_deref_def, cf_aalloc_def, cf_asub_def, cf_alength_def, cf_aupdate_def,
   cf_aw8alloc_def, cf_aw8sub_def, cf_aw8length_def, cf_aw8update_def,
   cf_copyaw8aw8_def, cf_log_def, cf_if_def, cf_match_def, cf_ffi_def,
   cf_raise_def, cf_handle_def]

val cleanup_exn_side_cond =
  simp [cfHeapsBaseTheory.SEP_IMPPOSTv_POSTe_left,
        cfHeapsBaseTheory.SEP_IMPPOSTv_POSTf_left,
        cfHeapsBaseTheory.SEP_IMPPOSTv_POSTd_left,
        cfHeapsBaseTheory.SEP_IMPPOSTv_POSTed_left,
        cfHeapsBaseTheory.SEP_IMPPOSTe_POSTv_left,
        cfHeapsBaseTheory.SEP_IMPPOSTe_POSTf_left,
        cfHeapsBaseTheory.SEP_IMPPOSTe_POSTd_left,
        cfHeapsBaseTheory.SEP_IMPPOSTe_POSTvd_left,
        cfHeapsBaseTheory.SEP_IMPPOSTf_POSTv_left,
        cfHeapsBaseTheory.SEP_IMPPOSTf_POSTe_left,
        cfHeapsBaseTheory.SEP_IMPPOSTf_POSTd_left,
        cfHeapsBaseTheory.SEP_IMPPOSTf_POSTve_left,
        cfHeapsBaseTheory.SEP_IMPPOSTf_POSTvd_left,
        cfHeapsBaseTheory.SEP_IMPPOSTf_POSTed_left,
        cfHeapsBaseTheory.SEP_IMPPOSTd_POSTv_left,
        cfHeapsBaseTheory.SEP_IMPPOSTd_POSTe_left,
        cfHeapsBaseTheory.SEP_IMPPOSTd_POSTf_left,
        cfHeapsBaseTheory.SEP_IMPPOSTd_POSTve_left,
        cfHeapsBaseTheory.SEP_IMPPOSTv_inv_POSTv_left,
        cfHeapsBaseTheory.SEP_IMPPOSTe_inv_POSTe_left
       ]

val xlocal =
  FIRST [
    first_assum MATCH_ACCEPT_TAC,
    (HO_MATCH_MP_TAC app_local \\ fs [] \\ NO_TAC),
    (HO_MATCH_ACCEPT_TAC cf_cases_local \\ NO_TAC),
    (asm_rewrite_tac (cf_defs) \\
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) \\
     rewrite_tac [local_is_local])
    (* Note the lack of NO_TAC in the final attempt -
       unsolved goals will be returned *)
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
  xpull_core \\ rpt strip_tac THEN_LT (NTH_GOAL xlocal 1)

(* [xsimpl] *)

val sep_imp_instantiate_tac =
  TRY hinst \\
  simp [SEP_IMP_REFL, cfHeapsBaseTheory.hsimpl_gc]

val xsimpl =
  simp [PULL_EXISTS,BOOL_T,BOOL_F] \\
  CHANGED_TAC (rpt (hsimpl \\ sep_imp_instantiate_tac))
  ORELSE sep_imp_instantiate_tac

(* [xcf], [xcfs] *)

(* Implemented in xcf.sml *)

(* [xlet] *)

fun xlet_core Q qname =
  xpull_check_not_needed \\
  head_unfold cf_let_def \\
  irule local_elim \\ hnf \\
  rewrite_tac [namespaceTheory.nsOptBind_def] \\
  qexists_tac Q \\
  rpt CONJ_TAC THENL [
    all_tac,
    TRY (MATCH_ACCEPT_TAC cfHeapsBaseTheory.SEP_IMPPOSTv_inv_POSTv_left),
    qx_gen_tac qname \\ simp_tac (srw_ss()) [] \\ TRY xpull
  ]

val res_CASE_tm =
  CONJ_PAIR cfHeapsBaseTheory.res_case_def
  |> fst |> SPEC_ALL |> concl
  |> lhs |> strip_comb |> fst

val POSTv_tm =
  cfHeapsBaseTheory.POSTv_def |> SPEC_ALL |> concl
  |> lhs |> strip_comb |> fst

val POST_tm =
  cfHeapsBaseTheory.POST_def |> SPEC_ALL |> concl
  |> lhs |> strip_comb |> fst

fun vname_of_post fallback Qtm = let
  val vname_lam = fst o dest_var o fst o dest_abs
  fun vname_res_CASE_lam tm = let
      val body = dest_abs tm |> snd
    in
      if body ~~ res_CASE_tm then
        List.nth (strip_comb body |> snd, 1)
        |> vname_lam
      else fail ()
    end
  fun vname_POSTv tm = let
      val (base, args) = strip_comb tm
    in if base ~~ POSTv_tm then vname_lam (List.hd args)
       else fail()
    end
  fun vname_POST tm = let
      val (base, args) = strip_comb tm
    in if base ~~ POST_tm then vname_lam (List.hd args)
       else fail()
    end
in
  vname_POSTv Qtm handle HOL_ERR _ =>
  vname_POST Qtm handle HOL_ERR _ =>
  vname_res_CASE_lam Qtm handle HOL_ERR _ =>
  fallback
end

(* temporary basic wrapper until evars *)
fun xlet Q (g as (asl, w)) = let
  val ctx = free_varsl (w :: asl)
  val name = vname_of_post "v" (Term Q)
  val name' = prim_variant ctx (mk_var (name, v_ty)) |> dest_var |> fst
in
  xlet_core Q [QUOTE name'] g
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

fun xfun_core (g as (_, w)) =
  if is_cf_fun w then
    xfun_norec_core g
  else if is_cf_fun_rec w then
    xfun_rec_core g
  else
    err_tac "xfun" "goal is not a cf_fun or cf_fun_rec" g

val simp_spec = CONV_RULE (REPEATC (reduce_conv THENC PURE_ONCE_REWRITE_CONV[cf_def]))

fun xfun qname =
  xpull_check_not_needed \\
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
  irule local_frame_gc THEN
    CONJ_TAC THEN1 xlocal THEN
    CONSEQ_CONV_TAC (K (
      ecc_conseq_conv (
        conj1_ecc (irule_ecc H)
      )
    )) \\
    CONV_TAC (DEPTH_CONV (REWR_CONV ConseqConvTheory.AND_CLAUSES_TX))

fun xapply H =
  xpull_check_not_needed \\
  xapply_core H all_tac all_tac
  ORELSE err_tac "xapply" "Failed to apply the given theorem"

(* [xspec] *)

datatype spec_kind =
    CF_spec
  | Translator_spec

fun spec_kind_toString CF_spec = "CF"
  | spec_kind_toString Translator_spec = "translator"

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

fun goal_app_infos tm : hol_type * term =
  let val (p, f_tm, _, _, _) = cfAppSyntax.dest_app tm
      val ffi_ty = cfHeapsBaseSyntax.dest_ffi_proj (type_of p)
  in (ffi_ty, f_tm) end

fun is_cf_spec_for f tm =
  (concl_tm tm |> goal_app_infos |> snd) ~~ f
  handle HOL_ERR _ => false

fun is_arrow_spec_for f tm =
  let val tm = tm |> strip_imp |> #2 in
    ml_translatorSyntax.is_Arrow (tm |> rator |> rator) andalso
    (rand tm) ~~ f
  end handle HOL_ERR _ => false

fun spec_kind_for f tm : spec_kind option =
  if is_cf_spec_for f tm then SOME CF_spec
  else if is_arrow_spec_for f tm then SOME Translator_spec
  else NONE

fun is_spec_for f tm : bool =
  spec_kind_for f tm <> NONE

fun xspec_in_asl f asl : (spec_kind * term) option =
  find_map (fn tm =>
    case spec_kind_for f tm of
        SOME k => SOME (k, tm)
      | NONE => NONE)
  asl

fun xspec_in_db f : (string * string * spec_kind * thm) option =
  case DB.matchp (fn thm => can (find_term (same_const f)) (concl thm) andalso is_spec_for f (concl thm)) [] of
      ((thy, name), (thm, _, _)) :: _ =>
      (case spec_kind_for f (concl thm) of
           SOME k => SOME (thy, name, k, thm)
         | NONE => fail())
    | _ => NONE

fun cf_spec (ffi_ty : hol_type) (kind : spec_kind) (spec : thm) : thm =
  case kind of
      CF_spec => spec
    | Translator_spec => app_of_Arrow_rule ffi_ty spec

(* todo: variants *)
fun xspec ffi_ty f (ttac: thm_tactic) (g as (asl, w)) =
  case xspec_in_asl f asl of
      SOME (k, a) =>
      (print
         ("Using a " ^ (spec_kind_toString k) ^
          " specification from the assumptions\n");
       ttac (cf_spec ffi_ty k (ASSUME a)) g)
    | NONE =>
      case xspec_in_db f of
          SOME (thy, name, k, thm) =>
          (print ("Using " ^ (spec_kind_toString k) ^
                  " specification " ^ name ^
                  " from theory " ^ thy ^ "\n");
           ttac (cf_spec ffi_ty k thm) g)
        | NONE =>
          raise ERR "xspec" ("Could not find a specification for " ^
                             fst (dest_const f))

(* [xapp] *)

val unfolded_app_reduce_conv =
let
  fun fail_if_F_conv msg tm =
    if Feq tm then raise ERR "xapp" msg
    else ALL_CONV tm

  val fname_lookup_reduce_conv =
    reduce_conv THENC
    (fail_if_F_conv "Unbound function")

  val args_lookup_reduce_conv =
    reduce_conv THENC
    (fail_if_F_conv "Unbound argument(s)")
in
  STRIP_QUANT_CONV (
    FORK_CONV (
      fname_lookup_reduce_conv,
      (LAND_CONV args_lookup_reduce_conv)
    )
  )
end

val unfold_cf_app =
  head_unfold cf_app_def \\
  irule local_elim \\ hnf \\
  CONV_TAC unfolded_app_reduce_conv \\
  reduce_tac

val xapp_prepare_goal =
  xpull_check_not_needed \\
  (fn (g as (_, w)) =>
    if is_cf_app w then unfold_cf_app g
    else if cfAppSyntax.is_app w then all_tac g
    else err_tac "xapp"
      "Goal is not of the right form (must be a cf_app or app)" g)

(* This tactical assumes the goal is of the form [app _ _ _ _ _].
   This is the case after calling [xapp_prepare_goal] (if it doesn't fail).
*)
fun app_f_tac tmtac (g as (_, w)) = tmtac (goal_app_infos w) g

fun xapp_common spec do_xapp =
  xapp_prepare_goal \\
  app_f_tac (fn (ffi_ty, f) =>
    case spec of
        SOME thm =>
        (case spec_kind_for f (concl thm) of
             SOME k => do_xapp (cf_spec ffi_ty k thm)
           | NONE => failwith "Invalid specification")
      | NONE => xspec ffi_ty f do_xapp)

fun xapp_xapply_no_simpl K =
  FIRST [irule K, xapply_core K all_tac all_tac] ORELSE
  err_tac "xapp" "Could not apply specification"

fun xapp_core spec =
  xapp_common spec xapp_xapply_no_simpl

val xapp = xapp_core NONE
fun xapp_spec spec = xapp_core (SOME spec)

(* [xret] *)

val xret_irule_lemma =
  FIRST [(* irule xret_lemma_unify,*)
         HO_MATCH_MP_TAC xret_lemma \\ conj_tac,
         HO_MATCH_MP_TAC xret_lemma1]

val xret_no_gc_core =
    FIRST [(*irule xret_lemma_unify,*)
           (* todo evars *) HO_MATCH_MP_TAC xret_no_gc_lemma \\ conj_tac]

val xlit_core =
  head_unfold cf_lit_def \\ cbv

val xcon_core =
  head_unfold cf_con_def \\ reduce_tac

val xvar_core =
  head_unfold cf_var_def \\ reduce_tac

fun xret_pre cont1 cont2 (g as (_, w)) =
  (xpull_check_not_needed \\
   (if is_cf_lit w then xlit_core
    else if is_cf_con w then xcon_core
    else if is_cf_var w then xvar_core
    else fail ()) \\
   cont1 \\
   cleanup_exn_side_cond
   ) g
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
  cleanup_exn_side_cond \\
  TRY (asm_exists_tac \\ simp [])

val xlog = xlog_base

(* [xif] *)

val xif_base =
  xpull_check_not_needed \\
  head_unfold cf_if_def \\
  irule local_elim \\ hnf \\
  reduce_tac \\
  TRY (asm_exists_tac
       \\ full_simp_tac std_ss []
       \\ conj_tac \\ DISCH_TAC)

val xif = xif_base

(* [xcases] *)

fun clean_cases_conv tm = let
  val cond_conv =
      HO_REWR_CONV exists_v_of_pat_norest_length THENC
      STRIP_QUANT_CONV (LAND_CONV (RHS_CONV eval)) THENC
      STRIP_QUANT_CONV (RAND_CONV (LAND_CONV (RHS_CONV eval))) THENC
      simp_conv [LENGTH_EQ_NUM_compute, PULL_EXISTS] THENC
      STRIP_QUANT_CONV
        (LHS_CONV eval THENC simp_conv [option_CLAUSES])
  val then_conv =
      HO_REWR_CONV forall_v_of_pat_norest_length THENC
      STRIP_QUANT_CONV (LAND_CONV (RHS_CONV eval)) THENC
      STRIP_QUANT_CONV (RAND_CONV (LAND_CONV (RHS_CONV eval))) THENC
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

val unfold_cases =
  (* using the "once" variant does not work *)
  pure_rewrite_tac [cf_cases_def] \\
  CONSEQ_HO_REWRITE_TAC ([local_elim], [], []) \\
  CONV_TAC (LAND_CONV clean_cases_conv) \\
  (* srw_ss() can potentially be weakened much more; bool_ss fails because
     it does not simplify something like
       Conv (SOME (TypeStamp "Some" 2)) [Conv NONE [v1_1; v1_2]] =
          Conv (SOME (TypeStamp "None" 2)) []
     to F *)
  asm_simp_tac (srw_ss()) []

fun validate_pat_conv tm = let
  val conv =
      REWR_CONV validate_pat_def THENC
      RAND_CONV eval THENC
      LAND_CONV (REWR_CONV pat_typechecks_def) THENC
      eval
  val conv' = (QUANT_CONV conv) THENC simp_conv []
  val th = conv' tm
in if Teq (rhs (concl th)) then th else fail () end

val validate_pat_all_conv =
  REPEATC (
    RAND_CONV validate_pat_conv THENC PURE_REWRITE_CONV [boolTheory.AND_CLAUSES]
  )

local
  val can_pmatch_all_tm =
    semanticPrimitivesTheory.can_pmatch_all_def
    |> CONJUNCT2 |> SPEC_ALL |> concl |> rand |> rand
  val c1 = SIMP_CONV (srw_ss()) [evaluatePropsTheory.can_pmatch_all_EVERY,
                                 evaluatePropsTheory.pmatch_not_type_error_EQ,
                                 semanticPrimitivesTheory.same_type_def]
  val c2 = eval THENC SIMP_CONV (srw_ss()) [] THENC eval
in
  fun can_pmatch_all_conv tm =
    if not (can (match_term can_pmatch_all_tm) tm)
    then NO_CONV tm else let
      val th1 = QCONV (c1 THENC c2) tm
      in if Teq (rhs (concl th1)) then th1 else QCONV c1 tm end
  val reduce_can_pmatch_all_tac =
    CONV_TAC (ONCE_DEPTH_CONV can_pmatch_all_conv)
    \\ PURE_REWRITE_TAC [boolTheory.AND_CLAUSES]
end

val xcases =
  xpull_check_not_needed \\
  unfold_cases \\
  CONV_TAC validate_pat_all_conv \\
  reduce_can_pmatch_all_tac

(* [xmatch] *)

val xmatch_base =
  xpull_check_not_needed \\
  head_unfold cf_match_def \\ irule local_elim \\
  reduce_tac \\
  xcases

val xmatch = xmatch_base

(* [xffi] *)

val xffi =
  xpull_check_not_needed \\
  head_unfold cf_ffi_def \\
  irule local_elim \\ hnf \\
  simp [app_ffi_def] \\ reduce_tac \\
  cleanup_exn_side_cond

(* [xraise] *)

val xraise =
  xpull_check_not_needed \\
  head_unfold cf_raise_def \\ reduce_tac \\
  HO_MATCH_MP_TAC xret_lemma1 \\
  cleanup_exn_side_cond

(* [xhandle] *)

fun xhandle_core cont0 cont1 =
  xpull_check_not_needed \\
  head_unfold cf_handle_def \\
  irule local_elim \\ hnf \\
  cont0 \\
  CONJ_TAC THENL [
    CONJ_TAC THENL [all_tac, cleanup_exn_side_cond],
    cont1
  ]

fun xhandle Q (g as (asl, w)) = let
  val ctx = free_varsl (w :: asl)
  val name = vname_of_post "e" (Term Q)
  val name' =
    prim_variant ctx (mk_var (name, v_ty))
    |> dest_var |> fst
  val qname = [QUOTE name']
in
  xhandle_core
    (qexists_tac Q)
    (qx_gen_tac qname \\
     reduce_tac \\
     TRY xpull)
    g
end

(* [xint_cmp] *)
val xint_cmp =
  xpull_check_not_needed \\
  head_unfold cf_int_cmp_def \\
  reduce_tac \\
  irule local_elim \\ hnf \\
  simp[app_int_cmp_def, semanticPrimitivesTheory.int_cmp_def] \\
  cleanup_exn_side_cond

(* [xarith] *)
val xarith =
  xpull_check_not_needed \\
  head_unfold cf_arith_def \\
  reduce_tac \\
  irule local_elim \\ hnf \\
  simp[app_arith_def] \\
  cleanup_exn_side_cond

val xref = xpull_check_not_needed \\ head_unfold cf_ref_def \\
           irule local_elim \\ hnf \\ simp[app_ref_def] \\ reduce_tac

end
