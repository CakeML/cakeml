structure cfAppLib :> cfAppLib = struct

open preamble
open ml_translatorSyntax helperLib cfAppSyntax semanticPrimitivesSyntax
open set_sepTheory cfHeapsBaseLib cfAppTheory ml_translatorTheory

fun mk_app_of_Arrow_goal t = let
  val (t_hyps, t_concl) = strip_imp t
  val (args_pred, ret_pred) = t_concl |> rator |> rator |> strip_Arrow
  val f = t_concl |> rator |> rand
  val f_v = t_concl |> rand
  val fvs = free_vars t_concl
  fun pred_ty pred = pred |> type_of |> dest_type |> snd |> hd
  val xs = mapi (fn i => fn pred =>
      variant fvs (mk_var ("x" ^ (Int.toString i), pred_ty pred))
    ) args_pred
  val vs = mapi (fn i => fn pred =>
      variant fvs (mk_var ("v" ^ (Int.toString i), v_ty))
    ) args_pred
  val args_hyps = map2 (fn pred => fn (x, v) =>
      list_mk_comb (pred, [x, v])
    ) args_pred (zip xs vs)
  val hyps_tm_opt =
    SOME (list_mk_conj (args_hyps @ (map strip_conj t_hyps |> flatten)))
    handle HOL_ERR _ => NONE
  val proj_tm = variant fvs (mk_var ("p", ``:'ffi ffi_proj``))
  val post_v = variant fvs (mk_var ("v", v_ty))
  val post_body =
    mk_cond (
      list_mk_comb (ret_pred, [list_mk_comb (f, xs), post_v])
    )
  fun mk_POSTv Qvtm = (lhs o concl) (SPEC Qvtm cfHeapsBaseTheory.POSTv_def)
  val post_tm = mk_POSTv (mk_abs (post_v, post_body))
  val app_spec_tm =
    mk_app (
      proj_tm,
      f_v,
      listSyntax.mk_list (vs, v_ty),
      emp_tm,
      post_tm
    )
  val goal_body =
      case hyps_tm_opt of
          SOME hyps_tm => list_mk_imp ([t, hyps_tm], app_spec_tm)
        | NONE => mk_imp (t, app_spec_tm)
in
  list_mk_forall (xs @ vs, goal_body)
end

fun auto_prove proof_name (goal,tac) = let
  val (rest,validation) = tac ([],goal) handle Empty => fail()
  in if length rest = 0 then validation [] else let
  in failwith("auto_prove failed for " ^ proof_name) end end

fun app_of_Arrow_rule thm = let
  val thm' = DISCH_ALL thm
  val proof_tac =
    rpt strip_tac \\
    rewrite_tac [app_def] \\
    last_x_assum (fn asm =>
      (drule asm \\ rpt (disch_then drule) \\ strip_tac
       handle HOL_ERR _ => NO_TAC) ORELSE
      (assume_tac asm)) \\
    ASSUM_LIST (fn assums =>
      foldr (fn (asm, tac_acc) =>
        drule Arrow_IMP_app_basic \\
        disch_then (fn th => mp_tac (MATCH_MP th asm)) \\
        match_mp_tac app_basic_weaken \\
        Cases THEN_LT REVERSE_LT THEN1 (simp [cfHeapsBaseTheory.POSTv_def]) \\
        fs [cond_def, SEP_EXISTS_THM] \\ rpt strip_tac \\
        qexists_tac `emp` \\ fs [SEP_CLAUSES] \\ tac_acc
      ) all_tac (rev assums)
    )
  val rule_thm = auto_prove "app_of_Arrow_rule"
    (mk_app_of_Arrow_goal (concl thm'), proof_tac)
in MATCH_MP rule_thm thm' |> SIMP_RULE std_ss [PRECONDITION_def, Eq_def] end

end
