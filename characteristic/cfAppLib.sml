(*
  Defines app_of_Arrow_rule function that converts the translator's
  Arrow to CF's app judgement.
*)
structure cfAppLib :> cfAppLib = struct

open preamble
open ml_translatorSyntax helperLib semanticPrimitivesSyntax
open cfHeapsBaseSyntax cfAppSyntax
open set_sepTheory cfHeapsBaseLib cfAppTheory ml_translatorTheory

fun mk_app_of_Arrow_goal ffi_ty t = let
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
  val proj_tm = variant fvs (mk_var ("p", mk_ffi_proj_ty ffi_ty))
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

fun mk_Arrow_of_app_goal t = let
  fun find_remove p l = let
      fun aux acc [] = NONE
        | aux acc (x::xs) =
          if p x then SOME (x, List.rev acc @ xs)
          else aux (x::acc) xs
    in aux [] l end
  fun strip_n n tm =
    if n = 0 then (tm, [])
    else let
      val (tm', arg) = dest_comb tm
      val (tm'', args) = strip_n (n-1) tm'
    in (tm'', args @ [arg]) end
  fun dest_pred t = strip_n 2 t
  fun pred_v t = case dest_pred t of (_, [_, v]) => v | _ => failwith "pred_v"
  fun pred_x t = case dest_pred t of (_, [x, _]) => x | _ => failwith "pred_x"
  val (t_vars, t_body) = strip_forall t
  val (hyps1, concl_tm) = strip_imp t_body
  (* hyps: list of hypothesis *)
  val hyps = flatten (map strip_conj hyps1)
  (* conclusion: of the form "app fv [v1,...,vn] emp post" *)
  val (_, fv, argsv, _, post) = dest_app concl_tm
  (* list of value arguments: v1,...,vn *)
  val (argsv_list, _) = listSyntax.dest_list argsv
  (* hyps are either representation predicates (aka refinement invariants) about
     arguments, or something else
  *)
  val (pred_hyps, other_hyps) = partition (fn p =>
      exists (fn argv => pred_v p ~~ argv handle HOL_ERR _ => false) argsv_list
    ) hyps
  val other_hyps_fvs = free_varsl other_hyps
  (* Mapping with the logical counterparts of v1,...,vn *)
  val assoc_argsv_args = List.map (fn p => (pred_v p, pred_x p)) pred_hyps
  (* Gives the predicate for an argument value.
     We may need to wrap the predicate using Eq if v appears elsewhere. *)
  fun pred_for v = let
    val x = tassoc v assoc_argsv_args
    val need_Eq = tmem x other_hyps_fvs
    val base_pred =
      case List.find (fn p => pred_v p ~~ v) pred_hyps of
          NONE => fail()
        | SOME p => (fst o dest_pred) p
  in if need_Eq then mk_Eq (base_pred, x) else base_pred end
  (* stripping post... *)
  val (_, post_body1) = dest_comb post (* dest_POSTv *)
  val (_, post_body2) = dest_abs post_body1
  val (_, pure_post) = dest_comb post_body2 (* dest_cond *)
  val (concl_pred, f_x, v) =
    (case dest_pred pure_post of
       (concl_pred, [f_x, v]) => (concl_pred, f_x, v)
     | _ => failwith "dest_pred")
  val (f, _) = strip_n (List.length argsv_list) f_x
  (* build the iterated Arrows *)
  val arrows = foldl (fn (argv, arrows) =>
      mk_Arrow (pred_for argv, arrows)
    ) concl_pred (List.rev argsv_list)
  (* re-generalize in the post what was originally quantified *)
  val other_hyps_vars = op_intersect aconv t_vars other_hyps_fvs
  fun mk_list_conj_imp ([], concl) = concl
    | mk_list_conj_imp (hyps, concl) = mk_imp (list_mk_conj hyps, concl)
  val arrows_full_tm =
    list_mk_forall (other_hyps_vars,
      mk_list_conj_imp (other_hyps,
        list_mk_comb (arrows, [f, fv])))
in mk_imp (t, arrows_full_tm) end

fun auto_prove proof_name (goal,tac) = let
  val (rest,validation) = tac ([],goal) handle Empty => fail()
  in if length rest = 0 then validation [] else let
  in failwith("auto_prove failed for " ^ proof_name) end end

fun app_of_Arrow_rule ffi_ty thm = let
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
        drule (INST_TYPE [ffi_varty |-> ffi_ty] Arrow_IMP_app_basic) \\
        disch_then (fn th => mp_tac (MATCH_MP th asm)) \\
        match_mp_tac app_basic_weaken \\
        Cases THEN_LT REVERSE_LT THEN1 (simp [cfHeapsBaseTheory.POSTv_def]) \\
        fs [cond_def, SEP_EXISTS_THM] \\ rpt strip_tac \\
        qexists_tac `emp` \\ fs [SEP_CLAUSES] \\ tac_acc
      ) all_tac (rev assums)
    )
  val rule_thm = auto_prove "app_of_Arrow_rule"
    (mk_app_of_Arrow_goal ffi_ty (concl thm'), proof_tac)
in MATCH_MP rule_thm thm' |> SIMP_RULE std_ss [PRECONDITION_def, Eq_def] end

end
