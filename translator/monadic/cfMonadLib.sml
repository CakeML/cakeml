structure cfMonadLib (* :> cfMonadLib *) = struct

open cfAppTheory cfTacticsLib ml_monad_translatorTheory cfMonadTheory

val PURE_tm = ``PURE : ('a -> v -> bool) -> ('a, 'b) H``;
fun mk_app_of_ArrowP_goal spec = let
    val spec = PURE_REWRITE_RULE[ArrowM_def] spec
    val arrow_RI = concl spec |> rator |> rator
    val f_const = concl spec |> rator |> rand
    val fv_const = concl spec |> rand
    val H = arrow_RI |> rator |> rator |> rand
    val state_type = type_of H |> dest_type |> snd |> List.hd
    val state_var = mk_var("state", state_type)
    val p_var = mk_var("p", ``:unit ffi_proj``)

    (* Create variables for the HOL and CakeML parameters, retrieve the refinement invariants *)
    fun get_params arrow_RI n = let
	val (comb_tm, params) = strip_comb arrow_RI
	val ri = rator arrow_RI |> rand |> rand
	val arrow_RI' = rand arrow_RI
	val comb_tm = rator arrow_RI'
	val x = mk_var("x"^(Int.toString n), type_of ri |> dest_type |> snd |> List.hd)
	val xv = mk_var("xv"^(Int.toString n), ``:v``)
	val x_triple = (x, xv, ri)
    in if same_const PURE_tm comb_tm then let
	   val arrow_RI' = rand arrow_RI'
	   val (params_v, ret_invs) = get_params arrow_RI' (n+1)
       in (x_triple::params_v, ret_invs) end
       else ([x_triple], (rator arrow_RI' |> rand, rand arrow_RI'))
    end
    val (params_info, (ret_inv, exn_inv)) = get_params arrow_RI 1
    val ri_hyps = List.map (fn (x, xv, ri) => list_mk_comb(ri, [x, xv])) params_info
    val params = List.map #1 params_info

    (* Start the recursion *)
    val current_f = list_mk_comb (f_const, List.take(params, List.length params - 1))
    val (last_x, last_xv, last_ri) = List.last params_info
    val xl = List.map #1 params_info
    val xvl = List.map #2 params_info
    val params_info = List.tl(List.rev params_info)
    val fv_var = mk_var("fv", ``:v``)
    val gv_var = mk_var("gv", ``:v``)

    val th = ISPECL[last_ri, ret_inv, exn_inv, current_f, gv_var, H, last_x, last_xv, state_var] ArrowP_MONAD_to_app |> SPEC_ALL |> UNDISCH

    val Q = concl th |> rand |> rand
    val Q_abs = mk_abs(state_var, Q)

    (* Perform the recursion *)
    (* val (x, xv, ri) = List.hd params_info *)
    fun mk_app_rec th ((x, xv, ri)::x_info) = let
	val A = ri
	val B = concl th |> dest_imp |> fst |> rator |> rator
	val (xv2, xvl) = concl th |> dest_imp |> snd |> rator |> rator |> rand |> dest_comb
	val xv2 = rand xv2
	val f_tm = concl th |> dest_imp |> fst |> rator |> rand |> rator
	
	val assum = GENL[state_var, gv_var] th
	val imp_th = ISPECL[A, B, f_tm, fv_var, x, xv, xv2, xvl, H, Q_abs] ArrowP_PURE_to_app
			|> SPEC_ALL |> UNDISCH |> BETA_RULE
	val th = MP imp_th assum |> SPEC_ALL |> Thm.INST [fv_var |-> gv_var]
    in mk_app_rec th x_info end
      | mk_app_rec th [] = th
    val th = mk_app_rec th params_info

    (* Instantiate the CakeML function variable and remove the ArrowP hypothesis *)
    val th = MP (Thm.INST[gv_var |-> fv_const] th) spec

    (* Undischarge the refinement invariants for the arguments *)
    val th = List.foldr (fn (a, th) => DISCH a th) th ri_hyps

    (* Generalize the variables *)
    val th = GENL[state_var, p_var] th |> GENL xvl |> GENL xl
in th end

end
