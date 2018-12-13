(*
  Functions that aid building the CakeML code for the basis library.
*)
structure basisFunctionsLib :> basisFunctionsLib =
struct

open preamble
     semanticPrimitivesTheory ml_translatorTheory
     ml_translatorLib ml_progLib cfLib
(* TODO: process_topdecs is exported here, but should probably be in a parsing
         library instead *)

fun get_module_prefix () = let
  val mod_tm = ml_progLib.get_thm (get_ml_prog_state ())
               |> concl |> rator |> rator |> rand
  in if optionSyntax.is_none mod_tm then "" else
       stringSyntax.fromHOLstring (mod_tm |> rand |> rator |> rand) ^ "_"
  end

fun trans ml_name rhs = let
  val prefix = get_module_prefix ()
  val hol_name = prefix ^ pick_name ml_name
  val hol_name_clashes = (fst (dest_const rhs) = hol_name)
                         handle HOL_ERR _ => false
  val tm = mk_eq(mk_var(hol_name,type_of rhs),rhs)
  val def = Define `^tm`
  val _ = (next_ml_names := [ml_name])
  val v_thm = translate (def |> SIMP_RULE std_ss [FUN_EQ_THM])
  val v_thm = v_thm |> REWRITE_RULE [def]
                    |> CONV_RULE (DEPTH_CONV ETA_CONV)
  val v_name = v_thm |> concl |> rand |> dest_const |> fst
  val _ = if hol_name_clashes
          then remove_ovl_mapping hol_name
                 {Name = hol_name, Thy = current_theory()}
          else ()
  (* evaluate precondition *)
  val pat = PRECONDITION_def |> SPEC_ALL |> GSYM |> concl |> rand
  fun PRECOND_CONV c tm =
    if can (match_term pat) tm then RAND_CONV c tm else NO_CONV tm
  val v_thm = v_thm |> DISCH_ALL
                    |> CONV_RULE (ONCE_DEPTH_CONV (PRECOND_CONV EVAL))
                    |> UNDISCH_ALL
  val _ = save_thm(v_name ^ "_thm",v_thm)
  in v_thm end

fun append_prog tm = let
  val tm = QCONV EVAL tm |> concl |> rand
  in ml_prog_update (ml_progLib.add_prog tm pick_name) end

fun append_dec tm = let
  val tm = QCONV EVAL tm |> concl |> rand
  in ml_prog_update (ml_progLib.add_dec tm pick_name) end

fun append_decs tm = let
  val tm = QCONV EVAL tm |> concl |> rand
  val tms = fst (listSyntax.dest_list tm)
  in (map append_dec tms; ()) end

fun prove_ref_spec op_name =
  xcf op_name (get_ml_prog_state ()) \\
  fs [cf_ref_def, cf_deref_def, cf_assign_def] \\ irule local_elim \\
  reduce_tac \\ fs [app_ref_def, app_deref_def, app_assign_def] \\
  xsimpl \\ fs [UNIT_TYPE_def]

end
