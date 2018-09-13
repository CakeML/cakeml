open preamble basis

val div_ind = Q.store_thm("div_ind",
  `!fv xs H Qd env funs f.
       fv = Recclosure env funs f /\
       (?param body. find_recfun f funs = SOME (param, body) /\
     (app (p:'ffi ffi_proj) fv xs H (POSTd Qd) ==>
         cf (p:'ffi ffi_proj) body
            (extend_env_rec
              (MAP (\ (f,_,_). f) funs)
              (MAP (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f) funs)
          [param] xs env) H (POSTd Qd))) ==>
     app (p:'ffi ffi_proj) fv xs H (POSTd Qd)`,
  cheat
);

val _ = new_theory "pureLoop";

val _ = translation_extends "basisProg";

val _ = process_topdecs `fun loop x = loop x` |> append_prog;

val s = get_ml_prog_state ();

val th = fetch "-" "loop_v_def"

val env = th |> concl |> rand |> rator |> rator |> rand

val funs = th |> concl |> rand |> rator |> rand

val f = th |> concl |> rand |> rand


val cs = computeLib.the_compset
val () = listLib.list_rws cs
val () = basicComputeLib.add_basic_compset cs
val () = semanticsComputeLib.add_semantics_compset cs
val () = ml_progComputeLib.add_env_compset cs
val () = cfComputeLib.add_cf_aux_compset cs
val () = computeLib.extend_compset [
  computeLib.Defs [
    ml_progTheory.merge_env_def,
    ml_progTheory.write_def,
    ml_progTheory.write_mod_def,
    ml_progTheory.write_cons_def,
    ml_progTheory.empty_env_def
    (*semanticPrimitivesTheory.merge_alist_mod_env_def*)
  ]] cs

val _ = (max_print_depth := 15)

val eval = computeLib.CBV_CONV cs THENC EVAL (* TODO: remove EVAL *)
val eval_tac = CONV_TAC eval
fun eval_pat t = (compute_pat cs t) THENC EVAL (* TODO: same *)
fun eval_pat_tac pat = CONV_TAC (DEPTH_CONV (eval_pat pat))



val loop_spec = Q.store_thm ("loop_spec",
  `!xv.
     app (p:'ffi ffi_proj) ^(fetch_v "loop" s) [xv]
       emp (POSTd &T)`,
  rw []
  \\ match_mp_tac div_ind
  \\ EXISTS_TAC env
  \\ EXISTS_TAC funs
  \\ EXISTS_TAC f
  \\ conj_tac THEN1 (simp [th])
  \\ simp [semanticPrimitivesTheory.find_recfun_def]
  \\ rw [cf_def, cfNormaliseTheory.dest_opapp_def]
  \\ CONV_TAC ((RATOR_CONV o RATOR_CONV o RAND_CONV) EVAL)
  \\ fs [th]
  \\ simp [cf_app_def, cfNormaliseTheory.exp2v_def,namespacePropsTheory.nsLookup_nsAppend_some, namespaceTheory.nsLookup_def, cfNormaliseTheory.exp2v_list_def, cfHeapsTheory.local_def]

);

val _ = export_theory ();