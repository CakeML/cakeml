open preamble basis

val _ = new_theory "divLoop";

val _ = translation_extends "basisProg";

val div_ind = Q.store_thm("div_ind",
  `!fv xs H Qd env funs f.
       fv = Recclosure env funs f /\
       (?param body. find_recfun f funs = SOME (param, body) /\
       (?h. Qd h) /\
     (!n. app (p:'ffi ffi_proj) fv xs H (POST_DIV_N n Qd) ==>
            cf (p:'ffi ffi_proj) body
              (extend_env_rec
                (MAP (\ (f,_,_). f) funs)
                (MAP (\ (f,_,_). naryRecclosure env
                  (letrec_pull_params funs) f) funs)
              [param] xs env) H (POST_DIV_N n Qd))) ==>
     app (p:'ffi ffi_proj) fv xs H (POSTd Qd)`,
  cheat
);

val _ = process_topdecs `fun loop x = loop x` |> append_prog;

val s = get_ml_prog_state ();

val v_def = fetch "-" "loop_v_def"

val env = v_def |> concl |> rand |> rator |> rator |> rand

val funs = v_def |> concl |> rand |> rator |> rand

val f = v_def |> concl |> rand |> rand

val _ = (max_print_depth := 15)

val loop_spec = Q.store_thm ("loop_spec",
  `!xv.
     app (p:'ffi ffi_proj) ^(fetch_v "loop" s) [xv]
       emp (POSTd &T)`,
  rw []
  \\ match_mp_tac div_ind
  \\ EXISTS_TAC env
  \\ EXISTS_TAC funs
  \\ EXISTS_TAC f
  \\ conj_tac THEN1 (simp [v_def])
  \\ simp [semanticPrimitivesTheory.find_recfun_def]
  \\ conj_tac THEN1 (simp [cond_def])
  \\ rw [cf_def, cfNormaliseTheory.dest_opapp_def]
  \\ CONV_TAC ((RATOR_CONV o RATOR_CONV o RAND_CONV) EVAL)
  \\ fs [v_def |> CONV_RULE (RAND_CONV EVAL)]
  \\ simp [cf_app_def, cfNormaliseTheory.exp2v_def,
           namespacePropsTheory.nsLookup_nsAppend_some,
           namespaceTheory.nsLookup_def,
           cfNormaliseTheory.exp2v_list_def, cfHeapsTheory.local_def]
  \\ rw []
  \\ qexists_tac `emp`
  \\ qexists_tac `emp`
  \\ qexists_tac `POST_DIV_N n &T`
  \\ rpt strip_tac
  THEN1 (fs [SEP_CLAUSES])
  THEN1 (fs [])
  \\ xsimpl
);

val _ = export_theory ();