open preamble basis

val _ = new_theory "divLoop";

val _ = translation_extends "basisProg";

val _ = hide "name";

val evaluate_to_div_limit_def = Define `
  evaluate_to_div_limit st env exp heap lim_opt =
    ∃(sts: num->'ffi semanticPrimitives$state) (cks: num->num) io'.
       (* the heap is a representation of the final io_events *)
       io2heap io' = heap /\
       (* clocks increase *)
       (∀i. cks i < cks (i+1)) /\
       (* all clocks in the sequence produce timeout and a state in sts *)
       (∀i. (!n. lim_opt = SOME n ==> cks i < n) ==>
            evaluate_ck (cks i) st env [exp] =
              (sts i, Rerr (Rabort Rtimeout_error))) /\
       (* the limit state st' approximates all states in the sequence *)
       (∀i. LPREFIX (fromList (sts i).ffi.io_events) io') /\
       (* if there is a maximal io_event list, then io' is that list *)
       ∀j. (∀i. (sts i).ffi.io_events ≼ (sts j).ffi.io_events) ==>
           io' = fromList (sts j).ffi.io_events`;

val evaluate_to_heap_def = Q.prove(`
  evaluate_to_heap st env exp p heap (r:res) <=>
    case r of
    | Val v => (∃ck st'. evaluate_ck ck st env [exp] = (st', Rval [v]) /\
                         st2heap p st' = heap)
    | Exn e => (∃ck st'. evaluate_ck ck st env [exp] = (st', Rerr (Rraise e)) /\
                         st2heap p st' = heap)
    | FFIDiv n conf bytes => (∃ck st'.
        evaluate_ck ck st env [exp]
        = (st', Rerr(Rabort(Rffi_error(Final_event n conf bytes FFI_diverged)))) /\
        st2heap p st' = heap)
    | Div => evaluate_to_div_limit st env exp heap NONE
    | DivN n => evaluate_to_div_limit st env exp heap (SOME n)`,cheat);

(*

val evaluate_to_heap_Val_11 = store_thm("evaluate_to_heap_Val_11",
  ``!st x0 x1 p heap1 heap2 v1 v2.
      evaluate_to_heap st x0 x1 p heap1 (Val v1) /\
      evaluate_to_heap st x0 x1 p heap2 (Val v2) ==> heap1 = heap2 /\ v1 = v2``,
  cheat);

val app_def = prove(
  ``(∀p f Q H. app p f [] H Q ⇔ F) ∧
    (∀x p f Q H. app p f [x] H Q ⇔ app_basic p f x H Q) ∧
    ∀x v11 v10 p f Q H.
         app p f (x::v10::v11) H Q ⇔
         app_basic p f x H
           (POSTv g. H * &app p g (v10::v11) H Q)``,
  cheat);

val app_POST_DIV_N = store_thm("app_POST_DIV_N",
  ``!xs fv H.
      (!n. app (p:'ffi ffi_proj) fv xs H (POST_DIV_N n Qd)) =
      app (p:'ffi ffi_proj) fv xs H (POSTd Qd)``,

  once_rewrite_tac [EQ_SYM_EQ]
  \\ Induct THEN1 fs [app_def]
  \\ reverse (Cases_on `xs`)
  THEN1
   (fs [app_def,app_basic_def] \\ rw [] \\ eq_tac \\ rw []
    THEN1
     (first_x_assum drule \\ fs []
      \\ strip_tac \\ asm_exists_tac \\ fs []
      \\ Cases_on `r` \\ fs [POSTv_def] \\ TRY (fs [cond_def] \\ NO_TAC)
      \\ qexists_tac `Val v` \\ fs []
      \\ fs [SEP_EXISTS_THM,cond_STAR]
      \\ metis_tac [])
    \\ first_x_assum drule \\ fs []
    \\ Cases_on `do_opapp [fv; h']` \\ fs []
    \\ PairCases_on `x` \\ fs []
    \\ strip_tac
    \\ first_assum (qspec_then `0` strip_assume_tac)
    \\ asm_exists_tac \\ fs []
    \\ qexists_tac `r` \\ fs []
    \\ Cases_on `r` \\ fs [POSTv_def] \\ TRY (fs [cond_def] \\ NO_TAC)
    \\ fs [SEP_EXISTS_THM,cond_STAR]
    \\ strip_tac
    \\ first_assum (qspec_then `n` strip_assume_tac)
    \\ Cases_on `r` \\ fs [POSTv_def] \\ TRY (fs [cond_def] \\ NO_TAC)
    \\ fs [SEP_EXISTS_THM,cond_STAR]
    \\ imp_res_tac evaluate_to_heap_Val_11 \\ rveq \\ fs [])
  \\ pop_assum kall_tac
  \\ fs [app_def,app_basic_def] \\ rw [] \\ eq_tac \\ rw []
  THEN1
   (first_x_assum drule \\ fs []
    \\ strip_tac \\ asm_exists_tac \\ fs []
    \\ Cases_on `r` \\ fs [POSTd_def] \\ TRY (fs [cond_def] \\ NO_TAC)
    \\ qexists_tac `DivN n` \\ fs [POST_DIV_N_def,cond_STAR]
    \\ fs [evaluate_to_heap_def,evaluate_to_div_limit_def]
    \\ metis_tac [])
  \\ first_x_assum drule \\ fs []

  \\ strip_tac \\ asm_exists_tac \\ fs []
  \\ Cases_on `r` \\ fs [POSTd_def] \\ TRY (fs [cond_def] \\ NO_TAC)

*)

val app_eq_cf_body = store_thm("app_eq_cf_body",
  ``find_recfun f funs = SOME (param,body) /\
    cf (p:'ffi ffi_proj) body
      (extend_env_rec
         (MAP (\ (f,_,_). f) funs)
         (MAP (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f) funs)
      [param] xs env) H (POST_DIV_N n Qd) ==>
    app p (Recclosure env funs f) xs H (POST_DIV_N (SUC n) Qd)``,
  rw []
  \\ drule (cf_sound |> SIMP_RULE std_ss [sound_def,htriple_valid_def])


  cheat);






val app_POST_DIV_N_0 = store_thm("app_POST_DIV_N_0",
  ``xs <> [] /\ find_recfun f funs = SOME (param, body) ==>
    app p (Recclosure env funs f) xs H (POST_DIV_N 0 (&T))``,
  Induct_on `xs` \\ fs [app_def]
  \\ Cases_on `xs` \\ fs [app_def]
  THEN1
   (fs [app_basic_def,POST_DIV_N_def] \\ rw []
    \\ fs [EVAL ``do_opapp [Recclosure env funs f; h]``,
           option_case_eq,pair_case_eq,PULL_EXISTS]
    \\ qexists_tac `DivN 0` \\ fs [cond_STAR] \\ fs [cond_def]
    \\ fs [evaluate_to_heap_def,evaluate_to_div_limit_def,PULL_EXISTS]
    \\ cheat)
  \\ cheat);

val div_ind = Q.store_thm("div_ind",
  `!fv xs H env funs f.
       fv = Recclosure env funs f /\ xs <> [] /\
       (?param body. find_recfun f funs = SOME (param, body) /\
     (!n. app (p:'ffi ffi_proj) fv xs H (POST_DIV_N n (&T)) ==>
            cf (p:'ffi ffi_proj) body
              (extend_env_rec
                (MAP (\ (f,_,_). f) funs)
                (MAP (\ (f,_,_). naryRecclosure env
                  (letrec_pull_params funs) f) funs)
              [param] xs env) H (POST_DIV_N n (&T)))) ==>
     !n. app (p:'ffi ffi_proj) fv xs H (POST_DIV_N n (&T))`,
  rw [] \\ Induct_on `n`
  THEN1 metis_tac [app_POST_DIV_N_0]
  \\ match_mp_tac (GEN_ALL app_eq_cf_body)
  \\ fs []);

val _ = process_topdecs `fun loop x = loop x` |> append_prog;

val s = get_ml_prog_state ();

val v_def = fetch "-" "loop_v_def"

val env = v_def |> concl |> rand |> rator |> rator |> rand

val funs = v_def |> concl |> rand |> rator |> rand

val f = v_def |> concl |> rand |> rand

val _ = (max_print_depth := 15)

val loop_spec = Q.store_thm ("loop_spec",
  `!xv n.
     app (p:'ffi ffi_proj) ^(fetch_v "loop" s) [xv]
       emp (POST_DIV_N n &T)`,
  strip_tac
  \\ match_mp_tac div_ind
  \\ EXISTS_TAC env
  \\ EXISTS_TAC funs
  \\ EXISTS_TAC f
  \\ conj_tac THEN1 (simp [v_def])
  \\ simp [semanticPrimitivesTheory.find_recfun_def]
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
  \\ xsimpl);

val _ = export_theory ();
