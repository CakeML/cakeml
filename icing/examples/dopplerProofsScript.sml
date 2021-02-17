(**
  Doppler program proofs
**)

open compilerTheory fromSexpTheory cfTacticsLib ml_translatorLib;
open RealIntervalInferenceTheory ErrorIntervalInferenceTheory CertificateCheckerTheory;
open source_to_sourceTheory source_to_sourceProofsTheory CakeMLtoFloVerTheory
     CakeMLtoFloVerProofsTheory icing_optimisationProofsTheory fpSemPropsTheory
     pureExpsTheory icing_realIdProofsTheory
     (* icing_optimisationsLib *) dopplerProgCompTheory cfSupportTheory;
open machine_ieeeTheory binary_ieeeTheory realTheory realLib RealArith sptreeTheory;
open astToSexprLib fromSexpTheory basis_ffiTheory cfHeapsBaseTheory basis;
open preamble;

val _ = new_theory "dopplerProofs";

val _ = translation_extends "dopplerProgComp";

(** Integrated in automation:
val local_opt_run_thm = mk_local_opt_thm theAST_opt theAST_def;

val (fname, fvars, body) =
  EVAL (Parse.Term ‘getDeclLetParts ^(theOptProg_def |> concl |> rhs)’)
  |> concl |> rhs |> dest_pair
  |> (fn (x,y) => let val (y,z) = dest_pair y in (x,y,z) end)

val (_, fvars_before, body_before) =
  EVAL (Parse.Term ‘getDeclLetParts ^(theAST_def |> concl |> rhs)’)
  |> concl |> rhs |> dest_pair
  |> (fn (x,y) => let val (y,z) = dest_pair y in (x,y,z) end)

val plan_list = theAST_plan_result |> concl |> rhs (* Get the actual plan *)
                   |> listSyntax.dest_list (* get the single plan *)
                   |> (fn (ts, tp) => if (length ts <> 1) then raise ERR "Too many plans constructed" ""
                                        else hd ts)
                   |> listSyntax.dest_list (* extract the plan as a list *)
                   |> #1 (* take the list, ignore type *)

(** Build a backwards simulation theorem for the optimisations and show that they are real-valued ids **)
Theorem doppler_opts_icing_correct =
  mk_opt_correct_thm [Q.SPEC ‘FP_Add’ fp_comm_gen_correct, fp_fma_intro_correct];

Theorem doppler_opts_real_id =
  mk_real_id_thm [SIMP_RULE (srw_ss()) [] (Q.SPEC ‘FP_Add’ fp_comm_gen_real_id), fma_intro_real_id];

*)

val st = get_ml_prog_state ();

val (args, argList, vList) =
  if numArgs = 1 then (“(w1):word64”, “[w1]:word64 list”, “[d1]:v list”)
  else if numArgs = 2 then (“(w1, w2):word64 # word64”, “[w1;w2]:word64 list”, “[d1; d2]:v list”)
  else if numArgs = 3 then (“(w1, w2, w3):word64 # word64 # word64”,
                            “[w1; w2; w3]:word64 list”,
                            “[d1; d2; d3]:v list”)
  else if numArgs = 4 then
    (“(w1, w2, w3, w4):word64 # word64 # word64 #word64”,
     “[w1; w2; w3; w4]:word64 list”,
     “[d1; d2; d3; d4]:v list”)
  else if numArgs = 6 then
    (“(w1, w2, w3, w4, w5, w6):word64 # word64 # word64 # word64 # word64 #word64”,
     “[w1; w2; w3; w4; w5; w6]:word64 list”,
     “[d1; d2; d3; d4; d5; d6]:v list”)
  else if numArgs = 8 then
    (“(w1, w2, w3, w4, w5, w6, w7, w8):word64#word64#word64#word64#word64#word64#word64#word64”,
     “[w1; w2; w3; w4; w5; w6; w7; w8]:word64 list”,
     “[d1; d2; d3; d4; d5; d6; d7; d8]:v list”)
  else (“(w1, w2, w3, w4, w5, w6, w7, w8, w9):word64#word64#word64#word64#word64#word64#word64#word64#word64”,
        “[w1; w2; w3; w4; w5; w6; w7; w8; w9]:word64 list”,
        “[d1; d2; d3; d4; d5; d6; d7; d8; d9]:v list”)

val theAST_real_spec_def =
  Define ‘theAST_real_spec ^args = real_spec_prog ^body_opt theAST_env ^fvars ^argList’

val theAST_opt_float_option_noopt_def =
  Define ‘theAST_opt_float_option_noopt ^args =
          case evaluate
               (empty_state with fp_state := empty_state.fp_state with canOpt := FPScope NoOpt)
               (theAST_env with v := extend_env_with_vars (REVERSE ^fvars) (REVERSE ^argList) (theAST_env).v)
   [^body_opt] of
   | (st, Rval [FP_WordTree fp]) =>
     if st = (empty_state with fp_state := empty_state.fp_state with canOpt := FPScope NoOpt)
     then SOME fp else NONE
   | _ => NONE’

val theAST_opt_float_option_def =
  Define ‘theAST_opt_float_option ^args =
         case evaluate empty_state
                       (theAST_env with v := extend_env_with_vars (REVERSE ^fvars) (REVERSE ^argList) (theAST_env).v)
   [^body_opt] of
   | (st, Rval [FP_WordTree fp]) => if (st = empty_state) then SOME fp else NONE
   | _ => NONE’

val theAST_float_returns_def =
  Define ‘
  theAST_float_returns ^args w ⇔
  ∃ fpOpts st2 fp.
    let theOpts = FLAT (MAP (λ x. case x of |Apply (_, rws) => rws |_ => []) (HD theAST_plan)) in
      evaluate (empty_state with fp_state :=
                empty_state.fp_state with
                           <| rws := theOpts ; opts := fpOpts; canOpt := FPScope NoOpt |>)
               (theAST_env with v :=
                extend_env_with_vars (REVERSE ^fvars) (REVERSE ^argList) (theAST_env).v)
               [^body] = (st2, Rval [FP_WordTree fp]) ∧ compress_word fp = w’

Theorem freeVars_list_body:
  ∀ (st1:unit semanticPrimitives$state) st2.
    freeVars_list_arithExp_bound
      st1 st2 [^body]
      (theAST_env with v :=
       extend_env_with_vars (REVERSE ^fvars) (REVERSE ^argList) (theAST_env).v)
Proof
  rpt strip_tac
  \\ gs[freeVars_arithExp_bound_def, icing_rewriterTheory.isFpArithExp_def,
        freeVars_fp_bound_def]
  \\ rpt conj_tac
  (* Non-let goals are automatically solved *)
  \\ TRY (gs[extend_env_with_vars_def] \\ NO_TAC)
  (* Remainder: let-goals *)
  \\ rpt strip_tac
  (* Let-goals not reasoning about let-bound variable *)
  \\ TRY (gs[extend_env_with_vars_def,namespaceTheory.nsOptBind_def] \\ NO_TAC)
  \\ rveq
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ qmatch_goalsub_abbrev_tac ‘evaluate theState theEnv [theExp] = _’
  \\ ‘isFpArithExp theExp’ by (unabbrev_all_tac \\ EVAL_TAC)
  \\ first_x_assum $ mp_then Any mp_tac (INST_TYPE [“:'a” |-> “:unit”] (CONJUNCT1 icing_rewriterProofsTheory.isFpArithExp_matched_evaluates))
  \\ disch_then (qspecl_then [‘theEnv’, ‘theState’] mp_tac)
  \\ impl_tac
  (* free variables must be bound *)
  \\ TRY (rpt strip_tac \\ rename1 ‘x IN FV theExp’ \\ unabbrev_all_tac
          \\ gs[extend_env_with_vars_def, namespaceTheory.nsOptBind_def]
          \\ NO_TAC)
  (* use the theorem to prove the conclusion *)
  \\ TRY (rpt strip_tac \\ imp_res_tac evaluatePropsTheory.evaluate_sing \\ gs[]
          \\ rveq \\ gs[extend_env_with_vars_def, namespaceTheory.nsOptBind_def] \\ NO_TAC)
QED

Theorem theAST_opt_backward_sim:
  theAST_opt_float_option_noopt ^args = SOME w ⇒
  theAST_float_returns ^args (compress_word w)
Proof
  simp[theAST_opt_float_option_noopt_def, theAST_float_returns_def]
  \\ rpt gen_tac
  \\ ntac 5 (TOP_CASE_TAC \\ fs[])
  \\ strip_tac \\ rveq
  \\ fs[GSYM local_opt_thm]
  \\ first_x_assum (mp_then Any assume_tac no_optimisations_eval_sim)
  \\ fs[]
  \\ first_x_assum (qspecl_then [‘NoOpt’, ‘empty_state.fp_state.choices’] assume_tac)
  \\ pop_assum mp_tac \\ impl_tac
  >- (EVAL_TAC)
  \\ strip_tac
  \\ fs[] \\ imp_res_tac noopt_sim_val \\ rveq
  \\ imp_res_tac noopt_sim_val_fp \\ rveq \\ fs[]
  \\ qpat_x_assum `evaluate _ _ _ = _` mp_tac
  \\ qmatch_goalsub_abbrev_tac ‘evaluate emp_upd dEnv [FST(optimise_with_plan theOpts thePlan e_init)] = (emp_res, _)’
  \\ strip_tac
  \\ assume_tac (INST_TYPE [“:'a” |-> “:unit”] stos_pass_correct_thm)
  \\ first_x_assum
       (qspecl_then [‘emp_upd’, ‘emp_res’, ‘dEnv’, ‘theOpts’, ‘[e_init]’, ‘[FP_WordTree fp2]’] mp_tac)
  \\ simp[is_optimise_with_plan_correct_def]
  \\ impl_tac
  >- (
   unabbrev_all_tac
   \\ fs[empty_state_def, theOpts_def, extend_conf_def, no_fp_opt_conf_def,
         theAST_env_def, stos_pass_with_plans_def, theAST_plan_result]
   \\ assume_tac freeVars_list_body \\ gs[theAST_env_def])
  \\ rpt strip_tac
  \\ unabbrev_all_tac
  \\ fs[empty_state_def, semanticPrimitivesTheory.state_component_equality, theAST_env_def]
  \\ qpat_x_assum ‘evaluate _ _ [ _ ] = _’ mp_tac
  \\ qmatch_goalsub_abbrev_tac ‘evaluate newSt newEnv _ = _’
  \\ strip_tac
  \\ qexists_tac ‘newSt.fp_state.opts’
  \\ unabbrev_all_tac
  \\ first_x_assum (mp_then Any (qspec_then ‘0’ assume_tac) (CONJUNCT1 fpSemPropsTheory.evaluate_add_choices))
  \\ fs[theOpts_def, no_fp_opt_conf_def, extend_conf_def,
        config_component_equality, theAST_plan_result]
QED

val theAST_side_def =
  Define ‘theAST_side ^args = (is_precond_sound ^fvars ^argList ^(theAST_pre_def |> concl |> rhs))’

Definition is_Double_def:
  is_Double [] [] = T ∧
  is_Double (w1::ws) (d1::ds) = (DOUBLE (Fp_const w1) d1 ∧ is_Double ws ds)
End

val theAST_v = fetch_v (stringSyntax.fromHOLstring fname) st
val theAST_v_def = DB.find ((term_to_string theAST_v)^"_def") |> hd |> #2 |> #1

Theorem theAST_spec:
  theAST_side ^args ∧
  is_Double ^argList ^vList  ⇒
  let result = (theAST_opt_float_option ^args) in
    (∀ p.
       app (p:'ffi ffi_proj) ^theAST_v
           ^vList
           (emp)
           (POSTv v.
            &DOUBLE_RES result v)) ∧
    theAST_float_returns (w1,w2,w3) (compress_word (THE result)) ∧
    real$abs (fp64_to_real (compress_word (THE result)) - theAST_real_spec ^args) ≤ theErrBound
Proof
  rpt gen_tac \\ simp[app_def, theAST_side_def, is_Double_def]
  \\ rpt (disch_then assume_tac)
  \\ rpt (gen_tac ORELSE (disch_then assume_tac)) \\ fs[]
  \\ mp_tac errorbounds_AST
  \\ fs[isOkError_def, option_case_eq, pair_case_eq, getErrorbounds_def, stripFuns_def, PULL_EXISTS]
  \\ rpt gen_tac
  \\ TOP_CASE_TAC \\ fs[option_case_eq, pair_case_eq]
  \\ rpt (gen_tac ORELSE (disch_then assume_tac)) \\ fs[] \\ rveq
  \\ first_assum (mp_then Any mp_tac CakeML_FloVer_infer_error)
  \\ fs[checkErrorbounds_succeeds_def, PULL_EXISTS]
  \\ qpat_x_assum ‘toFloVerCmd _ _ _ = SOME _’
                  (fn th => disch_then (fn ith => mp_then Any mp_tac ith th) \\ assume_tac th)
  \\ fs[theAST_pre_def]
  \\ disch_then (qspecl_then
                 [‘theAST_env’,
                  ‘case ^(theAST_opt |> concl |> rhs) of | [Dlet _ _ e] => e’] mp_tac)
  \\ impl_tac
  >- fs[stripFuns_def]
  \\ strip_tac
  \\ simp[semanticPrimitivesTheory.do_opapp_def, theAST_v_def]
  \\ reverse conj_tac
  >- (
   rpt (pop_assum mp_tac) \\ simp[] \\ rpt (disch_then assume_tac)
   \\ rveq
   \\ ‘theAST_opt_float_option_noopt ^args = SOME fp’
      by (fs[theAST_opt_float_option_noopt_def])
   \\ imp_res_tac theAST_opt_backward_sim
   \\ rfs[theAST_opt_float_option_def, theAST_real_spec_def,
          real_spec_prog_def, theAST_real_spec_def]
   \\ assume_tac (INST_TYPE [“:'a” |-> “:unit”] stos_pass_real_id_thm)
   \\ qpat_x_assum `evaluate _ _ [realify _] = _` mp_tac
   \\ unabbrev_all_tac
   \\ simp[GSYM local_opt_thm]
   \\ qmatch_goalsub_abbrev_tac ‘evaluate _ _ [realify (no_optimisations theOpts (FST e_opt))] = _’
   \\ disch_then (mp_then Any mp_tac evaluate_no_optimisations)
   \\ fs[]
   \\ disch_then (qspecl_then [‘NoOpt’, ‘empty_state.fp_state.choices’] mp_tac)
   \\ impl_tac \\ unabbrev_all_tac
   >- (EVAL_TAC)
   \\ qmatch_goalsub_abbrev_tac ‘evaluate emptyWithReals realEnv [realify (FST (optimise_with_plan theOpts thePlan e_init))] = _’
   \\ strip_tac
   \\ fs[is_real_id_optimise_with_plan_def]
   \\ first_x_assum (
      qspecl_then [ ‘emptyWithReals’, ‘emptyWithReals’, ‘realEnv’, ‘theOpts’, ‘[e_init]’, ‘[Real r]’] mp_tac)
   \\ simp[MAP]
   \\ unabbrev_all_tac \\ fs[theAST_plan_result]
   \\ impl_tac
   >- (
    imp_res_tac evaluate_realify_state
    \\ qpat_x_assum `isPureExp _ ⇒ _ = _` mp_tac
    \\ impl_tac >- EVAL_TAC
    \\ strip_tac \\ fs[theOpts_def, no_fp_opt_conf_def])
   \\ strip_tac \\ rveq
   \\ irule REAL_LE_TRANS \\ asm_exists_tac \\ fs[])
  \\ ntac (numArgs-1)
          (rpt strip_tac \\ once_rewrite_tac [app_basic_def]
           \\ simp[semanticPrimitivesTheory.do_opapp_def, set_sepTheory.cond_def]
           \\ rpt strip_tac
           (* We will return a val but we do not know which one *)
           \\ Q.REFINE_EXISTS_TAC ‘Val v’
           \\ simp[evaluate_to_heap_def, evaluate_ck_def, terminationTheory.evaluate_def]
           \\ ntac 2 (qexists_tac ‘EMPTY’)
           \\ fs[emp_def, set_sepTheory.SPLIT_def, cfHeapsBaseTheory.SPLIT3_def,
                 set_sepTheory.SEP_EXISTS]
           \\ simp[Once set_sepTheory.STAR_def]
           \\ qexists_tac ‘emp’
           \\ rpt (qexists_tac ‘EMPTY’) \\ conj_tac
           >- fs[emp_def, set_sepTheory.SPLIT_def, cfHeapsBaseTheory.SPLIT3_def]
           \\ conj_tac
           >- fs[emp_def])
  \\ once_rewrite_tac [app_basic_def]
  \\ simp[semanticPrimitivesTheory.do_opapp_def, set_sepTheory.cond_def]
  \\ rpt strip_tac
  \\ Q.REFINE_EXISTS_TAC ‘Val v’
  \\ simp[DOUBLE_RES_def, theAST_opt_float_option_def]
  \\ fs[emp_def] \\ rveq
  \\ qexists_tac ‘EMPTY’
  \\ rename1 ‘st2heap p st_final’
  \\ qexists_tac ‘st2heap p st_final’ \\ conj_tac
  >- fs[emp_def, set_sepTheory.SPLIT_def, cfHeapsBaseTheory.SPLIT3_def]
  \\ simp[evaluate_to_heap_def, evaluate_ck_def]
  \\ first_x_assum
     (mp_then Any mp_tac
      (INST_TYPE [“:'a”|->“:unit”, “:'b”|->“:'ffi”] pureExpsTheory.isPureExpList_swap_state))
  \\ disch_then (qspec_then ‘st_final with clock := 0’ mp_tac)
  \\ impl_tac \\ fs[]
  >- (unabbrev_all_tac \\ EVAL_TAC)
  \\ strip_tac \\ qexists_tac ‘0’ \\ fs[extend_env_with_vars_def, DOUBLE_def, theAST_env_def]
QED

val (cl_list, inp_list, inps) =
  let val (cstStrs, inps) =
      if numArgs = 1 then
        (“[cst1s]:mlstring list”, “(cst1s):mlstring”)
      else if numArgs = 2 then
        (“[cst1s; cst2s]:mlstring list”, “(cst1s,cst2s):mlstring#mlstring”)
      else if numArgs = 3 then
        (“[cst1s; cst2s; cst3s]:mlstring list”,
        “(cst1s, cst2s, cst3s):mlstring#mlstring#mlstring”)
      else if numArgs = 4 then
        (“[cst1s; cst2s; cst3s; cst4s]:mlstring list”,
        “(cst1s, cst2s, cst3s, cst4s):mlstring#mlstring#mlstring#mlstring”)
      else if numArgs = 6 then
        (“[cst1s; cst2s; cst3s; cst4s; cst5s; cst6s]:mlstring list”,
        “(cst1s, cst2s, cst3s, cst4s, cst5s, cst6s):
          mlstring#mlstring#mlstring#mlstring#mlstring#mlstring”)
      else if numArgs = 8 then
        (“[cst1s; cst2s; cst3s; cst4s; cst5s; cst6s; cst7s; cst8s]:mlstring list”,
        “(cst1s, cst2s, cst3s, cst4s, cst5s, cst6s, cst7s, cst8s):
          mlstring#mlstring#mlstring#mlstring#mlstring#mlstring#mlstring#mlstring”)
      else (* numArgs = 9 *)
        (“[cst1s; cst2s; cst3s; cst4s; cst5s; cst6s; cst7s; cst8s; cst9s]:mlstring list”,
        “(cst1s, cst2s, cst3s, cst4s, cst5s, cst6s, cst7s, cst8s, cst9s):
          mlstring#mlstring#mlstring#mlstring#mlstring#mlstring#mlstring#mlstring#mlstring”)
  in (EVAL (Parse.Term ‘[fname] ++ ^cstStrs’) |> concl |> rhs, cstStrs, inps)
  end

Definition all_float_string_def:
  all_float_string [] [] = T ∧
  all_float_string (s1::ss) (w1::ws) = (is_float_string s1 w1 ∧ all_float_string ss ws)
End

Theorem main_spec:
  ∀ p.
  cl = ^cl_list ∧
  all_float_string ^inp_list ^argList ∧
  theAST_side ^args ⇒
  let
    result = theAST_opt_float_option ^args
  in
  app p ^(fetch_v "main" st)
    [Conv NONE []]
    (STDIO fs * COMMANDLINE cl)
    (POSTv uv. &UNIT_TYPE () uv *
     STDIO (add_stdout fs (mlint$toString (&w2n (compress_word (THE result))))))
    ∧
    theAST_float_returns ^args (compress_word (THE result)) ∧
    real$abs (fp64_to_real (compress_word (THE result)) -
      theAST_real_spec ^args) ≤ theErrBound
Proof
  simp[all_float_string_def] \\ rpt strip_tac
  \\ first_x_assum $ mp_then Any assume_tac
                   $ SIMP_RULE std_ss [is_Double_def] (INST_TYPE [“:'ffi”|->“:'a”] theAST_spec)
  >- (
   xcf "main" st
   (* let for unit value *)
   \\ xlet_auto >- (xcon \\ xsimpl)
   \\ ‘^(numSyntax.term_of_int (numArgs+1)) = LENGTH cl’ by (rveq \\ fs[])
   \\ rveq
   \\ xlet_auto_spec (SOME reader_spec)
   >- (xsimpl \\ qexists_tac ‘emp’ \\ xsimpl
       \\ qexists_tac ‘fs’ \\ xsimpl)
   \\ xmatch
   \\ fs[PAIR_TYPE_def] \\ reverse conj_tac
   >- (EVAL_TAC \\ fs[])
   \\ rveq \\ fs[is_float_string_def] \\ rveq
   \\ ntac numArgs (
     last_x_assum (mp_then Any mp_tac intToFP_spec)
     \\ disch_then (fn ith => last_x_assum $ mp_then Any mp_tac ith)
     \\ disch_then drule
     \\ disch_then (qspecl_then [‘p’, ‘fs’] assume_tac)
     \\ xlet_auto
     >- (xsimpl \\ qexists_tac ‘emp’ \\ xsimpl
         \\ qexists_tac ‘fs’ \\ xsimpl)
     \\ qpat_x_assum `app _ intToFP_v _ _ _` kall_tac)
   \\ first_x_assum drule
   \\ rpt (disch_then drule) \\ strip_tac
   \\ xlet_auto >- xsimpl
   \\ qpat_x_assum ‘DOUBLE_RES _ _’ mp_tac
   \\ simp[DOUBLE_RES_def] \\ TOP_CASE_TAC \\ fs[]
   \\ rpt strip_tac \\ rveq
   \\ qmatch_goalsub_abbrev_tac ‘compress_word f’
   \\ xlet ‘POSTv v. &WORD (compress_word f) v * STDIO fs’
   >- (
    fs[cf_fptoword_def, cfHeapsTheory.local_def, cfNormaliseTheory.exp2v_def,
       cfTheory.app_fptoword_def]
    \\ rpt strip_tac
    \\ fs[WORD_def]
    \\ qexists_tac ‘STDIO fs’ \\ qexists_tac ‘emp’
    \\ fs[set_sepTheory.STAR_def]
    \\ qexists_tac ‘POSTv v. &WORD (compress_word f) v * STDIO fs’ \\ rpt conj_tac
    >- (
     qexists_tac ‘h’ \\ qexists_tac ‘EMPTY’ \\ fs[SPLIT_def, emp_def])
    >- (
     fs[DOUBLE_def, set_sepTheory.SEP_IMP_def]
     \\ rpt strip_tac \\ fs[set_sepTheory.cond_def, set_sepTheory.STAR_def]
     \\ qexists_tac ‘s’ \\ fs[SPLIT_def])
    \\ xsimpl \\ rveq \\ rpt strip_tac
    \\ fs[set_sepTheory.SEP_IMP_def, set_sepTheory.STAR_def] \\ rpt strip_tac
    \\ qexists_tac ‘s’ \\ qexists_tac ‘EMPTY’
    \\ fs[SPLIT_def, GC_def] \\ conj_tac
    >- (rveq \\ rewrite_tac [CONJ_ASSOC]
        \\ once_rewrite_tac [CONJ_COMM] \\ asm_exists_tac \\ fs[]
        \\ qexists_tac ‘EMPTY’
        \\ fs[set_sepTheory.cond_def, WORD_def])
    \\ fs[set_sepTheory.SEP_EXISTS] \\ qexists_tac ‘emp’ \\ fs[emp_def])
   \\ xapp \\ xsimpl)
  \\ fs[DOUBLE_def]
QED

Theorem main_whole_prog_spec:
  cl = ^cl_list ∧
  all_float_string ^inp_list ^argList ∧
  theAST_side ^args ⇒
  whole_prog_spec ^(fetch_v "main" st) cl fs
  NONE
  ((=)
   (add_stdout fs (mlint$toString (&w2n (compress_word (THE (theAST_opt_float_option ^args)))))))
  ∧
  theAST_float_returns ^args (compress_word (THE (theAST_opt_float_option ^args))) ∧
  real$abs (fp64_to_real (compress_word (THE (theAST_opt_float_option ^args))) -
            theAST_real_spec ^args) ≤ theErrBound
Proof
  simp[whole_prog_spec_def]
  \\ qmatch_goalsub_abbrev_tac`fs1 = _ with numchars := _`
  \\ rpt (strip_tac)
  \\ qspec_then ‘(basis_proj1, basis_proj2)’ mp_tac main_spec
  \\ impl_tac \\ fs[]
  \\ strip_tac
  \\ qexists_tac`fs1`
  \\ simp[Abbr`fs1`,GSYM add_stdo_with_numchars,with_same_numchars]
  \\ first_x_assum (fn main_spec => irule (MP_CANON (MATCH_MP app_wgframe main_spec)))
  \\ xsimpl
QED

val spec = main_whole_prog_spec;
val name = "main";

val (prog_rewrite, semantics_prog_thm) = mk_whole_prog_spec_thm spec name (get_ml_prog_state());

val theAST_prog_tm = rhs (concl prog_rewrite);

val theAST_prog_def = Define`theAST_prog = ^theAST_prog_tm`;

val full_semantics_prog_thm =
      CONJUNCT2 (SIMP_RULE std_ss [cfSupportTheory.IMP_SPLIT] main_whole_prog_spec)
              |> SIMP_RULE std_ss [GSYM cfSupportTheory.IMP_SPLIT, GSYM AND_IMP_INTRO]
              |> UNDISCH_ALL
              |> (fn th => LIST_CONJ [semantics_prog_thm, th])
              |> DISCH_ALL |> SIMP_RULE std_ss [];

Theorem theAST_semantics =
  full_semantics_prog_thm |> ONCE_REWRITE_RULE[GSYM theAST_prog_def]
  |> DISCH_ALL |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC];

Definition theAST_semantics_side_def:
  theAST_semantics_side ^inps ^args ⇔
    all_float_string ^inp_list ^argList ∧
    theAST_side ^args
End

Theorem theAST_semantics_final:
  theAST_semantics_side ^inps ^args ∧ init_ok (^cl_list,fs) ⇒
  ∃ (w:word64).
    CakeML_evaluates_and_prints (^cl_list,fs,theAST_prog) (toString w) ∧
    theAST_float_returns ^args w ∧
    real$abs (fp64_to_real w - theAST_real_spec ^args) ≤ theErrBound
Proof
  rpt strip_tac
  \\ fs[init_ok_def, CakeML_evaluates_and_prints_def, theAST_semantics_side_def]
  \\ first_x_assum (mp_then Any mp_tac theAST_semantics)
  \\ rpt (disch_then drule) \\ fs[]
  \\ disch_then drule \\ strip_tac
  \\ qexists_tac ‘compress_word (THE (theAST_opt_float_option ^args))’ \\ fs[]
  \\ asm_exists_tac \\ fs[toString_def]
QED

val _ = export_theory();
