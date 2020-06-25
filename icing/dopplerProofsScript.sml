(**
  Doppler program proofs
**)

open compilerTheory fromSexpTheory cfTacticsLib ml_translatorLib;
open RealIntervalInferenceTheory ErrorIntervalInferenceTheory CertificateCheckerTheory;
open source_to_sourceTheory source_to_sourceProofsTheory CakeMLtoFloVerTheory
     CakeMLtoFloVerProofsTheory icing_optimisationProofsTheory icing_optimisationsLib dopplerProgCompTheory cfSupportTheory;
open machine_ieeeTheory binary_ieeeTheory realTheory realLib RealArith;
open astToSexprLib fromSexpTheory basis_ffiTheory cfHeapsBaseTheory basis;
open preamble;

val _ = new_theory "dopplerProofs";

val _ = translation_extends "cfSupport";

(** Step 1: Build a backwards simulation theorem for the optimisations **)
val all_rewrites_corr =
  mk_opt_correct_thm [Q.SPEC ‘FP_Add’ fp_comm_gen_correct, fma_intro_correct]

Theorem doppler_opts_icing_correct = all_rewrites_corr;

val reader =
  process_topdecs ‘
   fun reader u =
   let
   val cl = CommandLine.arguments ();
   val cst1 = List.hd cl;
   val cst2 = List.hd (List.tl cl);
   val cst3 = List.hd (List.tl (List.tl cl));
   in (cst1, (cst2, cst3)) end;’

(*
  process_topdecs ‘
   fun reader u =
   let
   val cl = CommandLine.arguments ();
   in
   case cl of
    x1::x2::x3::xs => (x1,(x2,x3))
   end;’ *)

val _ = append_prog reader;

val main =
“[Dlet unknown_loc (Pvar "main")
  (Fun "a"
   (Let (SOME "u") (Con NONE [])
   (Let (SOME "strArgs")
    (App Opapp [Var (Short "reader"); Var (Short "u")])
    (Mat (Var (Short "strArgs"))
     [(Pcon NONE [Pvar "d1s"; Pcon NONE [Pvar "d2s"; Pvar "d3s"]],
       (Let (SOME "d1")
        (App Opapp [Var (Short "intToFP"); Var (Short "d1s")])
        (Let (SOME "d2")
         (App Opapp [Var (Short "intToFP"); Var (Short "d2s")])
         (Let (SOME "d3")
          (App Opapp [Var (Short "intToFP"); Var (Short "d3s")])
          (Let (SOME "x" )
           (App Opapp [
              App Opapp [
                App Opapp [Var (Short "doppler"); Var (Short "d1")];
                Var (Short "d2")];
              Var (Short "d3")])
           (Let (SOME "y")
            (App FpToWord [Var (Short "x")])
            (App Opapp [
               Var (Short "printer");
               Var (Short "y")])))))))]))))]”;

val iter_code = process_topdecs ‘
 fun iter n s f =
     if (n = 0) then s else iter (n-1) (f s) f;’

val iter_count = “10000000:int”

val call_code = Parse.Term ‘
 [Dlet unknown_loc (Pvar "it")
  (Let (SOME "b")
   (Fun "x"
    (Let NONE
     (App Opapp [
        App Opapp [
          App Opapp [
            Var (Short "doppler");
            App FpFromWord [Lit (Word64 4607182418800017408w)]];
          App FpFromWord [Lit (Word64 4607182418800017408w)]];
        App FpFromWord [Lit (Word64 4607182418800017408w)]])
     (Con NONE [])))
   (Let (SOME "a") (Con NONE [])
    (App Opapp [
       App Opapp [
         App Opapp [Var (Short "iter"); Lit (IntLit ^iter_count)];
         Var (Short "a")]; Var (Short "b")])))]’;

Definition theBenchmarkMain_def:
  theBenchmarkMain =
  (HD (^iter_code)) :: (^call_code)
End

val st_no_doppler = get_ml_prog_state ();

val doppler_env = st_no_doppler
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_env;

val _ = append_prog (theOptProg_def |> concl |> rhs)

val _ = append_prog main;

val st = get_ml_prog_state ();

Theorem stos_pass_decs_unfold:
  stos_pass_decs cfg [Dlet loc p e] = [Dlet loc p (HD (stos_pass cfg [e]))]
Proof
  simp[stos_pass_decs_def]
QED

Theorem stos_pass_unfold:
  stos_pass cfg [Fun s e] = [Fun s (HD (stos_pass cfg [e]))]
Proof
  simp[stos_pass_def]
QED

Theorem stos_pass_optimise:
  stos_pass cfg [FpOptimise sc e] = [optimise cfg (FpOptimise sc e)]
Proof
  simp[stos_pass_def]
QED

Theorem no_opt_decs_unfold:
  no_opt_decs cfg [Dlet loc p e] = [Dlet loc p (no_optimisations cfg e)]
Proof
  simp[no_opt_decs_def]
QED

Theorem no_optimisations_unfold:
  no_optimisations cfg (Fun s e) = Fun s (no_optimisations cfg e)
Proof
  simp[no_optimisations_def]
QED

val local_optThm = REWRITE_CONV [HD, no_optimisations_unfold, no_opt_decs_unfold, stos_pass_optimise, stos_pass_unfold,stos_pass_decs_unfold, theAST_def] (theAST_opt |> concl |> lhs);

val local_opt_run_thm =
    SIMP_RULE std_ss [locationTheory.unknown_loc_def, TypeBase.one_one_of “:ast$exp”, TypeBase.one_one_of “:ast$dec”, TypeBase.one_one_of “:'a list”]
    (ONCE_REWRITE_RULE [local_optThm] theAST_opt);

(*
val benchmarking = false;

val fullProg =
  if benchmarking
  then
    (EVAL (Parse.Term
           ‘(^(theAST_def |> concl |> rhs)) :: (^(theBenchmarkMain_def |> concl |> rhs))’)
     |> concl |> rhs)
  else
    (EVAL (Parse.Term
           ‘[HD (^(theAST_def |> concl |> rhs)); HD ^main]’)
     |> concl |> rhs);

val fullOptProg =
  if benchmarking
  then
    (EVAL (Parse.Term ‘(HD (^(theAST_opt |> concl |> rhs))) :: (^(theBenchmarkMain_def |> concl |> rhs))’)
     |> concl |> rhs)
  else
    (EVAL (Parse.Term
           ‘[HD (^(theAST_opt |> concl |> rhs)); HD ^main]’)
     |> concl |> rhs);

val filename = "theProg.sexp.cml";
val _ = ((write_ast_to_file filename) o rhs o concl) theProg_def;

val filename = "theOptProg.sexp.cml";
val _ = ((write_ast_to_file filename) o rhs o concl) theOptProg_def;
*)

Definition getDeclLetParts_def:
  getDeclLetParts [Dlet loc (Pvar fname) e] =
  let (vars, body) = stripFuns e in
  (fname, vars, body)
End

val (fname, fvars, body) =
  EVAL (Parse.Term ‘getDeclLetParts ^(theOptProg_def |> concl |> rhs)’)
  |> concl |> rhs |> dest_pair
  |> (fn (x,y) => let val (y,z) = dest_pair y in (x,y,z) end)

Definition doppler_opt_real_spec_def:
  doppler_opt_real_spec =
  (λ w1.
   λ w2.
   λ w3.
   case evaluate
     (empty_state with fp_state := empty_state.fp_state with real_sem := T)
     (^doppler_env with v := toRspace (extend_env_with_vars (REVERSE ^fvars) (REVERSE [w1;w2;w3]) ^(doppler_env).v))
   [realify ^body] of
   | (st, Rval [Real r]) => r)
End

Definition doppler_opt_float_spec_def:
  doppler_opt_float_spec =
  (λ w1.
   λ w2.
   λ w3.
   case evaluate empty_state
   (^doppler_env with v := extend_env_with_vars (REVERSE ^fvars) (REVERSE [w1;w2;w3]) ^(doppler_env).v)
   [^body] of
   | (st, Rval [FP_WordTree fp]) => fp)
End

val (_, fvars_before, body_before) =
  EVAL (Parse.Term ‘getDeclLetParts ^(theAST_def |> concl |> rhs)’)
  |> concl |> rhs |> dest_pair
  |> (fn (x,y) => let val (y,z) = dest_pair y in (x,y,z) end)

Definition doppler_opt_float_option_def:
  doppler_opt_float_option w1 w2 w3 =
   case evaluate empty_state
   (^doppler_env with v := extend_env_with_vars (REVERSE ^fvars) (REVERSE [w1;w2;w3]) ^(doppler_env).v)
   [^body] of
   | (st, Rval [FP_WordTree fp]) => if (st = empty_state) then SOME fp else NONE
   | _ => NONE
End

Definition doppler_float_returns_def:
  doppler_float_returns (w1,w2,w3) w ⇔
  ∃ fpOpts st2 fp.
   evaluate (empty_state with fp_state := empty_state.fp_state with <| rws := theOpts.optimisations ; opts := fpOpts; canOpt := FPScope NoOpt |>)
   (^doppler_env with v :=
     extend_env_with_vars (REVERSE ^fvars) (REVERSE [w1;w2;w3]) ^(doppler_env).v)
   [^body_before] = (st2, Rval [FP_WordTree fp]) ∧ compress_word fp = w
End

Theorem doppler_opt_backward_sim:
  ∀ w1 w2 w3 w.
  doppler_opt_float_option w1 w2 w3 = SOME w ⇒
  doppler_float_returns (w1,w2,w3) (compress_word w)
Proof
  simp[doppler_opt_float_option_def, doppler_float_returns_def]
  \\ rpt gen_tac
  \\ ntac 5 (TOP_CASE_TAC \\ fs[])
  \\ strip_tac \\ rveq
  \\ fs[GSYM local_opt_run_thm]
  \\ first_x_assum (mp_then Any assume_tac no_optimisations_eval_sim)
  \\ fs[]
  \\ first_x_assum (qspecl_then [‘NoOpt’, ‘empty_state.fp_state.choices’] assume_tac)
  \\ fs[]
  \\ Cases_on ‘r2’ \\ fs[noopt_sim_def, v_sim_def]
  \\ Cases_on ‘a’ \\ fs[] \\ Cases_on ‘h’ \\ fs[]
  \\ qpat_x_assum `evaluate _ _ _ = _` mp_tac
  \\ qmatch_goalsub_abbrev_tac ‘evaluate emp_upd dEnv [optimise theOpts e_init] = (emp_res, _)’
  \\ strip_tac
  \\ assume_tac (INST_TYPE [“:'a” |-> “:unit”] all_rewrites_corr)
  \\ first_x_assum
       (qspecl_then [‘emp_upd’, ‘emp_res’, ‘dEnv’, ‘theOpts’, ‘[e_init]’, ‘[FP_WordTree f']’] mp_tac)
  \\ simp[is_optimise_correct_def]
  \\ impl_tac
  >- (
   unabbrev_all_tac
   \\ fs[empty_state_def, theOpts_def, extend_conf_def, no_fp_opt_conf_def]
   \\ imp_res_tac evaluatePropsTheory.evaluate_sing \\ fs[])
  \\ rpt strip_tac
  \\ unabbrev_all_tac \\ fs[empty_state_def, semanticPrimitivesTheory.state_component_equality]
  \\ pop_assum mp_tac
  \\ qmatch_goalsub_abbrev_tac ‘evaluate newSt newEnv _ = _’
  \\ strip_tac
  \\ qexists_tac ‘newSt.fp_state.opts’
  \\ unabbrev_all_tac
  \\ fs[theOpts_def, no_fp_opt_conf_def, extend_conf_def,
        config_component_equality]
QED

(** SPECIFICATION THEOREM FOR Doppler **)
Theorem reader_spec:
  4 = LENGTH cl ∧
  UNIT_TYPE () uv ⇒
  app p ^(fetch_v "reader" st)
  [uv]
  (STDIO fs * COMMANDLINE cl)
  (POSTv uv. &(PAIR_TYPE STRING_TYPE (PAIR_TYPE STRING_TYPE STRING_TYPE) (HD(TL cl), (HD (TL (TL cl)), HD (TL (TL (TL cl))))) uv) * STDIO fs)
Proof
  xcf "reader" st
  \\ reverse (Cases_on`STD_streams fs`) >-(fs[STDIO_def] \\ xpull)
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull)
  \\ ‘~ NULL cl’ by fs[wfcl_def,NULL_EQ]
  \\ xlet_auto >- xsimpl
  \\ ‘cl ≠ []’ by (Cases_on ‘cl’ \\ fs[])
  \\ ‘TL cl ≠ []’ by (Cases_on ‘cl’ \\ fs[] \\ Cases_on ‘t’ \\ fs[])
  \\ xlet_auto_spec (SOME hd_spec)
  >- (xsimpl)
  \\ xlet_auto_spec (SOME tl_spec) >- (xsimpl)
  \\ ‘TL (TL cl) ≠ []’
     by (Cases_on ‘cl’ \\ fs[] \\ Cases_on ‘t’ \\ fs[] \\ Cases_on ‘t'’ \\ fs[])
  \\ xlet_auto_spec (SOME hd_spec) >- (xsimpl)
  \\ xlet_auto_spec (SOME tl_spec) >- (xsimpl)
  \\ xlet_auto_spec (SOME tl_spec) >- (xsimpl)
  \\ ‘TL (TL (TL cl)) ≠ []’
     by (Cases_on ‘cl’ \\ fs[] \\ Cases_on ‘t’ \\ fs[] \\ Cases_on ‘t'’ \\ fs[] \\ Cases_on ‘t’ \\ fs[])
  \\ xlet_auto_spec (SOME hd_spec) >- (xsimpl)
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xcon \\ xsimpl
  \\ fs[PAIR_TYPE_def]
QED

val doppler_opt = theAST_opt |> concl |> rhs;

(*
val _ = computeLib.del_funs [sptreeTheory.subspt_def];
val _ = computeLib.add_funs [realTheory.REAL_INV_1OVER,
                             binary_ieeeTheory.float_to_real_def,
                             binary_ieeeTheory.float_tests,
                             sptreeTheory.subspt_eq,
                             sptreeTheory.lookup_def];
*)

val doppler_pre = doppler_pre_def |> concl |> rhs;

Definition doppler_side_def:
  doppler_side w1 w2 w3 =
   (evaluate_fine empty_state
     (^doppler_env with v :=
      extend_env_with_vars (REVERSE ^fvars) (REVERSE [w1;w2;w3]) ^(doppler_env).v)
     [^body] ∧
     (is_precond_sound ^fvars [w1; w2; w3] ^doppler_pre))
End

Definition is_float_string_def:
  is_float_string s w =
  ∃ i. fromString s = SOME i ∧
    0 ≤ i ∧
   w = ((n2w (Num i)):word64)
End

Definition doppler_float_fun_def:
  doppler_float_fun w1 w2 w3 =
    (compress_word (doppler_opt_float_spec w1 w2 w3))
End

Definition doppler_real_fun_def:
  doppler_real_fun w1 w2 w3 =
    (doppler_opt_real_spec w1 w2 w3)
End

Definition doppler_satisfies_error_def:
  doppler_satisfies_error w1 w2 w3 eps =
    (∃ r. doppler_opt_real_spec w1 w2 w3 = r ∧
    real$abs (
      fp64_to_real (compress_word (doppler_opt_float_spec w1 w2 w3)) -
      r) ≤ eps)
End

Theorem doppler_spec:
  ∀ w1 w2 w3 d1 d2 d3.
    doppler_side w1 w2 w3 ∧
    DOUBLE (Fp_const w1) d1 ∧
    DOUBLE (Fp_const w2) d2 ∧
    DOUBLE (Fp_const w3) d3 ⇒
    let result = (doppler_opt_float_option w1 w2 w3) in
      (∀ p.
        app (p:'ffi ffi_proj) ^(fetch_v "doppler" st)
          [d1; d2; d3]
          (emp)
          (POSTv v.
           &DOUBLE_RES result v)) ∧
        doppler_float_returns (w1,w2,w3) (compress_word (THE result)) ∧
      real$abs (fp64_to_real (compress_word (THE result)) - doppler_real_fun w1 w2 w3) ≤ theErrBound
Proof
  rpt gen_tac \\ simp[app_def, doppler_side_def, doppler_satisfies_error_def]
  \\ rpt (disch_then assume_tac)
  \\ simp[app_basic_def]
  \\ rpt (gen_tac ORELSE (disch_then assume_tac)) \\ fs[]
  \\ qpat_x_assum ‘evaluate_fine _ _ _’ mp_tac
  \\ qmatch_goalsub_abbrev_tac ‘evaluate_fine empty_state _ [doppler_body]’
  \\ disch_then assume_tac
  \\ mp_tac errorbounds_AST
  \\ fs[isOkError_def, option_case_eq, pair_case_eq, getErrorbounds_def, stripFuns_def, PULL_EXISTS]
  \\ TOP_CASE_TAC \\ fs[option_case_eq, pair_case_eq]
  \\ TOP_CASE_TAC \\ fs[option_case_eq, pair_case_eq]
  \\ TOP_CASE_TAC \\ fs[option_case_eq, pair_case_eq]
  \\ rpt (gen_tac ORELSE (disch_then assume_tac)) \\ fs[] \\ rveq
  \\ first_assum (mp_then Any mp_tac (INST_TYPE [“:'ffi” |-> “:unit”] CakeML_FloVer_infer_error))
  \\ disch_then (qspec_then ‘empty_state’ mp_tac) \\ fs[]
  \\ disch_then (qspecl_then
                 [‘^doppler_env’,
                  ‘[Short "u"; Short "v"; Short "t"]’,
                  ‘[w1;w2;w3]’,
                  ‘Fun "u" (Fun "v" (Fun "t" (FpOptimise NoOpt e)))’,
                  ‘(FpOptimise NoOpt e)’]  mp_tac)
  \\ fs[]
  \\ rpt (disch_then drule)
  \\ impl_tac >- (unabbrev_all_tac \\ fs[stripFuns_def])
  \\ rpt (disch_then assume_tac) \\ fs[]
  \\ simp[semanticPrimitivesTheory.do_opapp_def, fetch "-" "doppler_v_def"]
  \\ reverse conj_tac
  >- (
   rpt (pop_assum mp_tac) \\ simp[] \\ rpt (disch_then assume_tac)
   \\ rveq
   \\ ‘doppler_opt_float_option w1 w2 w3 = SOME fp’
      by (fs[doppler_opt_float_option_def])
   \\ imp_res_tac doppler_opt_backward_sim
   \\ fs[doppler_real_fun_def, doppler_opt_real_spec_def]
   \\ irule REAL_LE_TRANS \\ asm_exists_tac \\ fs[])
  \\ rpt strip_tac
  \\ Q.REFINE_EXISTS_TAC ‘Val v’
  \\ simp[evaluate_to_heap_def, evaluate_ck_def, terminationTheory.evaluate_def]
  \\ qexists_tac ‘EMPTY’ \\ qexists_tac ‘EMPTY’
  \\ fs[emp_def, set_sepTheory.SPLIT_def, cfHeapsBaseTheory.SPLIT3_def]
  \\ simp[set_sepTheory.SEP_EXISTS]
  \\ qexists_tac ‘emp’ \\ simp[set_sepTheory.STAR_def]
  \\ ntac 2 (qexists_tac ‘EMPTY’)
  \\ fs[emp_def, set_sepTheory.SPLIT_def, cfHeapsBaseTheory.SPLIT3_def]
  \\ simp[set_sepTheory.cond_def]
  \\ rpt strip_tac
  \\ Q.REFINE_EXISTS_TAC ‘Val v’ \\ simp[]
  \\ ntac 2 (qexists_tac ‘EMPTY’) \\ rpt conj_tac \\ TRY (simp[DISJOINT_DEF] \\ NO_TAC)
  \\ qexists_tac ‘emp’ \\ simp[emp_def]
  \\ rpt strip_tac
  \\ Q.REFINE_EXISTS_TAC ‘Val v’ \\ simp[]
  \\ ‘DISJOINT (st2heap p st'') EMPTY’ by (simp[DISJOINT_DEF])
  \\ asm_exists_tac \\ simp[DOUBLE_RES_def]
  \\ rveq \\ simp[doppler_opt_float_option_def]
  \\ first_x_assum (mp_then Any mp_tac (INST_TYPE [“:'a”|->“:unit”, “:'b”|->“:'ffi”] isPureExpList_swap_state))
  \\ disch_then (qspec_then ‘st'' with clock := 0’ mp_tac)
  \\ impl_tac \\ fs[]
  >- (unabbrev_all_tac \\ EVAL_TAC)
  \\ strip_tac \\ qexists_tac ‘0’ \\ fs[extend_env_with_vars_def, DOUBLE_def]
QED

Theorem main_spec:
  ∀ p.
  cl = [fname; cst1s; cst2s; cst3s] ∧
  is_float_string cst1s c1 ∧
  is_float_string cst2s c2 ∧
  is_float_string cst3s c3 ∧
  doppler_side c1 c2 c3 ⇒
  let
    result = doppler_opt_float_option c1 c2 c3
  in
  app p ^(fetch_v "main" st)
    [Conv NONE []]
    (STDIO fs * COMMANDLINE cl)
    (POSTv uv. &UNIT_TYPE () uv *
     STDIO (add_stdout fs (mlint$toString (&w2n (compress_word (THE result))))))
    ∧
    doppler_float_returns (c1,c2,c3) (compress_word (THE result)) ∧
    real$abs (fp64_to_real (compress_word (THE result)) -
      doppler_real_fun c1 c2 c3) ≤ theErrBound
Proof
  simp[] \\ rpt strip_tac
  \\ first_x_assum (mp_then Any assume_tac (SIMP_RULE std_ss [] (INST_TYPE [“:'ffi”|->“:'a”] doppler_spec)))
  >- (
   xcf "main" st
   \\ xlet_auto >- (xcon \\ xsimpl)
   \\ ‘4 = LENGTH cl’ by (rveq \\ fs[])
   \\ rveq
   \\ xlet_auto_spec (SOME reader_spec)
   >- (xsimpl \\ qexists_tac ‘emp’ \\ xsimpl
       \\ qexists_tac ‘fs’ \\ xsimpl)
   \\ xmatch
   \\ fs[PAIR_TYPE_def] \\ reverse conj_tac
   >- (EVAL_TAC \\ fs[])
   \\ rveq \\ fs[is_float_string_def]
   \\ xlet_auto_spec (SOME intToFP_spec)
   >- (xsimpl \\ qexists_tac ‘emp’ \\ xsimpl
       \\ qexists_tac ‘fs’ \\ xsimpl)
   \\ xlet ‘POSTv uv. &(DOUBLE (Fp_const ((n2w (Num i')):word64)) uv) * STDIO fs’
   >- (xapp \\ xsimpl \\ asm_exists_tac \\ fs[])
   \\ xlet ‘POSTv uv. &(DOUBLE (Fp_const ((n2w (Num i'')):word64)) uv) * STDIO fs’
   >- (xapp \\ xsimpl \\ asm_exists_tac \\ fs[])
   \\ rveq
   \\ first_x_assum (qspecl_then [‘uv'’, ‘uv''’, ‘uv'3'’] mp_tac)
   \\ impl_tac \\ fs[] \\ strip_tac
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
  cl = [fname; cst1s; cst2s; cst3s] ∧
  is_float_string cst1s c1 ∧
  is_float_string cst2s c2 ∧
  is_float_string cst3s c3 ∧
  doppler_side c1 c2 c3 ⇒
  whole_prog_spec ^(fetch_v "main" st) cl fs
  NONE
  ((=)
   (add_stdout fs (mlint$toString (&w2n (compress_word (THE (doppler_opt_float_option c1 c2 c3)))))))
  ∧
  doppler_float_returns (c1,c2,c3) (compress_word (THE (doppler_opt_float_option c1 c2 c3))) ∧
  real$abs (fp64_to_real (compress_word (THE (doppler_opt_float_option c1 c2 c3))) -
            doppler_real_fun c1 c2 c3) ≤ theErrBound
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

(** TODO: Below copied from basis_ffiLib.sml because of a bug in subset_basis_st *)

val basis_ffi_const = prim_mk_const{Thy="basis_ffi",Name="basis_ffi"};
val basis_ffi_tm =
  list_mk_comb(basis_ffi_const,
    map mk_var
      (zip ["cl","fs"]
        (#1(strip_fun(type_of basis_ffi_const)))))

local
  val heap_thms = [COMMANDLINE_precond, STDIO_precond];
  val heap_thms2 = [COMMANDLINE_precond, STDIO_precond, RUNTIME_precond];
  val user_thms = ref ([]: thm list);
  fun build_set [] = raise(ERR"subset_basis_st""no STDOUT in precondition")
    | build_set [th] = th
    | build_set (th1::th2::ths) =
        let
          val th = MATCH_MP append_hprop (CONJ th1 th2)
          val th = CONV_RULE(LAND_CONV EVAL)th
          val th = MATCH_MP th TRUTH |> SIMP_RULE (srw_ss()) [UNION_EMPTY]
          val th = (CONV_RULE(RAND_CONV (pred_setLib.UNION_CONV EVAL)) th
          handle _ => th) (* TODO quick fix *)
        in build_set (th::ths) end
in
  fun add_user_heap_thm thm =
      (user_thms := thm :: (!user_thms);
       HOL_MESG ("Adding user heap theorem:\n" ^ thm_to_string thm ^ "\n"))
  val sets_thm2 = build_set heap_thms2;
  val sets2 = rand (concl sets_thm2)
  fun mk_user_sets_thm () = build_set (heap_thms @ (!user_thms))
end

val (whole_prog_spec_thm,sets,sets_thm) =
let
  val sets_thm = mk_user_sets_thm ()
  val sets     = rand (concl sets_thm)
in
  (whole_prog_spec_semantics_prog, sets, sets_thm)
end

(** Build intermediate theorem with SPLIT assumption **)
val th =
  whole_prog_spec_thm
  |> C MATCH_MP (st |> get_Decls_thm |> GEN_ALL |> ISPEC basis_ffi_tm)
  |> SPEC(stringSyntax.fromMLstring name)
  |> CONV_RULE(QUANT_CONV(LAND_CONV(LAND_CONV EVAL THENC SIMP_CONV std_ss [])))
  |> CONV_RULE(HO_REWR_CONV UNWIND_FORALL_THM1)
  |> C HO_MATCH_MP (CONJUNCT1 (UNDISCH_ALL spec))
  |> SIMP_RULE bool_ss [option_case_def, set_sepTheory.SEP_CLAUSES]

val prog_with_snoc = th |> concl |> find_term listSyntax.is_snoc
val prog_rewrite = EVAL prog_with_snoc
val th = PURE_REWRITE_RULE[prog_rewrite] th
val (split,precondh1) = th |> concl |> dest_imp |> #1 |> strip_exists |> #2 |> dest_conj
val precond = rator precondh1
val st = split |> rator |> rand

(*This tactic proves that for a given state, parts_ok holds for the ffi and the basis_proj2*)
val prove_parts_ok_st =
    qmatch_goalsub_abbrev_tac`st.ffi`
    \\ `st.ffi.oracle = basis_ffi_oracle`
    by( simp[Abbr`st`] \\ EVAL_TAC \\ NO_TAC)
    \\ rw[cfStoreTheory.parts_ok_def]
    \\ TRY ( simp[Abbr`st`] \\ EVAL_TAC \\ NO_TAC )
    \\ TRY ( imp_res_tac oracle_parts \\ rfs[] \\ NO_TAC)
    \\ qpat_x_assum`MEM _ basis_proj2`mp_tac
    \\ simp[basis_proj2_def,basis_ffi_part_defs,cfHeapsBaseTheory.mk_proj2_def]
    \\ TRY (qpat_x_assum`_ = SOME _`mp_tac)
    \\ simp[basis_proj1_def,basis_ffi_part_defs,cfHeapsBaseTheory.mk_proj1_def,FUPDATE_LIST_THM]
    \\ rw[] \\ rw[] \\ pairarg_tac \\ fs[FLOOKUP_UPDATE] \\ rw[]
    \\ fs[FAPPLY_FUPDATE_THM,cfHeapsBaseTheory.mk_ffi_next_def]
    \\ TRY PURE_FULL_CASE_TAC
    \\ fs[]
    \\ EVERY (map imp_res_tac (CONJUNCTS basis_ffi_length_thms))
    \\ fs[fs_ffi_no_ffi_div,cl_ffi_no_ffi_div]
    \\ srw_tac[DNF_ss][] \\ simp[basis_ffi_oracle_def];

val SPLIT_thm =
  let
    val to_inst = free_vars sets
    val goal = pred_setSyntax.mk_subset(sets,st)
    val tac = (
          fs[cfStoreTheory.st2heap_def, cfStoreTheory.FFI_part_NOT_IN_store2heap,
             cfStoreTheory.Mem_NOT_IN_ffi2heap, cfStoreTheory.ffi2heap_def]
       \\ qmatch_goalsub_abbrev_tac`parts_ok ffii (basis_proj1,basis_proj2)`
       \\ `parts_ok ffii (basis_proj1,basis_proj2)`
              by (fs[Abbr`ffii`] \\ prove_parts_ok_st)
       \\ fs[Abbr`ffii`]
       \\ EVAL_TAC
       \\ rw[cfAppTheory.store2heap_aux_append_many,INJ_MAP_EQ_IFF,INJ_DEF,FLOOKUP_UPDATE]
       \\ rw[cfStoreTheory.store2heap_aux_def]
       )
    val (subgoals,_) = tac ([],goal)
    fun mk_mapping (x,y) =
      if tmem x to_inst then SOME (x |-> y) else
      if tmem y to_inst then SOME (y |-> x) else NONE
    fun safe_dest_eq tm =
      if boolSyntax.is_eq tm then boolSyntax.dest_eq tm else
      Lib.tryfind boolSyntax.dest_eq (boolSyntax.strip_disj tm)
      handle HOL_ERR _ =>
        raise(ERR"subset_basis_st"("Could not prove heap subgoal: "^(Parse.term_to_string tm)))
    val s =
       List.mapPartial (mk_mapping o safe_dest_eq o #2) subgoals
    val goal' = Term.subst s goal
    val th = prove(goal',tac)
    val th =
        MATCH_MP SPLIT_exists (CONJ (INST s sets_thm) th)
    val length_hyps = mapfilter (assert listSyntax.is_length o lhs) (hyp th)
                   |> map EVAL
  in
    foldl (uncurry PROVE_HYP) th length_hyps
  end;

val semantics_prog_thm =
  MATCH_MP th SPLIT_thm
  |> DISCH_ALL
  |> REWRITE_RULE [AND_IMP_INTRO]
  |> CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV std_ss [LENGTH]))
  |> REWRITE_RULE [GSYM AND_IMP_INTRO]
  |> UNDISCH_ALL

val doppler_prog_tm = rhs (concl prog_rewrite);

val doppler_prog_def = Define`doppler_prog = ^doppler_prog_tm`;

Theorem IMP_SPLIT:
  (P ⇒ (Q1 ∧ Q2)) ⇔ ((P ⇒ Q1) ∧ (P ⇒ Q2))
Proof
  EQ_TAC \\ rpt strip_tac \\ fs[]
QED

val full_semantics_prog_thm =
  LIST_CONJ [
    DISCH_ALL semantics_prog_thm,
    CONJUNCT2 (SIMP_RULE std_ss [IMP_SPLIT] main_whole_prog_spec)
              |> SIMP_RULE std_ss [GSYM IMP_SPLIT]
              |> REWRITE_RULE [CONJ_ASSOC]
              |> ONCE_REWRITE_RULE [CONJ_COMM]
              |> ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO]
              |> ONCE_REWRITE_RULE [CONJ_COMM]
              |> ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO]
              |> ONCE_REWRITE_RULE [CONJ_COMM]
              |> ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO]
              |> ONCE_REWRITE_RULE [CONJ_COMM]
              |> ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO]
  ]
  |> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
  |> SIMP_RULE std_ss [GSYM IMP_SPLIT];

Theorem doppler_semantics =
  full_semantics_prog_thm |> ONCE_REWRITE_RULE[GSYM doppler_prog_def]
  |> DISCH_ALL |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC];

Definition toString_def:
  toString (w:word64) = (mlint$toString:int->mlstring (&((w2n w):num)))
End

Definition CakeML_evaluates_and_prints_def:
  CakeML_evaluates_and_prints (cl,fs,prog) str =
    ∃io_events.
      semantics_prog (init_state (basis_ffi cl fs)) init_env prog
        (Terminate Success io_events) ∧
      extract_fs fs io_events = SOME (add_stdout fs str)
End

Definition init_ok_def:
  init_ok (cl,fs) ⇔ wfcl cl ∧ wfFS fs ∧ STD_streams fs
End

Definition doppler_semantics_side_def:
  doppler_semantics_side (s1,s2,s3) (c1,c2,c3) ⇔
    is_float_string s1 c1 ∧
    is_float_string s2 c2 ∧
    is_float_string s3 c3 ∧
    doppler_side c1 c2 c3
End

Theorem doppler_semantics_final:
  doppler_semantics_side (s1,s2,s3) (c1,c2,c3) ∧ init_ok ([fname;s1;s2;s3],fs) ⇒
  ∃ (w:word64).
    CakeML_evaluates_and_prints ([fname;s1;s2;s3],fs,doppler_prog) (toString w) ∧
    doppler_float_returns (c1,c2,c3) w ∧
    real$abs (fp64_to_real w - doppler_real_fun c1 c2 c3) ≤ theErrBound
Proof
  rpt strip_tac
  \\ fs[init_ok_def, CakeML_evaluates_and_prints_def, doppler_semantics_side_def]
  \\ first_x_assum (mp_then Any mp_tac doppler_semantics)
  \\ rpt (disch_then drule)
  \\ strip_tac \\ fs[]
  \\ first_x_assum (qspecl_then [‘fs’,‘fname’] mp_tac)
  \\ strip_tac \\ rfs[]
  \\ qexists_tac ‘compress_word (THE (doppler_opt_float_option c1 c2 c3))’ \\ fs[]
  \\ asm_exists_tac \\ fs[toString_def, doppler_float_fun_def]
QED

(**
FINAL THEOREM:

Let Doppler be the following program ... using floating-point operations,
let DopplerReal be to_real(Doppler), where to_real syntactically replaces all
floating-point operations by their real-numbered counterparts, and let
DopplerOpt = optimise(Doppler, ids), where optimise syntactically transforms a
floating-point program using our optimisation algorithm with identities ids, and
suppose ids contains only real-valued identities.
Then if there is a real number r such that
real_semantics(DopplerReal) = print(r), then there is a floating-point word w
such that semantics(DopplerOpt) = print(w), and |real(w)-r| ≤ error(DopplerOpt) ≤ the user given error constraint ε
(with respect to DopplerReal), where error uses the FloVer analysis tool to
compute an upper bound on the worst-case roundoff error between DopplerReal and DopplerOpt.

or

Let DopplerReal be the following program ... that uses real-number operations,
let Doppler be floatify(DopplerReal), where floatify syntactically turns all
real-number operations into floating-point operations, and let
DopplerOpt = optimise(Doppler, ids), where optimise syntactically transforms a
floating-point program using our optimisation algorithm with identities ids, and
suppose ids contains only real-valued identities.
Then if there is a real number r such that
real_semantics(DopplerReal) = print(r), then there is a floating-point word w
such that semantics(DopplerOpt) = print(w), and |real(w)-r| < error(DopplerReal),
where error uses the FloVer analysis tool to compute an upper bound on the
worst-case roundoff error between DopplerReal and DopplerOpt.
**)

val _ = export_theory();
