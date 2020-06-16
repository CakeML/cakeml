(**
  Doppler program proofs
**)

open compilerTheory fromSexpTheory cfTacticsLib ml_translatorLib basis;
open RealIntervalInferenceTheory ErrorIntervalInferenceTheory CertificateCheckerTheory;
open source_to_sourceTheory CakeMLtoFloVerTheory CakeMLtoFloVerProofsTheory dopplerProgCompTheory;
open machine_ieeeTheory binary_ieeeTheory realTheory realLib RealArith;
open fromSexpTheory basis basis_ffiTheory cfHeapsBaseTheory;
open preamble astToSexprLib;

val _ = new_theory "dopplerProofs";

val _ = translation_extends "basisProg";

val printer =
  “[Dlet unknown_loc (Pvar "printer")
    (Fun "x"
     (Let (SOME "z")
      (App Opapp [
         Var (Long "Word64" (Short "toInt"));
         Var (Short "x")])
      (Let (SOME "y")
       (App Opapp [
          Var (Long "Int" (Short "toString"));
          Var (Short "z")])
       (App Opapp [
          Var (Long "TextIO" (Short "print"));
          Var (Short "y")]))))]”;

val _ = append_prog printer;

val reader =
“[Dlet unknown_loc (Pvar "reader")
   (Fun "x"
    (Let (SOME "inp")
     (App Opapp [ Var (Long "TextIO" (Short "stdIn")); Con NONE []])
     ( (Let (SOME "w1")
         (App Opapp [
            Var (Long "TextIO" (Short "inputLine"));
            Var (Short "inp")])
         (App Opapp [
            Var (Long "Double" (Short "fromString"));
            Var (Short "w1")])))))]”

val _ = append_prog reader;

val main =
“[Dlet unknown_loc (Pvar "main")
  (Fun "a"
   (Let (SOME "d1")
    (App FpFromWord [Lit (Word64 4607182418800017408w)])
    (Let (SOME "d2")
     (App FpFromWord [Lit (Word64 4607182418800017408w)])
     (Let (SOME "d3")
      (App FpFromWord [Lit (Word64 4607182418800017408w)])
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
           Var (Short "y")])))))))]”;

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

Definition doppler_opt_real_spec_def:
  doppler_opt_real_spec decl =
  let (fname, fvars, body) = getDeclLetParts decl in
  (λ w1.
   λ w2.
   λ w3.
   case evaluate
     (empty_state with fp_state := empty_state.fp_state with real_sem := T)
     (^doppler_env with v := toRspace (extend_env_with_vars (REVERSE fvars) (REVERSE [w1;w2;w3]) ^(doppler_env).v))
   [realify body] of
   | (st, Rval [Real r]) => r)
End

Definition doppler_opt_float_spec_def:
  doppler_opt_float_spec decl =
  let (fname, fvars, body) = getDeclLetParts decl in
  (λ w1.
   λ w2.
   λ w3.
   case evaluate empty_state
   (^doppler_env with v := extend_env_with_vars (REVERSE fvars) (REVERSE [w1;w2;w3]) ^(doppler_env).v)
   [body] of
   | (st, Rval [FP_WordTree fp]) => fp)
End

(** SPECIFICATION THEOREM FOR Doppler **)
Definition DOUBLE_def:
  DOUBLE (d:fp_word_val) =
  λ v. v = FP_WordTree d
End

(*
Definition DOUBLE_APPROX_def:
  DOUBLE_APPROX (r:real) (fp:fp_word_val) (err:real) =
  λ v.
  case v of
  |FP_WordTree fp2 => (compress_word fp2 = compress_word fp ∧
                      real$abs(fp64_to_real (compress_word fp) - r) ≤ err)
  | _ => F
End
*)

val (fname, fvars, body) =
  EVAL (Parse.Term ‘getDeclLetParts ^(theOptProg_def |> concl |> rhs)’)
  |> concl |> rhs |> dest_pair
  |> (fn (x,y) => let val (y,z) = dest_pair y in (x,y,z) end)

Theorem printer_spec:
  WORD (w:word64) v ⇒
  app (p:'ffi ffi_proj) ^(fetch_v "printer" st)
    [v]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv * STDIO (add_stdout fs (mlint$toString (&w2n w))))
Proof
  xcf "printer" st
  \\ xlet_auto
  >- (xsimpl)
  \\ xlet_auto
  >- (xsimpl)
  \\ xapp \\ xsimpl
QED

(**  INSTREAM fd fdv ∧ IS_SOME (get_file_content fs fd) ∧ get_mode fs fd = SOME ReadMode
   ⇒
   app (p:'ffi ffi_proj) TextIO_inputLine_v [fdv]
     (STDIO fs)
     (POSTv sov.
       &OPTION_TYPE STRING_TYPE (OPTION_MAP implode (lineFD fs fd)) sov *
       STDIO (lineForwardFD fs fd))
Theorem reader_spec:
app (p:ffi ffi_proj) ^(fetch_v "reader" st)
  [Conv NONE []]
  (STDIO fs)
  (POSTv uv. &(DOUBLE d uv))
Proof
  xcf "reader" st
  \\ xlet_auto
  \\ assume_tac TextIOProofTheory.INSTREAM_stdin
  \\ xlet ‘POSTv sov.
       &OPTION_TYPE STRING_TYPE (OPTION_MAP implode (lineFD fs 0)) sov *
       STDIO (lineForwardFD fs 0)’
  \\ xlet_auto
  \\ xlet ‘POSTv uv. INSTREAM 0 stdin_v uv’
  \\ xlet_auto
**)

Theorem cf_fpfromword:
  ∀ env.
  cf_fpfromword (Lit (Word64 w)) env (STDIO fs)
  (POSTv v. &DOUBLE (Fp_const w) v * STDIO fs)
Proof
  rpt strip_tac
  \\ qmatch_goalsub_abbrev_tac ‘cf_fpfromword _ _ _ Post’
  \\ fs[cf_fpfromword_def, cfHeapsTheory.local_def, cfNormaliseTheory.exp2v_def,
         cfTheory.app_fpfromword_def]
  \\ rpt strip_tac
  \\ qexists_tac ‘STDIO fs’ \\ qexists_tac ‘emp’
  \\ qexists_tac ‘Post’ \\ rpt conj_tac \\ unabbrev_all_tac \\ xsimpl
   >- (
    simp[set_sepTheory.STAR_def] \\ qexists_tac ‘h’ \\ qexists_tac ‘EMPTY’
    \\ fs[SPLIT_def, emp_def])
   \\ fs[DOUBLE_def, set_sepTheory.SEP_IMP_def]
   \\ rpt strip_tac \\ fs[set_sepTheory.cond_def, set_sepTheory.STAR_def]
   \\ unabbrev_all_tac \\ fs[SPLIT_def]
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

Definition doppler_float_result_def:
  doppler_float_result w1 w2 w3 =
    (compress_word (doppler_opt_float_spec ^doppler_opt w1 w2 w3))
End

Definition doppler_real_result_def:
  doppler_real_result w1 w2 w3 =
    (doppler_opt_real_spec ^doppler_opt w1 w2 w3)
End

Definition doppler_satisfies_error_def:
  doppler_satisfies_error w1 w2 w3 eps =
    (∃ r. doppler_opt_real_spec ^doppler_opt w1 w2 w3 = r ∧
    real$abs (
      fp64_to_real (compress_word (doppler_opt_float_spec ^doppler_opt w1 w2 w3)) -
      r) ≤ eps)
End

Theorem doppler_spec:
  doppler_side w1 w2 w3 ∧
  DOUBLE (Fp_const w1) d1 ∧
  DOUBLE (Fp_const w2) d2 ∧
  DOUBLE (Fp_const w3) d3 ⇒
  let theResult = (doppler_opt_float_spec ^doppler_opt w1 w2 w3) in
  app (p:'ffi ffi_proj) ^(fetch_v "doppler" st)
    [d1; d2; d3]
    (emp)
    (POSTv v.
     &DOUBLE theResult v) ∧
  real$abs (fp64_to_real (doppler_float_result w1 w2 w3) - doppler_real_result w1 w2 w3) ≤ theErrBound
Proof
  rpt gen_tac \\ simp[app_def, doppler_side_def, doppler_real_result_def, doppler_float_result_def]
  \\ rpt (disch_then assume_tac)
  \\ simp[app_basic_def, getDeclLetParts_def, stripFuns_def, PULL_FORALL]
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
                 [‘merge_env dopplerProofs_env_0 init_env’,
                  ‘[Short "u"; Short "v"; Short "t"]’,
                  ‘[w1;w2;w3]’,
                  ‘Fun "u" (Fun "v" (Fun "t" (FpOptimise NoOpt e)))’,
                  ‘(FpOptimise NoOpt e)’]  mp_tac)
  \\ fs[]
  \\ rpt (disch_then drule)
  \\ impl_tac >- (unabbrev_all_tac \\ fs[stripFuns_def])
  \\ rpt (disch_then assume_tac) \\ fs[]
  \\ reverse conj_tac
  >- (
   fs[doppler_opt_float_spec_def, doppler_opt_real_spec_def]
   \\ simp[getDeclLetParts_def] \\ rewrite_tac[stripFuns_def]
   \\ rpt (pop_assum mp_tac)
   \\ simp[]
   \\ rpt strip_tac \\ irule REAL_LE_TRANS \\ asm_exists_tac \\ fs[])
  \\ rpt strip_tac
  \\ simp[semanticPrimitivesTheory.do_opapp_def, fetch "-" "doppler_v_def"]
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
  \\ asm_exists_tac \\ simp[DOUBLE_def]
  \\ mp_tac (GEN_ALL (SIMP_RULE std_ss [ml_progTheory.eval_rel_def] evaluate_empty_state_IMP))
  \\ disch_then (qspecl_then [‘FP_WordTree fp2’, ‘st''’, ‘st''.refs’, ‘FpOptimise NoOpt e’] mp_tac)
  \\ fs[semanticPrimitivesTheory.state_component_equality, empty_state_def, PULL_EXISTS]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate _ dEnv _ = _’
  \\ disch_then (qspecl_then [‘dEnv’, ‘0’, ‘0’] mp_tac)
  \\ impl_tac
  >- (fs[] \\ cheat (* FIX CakeML_FloVer_thm *))
  \\ strip_tac \\ qexists_tac ‘ck1’
  \\ fs[doppler_opt_float_spec_def, getDeclLetParts_def, stripFuns_def, empty_state_def]
  \\ fs[cfStoreTheory.st2heap_def]
  \\ cheat (* FIXME: Minor ref juggling *)
QED

Theorem main_spec:
  ∀ p.
  doppler_side 4607182418800017408w 4607182418800017408w 4607182418800017408w ⇒
  app (p:'ffi ffi_proj) ^(fetch_v "main" st)
    [Conv NONE []]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
     STDIO (add_stdout fs (mlint$toString (&w2n (compress_word (doppler_opt_float_spec ^doppler_opt 4607182418800017408w 4607182418800017408w 4607182418800017408w))))))
    ∧
    real$abs (fp64_to_real (doppler_float_result 4607182418800017408w 4607182418800017408w 4607182418800017408w) - doppler_real_result 4607182418800017408w 4607182418800017408w 4607182418800017408w) ≤ theErrBound
Proof
  rpt strip_tac
  \\ first_x_assum (mp_then Any assume_tac (SIMP_RULE std_ss [] doppler_spec))
  >- (
   xcf "main" st
   \\ xlet ‘POSTv v. &(DOUBLE (Fp_const 4607182418800017408w) v) * STDIO fs’
   >- (irule cf_fpfromword)
   \\ xlet ‘POSTv v. &(DOUBLE (Fp_const 4607182418800017408w) v) * STDIO fs’
   >- (irule cf_fpfromword)
   \\ xlet ‘POSTv v. &(DOUBLE (Fp_const 4607182418800017408w) v) * STDIO fs’
   >- (irule cf_fpfromword)
   \\ first_x_assum (qspecl_then [‘p’, ‘v''’, ‘v'’, ‘v’] mp_tac)
   \\ impl_tac \\ fs[] \\ strip_tac
   \\ xlet_auto >- xsimpl
   \\ fs[DOUBLE_def]
   \\ Cases_on ‘v'3'’ \\ fs[]
   \\ xlet ‘POSTv v. &WORD (compress_word f) v * STDIO fs’
   >- (
    fs[cf_fptoword_def, cfHeapsTheory.local_def, cfNormaliseTheory.exp2v_def,
       cfTheory.app_fptoword_def]
    \\ rpt strip_tac
    \\ fs[WORD_def]
    \\ qexists_tac ‘STDIO fs’ \\ qexists_tac ‘emp’
    \\ simp[]
    \\ qexists_tac ‘POSTv v. &WORD (compress_word f) v * STDIO fs’ \\ rpt conj_tac
    >- (
     simp[set_sepTheory.STAR_def] \\ qexists_tac ‘h’ \\ qexists_tac ‘EMPTY’
     \\ fs[SPLIT_def, emp_def])
    >- (
     fs[DOUBLE_def, set_sepTheory.SEP_IMP_def]
     \\ rpt strip_tac \\ fs[set_sepTheory.cond_def, set_sepTheory.STAR_def]
     >- (qexists_tac ‘s’ \\ fs[SPLIT_def])
     \\ xsimpl)
    \\ xsimpl \\ rveq \\ strip_tac \\ fs[WORD_def, DOUBLE_def])
   \\ xapp \\ xsimpl)
  \\ fs[DOUBLE_def]
QED

Definition u_val_def:
  u_val = 4607182418800017408w
End

Definition v_val_def:
  v_val = 4607182418800017408w
End

Definition t_val_def:
  t_val = 4607182418800017408w
End

Theorem main_whole_prog_spec:
  doppler_side u_val v_val t_val ⇒
  whole_prog_spec ^(fetch_v "main" st) cl fs
  NONE
  ((=)
   (add_stdout fs (mlint$toString (&w2n (compress_word (doppler_opt_float_spec ^doppler_opt u_val v_val t_val))))))
  ∧
    real$abs (fp64_to_real (doppler_float_result u_val v_val t_val) - doppler_real_result u_val v_val t_val) ≤ theErrBound
Proof
  simp[whole_prog_spec_def, u_val_def, v_val_def, t_val_def]
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
    CONJUNCT2 (SIMP_RULE std_ss [IMP_SPLIT] main_whole_prog_spec) |> ONCE_REWRITE_RULE [CONJ_COMM]
  ]
  |> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
  |> SIMP_RULE std_ss [GSYM IMP_SPLIT];

Theorem doppler_semantics =
  full_semantics_prog_thm |> ONCE_REWRITE_RULE[GSYM doppler_prog_def]
  |> DISCH_ALL |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC];

Theorem doppler_semantics_final:
  doppler_side u_val v_val t_val ⇒
     (wfcl cl ∧ wfFS fs ∧ STD_streams fs ⇒
      ∃io_events (w:word64).
          semantics_prog (init_state (basis_ffi cl fs)) init_env doppler_prog
            (Terminate Success io_events) ∧
          extract_fs fs io_events =
          SOME
            (add_stdout fs (toString:int->mlstring (&((w2n w):num)))) ∧
     doppler_float_result u_val v_val t_val = w) ∧
     real$abs (fp64_to_real (doppler_float_result u_val v_val t_val) - doppler_real_result u_val v_val t_val) ≤ theErrBound
Proof
  rpt strip_tac
  \\ imp_res_tac doppler_semantics \\ fs[]
  \\ asm_exists_tac \\ fs[doppler_float_result_def]
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

(**
Definition semantics_adds_to_stdout_def:
  semantics_adds_to_stdout cl fs prog str =
    ∃ io_events.
      semantics_prog (init_state (basis_ffi cl fs)) init_env prog
        (Terminate Success io_events) ∧
      extract_fs fs io_events = SOME (add_stdout fs str)
End

Theorem doppler_kernel_main_thm:
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ⇒
  ∃ (w:word64) (r:real).
    semantics_adds_to_stdout cl fs theOptProg
      (word64_to_string w) ∧
    semantics_adds_to_stdout cl fs (realify theProg)
      (real_to_string r) ∧
    real$abs(fp64_to_real w - r) ≤ theErrBound
Proof
  rpt strip_tac
  (* TODO: By computation above... *)
  \\ assume_tac (Q.prove (‘isOkError theAST theErrBound = SOME T’, cheat))
  \\ simp[Once theOptProg_def]
  \\ simp[Once semanticsTheory.semantics_prog_def,
          semanticsTheory.evaluate_prog_with_clock_def,
          Once evaluatePropsTheory.evaluate_decs_cons]
  (* Rewrite with eval theorem *)
  \\ simp[Once theAST_opt_eval]
  \\ simp[Once semanticPrimitivesTheory.extend_dec_env_def]
  \\ simp[ml_progTheory.init_state_def]
  \\ simp[terminationTheory.evaluate_decs_def]
  \\ simp[ALL_DISTINCT, astTheory.pat_bindings_def]
  \\ simp[Once terminationTheory.evaluate_def]
  \\ simp[Once terminationTheory.evaluate_def]
  \\ simp[astTheory.getOpClass_def]
  \\ simp[Once evaluatePropsTheory.evaluate_cons, evaluate_fpfromword_const]
  \\ simp[Once terminationTheory.evaluate_def]
  \\ simp[astTheory.getOpClass_def, Once evaluatePropsTheory.evaluate_cons, evaluate_fpfromword_const]
  \\ simp[Once terminationTheory.evaluate_def]
  \\ simp[astTheory.getOpClass_def, Once evaluatePropsTheory.evaluate_cons, evaluate_fpfromword_const]
  \\ simp[Once terminationTheory.evaluate_def]
  \\ qmatch_goalsub_abbrev_tac ‘<| v := Bind [("doppler", Closure init_env "u" doppler_body)] []; c := Bind [] []|>’
  \\ simp[ml_progTheory.nsLookup_nsAppend_Short, namespaceTheory.nsLookup_def]
  \\ simp[semanticPrimitivesTheory.do_opapp_def]
  \\ fs[GSYM PULL_EXISTS]
  \\ simp[PULL_EXISTS]
  \\ qexists_tac ‘5’ \\ fs[evaluateTheory.dec_clock_def]
  \\ unabbrev_all_tac \\ simp[Once terminationTheory.evaluate_def]
  \\ simp[Once terminationTheory.evaluate_def]
  \\ qmatch_goalsub_abbrev_tac ‘Let NONE (App Opapp [Var (Long "Runtime" (Short "assert")); doppler_pre ]) _’
  \\ simp[Once terminationTheory.evaluate_def]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate stA envA [App Opapp [Var (Long "Runtime" (Short "assert")); doppler_pre]]’
  \\ ‘evaluate stA envA [App Opapp [Var (Long "Runtime" (Short "assert")); doppler_pre]] = (dec_clock stA, Rval [Conv NONE []])’
     by (cheat)
  \\ fs[]
  \\ simp[Once terminationTheory.evaluate_def]
  \\ unabbrev_all_tac \\ fs[evaluateTheory.dec_clock_def]
  \\ qmatch_goalsub_abbrev_tac ‘combine_dec_result <| v := Bind [doppler_clos] _; c := _ |>’
  \\ qmatch_goalsub_abbrev_tac ‘evaluate stA envA [doppler_body]’

  \\ fs[isOkError_def, option_case_eq, pair_case_eq, getErrorbounds_def]
  \\ rveq
  \\ qspecl_then [‘stA’, ‘stA’,‘envA’, ‘prepareGamma floverVars’, ‘P’, ‘theBounds’,
                  ‘theAST’, ‘ids’, ‘cake_P’, ‘f’, ‘floverVars’, ‘varMap’,
                  ‘freshId’, ‘freshId'’, ‘theIds’, ‘theCmd’, ‘dVars’]
                 mp_tac CakeML_FloVer_infer_error
  \\ impl_tac \\ fs[]
  >- (
   rpt conj_tac
   >- (cheat) (* TODO: Should become a different assumption *)
   >- (cheat) (* Same as above *)
   >- (cheat) (* reword to :st.fp_state.canOpt ≠ FPScope Opt *)
   >- (cheat) (* Assumption *)
   >- (cheat) (* Lemma *)
   >- (cheat) (* Assumption? *)
   )
  \\ strip_tac
  \\ ‘doppler_body = f’ by (cheat)
  \\ fs[]
  \\

       TextIOProofTheory.print_spec
       IntProofTheory.toString_spec



QED
*)

val _ = export_theory();
