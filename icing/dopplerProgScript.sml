(**
  Icing benchmark input file
  Use this file to run a CakeML AST through the Icing optimizer
**)

(* INCLUDES, do not change those *)
open compilerTheory fromSexpTheory cfTacticsLib ml_translatorLib basis;
open RealIntervalInferenceTheory ErrorIntervalInferenceTheory CertificateCheckerTheory;
open source_to_sourceTheory CakeMLtoFloVerTheory CakeMLtoFloVerProofsTheory;
open machine_ieeeTheory binary_ieeeTheory realTheory realLib RealArith;
open preamble astToSexprLib;

val _ = new_theory "icing_input";

val _ = translation_extends "basisProg";

val doppler_pre =
“(** Precondition **)
 (Let NONE
  (App Opapp
   [Var (Long "Runtime" (Short "assert"));
    (Log And
     (Log And
      (App (FP_cmp FP_LessEqual)
       [App FpFromWord [Lit (Word64 13860109328209412096w)]; Var (Short "u")])
      (App (FP_cmp FP_LessEqual)
       [Var (Short "u"); App FpFromWord [Lit (Word64 4636807660098813952w)]]))
     (Log And
      (Log And
       (App (FP_cmp FP_LessEqual)
        [App FpFromWord [Lit (Word64 4626322717216342016w)]; Var (Short "v")])
       (App (FP_cmp FP_LessEqual)
        [Var (Short "v"); App FpFromWord [Lit (Word64 4671226772094713856w)]]))
      (Log And
       (App (FP_cmp FP_LessEqual)
        [App FpFromWord [Lit (Word64 13852509503838224384w)]; Var (Short "t")])
       (App (FP_cmp FP_LessEqual)
        [Var (Short "t"); App FpFromWord [Lit (Word64 4632233691727265792w)]]))))]))”;

(**
  Define the CakeML source AST as a polyML/HOL4 declaration
**)
val doppler =
“[Dlet unknown_loc (Pvar "doppler")
  (Fun "u" (Fun "v" (Fun "t"
  (** Numerical kernel **)
  (FpOptimise Opt
   (Let (SOME "t1")
    (App (FP_bop FP_Add)
     [
       (App FpFromWord [Lit (Word64 (4644537666646730342w:word64))]);
       (App (FP_bop FP_Mul)
        [
          (App FpFromWord [Lit (Word64 (4603579539098121011w:word64))]);
          Var (Short  "t")
        ])
     ])
    (App (FP_bop FP_Div)
     [
       (App (FP_bop FP_Mul)
        [
          (App (FP_uop FP_Neg)
           [Var (Short "t1")]);
          Var (Short "v")
        ]);
       (App (FP_bop FP_Mul)
        [
          (App (FP_bop FP_Add)
           [Var (Short "t1");
            Var (Short "u")]);
          (App (FP_bop FP_Add)
           [Var (Short "t1");
            Var (Short "u")])
        ])
     ])
   )))))]”

(* SPEC must be stated in terms of word64's, see construction of
   Arrow_doppler theorem below *)
Definition doppler_spec_def:
  doppler_spec =
  (λ u:word64. λ v:word64. λ t:word64.
   let t1 =
   (Fp_bop FP_Add
    (Fp_const (4644537666646730342w:word64))
    (Fp_bop FP_Mul
     (Fp_const (4603579539098121011w:word64))
     (Fp_const t)))
   in
   compress_word (
   (Fp_bop FP_Div
    (Fp_bop FP_Mul
     (Fp_uop FP_Neg t1) (Fp_const v))
    (Fp_bop FP_Mul
     (Fp_bop FP_Add t1 (Fp_const u))
     (Fp_bop FP_Add t1 (Fp_const u))))))
End

Definition theAST_def:
  theAST =
  (** REPLACE AST BELOW THIS LINE **)
  ^doppler
End

val _ = append_prog doppler;

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

val _ = append_prog main;

val st = get_ml_prog_state ();

(** SPECIFICATION THEOREM FOR Doppler **)
Definition DOUBLE_def:
  DOUBLE (d:word64) =
    λ v. ∃ fp. v = FP_WordTree fp ∧ compress_word fp = d
End

(*
val Arrow_doppler=
GEN “a:'a ->v-> bool” (GSYM cfAppTheory.Arrow_eq_app_basic)
|> ISPEC “DOUBLE”
|> GEN “b:'b -> v -> bool”
|> ISPEC “DOUBLE --> (DOUBLE --> DOUBLE)”
|> GEN “fv:v”
|> SPEC (fetch_v "doppler" st)
|> GEN “f:word64->word64->word64->word64”
|> SPEC “doppler_spec”
|> GEN “p:'c ffi_proj”
|> ISPEC “p:'ffi ffi_proj”
|> EQ_IMP_RULE
|> (fn (t1,t2) => (SIMP_RULE std_ss [PULL_FORALL] t1, SIMP_RULE std_ss [PULL_FORALL] t2));
*)

Theorem doppler_spec:
  DOUBLE w1 d1 ∧
  DOUBLE w2 d2 ∧
  DOUBLE w3 d3 ⇒
  app (p:'ffi ffi_proj) ^(fetch_v "doppler" st)
  [d1; d2; d3]
  (emp)
  (POSTv v. &(DOUBLE (doppler_spec w1 w2 w3) v))
Proof
  rpt strip_tac \\ simp[app_def]
  \\ simp[app_basic_def]
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
  \\ asm_exists_tac \\ fs[]
  \\ cheat
QED

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

Theorem main_spec:
  app (p:'ffi ffi_proj) ^(fetch_v "main" st)
    [Conv NONE []]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
       STDIO (add_stdout fs (mlint$toString (&w2n (doppler_spec 4607182418800017408w 4607182418800017408w 4607182418800017408w)))))
Proof
  xcf "main" st
  \\ xlet ‘POSTv v. &(DOUBLE 4607182418800017408w v) * STDIO fs’
  >- (cheat)
  \\ xlet ‘POSTv v. &(DOUBLE 4607182418800017408w v) * STDIO fs’
  >- (cheat)
  \\ xlet ‘POSTv v. &(DOUBLE 4607182418800017408w v) * STDIO fs’
  >- (cheat)
  \\ xlet_auto
  >- (xsimpl)
  \\ rename1 ‘DOUBLE dRes v'3'’
  \\ fs[DOUBLE_def]
  \\ xlet ‘POSTv v. &WORD dRes v * STDIO fs’
  >- (
   fs[cf_fptoword_def, cfHeapsTheory.local_def, cfNormaliseTheory.exp2v_def,
         cfTheory.app_fptoword_def]
   \\ rpt strip_tac
   \\ fs[WORD_def]
   \\ qexists_tac ‘STDIO fs’ \\ qexists_tac ‘emp’
   \\ simp[]
   \\ qexists_tac ‘POSTv v. &WORD dRes v * STDIO fs’ \\ rpt conj_tac
   >- (
    simp[set_sepTheory.STAR_def] \\ qexists_tac ‘h’ \\ qexists_tac ‘EMPTY’
    \\ fs[SPLIT_def, emp_def])
   >- (
    fs[DOUBLE_def, set_sepTheory.SEP_IMP_def]
    \\ rpt strip_tac \\ fs[set_sepTheory.cond_def, set_sepTheory.STAR_def]
    >- (qexists_tac ‘s’ \\ fs[SPLIT_def])
    \\ xsimpl)
   \\ xsimpl \\ rveq \\ strip_tac \\ fs[WORD_def, DOUBLE_def])
  \\ xapp \\ xsimpl
  \\ qexists_tac ‘emp’ \\ qexists_tac ‘dRes’ \\ qexists_tac ‘fs’
  \\ fs[] \\ conj_tac
  \\ xsimpl \\ rpt strip_tac
  \\ qexists_tac ‘dRes’ \\ xsimpl
QED

Theorem main_whole_prog_spec:
   whole_prog_spec ^(fetch_v "main" st) cl fs NONE
    ((=) (add_stdout fs (mlint$toString (&w2n (doppler_spec 4607182418800017408w 4607182418800017408w 4607182418800017408w)))))
Proof
  rw[whole_prog_spec_def]
  \\ qmatch_goalsub_abbrev_tac`fs1 = _ with numchars := _`
  \\ qexists_tac`fs1`
  \\ simp[Abbr`fs1`,GSYM add_stdo_with_numchars,with_same_numchars]
  \\ match_mp_tac (MP_CANON (MATCH_MP app_wgframe main_spec))
  \\ xsimpl
QED

val spec = main_whole_prog_spec;
val name = "main";

val (call_thm_hello, doppler_prog_tm) = whole_prog_thm st name spec;
val doppler_prog_def = Define`doppler_prog = ^doppler_prog_tm`;

val main_semantics = save_thm("main_semantics",
  call_thm_hello |> ONCE_REWRITE_RULE[GSYM doppler_prog_def]
  |> DISCH_ALL |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]);

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

(** Optimizations to be applied by Icing **)
Definition theOpts_def:
  theOpts = extend_conf no_fp_opt_conf
  [
    (Binop FP_Add (Var 0) (Binop FP_Mul (Var 1) (Var 2)),
     Binop FP_Add (Binop FP_Mul (Var 1) (Var 2)) (Var 0))
    ;
    (Binop FP_Add (Binop FP_Mul (Var 0) (Var 1)) (Var 2),
    Terop FP_Fma (Var 2) (Var 0) (Var 1))
    (*
      (* WRITE OPTIMISATIONS HERE AS ; SEPARATED LIST *)
    (Binop FP_Mul (Binop FP_Add (Var 0) (Var 1)) (Binop FP_Add (Var 0) (Var 1)),
     Binop FP_Mul (Var 0) (Binop FP_Add (Var 1) (Var 1)));
    (Binop FP_Mul (Var 0) (Binop FP_Add (Var 1) (Var 2)),
     Terop FP_Fma (Var 0) (Var 1) (Var 2)) *)
  ]
End

(** The code below stores in theorem theAST_opt the optimized version of the AST
    from above and in errorbounds_AST the inferred FloVer roundoff error bounds
 **)
Theorem theAST_opt =
  EVAL
    (Parse.Term ‘
      (source_to_source$no_opt_decs theOpts (source_to_source$stos_pass_decs theOpts
       [theAST]))’);

Theorem theAST_opt_eval =
GEN_ALL (EVAL (Parse.Term ‘evaluate_decs st env ^(theAST_opt |> concl |> rhs)’));

Definition theErrBound_def:
  theErrBound = inv (2 pow (10))
End

val benchmarking = false;

val fullProg =
  if benchmarking
  then
    (EVAL (Parse.Term
           ‘(^(theAST_def |> concl |> rhs)) :: (^(theBenchmarkMain_def |> concl |> rhs))’)
     |> concl |> rhs)
  else
    (EVAL (Parse.Term
           ‘[(^(theAST_def |> concl |> rhs)); HD (^(theMain_def |> concl |> rhs))]’)
     |> concl |> rhs);

val fullOptProg =
  if benchmarking
  then
    (EVAL (Parse.Term ‘(HD (^(theAST_opt |> concl |> rhs))) :: (^(theBenchmarkMain_def |> concl |> rhs))’)
     |> concl |> rhs)
  else
    (EVAL (Parse.Term
           ‘[HD (^(theAST_opt |> concl |> rhs)); HD (^(theMain_def |> concl |> rhs))]’)
     |> concl |> rhs);

Definition theProg_def:
  theProg = ^fullProg
End

Definition theOptProg_def:
  theOptProg = ^fullOptProg
End

val filename = "theProg.sexp.cml";
val _ = ((write_ast_to_file filename) o rhs o concl) theProg_def;

val filename = "theOptProg.sexp.cml";
val _ = ((write_ast_to_file filename) o rhs o concl) theOptProg_def;

val _ = computeLib.del_funs [sptreeTheory.subspt_def];
val _ = computeLib.add_funs [realTheory.REAL_INV_1OVER,
                             binary_ieeeTheory.float_to_real_def,
                             binary_ieeeTheory.float_tests,
                             sptreeTheory.subspt_eq,
                             sptreeTheory.lookup_def];

Theorem errorbounds_AST =
  EVAL (Parse.Term
      ‘isOkError (HD ^(concl theAST_opt |> rhs)) theErrBound’);

(** TODO: Final Theorem **)
(**
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

Theorem evaluate_fpfromword_const =
  GEN_ALL (EVAL “evaluate st env [App FpFromWord [Lit (Word64 w)]]”);

Theorem doppler_kernel_main_thm:
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ⇒
  ∃io_events1 io_events2 (w:word64) (r:real).
  (* TODO: Extract function/predicate *)
    semantics_prog (init_state (basis_ffi cl fs)) init_env theOptProg
      (Terminate Success io_events1) ∧
    extract_fs fs io_events1 = SOME (add_stdout fs (word64_to_string w)) ∧
  (* until here *)
    semantics_prog (init_state (basis_ffi cl fs)) (toRealEnv init_env)
      (realify theProg) (Terminate Success io_events2) ∧
    extract_fs fs io_events2 = SOME (add_stdout fs (real_to_string r)) ∧
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
  \\ qspecl_then [‘stA’, ‘stA’,‘envA’, ‘prepareGamma floverVars’, ‘P’, ‘theBounds’, ‘theAST’, ‘ids’, ‘cake_P’, ‘f’, ‘floverVars’, ‘varMap’, ‘freshId’, ‘freshId'’, ‘theIds’, ‘theCmd’, ‘dVars’] mp_tac CakeML_FloVer_infer_error
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

val _ = export_theory();
