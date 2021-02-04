(*
  Lib to prove examples
*)
structure exampleLib =
struct
  open astTheory cfTacticsLib ml_translatorLib;
  open basis_ffiTheory cfHeapsBaseTheory basis;
  open FloverMapTheory RealIntervalInferenceTheory ErrorIntervalInferenceTheory CertificateCheckerTheory;
  open floatToRealProofsTheory source_to_sourceTheory CakeMLtoFloVerTheory cfSupportTheory optPlannerTheory;
  open machine_ieeeTheory binary_ieeeTheory realTheory realLib RealArith;

  fun flatMap (ll:'a list list) =
    case ll of [] => []
    | l1 :: ls => l1 @ flatMap ls

  fun dedup l =
    case l of
    [] => []
    | l1::ls =>
        let val lclean = dedup ls in
          if (List.exists (fn x => x = l1) lclean)
          then lclean
          else l1::lclean
        end;

  val iter_code = process_topdecs ‘
    fun iter n s f =
      if (n = 0) then s else iter (n-1) (f s) f;’

  val iter_count = “10000000:int”

  val main1 =
    “[Dlet unknown_loc (Pvar "main")
      (Fun "a"
       (Let (SOME "u") (Con NONE [])
        (Let (SOME "strArgs")
         (App Opapp [Var (Short "reader1"); Var (Short "u")])
         (Mat (Var (Short "strArgs"))
          [(Pvar "d1s",
            (Let (SOME "d1")
             (App Opapp [Var (Short "intToFP"); Var (Short "d1s")])
                (Let (SOME "x" )
                  (App Opapp [Var (Short "doppler"); Var (Short "d1")])
                (Let (SOME "y")
                 (App FpToWord [Var (Short "x")])
                 (App Opapp [
                     Var (Short "printer");
                     Var (Short "y")])))))]))))]”;

  val main2 =
    “[Dlet unknown_loc (Pvar "main")
      (Fun "a"
       (Let (SOME "u") (Con NONE [])
        (Let (SOME "strArgs")
         (App Opapp [Var (Short "reader2"); Var (Short "u")])
         (Mat (Var (Short "strArgs"))
          [(Pcon NONE [Pvar "d1s"; Pvar "d2s"],
            (Let (SOME "d1")
             (App Opapp [Var (Short "intToFP"); Var (Short "d1s")])
             (Let (SOME "d2")
              (App Opapp [Var (Short "intToFP"); Var (Short "d2s")])
                (Let (SOME "x" )
                  (App Opapp [
                          App Opapp [Var (Short "doppler"); Var (Short "d1")];
                        Va  r (Short "d2")])
                (Let (SOME "y")
                 (App FpToWord [Var (Short "x")])
                 (App Opapp [
                     Var (Short "printer");
                     Var (Short "y")]))))))]))))]”;

  val main3 =
    “[Dlet unknown_loc (Pvar "main")
      (Fun "a"
       (Let (SOME "u") (Con NONE [])
        (Let (SOME "strArgs")
         (App Opapp [Var (Short "reader3"); Var (Short "u")])
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

    val main4 =
  “[Dlet unknown_loc (Pvar "main")
    (Fun "a"
     (Let (SOME "u") (Con NONE [])
     (Let (SOME "strArgs")
      (App Opapp [Var (Short "reader4"); Var (Short "u")])
      (Mat (Var (Short "strArgs"))
       [(Pcon NONE [Pvar "d1s"; Pcon NONE [Pvar "d2s"; Pcon NONE [Pvar "d3s"; Pvar "d4s"]]]),
         (Let (SOME "d1")
          (App Opapp [Var (Short "intToFP"); Var (Short "d1s")])
          (Let (SOME "d2")
           (App Opapp [Var (Short "intToFP"); Var (Short "d2s")])
           (Let (SOME "d3")
            (App Opapp [Var (Short "intToFP"); Var (Short "d3s")])
            (Let (SOME "d4")
             (App Opapp [Var (Short "intToFP"); Var (Short "d4s")])
             (Let (SOME "x" )
              (App Opapp [
                 App Opapp [
                   App Opapp [
                     App Opapp [Var (Short "nn1Layer"); Var (Short "d1")];
                     Var (Short "d2")];
                   Var (Short "d3")];
                 Var (Short "d4")])
             (Let (SOME "y")
              (App FpToWord [Var (Short "x")])
              (App Opapp [
                 Var (Short "printer");
                 Var (Short "y")])))))))]))))]”;

  val call1_code = Parse.Term ‘
    [Dlet unknown_loc (Pvar "it")
     (Let (SOME "u") (App FpFromWord [Lit (Word64 (4613937818241073152w:word64))])
      (Let (SOME "strArgs")
       (App Opapp [Var (Short "reader1"); Var (Short "u")])
       (Mat (Var (Short "strArgs"))
        [(Pvar "d1s",
          (Let (SOME "d1")
           (App Opapp [Var (Short "intToFP"); Var (Short "d1s")])
            (Let (SOME "b")
               (Fun "x"
               (Let (SOME "y")
                (App Opapp [
                          Var (Short "doppler"); Var (Short "d1")])
                (Var (Short "y"))))
              (App Opapp [
                  App Opapp [
                      App Opapp [Var (Short "iter"); Lit (IntLit ^iter_count)];
                      Var (Short "u")]; Var (Short "b")]))))])))]’;

  val call2_code = Parse.Term ‘
    [Dlet unknown_loc (Pvar "it")
     (Let (SOME "u") (App FpFromWord [Lit (Word64 (4613937818241073152w:word64))])
      (Let (SOME "strArgs")
       (App Opapp [Var (Short "reader2"); Var (Short "u")])
       (Mat (Var (Short "strArgs"))
        [(Pcon NONE [Pvar "d1s"; Pvar "d2s"],
          (Let (SOME "d1")
           (App Opapp [Var (Short "intToFP"); Var (Short "d1s")])
           (Let (SOME "d2")
            (App Opapp [Var (Short "intToFP"); Var (Short "d2s")])
             (Let (SOME "b")
              (Fun "x"
               (Let (SOME "y")
                (App Opapp [
                          App Opapp [Var (Short "doppler"); Var (Short "d1")];
                        Var (Short "d2")])
                (Var (Short "y"))))
              (App Opapp [
                  App Opapp [
                      App Opapp [Var (Short "iter"); Lit (IntLit ^iter_count)];
                      Var (Short "u")]; Var (Short "b")])))))])))]’;

  val call3_code = Parse.Term ‘
    [Dlet unknown_loc (Pvar "it")
     (Let (SOME "u") (App FpFromWord [Lit (Word64 (4613937818241073152w:word64))])
      (Let (SOME "strArgs")
       (App Opapp [Var (Short "reader3"); Var (Short "u")])
       (Mat (Var (Short "strArgs"))
        [(Pcon NONE [Pvar "d1s"; Pcon NONE [Pvar "d2s"; Pvar "d3s"]],
          (Let (SOME "d1")
           (App Opapp [Var (Short "intToFP"); Var (Short "d1s")])
           (Let (SOME "d2")
            (App Opapp [Var (Short "intToFP"); Var (Short "d2s")])
            (Let (SOME "d3")
             (App Opapp [Var (Short "intToFP"); Var (Short "d3s")])
             (Let (SOME "b")
              (Fun "x"
               (Let (SOME "y")
                (App Opapp [
                    App Opapp [
                        App Opapp [Var (Short "doppler"); Var (Short "d1")];
                        Var (Short "d2")];
                    Var (Short "d3")])
                (Var (Short "y"))))
              (App Opapp [
                  App Opapp [
                      App Opapp [Var (Short "iter"); Lit (IntLit ^iter_count)];
                      Var (Short "u")]; Var (Short "b")]))))))])))]’;

  val call4_code = Parse.Term ‘
      [Dlet unknown_loc (Pvar "it")
  (Let (SOME "u") (App FpFromWord [Lit (Word64 (4613937818241073152w:word64))])
   (Let (SOME "strArgs")
    (App Opapp [Var (Short "reader4"); Var (Short "u")])
    (Mat (Var (Short "strArgs"))
       [(Pcon NONE [Pvar "d1s"; Pcon NONE [Pvar "d2s"; Pcon NONE [Pvar "d3s"; Pvar "d4s"]]]),
         (Let (SOME "d1")
          (App Opapp [Var (Short "intToFP"); Var (Short "d1s")])
          (Let (SOME "d2")
           (App Opapp [Var (Short "intToFP"); Var (Short "d2s")])
           (Let (SOME "d3")
            (App Opapp [Var (Short "intToFP"); Var (Short "d3s")])
            (Let (SOME "d4")
             (App Opapp [Var (Short "intToFP"); Var (Short "d4s")])
          (Let (SOME "b")
           (Fun "x"
            (Let (SOME "y")
             (App Opapp [
             App Opapp [
                App Opapp [
                  App Opapp [Var (Short "nn1Layer"); Var (Short "d1")];
                  Var (Short "d2")];
                Var (Short "d3")];
                Var (Short "d4")])
             (Var (Short "y"))))
           (App Opapp [
              App Opapp [
                App Opapp [Var (Short "iter"); Lit (IntLit ^iter_count)];
                Var (Short "u")]; Var (Short "b")]))))))])))]’;

  fun do_stuff theAST_def theAST_pre_def =
  let
    val theAST = theAST_def |> concl |> rhs
    val theAST_pre = theAST_pre_def |> concl |> rhs
    (** Optimizations to be applied by Icing **)
    val theOpts_def = Define ‘theOpts = no_fp_opt_conf’
    val numArgs = EVAL “LENGTH (FST (SND (getDeclLetParts theAST)))” |> concl
                  |> rhs
                  |> numSyntax.dest_numeral
                  |>  Arbnumcore.toInt
    val (theMain, call_code) =
      if numArgs = 1 then (main1, call1_code)
      else if numArgs = 2 then (main2, call2_code)
      else if numArgs = 3 then (main3, call3_code)
      else if numArgs = 4 then (main4, call4_code)
      else raise ERR "Too many arguments" ""
    val theAST_plan = save_thm ("theAST_plan", EVAL (Parse.Term ‘generate_plan_decs theOpts theAST’));
    val thePlan_def = EVAL “HD ^(theAST_plan |> concl |> rhs)”
    val hotRewrites = thePlan_def |> concl |> rhs |> listSyntax.dest_list |> #1
                      |> map (fn t => EVAL “case ^t of | Apply (_, rws) => rws | _ => [] ”
                                |> concl |> rhs |> listSyntax.dest_list |> #1)
                      |> flatMap
                      |> map (fn t => DB.apropos_in t (DB.thy "icing_optimisations"))
                      |> flatMap
                      |> map (#2 o #1)
                      |> dedup
                      |> List.foldl (fn (elem, acc) => acc ^ " " ^ elem ^ " ;") "Used rewrites:"
    val _ = adjoin_to_theory
             { sig_ps =
            SOME (fn _ => PP.add_string
                      ("(* "^hotRewrites^" *)")),
            struct_ps = NONE };
  (** The code below stores in theorem theAST_opt the optimized version of the AST
      from above and in errorbounds_AST the inferred FloVer roundoff error bounds
   **)
  val theAST_opt = save_thm ("theAST_opt",
    EVAL
      (Parse.Term ‘
        (no_opt_decs theOpts
         (MAP FST (stos_pass_with_plans_decs theOpts (generate_plan_decs theOpts theAST) theAST)))’));
  val doppler_opt = theAST_opt |> concl |> rhs;
  val theProg_def = Define ‘theProg = ^theAST’
  val theOptProg_def = Define ‘theOptProg = ^doppler_opt’;
  val theBenchmarkMain_def = Define ‘theBenchmarkMain =
   (HD (^iter_code)) :: (^call_code  )’;
  val st_no_doppler = get_ml_prog_state ();
  val theAST_env = st_no_doppler
   |> ml_progLib.clean_state
   |> ml_progLib.remove_snocs
   |> ml_progLib.get_env;
  val _ = append_prog (theOptProg_def |> concl |> rhs)
  val _ = append_prog theMain;
  val theAST_env_def = Define ‘theAST_env = ^theAST_env’;
  (* val _ = computeLib.del_funs [sptreeTheory.subspt_def]; *)
  val _ = computeLib.add_funs [realTheory.REAL_INV_1OVER,
                             binary_ieeeTheory.float_to_real_def,
                             binary_ieeeTheory.float_tests,
                             sptreeTheory.subspt_eq,
                             sptreeTheory.lookup_def];
  val errorbounds_AST = save_thm ("errorbounds_AST",
    EVAL (Parse.Term
       ‘isOkError ^(concl theAST_opt |> rhs) theAST_pre theErrBound’))
  in () end;
(*
val _ =
  supportLib.write_code_to_file true theAST_def theAST_opt
(Parse.Term ‘APPEND ^(reader3_def |> concl |> rhs) (APPEND ^(intToFP_def |> concl |> rhs) (APPEND ^(printer_def |> concl |> rhs) ^(theBenchmarkMain_def |> concl |> rhs)))’)
    (Parse.Term ‘APPEND ^(reader3_def |> concl |> rhs) (APPEND ^(intToFP_def |> concl |> rhs) (APPEND ^(printer_def |> concl |> rhs) ^(theBenchmarkMain_def |> concl |> rhs)))’)
    "doppler";
*)

  fun define_benchmark theAST theAST_pre benchmarking =
    let
      val theAST_pre_term = theAST_pre |> concl |> rhs
      val theAST_term = theAST |> concl |> rhs
      val numArgs = EVAL “LENGTH (FST (SND (getDeclLetParts theAST)))” |> concl
                    |> rhs
                    |> numSyntax.dest_numeral
                    |>  Arbnumcore.toInt
      val (theMain, theCall) =
        if numArgs = 1 then (main1, call1_code)
        else if numArgs = 2 then (main2, call2_code)
        else if numArgs = 3 then (main3, call3_code)
        else if numArgs = 4 then (main4, call4_code)
        else raise ERR "Too many arguments" ""
      val thePlan = EVAL (Parse.Term ‘generate_plan_decs no_fp_opt_conf theAST’)
      val thePlan_simpl = EVAL (Parse.Term ‘FLAT
                                            (MAP (FOLDL (λ acc x. case x of | Apply (pth, rws) => acc ++ [(pth, rws)] |_ => acc) []) ^(thePlan |> concl |> rhs))’)
      val theAST_plan = save_thm ("theAST_plan", thePlan)
      val hotRewrites = thePlan_simpl |> concl |> rhs |> listSyntax.dest_list |> #1
                       |> map (#2 o dest_pair)
                       |> map (#1 o listSyntax.dest_list)
                       |> flatMap
                       |> map (fn t => DB.apropos_in t (DB.thy "icing_optimisations"))
                       |> flatMap
                       |> map (#2 o #1)
                       |> dedup
                       |> List.foldl (fn (elem, acc) => acc ^ " " ^ elem ^ " ;") "Used rewrites:"
       (* val _ = adjoin_to_theory
               { sig_ps =
                 SOME (fn _ => PP.add_string
                                 ("val hotRewrites = \""^hotRewrites^"\";")),
                 struct_ps = NONE } *)
       val theAST_optimized = save_thm ("theAST_optimized", EVAL (Parse.Term ‘(stos_pass_with_plans_decs theOpts (generate_plan_decs theOpts theAST) theAST)’))
       val opt_result = theAST_optimized |> concl |> rhs |> listSyntax.dest_list |> #1
                        |> hd |> dest_pair |> #2
       val theAST_opt_nop = save_thm ("theAST_opt_nop",
                                      EVAL (Parse.Term ‘
                                             (no_opt_decs theOpts
       (MAP FST (stos_pass_with_plans_decs theOpts (generate_plan_decs theOpts theAST) theAST)))’))
       val _ =  if (Term.compare(opt_result, Parse.Term ‘source_to_source$Success’) = EQUAL)
                then print("Succesfully applied optimisations")
                else print ("Optimisation failed with "^Parse.term_to_string opt_result)
       val theProg_def = bossLib.Define ‘theProg = ^theAST_term’
       val theOptProg_def = bossLib.Define ‘theOptProg = ^(theAST_opt_nop |> concl |> rhs)’
      val theBenchmarkMain_def = bossLib.Define ‘theBenchmarkMain = (HD (^iter_code)) :: (^theCall)’
      val st_no_doppler = get_ml_prog_state ();
      val theAST_env = st_no_doppler
                          |> ml_progLib.clean_state
                          |> ml_progLib.remove_snocs
                          |> ml_progLib.get_env
      val theAST_env_def = bossLib.Define ‘theAST_env = ^theAST_env’
      val _ = append_prog (theOptProg_def |> concl |> rhs)
      val _ = append_prog main3;
      (* FIXME val _ =
        supportLib.write_code_to_file true theAST_def theAST_opt
                  (Parse.Term ‘APPEND ^(reader3_def |> concl |> rhs) (APPEND ^(intToFP_def |> concl |> rhs) (APPEND ^(printer_def |> concl |> rhs) ^(theBenchmarkMain_def |> concl |> rhs)))’)
                  (Parse.Term ‘APPEND ^(reader3_def |> concl |> rhs) (APPEND ^(intToFP_def |> concl |> rhs) (APPEND ^(printer_def |> concl |> rhs) ^(theBenchmarkMain_def |> concl |> rhs)))’)
                  "doppler"; *)
      (* val _ = computeLib.del_funs [sptreeTheory.subspt_def]; *)
      val _ = computeLib.add_funs [realTheory.REAL_INV_1OVER,
                                   binary_ieeeTheory.float_to_real_def,
                                   binary_ieeeTheory.float_tests,
                                   sptreeTheory.subspt_eq,
                                   sptreeTheory.lookup_def];
      (* val errorbounds_AST = save_thm ("errorbounds_AST",
        EVAL (Parse.Term
          ‘isOkError ^(concl theAST_opt_nop |> rhs) doppler_pre theErrBound’))
      val errorbound_opt = save_thm ("errorbound_opt",
        EVAL (Parse.Term
          ‘getError ^(concl theAST_opt_nop |> rhs) doppler_pre theErrBound’))
      val errorbound_unopt = save_thm ("errorbound_unopt",
        EVAL (Parse.Term
          ‘getError ^theAST_term doppler_pre theErrBound’)) *)
      in () end;

end;
