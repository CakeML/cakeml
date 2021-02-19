(*
  Lib to prove examples
*)
structure exampleLib =
struct
  open astTheory cfTacticsLib ml_translatorLib;
  open basis_ffiTheory cfHeapsBaseTheory basis;
  open FloverMapTheory RealIntervalInferenceTheory ErrorIntervalInferenceTheory
       CertificateCheckerTheory;
  open floatToRealProofsTheory source_to_sourceTheory CakeMLtoFloVerTheory
       source_to_sourceProofsTheory
       cfSupportTheory optPlannerTheory icing_realIdProofsTheory;
  open machine_ieeeTheory binary_ieeeTheory realTheory realLib RealArith;
  open supportLib;

  val logErrors = ref false;

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

  fun main1 fname =
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
                  (App Opapp [Var (Short ^fname); Var (Short "d1")])
                (Let (SOME "y")
                 (App FpToWord [Var (Short "x")])
                 (App Opapp [
                     Var (Short "printer");
                     Var (Short "y")])))))]))))]”;

  fun main2 fname =
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
                          App Opapp [Var (Short ^fname); Var (Short "d1")];
                        Var (Short "d2")])
                (Let (SOME "y")
                 (App FpToWord [Var (Short "x")])
                 (App Opapp [
                     Var (Short "printer");
                     Var (Short "y")]))))))]))))]”;

  fun main3 fname =
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
                        App Opapp [Var (Short ^fname); Var (Short "d1")];
                        Var (Short "d2")];
                    Var (Short "d3")])
                (Let (SOME "y")
                 (App FpToWord [Var (Short "x")])
                 (App Opapp [
                     Var (Short "printer");
                     Var (Short "y")])))))))]))))]”;

  fun main4 fname =
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
                     App Opapp [Var (Short ^fname); Var (Short "d1")];
                     Var (Short "d2")];
                   Var (Short "d3")];
                 Var (Short "d4")])
             (Let (SOME "y")
              (App FpToWord [Var (Short "x")])
              (App Opapp [
                 Var (Short "printer");
                 Var (Short "y")])))))))]))))]”;

  fun main6 fname =
  “[Dlet unknown_loc (Pvar "main")
    (Fun "a"
     (Let (SOME "u") (Con NONE [])
     (Let (SOME "strArgs")
      (App Opapp [Var (Short "reader6"); Var (Short "u")])
      (Mat (Var (Short "strArgs"))
       [(Pcon NONE [Pvar "d1s"; Pcon NONE [Pvar "d2s"; Pcon NONE [Pvar "d3s";
         Pcon NONE [Pvar "d4s"; Pcon NONE [Pvar "d5s"; Pvar "d6s"]]]]]),
         (Let (SOME "d1")
          (App Opapp [Var (Short "intToFP"); Var (Short "d1s")])
          (Let (SOME "d2")
           (App Opapp [Var (Short "intToFP"); Var (Short "d2s")])
           (Let (SOME "d3")
            (App Opapp [Var (Short "intToFP"); Var (Short "d3s")])
            (Let (SOME "d4")
             (App Opapp [Var (Short "intToFP"); Var (Short "d4s")])
             (Let (SOME "d5")
              (App Opapp [Var (Short "intToFP"); Var (Short "d5s")])
             (Let (SOME "d6")
              (App Opapp [Var (Short "intToFP"); Var (Short "d6s")])
             (Let (SOME "x" )
              (App Opapp [
                 App Opapp [
                   App Opapp [
                     App Opapp [
                       App Opapp [
                         App Opapp [Var (Short ^fname); Var (Short "d1")];
                         Var (Short "d2")];
                       Var (Short "d3")];
                     Var (Short "d4")];
                   Var (Short "d5")];
                 Var (Short "d6")])
             (Let (SOME "y")
              (App FpToWord [Var (Short "x")])
              (App Opapp [
                 Var (Short "printer");
                 Var (Short "y")])))))))))]))))]”;

  fun main8 fname =
  “[Dlet unknown_loc (Pvar "main")
    (Fun "a"
     (Let (SOME "u") (Con NONE [])
     (Let (SOME "strArgs")
      (App Opapp [Var (Short "reader8"); Var (Short "u")])
      (Mat (Var (Short "strArgs"))
       [(Pcon NONE [Pvar "d1s"; Pcon NONE [Pvar "d2s"; Pcon NONE [Pvar "d3s";
         Pcon NONE [Pvar "d4s"; Pcon NONE [Pvar "d5s"; Pcon NONE [Pvar "d6s";
         Pcon NONE [Pvar "d7s"; Pvar "d8s"]]]]]]]),
         (Let (SOME "d1")
          (App Opapp [Var (Short "intToFP"); Var (Short "d1s")])
          (Let (SOME "d2")
           (App Opapp [Var (Short "intToFP"); Var (Short "d2s")])
           (Let (SOME "d3")
            (App Opapp [Var (Short "intToFP"); Var (Short "d3s")])
            (Let (SOME "d4")
             (App Opapp [Var (Short "intToFP"); Var (Short "d4s")])
             (Let (SOME "d5")
              (App Opapp [Var (Short "intToFP"); Var (Short "d5s")])
             (Let (SOME "d6")
              (App Opapp [Var (Short "intToFP"); Var (Short "d6s")])
              (Let (SOME "d7")
               (App Opapp [Var (Short "intToFP"); Var (Short "d7s")])
                (Let (SOME "d8")
                 (App Opapp [Var (Short "intToFP"); Var (Short "d8s")])
             (Let (SOME "x" )
              (App Opapp [
                 App Opapp [
                   App Opapp [
                     App Opapp [
                       App Opapp [
                         App Opapp [
                           App Opapp [
                             App Opapp [Var (Short ^fname); Var (Short "d1")];
                             Var (Short "d2")];
                           Var (Short "d3")];
                         Var (Short "d4")];
                       Var (Short "d5")];
                     Var (Short "d6")];
                   Var (Short "d7")];
                 Var (Short "d8")])
             (Let (SOME "y")
              (App FpToWord [Var (Short "x")])
              (App Opapp [
                 Var (Short "printer");
                 Var (Short "y")])))))))))))]))))]”;

  fun main9 fname =
  “[Dlet unknown_loc (Pvar "main")
    (Fun "a"
     (Let (SOME "u") (Con NONE [])
     (Let (SOME "strArgs")
      (App Opapp [Var (Short "reader9"); Var (Short "u")])
      (Mat (Var (Short "strArgs"))
       [(Pcon NONE [Pvar "d1s"; Pcon NONE [Pvar "d2s"; Pcon NONE [Pvar "d3s";
         Pcon NONE [Pvar "d4s"; Pcon NONE [Pvar "d5s"; Pcon NONE [Pvar "d6s";
         Pcon NONE [Pvar "d7s"; Pcon NONE [Pvar "d8s"; Pvar "d9s"]]]]]]]]),
         (Let (SOME "d1")
          (App Opapp [Var (Short "intToFP"); Var (Short "d1s")])
          (Let (SOME "d2")
           (App Opapp [Var (Short "intToFP"); Var (Short "d2s")])
           (Let (SOME "d3")
            (App Opapp [Var (Short "intToFP"); Var (Short "d3s")])
            (Let (SOME "d4")
             (App Opapp [Var (Short "intToFP"); Var (Short "d4s")])
             (Let (SOME "d5")
              (App Opapp [Var (Short "intToFP"); Var (Short "d5s")])
             (Let (SOME "d6")
              (App Opapp [Var (Short "intToFP"); Var (Short "d6s")])
              (Let (SOME "d7")
               (App Opapp [Var (Short "intToFP"); Var (Short "d7s")])
                (Let (SOME "d8")
                 (App Opapp [Var (Short "intToFP"); Var (Short "d8s")])
                  (Let (SOME "d9")
                   (App Opapp [Var (Short "intToFP"); Var (Short "d9s")])
             (Let (SOME "x" )
              (App Opapp [
                 App Opapp [
                   App Opapp [
                     App Opapp [
                       App Opapp [
                         App Opapp [
                           App Opapp [
                             App Opapp [
                               App Opapp [Var (Short ^fname); Var (Short "d1")];
                               Var (Short "d2")];
                             Var (Short "d3")];
                           Var (Short "d4")];
                         Var (Short "d5")];
                       Var (Short "d6")];
                     Var (Short "d7")];
                   Var (Short "d8")];
                 Var (Short "d9")])
             (Let (SOME "y")
              (App FpToWord [Var (Short "x")])
              (App Opapp [
                 Var (Short "printer");
                 Var (Short "y")]))))))))))))]))))]”;

  fun call1_code fname = Parse.Term ‘
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
                          Var (Short ^fname); Var (Short "d1")])
                (Var (Short "y"))))
              (App Opapp [
                  App Opapp [
                      App Opapp [Var (Short "iter"); Lit (IntLit ^iter_count)];
                      Var (Short "u")]; Var (Short "b")]))))])))]’;

  fun call2_code fname = Parse.Term ‘
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
                          App Opapp [Var (Short ^fname); Var (Short "d1")];
                        Var (Short "d2")])
                (Var (Short "y"))))
              (App Opapp [
                  App Opapp [
                      App Opapp [Var (Short "iter"); Lit (IntLit ^iter_count)];
                      Var (Short "u")]; Var (Short "b")])))))])))]’;

  fun call3_code fname = Parse.Term ‘
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
                        App Opapp [Var (Short ^fname); Var (Short "d1")];
                        Var (Short "d2")];
                    Var (Short "d3")])
                (Var (Short "y"))))
              (App Opapp [
                  App Opapp [
                      App Opapp [Var (Short "iter"); Lit (IntLit ^iter_count)];
                      Var (Short "u")]; Var (Short "b")]))))))])))]’;

  fun call4_code fname = Parse.Term ‘
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
                  App Opapp [Var (Short ^fname); Var (Short "d1")];
                  Var (Short "d2")];
                Var (Short "d3")];
                Var (Short "d4")])
             (Var (Short "y"))))
           (App Opapp [
              App Opapp [
                App Opapp [Var (Short "iter"); Lit (IntLit ^iter_count)];
                Var (Short "u")]; Var (Short "b")]))))))])))]’;

  fun call6_code fname = Parse.Term ‘
      [Dlet unknown_loc (Pvar "it")
  (Let (SOME "u") (App FpFromWord [Lit (Word64 (4613937818241073152w:word64))])
   (Let (SOME "strArgs")
    (App Opapp [Var (Short "reader6"); Var (Short "u")])
    (Mat (Var (Short "strArgs"))
       [(Pcon NONE [Pvar "d1s"; Pcon NONE [Pvar "d2s"; Pcon NONE [Pvar "d3s";
         Pcon NONE [Pvar "d4s"; Pcon NONE [Pvar "d5s"; Pvar "d6s"]]]]]),
         (Let (SOME "d1")
          (App Opapp [Var (Short "intToFP"); Var (Short "d1s")])
          (Let (SOME "d2")
           (App Opapp [Var (Short "intToFP"); Var (Short "d2s")])
           (Let (SOME "d3")
            (App Opapp [Var (Short "intToFP"); Var (Short "d3s")])
            (Let (SOME "d4")
             (App Opapp [Var (Short "intToFP"); Var (Short "d4s")])
             (Let (SOME "d5")
              (App Opapp [Var (Short "intToFP"); Var (Short "d5s")])
             (Let (SOME "d6")
              (App Opapp [Var (Short "intToFP"); Var (Short "d6s")])
          (Let (SOME "b")
           (Fun "x"
            (Let (SOME "y")
             (App Opapp [
             App Opapp [
                App Opapp [
                  App Opapp [
                    App Opapp [
                      App Opapp [Var (Short ^fname); Var (Short "d1")];
                      Var (Short "d2")];
                    Var (Short "d3")];
                    Var (Short "d4")];
                  Var (Short "d5")];
                Var (Short "d6")])
             (Var (Short "y"))))
           (App Opapp [
              App Opapp [
                App Opapp [Var (Short "iter"); Lit (IntLit ^iter_count)];
                Var (Short "u")]; Var (Short "b")]))))))))])))]’;

  fun call8_code fname = Parse.Term ‘
      [Dlet unknown_loc (Pvar "it")
  (Let (SOME "u") (App FpFromWord [Lit (Word64 (4613937818241073152w:word64))])
   (Let (SOME "strArgs")
    (App Opapp [Var (Short "reader8"); Var (Short "u")])
    (Mat (Var (Short "strArgs"))
       [(Pcon NONE [Pvar "d1s"; Pcon NONE [Pvar "d2s"; Pcon NONE [Pvar "d3s";
         Pcon NONE [Pvar "d4s"; Pcon NONE [Pvar "d5s"; Pcon NONE [Pvar "d6s";
         Pcon NONE [Pvar "d7s"; Pvar "d8s"]]]]]]]),
         (Let (SOME "d1")
          (App Opapp [Var (Short "intToFP"); Var (Short "d1s")])
          (Let (SOME "d2")
           (App Opapp [Var (Short "intToFP"); Var (Short "d2s")])
           (Let (SOME "d3")
            (App Opapp [Var (Short "intToFP"); Var (Short "d3s")])
            (Let (SOME "d4")
             (App Opapp [Var (Short "intToFP"); Var (Short "d4s")])
             (Let (SOME "d5")
              (App Opapp [Var (Short "intToFP"); Var (Short "d5s")])
             (Let (SOME "d6")
              (App Opapp [Var (Short "intToFP"); Var (Short "d6s")])
              (Let (SOME "d7")
               (App Opapp [Var (Short "intToFP"); Var (Short "d7s")])
                (Let (SOME "d8")
                 (App Opapp [Var (Short "intToFP"); Var (Short "d8s")])
          (Let (SOME "b")
           (Fun "x"
            (Let (SOME "y")
              (App Opapp [
                 App Opapp [
                   App Opapp [
                     App Opapp [
                       App Opapp [
                         App Opapp [
                           App Opapp [
                             App Opapp [Var (Short ^fname); Var (Short "d1")];
                             Var (Short "d2")];
                           Var (Short "d3")];
                         Var (Short "d4")];
                       Var (Short "d5")];
                     Var (Short "d6")];
                   Var (Short "d7")];
                 Var (Short "d8")])
               (Var (Short "y"))))
           (App Opapp [
              App Opapp [
                App Opapp [Var (Short "iter"); Lit (IntLit ^iter_count)];
                Var (Short "u")]; Var (Short "b")]))))))))))])))]’;

  fun call9_code fname = Parse.Term ‘
      [Dlet unknown_loc (Pvar "it")
  (Let (SOME "u") (App FpFromWord [Lit (Word64 (4613937818241073152w:word64))])
   (Let (SOME "strArgs")
    (App Opapp [Var (Short "reader9"); Var (Short "u")])
    (Mat (Var (Short "strArgs"))
       [(Pcon NONE [Pvar "d1s"; Pcon NONE [Pvar "d2s"; Pcon NONE [Pvar "d3s";
         Pcon NONE [Pvar "d4s"; Pcon NONE [Pvar "d5s"; Pcon NONE [Pvar "d6s";
         Pcon NONE [Pvar "d7s"; Pcon NONE [Pvar "d8s"; Pvar "d9s"]]]]]]]]),
         (Let (SOME "d1")
          (App Opapp [Var (Short "intToFP"); Var (Short "d1s")])
          (Let (SOME "d2")
           (App Opapp [Var (Short "intToFP"); Var (Short "d2s")])
           (Let (SOME "d3")
            (App Opapp [Var (Short "intToFP"); Var (Short "d3s")])
            (Let (SOME "d4")
             (App Opapp [Var (Short "intToFP"); Var (Short "d4s")])
             (Let (SOME "d5")
              (App Opapp [Var (Short "intToFP"); Var (Short "d5s")])
             (Let (SOME "d6")
              (App Opapp [Var (Short "intToFP"); Var (Short "d6s")])
              (Let (SOME "d7")
               (App Opapp [Var (Short "intToFP"); Var (Short "d7s")])
                (Let (SOME "d8")
                 (App Opapp [Var (Short "intToFP"); Var (Short "d8s")])
                  (Let (SOME "d9")
                   (App Opapp [Var (Short "intToFP"); Var (Short "d9s")])
          (Let (SOME "b")
           (Fun "x"
            (Let (SOME "y")
              (App Opapp [
                 App Opapp [
                   App Opapp [
                     App Opapp [
                       App Opapp [
                         App Opapp [
                           App Opapp [
                             App Opapp [
                               App Opapp [Var (Short ^fname); Var (Short "d1")];
                               Var (Short "d2")];
                             Var (Short "d3")];
                           Var (Short "d4")];
                         Var (Short "d5")];
                       Var (Short "d6")];
                     Var (Short "d7")];
                   Var (Short "d8")];
                 Var (Short "d9")])
               (Var (Short "y"))))
           (App Opapp [
              App Opapp [
                App Opapp [Var (Short "iter"); Lit (IntLit ^iter_count)];
                Var (Short "u")]; Var (Short "b")])))))))))))])))]’;

  fun define_benchmark theAST_def theAST_pre_def checkError =
  let
    val theAST = theAST_def |> concl |> rhs
    val theAST_pre = theAST_pre_def |> concl |> rhs
    (** Optimizations to be applied by Icing **)
    val theOpts_def = Define ‘theOpts = no_fp_opt_conf’
    val theAST_plan_def = Define ‘theAST_plan = generate_plan_decs theOpts theAST’
    val theAST_plan_result = save_thm ("theAST_plan_result", EVAL (Parse.Term ‘theAST_plan’));
    val thePlan_def = EVAL “HD ^(theAST_plan_result |> concl |> rhs)”
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
  val theAST_opt_result = save_thm ("theAST_opt_result",
    EVAL
      (Parse.Term ‘
        MAP SND (stos_pass_with_plans_decs theOpts theAST_plan theAST)’));
  val _ = if Term.compare (theAST_opt_result |> concl |> rhs,“[source_to_source$Success]”) <> EQUAL
          then raise ERR ("Failed optimization with error:"^
                          (Parse.thm_to_string theAST_opt_result)) ""
          else ()
  val theAST_opt = save_thm ("theAST_opt",
    EVAL
      (Parse.Term ‘
        (no_opt_decs theOpts (MAP FST (stos_pass_with_plans_decs theOpts theAST_plan theAST)))’));
    val (fname_opt, fvars_opt, body_opt) =
      EVAL (Parse.Term ‘getDeclLetParts ^(theAST_opt |> concl |> rhs)’)
      |> concl |> rhs |> dest_pair
      |> (fn (x,y) => let val (y,z) = dest_pair y in (x,y,z) end)
    val (fname, fvars, body) =
      EVAL (Parse.Term ‘getDeclLetParts theAST’)
      |> concl |> rhs |> dest_pair
      |> (fn (x,y) => let val (y,z) = dest_pair y in (x,y,z) end)
    val numArgs = EVAL “LENGTH ^fvars” |> concl
                  |> rhs
                  |> numSyntax.dest_numeral
                  |>  Arbnumcore.toInt
    val (theMain, call_code, reader_def, reader_spec) =
      if numArgs = 1 then (main1 fname, call1_code fname, reader1_def, reader1_spec)
      else if numArgs = 2 then (main2 fname, call2_code fname, reader2_def, reader2_spec)
      else if numArgs = 3 then (main3 fname, call3_code fname, reader3_def, reader3_spec)
      else if numArgs = 4 then (main4 fname, call4_code fname, reader4_def, reader4_spec)
      else if numArgs = 6 then (main6 fname, call6_code fname, reader6_def, reader6_spec)
      else if numArgs = 8 then (main8 fname, call8_code fname, reader8_def, reader8_spec)
      else if numArgs = 9 then (main9 fname, call9_code fname, reader9_def, reader9_spec)
      else raise ERR ("Too many arguments:"^(Int.toString numArgs)) ""
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
  val errorbounds_AST =
    if ((!logErrors) andalso checkError) then
      let
        val error_thm_opt =
           EVAL (Parse.Term  ‘getErrorbounds ^(concl theAST_opt |> rhs) theAST_pre’)
         val (bounds, cmd) =
           EVAL (Parse.Term ‘case ^(error_thm_opt |> concl |> rhs) of
                     |(SOME (bounds, cmd, _), _) => (bounds,cmd)’)
                     |> concl |> rhs |> dest_pair
         val theBound =
           EVAL (Parse.Term ‘case FloverMapTree_find (getRetExp (toRCmd ^cmd)) ^bounds of
                             |SOME ((lo,hi),e)  => e’)
         val theAST_opt_bound_def = Define ‘theAST_opt_bound = ^(theBound |> concl |> rhs)’
         val error_thm_unopt =
           EVAL (Parse.Term  ‘getErrorbounds (no_opt_decs no_fp_opt_conf ^(concl theAST_def |> rhs)) theAST_pre’)
         val (bounds_unopt, cmd_unopt) =
           EVAL (Parse.Term ‘case ^(error_thm_unopt |> concl |> rhs) of
                     |(SOME (bounds, cmd, _), _) => (bounds,cmd)’)
                     |> concl |> rhs |> dest_pair
         val theBound =
           EVAL (Parse.Term ‘case FloverMapTree_find (getRetExp (toRCmd ^cmd_unopt)) ^bounds_unopt of
                             |SOME ((lo,hi),e)  => e’)
         val theAST_unopt_bound_def = Define ‘theAST_unopt_bound = ^(theBound |> concl |> rhs)’
      in
        store_thm ("errorbounds_AST",
          Parse.Term(‘isOkError ^(concl theAST_opt |> rhs) theAST_pre theErrBound = (SOME T, NONE)’),
          simp[isOkError_def, error_thm_opt] \\ EVAL_TAC)
       end
    else if checkError then
      save_thm ("errorbounds_AST",
        EVAL (Parse.Term
          ‘isOkError ^(concl theAST_opt |> rhs) theAST_pre theErrBound’))
    else CONJ_COMM
  val local_opt_thm = save_thm ("local_opt_thm", mk_local_opt_thm theAST_opt theAST_def);
  val _ =
   supportLib.write_code_to_file true theAST_def theAST_opt
  (Parse.Term ‘APPEND ^(reader_def |> concl |> rhs) (APPEND ^(intToFP_def |> concl |> rhs) (APPEND ^(printer_def |> concl |> rhs) ^(theBenchmarkMain_def |> concl |> rhs)))’)
  (Parse.Term ‘APPEND ^(reader_def |> concl |> rhs) (APPEND ^(intToFP_def |> concl |> rhs) (APPEND ^(printer_def |> concl |> rhs) ^(theBenchmarkMain_def |> concl |> rhs)))’)
    (stringSyntax.fromHOLstring fname) numArgs;
  (* Plan correctness theorem *)
  val plan_list = theAST_plan_result |> concl |> rhs (* Get the actual plan *)
                   |> listSyntax.dest_list (* get the single plan *)
                   |> (fn (ts, tp) => if (length ts <> 1) then raise ERR "Too many plans constructed" ""
                                        else hd ts)
                   |> listSyntax.dest_list (* extract the plan as a list *)
                   |> #1 (* take the list, ignore type *)
  val stos_pass_correct_thm =
    if (not (!logErrors)) then save_thm ("stos_pass_correct_thm", mk_stos_pass_correct_thm plan_list)
    else CONJ_COMM
  val stos_pass_real_id_thm =
    if (not (!logErrors)) then save_thm ("stos_pass_real_id_thm", mk_stos_pass_real_id_thm plan_list)
    else CONJ_COMM
  val main_spec_thm =
    if (not checkError orelse !logErrors) then CONJ_COMM
    else
      let
      val st = get_ml_prog_state ();
      (* Precreate terms for arguments *)
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
        else (“(w1, w2, w3, w4, w5, w6, w7, w8, w9):
                word64#word64#word64#word64#word64#word64#word64#word64#word64”,
              “[w1; w2; w3; w4; w5; w6; w7; w8; w9]:word64 list”,
              “[d1; d2; d3; d4; d5; d6; d7; d8; d9]:v list”)
      (* Define a real-number and floating-point spec*)
      val theAST_real_spec_def =
        Define ‘theAST_real_spec ^args = real_spec_prog ^body_opt theAST_env ^fvars ^argList’
      val theAST_opt_float_option_noopt_def =
        Define ‘theAST_opt_float_option_noopt ^args =
                case evaluate
                     (empty_state with fp_state := empty_state.fp_state with canOpt := FPScope NoOpt)
                     (theAST_env with v :=
                        extend_env_with_vars (REVERSE ^fvars) (REVERSE ^argList) (theAST_env).v)
                [^body_opt] of
                | (st, Rval [FP_WordTree fp]) =>
                  if st = (empty_state with fp_state := empty_state.fp_state
                    with canOpt := FPScope NoOpt)
                  then SOME fp else NONE
                | _ => NONE’
      val theAST_opt_float_option_def =
        Define ‘theAST_opt_float_option ^args =
               case evaluate empty_state
                      (theAST_env with v :=
                        extend_env_with_vars (REVERSE ^fvars) (REVERSE ^argList) (theAST_env).v)
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
      val freeVars_list_body = store_thm ("freeVars_list_body",
        Parse.Term ‘
        ∀ (st1:unit semanticPrimitives$state) st2.
          freeVars_plan_bound st1 st2
            (theAST_env with v :=
             extend_env_with_vars (REVERSE ^fvars) (REVERSE ^argList) (theAST_env).v)
            no_fp_opt_conf
            (HD theAST_plan)
            ^body’,
        rpt strip_tac
        \\ gs[theAST_plan_result, freeVars_plan_bound_def, freeVars_arithExp_bound_def, EVERYi_def]
        \\  rpt conj_tac
        (* Non-let goals automatically solved *)
        \\ rpt (gs[freeVars_fp_bound_def, extend_env_with_vars_def, EVERYi_def]
        \\  qmatch_goalsub_abbrev_tac ‘freeVars_arithExp_bound st1 st2 theAST_env_new _ _ rewrittenExp’
        \\ qpat_x_assum ‘Abbrev(rewrittenExp = _)’ (assume_tac o EVAL_RULE)
        \\ unabbrev_all_tac \\ gs[freeVars_arithExp_bound_def]
        \\ gs[freeVars_fp_bound_def, extend_env_with_vars_def])
        \\ rpt strip_tac \\ gs[ml_progTheory.nsLookup_nsBind_compute])
      val freeVars_real_list_body = store_thm ("freeVars_list_body",
        Parse.Term ‘
        ∀ (st1:unit semanticPrimitives$state) st2.
          freeVars_realPlan_bound st1 st2
            (theAST_env with v :=
             toRspace (extend_env_with_vars (REVERSE ^fvars) (REVERSE ^argList) (theAST_env).v))
            no_fp_opt_conf []
            ^body’,
        rpt strip_tac
        \\ gs[theAST_plan_result, freeVars_realPlan_bound_def, freeVars_realExp_bound_def, EVERYi_def]
        \\  rpt conj_tac
        (* Non-let goals automatically solved *)
        \\ rpt (gs[freeVars_real_bound_def, extend_env_with_vars_def, EVERYi_def]
        \\  qmatch_goalsub_abbrev_tac ‘freeVars_arithExp_bound st1 st2 theAST_env_new _ _ rewrittenExp’
        \\ qpat_x_assum ‘Abbrev(rewrittenExp = _)’ (assume_tac o EVAL_RULE)
        \\ unabbrev_all_tac \\ gs[freeVars_realExp_bound_def]
        \\ gs[freeVars_real_bound_def, extend_env_with_vars_def])
        \\ rpt strip_tac \\ gs[ml_progTheory.nsLookup_nsBind_compute])
      val theAST_opt_backward_sim = store_thm ("theAST_opt_backward_sim",
        Parse.Term ‘theAST_opt_float_option_noopt ^args = SOME w ⇒
        theAST_float_returns ^args (compress_word w)’,
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
        \\ qmatch_goalsub_abbrev_tac ‘evaluate emp_upd dEnv
              [FST(optimise_with_plan theOpts thePlan e_init)] = (emp_res, _)’
        \\ strip_tac
        \\ assume_tac (INST_TYPE [“:'a” |-> “:unit”] stos_pass_correct_thm)
        \\ first_x_assum
             (qspecl_then [‘emp_upd’, ‘emp_res’, ‘dEnv’, ‘theOpts’, ‘[e_init]’,
                           ‘[FP_WordTree fp2]’] mp_tac)
        \\ simp[is_optimise_with_plan_correct_def]
        \\ impl_tac
        >- (
         unabbrev_all_tac
         \\ assume_tac freeVars_list_body
         \\ gs[empty_state_def, theOpts_def, extend_conf_def, no_fp_opt_conf_def,
               theAST_env_def, stos_pass_with_plans_def, theAST_plan_result])
        \\ rpt strip_tac
        \\ unabbrev_all_tac
        \\ fs[empty_state_def, semanticPrimitivesTheory.state_component_equality, theAST_env_def]
        \\ qpat_x_assum ‘evaluate _ _ [ _ ] = _’ mp_tac
        \\ qmatch_goalsub_abbrev_tac ‘evaluate newSt newEnv _ = _’
        \\ strip_tac
        \\ qexists_tac ‘newSt.fp_state.opts’
        \\ unabbrev_all_tac
        \\ first_x_assum (mp_then Any (qspec_then ‘0’ assume_tac)
                      (CONJUNCT1 fpSemPropsTheory.evaluate_add_choices))
        \\ fs[theOpts_def, no_fp_opt_conf_def, extend_conf_def,
              config_component_equality, theAST_plan_result]
        )
      (* Define a side-condition for the AST *)
      val theAST_side_def =
        Define ‘theAST_side ^args = (is_precond_sound ^fvars ^argList ^(theAST_pre_def |> concl |> rhs))’
      val is_Double_def = Define ‘
        is_Double [] [] = T ∧
        is_Double (w1::ws) (d1::ds) = (DOUBLE (Fp_const w1) d1 ∧ is_Double ws ds)’
      (* Load the necessary constants from the state *)
      val theAST_v = fetch_v (stringSyntax.fromHOLstring fname) st
      val theAST_v_def = DB.find ((term_to_string theAST_v)^"_def") |> hd |> #2 |> #1
      val theAST_spec = store_thm ("theAST_spec",
        Parse.Term ‘
        theAST_side ^args ∧
        is_Double ^argList ^vList  ⇒
        let result = (theAST_opt_float_option ^args) in
          (∀ p.
             app (p:'ffi ffi_proj) ^theAST_v
                 ^vList
                 (emp)
                 (POSTv v.
                  &DOUBLE_RES result v)) ∧
          theAST_float_returns ^args (compress_word (THE result)) ∧
          real$abs (fp64_to_real (compress_word (THE result)) - theAST_real_spec ^args) ≤ theErrBound’,
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
         \\ qmatch_goalsub_abbrev_tac
              ‘evaluate emptyWithReals realEnv
                [realify (FST (optimise_with_plan theOpts thePlan e_init))] = _’
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
          \\ strip_tac \\ gs[theOpts_def, no_fp_opt_conf_def]
          \\ assume_tac freeVars_real_list_body \\ gs[no_fp_opt_conf_def])
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
        )
      (* Some more precreated terms *)
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
      val all_float_string_def = Define ‘
        all_float_string [] [] = T ∧
        all_float_string (s1::ss) (w1::ws) = (is_float_string s1 w1 ∧ all_float_string ss ws)’
      val main_spec = store_thm ("main_spec",
        Parse.Term ‘
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
            theAST_real_spec ^args) ≤ theErrBound’,
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
        )
      val main_whole_prog_spec = store_thm ("main_whole_prog_spec",
        Parse.Term ‘
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
                  theAST_real_spec ^args) ≤ theErrBound’,
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
        )
      (* Put it all together into a theorem for the final spec proof *)
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
      val theAST_semantics =
        full_semantics_prog_thm |> ONCE_REWRITE_RULE[GSYM theAST_prog_def]
        |> DISCH_ALL |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC];
      val theAST_semantics_side_def = Define ‘
        theAST_semantics_side ^inps ^args ⇔
          all_float_string ^inp_list ^argList ∧
          theAST_side ^args’
      val theAST_semantics_final = store_thm ("theAST_semantics_final",
        Parse.Term ‘theAST_semantics_side ^inps ^args ∧ init_ok (^cl_list,fs) ⇒
        ∃ (w:word64).
          CakeML_evaluates_and_prints (^cl_list,fs,theAST_prog) (toString w) ∧
          theAST_float_returns ^args w ∧
          real$abs (fp64_to_real w - theAST_real_spec ^args) ≤ theErrBound’,
        rpt strip_tac
        \\ fs[init_ok_def, CakeML_evaluates_and_prints_def, theAST_semantics_side_def]
        \\ first_x_assum (mp_then Any mp_tac theAST_semantics)
        \\ rpt (disch_then drule) \\ fs[]
        \\ disch_then drule \\ strip_tac
        \\ qexists_tac ‘compress_word (THE (theAST_opt_float_option ^args))’ \\ fs[]
        \\ asm_exists_tac \\ fs[toString_def]
        )
      in theAST_semantics_final end
  in () end;

end;
