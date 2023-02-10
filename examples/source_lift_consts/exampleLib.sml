(*
  Lib to prove examples
*)
structure exampleLib =
struct
  open astTheory cfTacticsLib ml_translatorLib fpSemTheory fpValTreeTheory semanticPrimitivesTheory fpOptTheory;
  open basis_ffiTheory cfHeapsBaseTheory basis;
  (* open (* data_monadTheory*) (* compilationLib; *) *)
  open cfSupportTheory;
  open machine_ieeeTheory binary_ieeeTheory realTheory realLib RealArith sptreeTheory;
  open preamble;

  val _ = ParseExtras.temp_tight_equality();

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

  (** Run loop 100 million times **)
  val iter_count = (rhs o concl) (EVAL “100 *1000000:int”)

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

  fun define_benchmark theAST_def IGNORED1 IGNORED2 =
  let
    val theAST = theAST_def |> concl |> rhs
    val (fname, fvars, body) =
      EVAL (Parse.Term ‘getDeclLetParts theAST’)
      |> concl |> rhs |> dest_pair
      |> (fn (x,y) => let val (y,z) = dest_pair y in (x,y,z) end)
    val numArgs = EVAL “LENGTH ^fvars” |> concl
                  |> rhs
                  |> numSyntax.dest_numeral
                  |>  Arbnumcore.toInt
    val (theMain, call_code, reader_def) =
      if numArgs = 1 then (main1 fname, call1_code fname, reader1_def)
      else if numArgs = 2 then (main2 fname, call2_code fname, reader2_def)
      else if numArgs = 3 then (main3 fname, call3_code fname, reader3_def)
      else if numArgs = 4 then (main4 fname, call4_code fname, reader4_def)
      else if numArgs = 6 then (main6 fname, call6_code fname, reader6_def)
      else if numArgs = 8 then (main8 fname, call8_code fname, reader8_def)
      else if numArgs = 9 then (main9 fname, call9_code fname, reader9_def)
      else raise ERR ("Too many arguments:"^(Int.toString numArgs)) ""
  val theBenchmarkMain_def = Define ‘theBenchmarkMain =
   (HD (^iter_code)) :: (^call_code  )’;
  val _ =
   supportLib.write_code_to_file theAST
  (Parse.Term ‘APPEND ^(reader_def |> concl |> rhs) (APPEND ^(intToFP_def |> concl |> rhs) (APPEND ^(printer_def |> concl |> rhs) ^(theBenchmarkMain_def |> concl |> rhs)))’)
    (stringSyntax.fromHOLstring fname) numArgs;
  in () end;

end;
