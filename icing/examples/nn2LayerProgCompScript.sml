(**
  Icing benchmark input file
  Use this file to run a CakeML AST through the Icing optimizer
**)

(* INCLUDES, do not change those *)
open astTheory cfTacticsLib ml_translatorLib;
open basis_ffiTheory cfHeapsBaseTheory basis;
open RealIntervalInferenceTheory ErrorIntervalInferenceTheory CertificateCheckerTheory;
open source_to_sourceTheory CakeMLtoFloVerTheory cfSupportTheory;
open machine_ieeeTheory binary_ieeeTheory realTheory realLib RealArith;
open preamble;

val _ = new_theory "nn2LayerProgComp";

val _ = translation_extends "cfSupport";

(** Precondition **)
val nn2Layer_pre =
“λ (x:(string,string) id).
 if x = Short "x1"
 then ((- (48/100), 48/100):(real#real))
 else if x = Short "x2"
 then (- 10/1, 10/1)
 else if x = Short "x3"
 then (- 24/1, 24/1)
 else if x = Short "x4"
 then (-10/1, 10/1)
 else (0,0)”

Definition nn2Layer_pre_def:
  nn2Layer_pre = ^nn2Layer_pre
End

(**
  Define the CakeML source AST as a polyML/HOL4 declaration
**)
val nn2Layer =
(** REPLACE AST BELOW THIS LINE **)
“[
Dlet unknown_loc (Pvar "nn2Layer")
(Fun "x1" (Fun "x2" (Fun "x3" (Fun "x4" (FpOptimise Opt
(Let (SOME "dot1")
  (App (FP_bop FP_Div)
    [
      (App (FP_bop FP_Sub)
      [
        (App (FP_bop FP_Sub)
        [
          (App (FP_bop FP_Add)
          [
            (App (FP_bop FP_Sub)
            [
              (App (FP_bop FP_Mul)
              [
                (App FpFromWord [Lit (Word64 (-4629260865613238528w:word64))]);
                Var (Short  "x1")
              ]);
              (App (FP_bop FP_Mul)
              [
                (App FpFromWord [Lit (Word64 (4591668418803651523w:word64))]);
                Var (Short  "x2")
              ])
            ]);
            (App (FP_bop FP_Mul)
            [
              (App FpFromWord [Lit (Word64 (4601340349363392401w:word64))]);
              Var (Short  "x3")
            ])
          ]);
          (App (FP_bop FP_Mul)
          [
            (App FpFromWord [Lit (Word64 (4581508298044303684w:word64))]);
            Var (Short  "x4")
          ])
        ]);
        (App FpFromWord [Lit (Word64 (4603159803612850081w:word64))])
      ]);
      (App FpFromWord [Lit (Word64 (4652007308841189376w:word64))])
    ])
  (Let (SOME "dot2")
    (App (FP_bop FP_Div)
      [
        (App (FP_bop FP_Add)
        [
          (App (FP_bop FP_Sub)
          [
            (App (FP_bop FP_Sub)
            [
              (App (FP_bop FP_Sub)
              [
                (App (FP_bop FP_Mul)
                [
                  (App FpFromWord [Lit (Word64 (-4626688409506084500w:word64))]);
                  Var (Short  "x1")
                ]);
                (App (FP_bop FP_Mul)
                [
                  (App FpFromWord [Lit (Word64 (4599470454798108171w:word64))]);
                  Var (Short  "x2")
                ])
              ]);
              (App (FP_bop FP_Mul)
              [
                (App FpFromWord [Lit (Word64 (4610569576079762758w:word64))]);
                Var (Short  "x3")
              ])
            ]);
            (App (FP_bop FP_Mul)
            [
              (App FpFromWord [Lit (Word64 (4606532999733750582w:word64))]);
              Var (Short  "x4")
            ])
          ]);
          (App FpFromWord [Lit (Word64 (4597933826605249357w:word64))])
        ]);
        (App FpFromWord [Lit (Word64 (4652007308841189376w:word64))])
      ])
    (Let (SOME "dot3")
      (App (FP_bop FP_Div)
        [
          (App (FP_bop FP_Add)
          [
            (App (FP_bop FP_Sub)
            [
              (App (FP_bop FP_Sub)
              [
                (App (FP_bop FP_Sub)
                [
                  (App (FP_bop FP_Mul)
                  [
                    (App FpFromWord [Lit (Word64 (4595354164738691537w:word64))]);
                    Var (Short  "x1")
                  ]);
                  (App (FP_bop FP_Mul)
                  [
                    (App FpFromWord [Lit (Word64 (4607178815920315512w:word64))]);
                    Var (Short  "x2")
                  ])
                ]);
                (App (FP_bop FP_Mul)
                [
                  (App FpFromWord [Lit (Word64 (4613497591377497686w:word64))]);
                  Var (Short  "x3")
                ])
              ]);
              (App (FP_bop FP_Mul)
              [
                (App FpFromWord [Lit (Word64 (4609482407129715520w:word64))]);
                Var (Short  "x4")
              ])
            ]);
            (App FpFromWord [Lit (Word64 (4604500975581881015w:word64))])
          ]);
          (App FpFromWord [Lit (Word64 (4652007308841189376w:word64))])
        ])
      (Let (SOME "dot4")
        (App (FP_bop FP_Div)
          [
            (App (FP_bop FP_Add)
            [
              (App (FP_bop FP_Add)
              [
                (App (FP_bop FP_Add)
                [
                  (App (FP_bop FP_Add)
                  [
                    (App (FP_bop FP_Mul)
                    [
                      (App FpFromWord [Lit (Word64 (4589982271103164010w:word64))]);
                      Var (Short  "x1")
                    ]);
                    (App (FP_bop FP_Mul)
                    [
                      (App FpFromWord [Lit (Word64 (4607217546877110898w:word64))]);
                      Var (Short  "x2")
                    ])
                  ]);
                  (App (FP_bop FP_Mul)
                  [
                    (App FpFromWord [Lit (Word64 (4611453182326652849w:word64))]);
                    Var (Short  "x3")
                  ])
                ]);
                (App (FP_bop FP_Mul)
                [
                  (App FpFromWord [Lit (Word64 (4608660950557683142w:word64))]);
                  Var (Short  "x4")
                ])
              ]);
              (App FpFromWord [Lit (Word64 (4605176515525986589w:word64))])
            ]);
            (App FpFromWord [Lit (Word64 (4652007308841189376w:word64))])
          ])
        (Let (SOME "layer1_1")
          (App (FP_bop FP_Mul)
            [
              (App (FP_bop FP_Add)
              [
                (App (FP_bop FP_Add)
                [
                  (App (FP_bop FP_Add)
                  [
                    (App (FP_bop FP_Add)
                    [
                      (App (FP_bop FP_Mul)
                      [
                        (App (FP_bop FP_Mul)
                        [
                          (App (FP_bop FP_Mul)
                          [
                            (App (FP_bop FP_Mul)
                            [
                              (App FpFromWord [Lit (Word64 (-4622919338331026848w:word64))]);
                              Var (Short  "dot1")
                            ]);
                            Var (Short  "dot1")
                          ]);
                          Var (Short  "dot1")
                        ]);
                        Var (Short  "dot1")
                      ]);
                      (App (FP_bop FP_Mul)
                      [
                        (App (FP_bop FP_Mul)
                        [
                          (App (FP_bop FP_Mul)
                          [
                            (App FpFromWord [Lit (Word64 (4578030308564393824w:word64))]);
                            Var (Short  "dot1")
                          ]);
                          Var (Short  "dot1")
                        ]);
                        Var (Short  "dot1")
                      ])
                    ]);
                    (App (FP_bop FP_Mul)
                    [
                      (App (FP_bop FP_Mul)
                      [
                        (App FpFromWord [Lit (Word64 (4605375934827414562w:word64))]);
                        Var (Short  "dot1")
                      ]);
                      Var (Short  "dot1")
                    ])
                  ]);
                  (App (FP_bop FP_Mul)
                  [
                    (App FpFromWord [Lit (Word64 (4602544837263876625w:word64))]);
                    Var (Short  "dot1")
                  ])
                ]);
                (App FpFromWord [Lit (Word64 (4588679636976576441w:word64))])
              ]);
              (App FpFromWord [Lit (Word64 (4652007308841189376w:word64))])
            ])
          (Let (SOME "layer1_2")
            (App (FP_bop FP_Mul)
              [
                (App (FP_bop FP_Add)
                [
                  (App (FP_bop FP_Add)
                  [
                    (App (FP_bop FP_Add)
                    [
                      (App (FP_bop FP_Add)
                      [
                        (App (FP_bop FP_Mul)
                        [
                          (App (FP_bop FP_Mul)
                          [
                            (App (FP_bop FP_Mul)
                            [
                              (App (FP_bop FP_Mul)
                              [
                                (App FpFromWord [Lit (Word64 (-4622919338331026848w:word64))]);
                                Var (Short  "dot2")
                              ]);
                              Var (Short  "dot2")
                            ]);
                            Var (Short  "dot2")
                          ]);
                          Var (Short  "dot2")
                        ]);
                        (App (FP_bop FP_Mul)
                        [
                          (App (FP_bop FP_Mul)
                          [
                            (App (FP_bop FP_Mul)
                            [
                              (App FpFromWord [Lit (Word64 (4578030308564393824w:word64))]);
                              Var (Short  "dot2")
                            ]);
                            Var (Short  "dot2")
                          ]);
                          Var (Short  "dot2")
                        ])
                      ]);
                      (App (FP_bop FP_Mul)
                      [
                        (App (FP_bop FP_Mul)
                        [
                          (App FpFromWord [Lit (Word64 (4605375934827414562w:word64))]);
                          Var (Short  "dot2")
                        ]);
                        Var (Short  "dot2")
                      ])
                    ]);
                    (App (FP_bop FP_Mul)
                    [
                      (App FpFromWord [Lit (Word64 (4602544837263876625w:word64))]);
                      Var (Short  "dot2")
                    ])
                  ]);
                  (App FpFromWord [Lit (Word64 (4588679636976576441w:word64))])
                ]);
                (App FpFromWord [Lit (Word64 (4652007308841189376w:word64))])
              ])
            (Let (SOME "layer1_3")
              (App (FP_bop FP_Mul)
                [
                  (App (FP_bop FP_Add)
                  [
                    (App (FP_bop FP_Add)
                    [
                      (App (FP_bop FP_Add)
                      [
                        (App (FP_bop FP_Add)
                        [
                          (App (FP_bop FP_Mul)
                          [
                            (App (FP_bop FP_Mul)
                            [
                              (App (FP_bop FP_Mul)
                              [
                                (App (FP_bop FP_Mul)
                                [
                                  (App FpFromWord [Lit (Word64 (-4622919338331026848w:word64))]);
                                  Var (Short  "dot3")
                                ]);
                                Var (Short  "dot3")
                              ]);
                              Var (Short  "dot3")
                            ]);
                            Var (Short  "dot3")
                          ]);
                          (App (FP_bop FP_Mul)
                          [
                            (App (FP_bop FP_Mul)
                            [
                              (App (FP_bop FP_Mul)
                              [
                                (App FpFromWord [Lit (Word64 (4578030308564393824w:word64))]);
                                Var (Short  "dot3")
                              ]);
                              Var (Short  "dot3")
                            ]);
                            Var (Short  "dot3")
                          ])
                        ]);
                        (App (FP_bop FP_Mul)
                        [
                          (App (FP_bop FP_Mul)
                          [
                            (App FpFromWord [Lit (Word64 (4605375934827414562w:word64))]);
                            Var (Short  "dot3")
                          ]);
                          Var (Short  "dot3")
                        ])
                      ]);
                      (App (FP_bop FP_Mul)
                      [
                        (App FpFromWord [Lit (Word64 (4602544837263876625w:word64))]);
                        Var (Short  "dot3")
                      ])
                    ]);
                    (App FpFromWord [Lit (Word64 (4588679636976576441w:word64))])
                  ]);
                  (App FpFromWord [Lit (Word64 (4652007308841189376w:word64))])
                ])
              (Let (SOME "layer1_4")
                (App (FP_bop FP_Mul)
                  [
                    (App (FP_bop FP_Add)
                    [
                      (App (FP_bop FP_Add)
                      [
                        (App (FP_bop FP_Add)
                        [
                          (App (FP_bop FP_Add)
                          [
                            (App (FP_bop FP_Mul)
                            [
                              (App (FP_bop FP_Mul)
                              [
                                (App (FP_bop FP_Mul)
                                [
                                  (App (FP_bop FP_Mul)
                                  [
                                    (App FpFromWord [Lit (Word64 (-4622919338331026848w:word64))]);
                                    Var (Short  "dot4")
                                  ]);
                                  Var (Short  "dot4")
                                ]);
                                Var (Short  "dot4")
                              ]);
                              Var (Short  "dot4")
                            ]);
                            (App (FP_bop FP_Mul)
                            [
                              (App (FP_bop FP_Mul)
                              [
                                (App (FP_bop FP_Mul)
                                [
                                  (App FpFromWord [Lit (Word64 (4578030308564393824w:word64))]);
                                  Var (Short  "dot4")
                                ]);
                                Var (Short  "dot4")
                              ]);
                              Var (Short  "dot4")
                            ])
                          ]);
                          (App (FP_bop FP_Mul)
                          [
                            (App (FP_bop FP_Mul)
                            [
                              (App FpFromWord [Lit (Word64 (4605375934827414562w:word64))]);
                              Var (Short  "dot4")
                            ]);
                            Var (Short  "dot4")
                          ])
                        ]);
                        (App (FP_bop FP_Mul)
                        [
                          (App FpFromWord [Lit (Word64 (4602544837263876625w:word64))]);
                          Var (Short  "dot4")
                        ])
                      ]);
                      (App FpFromWord [Lit (Word64 (4588679636976576441w:word64))])
                    ]);
                    (App FpFromWord [Lit (Word64 (4652007308841189376w:word64))])
                  ])
                (Let (SOME "dot2_1")
                  (App (FP_bop FP_Sub)
                    [
                      (App (FP_bop FP_Sub)
                      [
                        (App (FP_bop FP_Add)
                        [
                          (App (FP_bop FP_Add)
                          [
                            (App (FP_bop FP_Mul)
                            [
                              (App FpFromWord [Lit (Word64 (-4627019874438658969w:word64))]);
                              Var (Short  "layer1_1")
                            ]);
                            (App (FP_bop FP_Mul)
                            [
                              (App FpFromWord [Lit (Word64 (4604393789910749597w:word64))]);
                              Var (Short  "layer1_2")
                            ])
                          ]);
                          (App (FP_bop FP_Mul)
                          [
                            (App FpFromWord [Lit (Word64 (4604380279111867485w:word64))]);
                            Var (Short  "layer1_3")
                          ])
                        ]);
                        (App (FP_bop FP_Mul)
                        [
                          (App FpFromWord [Lit (Word64 (4608008829331639894w:word64))]);
                          Var (Short  "layer1_4")
                        ])
                      ]);
                      (App FpFromWord [Lit (Word64 (4600288308490438653w:word64))])
                    ])
                  (Let (SOME "dot2_2")
                    (App (FP_bop FP_Add)
                      [
                        (App (FP_bop FP_Add)
                        [
                          (App (FP_bop FP_Sub)
                          [
                            (App (FP_bop FP_Add)
                            [
                              (App (FP_bop FP_Mul)
                              [
                                (App FpFromWord [Lit (Word64 (-4626313710017087275w:word64))]);
                                Var (Short  "layer1_1")
                              ]);
                              (App (FP_bop FP_Mul)
                              [
                                (App FpFromWord [Lit (Word64 (4582200050947067793w:word64))]);
                                Var (Short  "layer1_2")
                              ])
                            ]);
                            (App (FP_bop FP_Mul)
                            [
                              (App FpFromWord [Lit (Word64 (4607971449454732719w:word64))]);
                              Var (Short  "layer1_3")
                            ])
                          ]);
                          (App (FP_bop FP_Mul)
                          [
                            (App FpFromWord [Lit (Word64 (4608569527485247521w:word64))]);
                            Var (Short  "layer1_4")
                          ])
                        ]);
                        (App FpFromWord [Lit (Word64 (4598187829624233053w:word64))])
                      ])
                    (App (FP_bop FP_Sub)
                      [
                        Var (Short  "dot2_1");
                        Var (Short  "dot2_2")
                      ]))))))))))))))))]”;

Definition theAST_def:
  theAST =
  ^nn2Layer
End

(** Optimizations to be applied by Icing **)
Definition theOpts_def:
  theOpts = extend_conf no_fp_opt_conf
  [
    fp_sub_add;
    fp_comm_gen FP_Add;
    fp_neg_push_mul_r;
    fp_fma_intro
  ]
End

(** The code below stores in theorem theAST_opt the optimized version of the AST
    from above and in errorbounds_AST the inferred FloVer roundoff error bounds
 **)
Theorem theAST_opt =
  EVAL
    (Parse.Term ‘
      (source_to_source$no_opt_decs theOpts (source_to_source$stos_pass_decs theOpts
       theAST))’);

val nn2Layer_opt = theAST_opt |> concl |> rhs;

Definition theErrBound_def:
  theErrBound = inv (2 pow (10))
End

Definition theProg_def:
  theProg = ^nn2Layer
End

Definition theOptProg_def:
  theOptProg = ^nn2Layer_opt
End

val main =
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
                   App Opapp [Var (Short "nn2Layer"); Var (Short "d1")];
                   Var (Short "d2")];
                 Var (Short "d3")];
               Var (Short "d4")])
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
        (Let (SOME "b")
         (Fun "x"
          (Let NONE
           (App Opapp [
           App Opapp [
              App Opapp [
                App Opapp [Var (Short "nn2Layer"); Var (Short "d1")];
                Var (Short "d2")];
              Var (Short "d3")];
              Var (Short "d4")])
           (Con NONE [])))
         (App Opapp [
            App Opapp [
              App Opapp [Var (Short "iter"); Lit (IntLit ^iter_count)];
              Var (Short "u")]; Var (Short "b")]))))))])))]’;

Definition theBenchmarkMain_def:
  theBenchmarkMain =
  (HD (^iter_code)) :: (^call_code)
End

val st_no_nn2Layer = get_ml_prog_state ();

val nn2Layer_env = st_no_nn2Layer
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_env;

val _ = append_prog (theOptProg_def |> concl |> rhs)

val _ = append_prog main;

Definition nn2Layer_env:
  nn2Layer_env = ^nn2Layer_env
End

val _ =
  supportLib.write_code_to_file true theAST_def theAST_opt
(Parse.Term ‘APPEND ^(reader4_def |> concl |> rhs) (APPEND ^(intToFP_def |> concl |> rhs) (APPEND ^(printer_def |> concl |> rhs) ^(theBenchmarkMain_def |> concl |> rhs)))’)
    (Parse.Term ‘APPEND ^(reader4_def |> concl |> rhs) (APPEND ^(intToFP_def |> concl |> rhs) (APPEND ^(printer_def |> concl |> rhs) ^main))’)
    "nn2Layer";

val _ = export_theory();
