(**
  Support lemmas for CF proofs in the end-to-end correctness theorems
**)
open basis_ffiTheory cfHeapsBaseTheory basis;
open preamble;

val _ = new_theory "cfSupport";

Definition stripFuns_def:
  stripFuns (Fun var body):(((string, string) id) list# ast$exp)=
    (let (vars, body) = stripFuns body in
    (Short var :: vars, body)) ∧
  stripFuns e = ([], e)
End

Definition getDeclLetParts_def:
  getDeclLetParts [Dlet loc (Pvar fname) e] =
  let (vars, body) = stripFuns e in
  (fname, vars, body)
End

Definition reader1_def:
  reader1 =
    [Dletrec
     unknown_loc
     [("reader1","u",
       Let (SOME "a") (Con NONE [])
           (Let (SOME "cl")
            (App Opapp
             [Var (Long "CommandLine" (Short "arguments"));
              Var (Short "a")])
            (Let (SOME "cst1")
             (App Opapp
              [Var (Long "List" (Short "hd")); Var (Short "cl")])
             (Var (Short "cst1")))))]]
End

Definition reader2_def:
  reader2 =
  [Dletrec
   unknown_loc
   [("reader2","u",
     Let (SOME "a") (Con NONE [])
         (Let (SOME "cl")
          (App Opapp
           [Var (Long "CommandLine" (Short "arguments"));
            Var (Short "a")])
          (Let (SOME "cst1")
           (App Opapp
            [Var (Long "List" (Short "hd")); Var (Short "cl")])
           (Let (SOME "b")
            (App Opapp
             [Var (Long "List" (Short "tl")); Var (Short "cl")])
            (Let (SOME "cst2")
             (App Opapp
              [Var (Long "List" (Short "hd")); Var (Short "b")])
             (Con NONE [Var (Short "cst1"); Var (Short "cst2")]))))))]]
End

(**
   fun reader3 u =
   let
   val cl = CommandLine.arguments ();
   val cst1 = List.hd cl;
   val cst2 = List.hd (List.tl cl);
   val cst3 = List.hd (List.tl (List.tl cl));
   in (cst1, (cst2, cst3)) end;
**)
Definition reader3_def:
  reader3 =
  [Dletrec
   unknown_loc
   [("reader3","u",
     Let (SOME "a") (Con NONE [])
         (Let (SOME "cl")
          (App Opapp
           [Var (Long "CommandLine" (Short "arguments"));
            Var (Short "a")])
          (Let (SOME "cst1")
           (App Opapp
            [Var (Long "List" (Short "hd")); Var (Short "cl")])
           (Let (SOME "b")
            (App Opapp
             [Var (Long "List" (Short "tl")); Var (Short "cl")])
            (Let (SOME "cst2")
             (App Opapp
              [Var (Long "List" (Short "hd")); Var (Short "b")])
             (Let (SOME "c")
              (App Opapp
               [Var (Long "List" (Short "tl"));
                Var (Short "cl")])
              (Let (SOME "d")
               (App Opapp
                [Var (Long "List" (Short "tl"));
                 Var (Short "c")])
               (Let (SOME "cst3")
                (App Opapp
                 [Var (Long "List" (Short "hd"));
                  Var (Short "d")])
                (Let (SOME "e")
                 (Con NONE
                  [Var (Short "cst2");
                   Var (Short "cst3")])
                 (Con NONE
                  [Var (Short "cst1"); Var (Short "e")]))))))))))]]
End

(**
   fun reader4 u =
   let
   val cl = CommandLine.arguments ();
   val cst1 = List.hd cl;
   val cst2 = List.hd (List.tl cl);
   val cst3 = List.hd (List.tl (List.tl cl));
   val cst4 = List.hd (List.tl (List.tl (List.tl cl)));
   in (cst1, (cst2, (cst3, cst4))) end;
**)
Definition reader4_def:
  reader4 =
  [Dletrec unknown_loc
   [("reader4","u",
     Let (SOME "a") (Con NONE [])
         (Let (SOME "cl")
          (App Opapp
           [Var (Long "CommandLine" (Short "arguments"));
            Var (Short "a")])
          (Let (SOME "cst1")
           (App Opapp
            [Var (Long "List" (Short "hd")); Var (Short "cl")])
           (Let (SOME "b")
            (App Opapp
             [Var (Long "List" (Short "tl")); Var (Short "cl")])
            (Let (SOME "cst2")
             (App Opapp
              [Var (Long "List" (Short "hd")); Var (Short "b")])
             (Let (SOME "c")
              (App Opapp
               [Var (Long "List" (Short "tl"));
                Var (Short "cl")])
              (Let (SOME "d")
               (App Opapp
                [Var (Long "List" (Short "tl"));
                 Var (Short "c")])
               (Let (SOME "cst3")
                (App Opapp
                 [Var (Long "List" (Short "hd"));
                  Var (Short "d")])
                (Let (SOME "e")
                 (App Opapp
                  [Var (Long "List" (Short "tl"));
                   Var (Short "cl")])
                 (Let (SOME "f")
                  (App Opapp
                   [Var (Long "List" (Short "tl"));
                    Var (Short "e")])
                  (Let (SOME "g")
                   (App Opapp
                    [Var (Long "List" (Short "tl"));
                     Var (Short "f")])
                   (Let (SOME "cst4")
                    (App Opapp
                     [Var
                      (Long "List" (Short "hd"));
                      Var (Short "g")])
                    (Let (SOME "h")
                     (Con NONE
                      [Var (Short "cst3");
                       Var (Short "cst4")])
                     (Let (SOME "i")
                      (Con NONE
                       [Var (Short "cst2");
                        Var (Short "h")])
                      (Con NONE
                       [Var (Short "cst1");
                        Var (Short "i")])))))))))))))))]]
End

(**
   fun reader6 u =
   let
   val cl = CommandLine.arguments ();
   val cst1 = List.hd cl;
   val cst2 = List.hd (List.tl cl);
   val cst3 = List.hd (List.tl (List.tl cl));
   val cst4 = List.hd (List.tl (List.tl (List.tl cl)));
   val cst5 = List.hd (List.tl (List.tl (List.tl (List.tl cl))));
   val cst6 = List.hd (List.tl (List.tl (List.tl (List.tl (List.tl cl)))));
   in (cst1, (cst2, (cst3, (cst4, (cst5, cst6))))) end;
**)
Definition reader6_def:
  reader6 =
   [Dletrec unknown_loc
    [("reader6","u",
      Let (SOME "a") (Con NONE [])
          (Let (SOME "cl")
           (App Opapp
            [Var (Long "CommandLine" (Short "arguments"));
             Var (Short "a")])
           (Let (SOME "cst1")
            (App Opapp
             [Var (Long "List" (Short "hd")); Var (Short "cl")])
            (Let (SOME "b")
             (App Opapp
              [Var (Long "List" (Short "tl")); Var (Short "cl")])
             (Let (SOME "cst2")
              (App Opapp
               [Var (Long "List" (Short "hd")); Var (Short "b")])
              (Let (SOME "c")
               (App Opapp
                [Var (Long "List" (Short "tl"));
                 Var (Short "cl")])
               (Let (SOME "d")
                (App Opapp
                 [Var (Long "List" (Short "tl"));
                  Var (Short "c")])
                (Let (SOME "cst3")
                 (App Opapp
                  [Var (Long "List" (Short "hd"));
                   Var (Short "d")])
                 (Let (SOME "e")
                  (App Opapp
                   [Var (Long "List" (Short "tl"));
                    Var (Short "cl")])
                  (Let (SOME "f")
                   (App Opapp
                    [Var (Long "List" (Short "tl"));
                     Var (Short "e")])
                   (Let (SOME "g")
                    (App Opapp
                     [Var (Long "List" (Short "tl"));
                      Var (Short "f")])
                    (Let (SOME "cst4")
                     (App Opapp
                      [Var
                       (Long "List" (Short "hd"));
                       Var (Short "g")])
                     (Let (SOME "h")
                      (App Opapp
                       [Var
                        (Long "List"
                         (Short "tl"));
                        Var (Short "cl")])
                      (Let (SOME "i")
                       (App Opapp
                        [Var
                         (Long "List"
                          (Short "tl"));
                         Var (Short "h")])
                       (Let (SOME "j")
                        (App Opapp
                         [Var
                          (Long "List"
                           (Short "tl"));
                          Var (Short "i")])
                        (Let (SOME "k")
                         (App Opapp
                          [Var
                           (Long "List"
                            (Short "tl"));
                           Var (Short "j")])
                         (Let (SOME "cst5")
                          (App Opapp
                           [Var
                            (Long "List"
                             (Short
                              "hd"));
                            Var
                            (Short "k")])
                          (Let (SOME "l")
                           (App Opapp
                            [Var
                             (Long
                              "List"
                              (Short
                               "tl"));
                             Var
                             (Short
                              "cl")])
                           (Let (SOME "m")
                            (App Opapp
                             [Var
                              (Long
                               "List"
                               (Short
                                "tl"));
                              Var
                              (Short
                               "l")])
                            (Let
                             (SOME "n")
                             (App
                              Opapp
                              [Var
                               (Long
                                "List"
                                (Short
                                 "tl"));
                               Var
                               (Short
                                "m")])
                             (Let
                              (SOME
                               "o")
                              (App
                               Opapp
                               [Var
                                (Long
                                 "List"
                                 (Short
                                  "tl"));
                                Var
                                (Short
                                 "n")])
                              (Let
                               (SOME
                                "p")
                               (App
                                Opapp
                                [Var
                                 (Long
                                  "List"
                                  (Short
                                   "tl"));
                                 Var
                                 (Short
                                  "o")])
                               (Let
                                (SOME
                                 "cst6")
                                (App
                                 Opapp
                                 [Var
                                  (Long
                                   "List"
                                   (Short
                                    "hd"));
                                  Var
                                  (Short
                                   "p")])
                                (Let
                                 (SOME
                                  "q")
                                 (Con
                                  NONE
                                  [Var
                                   (Short
                                    "cst5");
                                   Var
                                   (Short
                                    "cst6")])
                                 (Let
                                  (SOME
                                   "r")
                                  (Con
                                   NONE
                                   [Var
                                    (Short
                                     "cst4");
                                    Var
                                    (Short
                                     "q")])
                                  (Let
                                   (SOME
                                    "s")
                                   (Con
                                    NONE
                                    [Var
                                     (Short
                                      "cst3");
                                     Var
                                     (Short
                                      "r")])
                                   (Let
                                    (SOME
                                     "t")
                                    (Con
                                     NONE
                                     [Var
                                      (Short
                                       "cst2");
                                      Var
                                      (Short
                                       "s")])
                                    (Con
                                     NONE
                                     [Var
                                      (Short
                                       "cst1");
                                      Var
                                      (Short
                                       "t")]))))))))))))))))))))))))))))]]
End

(**
fun reader8 u =
   let
   val cl = CommandLine.arguments ();
   val cst1 = List.hd cl;
   val cst2 = List.hd (List.tl cl);
   val cst3 = List.hd (List.tl (List.tl cl));
   val cst4 = List.hd (List.tl (List.tl (List.tl cl)));
   val cst5 = List.hd (List.tl (List.tl (List.tl (List.tl cl))));
   val cst6 = List.hd (List.tl (List.tl (List.tl (List.tl (List.tl cl)))));
   val cst7 = List.hd (List.tl (List.tl (List.tl (List.tl (List.tl (List.tl cl))))));
   val cst8 = List.hd (List.tl (List.tl (List.tl (List.tl (List.tl (List.tl (List.tl cl)))))));
   in (cst1, (cst2, (cst3, (cst4, (cst5, (cst6, (cst7, cst8))))))) end;
**)
Definition reader8_def:
  reader8 =
  [Dletrec unknown_loc
   [("reader8","u",
     Let (SOME "a") (Con NONE [])
         (Let (SOME "cl")
          (App Opapp
           [Var (Long "CommandLine" (Short "arguments"));
            Var (Short "a")])
          (Let (SOME "cst1")
           (App Opapp
            [Var (Long "List" (Short "hd")); Var (Short "cl")])
           (Let (SOME "b")
            (App Opapp
             [Var (Long "List" (Short "tl")); Var (Short "cl")])
            (Let (SOME "cst2")
             (App Opapp
              [Var (Long "List" (Short "hd")); Var (Short "b")])
             (Let (SOME "c")
              (App Opapp
               [Var (Long "List" (Short "tl"));
                Var (Short "cl")])
              (Let (SOME "d")
               (App Opapp
                [Var (Long "List" (Short "tl"));
                 Var (Short "c")])
               (Let (SOME "cst3")
                (App Opapp
                 [Var (Long "List" (Short "hd"));
                  Var (Short "d")])
                (Let (SOME "e")
                 (App Opapp
                  [Var (Long "List" (Short "tl"));
                   Var (Short "cl")])
                 (Let (SOME "f")
                  (App Opapp
                   [Var (Long "List" (Short "tl"));
                    Var (Short "e")])
                  (Let (SOME "g")
                   (App Opapp
                    [Var (Long "List" (Short "tl"));
                     Var (Short "f")])
                   (Let (SOME "cst4")
                    (App Opapp
                     [Var
                      (Long "List" (Short "hd"));
                      Var (Short "g")])
                    (Let (SOME "h")
                     (App Opapp
                      [Var
                       (Long "List"
                        (Short "tl"));
                       Var (Short "cl")])
                     (Let (SOME "i")
                      (App Opapp
                       [Var
                        (Long "List"
                         (Short "tl"));
                        Var (Short "h")])
                      (Let (SOME "j")
                       (App Opapp
                        [Var
                         (Long "List"
                          (Short "tl"));
                         Var (Short "i")])
                       (Let (SOME "k")
                        (App Opapp
                         [Var
                          (Long "List"
                           (Short "tl"));
                          Var (Short "j")])
                        (Let (SOME "cst5")
                         (App Opapp
                          [Var
                           (Long "List"
                            (Short
                             "hd"));
                           Var
                           (Short "k")])
                         (Let (SOME "l")
                          (App Opapp
                           [Var
                            (Long
                             "List"
                             (Short
                              "tl"));
                            Var
                            (Short
                             "cl")])
                          (Let (SOME "m")
                           (App Opapp
                            [Var
                             (Long
                              "List"
                              (Short
                               "tl"));
                             Var
                             (Short
                              "l")])
                           (Let
                            (SOME "n")
                            (App
                             Opapp
                             [Var
                              (Long
                               "List"
                               (Short
                                "tl"));
                              Var
                              (Short
                               "m")])
                            (Let
                             (SOME
                              "o")
                             (App
                              Opapp
                              [Var
                               (Long
                                "List"
                                (Short
                                 "tl"));
                               Var
                               (Short
                                "n")])
                             (Let
                              (SOME
                               "p")
                              (App
                               Opapp
                               [Var
                                (Long
                                 "List"
                                 (Short
                                  "tl"));
                                Var
                                (Short
                                 "o")])
                              (Let
                               (SOME
                                "cst6")
                               (App
                                Opapp
                                [Var
                                 (Long
                                  "List"
                                  (Short
                                   "hd"));
                                 Var
                                 (Short
                                  "p")])
                               (Let
                                (SOME
                                 "q")
                                (App
                                 Opapp
                                 [Var
                                  (Long
                                   "List"
                                   (Short
                                    "tl"));
                                  Var
                                  (Short
                                   "cl")])
                                (Let
                                 (SOME
                                  "r")
                                 (App
                                  Opapp
                                  [Var
                                   (Long
                                    "List"
                                    (Short
                                     "tl"));
                                   Var
                                   (Short
                                    "q")])
                                 (Let
                                  (SOME
                                   "s")
                                  (App
                                   Opapp
                                   [Var
                                    (Long
                                     "List"
                                     (Short
                                      "tl"));
                                    Var
                                    (Short
                                     "r")])
                                  (Let
                                   (SOME
                                    "t")
                                   (App
                                    Opapp
                                    [Var
                                     (Long
                                      "List"
                                      (Short
                                       "tl"));
                                     Var
                                     (Short
                                      "s")])
                                   (Let
                                    (SOME
                                     "v")
                                    (App
                                     Opapp
                                     [Var
                                      (Long
                                       "List"
                                       (Short
                                        "tl"));
                                      Var
                                      (Short
                                       "t")])
                                    (Let
                                     (SOME
                                      "w")
                                     (App
                                      Opapp
                                      [Var
                                       (Long
                                        "List"
                                        (Short
                                         "tl"));
                                       Var
                                       (Short
                                        "v")])
                                     (Let
                                      (SOME
                                       "cst7")
                                      (App
                                       Opapp
                                       [Var
                                        (Long
                                         "List"
                                         (Short
                                          "hd"));
                                        Var
                                        (Short
                                         "w")])
                                      (Let
                                       (SOME
                                        "x")
                                       (App
                                        Opapp
                                        [Var
                                         (Long
                                          "List"
                                          (Short
                                           "tl"));
                                         Var
                                         (Short
                                          "cl")])
                                       (Let
                                        (SOME
                                         "y")
                                        (App
                                         Opapp
                                         [Var
                                          (Long
                                           "List"
                                           (Short
                                            "tl"));
                                          Var
                                          (Short
                                           "x")])
                                        (Let
                                         (SOME
                                          "z")
                                         (App
                                          Opapp
                                          [Var
                                           (Long
                                            "List"
                                            (Short
                                             "tl"));
                                           Var
                                           (Short
                                            "y")])
                                         (Let
                                          (SOME
                                           "t0")
                                          (App
                                           Opapp
                                           [Var
                                            (Long
                                             "List"
                                             (Short
                                              "tl"));
                                            Var
                                            (Short
                                             "z")])
                                          (Let
                                           (SOME
                                            "t1")
                                           (App
                                            Opapp
                                            [Var
                                             (Long
                                              "List"
                                              (Short
                                               "tl"));
                                             Var
                                             (Short
                                              "t0")])
                                           (Let
                                            (SOME
                                             "t2")
                                            (App
                                             Opapp
                                             [Var
                                              (Long
                                               "List"
                                               (Short
                                                "tl"));
                                              Var
                                              (Short
                                               "t1")])
                                            (Let
                                             (SOME
                                              "t3")
                                             (App
                                              Opapp
                                              [Var
                                               (Long
                                                "List"
                                                (Short
                                                 "tl"));
                                               Var
                                               (Short
                                                "t2")])
                                             (Let
                                              (SOME
                                               "cst8")
                                              (App
                                               Opapp
                                               [Var
                                                (Long
                                                 "List"
                                                 (Short
                                                  "hd"));
                                                Var
                                                (Short
                                                 "t3")])
                                              (Let
                                               (SOME
                                                "t4")
                                               (Con
                                                NONE
                                                [Var
                                                 (Short
                                                  "cst7");
                                                 Var
                                                 (Short
                                                  "cst8")])
                                               (Let
                                                (SOME
                                                 "t5")
                                                (Con
                                                 NONE
                                                 [Var
                                                  (Short
                                                   "cst6");
                                                  Var
                                                  (Short
                                                   "t4")])
                                                (Let
                                                 (SOME
                                                  "t6")
                                                 (Con
                                                  NONE
                                                  [Var
                                                   (Short
                                                    "cst5");
                                                   Var
                                                   (Short
                                                    "t5")])
                                                 (Let
                                                  (SOME
                                                   "t7")
                                                  (Con
                                                   NONE
                                                   [Var
                                                    (Short
                                                     "cst4");
                                                    Var
                                                    (Short
                                                     "t6")])
                                                  (Let
                                                   (SOME
                                                    "t8")
                                                   (Con
                                                    NONE
                                                    [Var
                                                     (Short
                                                      "cst3");
                                                     Var
                                                     (Short
                                                      "t7")])
                                                   (Let
                                                    (SOME
                                                     "t9")
                                                    (Con
                                                     NONE
                                                     [Var
                                                      (Short
                                                       "cst2");
                                                      Var
                                                      (Short
                                                       "t8")])
                                                    (Con
                                                     NONE
                                                     [Var
                                                      (Short
                                                       "cst1");
                                                      Var
                                                      (Short
                                                       "t9")])))))))))))))))))))))))))))))))))))))))))))))]]
End

(**
fun reader8 u =
   let
   val cl = CommandLine.arguments ();
   val cst1 = List.hd cl;
   val cst2 = List.hd (List.tl cl);
   val cst3 = List.hd (List.tl (List.tl cl));
   val cst4 = List.hd (List.tl (List.tl (List.tl cl)));
   val cst5 = List.hd (List.tl (List.tl (List.tl (List.tl cl))));
   val cst6 = List.hd (List.tl (List.tl (List.tl (List.tl (List.tl cl)))));
   val cst7 = List.hd (List.tl (List.tl (List.tl (List.tl (List.tl (List.tl cl))))));
   val cst8 = List.hd (List.tl (List.tl (List.tl (List.tl (List.tl (List.tl (List.tl cl)))))));
   val cst9 = List.hd (List.tl (List.tl (List.tl (List.tl (List.tl (List.tl (List.tl (List.tl cl))))))));
   in (cst1, (cst2, (cst3, (cst4, (cst5, (cst6, (cst7, (cst8, cst9)))))))) end;
**)
Definition reader9_def:
  reader9 =
  [Dletrec unknown_loc
   [("reader9","u",
     Let (SOME "a") (Con NONE [])
         (Let (SOME "cl")
          (App Opapp
           [Var (Long "CommandLine" (Short "arguments"));
            Var (Short "a")])
          (Let (SOME "cst1")
           (App Opapp
            [Var (Long "List" (Short "hd")); Var (Short "cl")])
           (Let (SOME "b")
            (App Opapp
             [Var (Long "List" (Short "tl")); Var (Short "cl")])
            (Let (SOME "cst2")
             (App Opapp
              [Var (Long "List" (Short "hd")); Var (Short "b")])
             (Let (SOME "c")
              (App Opapp
               [Var (Long "List" (Short "tl"));
                Var (Short "cl")])
              (Let (SOME "d")
               (App Opapp
                [Var (Long "List" (Short "tl"));
                 Var (Short "c")])
               (Let (SOME "cst3")
                (App Opapp
                 [Var (Long "List" (Short "hd"));
                  Var (Short "d")])
                (Let (SOME "e")
                 (App Opapp
                  [Var (Long "List" (Short "tl"));
                   Var (Short "cl")])
                 (Let (SOME "f")
                  (App Opapp
                   [Var (Long "List" (Short "tl"));
                    Var (Short "e")])
                  (Let (SOME "g")
                   (App Opapp
                    [Var (Long "List" (Short "tl"));
                     Var (Short "f")])
                   (Let (SOME "cst4")
                    (App Opapp
                     [Var
                      (Long "List" (Short "hd"));
                      Var (Short "g")])
                    (Let (SOME "h")
                     (App Opapp
                      [Var
                       (Long "List"
                        (Short "tl"));
                       Var (Short "cl")])
                     (Let (SOME "i")
                      (App Opapp
                       [Var
                        (Long "List"
                         (Short "tl"));
                        Var (Short "h")])
                      (Let (SOME "j")
                       (App Opapp
                        [Var
                         (Long "List"
                          (Short "tl"));
                         Var (Short "i")])
                       (Let (SOME "k")
                        (App Opapp
                         [Var
                          (Long "List"
                           (Short "tl"));
                          Var (Short "j")])
                        (Let (SOME "cst5")
                         (App Opapp
                          [Var
                           (Long "List"
                            (Short
                             "hd"));
                           Var
                           (Short "k")])
                         (Let (SOME "l")
                          (App Opapp
                           [Var
                            (Long
                             "List"
                             (Short
                              "tl"));
                            Var
                            (Short
                             "cl")])
                          (Let (SOME "m")
                           (App Opapp
                            [Var
                             (Long
                              "List"
                              (Short
                               "tl"));
                             Var
                             (Short
                              "l")])
                           (Let
                            (SOME "n")
                            (App
                             Opapp
                             [Var
                              (Long
                               "List"
                               (Short
                                "tl"));
                              Var
                              (Short
                               "m")])
                            (Let
                             (SOME
                              "o")
                             (App
                              Opapp
                              [Var
                               (Long
                                "List"
                                (Short
                                 "tl"));
                               Var
                               (Short
                                "n")])
                             (Let
                              (SOME
                               "p")
                              (App
                               Opapp
                               [Var
                                (Long
                                 "List"
                                 (Short
                                  "tl"));
                                Var
                                (Short
                                 "o")])
                              (Let
                               (SOME
                                "cst6")
                               (App
                                Opapp
                                [Var
                                 (Long
                                  "List"
                                  (Short
                                   "hd"));
                                 Var
                                 (Short
                                  "p")])
                               (Let
                                (SOME
                                 "q")
                                (App
                                 Opapp
                                 [Var
                                  (Long
                                   "List"
                                   (Short
                                    "tl"));
                                  Var
                                  (Short
                                   "cl")])
                                (Let
                                 (SOME
                                  "r")
                                 (App
                                  Opapp
                                  [Var
                                   (Long
                                    "List"
                                    (Short
                                     "tl"));
                                   Var
                                   (Short
                                    "q")])
                                 (Let
                                  (SOME
                                   "s")
                                  (App
                                   Opapp
                                   [Var
                                    (Long
                                     "List"
                                     (Short
                                      "tl"));
                                    Var
                                    (Short
                                     "r")])
                                  (Let
                                   (SOME
                                    "t")
                                   (App
                                    Opapp
                                    [Var
                                     (Long
                                      "List"
                                      (Short
                                       "tl"));
                                     Var
                                     (Short
                                      "s")])
                                   (Let
                                    (SOME
                                     "v")
                                    (App
                                     Opapp
                                     [Var
                                      (Long
                                       "List"
                                       (Short
                                        "tl"));
                                      Var
                                      (Short
                                       "t")])
                                    (Let
                                     (SOME
                                      "w")
                                     (App
                                      Opapp
                                      [Var
                                       (Long
                                        "List"
                                        (Short
                                         "tl"));
                                       Var
                                       (Short
                                        "v")])
                                     (Let
                                      (SOME
                                       "cst7")
                                      (App
                                       Opapp
                                       [Var
                                        (Long
                                         "List"
                                         (Short
                                          "hd"));
                                        Var
                                        (Short
                                         "w")])
                                      (Let
                                       (SOME
                                        "x")
                                       (App
                                        Opapp
                                        [Var
                                         (Long
                                          "List"
                                          (Short
                                           "tl"));
                                         Var
                                         (Short
                                          "cl")])
                                       (Let
                                        (SOME
                                         "y")
                                        (App
                                         Opapp
                                         [Var
                                          (Long
                                           "List"
                                           (Short
                                            "tl"));
                                          Var
                                          (Short
                                           "x")])
                                        (Let
                                         (SOME
                                          "z")
                                         (App
                                          Opapp
                                          [Var
                                           (Long
                                            "List"
                                            (Short
                                             "tl"));
                                           Var
                                           (Short
                                            "y")])
                                         (Let
                                          (SOME
                                           "t0")
                                          (App
                                           Opapp
                                           [Var
                                            (Long
                                             "List"
                                             (Short
                                              "tl"));
                                            Var
                                            (Short
                                             "z")])
                                          (Let
                                           (SOME
                                            "t1")
                                           (App
                                            Opapp
                                            [Var
                                             (Long
                                              "List"
                                              (Short
                                               "tl"));
                                             Var
                                             (Short
                                              "t0")])
                                           (Let
                                            (SOME
                                             "t2")
                                            (App
                                             Opapp
                                             [Var
                                              (Long
                                               "List"
                                               (Short
                                                "tl"));
                                              Var
                                              (Short
                                               "t1")])
                                            (Let
                                             (SOME
                                              "t3")
                                             (App
                                              Opapp
                                              [Var
                                               (Long
                                                "List"
                                                (Short
                                                 "tl"));
                                               Var
                                               (Short
                                                "t2")])
                                             (Let
                                              (SOME
                                               "cst8")
                                              (App
                                               Opapp
                                               [Var
                                                (Long
                                                 "List"
                                                 (Short
                                                  "hd"));
                                                Var
                                                (Short
                                                 "t3")])
                                              (Let
                                               (SOME
                                                "t4")
                                               (App
                                                Opapp
                                                [Var
                                                 (Long
                                                  "List"
                                                  (Short
                                                   "tl"));
                                                 Var
                                                 (Short
                                                  "cl")])
                                               (Let
                                                (SOME
                                                 "t5")
                                                (App
                                                 Opapp
                                                 [Var
                                                  (Long
                                                   "List"
                                                   (Short
                                                    "tl"));
                                                  Var
                                                  (Short
                                                   "t4")])
                                                (Let
                                                 (SOME
                                                  "t6")
                                                 (App
                                                  Opapp
                                                  [Var
                                                   (Long
                                                    "List"
                                                    (Short
                                                     "tl"));
                                                   Var
                                                   (Short
                                                    "t5")])
                                                 (Let
                                                  (SOME
                                                   "t7")
                                                  (App
                                                   Opapp
                                                   [Var
                                                    (Long
                                                     "List"
                                                     (Short
                                                      "tl"));
                                                    Var
                                                    (Short
                                                     "t6")])
                                                  (Let
                                                   (SOME
                                                    "t8")
                                                   (App
                                                    Opapp
                                                    [Var
                                                     (Long
                                                      "List"
                                                      (Short
                                                       "tl"));
                                                     Var
                                                     (Short
                                                      "t7")])
                                                   (Let
                                                    (SOME
                                                     "t9")
                                                    (App
                                                     Opapp
                                                     [Var
                                                      (Long
                                                       "List"
                                                       (Short
                                                        "tl"));
                                                      Var
                                                      (Short
                                                       "t8")])
                                                    (Let
                                                     (SOME
                                                      "t10")
                                                     (App
                                                      Opapp
                                                      [Var
                                                       (Long
                                                        "List"
                                                        (Short
                                                         "tl"));
                                                       Var
                                                       (Short
                                                        "t9")])
                                                     (Let
                                                      (SOME
                                                       "t11")
                                                      (App
                                                       Opapp
                                                       [Var
                                                        (Long
                                                         "List"
                                                         (Short
                                                          "tl"));
                                                        Var
                                                        (Short
                                                         "t10")])
                                                      (Let
                                                       (SOME
                                                        "cst9")
                                                       (App
                                                        Opapp
                                                        [Var
                                                         (Long
                                                          "List"
                                                          (Short
                                                           "hd"));
                                                         Var
                                                         (Short
                                                          "t11")])
                                                       (Let
                                                        (SOME
                                                         "t12")
                                                        (Con
                                                         NONE
                                                         [Var
                                                          (Short
                                                           "cst8");
                                                          Var
                                                          (Short
                                                           "cst9")])
                                                        (Let
                                                         (SOME
                                                          "t13")
                                                         (Con
                                                          NONE
                                                          [Var
                                                           (Short
                                                            "cst7");
                                                           Var
                                                           (Short
                                                            "t12")])
                                                         (Let
                                                          (SOME
                                                           "t14")
                                                          (Con
                                                           NONE
                                                           [Var
                                                            (Short
                                                             "cst6");
                                                            Var
                                                            (Short
                                                             "t13")])
                                                          (Let
                                                           (SOME
                                                            "t15")
                                                           (Con
                                                            NONE
                                                            [Var
                                                             (Short
                                                              "cst5");
                                                             Var
                                                             (Short
                                                              "t14")])
                                                           (Let
                                                            (SOME
                                                             "t16")
                                                            (Con
                                                             NONE
                                                             [Var
                                                              (Short
                                                               "cst4");
                                                              Var
                                                              (Short
                                                               "t15")])
                                                            (Let
                                                             (SOME
                                                              "t17")
                                                             (Con
                                                              NONE
                                                              [Var
                                                               (Short
                                                                "cst3");
                                                               Var
                                                               (Short
                                                                "t16")])
                                                             (Let
                                                              (SOME
                                                               "t18")
                                                              (Con
                                                               NONE
                                                               [Var
                                                                (Short
                                                                 "cst2");
                                                                Var
                                                                (Short
                                                                 "t17")])
                                                              (Con
                                                               NONE
                                                               [Var
                                                                (Short
                                                                 "cst1");
                                                                Var
                                                                (Short
                                                                 "t18")])))))))))))))))))))))))))))))))))))))))))))))))))))))))]]
End

Definition printer_def:
  printer =
  [Dlet unknown_loc (Pvar "printer")
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
          Var (Short "y")]))))]
End

Definition intToFP_def:
  intToFP =
  [Dlet unknown_loc (Pvar "intToFP")
    (Fun "s"
     (Let (SOME "io")
      (App Opapp [Var (Long "Int" (Short "fromString")); Var (Short "s")])
      (Let (SOME "i")
       (App Opapp [Var (Long "Option" (Short "valOf")); Var (Short ("io"))])
       (Let (SOME "w")
        (App Opapp [Var (Long "Word64" (Short "fromInt")); Var (Short "i")])
        (App FpFromWord [Var (Short "w")])))))]
End

val _ = export_theory();
