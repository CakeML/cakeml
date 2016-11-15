open HolKernel boolLib bossLib lcsymtacs;
open x64_compileLib x64_exportLib
open helloProgTheory

val _ = new_theory "benchmark"

val rconc = rhs o concl

val _ = PolyML.timing true;
val _ = Globals.max_print_depth := 20;
val _ = PolyML.print_depth 5;

fun println s = print (strcat s "\n");

fun to_bytes alg conf prog =
  let
  val _ = println "Compile to livesets"
  val init = Count.apply eval``to_livesets ^(conf) ^(prog)``
  val _ = println "External oracle"
  val oracles = reg_allocComputeLib.get_oracle alg (fst (pairSyntax.dest_pair (rconc init)))
  val wc = ``<|reg_alg:=3;col_oracle:= ^(oracles)|>``
  val _ = println "Repeat compilation with oracle"
  (*This repeats the "to_livesets" step, but that isn't very costly*)
  val compile_thm = Count.apply eval``
    compile (^(conf) with word_to_word_conf := ^(wc)) ^(prog)``
  (* Alternatively: we can use the theories to manipulate init directly
  however, running the simplifier on the result takes quite long as well
  val rw = backendTheory.to_livesets_invariant |> SIMP_RULE std_ss[LET_THM]
   |> GEN_ALL |> ISPECL [wc,prog,``x64_compiler_config``]
   |> ONCE_REWRITE_RULE[init] |> SIMP_RULE std_ss []
  val test2 = Count.apply eval``
    let (rcm,c,p) = ^(rconc init) in
    from_livesets (rcm,c with word_to_word_conf:= ^(wc),p)``
   *)
  in
    compile_thm
  end

val qsortimp =``
[Tdec
  (Dletrec
     [("swap","i",
       Fun "j"
         (Fun "arr"
            (Let (SOME "ti")
               (App Asub [Var (Short "arr"); Var (Short "i")])
               (Let (SOME "tj")
                  (App Asub [Var (Short "arr"); Var (Short "j")])
                  (Let (SOME "d")
                     (App Aupdate [Var (Short "arr");Var (Short "i"); Var (Short "tj")])
                     (Let (SOME "d")
                        (App Aupdate [Var (Short "arr");Var (Short "j"); Var (Short "ti")])
                        (Var (Short "arr"))))))))]);
Tdec
  (Dletrec
     [("part_loop","i",
       Fun "j"
         (Fun "k"
            (Fun "arr"
               (If
                  (App (Opb Lt) [Var (Short "i"); Var (Short "j")])
                  (If
                     (App (Opb Leq) [App Asub [Var (Short "arr"); Var (Short "i")]; Var (Short "k")])
                     (App Opapp
                        [App Opapp
                           [App Opapp
                              [App Opapp
                                 [Var (Short "part_loop");
                                  App (Opn Plus) [Var (Short "i");Lit (IntLit 1)]];
                               Var (Short "j")]; Var (Short "k")];
                         Var (Short "arr")])
                     (Let (SOME "arr")
                        (App Opapp
                           [App Opapp
                              [App Opapp
                                 [Var (Short "swap");
                                  Var (Short "i")];
                               App (Opn Minus) [Var (Short "j"); Lit (IntLit 1)]];
                            Var (Short "arr")])
                        (App Opapp
                           [App Opapp
                              [App Opapp
                                 [App Opapp
                                    [Var (Short "part_loop");
                                     Var (Short "i")];
                                  App (Opn Minus) [Var (Short "j"); Lit (IntLit 1)]];
                               Var (Short "k")];
                            Var (Short "arr")])))
                  (Con NONE
                     [Var (Short "i"); Var (Short "arr")])))))]);
Tdec
  (Dletrec
     [("inplace_partition","b",
       Fun "e"
         (Fun "arr"
            (Let (SOME "k")
               (App Opapp
                  [App Opapp
                     [Var (Long "Array" "sub");
                      Var (Short "arr")]; Var (Short "b")])
               (Let (SOME "res")
                  (App Opapp
                     [App Opapp
                        [App Opapp
                           [App Opapp
                              [Var (Short "part_loop");
                               App (Opn Plus) [Var (Short "b"); Lit (IntLit 1)]];
                            Var (Short "e")]; Var (Short "k")];
                      Var (Short "arr")])
                  (Mat (Var (Short "res"))
                     [(Pcon NONE [Pvar "i"; Pvar "arr"],
                       Let (SOME "arr")
                         (App Opapp
                            [App Opapp
                               [App Opapp
                                  [Var (Short "swap");
                                   Var (Short "b")];
                                App (Opn Minus) [Var (Short "i"); Lit (IntLit 1)]];
                             Var (Short "arr")])
                         (Con NONE
                            [App (Opn Minus) [Var (Short "i"); Lit (IntLit 1)];
                             Var (Short "arr")]))])))))]);
Tdec
  (Dletrec
     [("inplace_qsort","b",
       Fun "e"
         (Fun "arr"
            (If
               (App (Opb Lt) [App (Opn Plus) [Var (Short "b"); Lit (IntLit 1)]; Var (Short "e")])
               (Let (SOME "res")
                  (App Opapp
                     [App Opapp
                        [App Opapp
                           [Var (Short "inplace_partition");
                            Var (Short "b")]; Var (Short "e")];
                      Var (Short "arr")])
                  (Mat (Var (Short "res"))
                     [(Pcon NONE [Pvar "i"; Pvar "arr"],
                       Let (SOME "arr")
                         (App Opapp
                            [App Opapp
                               [App Opapp
                                  [Var (Short "inplace_qsort");
                                   Var (Short "b")];
                                Var (Short "i")];
                             Var (Short "arr")])
                         (Let (SOME "arr")
                            (App Opapp
                               [App Opapp
                                  [App Opapp
                                     [Var (Short "inplace_qsort");
                                      App (Opn Plus) [Var (Short "i"); Lit (IntLit 1)]];
                                   Var (Short "e")];
                                Var (Short "arr")])
                            (Var (Short "arr"))))]))
               (Var (Short "arr")))))]);
Tdec
  (Dletrec
     [("initarr","len",
       Fun "arr"
         (Fun "n"
            (If
               (App Equality [Var (Short "n"); Var (Short "len")])
               (Var (Short "arr"))
               (Let (SOME "u")
                  (App Aupdate [Var (Short "arr"); Var (Short "n");
                      App (Opn Minus) [Var (Short "len"); Var (Short "n")]])
                  (Let (SOME "u")
                     (App Aupdate [Var (Short "arr"); App (Opn Plus) [Var (Short "n"); Var (Short "len")];App (Opn Minus) [Var (Short "len"); Var (Short "n")]])
                     (App Opapp
                        [App Opapp
                           [App Opapp
                              [Var (Short "initarr");
                               Var (Short "len")];
                            Var (Short "arr")];
                         App (Opn Plus) [Var (Short "n"); Lit (IntLit 1)]]))))))]);
Tdec
  (Dletrec
     [("mkarr","n",
       App Opapp
         [App Opapp
            [App Opapp [Var (Short "initarr"); Var (Short "n")];
             App Aalloc [App (Opn Plus) [Var (Short "n"); Var (Short "n")]; Lit (IntLit 0)]];
          Lit (IntLit 0)])]);
Tdec
  (Dlet (Pvar "test")
     (App Opapp
        [App Opapp
           [App Opapp
              [Var (Short "inplace_qsort"); Lit (IntLit 0)];
            Lit (IntLit 40000)];
         App Opapp [Var (Short "mkarr"); Lit (IntLit 20000)]]))]``

val btree = ``
[Tdec
  (Dtype
     [([],"tree",
       [("Leaf",[]);
        ("Branch",
         [Tapp [] (TC_name (Short "tree"));
          Tapp [] (TC_int);
          Tapp [] (TC_name (Short "tree"))])])]);
Tdec
  (Dletrec
     [("insert","x",
       Fun "t"
         (Mat (Var (Short "t"))
            [(Pcon (SOME (Short "Leaf")) [],
              Con (SOME (Short "Branch"))
                [Con (SOME (Short "Leaf")) []; Var (Short "x");
                 Con (SOME (Short "Leaf")) []]);
             (Pcon (SOME (Short "Branch"))
                [Pvar "t1"; Pvar "y"; Pvar "t2"],
              If
                (App (Opb Lt) [Var (Short "x"); Var (Short "y")])
                (Con (SOME (Short "Branch"))
                   [App Opapp
                      [App Opapp
                         [Var (Short "insert"); Var (Short "x")];
                       Var (Short "t1")]; Var (Short "y");
                    Var (Short "t2")])
                (If
                   (App (Opb Lt) [Var (Short "y"); Var (Short "x")])
                   (Con (SOME (Short "Branch"))
                      [Var (Short "t1"); Var (Short "y");
                       App Opapp
                         [App Opapp
                            [Var (Short "insert");
                             Var (Short "x")]; Var (Short "t2")]])
                   (Con (SOME (Short "Branch"))
                      [Var (Short "t1"); Var (Short "y");
                       Var (Short "t2")])))]))]);
Tdec
  (Dletrec
     [("build_tree","l",
       Mat (Var (Short "l"))
         [(Pcon (SOME (Short "nil")) [],
           Con (SOME (Short "Leaf")) []);
          (Pcon (SOME (Short "::")) [Pvar "x"; Pvar "xs"],
           App Opapp
             [App Opapp [Var (Short "insert"); Var (Short "x")];
              App Opapp
                [Var (Short "build_tree");
                 Var (Short "xs")]])])]);
Tdec
  (Dletrec
     [("append","l",
       Fun "ys"
         (Mat (Var (Short "l"))
            [(Pcon (SOME (Short "nil")) [],Var (Short "ys"));
             (Pcon (SOME (Short "::")) [Pvar "x"; Pvar "xs"],
              Con (SOME (Short "::"))
                [Var (Short "x");
                 App Opapp
                   [App Opapp
                      [Var (Short "append"); Var (Short "xs")];
                    Var (Short "ys")]])]))]);
Tdec
  (Dletrec
     [("flatten","t",
       Mat (Var (Short "t"))
         [(Pcon (SOME (Short "Leaf")) [],
           Con (SOME (Short "nil")) []);
          (Pcon (SOME (Short "Branch"))
             [Pvar "t1"; Pvar "x"; Pvar "t2"],
           App Opapp
             [App Opapp
                [Var (Short "append");
                 App Opapp
                   [Var (Short "flatten"); Var (Short "t1")]];
              App Opapp
                [App Opapp
                   [Var (Short "append");
                    Con (SOME (Short "::"))
                      [Var (Short "x");
                       Con (SOME (Short "nil")) []]];
                 App Opapp
                   [Var (Short "flatten");
                    Var (Short "t2")]]])])]);
Tdec
  (Dletrec
     [("tree_sort","xs",
       App Opapp
         [Var (Short "flatten");
          App Opapp
            [Var (Short "build_tree"); Var (Short "xs")]])]);
Tdec
  (Dletrec
     [("mk_list","n",
       If (App Equality [Var (Short "n"); Lit (IntLit 0)])
         (Con (SOME (Short "nil")) [])
         (Con (SOME (Short "::"))
            [Var (Short "n");
             App Opapp
               [Var (Short "mk_list");
                App (Opn Minus) [Var (Short "n"); Lit (IntLit 1)]]]))]);
Tdec
  (Dletrec
     [("use_tree","n",
       App Opapp
         [Var (Short "tree_sort");
          App Opapp
            [App Opapp
               [Var (Short "append");
                App Opapp
                  [Var (Short "mk_list"); Var (Short "n")]];
             App Opapp
               [Var (Short "mk_list"); Var (Short "n")]]])]);
Tdec
  (Dlet (Pvar "test")
     (App Opapp [Var (Short "use_tree"); Lit (IntLit 10000)]))]``

val queue = ``
[Tdec
  (Dtype
     [(["'a"],"q",
       [("QUEUE",
         [Tapp [Tvar "'a"] (TC_name (Short "list"));
          Tapp [Tvar "'a"] (TC_name (Short "list"))])])]);
Tdec
  (Dlet (Pvar "empty")
     (Con (SOME (Short "QUEUE"))
        [Con (SOME (Short "nil")) [];
         Con (SOME (Short "nil")) []]));
Tdec
  (Dletrec
     [("is_empty","q",
       Mat (Var (Short "q"))
         [(Pcon (SOME (Short "QUEUE"))
             [Pcon (SOME (Short "nil")) []; Pvar "xs"],
           Con (SOME (Short "true")) []);
          (Pvar "_",Con (SOME (Short "false")) [])])]);
Tdec
  (Dletrec
     [("reverse_aux","l",
       Fun "acc"
         (Mat (Var (Short "l"))
            [(Pcon (SOME (Short "nil")) [],Var (Short "acc"));
             (Pcon (SOME (Short "::")) [Pvar "x"; Pvar "xs"],
              App Opapp
                [App Opapp
                   [Var (Short "reverse_aux"); Var (Short "xs")];
                 Con (SOME (Short "::"))
                   [Var (Short "x"); Var (Short "acc")]])]))]);
Tdec
  (Dletrec
     [("reverse","xs",
       App Opapp
         [App Opapp [Var (Short "reverse_aux"); Var (Short "xs")];
          Con (SOME (Short "nil")) []])]);
Tdec
  (Dletrec
     [("checkf","q",
       Mat (Var (Short "q"))
         [(Pcon (SOME (Short "QUEUE"))
             [Pcon (SOME (Short "nil")) []; Pvar "xs"],
           Con (SOME (Short "QUEUE"))
             [App Opapp [Var (Short "reverse"); Var (Short "xs")];
              Con (SOME (Short "nil")) []]);
          (Pvar "_",Var (Short "q"))])]);
Tdec
  (Dletrec
     [("snoc","q",
       Fun "x"
         (Mat (Var (Short "q"))
            [(Pcon (SOME (Short "QUEUE")) [Pvar "f"; Pvar "r"],
              App Opapp
                [Var (Short "checkf");
                 Con (SOME (Short "QUEUE"))
                   [Var (Short "f");
                    Con (SOME (Short "::"))
                      [Var (Short "x"); Var (Short "r")]]])]))]);
Tdec
  (Dletrec
     [("head","q",
       Mat (Var (Short "q"))
         [(Pcon (SOME (Short "QUEUE"))
             [Pcon (SOME (Short "::")) [Pvar "x"; Pvar "f"];
              Pvar "r"],Var (Short "x"))])]);
Tdec
  (Dletrec
     [("tail","q",
       Mat (Var (Short "q"))
         [(Pcon (SOME (Short "QUEUE"))
             [Pcon (SOME (Short "::")) [Pvar "x"; Pvar "f"];
              Pvar "r"],
           App Opapp
             [Var (Short "checkf");
              Con (SOME (Short "QUEUE"))
                [Var (Short "f"); Var (Short "r")]])])]);
Tdec
  (Dletrec
     [("use_queue","n",
       Fun "q"
         (If (App Equality [Var (Short "n"); Lit (IntLit 0)])
            (Var (Short "q"))
            (App Opapp
               [App Opapp
                  [Var (Short "use_queue");
                   App (Opn Minus) [Var (Short "n"); Lit (IntLit 1)]];
                App Opapp
                  [Var (Short "tail");
                   App Opapp
                     [App Opapp
                        [Var (Short "snoc");
                         App Opapp
                           [App Opapp [Var (Short "snoc"); Var (Short "q")];
                            App (Opn Minus) [Var (Short "n"); Lit (IntLit 1)]]];
                      App (Opn Minus) [Var (Short "n"); Lit (IntLit 1)]]
                  ]
              ])))]);
Tdec
  (Dletrec
     [("run_queue","n",
       App Opapp
         [Var (Short "head");
          App Opapp
            [App Opapp [Var (Short "use_queue"); Var (Short "n")];
             Var (Short "empty")]])]);
Tdec
  (Dlet (Pvar "test")
     (App Opapp [Var (Short "run_queue"); Lit (IntLit 20000000)]))]``

(* 4-argument part
val qsort = ``
[Tdec
  (Dletrec
     [("part","p",
       Fun "l"
         (Fun "l1"
            (Fun "l2"
               (Mat (Var (Short "l"))
                  [(Pcon (SOME (Short "nil")) [],
                    Con NONE
                      [Var (Short "l1"); Var (Short "l2")]);
                   (Pcon (SOME (Short "::"))
                      [Pvar "h"; Pvar "rst"],
                    If
                      (App Opapp
                         [Var (Short "p"); Var (Short "h")])
                      (App Opapp
                         [App Opapp
                            [App Opapp
                               [App Opapp
                                  [Var (Short "part");
                                   Var (Short "p")];
                                Var (Short "rst")];
                             Con (SOME (Short "::"))
                               [Var (Short "h");
                                Var (Short "l1")]];
                          Var (Short "l2")])
                      (App Opapp
                         [App Opapp
                            [App Opapp
                               [App Opapp
                                  [Var (Short "part");
                                   Var (Short "p")];
                                Var (Short "rst")];
                             Var (Short "l1")];
                          Con (SOME (Short "::"))
                            [Var (Short "h");
                             Var (Short "l2")]]))]))))]);
Tdec
  (Dletrec
     [("partition","p",
       Fun "l"
         (App Opapp
            [App Opapp
               [App Opapp
                  [App Opapp
                     [Var (Short "part"); Var (Short "p")];
                   Var (Short "l")]; Con (SOME (Short "nil")) []];
             Con (SOME (Short "nil")) []]))]);
Tdec
  (Dletrec
     [("append","l1",
       Fun "l2"
         (Mat (Var (Short "l1"))
            [(Pcon (SOME (Short "nil")) [],Var (Short "l2"));
             (Pcon (SOME (Short "::")) [Pvar "x"; Pvar "xs"],
              Con (SOME (Short "::"))
                [Var (Short "x");
                 App Opapp
                   [App Opapp
                      [Var (Short "append"); Var (Short "xs")];
                    Var (Short "l2")]])]))]);
Tdec
  (Dletrec
     [("qsort","r",
       Fun "l"
         (Mat (Var (Short "l"))
            [(Pcon (SOME (Short "nil")) [],
              Con (SOME (Short "nil")) []);
             (Pcon (SOME (Short "::")) [Pvar "h"; Pvar "t"],
              Mat
                (App Opapp
                   [App Opapp
                      [Var (Short "partition");
                       Fun "y"
                         (App Opapp
                            [App Opapp
                               [Var (Short "r"); Var (Short "y")];
                             Var (Short "h")])]; Var (Short "t")])
                [(Pcon NONE [Pvar "l1"; Pvar "l2"],
                  App Opapp
                    [App Opapp
                       [Var (Short "append");
                        App Opapp
                          [App Opapp
                             [Var (Short "qsort");
                              Var (Short "r")];
                           Var (Short "l1")]];
                     App Opapp
                       [App Opapp
                          [Var (Short "append");
                           Con (SOME (Short "::"))
                             [Var (Short "h");
                              Con (SOME (Short "nil")) []]];
                        App Opapp
                          [App Opapp
                             [Var (Short "qsort");
                              Var (Short "r")];
                           Var (Short "l2")]]])])]))]);
Tdec
  (Dletrec
     [("mk_list","n",
       If (App Equality [Var (Short "n"); Lit (IntLit 0)])
         (Con (SOME (Short "nil")) [])
         (Con (SOME (Short "::"))
            [Var (Short "n");
             App Opapp
               [Var (Short "mk_list");
                App (Opn Minus)
                  [Var (Short "n"); Lit (IntLit 1)]]]))]);
Tdec
  (Dletrec
     [("use_qsort","n",
       App Opapp
         [App Opapp
            [Var (Short "qsort");
             Fun "x"
               (Fun "y"
                  (App (Opb Leq) [Var (Short "x"); Var (Short "y")]))];
          App Opapp
            [App Opapp
               [Var (Short "append");
                App Opapp
                  [Var (Short "mk_list"); Var (Short "n")]];
             App Opapp
               [Var (Short "mk_list"); Var (Short "n")]]])]);
Tdec
  (Dlet (Pvar "test")
     (App Opapp [Var (Short "use_qsort"); Lit (IntLit 10000)]))]``
*)

(* 3-argument part *)
val qsort = ``
[Tdec
  (Dletrec
     [("part","p",
       Fun "l"
         (Fun ""
            (Mat (Var (Short ""))
               [(Pcon NONE [Pvar "l1"; Pvar "l2"],
                 Mat (Var (Short "l"))
                   [(Pcon (SOME (Short "nil")) [],
                     Con NONE [Var (Short "l1"); Var (Short "l2")]);
                    (Pcon (SOME (Short "::")) [Pvar "h"; Pvar "rst"],
                     If
                       (App Opapp [Var (Short "p"); Var (Short "h")])
                       (App Opapp
                          [App Opapp
                             [App Opapp
                                [Var (Short "part");
                                 Var (Short "p")];
                              Var (Short "rst")];
                           Con NONE
                             [Con (SOME (Short "::"))
                                [Var (Short "h"); Var (Short "l1")];
                              Var (Short "l2")]])
                       (App Opapp
                          [App Opapp
                             [App Opapp
                                [Var (Short "part");
                                 Var (Short "p")];
                              Var (Short "rst")];
                           Con NONE
                             [Var (Short "l1");
                              Con (SOME (Short "::"))
                                [Var (Short "h");
                                 Var (Short "l2")]]]))])])))]);
Tdec
  (Dletrec
     [("partition","p",
       Fun "l"
         (App Opapp
            [App Opapp
               [App Opapp [Var (Short "part"); Var (Short "p")];
                Var (Short "l")];
             Con NONE
               [Con (SOME (Short "nil")) [];
                Con (SOME (Short "nil")) []]]))]);
Tdec
  (Dletrec
     [("append","l1",
       Fun "l2"
         (Mat (Var (Short "l1"))
            [(Pcon (SOME (Short "nil")) [],Var (Short "l2"));
             (Pcon (SOME (Short "::")) [Pvar "x"; Pvar "xs"],
              Con (SOME (Short "::"))
                [Var (Short "x");
                 App Opapp
                   [App Opapp
                      [Var (Short "append"); Var (Short "xs")];
                    Var (Short "l2")]])]))]);
Tdec
  (Dletrec
     [("qsort","r",
       Fun "l"
         (Mat (Var (Short "l"))
            [(Pcon (SOME (Short "nil")) [],
              Con (SOME (Short "nil")) []);
             (Pcon (SOME (Short "::")) [Pvar "h"; Pvar "t"],
              Mat
                (App Opapp
                   [App Opapp
                      [Var (Short "partition");
                       Fun "y"
                         (App Opapp
                            [App Opapp
                               [Var (Short "r"); Var (Short "y")];
                             Var (Short "h")])]; Var (Short "t")])
                [(Pcon NONE [Pvar "l1"; Pvar "l2"],
                  App Opapp
                    [App Opapp
                       [Var (Short "append");
                        App Opapp
                          [App Opapp
                             [Var (Short "qsort"); Var (Short "r")];
                           Var (Short "l1")]];
                     App Opapp
                       [App Opapp
                          [Var (Short "append");
                           Con (SOME (Short "::"))
                             [Var (Short "h");
                              Con (SOME (Short "nil")) []]];
                        App Opapp
                          [App Opapp
                             [Var (Short "qsort"); Var (Short "r")];
                           Var (Short "l2")]]])])]))]);
Tdec
  (Dletrec
     [("mk_list","n",
       If (App Equality [Var (Short "n"); Lit (IntLit 0)])
         (Con (SOME (Short "nil")) [])
         (Con (SOME (Short "::"))
            [Var (Short "n");
             App Opapp
               [Var (Short "mk_list");
                App (Opn Minus)
                  [Var (Short "n"); Lit (IntLit 1)]]]))]);
Tdec
  (Dletrec
     [("use_qsort","n",
       App Opapp
         [App Opapp
            [Var (Short "qsort");
             Fun "x"
               (Fun "y"
                  (App (Opb Leq) [Var (Short "x"); Var (Short "y")]))];
          App Opapp
            [App Opapp
               [Var (Short "append");
                App Opapp
                  [Var (Short "mk_list"); Var (Short "n")]];
             App Opapp
               [Var (Short "mk_list"); Var (Short "n")]]])]);
Tdec
     (Dlet (Pvar "test")
        (App Opapp [Var (Short "use_qsort"); Lit (IntLit 10000)]))]``

val fib = ``
[Tdec
  (Dletrec
     [("fib","n",
       If
         (App (Opb Lt) [Var (Short "n"); Lit (IntLit 2)]) (Var (Short "n"))
         (App (Opn Plus)
            [App Opapp [Var (Short "fib"); App (Opn Minus) [Var (Short "n"); Lit (IntLit 1)]];
             App Opapp [Var (Short "fib"); App (Opn Minus) [Var (Short "n"); Lit (IntLit 2)]]]))]);
Tdec
  (Dletrec
     [("use_fib","n",
      App (Opn Plus)
         [App (Opn Plus)
            [App (Opn Plus)
                   [App (Opn Plus)
                           [App (Opn Plus)
                              [App Opapp [Var (Short "fib"); Var (Short "n")];
                               App Opapp [Var (Short "fib"); Var (Short "n")]];
                           App Opapp [Var (Short "fib"); Var (Short "n")]];
                   App Opapp [Var (Short "fib"); Var (Short "n")]];
            App Opapp [Var (Short "fib"); Var (Short "n")]];
         App Opapp [Var (Short "fib"); Var (Short "n")]]
     )]);
Tdec
  (Dlet (Pvar "test")
     (App Opapp [Var (Short "use_fib"); Lit (IntLit 36)]))]``

val reverse =``
[Tdec
   (Dletrec
      [("reverse","xs",
        Letrec
          [("append","xs",
            Fun "ys"
              (Mat (Var (Short "xs"))
                 [(Pcon (SOME (Short "nil")) [],Var (Short "ys"));
                  (Pcon (SOME (Short "::")) [Pvar "x"; Pvar "xs"],
                   Con (SOME (Short "::"))
                     [Var (Short "x");
                      App Opapp
                        [App Opapp
                           [Var (Short "append"); Var (Short "xs")];
                         Var (Short "ys")]])]))]
          (Letrec
             [("rev","xs",
               Mat (Var (Short "xs"))
                 [(Pcon (SOME (Short "nil")) [],Var (Short "xs"));
                  (Pcon (SOME (Short "::")) [Pvar "x"; Pvar "xs"],
                   App Opapp
                     [App Opapp
                        [Var (Short "append");
                         App Opapp
                           [Var (Short "rev"); Var (Short "xs")]];
                      Con (SOME (Short "::"))
                        [Var (Short "x");
                         Con (SOME (Short "nil")) []]])])]
             (App Opapp [Var (Short "rev"); Var (Short "xs")])))]);
Tdec
   (Dletrec
      [("mk_list","n",
        If (App Equality [Var (Short "n"); Lit (IntLit 0)])
          (Con (SOME (Short "nil")) [])
          (Con (SOME (Short "::"))
             [Var (Short "n");
              App Opapp
                [Var (Short "mk_list");
                 App (Opn Minus) [Var (Short "n"); Lit (IntLit 1)]]]))]);

Tdec
   (Dlet (Pvar "test")
      (App Opapp
         [Var (Short "reverse");
          App Opapp [Var (Short "mk_list"); Lit (IntLit 20000)]]))]``

val foldl = ``
[Tdec
 (Dletrec
    [("foldl","f",
      Fun "e"
        (Fun "xs"
           (Mat (Var (Short "xs"))
              [(Pcon (SOME (Short "nil")) [],Var (Short "e"));
               (Pcon (SOME (Short "::")) [Pvar "x"; Pvar "xs"],
                App Opapp
                  [App Opapp
                     [App Opapp
                        [Var (Short "foldl"); Var (Short "f")];
                      App Opapp
                        [App Opapp
                           [Var (Short "f"); Var (Short "e")];
                         Var (Short "x")]];
                   Var (Short "xs")])])))]);
Tdec
 (Dletrec
    [("repeat","x",
      Fun "n"
        (If
           (App Equality [Var (Short "n"); Lit (IntLit 0)])
           (Con (SOME (Short "nil")) [])
           (Con (SOME (Short "::"))
              [Var (Short "x");
               App Opapp
                 [App Opapp [Var (Short "repeat"); Var (Short "x")];
                  App (Opn Minus) [Var (Short "n"); Lit (IntLit 1)]]
                  ])))]);
Tdec
 (Dlet (Pvar "test")
    (App Opapp
       [App Opapp
          [App Opapp
             [Var (Short "foldl");
              Fun "x"
                (Fun "y"
                   (App (Opn Plus) [Var (Short "x");
                       App Opapp
                         [App Opapp
                            [App Opapp
                               [Var (Short "foldl");
                                Fun "x"
                                  (Fun "y"
                                     (App (Opn Plus) [Var (Short "x");
                                                      Var (Short "y")]))];
                             Lit (IntLit 0)]; Var (Short "y")]]))];
           Lit (IntLit 0)];
        App Opapp
          [App Opapp
             [Var (Short "repeat");
              App Opapp
                [App Opapp [Var (Short "repeat"); Lit (IntLit 1)];
                 Lit (IntLit 15000)]]; Lit (IntLit 15000)]]))]``;

(* TODO: Flipped order of comparison for abs *)
val nqueens =
``[Tdec (Dexn "Fail" []);
  Tdec
    (Dletrec
       [("abs","x",
         If
           (App (Opb Lt) [Var (Short "x");Lit (IntLit 0)])
           (Var (Short "x"))
           (App (Opn Minus) [Lit (IntLit 0); Var (Short "x")]))]);
  Tdec
    (Dletrec
       [("curcheck","p",
         Fun "ls"
           (Mat (Var (Short "ls"))
              [(Pcon (SOME (Short "nil")) [],Con NONE []);
               (Pcon (SOME (Short "::")) [Pvar "l"; Pvar "ls"],
                Mat (Var (Short "p"))
                  [(Pcon NONE [Pvar "x"; Pvar "y"],
                    Mat (Var (Short "l"))
                      [(Pcon NONE [Pvar "a"; Pvar "b"],
                        If
                          (Log Or
                             (Log Or
                                (App Equality
                                   [Var (Short "a");Var (Short "x")])
                                (App Equality
                                   [Var (Short "b");Var (Short "y")]))
                             (App Equality
                                [App Opapp [Var (Short "abs");
                                   App (Opn Minus)
                                     [Var (Short "a");Var (Short "x")]];
                                 App Opapp [Var (Short "abs");
                                    App (Opn Minus)
                                       [Var (Short "b");Var (Short "y")]]])
                            )
                          (Raise (Con (SOME (Short "Fail")) []))
                          (App Opapp
                             [App Opapp
                                [Var (Short "curcheck");
                                 Con NONE
                                   [Var (Short "x");
                                    Var (Short "y")]];
                              Var (Short "ls")]))])])]))]);
  Tdec
    (Dletrec
       [("nqueens","n",
         Fun "cur"
           (Fun "ls"
              (If
                 (App (Opb Geq) [Var (Short "cur");Var (Short "n")])
                 (Var (Short "ls"))
                 (Letrec
                    [("find_queen","y",
                      If
                        (App (Opb Geq) [Var (Short "y");Var (Short "n")])
                        (Raise (Con (SOME (Short "Fail")) []))
                        (Handle
                           (Let NONE
                              (App Opapp
                                 [App Opapp
                                    [Var (Short "curcheck");
                                     Con NONE
                                       [Var (Short "cur");
                                        Var (Short "y")]];
                                  Var (Short "ls")])
                              (App Opapp
                                 [App Opapp
                                    [App Opapp
                                       [Var (Short "nqueens");
                                        Var (Short "n")];
                                     App (Opn Plus)[Var (Short "cur");
                                        Lit (IntLit 1)]];
                                  Con (SOME (Short "::"))
                                    [Con NONE
                                       [Var (Short "cur");
                                        Var (Short "y")];
                                     Var (Short "ls")]]))
                           [(Pcon (SOME (Short "Fail")) [],
                             App Opapp
                               [Var (Short "find_queen");
                                App (Opn Plus) [Var (Short "y");
                                   Lit (IntLit 1)]])]))]
                    (App Opapp
                       [Var (Short "find_queen");
                        Lit (IntLit 0)])))))]);
  Tdec
    (Dlet (Pvar "foo")
       (App Opapp
          [App Opapp
             [App Opapp [Var (Short "nqueens"); Lit (IntLit 29)];
              Lit (IntLit 0)]; Con (SOME (Short "nil")) []]))]``

val hello = entire_program_def |> concl |> rand
val benchmarks = [qsortimp,nqueens,hello,foldl,reverse,fib,btree,queue,qsort]
val names = ["qsortimp","nqueens","hello","foldl","reverse","fib","btree","queue","qsort"]

val extract_bytes = pairSyntax.dest_pair o optionSyntax.dest_some o rconc

fun write_asm [] = ()
  | write_asm ((name,(bytes,ffi_count))::xs) =
    (write_cake_S 1000 1000 (numSyntax.int_of_term ffi_count)
       bytes ("cakeml/" ^ name ^ ".S") ;
    write_asm xs)

val benchmarks_compiled = map (to_bytes 3 ``x64_compiler_config``) benchmarks

val benchmarks_bytes = map extract_bytes benchmarks_compiled
val _ = write_asm (zip names benchmarks_bytes);

val _ = map save_thm (zip names benchmarks_compiled);

(*
(*Turning down the register allocator*)
val benchmarks_compiled2 = map (to_bytes 0 ``x64_compiler_config``) benchmarks
val benchmarks_bytes2 = map extract_bytes benchmarks_compiled2
val _ = write_asm (zip names benchmarks_bytes2);

(* Turn off clos optimizations*)
val clos_o0 = ``x64_compiler_config.clos_conf with <|do_mti:=F;do_known:=F;do_call:=F;do_remove:=F|>``
val benchmarks_compiled3 = map (to_bytes 0 ``x64_compiler_config with clos_conf:=^(clos_o0)``) benchmarks
val benchmarks_bytes3 = map extract_bytes benchmarks_compiled3
val _ = write_asm (zip names benchmarks_bytes3);

(* Turn off bvl_to_bvi optimzations ?*)
val bvl_o0 =  ``<|inline_size_limit := 0 ; exp_cut := 10000 ; split_main_at_seq := F|>``
val benchmarks_compiled4 = map (to_bytes 0 ``x64_compiler_config with <|clos_conf:=^(clos_o0);bvl_conf:=^(bvl_o0)|>``) benchmarks
val benchmarks_bytes4 = map extract_bytes benchmarks_compiled4
val _ = write_asm (zip names benchmarks_bytes4);
*)

(*
val clos_o0 = ``x64_compiler_config.clos_conf with <|do_mti:=F;do_known:=F;do_call:=F;do_remove:=F|>``
val clos_o1 = ``x64_compiler_config.clos_conf with <|do_mti:=T;do_known:=F;do_call:=F;do_remove:=F|>``
val clos_o2 = ``x64_compiler_config.clos_conf with <|do_mti:=T;do_known:=T;do_call:=F;do_remove:=F|>``
val clos_o3 = ``x64_compiler_config.clos_conf with <|do_mti:=T;do_known:=T;do_call:=T;do_remove:=F|>``
val clos_o4 = ``x64_compiler_config.clos_conf with <|do_mti:=T;do_known:=T;do_call:=T;do_remove:=T|>``

val benchmarks_o0 = map (to_bytes 3 ``x64_compiler_config with clos_conf:=^(clos_o0)``) benchmarks
val benchmarks_o1 = map (to_bytes 3 ``x64_compiler_config with clos_conf:=^(clos_o1)``) benchmarks
val benchmarks_o2 = map (to_bytes 3 ``x64_compiler_config with clos_conf:=^(clos_o2)``) benchmarks
val benchmarks_o3 = map (to_bytes 3 ``x64_compiler_config with clos_conf:=^(clos_o3)``) benchmarks
val benchmarks_o4 = map (to_bytes 3 ``x64_compiler_config with clos_conf:=^(clos_o4)``) benchmarks

val benchmarks_o0_bytes = map extract_bytes benchmarks_o0
val benchmarks_o1_bytes = map extract_bytes benchmarks_o1
val benchmarks_o2_bytes = map extract_bytes benchmarks_o2
val benchmarks_o3_bytes = map extract_bytes benchmarks_o3
val benchmarks_o4_bytes = map extract_bytes benchmarks_o4

val _ = write_asm (zip (map (fn s => "o0_"^s)names) benchmarks_o0_bytes);
val _ = write_asm (zip (map (fn s => "o1_"^s)names) benchmarks_o1_bytes);
val _ = write_asm (zip (map (fn s => "o2_"^s)names) benchmarks_o2_bytes);
val _ = write_asm (zip (map (fn s => "o3_"^s)names) benchmarks_o3_bytes);
val _ = write_asm (zip (map (fn s => "o4_"^s)names) benchmarks_o4_bytes);
*)

val _ = export_theory ();
