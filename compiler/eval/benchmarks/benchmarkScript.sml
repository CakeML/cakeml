open HolKernel boolLib bossLib lcsymtacs;

open x64_compileLib x64_exportLib

val _ = new_theory "benchmark"

val rconc = rhs o concl

val _ = PolyML.timing true;
val _ = Globals.max_print_depth := 20;
val _ = PolyML.print_depth 5;

(*Compilation of basis_prog is very slow, so we avoid it for now*)
(*val initial_prog = rconc (EVAL``prim_types_program``)*)

fun println s = print (strcat s "\n");

fun to_bytes prog =
  let
  val _ = println "Compile to livesets"
  val init = Count.apply eval``to_livesets x64_compiler_config ^(prog)``
  val _ = println "External oracle"
  val oracles = reg_allocComputeLib.get_oracle (fst (pairSyntax.dest_pair (rconc init)))
  val wc = ``<|reg_alg:=1;col_oracle:= ^(oracles)|>``
  val _ = println "Repeat compilation with oracle"
  (*This repeats the "to_livesets" step, but that isn't very costly*)
  val compile_thm = Count.apply eval``
    compile (x64_compiler_config with word_to_word_conf := ^(wc)) ^(prog)``
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
     (App Opapp [Var (Short "use_tree"); Lit (IntLit 1000)]))]``

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
     (App Opapp [Var (Short "run_queue"); Lit (IntLit 1000000)]))]``

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
     (App Opapp [Var (Short "use_qsort"); Lit (IntLit 1000)]))]``

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
     (App Opapp [Var (Short "use_fib"); Lit (IntLit 31)]))]``

val benchmarks = [fib,btree,queue,qsort]
val names = ["fib","btree","queue","qsort"]

val benchmarks_compiled = map to_bytes benchmarks

val extract_bytes = fst o pairSyntax.dest_pair o optionSyntax.dest_some o rconc

val benchmarks_bytes = map extract_bytes benchmarks_compiled

fun write_asm [] = ()
  | write_asm ((name,bytes)::xs) =
    (write_cake_S 50 50 0 bytes ("exec/benchmark_" ^ name ^ ".S") ;
    write_asm xs)

val _ = write_asm (zip names benchmarks_bytes);

val _ = map save_thm (zip names benchmarks_compiled);

val _ = export_theory ();
