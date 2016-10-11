open HolKernel boolLib bossLib lcsymtacs;
open x64_compileLib
open riscv_compileLib
open arm_compileLib
open mips_compileLib
open arm8_compileLib
open arm_exportLib arm8_exportLib mips_exportLib riscv_exportLib x64_exportLib

val _ = new_theory "benchmark"

val rconc = rhs o concl

val _ = PolyML.timing true;
val _ = Globals.max_print_depth := 20;
val _ = PolyML.print_depth 5;

fun println s = print (strcat s "\n");

fun to_bytes alg eval conf prog =
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

val sayhi = ``
[Tdec (Dlet (Pvar"h") (App (FFI 0) [App Aw8alloc [Lit(IntLit 1); Lit(Word8(n2w(104)))]]));
 Tdec (Dlet (Pvar"i") (App (FFI 0) [App Aw8alloc [Lit(IntLit 1); Lit(Word8(n2w(105)))]]))]``

val benchmarks = [sayhi,foldl,reverse,fib,btree,queue,qsort]
val names = ["sayhi","foldl","reverse","fib","btree","queue","qsort"]

val extract_bytes = pairSyntax.dest_pair o optionSyntax.dest_some o rconc

fun save_th conf (str,th)=
  save_thm (conf^"_"^str,th)

fun write_asm sz prefix exporter [] = ()
  | write_asm sz prefix exporter ((name,(bytes,ffi_count))::xs) =
    (exporter sz sz (numSyntax.int_of_term ffi_count)
       bytes ("cakeml/" ^ prefix ^"_"^ name ^ ".S") ;
    write_asm sz prefix exporter xs)

(*"*)
(* Set up for benchmarking with / without optimizations *)

fun to_bytes_wrap opt eval conf =
  if opt
  then
    to_bytes 3 eval conf
  else
    (* no reg_alloc *)
    to_bytes 0 eval
    (rconc (eval``
    let conf = ^(conf) in
    (* no fp opts *)
    let clos = conf.clos_conf with <|do_mti:=F;do_known:=F;do_call:=F;do_remove:=F|> in
    (* no bvl opts *)
    let bvl = <|inline_size_limit := 0 ; exp_cut := 10000 ; split_main_at_seq := F|> in
    (* no pattern match opt *)
    let orig_pad = conf.data_conf.pad_bits in
    let data = <|tag_bits:=0; len_bits:=0; pad_bits:= 1; len_size:=conf.data_conf.len_size|> in
    conf with <|clos_conf:=clos;bvl_conf:=bvl;data_conf:=data|>``))

(* x64 all opts and no opts *)
val x64_benchmarks_compiled_all = map (to_bytes_wrap true x64_compileLib.eval ``x64_compiler_config``) benchmarks;
val x64_benchmarks_bytes_all = map extract_bytes x64_benchmarks_compiled_all;
val _ = write_asm 1000 "x64_all" x64_exportLib.write_cake_S (zip names x64_benchmarks_bytes_all);

val x64_benchmarks_compiled_none = map (to_bytes_wrap false x64_compileLib.eval ``x64_compiler_config``) benchmarks;
val x64_benchmarks_bytes_none = map extract_bytes x64_benchmarks_compiled_none;
val _ = write_asm 1000 "x64_none" x64_exportLib.write_cake_S (zip names x64_benchmarks_bytes_none);

(* arm all_opts and no opts *)
val arm_benchmarks_compiled_all = map (to_bytes_wrap true arm_compileLib.eval ``arm_compiler_config``) benchmarks;
val arm_benchmarks_bytes_all = map extract_bytes arm_benchmarks_compiled_all;
val _ = write_asm 500 "arm_all" arm_exportLib.write_cake_S (zip names arm_benchmarks_bytes_all);

val arm_benchmarks_compiled_none = map (to_bytes_wrap false arm_compileLib.eval ``arm_compiler_config``) benchmarks;
val arm_benchmarks_bytes_none = map extract_bytes arm_benchmarks_compiled_none;
val _ = write_asm 500 "arm_none" arm_exportLib.write_cake_S (zip names arm_benchmarks_bytes_none);

(* riscv all_opts and no opts *)
val riscv_benchmarks_compiled_all = map (to_bytes_wrap true riscv_compileLib.eval ``riscv_compiler_config``) benchmarks;
val riscv_benchmarks_bytes_all = map extract_bytes riscv_benchmarks_compiled_all;
val _ = write_asm 1000 "riscv_all" riscv_exportLib.write_cake_S (zip names riscv_benchmarks_bytes_all);

val riscv_benchmarks_compiled_none = map (to_bytes_wrap false riscv_compileLib.eval ``riscv_compiler_config``) benchmarks;
val riscv_benchmarks_bytes_none = map extract_bytes riscv_benchmarks_compiled_none;
val _ = write_asm 1000 "riscv_none" riscv_exportLib.write_cake_S (zip names riscv_benchmarks_bytes_none);

(* arm8 all_opts and no opts *)
val arm8_benchmarks_compiled_all = map (to_bytes_wrap true arm8_compileLib.eval ``arm8_compiler_config``) benchmarks;
val arm8_benchmarks_bytes_all = map extract_bytes arm8_benchmarks_compiled_all;
val _ = write_asm 1000 "arm8_all" arm8_exportLib.write_cake_S (zip names arm8_benchmarks_bytes_all);

val arm8_benchmarks_compiled_none = map (to_bytes_wrap false arm8_compileLib.eval ``arm8_compiler_config``) benchmarks;
val arm8_benchmarks_bytes_none = map extract_bytes arm8_benchmarks_compiled_none;
val _ = write_asm 1000 "arm8_none" arm8_exportLib.write_cake_S (zip names arm8_benchmarks_bytes_none);

(* mips all_opts and no opts *)
val mips_benchmarks_compiled_all = map (to_bytes_wrap true mips_compileLib.eval ``mips_compiler_config``) benchmarks;
val mips_benchmarks_bytes_all = map extract_bytes mips_benchmarks_compiled_all;
val _ = write_asm 1000 "mips_all" mips_exportLib.write_cake_S (zip names mips_benchmarks_bytes_all);

val mips_benchmarks_compiled_none = map (to_bytes_wrap false mips_compileLib.eval ``mips_compiler_config``) benchmarks;
val mips_benchmarks_bytes_none = map extract_bytes mips_benchmarks_compiled_none;
val _ = write_asm 1000 "mips_none" mips_exportLib.write_cake_S (zip names mips_benchmarks_bytes_none);

val _ = export_theory ();
