open HolKernel boolLib bossLib lcsymtacs;
open x64_compileLib;

val source_conf = ``<|next_global:=0;mod_env:=(FEMPTY,FEMPTY)|>``
val mod_conf = ``<|next_exception:=LN;tag_env:=(FEMPTY,FEMPTY);exh_ctors_env:=FEMPTY|>``
val clos_conf = ``<|next_loc := 0 ; start:=0|>``
val bvp_conf = ``<| tag_bits:=8; len_bits:=8; pad_bits:=0; len_size:=16|>``
val word_to_word_conf = ``<| reg_alg:=1; col_oracle := λn. NONE |>``
(*val word_conf = ``<| bitmaps := [] |>``*)
val stack_conf = ``<|reg_names:=x64_names;stack_ptr:=5;max_heap:=1000000|>``
(*??*)
val lab_conf = ``<|encoder:=x64_enc;labels:=LN;asm_conf:=x64_config;init_clock:=5|>``

val conf = ``<|source_conf:=^(source_conf);
               mod_conf:=^(mod_conf);
               clos_conf:=^(clos_conf);
               bvp_conf:=^(bvp_conf);
               word_to_word_conf:=^(word_to_word_conf);
               (*word_conf:=^(word_conf);*)
               stack_conf:=^(stack_conf);
               lab_conf:=^(lab_conf)
               |>``

val _ = PolyML.timing true;
val _ = Globals.max_print_depth := 20;
val _ = PolyML.print_depth 5;

val rconc = rhs o concl

(*Compilation of basis_prog is very slow, so we avoid it for now*)
val initial_prog = rconc (EVAL``prim_types_program``)

fun println s = print (strcat s "\n");

fun to_bytes prog =
  let
  val prog = ``^(initial_prog) ++ ^(prog)``
  val _ = println "Compile to livesets"
  val test = Count.apply eval``to_livesets ^(conf) ^(prog)``
  val _ = println "External oracle"
  val oracles = reg_allocComputeLib.get_oracle (fst (pairSyntax.dest_pair (rconc test)))
  val _ = println "Eval with oracle attached"
  val test2 = Count.apply eval``
    let (rcm,c,p) = ^(rconc test) in
    from_livesets (rcm,c with word_to_word_conf:= <|reg_alg:=1;col_oracle:= ^(oracles)|>,p)``
  in
    test2
  end

fun to_bytes_verbose prog =
  let
  val prog = ``^(initial_prog) ++ ^(prog)``
  val _ = println "Compile to livesets"
  val test = Count.apply eval``to_livesets ^(conf) ^(prog)``
  val _ = println "External oracle"
  val oracles = reg_allocComputeLib.get_oracle (fst (pairSyntax.dest_pair (rconc test)))
  val _ = println "Eval with oracle attached"
  val test2 = Count.apply eval``
    let ((k,clashmov),c,p) = ^(rconc test) in
    let (word_conf,asm_conf) = (c.word_to_word_conf,c.lab_conf.asm_conf) in
    let (n_oracles,col) = next_n_oracle (LENGTH p) ^(oracles) in
    let alg = word_conf.reg_alg in
    let prog_with_oracles = ZIP (n_oracles,ZIP(clashmov,p)) in
    let p =
      MAP (λ(col_opt,((tree,moves),name_num,arg_count,prog)).
        case oracle_colour_ok k col_opt tree prog of
          NONE =>
            (let (clash_graph,_) = clash_tree_to_spg tree [] LN in
               let col = reg_alloc alg clash_graph k moves
               in
                 (name_num,arg_count,remove_must_terminate (apply_colour (total_colour col) prog)))
        | SOME col_prog => (name_num,arg_count,remove_must_terminate col_prog)) prog_with_oracles in
    let c = c with word_to_word_conf updated_by (λc. c with col_oracle := col) in
    (c,p)``
  val _ = println "Compile to labLang"
  val test3 = Count.apply eval``
    let (c,p) = ^(rconc test2) in
    (*unverified: let p = MAP (λa,b,prog. a,b,FST(remove_dead prog LN)) p in*)
    let (c',p) = word_to_stack$compile c.lab_conf.asm_conf p in
    let c = c with word_conf := c' in
    let p = stack_to_lab$compile c.stack_conf c.bvp_conf c.word_conf p in
    (c,p)``
  val _ = println "First encoding"
  val test4 = Count.apply eval``
    let (c,p) = ^(rconc test3) in
    let p = filter_skip p in
    let c = c.lab_conf in
    let limit = find_ffi_index_limit p in
    let (c,enc,l) = (c.asm_conf,c.encoder,c.labels) in
    (c,enc,l,enc_sec_list enc p,limit)``
  val _ = println "Remove labels loop"
  val test5 = Count.apply eval``
    let (c,enc,l,sec_list,limit) = ^(rconc test4) in
    remove_labels_loop 1000000 c enc sec_list l``
  val _ = println "Extract byte list"
  val test6 = Count.apply eval``
    case ^(rconc test5) of
    SOME (sec_list,l1) => prog_to_bytes sec_list`` in
    rconc test6 end

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

val fib_bytes = to_bytes fib
val qsort_bytes = to_bytes qsort
val queue_bytes = to_bytes queue
val btree_bytes = to_bytes btree

fun dump_file file t =
  let
    val f = TextIO.openOut (file)
  in
    TextIO.output(f,term_to_string t);
    TextIO.closeOut f
  end

val _ = Globals.max_print_depth := ~1;
val _ = PolyML.print_depth 5;

val bytes_tm = fst(pairSyntax.dest_pair(optionSyntax.dest_some(rconc fib_bytes)))
val _ = dump_file "fib" bytes_tm

open x64_exportLib

val _ = x64_exportLib.write_cake_S 1 1 0 bytes_tm "cake.S"
