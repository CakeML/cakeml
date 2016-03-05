open HolKernel boolLib bossLib lcsymtacs;
open x64_compileLib;

(*--Simple Tests--*)
val source_conf = ``<|next_global:=0;mod_env:=(FEMPTY,FEMPTY)|>``
val mod_conf = ``<|next_exception:=LN;tag_env:=(FEMPTY,FEMPTY);exh_ctors_env:=FEMPTY|>``
val clos_conf = ``<|next_loc := 0 ; start:=0|>``
val bvp_conf = ``<| tag_bits:=8; len_bits:=8; pad_bits:=0; len_size:=16|>``
val word_to_word_conf = ``<| reg_alg:=1; col_oracle := λn. NONE |>``
(*val word_conf = ``<| bitmaps := [] |>``*)
val stack_conf = ``<|reg_names:=x64_names;stack_ptr:=5;max_heap:=1000|>``
(*??*)
val lab_conf = ``<|encoder:=x64_enc;labels:=LN;asm_conf:=x64_config|>``

val conf = ``<|source_conf:=^(source_conf);
               mod_conf:=^(mod_conf);
               clos_conf:=^(clos_conf);
               bvp_conf:=^(bvp_conf);
               word_to_word_conf:=^(word_to_word_conf);
               (*word_conf:=^(word_conf);*)
               stack_conf:=^(stack_conf);
               lab_conf:=^(lab_conf)
               |>``

(*val y = (fn x => x)*)

val prog = ``[Tdec (Dlet (Pvar "y") (Fun "x" (Var (Short "x"))))]``

val _ = PolyML.timing true;
val _ = Globals.max_print_depth := 20
val _ = PolyML.print_depth 20;

val test = eval``to_livesets ^(conf) ^(prog)``

val rconc = rhs o concl

val oracles = reg_allocComputeLib.get_oracle (fst (pairSyntax.dest_pair (rconc test)))

(*The custom eval takes forever here...*)
val test_oracle = EVAL``
  let ((reg_count,clashmov),c,p) = ^(rconc test) in
  let (n_oracles,col) = next_n_oracle (LENGTH p) ^(oracles) in
  let merge = ZIP(n_oracles,ZIP(MAP FST clashmov,MAP (SND o SND)p)) in
  EVERY IS_SOME(MAP (\col_opt,sets,prog. oracle_colour_ok reg_count col_opt sets prog) merge)``

(*Here, we re-eval with the oracle attached*)

val test2= EVAL``
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

val test3 = Count.apply EVAL``
  let (c,p) = ^(rconc test2) in
  let (c',p) = word_to_stack$compile c.lab_conf.asm_conf p in
  let c = c with word_conf := c' in
  let p = stack_to_lab$compile c.stack_conf c.bvp_conf c.word_conf p in
  (c,p)``

(*Didn't finish after 10mins*)
val test4 = Count.apply eval
  ``let (c,p) = ^(rconc test3) in
  lab_to_target$compile c.lab_conf p``

(* Testing eval of check_clash_tree
  The custom eval appears to use more Prims than EVAL?
*)

val tree = ``
  Seq (Delta [1;2;3;4;5;6;7] [5;4;3;2;1])
  (Seq (Delta [1;2;3;4;5;6;7] [5;4;3;2;1])
  (Seq (Delta [1;2;3;4;5;6;7] [5;4;3;2;1])
  (Seq (Delta [1;2;3;4;5;6;7] [5;4;3;2;1])
  (Seq (Delta [1;2;3;4;5;6;7] [5;4;3;2;1])
  (Seq (Delta [1;2;3;4;5;6;7] [5;4;3;2;1])
  (Seq (Delta [1;2;3;4;5;6;7] [5;4;3;2;1])
  (Seq (Delta [1;2;3;4;5;6;7] [5;4;3;2;1])
  (Seq (Delta [1;2;3;4;5;6;7] [5;4;3;2;1])
  (Seq (Delta [1;2;3;4;5;6;7] [5;4;3;2;1])
  (Seq (Delta [1;2;3;4;5;6;7] [5;4;3;2;1]) (Set (numset_list_insert [1;2;3;4;5] LN))))))))))))``

val foo = Count.apply eval``
  check_clash_tree I ^(tree) LN LN``

val foo2 = Count.apply EVAL``
  check_clash_tree I ^(tree) LN LN``

