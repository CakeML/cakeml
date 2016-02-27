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

val prog = ``[Tdec (Dlet (Pvar "y") (Fun "x" (Var (Short "x"))))]``;

val _ = PolyML.timing true;
val _ = Globals.max_print_depth := 20
val _ = PolyML.print_depth 20;

val test = eval``
    let (c,p) = (^(conf),^(prog)) in
    let (c',p) = source_to_mod$compile c.source_conf p in
    let c = c with source_conf := c' in
    let (c',p) = mod_to_con$compile c.mod_conf p in
    let c = c with mod_conf := c' in
    let (n,e) = con_to_dec$compile c.source_conf.next_global p in
    let c = c with source_conf updated_by (λc. c with next_global := n) in
    let e = dec_to_exh$compile_exp c.mod_conf.exh_ctors_env e in
    let e = exh_to_pat$compile e in
    let e = pat_to_clos$compile e in
    let (c',p) = clos_to_bvl$compile c.clos_conf e in
    let c = c with clos_conf := c' in
    let (s,p,n) = bvl_to_bvi$compile c.clos_conf.start c.clos_conf.next_loc p in
    let c = c with clos_conf updated_by (λc. c with <| start := s; next_loc := n |>) in
    let p = bvi_to_bvp$compile_prog p in (c,p)``

val rconc = rhs o concl

(*Evaluate bvp_to_word partially until the livesets are visible*)
val test1 = Count.apply eval``
  let (c,p) = ^(rconc test) in
  let (bvp_conf,word_conf,asm_conf,p) = (c.bvp_conf,c.word_to_word_conf,c.lab_conf.asm_conf,p) in
  (*The next element is massive*)
  let p:(num,num#64 wordLang$prog)alist = MAP (compile_part bvp_conf) p in
  let (two_reg_arith,reg_count) = (asm_conf.two_reg_arith,asm_conf.reg_count − 4) in
  (*This is compile_single, less the word_alloc step*)
  let p = (MAP (\(name_num,arg_count,prog).
  let maxv = max_var prog + 1 in
  let inst_prog = inst_select asm_conf maxv prog in
  let ssa_prog = full_ssa_cc_trans arg_count inst_prog in
  let prog = if two_reg_arith then three_to_two_reg ssa_prog
                              else ssa_prog in (name_num,arg_count,prog)) p) in
  let clashmov = MAP (\(name_num,arg_count,prog). ((\h,tl. h::tl)(get_clash_sets prog LN),get_prefs prog [])) p in
  ((reg_count,clashmov),c,p)``

val oracles = compute_reg_allocLib.get_oracle (fst (pairSyntax.dest_pair (rconc test1)))

val test_oracle = Count.apply eval``
  let ((reg_count,clashmov),c,p) = ^(rconc test1) in
  let (n_oracles,col) = next_n_oracle (LENGTH p) ^(oracles) in
  let merge = ZIP(n_oracles,ZIP(MAP FST clashmov,MAP (SND o SND)p)) in
  MAP (\col_opt,sets,prog. oracle_colour_ok reg_count col_opt sets prog) merge``

(* Rest of lab_to_target (after stack_to_lab$compile)
    let bc' = lab_to_target$compile c.lab_conf p in
      OPTION_MAP (λ(b,c'). (b,c with lab_conf := c')) bc'``;*)


