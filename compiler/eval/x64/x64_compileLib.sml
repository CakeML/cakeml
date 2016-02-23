structure x64_compileLib =
struct

open HolKernel boolLib bossLib lcsymtacs;
open x64_targetLib asmLib;
open compilerComputeLib;
open x64DisassembleLib

(* open x64_targetTheory *)

val compset = the_compiler_compset
val () = add_x64_encode_compset compset
val () = add_asm_compset compset
val _ = computeLib.add_funs [x64Theory.e_imm32_def,x64Theory.encode_def];

val eval = computeLib.CBV_CONV compset

fun print_asm res =
  let val res = (rand o concl) res
      val bytes = hd(pairSyntax.strip_pair (optionSyntax.dest_some res))
      val dis = x64_disassemble bytes
      val maxlen = 30
      fun pad 0 = ()
      |   pad n = (print" ";pad (n-1))
      fun printAsm [] = ()
      |   printAsm (x::xs) = case x of (hex,dis) =>
          (print hex;pad (maxlen-String.size hex);print dis;print"\n";printAsm xs)
      in
        print"Bytes";pad (maxlen -5);print"Instruction\n";
        printAsm dis
      end

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

(*reg_alloc doesn't eval properly yet -- throw away most of the progs generated*)
val test2 = eval``
    let (c,p) = ^(rconc test) in
    let p = TAKE 2 p in
    let (col,p) = bvp_to_word$compile c.bvp_conf c.word_to_word_conf c.lab_conf.asm_conf p in
    let c = c with word_to_word_conf updated_by (λc. c with col_oracle := col) in
    (c,p)``

val test3 = eval``
    let (c,p) = ^(rconc test2) in
    let (c',p) = word_to_stack$compile c.lab_conf.asm_conf p in
    let c = c with word_conf := c' in
    let p = stack_to_lab$compile c.clos_conf.start c.stack_conf c.bvp_conf c.word_conf p in
    let (lc,sec_list) = (c.lab_conf,p) in
    let sec_list = filter_skip sec_list in
      (enc_sec_list lc.encoder sec_list)``

(* Rest of lab_to_target (after stack_to_lab$compile)
    let bc' = lab_to_target$compile c.lab_conf p in
      OPTION_MAP (λ(b,c'). (b,c with lab_conf := c')) bc'``;*)


(*
open x64_targetTheory lab_to_targetTheory;
open x64_exportLib wordsTheory wordsLib;

val _ = computeLib.add_funs [x64Theory.e_imm32_def,x64Theory.encode_def];

val bytes_tm =
  eval ``lab_to_target$compile (x64_config,x64_enc,LN) [Section 0 [LabAsm Halt 0w [] 0]]``
  |> concl |> rand |> rand

val _ = write_cake_S 1 1 0 bytes_tm ""

Try:   gcc cake.S -o cake && ./cake

*)

end
