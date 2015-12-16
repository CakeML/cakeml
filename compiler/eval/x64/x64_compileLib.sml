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
val stack_conf = ``<|reg_names:=x64_names;stack_ptr:=5;base_ptr:=6|>``
(*??*)
val lab_conf = ``<|encoder:=x64_enc;labels:=LN;asm_conf:=x64_config|>``

val conf = ``<|source_conf:=^(source_conf);
               mod_conf:=^(mod_conf);
               clos_conf:=^(clos_conf);
               bvp_conf:=^(bvp_conf);
               stack_conf:=^(stack_conf);
               lab_conf:=^(lab_conf)
               |>``

val prog = ``[Tdec (Dlet (Pvar "y") (Fun "x" (Var (Short "x"))))]``;

val _ = PolyML.timing true;

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
    let p = bvi_to_bvp$compile_prog p in
    let (p: (num,num#64 wordLang$prog) alist) = bvp_to_word$compile c.bvp_conf p in
    let p = word_to_stack$compile c.clos_conf.start c.lab_conf.asm_conf p in
    let p = stack_to_lab$compile c.clos_conf.start c.stack_conf p in
    let bc' = lab_to_target$compile c.lab_conf p in
    OPTION_MAP (λ(b,c'). (b,c with lab_conf := c')) bc'``;

(*
167.8s source to bytecode, expanded
val prog = ``[Tdec (Dlet (Pvar "x") (Fun "x" (Var (Short "x"))))]``

174.8s
val prog = ``[Tdec (Dlet (Pvar "x") (Lit (IntLit 0)))]``

372.2s
val prog = ``[Tdec (Dlet (Pvar "y") (Fun "x" (Var (Short "x"))));
              Tdec (Dlet (Pvar "x") (Lit (IntLit 0)))]``
*)

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
