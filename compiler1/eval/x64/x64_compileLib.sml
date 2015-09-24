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

val eval = computeLib.CBV_CONV compset

(*Configurations stack*)
val x64_lab_conf = ``(x64_config,x64_enc,LN):64 lab_conf``
val x64_stack_conf = ``(x64_names,5,6,^(x64_lab_conf)):64 stack_conf``
(*Maybe make word take configs for the allocator too*)
val x64_word_conf = x64_stack_conf
val x64_bvp_conf =
        ``(<| tag_bits:=8
            ; len_bits:=8
            ; pad_bits:=0
            ; len_size:=16|>,^(x64_word_conf)):64 bvp_conf``
val x64_bvl_conf = ``(0,^(x64_bvp_conf)):64 bvl_conf``
val x64_clos_conf = ``(0,^(x64_bvl_conf)):64 clos_conf``
(*pat,exh take same conf*)
val x64_dec_conf = ``(FEMPTY,^(x64_clos_conf)):64 dec_conf``
val x64_con_conf = ``(0,^(x64_dec_conf)):64 con_conf``
val x64_mod_conf = ``((LN,(FEMPTY,FEMPTY)),^(x64_con_conf)):64 mod_conf``
val x64_source_conf = ``((0,(FEMPTY,FEMPTY)),^(x64_mod_conf)):64 config``

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
val labtest = eval ``lab_to_target$compile ^(x64_lab_conf) [Section 0 [LabAsm Halt 0w [] 0]]``
val stacktest = eval ``stack_to_target$compile 50 ^(x64_stack_conf) [0,(Seq (Skip:64 stackLang$prog) (StackStore 5 3 ))]``

val wordtest = eval ``word_to_target$compile 50 ^(x64_word_conf) [0,2,(Seq (Assign 5 (Op Add [(Var 0);(Var 2)])) (Return 5 5))]``

val bvptest = eval ``bvp_to_target$compile 50 ^(x64_bvp_conf) [0,2,(Seq (Move 5 0) (Return 5))]``

val bvitest = eval ``bvi_to_bvp$compile_part (0,5,(Var 3))``
val bvitest2 = eval ``bvi_to_target$compile 50 ^(x64_bvp_conf) [(0,5,(Var 3))]``

(*val prog = ``[Tdec (Dlet (Pvar "x") (Fun "x" (Var (Short "x"))))]``*)

val prog = ``[Tdec (Dlet (Pvar "x") (Lit (IntLit 0)))]``
val _ = PolyML.timing true;

(*Step through entire compiler*)
val e1 =
eval ``let((next,menv,env),c) = ^(x64_source_conf) in
let prog = ^(prog) in
let (next,menv,env,prog) = source_to_mod$compile_prog next menv env prog in

let ((exc,tag),(n,(exh,c))) = c in
let ((exc,tag,exh),prog) = mod_to_con$compile_prog (exc,tag,exh) prog in

let (n,e) =
    con_to_dec$compile_prog
      (none_tag,TypeId(Short"option"))
      (some_tag,TypeId(Short"option"))
      n prog in

let e = dec_to_exh$compile_exp exh e in

let e = exh_to_pat$compile_exp [] e in

let exp = pat_to_clos$compile e in

let (next_loc,c) = c in
let es = intro_multi [exp] in
let (es,l) = remove es in
let (next_loc,es) = renumber_code_locs_list next_loc es in
let es = annotate es in
let (es,aux) = clos_to_bvl$compile es [] in

(*bvl_to_targe$compile 0 c ((MAP (λe. (0,0,e)) es)++aux)*)
let progs = ((MAP (λe. (0,0,e)) es)++aux) in
let (n,c) = c in
let (s,bvi_progs,n) = bvl_to_bvi$compile_prog 0 n progs in

let bvp_progs = bvi_to_bvp$compile_prog bvi_progs in

(*bvp_to_target$compile s c bvp_progs -- 278.2*)
let (bvp_c,c) = c in
let word_progs: (num#num#64 wordLang$prog) list = bvp_to_word$compile bvp_c bvp_progs in

(*word_to_target$compile s c word_progs*)
let (two_reg_arith,reg_count) = get_conf_props c in
let prog = MAP ((compile_single two_reg_arith reg_count)) word_progs in

(*stack_to_target$compile s c prog -- 140.4 *)
let(f,sp,bp,conf) = c in
let prog' = stub1 s :: prog in
let without_stack = stub0 sp bp :: stack_remove$compile (sp,bp) prog' in
let with_target_names = stack_names$compile f without_stack in
let sec_list = stack_to_lab$compile with_target_names in

(*lab_to_target$compile conf sec_list -- 77.5*)
let remove = filter_skip sec_list in
let (c,enc,l) = conf in
  case remove_labels c enc sec_list l of 
  | SOME (sec_list,l1) => SOME (prog_to_bytes sec_list,(c,enc,l1))
  | NONE => NONE``;
(*Fully unfolded -- 77.3*)

val progtest = eval ``source_to_target$compile ^(x64_source_conf) ^(prog)``
(*Eval from top: 578.5*)

val _ = print_asm progtest


(*
Machinery to test compile_lab -- probably not needed anymore

let sec_list = filter_skip sec_list in
enc_sec_list enc sec_list,c,enc,l``

val e2 = (rand o concl) e1
val [sec_list,c,enc,l] = pairSyntax.strip_pair e2

val all_lengths_ok_2_def = Define `
  (all_lengths_ok_2 pos [] = (T,pos,[])) /\
  (all_lengths_ok_2 pos ((Section s lines)::rest) =
     if sec_lengths_ok pos lines
     then all_lengths_ok_2 (pos + sec_length lines 0) rest
     else (F,pos,rest))`

val sec_lengths_ok_2_def = Define `
  (sec_lengths_ok_2 pos [] <=> (T,pos,[])) /\
  (sec_lengths_ok_2 pos ((Label _ _ l)::xs) <=>
     if (if EVEN pos then (l = 0) else (l = 1)) then
       sec_lengths_ok_2 (pos+l) xs
     else (F,pos,xs)) /\
  (sec_lengths_ok_2 pos ((Asm x1 x2 l)::xs) <=> sec_lengths_ok_2 (pos+l) xs) /\
  (sec_lengths_ok_2 pos ((LabAsm a w bytes l)::xs) <=>
     if LENGTH bytes <= l then sec_lengths_ok_2 (pos+l) xs else (F,pos,xs))`

val all_lengths_update_2_def = Define `
  (all_lengths_update_2 pos [] = []) /\
  (all_lengths_update_2 pos ((Section s lines)::rest) =
     (pos,Section s (sec_lengths_update pos lines)) ::
       all_lengths_update_2 (pos + sec_length lines 0) rest)`;

val sec_lengths_update_2_def = Define `
  (sec_lengths_update_2 pos [] = []) /\
  (sec_lengths_update_2 pos ((Label k1 k2 l)::xs) =
     let l = if EVEN pos then 0 else 1 in
       (pos,Label k1 k2 l) :: sec_lengths_update_2 (pos+l) xs) /\
  (sec_lengths_update_2 pos ((Asm x1 x2 l)::xs) <=>
     (pos,Asm x1 x2 l) :: sec_lengths_update_2 (pos+l) xs) /\
  (sec_lengths_update_2 pos ((LabAsm a w bytes l)::xs) <=>
     let m = LENGTH bytes in
     let l = if l < m then m else l in
       (pos,LabAsm a w bytes l) ::
          sec_lengths_update_2 (pos+l) xs)`


val () = computeLib.add_thms [all_lengths_ok_2_def,sec_lengths_ok_2_def,all_lengths_update_2_def,sec_lengths_update_2_def] compset
val eval = computeLib.CBV_CONV compset
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
