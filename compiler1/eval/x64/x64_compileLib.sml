structure x64_compileLib =
struct

open HolKernel boolLib bossLib lcsymtacs;
open x64_targetLib asmLib;
open compilerComputeLib;

(* open x64_targetTheory *)

val compset = the_compiler_compset
val () = add_x64_encode_compset compset
val () = add_asm_compset compset

val () = computeLib.add_thms[bvpTheory.mk_ticks_def] compset

val eval = computeLib.CBV_CONV compset

(*Test evaluation. TODO: Need to fix the confs*)
val x64_lab_conf = ``(x64_config,x64_enc,LN):64 lab_conf``
val labtest = eval ``lab_to_target$compile ^(x64_lab_conf) [Section 0 [LabAsm Halt 0w [] 0]]``

val x64_stack_conf = ``(x64_names,5,6,^(x64_lab_conf)):64 stack_conf``
val stacktest = eval ``stack_to_target$compile 50 ^(x64_stack_conf) [0,(Seq (Skip:64 stackLang$prog) (StackStore 5 3 ))]``

(*Maybe make word take configs for the allocator too*)
val x64_word_conf = x64_stack_conf
val wordtest = eval ``word_to_target$compile 50 ^(x64_word_conf) [0,2,(Seq (Assign 5 (Op Add [(Var 0);(Var 2)])) (Return 5 5))]``

val x64_bvp_conf =
        ``(<| tag_bits:=8
            ; len_bits:=8
            ; pad_bits:=0
            ; len_size:=16|>,^(x64_word_conf)):64 bvp_conf``
val bvptest = eval ``bvp_to_target$compile 50 ^(x64_bvp_conf) [0,2,(Seq (Move 5 0) (Return 5))]``

val bvitest = eval ``bvi_to_bvp$compile_part (0,5,(Var 3))``
val bvitest2 = eval ``bvi_to_target$compile 50 ^(x64_bvp_conf) [(0,5,(Var 3))]``

val x64_bvl_conf = ``(0,^(x64_bvp_conf)):64 bvl_conf``

val x64_clos_conf = ``(0,^(x64_bvl_conf)):64 clos_conf``
(*pat,exh take same conf*)

val x64_dec_conf = ``(FEMPTY,^(x64_clos_conf)):64 dec_conf``

val x64_con_conf = ``(0,^(x64_dec_conf)):64 con_conf``

val x64_mod_conf = ``((LN,(FEMPTY,FEMPTY)),^(x64_con_conf)):64 mod_conf``

val x64_source_conf = ``((0,(FEMPTY,FEMPTY)),^(x64_mod_conf)):64 config``

val prog = ``[Tdec (Dlet (Pvar "x") (Lit (IntLit 0)))]:prog``

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
let (next_loc,es) = renumber_code_locs_list next_loc es in
let es = annotate es in
let (es,aux) = clos_to_bvl$compile es [] in

let progs = ((MAP (λe. (0,0,e)) es)++aux) in
let (n,c) = c in
let (s,bvi_progs,n) = bvl_to_bvi$compile_prog 0 n progs in

let bvp_progs = bvi_to_bvp$compile_prog bvi_progs in

let (bvp_c,c) = c in
let word_progs: (num#num#64 wordLang$prog) list = bvp_to_word$compile bvp_c bvp_progs in
let (two_reg_arith,reg_count) = get_conf_props c in
let prog = MAP ((compile_single two_reg_arith reg_count)) word_progs in

let(f,sp,bp,conf) = c in
let prog' = stub1 s :: prog in
let without_stack = stub0 sp bp :: stack_remove$compile (sp,bp) prog' in
let with_target_names = stack_names$compile f without_stack in
with_target_names``
(*There's an ARB in here*)

(*
let sec_list = stack_to_lab$compile with_target_names in


val bvltest = eval ``let progs = bvl_to_bvi$compile_prog 0 [0,5,(Var 3)] in
let prog = HD ((FST progs)) in
let progs = bvi_to_bvp$compile_prog [prog] in
let wprogs:(num#num#64 wordLang$prog)list = bvp_to_word$compile (FST ^(x64_bvp_conf)) progs in
let conf = ^(x64_word_conf) in
let (two_reg_arith,reg_count) = get_conf_props conf in
let prog = MAP (compile_single two_reg_arith reg_count) wprogs in
let(f,sp,bp,conf) = conf in
let prog' = stub1 :: prog in
let without_stack = stub0 sp bp :: stack_remove$compile (sp,bp) prog' in
let with_target_names = stack_names$compile f without_stack in
let sec_list = stack_to_lab$compile with_target_names in
let (c,enc,l) = conf in
let sec_list = filter_skip sec_list in
let sec_list = enc_sec_list enc sec_list in
let labs = compute_labels 0 sec_list l in
let xs = enc_secs_again 0 labs enc sec_list in
if all_lengths_ok 0 xs then
      if all_asm_ok c xs then
        SOME (pad_code (enc (Inst Skip)) xs,filter_labs labs)
      else NONE
else NONE``


let progs = bvi_to_bvp$compile_prog [prog] in progs``

val bvltest = eval ``bvl_to_target$compile ^(x64_bvl_conf) [(0,5,(Var 3))]``
val bvltest = eval ``bvl_to_target$compile_exp_def``


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
