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

(*Evaluate bvp_to_word partially until the livesets are visible*)
val test1 = Count.apply eval``
  let (c,p) = ^(rconc test) in
  let (bvp_conf,word_conf,asm_conf,p) = (c.bvp_conf,c.word_to_word_conf,c.lab_conf.asm_conf,p) in
  (*The next element is massive*)
  let p = MAP (compile_part bvp_conf) (TAKE 18 p) in
  let (two_reg_arith,reg_count) = (asm_conf.two_reg_arith,asm_conf.reg_count − 4) in
  (*This is compile_single, less the word_alloc step*)
  let p = (MAP (\(name_num,arg_count,prog).
  let maxv = max_var prog + 1 in
  let inst_prog = inst_select asm_conf maxv prog in
  let ssa_prog = full_ssa_cc_trans arg_count inst_prog in
  let prog = if two_reg_arith then three_to_two_reg ssa_prog
                              else ssa_prog in (name_num,arg_count,prog)) p) in
  let clashmov = MAP (\(name_num,arg_count,prog). ((\h,tl. h::tl)(get_clash_sets prog LN),get_prefs prog [])) p in
  (c,reg_count,clashmov,p)``

(*Should be in unverified/reg_alloc, but that would make the folder depend on HOL*)
open reg_alloc
open sptreeSyntax numSyntax listSyntax

fun dest_unit_sptree tm =
 case Lib.total boolSyntax.dest_strip_comb tm of
    SOME ("sptree$LN", []) => Ln
  | SOME ("sptree$LS", [t]) => Ls ()
  | SOME ("sptree$BN", [t1, t2]) => Bn (dest_unit_sptree t1, dest_unit_sptree t2)
  | SOME ("sptree$BS", [t1, v, t2]) => Bs (dest_unit_sptree t1, (), dest_unit_sptree t2)
  | _ => raise ERR "dest_unit_sptree" "";

(*Int ML sptree to HOL num sptree*)
fun mk_num_sptree t =
 case t of
    Ln => mk_ln ``:num``
  | Ls a => mk_ls (term_of_int a)
  | Bn (Ln, t2) =>
       let
          val tm = mk_num_sptree t2
       in
          mk_bn (mk_ln ``:num``, tm)
       end
  | Bn (t1, Ln) =>
       let
          val tm = mk_num_sptree t1
       in
          mk_bn (tm, mk_ln (sptree_ty_of tm))
       end
  | Bn (t1, t2) => mk_bn (mk_num_sptree t1, mk_num_sptree t2)
  | Bs (t1, a, t2) =>
       let
          val ln = mk_ln ``:num``
          val tm1 = if t1 = Ln then ln else mk_num_sptree t1
          val tm2 = if t2 = Ln then ln else mk_num_sptree t2
       in
          mk_bs (tm1, (term_of_int a), tm2)
       end;

(*List of clash sets in HOL to unit sptree*)
fun dest_clash_set_list tm =
  let val (ls,_) = dest_list tm in
      map dest_unit_sptree ls
  end;

fun tup3 [x,y,z] =(x,(y,z))

fun dest_moves tm =
  let val (ls,_) = dest_list tm
      val split = map pairSyntax.strip_pair ls in
  map
  (fn p => tup3 (map int_of_term p)) split end

(*Main thing to call for external allocator*)
fun alloc_all k [] = []
|   alloc_all k ((clash_sets,moves)::xs) =
  let val clash_sets_poly = dest_clash_set_list clash_sets
      val moves_poly = dest_moves moves in
      irc_alloc clash_sets_poly k moves_poly :: alloc_all k xs
  end;

(*Extracted clashmov*)
val clash_mov_ls = map pairSyntax.dest_pair (fst(listSyntax.dest_list (rconc (EVAL``(FST (SND (SND ^(rconc test1))))``))))

val k_poly = int_of_term (rconc(EVAL ``FST (SND ^(rconc test1))``))
val alloc = listSyntax.mk_list (map mk_num_sptree (alloc_all k_poly clash_mov_ls),``:num num_map``)

val oracle = ``let alloc = ^(alloc) in
               \n. if n >= LENGTH alloc then NONE else SOME(EL n alloc)``

val test_oracle = Count.apply eval``
  let (c,reg_count,clashmov,p) = ^(rconc test1) in
  let (n_oracles,col) = next_n_oracle (LENGTH p) ^(oracle) in
  let merge = ZIP(n_oracles,ZIP(MAP FST clashmov,MAP (SND o SND)p)) in
  MAP (\col_opt,sets,prog. oracle_colour_ok reg_count col_opt sets prog) merge``

(*reg_alloc doesn't eval properly yet -- throw away most of the progs generated*)
val test2 = Count.apply eval``
    let (c,p) = ^(rconc test) in
    let p = TAKE 18 p in
    let (col,p) = bvp_to_word$compile c.bvp_conf c.word_to_word_conf c.lab_conf.asm_conf p in
    let c = c with word_to_word_conf updated_by (λc. c with col_oracle := col) in
    (c,p)``

val test3 = Count.apply eval``
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
