(*
  Compiles a program to wordLang
*)
open preamble compilationLib basis word_comSubExpElimTheory
val _ = new_theory "to_wordCompile"

val _ = (max_print_depth := 500);

Overload "▸" = “wordLang$Seq”
val _ = set_fixity "▸" (Infixl 500);

Definition comp_to_ssa_def:
  comp_to_ssa c b (name_num,arg_count,prog) =
    let prog = compile_exp prog;
        maxv = max_var prog + 1;
        inst_prog = inst_select c maxv prog;
        ssa_prog = (if b then full_ssa_cc_trans arg_count else I) inst_prog
    in
      compile_exp ssa_prog
End

Definition get_ssa_for_def:
  get_ssa_for fun_name b c p =
    let (_,funs,names) = to_word_0 c p in
    let xs = MAP (λ(x,y). (lookup x names,y)) funs in
    let fun_name = implode fun_name in
    let ys = FILTER (λ(x,y). case x of NONE => F | SOME s => fun_name = s) xs in
      comp_to_ssa c.lab_conf.asm_conf b (HD ys)
End

fun comp_to_ssa do_ssa fun_name prog_def =
  let
    val cs = compilation_compset()
    val conf_def = x64_configTheory.x64_backend_config_def
    val data_prog_name = "data_prog"
    val to_data_thm = compile_to_data cs conf_def prog_def data_prog_name
    val _ = save_thm("to_data_thm", to_data_thm)
    val data_prog_def = definition(mk_abbrev_name data_prog_name)
    val to_word_0_thm = compile_to_word_0 data_prog_def to_data_thm
    val word_0_p_def = fetch "-" "word_0_p_def"
    val word_0_names_def = fetch "-" "word_0_names_def"
    val () = computeLib.extend_compset
      [computeLib.Defs [word_0_p_def,word_0_names_def,comp_to_ssa_def,
         x64_backend_config_def, x64_targetTheory.x64_config_def, x64_names_def]] cs;
    val eval = computeLib.CBV_CONV cs;
    val s = stringSyntax.fromMLstring fun_name
    val tm = to_word_0_thm |> concl |> dest_eq |> fst
    val b = if do_ssa then T else F
    val l = “get_ssa_for ^s ^b ^(rand (rator tm)) ^(rand tm)”
  in
    l |> (REWR_CONV get_ssa_for_def THENC
          REWRITE_CONV [to_word_0_thm] THENC eval)
  end;

(* foldr example *)

val decs = process_topdecs ‘
  fun foldr f e xs =
    case xs of
      [] => e
    | (y::ys) => f y (foldr f e ys);
  val _ = foldr (fn x => x);’

Definition foldr_prog_def:
  foldr_prog = ^decs
End

Theorem foldr_example =
  comp_to_ssa false "foldr" foldr_prog_def;

Theorem foldr_example_ssa =
  comp_to_ssa true "foldr" foldr_prog_def;

val tm = foldr_example_ssa |> concl |> rand

Definition test_def:
  test p = word_cse p
End

Definition progCmp_def:
  progCmp p1 p2 =
    if p1=p2
      then []
      else case (p1,p2) of
           | (wordLang$Seq p11 p12, wordLang$Seq p21 p22) => (progCmp p11 p21) ++ (progCmp p12 p22)
           | (wordLang$If _ _ _ p11 p12, wordLang$If _ _ _ p21 p22) => (progCmp p11 p21) ++ (progCmp p12 p22)
           | (_,_) => [(p1,p2)]
End

(*
Definition prog1_def:
  prog1 =
        Move 1 [(37,0); (41,2); (45,4); (49,6)] ▸
        If Equal 41 (Imm 2w)
          (Inst (Const 53 18w) ▸ Move 0 [(2,45)] ▸ Return 37 2 ▸
           Move 1 [(181,37); (177,49)] ▸ Inst (Const 185 0w) ▸
           Inst (Const 189 0w) ▸ Inst (Const 193 0w) ▸ Move 1 [(197,53)] ▸
           Inst (Const 201 0w) ▸ Move 1 [(205,41)] ▸ Move 1 [(209,45)] ▸
           Inst (Const 213 0w) ▸ Inst (Const 217 0w))
          (Inst (Const 57 2w) ▸ Move 0 [(61,41)] ▸
           Inst (Arith (Shift Lsr 65 61 9)) ▸ OpCurrHeap Add 69 65 ▸
           Inst (Mem Load 73 (Addr 69 8w)) ▸ Move 0 [(77,41)] ▸
           Inst (Arith (Shift Lsr 81 77 9)) ▸ OpCurrHeap Add 85 81 ▸
           Inst (Mem Load 89 (Addr 85 16w)) ▸
           Move 1 [(95,37); (99,49); (103,73)] ▸
           Move 0 [(2,89); (4,45); (6,49)] ▸
           Call
             (SOME
                (2,insert 95 () (insert 99 () (insert 103 () LN)),
                 Move 1 [(109,95); (113,99); (117,103)] ▸ Move 0 [(121,2)],
                 249,2)) (SOME 249) [2; 4; 6] NONE ▸ Move 0 [(125,113)] ▸
           Inst (Arith (Shift Lsr 129 125 9)) ▸ OpCurrHeap Add 133 129 ▸
           Inst (Mem Load 137 (Addr 133 16w)) ▸
           If Equal 137 (Imm 4w)
             (Inst (Const 141 18w) ▸ Move 0 [(145,113)] ▸
              Inst (Arith (Shift Lsr 149 145 9)) ▸ OpCurrHeap Add 153 149 ▸
              Inst (Mem Load 157 (Addr 153 8w)) ▸
              Move 0 [(0,109); (2,121); (4,117); (6,113); (8,157)] ▸
              Call NONE NONE [0; 2; 4; 6; 8] NONE ▸
              Move 1 [(169,153); (165,141)] ▸ Move 1 [(173,157)])
             (Inst (Const 161 2w) ▸
              Move 0 [(0,109); (2,121); (4,117); (6,113)] ▸
              Call NONE (SOME 69) [0; 2; 4; 6] NONE ▸
              Move 1 [(169,133); (165,161)] ▸ Inst (Const 173 0w)) ▸
           Move 1 [(181,109); (177,113)] ▸ Move 1 [(185,137)] ▸
           Move 1 [(189,117)] ▸ Move 1 [(193,121)] ▸ Inst (Const 197 0w) ▸
           Move 1 [(201,173)] ▸ Inst (Const 205 0w) ▸ Inst (Const 209 0w) ▸
           Move 1 [(213,165)] ▸ Move 1 [(217,169)])
End


EVAL “progCmp ^tm (test ^tm)”
*)
val _ = export_theory ();
