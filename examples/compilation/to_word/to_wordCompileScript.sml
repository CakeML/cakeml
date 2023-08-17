(*
  Compiles a program to wordLang
*)
open preamble compilationLib basis word_cseTheory
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

Definition progCmp_def:
  progCmp p1 p2 =
    if p1=p2
      then []
      else case (p1,p2) of
           | (wordLang$Seq p11 p12, wordLang$Seq p21 p22) => (progCmp p11 p21) ++ (progCmp p12 p22)
           | (wordLang$If _ _ _ p11 p12, wordLang$If _ _ _ p21 p22) => (progCmp p11 p21) ++ (progCmp p12 p22)
           | (_,_) => [(p1,p2)]
End

val _ = export_theory ();