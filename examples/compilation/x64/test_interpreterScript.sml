(*
  Test insertion of interpreter
*)
open preamble helloProgTheory compilationLib basis

val _ = new_theory "test_interpreter"

Overload flat_to_clos_inc_compile[local] = ``flat_to_clos$inc_compile_decs``

Definition compile_inc_progs_def:
  compile_inc_progs c p_tup =
    let (env_id,p) = p_tup in
    let p = source_to_source$compile p in
    let (c',p) = source_to_flat$inc_compile env_id c p in
    let p = flat_to_clos_inc_compile p in
      FST (p:closLang$exp list # unit list)
End

val _ = (max_print_depth := 600);

val tm = parse_topdecs ‘
  fun foo x1 x2 x3 x4 x5 = ();
  fun read_input u = ();
  val _ = read_input();
  val (x,y,z) = foo read_input () "hello" "there" "test";
’

val th = “compile_inc_progs source_to_flat$empty_config ((60,60),^tm)” |> EVAL
val n = th |> concl |> find_terms (can $ match_term “Global 0”) |> length

val _ = (n > 0) orelse failwith "Failed to insert call to interpreter";

val _ = export_theory ();
