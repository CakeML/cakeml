open preamble sexp_compiler_x64ProgTheory

val _ = new_theory"to_dataBootstrap";

val _ = Globals.max_print_depth := 20;

(* These are evaluated out to avoid the type variable in prim_config *)
val cs = compilationLib.compilation_compset();
val eval = computeLib.CBV_CONV cs;
val default_source_conf = eval ``prim_config.source_conf`` |> rconc;
val default_mod_conf    = eval ``prim_config.mod_conf`` |> rconc;

val init_conf_def = zDefine`
  init_conf = <|
    source_conf := ^default_source_conf;
    mod_conf    := ^default_mod_conf;
    clos_conf   := clos_to_bvl$default_config;
    bvl_conf    := bvl_to_bvi$default_config with <| inline_size_limit := 3; exp_cut := 200 |>
  |>`;

(*
val (ls,ty) = entire_program_def |> rconc |> listSyntax.dest_list
val new_prog = listSyntax.mk_list(List.take(ls,80),ty)
val entire_program_thm = mk_thm([],mk_eq(lhs(concl(entire_program_def)),new_prog));
*)
val entire_program_thm = entire_program_def;

val to_data_x64_thm = save_thm("to_data_x64_thm",
  compilationLib.compile_to_data
    cs init_conf_def entire_program_thm "data_prog_x64");

val _ = export_theory();
