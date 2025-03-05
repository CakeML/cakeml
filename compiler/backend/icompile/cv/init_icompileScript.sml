open preamble
     eval_cake_icompile_x64Lib
     x64_configTheory;


val _ = Globals.max_print_depth := 10;

val _ = new_theory"init_icompile";


Definition x64_config'_def:
  x64_config' =
  let conf = x64_backend_config in
  let source_conf' = conf.source_conf with <| do_elim := F; init_vidx := 100000 |> in
  let stack_conf' = conf.stack_conf with do_rawcall := F in
    conf with <| source_conf := source_conf';
                 stack_conf := stack_conf'|>
End


val x64_conf_def = CONV_RULE (RAND_CONV EVAL) x64_config'_def; (* no optimisation *)

val x64_inc_conf = backendTheory.config_to_inc_config_def
                         |> ISPEC (x64_conf_def |> rconc)
                         |> CONV_RULE (RAND_CONV EVAL) |> rconc;


fun run () =
init_icompile x64_inc_conf;


val (init_icomp_thm, init_icomp_empty, init_ic_name) = time run ();


Theorem init_icomp_thm = init_icomp_thm;
Theorem init_icomp_empty = init_icomp_empty;
Definition x64_inc_conf_def:
  x64_inc_conf = ^(x64_inc_conf)
End


val _ = export_theory();
