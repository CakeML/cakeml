(*
  benchmarking stuff
  *)
open preamble
     eval_cake_icompile_x64Lib
     helloProgTheory
     x64_configTheory;

val _ = new_theory"icompile_x64";

val _ = Globals.max_print_depth := 10;

fun split_basis prog_name =
  let
    val prog_const = mk_const (prog_name, “: ast$dec list”);
    val basis = EVAL “TAKE 93 ^prog_const” |> rconc;
    val prog1 = EVAL “DROP 93 ^prog_const” |> rconc;
  in
    (basis, prog1)
  end;
(* set up config *)
val c = x64_backend_config_def |> concl |> lhs;
val x64_inc_conf = backendTheory.config_to_inc_config_def
                     |> ISPEC c |> CONV_RULE (RAND_CONV EVAL) |> rconc;
val inc_source_conf_init_vidx = EVAL “^(x64_inc_conf).inc_source_conf with
                                      <| init_vidx := 100000;
                                         do_elim := F;
                                      |>” |> rconc;
val inc_stack_conf_do_rawcall_f = EVAL “^(x64_inc_conf).inc_stack_conf with do_rawcall := F” |> rconc;
val x64_inc_conf = (EVAL “^(x64_inc_conf) with
        <| inc_source_conf := ^(inc_source_conf_init_vidx);
           inc_stack_conf := ^(inc_stack_conf_do_rawcall_f) |>” |> rconc);

(* example usage *)
val (basis_prog_tm, hello_prog1_tm) = split_basis "hello_prog";

val (init_icomp_thm, init_icomp_empty, init_ic_name) = init_icompile x64_inc_conf;

val (basis_prog_icomp, basis_prog_ic_name) = icompile init_ic_name init_icomp_empty "basis_prog" basis_prog_tm;

val (hello_prog1_icomp, hello_prog_ic_name) = icompile basis_prog_ic_name basis_prog_icomp "hello_prog1" hello_prog1_tm;

val final_thm = end_icompile init_icomp_thm
                             hello_prog1_icomp
                             hello_prog_ic_name
                             x64_inc_conf;

print_to_file final_thm "hello_prog_ic_with_lib.S";

val _ = export_theory();
