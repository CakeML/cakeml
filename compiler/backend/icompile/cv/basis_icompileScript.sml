(*
  icompile basis
*)
open preamble
     x64_configTheory
     helloProgTheory
     init_icompileTheory
     eval_cake_icompile_x64Lib;

val _ = Globals.max_print_depth := 10;

val _ = new_theory"basis_icompile";

fun split_basis prog_name =
  let
    val prog_const = mk_const (prog_name, “: ast$dec list”);
    val basis = EVAL “TAKE 93 ^prog_const” |> rconc;
    val prog1 = EVAL “DROP 93 ^prog_const” |> rconc;
  in
    (basis, prog1)
  end;

val (basis_prog_tm, _) = split_basis "hello_prog";

val (basis_prog_icomp, basis_prog_ic_name) =
  time (icompile "empty_prog_for_init_ic" init_icomp_empty "basis_prog") basis_prog_tm;

Theorem basis_prog_icomp = basis_prog_icomp;

val _ = export_theory();
