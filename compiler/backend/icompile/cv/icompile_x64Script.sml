open preamble
     ibackend_cvTheory
     helloProgTheory;
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



val _ = export_theory();
