open preamble bvi_to_bvpTheory bvp_to_targetTheory;

val _ = new_theory "bvi_to_target";

val compile_def = Define`
  compile c progs =
    let bvp_progs = bvi_to_bvp$compile_prog progs in
      bvp_to_target$compile c bvp_progs`

val _ = export_theory ();
