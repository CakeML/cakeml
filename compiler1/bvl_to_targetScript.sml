open preamble bvl_to_bviTheory bvi_to_targetTheory;

val _ = new_theory "bvl_to_target";

val compile_def = Define`
  compile c progs =
    let bvi_progs = bvl_to_bvi$compile_prog progs in
      bvi_to_target$compile c bvi_progs`

val _ = export_theory ();
