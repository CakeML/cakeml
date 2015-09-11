open preamble bvp_to_wordTheory word_to_targetTheory;

val _ = new_theory "bvp_to_target";

val compile_def = Define`
  compile (bvp_conf, c, enc, f, sp, bp) progs =
    let word_progs = bvp_to_word$compile bvp_conf progs in
      word_to_target$compile c enc f sp bp word_progs`

val _ = export_theory ();
