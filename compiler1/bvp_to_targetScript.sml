open preamble bvp_to_wordTheory word_to_targetTheory;

val _ = new_theory "bvp_to_target";

val _ = type_abbrev("bvp_conf", ``:bvp_to_word$config # 'a stack_conf``);

val compile_def = Define`
  compile start ((bvp_c, conf):'a bvp_conf) progs =
    let word_progs = bvp_to_word$compile bvp_c progs in
      case word_to_target$compile start conf word_progs of
      | NONE => NONE
      | SOME (bytes,conf) => SOME (bytes,(bvp_c,conf))`

val _ = export_theory ();
