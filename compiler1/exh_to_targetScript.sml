open preamble exh_to_patTheory pat_to_targetTheory

val _ = new_theory"exh_to_target";

val compile_def = Define`
  compile c e =
    pat_to_target$compile c (exh_to_pat$compile_exp [] e)`;

val _ = export_theory()
