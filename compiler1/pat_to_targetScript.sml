open preamble pat_to_closTheory clos_to_targetTheory;

val _ = new_theory"pat_to_target"

val compile_def = Define`
  compile c e =
    clos_to_target$compile c (pat_to_clos$compile e)`;

val _ = export_theory()
