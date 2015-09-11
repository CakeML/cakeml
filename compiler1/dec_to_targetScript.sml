open preamble
     mod_to_conTheory (* for exh_ctors_env *)
     dec_to_exhTheory
     exh_to_targetTheory;

val _ = new_theory"dec_to_target";

val _ = type_abbrev("dec_conf",``:exh_ctors_env # 'a clos_conf``);

val compile_def = Define`
  compile (exh,c) e =
    OPTION_MAP
      (λ(b,c). (b,(exh,c)))
      (exh_to_target$compile c (dec_to_exh$compile_exp exh e))`;

val _ = export_theory();
