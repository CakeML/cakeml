open preamble con_to_decTheory dec_to_targetTheory;

val _ = new_theory"con_to_target";

val _ = type_abbrev("con_conf",``:num # 'a dec_conf``);

val compile_def = Define`
  compile (n,c) prog =
  let (n,e) = con_to_dec$compile n prog in
  OPTION_MAP
    (λ(bytes,c). (bytes,(n,c)))
    (dec_to_target$compile c e)`;

val _ = export_theory();
