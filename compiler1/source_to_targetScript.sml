open preamble source_to_modTheory mod_to_targetTheory;

val _ = new_theory"source_to_target";

val _ = type_abbrev("config",``:(num # (varN,num) mod_env) # α mod_conf``)

val compile_def = Define`
  compile ((next,menv,env),c) prog =
    let (next,menv,env,prog) = source_to_mod$compile_prog next menv env prog in
      OPTION_MAP
        (λ(bytes,c). (bytes,((next,menv,env),c)))
        (mod_to_target$compile c prog)`;

val _ = export_theory();
