open preamble mod_to_conTheory con_to_targetTheory;

val _ = new_theory"mod_to_target";

val _ = type_abbrev("mod_conf",``:(num spt # tag_env) # 'a con_conf``);

val compile_def = Define`
  compile ((exc,tag),(n,(exh,c))) p =
    let ((exc,tag,exh),p) = mod_to_con$compile_prog (exc,tag,exh) p in
    OPTION_MAP
      (λ(bytes,(n,(exh,c))). (bytes,((exc,tag),(n,(exh,c)))))
      (con_to_target$compile (n,(exh,c)) p)`;

val _ = export_theory();
