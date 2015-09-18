open preamble
     clos_mtiTheory
     clos_callTheory
     clos_numberTheory
     clos_annotateTheory
     clos_to_bvlTheory
     bvl_to_targetTheory;

val _ = new_theory"clos_to_target";

val _ = type_abbrev("clos_conf",``:num # 'a bvl_conf``);

val compile_def = Define`
  compile (next_loc,c) exp =
  let es = intro_multi [exp] in
  (* TODO: introduce multi-argument applications, #70 *)
  (* TODO: let (exp,calls) = call_intro es in *)
  (* TODO: dead code elimination, #75 *)
  let (next_loc,es) = renumber_code_locs_list next_loc es in
  let es = annotate es in
  (* TODO: dead code elimination, #75 too *)
  let (es,aux) = clos_to_bvl$compile es [] in
    OPTION_MAP
      (λ(bytes,c). (bytes,(next_loc,c)))
      (* TODO: (0,0,e) is probably not correct *)
      (bvl_to_target$compile c ((MAP (λe. (0,0,e)) es)++aux))`;

val _ = export_theory();
