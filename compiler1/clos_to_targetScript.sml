open preamble
     clos_mtiTheory
     clos_callTheory
     clos_numberTheory
     clos_annotateTheory
     clos_to_bvlTheory
     bvl_to_targetTheory;

val _ = new_theory"clos_to_target";

val compile_def = Define`
  compile (c, next_loc) exp =
  let es = intro_multi [exp] in
  (* TODO: introduce multi-argument applications, #70 *)
  (* TODO: let (exp,calls) = call_intro es in *)
  (* TODO: dead code elimination *)
  let (next_loc,es) = renumber_code_locs_list next_loc es in
  let es = annotate es in
  (* TODO: dead code elimination *)
  let (es,aux) = clos_to_bvl$compile es [] in
    OPTION_MAP
      (λ(bytes,c). SOME (bytes,(c,next_loc)))
      (* TODO: (0,0,e) is probably not correct *)
      (bvl_to_target$compile c ((MAP (λe. (0,0,e)) es)++aux))`;

val _ = export_theory();
