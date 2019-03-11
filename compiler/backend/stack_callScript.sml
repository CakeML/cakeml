(*

Comment here

*)

open preamble stackLangTheory sptreeTheory;

val _ = new_theory "stack_call";

val get_alloc_def = Define `
  (get_alloc (Seq (StackAlloc mem) y) = mem) /\
  (get_alloc _ = 0)
`;

val mem_reqs_def = Define `
  (mem_reqs [] tree = tree)  /\
  (mem_reqs ((name, prog)::xs) tree =
    mem_reqs xs (insert name (get_alloc prog) tree))
`;

val strip_fun_def = Define `
  (strip_fun (Seq x y) raw_name = Seq x (Call NONE (INL raw_name) NONE)) /\
  (strip_fun p raw_name = Call NONE (INL raw_name) NONE)
`;

val create_raw_ep_def = Define `
  (create_raw_ep (Seq x y) = y) /\
  (create_raw_ep z = z)
`;

val new_mem_def = Define `
  (new_mem curr_mem dest_mem =
      if dest_mem < curr_mem then StackFree (curr_mem - dest_mem) else
      if curr_mem < dest_mem then StackAlloc (dest_mem - curr_mem) else
      Skip)
`;

val dest_StackFree_def = Define `
  (dest_StackFree (StackFree m) = SOME m) /\
  (dest_StackFree _ = NONE)
`;

val dest_Call_NONE_INL_def = Define `
  (dest_Call_NONE_INL (Call NONE (INL name) NONE) = SOME name) /\
  (dest_Call_NONE_INL _ = NONE)
`;

val opt_code_def = Define `
  opt_code prog tree =
    case prog of
    | Seq x y => (case (dest_StackFree x, dest_Call_NONE_INL y) of
                 | (SOME curr_mem, SOME name) =>
        (case lookup name tree of
         | NONE => Seq x y
         | SOME dest_mem =>
             Seq (new_mem curr_mem dest_mem)
                 (Call NONE (INL (name + 1)) NONE))
           | _ => Seq (opt_code x tree) (opt_code y tree))
    | If c r ri x y =>
        If c r ri (opt_code x tree) (opt_code y tree)
    | While c r ri x => While c r ri (opt_code x tree)
    | p => p
`;

val create_raw_eps_def = Define `
  (create_raw_eps [] tree = []) /\
  (create_raw_eps ((name, prog)::xs) tree =
    let raw_ep = create_raw_ep prog in
    let raw_name = name + 1 in
      (name, strip_fun prog raw_name)::
       (raw_name, opt_code raw_ep tree)::create_raw_eps xs tree)
`;

val compile_def = Define `
  compile stack_lang_prog =
    let tree = mem_reqs stack_lang_prog LN in
      (create_raw_eps stack_lang_prog tree, tree)
`;

val _ = export_theory ();