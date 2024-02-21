(*
  Compiler from Pancake to machine code
*)

open preamble
     pan_to_wordTheory backendTheory
     word_depthTheory word_to_wordTheory;

val _ = new_theory "pan_to_target";


Definition compile_prog_def:
  compile_prog c prog =
    let prog0 = case SPLITP (\(n,e,p,b). n = «main») prog of
                  ([],ys) => ys
                | (xs,[]) => («main»,F,[],Return (Const 0w))::xs
                | (xs,y::ys) => y::xs ++ ys in
    let prog1 = MAP (\(n,e,p,b). (n,p,b)) prog0 in
    let prog2 = pan_to_word$compile_prog c.lab_conf.asm_conf.ISA prog1 in
    let (col,prog3) = word_to_word$compile c.word_to_word_conf c.lab_conf.asm_conf prog2 in
    let names = fromAList (ZIP (MAP FST prog2,  (* func numbers *)
                                MAP FST prog1   (* func names *)
                )) : mlstring$mlstring num_map in
    let names = sptree$union (sptree$fromAList $ (word_to_stack$stub_names () ++
      stack_alloc$stub_names () ++ stack_remove$stub_names ())) names in
    let c = c with exposed := MAP FST (FILTER (FST o SND) prog) in
      from_word c names prog3
End

(*  TODO: evaluate max_depth ... (full_call_graph dest (fromAList prog))  *)

val _ = export_theory();
