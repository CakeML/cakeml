(*
  Compiler from Pancake to machine code
*)

open preamble
     pan_to_wordTheory backendTheory
     word_depthTheory word_to_wordTheory;

val _ = new_theory "pan_to_target";


Definition compile_prog_def:
  compile_prog c prog =
    (* Ensure either user-written main or new main that does nothing is first in func list *)
    let prog0 = case SPLITP (\(n,e,p,b). n = «main») prog of
                  ([],ys) => ys
                | (xs,[]) => («main»,F,[],Return (Const 0w))::xs
                | (xs,y::ys) => y::xs ++ ys in
    (* Prevent exported main functions *)
    if FST $ SND $ HD prog0 then NONE
    else
      (* Remove exported information from func list for compiler passes *)
      let prog1 = MAP (\(n,e,p,b). (n,p,b)) prog0 in
      (* Compiler passes *)
      let prog2 = pan_to_word$compile_prog c.lab_conf.asm_conf.ISA prog1 in
      let (col,prog3) = word_to_word$compile c.word_to_word_conf c.lab_conf.asm_conf prog2 in
      (* Add user functions to name mapping *)
      let names = fromAList (ZIP (MAP FST prog2,  (* func numbers *)
                                  MAP FST prog1   (* func names *)
                  )) : mlstring$mlstring num_map in
      (* Add stubs to name mapping *)
      let names = sptree$union (sptree$fromAList $ (word_to_stack$stub_names () ++
        stack_alloc$stub_names () ++ stack_remove$stub_names ())) names in
      (* Add exported functions to  *)
      let c = c with exported := MAP FST (FILTER (FST o SND) prog) in
        from_word c names prog3
End

(*  TODO: evaluate max_depth ... (full_call_graph dest (fromAList prog))  *)

val _ = export_theory();
