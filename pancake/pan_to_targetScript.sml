(*
  Compiler from Pancake to machine code
*)

open preamble
     pan_to_wordTheory backendTheory
     word_depthTheory word_to_wordTheory;

val _ = new_theory "pan_to_target";


Definition compile_prog_def:
  compile_prog asm_conf c prog =
    (* Ensure either user-written main or new main that does nothing is first in func list *)
    let prog0 = case SPLITP (\(n,e,p,b). n = «main») prog of
                  ([],ys) => ys
                | (xs,[]) => («main»,F,[],Return (Const 0w))::xs
                | (xs,y::ys) => y::xs ++ ys in
    (* Remove exported information from func list for compiler passes *)
    let prog1 = MAP (\(n,e,p,b). (n,p,b)) prog0 in
    (* Compiler passes *)
    let prog2 = pan_to_word$compile_prog asm_conf.ISA prog1 in
    let (col,prog3) = word_to_word$compile c.word_to_word_conf asm_conf prog2 in
    let c = c with
            word_to_word_conf updated_by (λc. c with col_oracle := col) in
    (* Add user functions to name mapping *)
    let names = fromAList (ZIP (QSORT $< (MAP FST prog2),  (* func numbers *)
                                MAP FST prog1              (* func names *)
                          )) : mlstring$mlstring num_map in
    (* Add stubs to name mapping *)
    let names = sptree$union (sptree$fromAList $ (word_to_stack$stub_names () ++
      stack_alloc$stub_names () ++ stack_remove$stub_names ())) names in
    (* Add exported functions to  *)
    let c = c with exported := MAP FST (FILTER (FST o SND) prog) in
      from_word c names prog3
End

(*  TODO: evaluate max_depth ... (full_call_graph dest (fromAList prog))  *)

Theorem compile_prog_eq:
  compile_prog asm_conf c prog =
    (* Ensure either user-written main or new main that does nothing is first in func list *)
    let prog0 = case SPLITP (\(n,e,p,b). n = «main») prog of
                  ([],ys) => ys
                | (xs,[]) => («main»,F,[],Return (Const 0w))::xs
                | (xs,y::ys) => y::xs ++ ys in
    (* Remove exported information from func list for compiler passes *)
    let prog1 = MAP (\(n,e,p,b). (n,p,b)) prog0 in
    (* Compiler passes *)
    let prog2 = pan_to_word$compile_prog asm_conf.ISA prog1 in
    (* Add user functions to name mapping *)
    let names = fromAList (ZIP (QSORT $< (MAP FST prog2),  (* func numbers *)
                                MAP FST prog1              (* func names *)
                          )) : mlstring$mlstring num_map in
    (* Add stubs to name mapping *)
    let names = sptree$union (sptree$fromAList $ (word_to_stack$stub_names () ++
                stack_alloc$stub_names () ++ stack_remove$stub_names ())) names in
    let c = c with exported := MAP FST (FILTER (FST o SND) prog) in
      from_word_0 asm_conf c names prog2
Proof
  rewrite_tac [compile_prog_def,LET_THM]
  \\ AP_THM_TAC \\ gvs [FUN_EQ_THM] \\ rw []
  \\ pairarg_tac \\ gvs[from_word_0_def]
QED

val _ = export_theory();
