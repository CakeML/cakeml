(*
  Compiler from Pancake to machine code
*)
Theory pan_to_target
Libs
  preamble
Ancestors
  mllist pan_to_word backend word_depth word_to_word

Definition exports_def:
  (exports(Function fi::ds) =
   if fi.export then fi.name::exports ds
   else exports ds) ∧
  exports (_::ds) = exports ds ∧
  exports [] = []
End

Definition compile_prog_def:
  compile_prog c prog =
    (* Ensure either user-written main or new main that does nothing is first in func list *)
    let prog1:'a decl list = case SPLITP (λx. case x of
                                   Function fi => fi.name = «main»
                                 | Decl _ _ _ => F) prog of
                  ([],ys) => ys
                | (xs,[]) => Function
                                <| name := «main»
                                 ; inline := F
                                 ; export := F
                                 ; params := []
                                 ; body := Return (Const 0w)
                                 ; return := One
                                |>
                                ::xs
                | (xs,y::ys) => y::xs ++ ys in
    (* Compiler passes *)
    let prog2 = pan_to_word$compile_prog c.lab_conf.asm_conf.ISA prog1 in
    let (col,prog3) = word_to_word$compile c.word_to_word_conf c.lab_conf.asm_conf prog2 in
    let c = c with
            word_to_word_conf updated_by (λc. c with col_oracle := col) in
    (* Add user functions to name mapping *)
    let names = fromAList (ZIP (sort $< (MAP FST prog2), (* func numbers *)
                                «generated_main»::
                                MAP FST (functions prog1) (* func names *)
                          )) : mlstring$mlstring num_map in
    (* Add stubs to name mapping *)
    let names = sptree$union (sptree$fromAList $ (word_to_stack$stub_names () ++
      stack_alloc$stub_names () ++ stack_remove$stub_names ())) names in
    (* Add exported functions to  *)
    let c = c with exported := exports prog in
      from_word c names prog3
End

(*  TODO: evaluate max_depth ... (full_call_graph dest (fromAList prog))  *)

Theorem compile_prog_eq:
  compile_prog c prog =
    (* Ensure either user-written main or new main that does nothing is first in func list *)
    let prog1:'a decl list = case SPLITP (λx. case x of
                                   Function fi => fi.name = «main»
                                 | Decl _ _ _ => F) prog of
                  ([],ys) => ys
                | (xs,[]) => Function
                                <| name := «main»
                                 ; inline := F
                                 ; export := F
                                 ; params := []
                                 ; body := Return (Const 0w)
                                 ; return := One
                                |>
                                ::xs
                | (xs,y::ys) => y::xs ++ ys in
    (* Compiler passes *)
    let prog2 = pan_to_word$compile_prog c.lab_conf.asm_conf.ISA prog1 in
    (* Add user functions to name mapping *)
    let names = fromAList (ZIP (sort $< (MAP FST prog2), (* func numbers *)
                                «generated_main»::
                                MAP FST (functions prog1) (* func names *)
                          )) : mlstring$mlstring num_map in
    (* Add stubs to name mapping *)
    let names = sptree$union (sptree$fromAList $ (word_to_stack$stub_names () ++
                stack_alloc$stub_names () ++ stack_remove$stub_names ())) names in
    let c = c with exported := exports prog in
      from_word_0 c names prog2
Proof
  rewrite_tac [compile_prog_def,LET_THM]
  \\ AP_THM_TAC \\ gvs [FUN_EQ_THM] \\ rw []
  \\ pairarg_tac \\ gvs[from_word_0_def]
QED
