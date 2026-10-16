(*
  Tests for ClosLang smart operation construction.
*)
Theory clos_op_test[no_sig_docs]
Ancestors
  clos_op
Libs
  preamble

Theorem eq_pure_list_test[local]:
   append
       (eq_pure_list
          [(Var None 5,
            Op None (BlockOp (Cons 70)) [Op None (IntOp (Const 2)) []; Op None (BlockOp (Cons 4)) []])]) =
     [Op None (BlockOp (TagLenEq 70 2)) [Var None 5];
      Op None (BlockOp (TagLenEq 4 0)) [Op None (BlockOp (ElemAt 0)) [Var None 5]];
      Op None (BlockOp (EqualConst (Int 2))) [Op None (BlockOp (ElemAt 1)) [Var None 5]]]
Proof
  EVAL_TAC
QED
