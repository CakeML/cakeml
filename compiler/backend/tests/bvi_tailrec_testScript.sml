(*
  Tests for the BVI tail recursion pass.
*)
Theory bvi_tailrec_test[no_sig_docs]
Ancestors
  bvi_tailrec
Libs
  preamble

val test1_tm = ``Let [] (Call 0 (SOME 0) [] NONE)``
Theorem has_rec_test1:
   has_rec1 0 ^test1_tm <=> F
Proof
EVAL_TAC
QED

val test2_tm = ``Op (IntOp Add) [Call 0 (SOME 0) [] NONE; Var 0]``
Theorem has_rec_test2:
   has_rec1 0 ^test2_tm <=> T
Proof
EVAL_TAC
QED

(* --- Test rewriting --- *)

val fac_tm = ``
  Let [Op (IntOp LessEq) [Var 0; Op (IntOp (Const 1)) []]]
    (If (Var 0)
       (Op (IntOp (Const 1)) [])
       (Let [Op (IntOp Sub) [Op (IntOp (Const 1)) []; Var 1]]
         (Op (IntOp Mult) [Var 2; Call 0 (SOME 0) [Var 0] NONE])))``

val opt_tm = ``
  Let [Op (IntOp LessEq) [Var 0; Op (IntOp (Const 1)) []]]
     (If (Var 0) (Op (IntOp Mult) [Var 2; Op (IntOp (Const 1)) []])
        (Let [Op (IntOp Sub) [Op (IntOp (Const 1)) []; Var 1]]
           (Call 0 (SOME 1) [Var 0; Op (IntOp Mult) [Var 3; Var 2]]
              NONE)))``
val aux_tm = ``Let [Var 0; Op (IntOp (Const 1)) []] ^opt_tm``

Theorem fac_check_exp[local]:
   check_exp 0 1 ^fac_tm = SOME Times
Proof
  EVAL_TAC
QED

Theorem fac_compile_exp:
   compile_exp 0 1 1 ^fac_tm = SOME (^aux_tm, ^opt_tm)
Proof
  EVAL_TAC
QED

val rev_tm = ``
  Let [Op (IntOp (Const 0)) []]
    (If (Op (BlockOp (TagLenEq 0 0)) [Var 1])
        (Op (BlockOp (Cons 0)) [])
        (Let [Op (MemOp El) [Op (IntOp (Const 0)) []; Var 1]]
          (Let [Op (MemOp El) [Op (IntOp (Const 1)) []; Var 2]]
            (Op (BlockOp ListAppend)
              [Op (BlockOp (Cons 0)) [Op (BlockOp (Cons 0)) []; Var 1];
               Call 0 (SOME 444) [Var 0] NONE]))))``

val opt_tm = ``
  Let [Op (IntOp (Const 0)) []]
    (If (Op (BlockOp (TagLenEq 0 0)) [Var 1])
        (Op (BlockOp ListAppend) [Var 2; Op (BlockOp (Cons 0)) []])
        (Let [Op (MemOp El) [Op (IntOp (Const 0)) []; Var 1]]
          (Let [Op (MemOp El) [Op (IntOp (Const 1)) []; Var 2]]
            (Call 0 (SOME 445)
              [Var 0;
               Op (BlockOp ListAppend) [Var 4; Op (BlockOp (Cons 0)) [Op (BlockOp (Cons 0)) []; Var 1]]]
              NONE))))``

val aux_tm = ``Let [Var 0; Op (BlockOp (Cons 0)) []] ^opt_tm``

Theorem rev_check_exp[local]:
  check_exp 444 1 ^rev_tm = SOME Append
Proof
  EVAL_TAC
QED

Theorem rev_compile_exp[local]:
  compile_exp 444 445 1 ^rev_tm = SOME (^aux_tm, ^opt_tm)
Proof
  EVAL_TAC
QED
