Theory bvi_lclunf
Ancestors
  bvi
Libs
  preamble


        
Datatype:
  rename_kind = Push num | ReorderAdd num num num | Delay num
End

Definition revar_ssh_def:
  (revar_ssh [] _ n = n) ∧
  (revar_ssh (x::xs) ssh n =
   case x of
     Push push =>
       (let n' = revar_ssh xs ssh n in
          if ssh ≤ n' then n' + push else n')
   | ReorderAdd n1 n2 v =>
       (let n' = revar_ssh xs ssh n in
          if n' < ssh then n'
          else if n' < ssh + n1 then n' + n2 + v
          else if n' < ssh + n1 + n2 then n' - n1
          else n' + v)
   | Delay d => revar_ssh xs (ssh + d) n)
End

Definition revar_def:
  revar rn n = revar_ssh rn 0 n
End

Definition rename_def:
  (rename rs (Var n) = Var (revar rs n)) ∧
  (rename rs (If g t e) = If (rename rs g) (rename rs t) (rename rs e)) ∧
  (rename rs (Let vs e) = renames (Delay (LENGTH vs)::rs) rs vs e []) ∧
  (rename rs (Raise e) = Raise (rename rs e)) ∧
  (rename rs (Tick e) = Tick (rename rs e)) ∧
  (rename rs (Call ticks fn args hdl) =
   Call ticks fn (renamel rs args) (OPTION_MAP (rename (Delay 1::rs)) hdl)) ∧
  (rename rs (Force loc n) = Force loc (revar rs n)) ∧
  (rename rs (Op op es) = Op op (renamel rs es)) ∧
  (rename rs (LetCall nret ticks fn args body) =
   LetCall nret ticks fn (renamel rs args) (rename (Delay nret::rs) body)) ∧
  (rename rs (Return es) = Return (renamel rs es)) ∧

  (renamel rs [] = []) ∧
  (renamel rs (y::ys) = rename rs y :: renamel rs ys) ∧

  (renames rs bs [] e racc = Let (REVERSE racc) (rename rs e)) ∧
  (renames rs bs (x::xs) e racc =
   case x of
     LetCall nret ticks fn args body =>
       (let k = LENGTH racc in
        let f = case racc of
                  [] => I
                | _ => Let (REVERSE racc)
        in
          f (LetCall nret ticks fn (renamel (Push k::bs) args)
                     (renames (ReorderAdd k (LENGTH xs + 1) nret::rs)
                              (Push (nret + k)::bs)
                              xs e
                              [rename (Delay nret::Push k::bs) body])))
   | _ => renames rs bs xs e (rename bs x::racc))
Termination
  wf_rel_tac ‘measure (λx.
                         case x of
                           INL (_, e)                  => 2 * exp_size e
                         | INR (INL (_, es))           => 2 * list_size exp_size es + 1
                         | INR (INR (_, _, xs, e, _))  => 2 * (list_size exp_size xs +
                                                               exp_size e) + 1)’
End

Definition lc_unfold_def:
  lc_unfold e = rename [] e
End

val lclunf_test1 = “Let [Op (IntOp (Const 0)) [];
                         Op (IntOp (Const 1)) []]
                    (Let [Op (IntOp (Const 2)) [];
                          LetCall 2 0 300 [Var 0; Var 1]
                                  (Op (BlockOp (Cons 0)) [Var 0; Var 1; Var 2]);
                          Op (IntOp (Const 3)) []]
                         (Op (BlockOp (Cons 0))
                             [Var 0; Var 1; Var 2; Var 3; Var 4]))”

val lclunf_res1 = “Let [Op (IntOp (Const 0)) []; Op (IntOp (Const 1)) []]
                   (Let [Op (IntOp (Const 2)) []]
                        (LetCall 2 0 300 [Var 1; Var 2]
                                 (Let
                                  [Op (BlockOp (Cons 0)) [Var 0; Var 1; Var 3];
                                   Op (IntOp (Const 3)) []]
                                  (Op (BlockOp (Cons 0)) [Var 4; Var 0; Var 1; Var 5; Var 6]))))”

Theorem lclunf_test1_thm:
  lc_unfold ^lclunf_test1 = ^lclunf_res1
Proof
  EVAL_TAC
QED

val lclunf_test2 = “(Let [LetCall 1 0 300 [] (Var 0); Var 0]
                       (Op (BlockOp (Cons 0)) [Var 0; Var 1]))”



val lclunf_res2 = “LetCall 1 0 300 []
                   (Let [Var 0; Var 1] (Op (BlockOp (Cons 0)) [Var 0; Var 1]))”

Theorem lclunf_test2_thm:
  lc_unfold ^lclunf_test2 = ^lclunf_res2
Proof
  EVAL_TAC
QED


val lclunf_test3 = “(Let [Op (IntOp (Const 0)) [];
                          LetCall 1 0 300 []
                                  (Let [Op (IntOp (Const 1)) []] (Var 1));
                          Op (IntOp (Const 2)) []]
                         (Op (BlockOp (Cons 0)) [Var 0; Var 1; Var 2]))”



val lclunf_res3 = “Let [Op (IntOp (Const 0)) []]
                   (LetCall 1 0 300 []
                            (Let
                             [Let [Op (IntOp (Const 1)) []] (Var 1); Op (IntOp (Const 2)) []]
                             (Op (BlockOp (Cons 0)) [Var 3; Var 0; Var 1])))”

Theorem lclunf_test3_thm:
  lc_unfold ^lclunf_test3 = ^lclunf_res3
Proof
  EVAL_TAC
QED

               
