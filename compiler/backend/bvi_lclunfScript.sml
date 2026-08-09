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

(*
  rename  rs e                : rs renames e's free indices.
  renamel rs es               : rs renames every element of es.
  renames rs bs xs e racc     : rs  renames the tail e,
                                bs  renames the remaining bindings xs,
                                racc is the reversed list of already-emitted
                                     target bindings, pending in a Let that
                                     has not been closed yet.

  The ReorderAdd triple (LENGTH racc, LENGTH xs + 1, nret) is forced by
  env_rel_ReorderAdd in section 5 -- see the LetCall case of rename_eq.
  Do not "simplify" it without redoing that step.

  The Call handler is deliberately left as OPTION_MAP: it is not a list
  traversal, so there is nothing to make mutually recursive.  If you want it
  gone too, write

    (case hdl of NONE => NONE | SOME h => SOME (rename (Delay 1::rs) h))

  and delete the ETA_CONV line plus the IS_SOME subgoal in the Call case.
*)
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
  (* every subgoal is now a first-order size comparison; the +1 on the list
     branch is what makes `rename` -> `renamel` and `renamel` -> `rename`
     decrease in opposite directions.  If the sum pattern above does not
     typecheck, print the goal left by wf_rel_tac -- the injection nesting is
     INL / INR o INL / INR o INR for three clause groups in this order. *)
End

Definition lc_unfold_def:
  lc_unfold e = rename [] e
End

Definition compile_prog_def:
  compile_prog prog = MAP (λ(n,arity,body). (n, arity, lc_unfold body)) prog
End

(* -------------------------------------------------------------------------
   2.  Examples / regression tests   (unchanged: renamel rs = MAP (rename rs)
       extensionally, so all three still EVAL to the same terms)
   ------------------------------------------------------------------------- *)

(*
  test1 -- the original example.  Verified by hand: with the final target env
  [l; v2] ++ [r0; r1; c2; v0; v1] ++ env0, the tail's source indices
  0..4 = (c2, l, c3, v0, v1) map to 4, 0, 1, 5, 6.

    Let [Op (Const 0) []; Op (Const 1) []]
      (Let [Op (Const 2) []]
        (LetCall 2 0 300 [Var 1; Var 2]
          (Let [Op (Cons 0) [Var 0; Var 1; Var 3]; Op (Const 3) []]
            (Op (Cons 0) [Var 4; Var 0; Var 1; Var 5; Var 6]))))
*)
val lcop_test1 =
  EVAL “lc_unfold (Let [Op (IntOp (Const 0)) [];
                        Op (IntOp (Const 1)) []]
                       (Let [Op (IntOp (Const 2)) [];
                             LetCall 2 0 300 [Var 0; Var 1]
                               (Op (BlockOp (Cons 0)) [Var 0; Var 1; Var 2]);
                             Op (IntOp (Const 3)) []]
                            (Op (BlockOp (Cons 0))
                                [Var 0; Var 1; Var 2; Var 3; Var 4])))”;

(*
  test2 -- regression for bug 1.  The binding after the hoisted call must be
  shifted past the call result.  Expected:

    LetCall 1 0 300 []
      (Let [Var 0; Var 1] (Op (Cons 0) [Var 0; Var 1]))
*)
val lcop_test2 =
  EVAL “lc_unfold (Let [LetCall 1 0 300 [] (Var 0); Var 0]
                       (Op (BlockOp (Cons 0)) [Var 0; Var 1]))”;

(*
  test3 -- regression for bug 2.  A nested Let inside a hoisted body must not
  shift indices that the inner Let already protects.  Expected:

    Let [Op (Const 0) []]
      (LetCall 1 0 300 []
        (Let [Let [Op (Const 1) []] (Var 1); Op (Const 2) []]
          (Op (Cons 0) [Var 3; Var 0; Var 1])))
*)
val lcop_test3 =
  EVAL “lc_unfold (Let [Op (IntOp (Const 0)) [];
                        LetCall 1 0 300 []
                          (Let [Op (IntOp (Const 1)) []] (Var 1));
                        Op (IntOp (Const 2)) []]
                       (Op (BlockOp (Cons 0)) [Var 0; Var 1; Var 2]))”;
