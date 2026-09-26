(*
  Constructed product result (CPR) optimisation for BVI.

  A function whose tail positions all build [Cons] blocks of one shape
  (or raise, or tail call functions already split with that shape) is
  split in two. The worker, at a fresh name, returns the fields with
  [Return], in [Op] argument order. The wrapper keeps the original name
  and is [LetCall w 0 worker (GENLIST Var arity) (rebuild 0 sh)]: it calls
  the worker and rebuilds the block. Tail calls to split functions in a
  worker become tail calls to their workers.
*)
Theory bvi_cpr
Ancestors
  bvi backend_common[qualified] bvi_inline[qualified]
Libs
  preamble

Datatype:
  cpr_shape = Leaf
            | ConsShape num (cpr_shape list)
            | Flexible
End

Definition sub_shape_def:
  (sub_shape Leaf _ = T) ∧
  (sub_shape (ConsShape n1 l1) (ConsShape n2 l2) = if n1 = n2 then sub_shape_list l1 l2 else F) ∧
  (sub_shape _ Flexible = T) ∧
  (sub_shape _ _ = F) ∧

  (sub_shape_list [] [] = T) ∧
  (sub_shape_list (e::es) (e'::es') = (sub_shape e e' ∧ sub_shape_list es es')) ∧
  (sub_shape_list _ _ = F)
End

Definition cpr_merge_def:
  (cpr_merge _ Leaf = Leaf) ∧
  (cpr_merge Leaf _ = Leaf) ∧
  (cpr_merge sh Flexible = sh) ∧
  (cpr_merge Flexible sh = sh) ∧
  (cpr_merge (ConsShape t1 xs) (ConsShape t2 ys) =
   if t1 = t2 /\ LENGTH xs = LENGTH ys
   then ConsShape t1 (cpr_merge_list xs ys)
   else Leaf) ∧

  (cpr_merge_list [] ys = []) ∧
  (cpr_merge_list xs [] = []) ∧
  (cpr_merge_list (x::xs) (y::ys) = cpr_merge x y :: cpr_merge_list xs ys)
End


Definition field_shape_def:
  (field_shape (Op (BlockOp (Cons t)) xs) = ConsShape t (field_shape_list xs)) /\
  (field_shape _ = Leaf) /\
  (field_shape_list [] = []) /\
  (field_shape_list (x::xs) = field_shape x :: field_shape_list xs)
End

Definition shape_and_tail_def:
  (shape_and_tail fname (Var n) = (Leaf, [])) /\
  (shape_and_tail fname (If g e1 e2) =
   let (sh1, c1) = shape_and_tail fname e1;
       (sh2, c2) = shape_and_tail fname e2
   in
     (cpr_merge sh1 sh2, c1 ++ c2)) /\
  (shape_and_tail fname (Let xs b) =
     shape_and_tail fname b) /\
  (shape_and_tail fname (Raise e) = (Flexible, [])) /\
  (shape_and_tail fname (Tick e) = shape_and_tail fname e) /\
  (shape_and_tail fname (Call ts dest args hdl) =
   case hdl of
     SOME _ => (Leaf, [])
   | NONE =>
       case dest of
         SOME dname => if fname = dname then (Flexible, []) else (Flexible, [dname])
       | _ => (Leaf, [])) /\
  (shape_and_tail fname (Force loc v) = (Leaf,[])) /\
  (shape_and_tail fname (Op op xs) = (field_shape (Op op xs), [])) /\
  (shape_and_tail fname (LetCall ret ticks dest args b) =
     shape_and_tail fname b) /\
  (shape_and_tail fname (Return xs) = (Leaf, []))
End

(* csh_map is a map of function to (worker_shape, worker) option *)
Definition tail_shape_def:
  (tail_shape _ [] = Flexible) ∧
  (tail_shape csh_map (f::fs) =
   case lookup f csh_map of
     NONE => Leaf
   | SOME (csh, wk:num) => case tail_shape csh_map fs of
                   Flexible => csh
                 | fsh => if fsh = csh then fsh else Leaf)
End

Definition return_shape_def:
  return_shape csh_map fname body =
  let (sh, cs) = shape_and_tail fname body;
      csh = tail_shape csh_map cs
  in
    case (csh, sh) of
        (Flexible, _) => sh
      | (_, Flexible) => csh
      | _ => if sub_shape csh sh then csh else Leaf
End

Definition shape_width_def:
  (shape_width Leaf = 1n) ∧
  (shape_width Flexible = 1) ∧
  (shape_width (ConsShape t shs) = shape_width_list shs) ∧

  (shape_width_list [] = 0) ∧
  (shape_width_list (sh::shs) = shape_width sh + shape_width_list shs)
End

Definition split_ok_def:
  split_ok sh ⇔ shape_width sh > 1
End

Definition flatten_exp_def:
  (flatten_exp Leaf e = [e]) ∧
  (flatten_exp Flexible e = [e]) ∧
  (flatten_exp (ConsShape t shs) e =
     case e of
       Op (BlockOp (Cons tag)) xs =>
         if tag = t ∧ LENGTH xs = LENGTH shs
         then flatten_list shs xs
         else [e]
     | _ => [e]) ∧

  (flatten_list [] xs = []) ∧
  (flatten_list shs [] = []) ∧
  (flatten_list (sh::shs) (x::xs) =
   flatten_exp sh x ++ flatten_list shs xs)
End

(* Call --> LetCall *)
Definition worker_body_def:
  (worker_body csh_map fname next sh (If g e1 e2) =
     If g (worker_body csh_map fname next sh e1) (worker_body csh_map fname next sh e2)) ∧
  (worker_body csh_map fname next sh (Let xs b) = Let xs (worker_body csh_map fname next sh b)) ∧
  (worker_body csh_map fname next sh (Tick e) = Tick (worker_body csh_map fname next sh e)) ∧
  (worker_body csh_map fname next sh (Raise e) = Raise e) ∧
  (worker_body csh_map fname next sh (LetCall ret ticks dest args b) =
     LetCall ret ticks dest args (worker_body csh_map fname next sh b)) ∧
  (worker_body csh_map fname next sh (Return xs) = Return xs) ∧
  (worker_body csh_map fname next sh (Call ts dest args hdl) =
   case hdl of
     SOME _ => Call ts dest args hdl
   | NONE =>
       case dest of
         SOME dname => (if fname = dname then TailCall (shape_width sh) ts next args
                        else case lookup dname csh_map of
                             | NONE => Call ts dest args hdl
                             | SOME (csh:cpr_shape, dwk:num) => TailCall (shape_width sh) ts dwk args)
       | _ => Call ts dest args hdl) ∧
  (worker_body csh_map fname next sh e = Return (flatten_exp sh e))
End

Definition rebuild_def:
  (rebuild i Leaf = Var i) ∧
  (rebuild i Flexible = Var i) ∧
  (rebuild i (ConsShape t shs) =
     Op (BlockOp (Cons t)) (rebuild_list i shs)) ∧

  (rebuild_list i [] = []) ∧
  (rebuild_list i (sh::shs) =
   rebuild i sh :: rebuild_list (i + shape_width sh) shs)
End


Definition make_wrapper_def:
  make_wrapper arity next sh =
    LetCall (shape_width sh) 0 next (GENLIST Var arity)
            (rebuild 0 sh)
End

Definition no_ret_def:            (* no Return anywhere *)
  (no_ret (If g e1 e2) ⇔ no_ret g ∧ no_ret e1 ∧ no_ret e2) ∧
  (no_ret (Let xs e) ⇔ no_ret_list xs ∧ no_ret e) ∧
  (no_ret (Tick e) ⇔ no_ret e) ∧
  (no_ret (Raise e) ⇔ no_ret e) ∧
  (no_ret (Return xs) ⇔ F) ∧
  (no_ret (Call ts d args hdl) ⇔
     no_ret_list args ∧ case hdl of NONE => T | SOME h => no_ret h) ∧
  (no_ret (LetCall r ts d args e) ⇔ no_ret_list args ∧ no_ret e) ∧
  (no_ret (Op op es) ⇔ no_ret_list es) ∧
  (no_ret e ⇔ T) ∧

  (no_ret_list [] ⇔ T) ∧
  (no_ret_list (x::xs) ⇔ (no_ret x ∧ no_ret_list xs))
End

Definition tail_form_def:         (* Return only in tail position *)
  (tail_form (If g e1 e2) ⇔ no_ret g ∧ tail_form e1 ∧ tail_form e2) ∧
  (tail_form (Let xs e) ⇔ no_ret_list xs ∧ tail_form e) ∧
  (tail_form (Tick e) ⇔ tail_form e) ∧
  (tail_form (LetCall r ts d args e) ⇔ no_ret_list args ∧ tail_form e) ∧
  (tail_form (Return xs) ⇔ no_ret_list xs) ∧
  (tail_form e ⇔ no_ret e)
End

Definition split_fun_def:
  split_fun csh_map next loc arity body =
    let sh = return_shape csh_map loc body in
      if split_ok sh ∧ tail_form body then
        SOME (worker_body csh_map loc next sh body,          (* the worker  *)
              make_wrapper arity next sh,                    (* the wrapper *)
              insert loc (sh, next) csh_map)                 (* update map  *)
      else NONE
End

Definition compile_prog_with_map_def:
  (compile_prog_with_map csh_map next [] = ((next, csh_map), [])) ∧
  (compile_prog_with_map csh_map next ((loc:num, arity:num, exp)::xs) =
     case split_fun csh_map next loc arity exp of
       NONE =>
         let (st, ys) = compile_prog_with_map csh_map next xs in
           (st, (loc, arity, exp)::ys)
     | SOME (worker, wrapper, new_map) =>
         let (st, ys) = compile_prog_with_map new_map (next + bvl_to_bvi_namespaces) xs in
           (st, (loc, arity, wrapper)::(next, arity, worker)::ys))
End

Definition compile_prog_def:
  compile_prog do_it (next, csh_map) xs =
    if do_it then compile_prog_with_map csh_map next xs
    else ((next, csh_map), xs)
End

(* Examples; the argument of each function is [Var 0]. *)

val flat_body =
  “Op (BlockOp (Cons 0)) [Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]; Var 0]”

val nested_body =
  “If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
     (Let [Call 0 (SOME 324) [Var 0] NONE]
        (Op (BlockOp (Cons 0))
           [Op (BlockOp (Cons 0)) [Var 0; Var 0];
            Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]]))
     (Let [Call 0 (SOME 324) [Var 0] NONE]
        (Op (BlockOp (Cons 0))
           [Op (BlockOp (Cons 0))
              [Op (IntOp Add) [Var 0; Op (IntOp (Const 2)) []];
               Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]];
            Var 0]))”

val self_tail_body =
  “If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
     (Op (BlockOp (Cons 0)) [Var 0; Var 0])
     (Call 0 (SOME 1000) [Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]] NONE)”

val other_tail_body =
  “If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
     (Op (BlockOp (Cons 0)) [Var 0; Op (IntOp (Const 1)) []])
     (Call 0 (SOME 1000) [Var 0] NONE)”

val handler_body =
  “If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
     (Op (BlockOp (Cons 0)) [Var 0; Var 0])
     (Call 0 (SOME 1000) [Var 0] (SOME (Op (IntOp (Const 0)) [])))”

val let_bound_body =
  “Let [Op (BlockOp (Cons 0)) [Var 0; Var 0]] (Var 0)”

Theorem cpr_flat_example:
  compile_prog T (1100,LN) [(1000,1,^flat_body)] =
    ((1105,insert 1000 (ConsShape 0 [Leaf; Leaf],1100) LN),
     [(1000,1,LetCall 2 0 1100 [Var 0] (Op (BlockOp (Cons 0)) [Var 0; Var 1]));
      (1100,1,Return [Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]; Var 0])])
Proof
  EVAL_TAC
QED

Theorem cpr_nested_example:
  compile_prog T (1100,LN) [(1000,1,^nested_body)] =
    ((1105,insert 1000 (ConsShape 0 [ConsShape 0 [Leaf; Leaf]; Leaf],1100) LN),
     [(1000,1,
       LetCall 3 0 1100 [Var 0]
         (Op (BlockOp (Cons 0)) [Op (BlockOp (Cons 0)) [Var 0; Var 1]; Var 2]));
      (1100,1,
       If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
         (Let [Call 0 (SOME 324) [Var 0] NONE]
            (Return
               [Var 0; Var 0; Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]]))
         (Let [Call 0 (SOME 324) [Var 0] NONE]
            (Return
               [Op (IntOp Add) [Var 0; Op (IntOp (Const 2)) []];
                Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]; Var 0])))])
Proof
  EVAL_TAC
QED

(* A self tail call, and a tail call to a function split earlier, become
   tail calls to the workers. *)
Theorem cpr_tail_call_example:
  compile_prog T (1100,LN)
    [(1000,1,^self_tail_body); (1004,1,^other_tail_body)] =
    ((1110,insert 1004 (ConsShape 0 [Leaf; Leaf],1105)
             (insert 1000 (ConsShape 0 [Leaf; Leaf],1100) LN)),
     [(1000,1,LetCall 2 0 1100 [Var 0] (Op (BlockOp (Cons 0)) [Var 0; Var 1]));
      (1100,1,
       If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
         (Return [Var 0; Var 0])
         (TailCall 2 0 1100 [Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]]));
      (1004,1,LetCall 2 0 1105 [Var 0] (Op (BlockOp (Cons 0)) [Var 0; Var 1]));
      (1105,1,
       If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
         (Return [Var 0; Op (IntOp (Const 1)) []])
         (TailCall 2 0 1100 [Var 0]))])
Proof
  EVAL_TAC
QED

(* A call with a handler in tail position, and a tuple bound by [Let],
   prevent the split; with [do_it = F] nothing changes. *)
Theorem cpr_unchanged_examples:
  compile_prog T (1100,LN)
    [(1000,1,^handler_body); (1004,1,^let_bound_body)] =
    ((1100,LN),[(1000,1,^handler_body); (1004,1,^let_bound_body)]) ∧
  compile_prog F (1100,LN) [(1000,1,^flat_body)] =
    ((1100,LN),[(1000,1,^flat_body)])
Proof
  EVAL_TAC
QED

(* bvi_inline inlines the wrapper into a (non-tail) caller. *)
Theorem cpr_inline_example:
  SND (bvi_inline$compile_prog
         (SND (compile_prog T (1100,LN)
                 [(1000,1,^flat_body);
                  (1004,1,Op (BlockOp (ElemAt 0))
                            [Call 0 (SOME 1000) [Var 0] NONE])]))) =
    [(1000,1,LetCall 2 0 1100 [Var 0] (Op (BlockOp (Cons 0)) [Var 0; Var 1]));
     (1100,1,Return [Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]; Var 0]);
     (1004,1,
      Op (BlockOp (ElemAt 0))
        [Let [Var 0]
           (LetCall 2 0 1100 [Var 0] (Op (BlockOp (Cons 0)) [Var 0; Var 1]))])]
Proof
  EVAL_TAC
QED
