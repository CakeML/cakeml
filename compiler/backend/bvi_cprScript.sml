(*
  Perform constructed product result optimisation.
*)
Theory bvi_cpr
Ancestors
  bvi backend_common[qualified]
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

val sub_shape_test = EVAL “sub_shape (ConsShape 1 [Leaf;Leaf]) (ConsShape 1 [ConsShape 2 [Leaf]; Leaf])”

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

Definition shape_and_tail_def:
  (shape_and_tail fname env (Var n) = (Leaf, [])) /\
  (shape_and_tail fname env (If g e1 e2) =
   let (sh1, c1) = shape_and_tail fname env e1;
       (sh2, c2) = shape_and_tail fname env e2
   in
     (cpr_merge sh1 sh2, c1 ++ c2)) /\
  (shape_and_tail fname env (Let xs b) =
     shape_and_tail fname (REPLICATE (LENGTH xs) Leaf ++ env) b) /\
  (shape_and_tail fname env (Raise e) = (Flexible, [])) /\
  (shape_and_tail fname env (Tick e) = shape_and_tail fname env e) /\
  (shape_and_tail fname env (Call ts dest args hdl) =
   case dest of
     SOME dname => if fname = dname then (Flexible, []) else (Flexible, [dname])
   | _ => (Leaf, [])) /\
  (shape_and_tail fname env (Force loc v) = (Leaf,[])) /\
  (shape_and_tail fname env (Op op xs) =
     (case op of
        BlockOp (Cons tag) =>
          let (shl, cs) = shape_and_tail_list fname env xs in
          (ConsShape tag shl, cs)
      | _ => (Leaf, []))) /\
  (shape_and_tail fname env (LetCall ret ticks dest args b) =
     shape_and_tail fname (REPLICATE ret Leaf ++ env) b) /\
  (shape_and_tail fname env (Return xs) = (Leaf, [])) ∧
  (shape_and_tail_list fname env xs =
   FOLDR (λx (shs, cs). let (xsh, xc) = shape_and_tail fname env x in
                          (xsh::shs, xc ++ cs))
         ([], []) xs)
Termination
  WF_REL_TAC ‘measure (\x. case x of
                             INL (_, _,e) => exp_size e
                           | INR (_,_,es) => list_size exp_size es)’
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

val tail_shape_test = EVAL “tail_shape (insert 1002 (ConsShape 1 [Leaf;Leaf], 2002)
                                               (insert 1000 (ConsShape 0 [Leaf;Leaf], 2000) LN)) [1000;1000]”


Definition return_shape_def:
  return_shape csh_map fname (arity:num) body =
  let (sh, cs) = shape_and_tail fname (REPLICATE arity Leaf) body;
      csh = tail_shape csh_map cs
  in
    case csh of
      Flexible => sh
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
   case dest of
     SOME dname => if fname = dname then TailCall (shape_width sh) 0 next args
                   else case lookup dname csh_map of
                        | NONE => Call ts dest args hdl
                        | SOME (csh:cpr_shape, dwk:num) => TailCall (shape_width sh) 0 dwk args
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
            (rebuild 1 sh)
End

Definition split_fun_def:
  split_fun csh_map next loc arity body =
    let sh = return_shape csh_map loc arity body in
      if split_ok sh then
        SOME (worker_body csh_map loc next sh body,          (* the worker  *)
              make_wrapper arity next sh,                    (* the wrapper *)
              insert loc (sh, next) csh_map)                 (* update map  *)
      else NONE
End
        
        
val test = “If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
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


val test1 = “If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
        (Let [Call 0 (SOME 324) [Var 0] NONE]
             (Op (BlockOp (Cons 0))
                 [Op (BlockOp (Cons 0)) [Var 0; Var 0; Op (IntOp Add) [Var 0; Op (IntOp (Const 2)) []]];
                  Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]]))
        (Let [Call 0 (SOME 324) [Var 0] NONE]
             (Op (BlockOp (Cons 0))
                 [Op (BlockOp (Cons 0))
                     [];
                  Var 0]))”


                  
val test_worker = “If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
        (Let [Call 0 (SOME 324) [Var 0] NONE]
             (Return [Var 0; Var 0; Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]]))
        (Let [Call 0 (SOME 324) [Var 0] NONE]
             (Return [Op (IntOp Add) [Var 0; Op (IntOp (Const 2)) []];
                      Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []];
                      Var 0]))”

val test_shape_and_tail = EVAL “shape_and_tail 1000 (REPLICATE 1 Leaf) ^test”
                       
val test_return_shape = EVAL “return_shape LN 1000 1 ^test”

val worker_eval  = EVAL “worker_body LN 1000 1100 (return_shape LN 1000 1 ^test1) ^test1”;
(* = ^test_worker *)

val wrapper_eval = EVAL “make_wrapper 1 next (return_shape LN 1000 1 ^test1)”;
(* = ^test_wrapper *)

val split_eval = EVAL “split_fun LN 1100 1000 1 ^test1”


val test2 = “If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
        (Let [Call 0 (SOME 324) [Var 0] NONE]
             (Op (BlockOp (Cons 0))
                 [Op (BlockOp (Cons 0)) [Var 0; Var 0; Op (IntOp Add) [Var 0; Op (IntOp (Const 2)) []]];
                  Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]]))
        (Let [Call 0 (SOME 324) [Var 0] NONE]
             (Call 0 (SOME 1000) [Var 0] NONE))”

val split_with_map_eval = EVAL “split_fun (insert 1000 (ConsShape 0 [Leaf; Leaf],1100) LN) 1102 1002 1 ^test2”


   
(* rec *)

val test_rec = “If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
        (Let [Call 0 (SOME 300) [Var 0] NONE]
             (Op (BlockOp (Cons 0))
                 [Op (BlockOp (Cons 0)) [Var 0; Var 0];
                  Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]]))
        (Let [Call 0 (SOME 300) [Var 0] NONE]
             (Call 0 (SOME 1000) [Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]] NONE))”


val test_return_shape_rec = EVAL “return_shape LN 1000 1 ^test_rec”

val worker_eval_rec = EVAL “worker_body LN 1000 1100 (return_shape LN 1000 1 ^test_rec) ^test_rec”;

val wrapper_eval_rec = EVAL “make_wrapper 1 1100 (return_shape LN 1000 1 ^test_rec)”;



   
(*
Definition compile_exp_def:
  compile_exp csh_map loc next arity exp =
    let sh = return_shape csh_map loc arity exp in
      if split_ok sh then
        SOME (make_wrapper arity next sh,            (* replaces original *)
              worker_body loc next sh exp)           (* installed at next *)
      else NONE
End
*)

Definition compile_prog_with_map_def:
  (compile_prog_with_map _ next [] = (next, [])) ∧
  (compile_prog_with_map csh_map next ((loc:num, arity:num, exp)::xs) =
     case split_fun csh_map next loc arity exp of
       NONE =>
         let (n, ys) = compile_prog_with_map csh_map next xs in
           (n, (loc, arity, exp)::ys)
     | SOME (wrapper, worker, new_map) =>
         let (n, ys) = compile_prog_with_map new_map (next + bvl_to_bvi_namespaces) xs in
           (n, (loc, arity, wrapper)::(next, arity, worker)::ys))
End

Definition compile_prog_def:
  compile_prog next xs = compile_prog_with_map LN next xs
End

        
val res = EVAL “compile_prog 1004 [(1000n, 1n, ^test_rec)]”;
(* = (1008,
      [(1000,1,
        If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
          (Let [Call 0 (SOME 300) [Var 0] NONE]
             (Return
                [Var 0; Var 0;
                 Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]]))
          (Let [Call 0 (SOME 300) [Var 0] NONE]
             (LetCall 3 0 1004
                [Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]]
                (Return [Var 0; Var 1; Var 2]))));
       (1004,1,
        LetCall 3 0 1004 [Var 0]
          (Op (BlockOp (Cons 0))
             [Op (BlockOp (Cons 0)) [Var 1; Var 2]; Var 3]))]) *)

              
val res_new = EVAL “compile_prog 2000 [(1000n, 1n, ^test1);(1004, 1n, ^test2)]”;


    
val let1 = “Let [e1;e2;LetCall 2 0 2004 [Var 0] (Op (BlockOp (Cons 0)) [Var 1; Var 2]); e3;e4] e”

val let2 = “Let [e1;e2] (LetCall 2 0 2004 [Var 0] )”




Definition remap_add_def:
  (remap_add _ 0n (shift:num) = [shift]) ∧
  (remap_add [] (SUC n) shift = 0::remap_add [] n shift) ∧
  (remap_add (remap::remapping) (SUC n) shift = remap::remap_add remapping n shift)
End

val test_remap = EVAL “remap_add [] 2 2”
        
(* Let opt *)
Definition lcop_unfold_def:
  (lcop_unfold remapping _ (Var n) = Var (n + SUM (TAKE (n + 1) remapping))) ∧
  (lcop_unfold remapping curr_v (If g e1 e2) =
   If g (lcop_unfold remapping curr_v e1) (lcop_unfold remapping curr_v e2)) ∧
  (lcop_unfold remapping curr_v (Let vs e) = lcop_unfold_lets remapping curr_v vs e []) ∧
  (lcop_unfold remapping curr_v (Op op es) = Op op (MAP (lcop_unfold remapping curr_v) es)) ∧
  (lcop_unfold _ _ e = e) (* TODO *) ∧

  (lcop_unfold_lets remapping curr_v [] e racc = Let (REVERSE racc) (lcop_unfold remapping curr_v e)) ∧
  (lcop_unfold_lets remapping curr_v (x::xs) e racc =
   case x of
     LetCall nret ticks f args body =>
       let new_remap = remap_add remapping curr_v nret;
           body_shift = curr_v + SUM (TAKE (curr_v + 1) remapping)
       in
       Let (REVERSE racc)
           (LetCall nret ticks f (MAP (lcop_unfold remapping curr_v) args)
                    (lcop_unfold_lets new_remap (curr_v + 1) xs e [lcop_unfold [body_shift] nret body]))
       | _ => lcop_unfold_lets remapping (curr_v + 1) xs e ((lcop_unfold remapping curr_v x)::racc))
Termination
  wf_rel_tac ‘measure (λx.
                         case x of
                           INL (_, _, e)         => 2 * exp_size e
                         | INR (_, _, xs, e, _)  => 2 * (list_size exp_size xs + exp_size e) + 1)’
End


val lcop_test1 = EVAL “lcop_unfold [] 0 (Let [Op (IntOp (Const 0)) [];
                                              Op (IntOp (Const 1)) [];
                                              LetCall 2 0 300 [Var 0;Var 1]
                                                      (Op (BlockOp (Cons 0)) [Var 0; Var 1]);
                                             ] (Op (BlockOp (Cons 0)) [Var 2; Var 2]))”


val lcop_test = EVAL “lcop_unfold [] 0 (Let [Op (IntOp (Const 0)) [];
                                             Op (IntOp (Const 1)) [];
                                             LetCall 2 0 300 [Var 0;Var 1]
                                                     (Op (BlockOp (Cons 0)) [Var 0; Var 1]);
                                             Op (IntOp (Const 0)) [];
                                             Op (IntOp (Const 1)) [];
                                             LetCall 2 0 300 [Var 3;Var 4]
                                                     (Op (BlockOp (Cons 0)) [Var 0; Var 1]);
                                            ] (Op (BlockOp (Cons 0)) [Var 2; Var 5]))”

                                              
(* Let [Op (IntOp (Const 0)) []; Op (IntOp (Const 1)) []]
       (LetCall 2 0 300 [Var 0; Var 1]
          (Let
             [Op (BlockOp (Cons 0)) [Var 2; Var 3]; Op (IntOp (Const 0)) [];
              Op (IntOp (Const 1)) []]
             (LetCall 2 0 300 [Var 5; Var 6]
                (Let [Op (BlockOp (Cons 0)) [Var 7; Var 8]]
                   (Op (BlockOp (Cons 0)) [Var 4; Var 9])))))
*)

                     
