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

Definition shape_of_def:
  (shape_of fname env (Var n) = Leaf) /\
  (shape_of fname env (If g e1 e2) =
     cpr_merge (shape_of fname env e1) (shape_of fname env e2)) /\
  (shape_of fname env (Let xs b) =
     shape_of fname (shape_list fname env xs ++ env) b) /\
  (shape_of fname env (Raise e) = Flexible) /\
  (shape_of fname env (Tick e) = shape_of fname env e) /\
  (shape_of fname env (Call ts dest args hdl) =
   case dest of
     SOME dname => if fname = dname then Flexible else Leaf
   | _ => Leaf) /\
  (shape_of fname env (Force loc v) = Leaf) /\
  (shape_of fname env (Op op xs) =
     (case op of
        BlockOp (Cons tag) =>
          ConsShape tag (shape_list fname env xs)
      | _ => Leaf)) /\
  (shape_of fname env (LetCall ret ticks dest args b) =
     shape_of fname (REPLICATE ret Leaf ++ env) b) /\
  (shape_of fname env (Return xs) = Leaf) /\

  (shape_list fname env [] = []) /\
  (shape_list fname env (x::xs) = shape_of fname env x :: shape_list fname env xs)
End

Definition return_shape_def:
  return_shape fname (arity:num) body =
    shape_of fname (REPLICATE arity Leaf) body
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
  (worker_body fname next sh (If g e1 e2) =
     If g (worker_body fname next sh e1) (worker_body fname next sh e2)) ∧
  (worker_body fname next sh (Let xs b) = Let xs (worker_body fname next sh b)) ∧
  (worker_body fname next sh (Tick e) = Tick (worker_body fname next sh e)) ∧
  (worker_body fname next sh (Raise e) = Raise e) ∧
  (worker_body fname next sh (LetCall ret ticks dest args b) =
     LetCall ret ticks dest args (worker_body fname next sh b)) ∧
  (worker_body fname next sh (Return xs) = Return xs) ∧
  (worker_body fname next sh (Call ts dest args hdl) =
   case dest of
     SOME dname => if fname = dname then TailCall (shape_width sh) 0 next args else Call ts dest args hdl
   | _ => Call ts dest args hdl) ∧
  (worker_body fname next sh e = Return (flatten_exp sh e))
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
  split_fun next (loc, arity, body) =
    let sh = return_shape loc arity body in
      if split_ok sh then
        SOME ((arity, worker_body loc next sh body),          (* the worker  *)
              (arity, make_wrapper arity next sh))            (* the wrapper *)
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

val test_wrapper = “LetCall 3 0 next [Var 0]
                   (Op (BlockOp (Cons 0))
                       [Op (BlockOp (Cons 0)) [Var 1; Var 2]; Var 3])”

val test_return_shape = EVAL “return_shape 1000 1 ^test”

val worker_eval  = EVAL “worker_body 1000 1100 (return_shape 1000 1 ^test1) ^test1”;
(* = ^test_worker *)

val wrapper_eval = EVAL “make_wrapper 1 next (return_shape 1000 1 ^test1)”;
(* = ^test_wrapper *)

(* rec *)

val test_rec = “If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
        (Let [Call 0 (SOME 300) [Var 0] NONE]
             (Op (BlockOp (Cons 0))
                 [Op (BlockOp (Cons 0)) [Var 0; Var 0];
                  Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]]))
        (Let [Call 0 (SOME 300) [Var 0] NONE]
             (Call 0 (SOME 1000) [Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]] NONE))”


val test_return_shape_rec = EVAL “return_shape 1000 1 ^test_rec”

val worker_eval_rec = EVAL “worker_body 1000 1100 (return_shape 1000 1 ^test_rec) ^test_rec”;

val wrapper_eval_rec = EVAL “make_wrapper 1 1100 (return_shape 1000 1 ^test_rec)”;



   

Definition compile_exp_def:
  compile_exp loc next arity exp =
    let sh = return_shape loc arity exp in
      if split_ok sh then
        SOME (make_wrapper arity next sh,            (* replaces original *)
              worker_body loc next sh exp)           (* installed at next *)
      else NONE
End


Definition compile_prog_def:
  (compile_prog next [] = (next, [])) ∧
  (compile_prog next ((loc:num, arity:num, exp)::xs) =
     case compile_exp loc next arity exp of
       NONE =>
         let (n, ys) = compile_prog next xs in
           (n, (loc, arity, exp)::ys)
     | SOME (wrapper, worker) =>
         let (n, ys) = compile_prog (next + bvl_to_bvi_namespaces) xs in
           (n, (loc, arity, wrapper)::(next, arity, worker)::ys))
End

        
val res = EVAL “compile_prog 1004 [(1000n, 1n, ^test_rec)]”;
(* = (1104,
     [(200, 1, LetCall 3 0 1000 [Var 0]
                 (Op (BlockOp (Cons 0))
                    [Op (BlockOp (Cons 0)) [Var 1; Var 2]; Var 3]));
      (1000, 1, ^test_worker)]) *)

