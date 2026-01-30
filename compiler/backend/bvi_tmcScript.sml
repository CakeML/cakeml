(*
  Perform tailrec modulo cons optimitaion to make more functions tail-recursive.
*)
Theory bvi_tmc
Ancestors
  bvi backend_common
Libs
  preamble

Definition scan_expr_def:
  (scan_expr ts loc [] = []) ∧
  (scan_expr ts loc (x::y::xs) = []) /\
  (scan_expr ts loc [Var n] = []) ∧
  (scan_expr ts loc [If xi xt xe] = []) ∧
  (scan_expr ts loc [Let xs x] = []) ∧
  (scan_expr ts loc [Raise x] = []) ∧
  (scan_expr ts loc [Tick x] = scan_expr ts loc [x]) ∧
  (scan_expr ts loc [Force _ n] = []) ∧
  (scan_expr ts loc [Call t d xs h] = []) ∧
  (scan_expr ts loc [Op op xs] =
    let opr = from_op op in
    let opt = op_type opr in
      case opr of
        Noop => (* Constants? *) []
      | BlockOp _ cons_args => (* Things we can optimize *)
        []
      | _ => [])
Termination
  cheat
End

(*Definition check_exp_def:
  check_exp loc arity exp =
    if ~has_rec1 loc exp then NONE else
      let context = REPLICATE arity Any in
        dtcase scan_expr context loc [exp] of
          [] => NONE
        | (ts,ty,r,opr)::_ =>
            dtcase opr of
              NONE => NONE
            | SOME op =>
                if ty <> op_type op then NONE else opr
End*)

Definition compile_exp_def:
  compile_exp (loc:num) (next:num) (arity:num) (exp:bvi$exp) =
    (*SOME (exp, exp)
    case check_exp loc arity exp of
      NONE => NONE
    | SOME op =>
      let context = REPLICATE arity Any in
      let (r, opt) = rewrite loc next op arity context exp in
      let aux      = let_wrap arity (id_from_op op) opt in
        SOME (aux, opt)
End

Definition compile_prog_def:
  (compile_prog next [] = (next, [])) ∧
  (compile_prog next ((loc, arity, exp)::xs) =
    case compile_exp loc next arity exp of
    | NONE =>
        let (n, ys) = compile_prog next xs in
          (n, (loc, arity, exp)::ys)
    | SOME (exp_aux, exp_opt) =>
        let (n, ys) = compile_prog (next + bvl_to_bvi_namespaces) xs in
        (n, (loc, arity, exp_aux)::(next, arity + 1, exp_opt)::ys))
End

(* testing *)

val tm = “Let [] (Var 0)”;
val test = EVAL “compile_exp 1 2 3 ^tm”;
val test = EVAL “compile_exp 4 5 6 ^tm”;

val prog = “[(700:num,1:num,^tm)]”
val test2 = EVAL “compile_prog 5 ^prog”;

val head = “Let [] (Op (BlockOp (ElemAt 0)) [Var 0])”;
val head_prog = “[(123:num,1:num,^head)]”;
val head_eval = EVAL “compile_prog 12 ^head_prog”;

(*
val append_exp = “Op (BlockOp (Cons 9)) []”; (* Cons x (append xs ys) (TODO) *)
val append_prog = “[(3:num,2:num,^append_exp)]”;
val append_eval = EVAL “compile_prog 6 ^append_prog”;
*)

val append_exp = “If (Op (BlockOp (TagLenEq 0 0)) [Var 0]) (Var 1) $
                  Let [Op (BlockOp (ElemAt 0)) [Var 0];
                       Op (BlockOp (ElemAt 1)) [Var 0]] $
                  Op (BlockOp (Cons 0)) [Call 0 (SOME 4000) [Var 1] NONE; Var 3]”;
val append_prog = “[(4000:num,2:num,^append_exp)]”;
val append_eval = EVAL “compile_prog 6 ^append_prog”;

(*
(func my_append@465 (b a)
   (let
      (c <- (op (Const 0)))
      (if (op (TagLenEq 0 0) (var a)) (var b)
         (let
            (d <- (op (ElemAt 0) (var a)))
            (let
               (e <- (op (ElemAt 1) (var a)))
           (let
                  (f <- (op (Const 0)))
                  (let
                     (g <- (op (Const 0)))
                     (op (Cons 0) (call my_append@465 (var b) (var e)) (var d)))))))))

*)
    
(*
  Questions:
    1. Let []?
    2. How is pattern matching represented in BVI?
    3. What about: Cons x (Cons x (append xs ys))
    4. Easy way to compile CakeML -> BVI? ./cake --explore
    5. Args to BlockOps Cons(Extend)?
*)
