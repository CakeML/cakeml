(*
  Perform tailrec modulo cons optimitaion to make more functions tail-recursive.
*)
Theory bvi_tmc
Ancestors
  bvi backend_common
Libs
  preamble

Definition optimize_expr_def:
  (optimize_expr ts loc loc_helper (Var n) = NONE) ∧
  (optimize_expr ts loc loc_helper (If xi xt xe) =
    let yt = case optimize_expr ts loc loc_helper xt of
      NONE => xt
    | SOME yt => yt in                
    let ye = case optimize_expr ts loc loc_helper xe of
      NONE => xe
    | SOME ye => ye in
    SOME $ If xi yt ye) ∧ (* TODO: if both are none this should be NONE *)
  (optimize_expr ts loc loc_helper (Let xs x) =
    case optimize_expr ts loc loc_helper x of
      NONE => NONE
    | SOME y => SOME $ Let xs y) ∧
  (optimize_expr ts loc loc_helper (Raise x) = NONE) ∧
  (optimize_expr ts loc loc_helper (Tick x) = optimize_expr ts loc loc_helper x) ∧
  (optimize_expr ts loc loc_helper (Force _ n) = NONE) ∧
  (optimize_expr ts loc loc_helper (Call t d args h) = NONE) ∧
  (optimize_expr ts loc loc_helper (Op (BlockOp (Cons block_tag)) (Call t (SOME loc_rec) args h::op_args)) = (* TODO: tail call might not be first *)
   if loc_rec=loc then NONE else (* TODO: figure out ~ *)
     let alloc     = op_args in (*alloc(x, HOLE);*) (* TODO: properly filter out tail call from op_args *)
     let tail_call = Call t (SOME loc_helper) args h in (*; append’ (p + 1) xs ys*) (* TODO: append HOLE pointer to args *)
     SOME $ Let (op_args ++ [tail_call]) $ (* finalize (... *) Var 1) ∧
  (optimize_expr ts loc loc_helper _ = NONE)
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
    SOME (exp, exp, exp)
    (*case check_exp loc arity exp of
      NONE => NONE
    | SOME op =>
      let context = REPLICATE arity Any in
      let (r, opt) = rewrite loc next op arity context exp in
      let aux      = let_wrap arity (id_from_op op) opt in
        SOME (aux, opt)*)
End

Definition compile_prog_def:
  (compile_prog next [] = (next, [])) ∧
  (compile_prog next ((loc, arity, exp)::xs) =
    case compile_exp loc next arity exp of
    | NONE =>
        let (n, ys) = compile_prog next xs in
          (n, (loc, arity, exp)::ys)
    | SOME (exp_unopt, exp_opt, exp_helper) =>
        let loc_opt      = next in
        let loc_helper   = loc_opt + bvl_to_bvi_namespaces in
        let next'        = loc_helper + bvl_to_bvi_namespaces in
        let (next'', ys) = compile_prog next' xs in
        (next'', (loc, arity, exp_unopt)::(loc_opt, arity, exp_opt)::(loc_helper, arity + 1, exp_helper)::ys))
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
