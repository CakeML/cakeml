(*
  Perform tailrec modulo cons optimisation to make more functions tail-recursive.
*)
Theory bvi_tmc
Ancestors
  bvi backend_common
Libs
  preamble

(* Primes Block args to be used as HoleBlock args.
   Extracts the recursive tail call from the list of args, and returns the args to the left and to the right of the tail call.
   Returns:
     * NONE                       if multiple recursive tail calls are found.
     * SOME (NONE, args)          if no recursive tail call is found
     * SOME (SOME l tail_call, r) if a single recursive tail call is found. In this case,
                                  ‘l’ are the args left of hole, ‘r’ are the args right of the hole,
                                  and the optimised version of ‘tail_call’ will be used to fill the hole. *)
Definition extract_tail_call_def:
  (extract_tail_call loc [] = SOME (NONE, [])) ∧
  (extract_tail_call loc ((Call t (SOME loc') args h)::op_args) =
    let call = Call t (SOME loc') args h in
    let rest = extract_tail_call loc op_args in
    if loc=loc' then
      (* found the recursive call *)
      case rest of
      | SOME (NONE, r) => SOME (SOME ([], call), r)
      | _ => NONE
    else
      (* found a different call *)
      case rest of
      | SOME (SOME (l, rec), r) => SOME (SOME (call::l, rec), r)
      | SOME (NONE, r) => SOME (NONE, call::r)
      | NONE => NONE) ∧
  (extract_tail_call loc (op_arg::op_args) =
    case extract_tail_call loc op_args of
    | SOME (SOME (l, rec), r) => SOME (SOME (op_arg::l, rec), r)
    | SOME (NONE, r) => SOME (NONE, op_arg::r)
    | NONE => NONE)
End

Definition rewrite_aux_def:
  (rewrite_aux ts loc loc_opt arity (Var n) = NONE) ∧
  (rewrite_aux ts loc loc_opt arity (If xi xt xe) =
    let opt_t = rewrite_aux ts loc loc_opt arity xt in
    let opt_e = rewrite_aux ts loc loc_opt arity xe in
    case (opt_t, opt_e) of
    | (NONE, NONE) => SOME $ If xi xt xe
    | (SOME yt, NONE) => SOME $ If xi yt xe
    | (NONE, SOME ye) => SOME $ If xi xt ye
    | (SOME yt, SOME ye) => SOME $ If xi yt ye) ∧
  (rewrite_aux ts loc loc_opt arity (Let xs x) =
    case rewrite_aux ts loc loc_opt arity x of
    | NONE => NONE
    | SOME y => SOME $ Let xs y) ∧
  (rewrite_aux ts loc loc_opt arity (Raise x) = NONE) ∧
  (rewrite_aux ts loc loc_opt arity (Tick x) = rewrite_aux ts loc loc_opt arity x) ∧ (* TODO: wrap in Tick *)
  (rewrite_aux ts loc loc_opt arity (Force _ n) = NONE) ∧
  (rewrite_aux ts loc loc_opt arity (Call t d args h) = NONE) ∧
  (rewrite_aux ts loc loc_opt arity (Op (BlockOp (Cons block_tag)) op_args) = (* TODO: tail call might not be first *)
    case extract_tail_call loc op_args of
    | SOME (SOME (l, Call t _ args h), r) =>
        let alloc_var = Var arity in
        let alloc_exp  = Var 0 in (*alloc(x, HOLE);*) (* hole needs to be constructed using l and r *)
        let tail_exp  = Call t (SOME loc_opt) args h in (*; append’ (p + 1) xs ys*) (* TODO: append HOLE pointer to args *)
        SOME $ Let [alloc_exp; tail_exp] (* finalize (... *) alloc_var
    | _ => NONE) ∧
  (rewrite_aux ts loc loc_opt arity _ = NONE)
Termination
  cheat
End

(* Assumes that the function can and should be optimised - has been checked by rewrite_aux_def. Also assumes De Bruijn indices have been shifted. *)
Definition rewrite_opt_def:
  (rewrite_opt ts loc loc_opt arity (If xi xt xe) =
    let yt = rewrite_opt ts loc loc_opt arity xt in
    let ye = rewrite_opt ts loc loc_opt arity xe in
    If xi yt ye) ∧
  (rewrite_opt ts loc loc_opt arity (Let xs x) = Let xs $ rewrite_opt ts loc loc_opt arity x) ∧
  (rewrite_opt ts loc loc_opt arity (Raise x) = Raise x) ∧
  (rewrite_opt ts loc loc_opt arity (Op (BlockOp (Cons block_tag)) op_args) =
    case extract_tail_call loc op_args of
    | SOME (SOME (l, Call t _ args h), r) =>
        let alloc_var = Var arity in
        let alloc_exp  = Var 0 in (*alloc(x, HOLE);*) (* hole needs to be constructed using l and r *)
        let assign_exp = alloc_var in (* heap[k] = p *) (* assign(Var 0, alloc_var) *)
        bvi$Let [alloc_exp; assign_exp] $ Call t (SOME loc_opt) args h (* TODO: append HOLE pointer to args *)
    | _ => Op (BlockOp (Cons block_tag)) op_args) ∧
  (rewrite_opt ts loc loc_opt arity expr = (* TODO: Fill hole *) expr)
Termination
  cheat
End

Definition compile_exp_def:
  compile_exp (loc:num) (next:num) (arity:num) (exp:bvi$exp) =
    case rewrite_aux 0 (* TODO *) loc next arity exp of
    | NONE => NONE
    | SOME exp_aux =>
      let exp_opt = rewrite_opt 0 (* TODO *) loc next arity exp in
      SOME (exp_aux, exp_opt)
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
