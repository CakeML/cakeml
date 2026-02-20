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
     * MultipleTC       if multiple recursive tail calls are found.
     * NoTC args        if no recursive tail call is found.
     * TC l tail_call r if a single recursive tail call is found. In this case,
                        ‘l’ are the args left of hole, ‘r’ are the args right of the hole,
                        and the optimised version of ‘tail_call’ will be used to fill the hole. *)
Datatype:
  tc_and_mut_cons = MultipleTC
                  | NoTC (exp list)
                  | TC (exp list) exp (exp list)
End

Definition extract_tail_call_def:
  (extract_tail_call loc [] = NoTC []) ∧
  (extract_tail_call loc ((Call t (SOME loc') args h)::op_args) =
    let call = Call t (SOME loc') args h in
    let rest = extract_tail_call loc op_args in
    if loc=loc' then
      (* found the recursive call *)
      case rest of
      | NoTC r => TC [] call r
      | _ => MultipleTC
    else
      (* found a different call *)
      case rest of
      | TC l rec r => TC (call::l) rec r
      | NoTC r => NoTC (call::r)
      | MultipleTC => MultipleTC) ∧
  (extract_tail_call loc (op_arg::op_args) =
    case extract_tail_call loc op_args of
    | TC l rec r => TC (op_arg::l) rec r
    | NoTC r => NoTC (op_arg::r)
    | MultipleTC => MultipleTC)
End

Definition to_mut_cons_def:
  to_mut_cons loc block_tag op_args =
    case extract_tail_call loc op_args of
    | TC l tail_call r =>
      let hole_idx = LENGTH l in
      let exp_hole = Op (IntOp (Const 0)) [] in
      let mut_cons = Op (MemOp (MutCons block_tag hole_idx)) (l ++ [exp_hole] ++ r) in
        SOME (tail_call, mut_cons)
    | _ => NONE
End

Definition rewrite_aux_BlockOp_Cons_def:
  rewrite_aux_BlockOp_Cons ts loc loc_opt arity block_tag op_args =
    case to_mut_cons loc block_tag op_args of
    | SOME (Call t _ args h, exp_mut_cons) =>
        let var_new_hole_ptr = Var arity in
        let exp_tail_call    = Call t (SOME loc_opt) (var_new_hole_ptr :: args) h in
        let exp_finalise     = Op (MemOp FinaliseCons) [var_new_hole_ptr] in
        SOME $ Let [exp_mut_cons; exp_tail_call] exp_finalise
    | _ => NONE
End

Definition rewrite_aux_def:
  (rewrite_aux ts loc loc_opt arity (Var n) = NONE) ∧
  (rewrite_aux ts loc loc_opt arity (If xi xt xe) =
    let opt_t = rewrite_aux ts loc loc_opt arity xt in
    let opt_e = rewrite_aux ts loc loc_opt arity xe in
    case (opt_t, opt_e) of
    | (NONE, NONE) => NONE
    | (SOME yt, NONE) => SOME $ If xi yt xe
    | (NONE, SOME ye) => SOME $ If xi xt ye
    | (SOME yt, SOME ye) => SOME $ If xi yt ye) ∧
  (rewrite_aux ts loc loc_opt arity (Let xs x) =
    case rewrite_aux ts loc loc_opt (arity + LENGTH xs) x of
    | NONE => NONE
    | SOME y => SOME $ Let xs y) ∧
  (rewrite_aux ts loc loc_opt arity (Raise x) = NONE) ∧
  (rewrite_aux ts loc loc_opt arity (Tick x) = OPTION_MAP Tick $ rewrite_aux ts loc loc_opt arity x) ∧
  (rewrite_aux ts loc loc_opt arity (Force _ n) = NONE) ∧
  (rewrite_aux ts loc loc_opt arity (Call t d args h) = NONE) ∧
  (rewrite_aux ts loc loc_opt arity (Op op op_args) =
    case op of
    | BlockOp (Cons block_tag) => rewrite_aux_BlockOp_Cons ts loc loc_opt arity block_tag op_args
    | _ => NONE) ∧
  (rewrite_aux ts loc loc_opt arity _ = NONE)
End

(* Assumes that the function can and should be optimised - has been checked by rewrite_aux_def. *)
Definition rewrite_opt_BlockOp_Cons_def:
  rewrite_opt_BlockOp_Cons ts loc loc_opt arity block_tag op_args =
    case to_mut_cons loc block_tag op_args of
    | SOME (Call t _ args h, exp_mut_cons) =>
        let arg_old_hole_ptr = Var arity in
        let var_new_hole_ptr = Var (arity + 1) in
        let exp_update_hole  = Op (MemOp UpdateCons) [arg_old_hole_ptr; var_new_hole_ptr] in
        let exp_tail_call    = Call t (SOME loc_opt) (var_new_hole_ptr :: args) h in
          Let [exp_mut_cons; exp_update_hole] $ exp_tail_call
    | _ => Op (BlockOp (Cons block_tag)) op_args
End

(* Assumes that the function can and should be optimised - has been checked by rewrite_aux_def. *)
Definition rewrite_opt_def:
  (rewrite_opt ts loc loc_opt arity (If xi xt xe) =
    let yt = rewrite_opt ts loc loc_opt arity xt in
    let ye = rewrite_opt ts loc loc_opt arity xe in
    If xi yt ye) ∧
  (rewrite_opt ts loc loc_opt arity (Let xs x) = Let xs $ rewrite_opt ts loc loc_opt (arity + LENGTH xs) x) ∧
  (rewrite_opt ts loc loc_opt arity (Raise x) = Raise x) ∧
  (rewrite_opt ts loc loc_opt arity (Op op op_args) =
    case op of
    | BlockOp (Cons block_tag) => rewrite_opt_BlockOp_Cons ts loc loc_opt arity block_tag op_args
    | _ =>
      let arg_old_hole_ptr = Var arity in
      Op (MemOp UpdateCons) [arg_old_hole_ptr; (Op op op_args)]) ∧
  (rewrite_opt ts loc loc_opt arity expr =
    let arg_old_hole_ptr = Var arity in
    Op (MemOp UpdateCons) [arg_old_hole_ptr; expr])
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
        (n, (loc, arity, exp_aux)::(next, arity + 2, exp_opt)::ys))
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

val append_exp = “If (Op (BlockOp (TagLenEq 0 0)) [Var 0]) (Var 1) $
                  Let [Op (BlockOp (ElemAt 0)) [Var 0];
                       Op (BlockOp (ElemAt 1)) [Var 0]] $
                  Op (BlockOp (Cons 0)) [Call 0 (SOME 4000) [Var 1; Var 3] NONE; Var 2]”;
val append_prog = “[(4000:num,2:num,^append_exp)]”;
val append_eval = EVAL “compile_prog 6 ^append_prog”;

(* Expected (at least I think):
   (9,
      [(4000,2,
        If (Op (BlockOp (TagLenEq 0 0)) [Var 0]) (Var 1)
          (Let [mk_elem_at (Var 0) 0; mk_elem_at (Var 0) 1]
             (Let
                [Op (MemOp (MutCons 0 0)) [Op (IntOp (Const 0)) []; Var 2];
                 Call 0 (SOME 6) [Var 4; Var 1; Var 3] NONE]
                (Op (MemOp FinaliseCons) [Var 4]))));
       (6,4,
        If (Op (BlockOp (TagLenEq 0 0)) [Var 0])
          (Op (MemOp UpdateCons) [Var 2; Var 1])
          (Let [mk_elem_at (Var 0) 0; mk_elem_at (Var 0) 1]
             (Let
                [Op (MemOp (MutCons 0 0)) [Op (IntOp (Const 0)) []; Var 2];
                 Op (MemOp UpdateCons) [Var 4; Var 5]]
                (Call 0 (SOME 6) [Var 5; Var 1; Var 3] NONE))))])
 *)

(* [1] :: [x] :: my_bar xs *)
val tail_cons1 = “extract_tail_call (4000:num) [Op (BlockOp (Cons 0))
                                                 [Call 0 (SOME 4000) [Var 3] NONE;
                                                  Op (BlockOp (Cons 0)) [Op (BlockOp (Cons 0)) []; Var 2]];
                                              Op (BlockOp (Build [Int 1; Con 0 []; Con 0 [0; 1]])) []]”;
val tail_cons_eval1 = EVAL tail_cons1;

