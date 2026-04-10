(*
  Perform tailrec modulo cons optimisation to make more functions tail-recursive.
*)
Theory bvi_tmc
Ancestors
  bvi backend_common
Libs
  preamble

(* TODO: Read only MemOps *)
Definition effectful_op_def:
  (effectful_op (Label _) = F) ∧
  (effectful_op (FFI _) = T) ∧
  (effectful_op (IntOp _) = F) ∧
  (effectful_op (WordOp _) = F) ∧
  (effectful_op (BlockOp _) = F) ∧
  (effectful_op (GlobOp _) = T) ∧
  (effectful_op (MemOp _) = T) ∧
  (effectful_op Install = T) ∧
  (effectful_op (ThunkOp _) = T)
End

Definition effectful_exps_def:
  (effectful_exps [] = F) ∧
  (effectful_exps [Var _] = F) ∧
  (effectful_exps [If e1 e2 e3] = (effectful_exps [e1] ∨ effectful_exps [e2] ∨ effectful_exps [e3])) ∧
  (effectful_exps [Let es e] = effectful_exps (e::es)) ∧
  (effectful_exps [Raise _] = T) ∧
  (effectful_exps [Tick e] = effectful_exps [e]) ∧ (* TODO *)
  (effectful_exps [Call _ _ _ _] = T) ∧
  (effectful_exps [Force _ _] = T) ∧
  (effectful_exps [Op op args] = (effectful_op op ∨ effectful_exps args)) ∧
  (effectful_exps (h::t) = (effectful_exps [h] ∨ effectful_exps t))
End

Definition effectful_exp_def:
  (effectful_exp e = effectful_exps [e])
End

Datatype:
  tcall = TCall num (exp list) (exp option) (* loc is not needed here, as it is known in function body *)
End

Datatype:
  hole_block = HoleBlock num (exp list) (hole_block option) (exp list)
End

Definition push_left_def:
  push_left (HoleBlock t l h r) e = HoleBlock t (e::l) h r
End

Definition to_mut_cons_def:
  to_mut_cons (HoleBlock t l h r) =
    let hole = case h of
      | SOME h' => to_mut_cons h'
      | NONE => Op (IntOp (Const 0)) [] in
    let i = LENGTH l in
    Op (MemOp (MutCons t i)) (l ++ [hole] ++ r)
End

Datatype:
  tc_and_hb = Invalid             (* Duplicate recursive tail calls. TODO: we can handle this - lift all but last into ‘Let’s.
                                     OR effectful expressions after the tail call. *)
            | NoTC                (* No recursive tail call. *)
            | TC tcall hole_block (* One recursive tail call.
                                     tcall fills the final ‘NONE’ hole nested in hole_block.
                                   *)
End

Definition dest_Cons_def:
  dest_Cons (BlockOp (Cons block_tag)) = SOME block_tag ∧
  dest_Cons _ = NONE
End

(* ‘cons_to_tc_and_mut_cons loc tag op_args’ finds a unique recursive call of index ‘loc’ nested within the args of a ‘BlockOp’ ‘Cons’
    block of the form ‘Op (BlockOp (Cons tag)) op_args’. If such a call is found, then the block is converted to a (possibily nested)
    ‘MemOp’ ‘MutCons’ hole block, where the hole is to be filled by the result of the recursive call.
    Returns:
      ‘DupTC’            if multiple matching recursive calls were found.
      ‘NoTC’             if no matching recursive call was found.
      ‘TC call mut_cons’ if ‘call’ is the only matching call and ‘mut_cons’ has a single hole to be filled by ‘call’. *)
Definition cons_to_tc_and_hb_def:
  (cons_to_tc_and_hb loc tag [] = NoTC) ∧
  (cons_to_tc_and_hb loc tag ((Op op op_args')::op_args) =
   case dest_Cons op of
   | SOME tag' =>
       (case (cons_to_tc_and_hb loc tag' op_args', cons_to_tc_and_hb loc tag op_args) of
        | (Invalid, _) => Invalid
        | (_, Invalid) => Invalid
        | (TC _ _, TC _ _) => Invalid
        | (NoTC, NoTC) => NoTC
        | (TC call' hb', NoTC) =>
            (let hb = HoleBlock tag [] (SOME hb') op_args in
               TC call' hb)
        | (NoTC, TC call hb) =>
            let cons = Op (BlockOp (Cons tag')) op_args' in
              if effectful_exp cons then Invalid else
                let hb'  = push_left hb cons in
                  TC call hb')
   | NONE =>
       (* TODO: helper *)
       case cons_to_tc_and_hb loc tag op_args of
       | Invalid => Invalid
       | NoTC => NoTC
       | TC call hb =>
           let op_arg = Op op op_args' in
           if effectful_exp op_arg then Invalid else
             let hb' = push_left hb op_arg in
               TC call hb') ∧
  (cons_to_tc_and_hb loc tag (Call t' (SOME loc') args' h'::op_args) =
    if loc=loc' then
      (* found the recursive call *)
      case cons_to_tc_and_hb loc tag op_args of
      | Invalid => Invalid
      | TC _ _ => Invalid
      | NoTC =>
         let call = TCall t' args' h' in
         let hb   = HoleBlock tag [] NONE op_args in
           TC call hb
    else
      (* found a different call *)
      case cons_to_tc_and_hb loc tag op_args of
      | Invalid => Invalid
      | NoTC => NoTC
      | TC call hb => Invalid (* Call is effectful *)) ∧
  (cons_to_tc_and_hb loc tag (op_arg::op_args) =
   (* TODO: helper *)
    case cons_to_tc_and_hb loc tag op_args of
    | Invalid => Invalid
    | NoTC => NoTC
    | TC call hb =>
       if effectful_exp op_arg then Invalid else
         let hb' = push_left hb op_arg in
           TC call hb')
End



Definition rewrite_aux_BlockOp_Cons_def:
  rewrite_aux_BlockOp_Cons loc loc_opt i_hole_ptr block_tag op_args =
    case cons_to_tc_and_hb loc block_tag op_args of
    | TC (TCall t args h) (HoleBlock tag l hole r) =>
        let hb            = HoleBlock tag l hole r in
        let i             = & LENGTH l in
        let var_hole_ptr  = Var i_hole_ptr in
        let exp_hole_idx  = Op (IntOp (Const i)) [] in
        let exp_mut_cons  = to_mut_cons hb in
        let exp_tail_call = Call t (SOME loc_opt) (exp_hole_idx :: var_hole_ptr :: args) h in
        let exp_finalise  = Op (MemOp FinaliseCons) [var_hole_ptr] in
        SOME $ Let [exp_mut_cons; exp_tail_call] exp_finalise
    | _ => NONE
End

Definition rewrite_aux_def:
  (rewrite_aux loc loc_opt i_hole_ptr (Var n) = NONE) ∧
  (rewrite_aux loc loc_opt i_hole_ptr (If xi xt xe) =
    let opt_t = rewrite_aux loc loc_opt i_hole_ptr xt in
    let opt_e = rewrite_aux loc loc_opt i_hole_ptr xe in
    case (opt_t, opt_e) of
    | (NONE, NONE) => NONE
    | (SOME yt, NONE) => SOME $ If xi yt xe
    | (NONE, SOME ye) => SOME $ If xi xt ye
    | (SOME yt, SOME ye) => SOME $ If xi yt ye) ∧
  (rewrite_aux loc loc_opt i_hole_ptr (Let xs x) =
    case rewrite_aux loc loc_opt (i_hole_ptr + LENGTH xs) x of
    | NONE => NONE
    | SOME y => SOME $ Let xs y) ∧
  (rewrite_aux loc loc_opt i_hole_ptr (Raise x) = NONE) ∧
  (rewrite_aux loc loc_opt i_hole_ptr (Tick x) = OPTION_MAP Tick $ rewrite_aux loc loc_opt i_hole_ptr x) ∧
  (rewrite_aux loc loc_opt i_hole_ptr (Force _ n) = NONE) ∧
  (rewrite_aux loc loc_opt i_hole_ptr (Call t d args h) = NONE) ∧
  (rewrite_aux loc loc_opt i_hole_ptr (Op op op_args) =
    case dest_Cons op of
    | SOME block_tag => rewrite_aux_BlockOp_Cons loc loc_opt i_hole_ptr block_tag op_args
    | NONE => NONE) ∧
  (rewrite_aux loc loc_opt i_hole_ptr _ = NONE)
End

(* Assumes that the function can and should be optimised - has been checked by rewrite_aux_def. *)
Definition rewrite_opt_BlockOp_Cons_def:
  rewrite_opt_BlockOp_Cons loc loc_opt i_old_hole_ptr i_old_hole_idx i_new_hole_ptr block_tag op_args =
    case cons_to_tc_and_hb loc block_tag op_args of
    | TC (TCall t args h) (HoleBlock tag l hole r) =>
        let hb               = HoleBlock tag l hole r in
        let i                = & LENGTH l in
        let arg_old_hole_ptr = Var i_old_hole_ptr in
        let arg_old_hole_idx = Var i_old_hole_idx in
        let var_new_hole_ptr = Var i_new_hole_ptr in
        let exp_new_hole_idx = Op (IntOp (Const i)) [] in
        let exp_mut_cons     = to_mut_cons hb in
        let exp_update_hole  = Op (MemOp UpdateCons) [var_new_hole_ptr; arg_old_hole_idx; arg_old_hole_ptr] in
        let exp_tail_call    = Call t (SOME loc_opt) (exp_new_hole_idx :: var_new_hole_ptr :: args) h in
          Let [exp_mut_cons; exp_update_hole] $ exp_tail_call
    | _ => Op (BlockOp (Cons block_tag)) op_args
End

(* Assumes that the function can and should be optimised - has been checked by rewrite_aux_def. *)
Definition rewrite_opt_def:
  (rewrite_opt loc loc_opt i_old_hole_ptr i_old_hole_idx i_new_hole_ptr (If xi xt xe) =
    let yt = rewrite_opt loc loc_opt i_old_hole_ptr i_old_hole_idx i_new_hole_ptr xt in
    let ye = rewrite_opt loc loc_opt i_old_hole_ptr i_old_hole_idx i_new_hole_ptr xe in
    If xi yt ye) ∧
  (rewrite_opt loc loc_opt i_old_hole_ptr i_old_hole_idx i_new_hole_ptr (Let xs x) =
    let offset = LENGTH xs in
      Let xs $ rewrite_opt loc loc_opt (i_old_hole_ptr + offset) (i_old_hole_idx + offset) (i_new_hole_ptr + offset) x) ∧
  (rewrite_opt loc loc_opt i_old_hole_ptr i_old_hole_idx i_new_hole_ptr (Raise x) = Raise x) ∧
  (rewrite_opt loc loc_opt i_old_hole_ptr i_old_hole_idx i_new_hole_ptr (Op op op_args) =
    case dest_Cons op of
    | SOME block_tag => rewrite_opt_BlockOp_Cons loc loc_opt i_old_hole_ptr i_old_hole_idx i_new_hole_ptr block_tag op_args
    | NONE =>
      let arg_hole_ptr = Var i_old_hole_ptr in
      let arg_hole_idx = Var i_old_hole_idx in
      let exp_hole_val = Op op op_args in
        Op (MemOp UpdateCons) [exp_hole_val; arg_hole_idx; arg_hole_ptr]) ∧
  (rewrite_opt loc loc_opt i_old_hole_ptr i_old_hole_idx i_new_hole_ptr (Tick x) =
    Tick $ rewrite_opt loc loc_opt i_old_hole_ptr i_old_hole_idx i_new_hole_ptr x) ∧
  (rewrite_opt loc loc_opt i_old_hole_ptr i_old_hole_idx i_new_hole_ptr expr =
    let arg_hole_ptr = Var i_old_hole_ptr in
    let arg_hole_idx = Var i_old_hole_idx in
      Op (MemOp UpdateCons) [expr; arg_hole_idx; arg_hole_ptr])
End

Definition compile_exp_def:
  compile_exp (loc:num) (next:num) (arity:num) (exp:bvi$exp) =
    case rewrite_aux loc next arity exp of
    | NONE => NONE
    | SOME exp_aux =>
      let exp_opt = rewrite_opt loc next arity (arity + 1) (arity + 2) exp in
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

(* --- Test rewriting --- *)

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
val append_expected = “(9:num,
      [(4000:num,2:num,
        If (Op (BlockOp (TagLenEq 0 0)) [Var 0]) (Var 1)
          (Let [mk_elem_at (Var 0) 0; mk_elem_at (Var 0) 1]
             (Let
                [Op (MemOp (MutCons 0 0)) [Op (IntOp (Const 0)) []; Var 2];
                 Call 0 (SOME 6) [Op (IntOp (Const 0)) []; Var 4; Var 1; Var 3] NONE]
                (Op (MemOp FinaliseCons) [Var 4]))));
       (6,4,
        If (Op (BlockOp (TagLenEq 0 0)) [Var 0])
          (Op (MemOp UpdateCons) [Var 1; Var 3; Var 2])
          (Let [mk_elem_at (Var 0) 0; mk_elem_at (Var 0) 1]
             (Let
                [Op (MemOp (MutCons 0 0)) [Op (IntOp (Const 0)) []; Var 2];
                 Op (MemOp UpdateCons) [Var 6; Var 5; Var 4]]
                (Call 0 (SOME 6) [Op (IntOp (Const 0)) []; Var 6; Var 1; Var 3] NONE))))])”;

Theorem append_check:
  compile_prog 6 ^append_prog = ^append_expected
Proof
  EVAL_TAC
QED

(*
let
      (c <- (op (Const 0)))
      (if (op (TagLenEq 0 0) (var b)) (op (Cons 0))
         (let
            (d <- (op (ElemAt 0) (var b)))
            (let
               (e <- (op (ElemAt 1) (var b)))
               (let
                  (f <- (op (Const 0)))
                  (let
                     (g <- (op (Const 0)))
                     (op (Cons 0)
                        (call my_map@471 (var e) (var a))
                        (let
                           (i <- (op (Const 0)))
                           (h <- (op (Const 0)))
                           (if
                              (op (EqualConst (Int 0)) (op (ElemAt 1) (var a)))
                              (call none (var d) (var a) (op (ElemAt 0) (var a)))
                              (call bvl_stub@69 (var d) (var a))))))))))
 *)
val map_exp = “Let [Op (IntOp (Const 0)) []] $
               If (Op (BlockOp (TagLenEq 0 0)) [Var 1]) (Op (BlockOp (Cons 0)) []) $
               Let [Op (BlockOp (ElemAt 0)) [Var 1]] $
               Let [Op (BlockOp (ElemAt 1)) [Var 1]] $
               Let [Op (IntOp (Const 0)) []] $
               Let [Op (IntOp (Const 0)) []] $
               Op (BlockOp (Cons 0))
               [ Call 0 (SOME 4000) [Var 4; Var 0] NONE;
                 Let [Op (IntOp (Const 0)) []; Op (IntOp (Const 0)) []] $
                     If (Op (BlockOp (EqualConst (Int 0))) [Op (BlockOp (ElemAt 1)) [Var 0]])
                     (Call 0 (SOME 1234) [Var 3; Var 0; Op (BlockOp (ElemAt 0)) [Var 0]] NONE)
                     (Call 0 (SOME 5432) [Var 3; Var 0] NONE)
                ]”;
val map_prog = “[(4000:num,2:num,^map_exp)]”;
val map_expected = “(9:num,
      [(4000:num,2:num,
        Let [Op (IntOp (Const 0)) []]
          (If (Op (BlockOp (TagLenEq 0 0)) [Var 1]) mk_unit
             (Let [mk_elem_at (Var 1) 0]
                (Let [mk_elem_at (Var 1) 1]
                   (Let [Op (IntOp (Const 0)) []]
                      (Let [Op (IntOp (Const 0)) []]
                         (Let
                            [Op (MemOp (MutCons 0 0))
                               [Op (IntOp (Const 0)) [];
                                Let
                                  [Op (IntOp (Const 0)) [];
                                   Op (IntOp (Const 0)) []]
                                  (If
                                     (Op (BlockOp (EqualConst (Int 0)))
                                        [mk_elem_at (Var 0) 1])
                                     (Call 0 (SOME 1234)
                                        [Var 3; Var 0; mk_elem_at (Var 0) 0]
                                        NONE)
                                     (Call 0 (SOME 5432) [Var 3; Var 0] NONE))];
                             Call 0 (SOME 6) [Op (IntOp (Const 0)) []; Var 7; Var 4; Var 0] NONE]
                            (Op (MemOp FinaliseCons) [Var 7]))))))));
       (6,4,
        Let [Op (IntOp (Const 0)) []]
          (If (Op (BlockOp (TagLenEq 0 0)) [Var 1]) mk_unit
             (Let [mk_elem_at (Var 1) 0]
                (Let [mk_elem_at (Var 1) 1]
                   (Let [Op (IntOp (Const 0)) []]
                      (Let [Op (IntOp (Const 0)) []]
                         (Let
                            [Op (MemOp (MutCons 0 0))
                               [Op (IntOp (Const 0)) [];
                                Let
                                  [Op (IntOp (Const 0)) [];
                                   Op (IntOp (Const 0)) []]
                                  (If
                                     (Op (BlockOp (EqualConst (Int 0)))
                                        [mk_elem_at (Var 0) 1])
                                     (Call 0 (SOME 1234)
                                        [Var 3; Var 0; mk_elem_at (Var 0) 0]
                                        NONE)
                                     (Call 0 (SOME 5432) [Var 3; Var 0] NONE))];
                             Op (MemOp UpdateCons) [Var 9; Var 8; Var 7]]
                            (Call 0 (SOME 6) [Op (IntOp (Const 0)) []; Var 9; Var 4; Var 0] NONE))))))))])”;

Theorem map_check:
  compile_prog 6 ^map_prog = ^map_expected
Proof
  EVAL_TAC
QED

(* [1] :: [x] :: my_bar xs *)
val tc_hb1 = “cons_to_tc_and_hb (4000:num) 12 [Op (BlockOp (Cons 0))
                                                  [Call 0 (SOME 4000) [Var 3] NONE;
                                                   Op (BlockOp (Cons 0)) [Op (BlockOp (Cons 0)) []; Var 2]];
                                               Op (BlockOp (Build [Int 1; Con 0 []; Con 0 [0; 1]])) []]”;
val tc_hb1_expected = “TC (TCall 0 [Var 3] NONE)
                       (HoleBlock 12
                                  []
                                  (SOME (HoleBlock 0
                                                   []
                                                   NONE
                                                   [Op (BlockOp (Cons 0)) [mk_unit; Var 2]]))
                                  [Op (BlockOp (Build [Int 1; Con 0 []; Con 0 [0; 1]])) []])”;

Theorem tc_check1:
  ^tc_hb1 = ^tc_hb1_expected
Proof
  EVAL_TAC
QED

(*
   (func my_foo@471 (a)
   (if (op LessEq (op (Const 0)) (var a))
      (op (Cons 0) (var a))
      (op (Cons 0) (op (Cons 0) (var a))
         (call my_foo@471 (var a)) (var a))))
*)

(* Node x (my_foo x) (Leaf x) *)
val tc_hb2 = “cons_to_tc_and_hb (4000:num) 0 [Op (BlockOp (Cons 0)) [Var 0]; Call 0 (SOME 4000) [Var 0] NONE; Var 0]”;
val tc_hb2_expected = “TC (TCall 0 [Var 0] NONE) (HoleBlock 0 [Op (BlockOp (Cons 0)) [Var 0]] NONE [Var 0])”;

Theorem tail_cons_check2:
  ^tc_hb2 = ^tc_hb2_expected
Proof
  EVAL_TAC
QED

(* Node x (my_foo x) (other x) *)
val tc_hb3 = “cons_to_tc_and_hb (4000:num) 0 [Call 0 (SOME 4321) [Var 0] NONE; Call 0 (SOME 4000) [Var 0] NONE; Var 0]”;

Theorem tail_cons_check3:
  ^tc_hb3 = Invalid
Proof
  EVAL_TAC
QED

(* Node x (other x) (my_foo x) *)
val tc_hb4 = “cons_to_tc_and_hb (4000:num) 0 [Call 0 (SOME 4000) [Var 0] NONE; Call 0 (SOME 4321) [Var 0] NONE; Var 0]”;
val tc_hb4_expected = “TC (TCall 0 [Var 0] NONE) (HoleBlock 0 [] NONE [Call 0 (SOME 4321) [Var 0] NONE; Var 0])”;

Theorem tail_cons_check4:
  ^tc_hb4 = ^tc_hb4_expected
Proof
  EVAL_TAC
QED

