(*
  Perform tailrec modulo cons optimisation to make more functions tail-recursive.
*)
Theory bvi_tmc
Ancestors
  bvi backend_common
Libs
  preamble

(* TODO: Read only MemOps *)
(* This needs to be very strict - nothing should be able to fail here *)
(* Only IntOps/IntOp Const/BlockOp Cons (as long as all internal ones don't fail) *)
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

Definition dest_Cons_def:
  dest_Cons (BlockOp (Cons block_tag)) = SOME block_tag ∧
  dest_Cons _ = NONE
End

(* PHASE 1: extract everything into a let bound "call block" *)
(* TODO: binders are messed up *)

(* CallBlock tag left child right
   This is the "skeleton" of the BlockOp Cons
   - with the same tag,
   - where the recursive call is at the bottom of child,
   - where left and right are de Bruijn indeces of the other args, positions preserved,
     with the original expressions assumed to be let bound.
 *)
(* Two cases instead of the SUM type *)
Datatype:
  call_block = CallBlock num (num list) call_block (num list)
             | RCall num (num list)
End

(* Returns a tuple of expressions to be in let binders and a list of corresponding de Bruijn indeces,
   for the purpose of buidling left and right above.
   I don't think I am doing de Bruijn indexing correctly yet. *)
Definition to_binder_def:
  (to_binder next (Var n) = ([],next + n)) ∧
  (to_binder next exp = ([exp],next))
End

(* Same as above, but for multiple expressions. Used only for arguments to recursive call. Same indexing problem. *)
Definition to_binders_def:
  (to_binders next [] = ([],[])) ∧
  (to_binders next (h::t) =
   case to_binder next h of
   | (b,n) =>
       case to_binders next t of
       | (bs,ns) => (b ++ bs,n::ns))
End

(* Attempts to build a CallBlock from the tag and args of a BlockOp Cons.
   If no recursive call found, returns each op arg expression in a list and (INL) a list of corresponding de Bruijn indeces.
   If a recursive call is found, returns all extracted/let-bound expressions and (INR) the call block.
   If an effectful operation appears right of the recursive call, the expression is not eligible for transformation and NONE is returned.
   If multiple recursive calls are found, all but the last are let bound. *)
Definition to_binders_or_cb_def:
  (to_binders_or_cb _ _ _ [] = SOME ([],INL [])) ∧
  (to_binders_or_cb next loc tag [Call t loc' args h] =
   if loc' = SOME loc ∧ h = NONE then
     (* Recursive call found - base case of CallBlock *)
     case to_binders next args of
     | (bs,ns) => SOME (bs,INR (CallBlock tag [] (RCall t ns) []))
   else
     (* Not a recursive call - gets let-bound *)
     case to_binder next (Call t loc' args h) of
     | (bs,n) => SOME (bs,INL [n])) ∧
  (to_binders_or_cb next loc tag [Op op args] =
   case dest_Cons op of
   | SOME _ =>
       (* BlockOp Cons - try to recurse *)
       (case to_binders_or_cb next loc tag args of
        | NONE => NONE
        | SOME (bs,INL ns) =>
            (* No recursive call - whole thing gets let-bound *)
            (case to_binder next (Op op args) of
             | (bs,n) => SOME (bs,INL [n]))
        | SOME (bs,INR cb) =>
            (* Recursive call - inductive case of CallBlock *)
            SOME (bs, INR (CallBlock tag [] cb [])))
   | NONE =>
       (* Not a BlockOp Cons - whole thing gets let-bound *)
       (case to_binder next (Op op args) of
        | (bs,n) => SOME (bs,INL [n]))) ∧
  (to_binders_or_cb next _ _ [exp] =
   (* Some other expression - whole thing gets let-bound *)
   case to_binder next exp of
   | (bs,n) => SOME (bs,INL [n])) ∧
  (to_binders_or_cb next loc tag (h::t) =
   (* Recurse right to left to find last occurence of recursive call *)
   case to_binders_or_cb next loc tag t of
   | NONE => NONE
   | SOME (bs2,INL ns2) =>
       (* No recursive call to the right. See if the first has one. *)
       (case to_binders_or_cb (next + LENGTH bs2) loc tag [h] of
        | NONE => NONE
        | SOME (bs1,INL ns1) =>
            (* No recursive call, keep building binders. *)
            SOME (bs1 ++ bs2,INL (ns1 ++ ns2))
        | SOME (bs1,INR (CallBlock _ [] cb [])) =>
            (* We've constructed a CallBlock at this level with just h, pad the other args *)
            (* l and r are always empty if args is a singleton! *)
            SOME (bs1 ++ bs2,INR (CallBlock tag [] cb ns2)))
   | SOME (bs2,INR (CallBlock tag l child r)) =>
       (* Recursive call found, first is let bound and added to the left *)
       case to_binder (next + LENGTH bs2) h of
       | (bs1,n1) =>
           SOME (bs1 ++ bs2,INR (CallBlock tag (n1::l) child r)))
End

val ex1 = “[Op (IntOp (Const 1)) []; Call 0 (SOME 0) [] NONE; Call 0 (SOME 7) [] NONE; Op (IntOp (Const 3)) []]”
val ex1_call = “to_binders_or_cb 0 0 99 ^ex1”
EVAL ex1_call

(* Calls the above but throws away an unoptimisable BlockOp Cons. *)
Definition to_call_block_def:
  to_call_block loc tag args =
  case to_binders_or_cb 0 loc tag args of
  | (_,Left _) => NONE
  | (bs,Right cb) => SOME (bs,cb)
End

(* Convert back to BlockOp Cons for comparing semantics *)
(* Pattern match child at top level *)
Definition cb_to_BlockOp_Cons_def:
  cb_to_BlockOp_Cons loc (CallBlock tag l child r) =
  let l' = MAP (λn. Var n) l in
  let child' =
      case child of
      | Left (RCall t args h) =>
          let args' = MAP (λn. Var n) args in
          bvi$Call t (SOME loc) args' h
      | Right cb => cb_to_BlockOp_Cons loc cb in
  let r' = MAP (λn. Var n) r in
  Op (BlockOp (Cons tag)) $ l' ++ [child'] ++ r'
End

(* Let bind the result of the above for a semantically equivalent BVI expression. *)
(* Return OPTION *)
Definition rewrite_lb_BlockOp_Cons_def:
  rewrite_lb_BlockOp_Cons loc tag args =
    case to_call_block loc tag args of
    | NONE => Op (BlockOp (Cons tag)) args
    | SOME (bs,cb) =>
        Let bs $ cb_to_BlockOp_Cons loc cb
End

(* Prove they are semantically equivalent - this will need to move but easier here for now. *)
(*
Theorem evaluate_rewrite_lb_BlockOp_Cons:
  ∀exp exp' loc tag args env s t r.
    exp = Op (BlockOp (Cons tag)) args ∧
    exp' = rewrite_lb_BlockOp_Cons loc tag args ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    evaluate ([exp],env,s) = (r,t) ⇒
    evaluate ([exp'],env,s) = (r,t)
Proof
  rw []
  >> gvs [rewrite_lb_BlockOp_Cons_def]
  >> CASE_TAC >> gvs []
  >> CASE_TAC >> gvs []
  >> rename [‘to_call_block loc tag args = SOME (bs,block_op_cons)’]
  >> gvs [evaluate_def]
  >> CASE_TAC >> gvs []
  >> rename [‘evaluate (bs,env,s) = (vs,t')’]
  >> Induct_on ‘bs’
  >-
   (gvs [to_call_block_def]
    >> CASE_TAC >> gvs []
    >> CASE_TAC >> gvs []
    >> rw []
    >> gvs [evaluate_def]
    >> Cases_on ‘b’ >> gvs []
    >> rename [‘to_binders_or_cb 0 loc tag args = ([],Right (CallBlock tag' l c r))’]
    >> gvs [cb_to_BlockOp_Cons_def, evaluate_def]
    >> Cases_on ‘args’ >> gvs [to_binders_or_cb_def]
    >> Cases_on ‘t'’ >> gvs [to_binders_or_cb_def]
    >> cheat)
  >> cheat
QED
 *)

(* Phase 2 - Convert call block into a hole block, where the hole is filled by the optimised version of recursive call. *)

(* Like call_block, but base case is NONE instead of RCall *)
Datatype:
  hole_block = HoleBlock num (num list) (hole_block option) (num list)
End

(* Convert a call_block to a hole_block, and return the RCall to be replaced with optimised version. *)
Definition to_hole_block_def:
  to_hole_block (CallBlock tag l child r) =
    case child of
    | Left rcall => (HoleBlock tag l NONE r,rcall)
    | Right cb =>
        case to_hole_block cb of
        | (hb,rcall) => (HoleBlock tag l (SOME hb) r,rcall)
End

(* Convert hole block to a MutCons allocation with hole represented as Const 0 *)
Definition hb_to_MemOp_MutCons_def:
  hb_to_MemOp_MutCons (HoleBlock t l h r) =
    let l' = MAP (λn. Var n) l in
    let h' =
        case h of
        | SOME hb => hb_to_MemOp_MutCons hb
        | NONE => Op (IntOp (Const 0)) [] in
    let r' = MAP (λn. Var n) r in
    let i = LENGTH l in
      Op (MemOp (MutCons t i)) (l' ++ [h'] ++ r')
End



(* New attempt at phase 1 *)

Datatype:
  lb_exp = LbVar num
         (*| LbLet (bvi$exp list) lb_exp*)
         | LbRCall num (lb_exp list) (bvi$exp option)
         | LbCons num (lb_exp list)
End

Definition bind_def:
  (bind next (bvi$Var n) = ([],[LbVar (n + next)])) ∧
  (bind next exp = ([exp],[LbVar next]))
End

Definition bind_all_def:
  (bind_all next [] = ([],[])) ∧
  (bind_all next (x::xs) =
   case bind next x of
   | (b,v) =>
       case bind_all (next + LENGTH b) xs of
       | (bs,vs) => (b ++ bs,v ++ vs))
End

Definition bvi_to_bvi_lb_def:
  (bvi_to_bvi_lb _ _ [] = ([],[])) ∧
  (bvi_to_bvi_lb loc next [Call t l args h] =
   if l = SOME loc then
     case bind_all next args of
     | (bs,args') => (bs, [LbRCall t args' h])
   else
     bind next $ Call t l args h) ∧
  (bvi_to_bvi_lb loc next [Op op args] =
   case dest_Cons op of
   | SOME tag =>
       (case bvi_to_bvi_lb loc next (REVERSE args) of
        | (bs,args') =>
            (REVERSE bs,[LbCons tag (REVERSE args')]))
   | NONE => bind next $ Op op args) ∧
  (bvi_to_bvi_lb _ next [exp] = bind next exp) ∧
  (bvi_to_bvi_lb loc_opt next (x::xs) =
   (case bvi_to_bvi_lb loc_opt next [x] of
    | (bs1,[LbRCall t args h]) =>
        (case bind_all next xs of
         | (bs2,vs2) => (bs1 ++ bs2,(LbRCall t args h)::vs2))
    | (bs1,[LbCons tag args]) =>
        (case bind_all next xs of
         | (bs2,vs2) => (bs1 ++ bs2,(LbCons tag args)::vs2))
    | (bs1,[LbVar n]) =>
        (case bvi_to_bvi_lb loc_opt next xs of
         | (bs2,vs2) => (bs1 ++ bs2,(LbVar n)::vs2))))
End







(* Old way - there are conflicting definitions (hole_block) so stuff below here doesn't compile currently *)

Datatype:
  hole_block = HoleBlock num (num list) (hole_block option) (num list)
End

Datatype:
  tcall = TCall num (exp list) (exp option) (* loc is not needed here, as it is known in function body *)
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

Definition fill_hole_def:
  fill_hole i_old_hole_ptr i_old_hole_idx expr =
    let arg_hole_ptr = Var i_old_hole_ptr in
    let arg_hole_idx = Var i_old_hole_idx in
    Op (MemOp UpdateCons) [expr; arg_hole_idx; arg_hole_ptr]
End

(* Assumes that the function can and should be optimised - has been checked by rewrite_aux_def. *)
Definition rewrite_opt_BlockOp_Cons_def:
  rewrite_opt_BlockOp_Cons loc loc_opt i_old_hole_ptr i_old_hole_idx i_new_hole_ptr block_tag op_args =
    case cons_to_tc_and_hb loc block_tag op_args of
    | TC (TCall t args h) (HoleBlock tag l hole r) =>
        let hb               = HoleBlock tag l hole r in
        let i                = & LENGTH l in
        let arg_old_hole_ptr = Var (i_old_hole_ptr + 1) in
        let arg_old_hole_idx = Var (i_old_hole_idx + 1) in
        let var_new_hole_ptr = Var 0 in
        let exp_new_hole_idx = Op (IntOp (Const i)) [] in
        let exp_mut_cons     = to_mut_cons hb in
        let exp_update_hole  = Op (MemOp UpdateCons) [var_new_hole_ptr; arg_old_hole_idx; arg_old_hole_ptr] in
        let exp_tail_call    = Call t (SOME loc_opt) (exp_new_hole_idx :: var_new_hole_ptr :: args) h in
          Let [exp_mut_cons] $
              Let [exp_update_hole] $ exp_tail_call
    | _ =>
        let expr = Op (BlockOp (Cons block_tag)) op_args in
          fill_hole i_old_hole_ptr i_old_hole_idx expr
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
        fill_hole i_old_hole_ptr i_old_hole_idx (Op op op_args)) ∧
  (rewrite_opt loc loc_opt i_old_hole_ptr i_old_hole_idx i_new_hole_ptr (Tick x) =
    Tick $ rewrite_opt loc loc_opt i_old_hole_ptr i_old_hole_idx i_new_hole_ptr x) ∧
  (rewrite_opt loc loc_opt i_old_hole_ptr i_old_hole_idx _ expr =
   (* This should check if it's a recursive call *)
   fill_hole i_old_hole_ptr i_old_hole_idx expr)
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
(*
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
            (If (Op (BlockOp (TagLenEq 0 0)) [Var 1])
             (Op (MemOp UpdateCons) [mk_unit; Var 4; Var 3])
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
*)
