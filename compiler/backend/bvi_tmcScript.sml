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

(* CallBlock tag left child right
   This is the "skeleton" of the BlockOp Cons
   - with the same tag,
   - where the recursive call is at the bottom of child,
   - where left and right are de Bruijn indeces of the other args, positions preserved,
     with the original expressions assumed to be let bound.
 *)
Datatype:
  call_block = CallBlock num (num list) call_block (num list)
             | RCall num (num list)
End

(* Returns a tuple of expressions to be in let binders and a list of corresponding de Bruijn indeces,
   for the purpose of buidling left and right above. *)
Definition to_binder_def:
  (to_binder next (Var n) = ([],next + n)) ∧
  (to_binder next exp = ([exp],next))
End

(* Same as above, but for multiple expressions. Used only for arguments to recursive call. *)
Definition to_binders_def:
  (to_binders next [] = ([],[])) ∧
  (to_binders next (h::t) =
   case to_binder next h of
   | (b,n) =>
       case to_binders (next + LENGTH b) t of
       | (bs,ns) => (b ++ bs,n::ns))
End

(* Attempts to build a CallBlock from the tag and args of a BlockOp Cons.
   If no recursive call found, returns each op arg expression in a list and (INL) a list of corresponding de Bruijn indeces.
   If a recursive call is found, returns all extracted/let-bound expressions and (INR) the call block.
   If an effectful operation appears right of the recursive call, the expression is not eligible for transformation and NONE is returned.
   If multiple recursive calls are found, all but the last are let bound. *)
Definition cons_to_cb_aux_def:
  (cons_to_cb_aux _ _ _ [] = SOME ([],INL [])) ∧
  (cons_to_cb_aux next loc tag [Call t loc' args h] =
   if loc' = SOME loc ∧ h = NONE then
     (* Recursive call found - base case of CallBlock *)
     case to_binders next args of
     | (bs,ns) => SOME (bs,INR (CallBlock tag [] (RCall t ns) []))
   else
     (* Not a recursive call - gets let-bound *)
     case to_binder next (Call t loc' args h) of
     | (bs,n) => SOME (bs,INL [n])) ∧
  (cons_to_cb_aux next loc tag [Op op args] =
   case dest_Cons op of
   | SOME tag' =>
       (* BlockOp Cons - try to recurse *)
       (case cons_to_cb_aux next loc tag' args of
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
  (cons_to_cb_aux next _ _ [exp] =
   (* Some other expression - whole thing gets let-bound *)
   case to_binder next exp of
   | (bs,n) => SOME (bs,INL [n])) ∧
  (cons_to_cb_aux next loc tag (h::t) =
   (* Recurse right to left to find last occurence of recursive call *)
   case cons_to_cb_aux next loc tag t of
   | NONE => NONE
   | SOME (bs2,INL ns2) =>
       (* No recursive call to the right. See if the first has one. *)
       (case cons_to_cb_aux (next + LENGTH bs2) loc tag [h] of
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

Theorem cons_to_cb_aux_sing:
  ∀next loc tag arg bs cb.
    cons_to_cb_aux next loc tag [arg] = SOME (bs,INR cb) ⇒
    ∃child.
      cb = CallBlock tag [] child []
Proof
  rw []
  >> Cases_on ‘arg’ >> gvs [cons_to_cb_aux_def, to_binder_def]
  >-
   (pop_assum mp_tac
    >> IF_CASES_TAC >> gvs [CaseEq "prod"]
    >> strip_tac
    >> gvs [])
  >> pop_assum mp_tac
  >> CASE_TAC >> gvs []
  >> CASE_TAC >> gvs []
  >> CASE_TAC >> gvs []
  >> CASE_TAC >> gvs []
  >> strip_tac
  >> gvs []
QED

Theorem cons_to_cb_aux_wf:
  ∀next loc tag args bs cb.
    cons_to_cb_aux next loc tag args = SOME (bs,INR cb) ⇒
    ∃l child r.
      cb = CallBlock tag l child r
Proof
  recInduct cons_to_cb_aux_ind
  >> rw []
  >~ [‘cons_to_cb_aux next loc tag []’] >-
   gvs [cons_to_cb_aux_def]
  >~ [‘cons_to_cb_aux next loc tag [Call t loc' args h]’] >-
   (gvs [cons_to_cb_aux_def]
    >> pop_assum mp_tac
    >> reverse IF_CASES_TAC >> gvs [to_binder_def]
    >> CASE_TAC >> gvs []
    >> strip_tac
    >> gvs [])
  >~ [‘cons_to_cb_aux next loc tag [Op op args]’] >-
   (gvs [cons_to_cb_aux_def]
    >> pop_assum mp_tac
    >> CASE_TAC >> gvs []
    >> CASE_TAC >> gvs []
    >> CASE_TAC >> gvs []
    >> CASE_TAC >> gvs []
    >> CASE_TAC >> gvs []
    >> strip_tac
    >> gvs [])
  >~ [‘cons_to_cb_aux next loc tag [Var n]’] >-
   (gvs [cons_to_cb_aux_def, to_binder_def])
  >~ [‘cons_to_cb_aux next loc tag [If x1 x2 x3]’] >-
   (gvs [cons_to_cb_aux_def, to_binder_def])
  >~ [‘cons_to_cb_aux next loc tag [Let xs x]’] >-
   (gvs [cons_to_cb_aux_def, to_binder_def])
  >~ [‘cons_to_cb_aux next loc tag [Raise x]’] >-
   (gvs [cons_to_cb_aux_def, to_binder_def])
  >~ [‘cons_to_cb_aux next loc tag [Tick x]’] >-
   (gvs [cons_to_cb_aux_def, to_binder_def])
  >~ [‘cons_to_cb_aux next loc tag [Force _ _]’] >-
   (gvs [cons_to_cb_aux_def, to_binder_def])
  >~ [‘cons_to_cb_aux next loc tag (x::y::xs)’] >-
   (gvs [cons_to_cb_aux_def]
    >> Cases_on ‘cons_to_cb_aux next loc tag (y::xs)’ >> gvs []
    >> Cases_on ‘x'’ >> gvs []
    >> reverse $ Cases_on ‘r’ >> gvs []
    >- gvs [CaseEq "prod"]
    >> gvs [CaseEq "option"]
    >> Cases_on ‘v’ >> gvs []
    >> Cases_on ‘r’ >> gvs []
    >> imp_res_tac cons_to_cb_aux_sing
    >> gvs [])
QED

Definition reverse_idx_def:
  reverse_idx len (n:num) = len - n - 1
End

(* Since op args are parsed right to left, we need to reverse the indexes to match the binders *)
Definition reverse_idxs_def:
  (reverse_idxs len (CallBlock tag l child r) =
     let l' = MAP (reverse_idx len) l in
     let child' = reverse_idxs len child in
     let r' = MAP (reverse_idx len) r in
       CallBlock tag l' child' r') ∧
  (reverse_idxs _ rcall = rcall) (* call args parsed left to right *)
End

Definition set_call_idxs_def:
  (set_call_idxs (n:num) [] = (n,[])) ∧
  (set_call_idxs (n:num) (_::t) =
     case set_call_idxs (n + 1) t of
     | (n',t') => (n',n::t'))
End

Definition set_op_idxs_def:
  (set_op_idxs (n:num) [] = (n,[])) ∧
  (set_op_idxs (n:num) (_::t) =
   case set_op_idxs n t of
   | (n',t') => (n' + 1,n'::t'))
End

Definition set_idxs_def:
  (set_idxs n (RCall ts args) =
   case set_call_idxs n args of
   | (n',args') => (n',RCall ts args')) ∧
  (set_idxs n (CallBlock tag l c r) =
   case set_op_idxs n r of
   | (nr,r') =>
       (case set_idxs nr c of
        | (nc,c') =>
            case set_call_idxs nc l of
            | (nl,l') =>
                (nl,CallBlock tag l' c' r')))
End

(* Calls the above but throws away an unoptimisable BlockOp Cons. *)
Definition cons_to_cb_def:
  cons_to_cb loc tag args =
  case cons_to_cb_aux 0 loc tag args of
  | SOME (bs,INR cb) =>
      (case set_idxs 0 cb of
       | (_,cb') => SOME (bs,cb'))
  | _ => NONE
End

Theorem cons_to_cb_wf:
  ∀loc tag args bs cb.
    cons_to_cb loc tag args = SOME (bs,cb) ⇒
    ∃l child r.
      cb = CallBlock tag l child r
Proof
  rw []
  >> Cases_on ‘args’ >> gvs [cons_to_cb_def, cons_to_cb_aux_def]
  >> gvs [CaseEq "option", CaseEq "prod", CaseEq "sum"]
  >> imp_res_tac cons_to_cb_aux_wf
  >> gvs [set_idxs_def, CaseEq "prod"]
QED

val ex1 = “[Op (IntOp (Const 1)) []; Call 0 (SOME 7) [] NONE; Call 0 (SOME 4) [] NONE; Op (IntOp (Const 3)) []]”
val ex1_call = “cons_to_cb 7 99 ^ex1”
(* EVAL ex1_call *)

val ex2 = “[Op (IntOp (Const 1)) [];
            Op (BlockOp (Cons 98)) [Call 0 (SOME 7) [] NONE];
            Call 0 (SOME 4) [] NONE;
            Op (IntOp (Const 3)) []]”
val ex2_call = “cons_to_cb 7 99 ^ex2”
(* EVAL ex2_call *)

val ex3 = “[Op (IntOp (Const 1)) [];
            Op (BlockOp (Cons 98)) [
                   Op (IntOp (Const 2)) [];
                   Call 0 (SOME 7) [] NONE;
                   Op (IntOp (Const 3)) []];
            Call 0 (SOME 4) [] NONE;
            Op (IntOp (Const 4)) []]”
val ex3_call = “cons_to_cb 7 99 ^ex3”
(* EVAL ex3_call *)

val ex4 = “[Op (IntOp (Const 1)) [];
            Op (BlockOp (Cons 98)) [
                   Op (IntOp (Const 2)) [];
                   Call 0 (SOME 7) [
                              Op (IntOp (Const 3)) [];
                              Op (IntOp (Const 4)) []] NONE;
                   Op (IntOp (Const 5)) []];
            Call 0 (SOME 4) [] NONE;
            Op (IntOp (Const 6)) []]”
val ex4_call = “cons_to_cb 7 99 ^ex4”
(* EVAL ex4_call *)

(* Convert back to BlockOp Cons for comparing semantics *)
Definition cb_to_cons_def:
  cb_to_cons loc (CallBlock tag l child r) =
  let l' = MAP (λn. Var n) l in
  let child' = cb_to_cons loc child in
  let r' = MAP (λn. Var n) r in
  Op (BlockOp (Cons tag)) $ l' ++ [child'] ++ r'
End

(* Let bind the result of the above for a semantically equivalent BVI expression. *)
Definition cb_to_bvi_def:
  cb_to_bvi loc tag args =
    case cons_to_cb loc tag args of
    | SOME (bs,cb) =>
        SOME $ Let bs $ cb_to_cons loc cb
    | NONE => NONE
End

(* Phase 2 - Convert call block into a hole block, where the hole is filled by the optimised version of recursive call. *)

(* Like call_block, but base case is NONE instead of RCall *)
Datatype:
  hole_block = HoleBlock num (num list) hole_block (num list)
             | Hole
End

(* Convert a hole_block to a MutCons allocation with hole represented as Const 0 *)
Definition hb_to_mutcons_def:
  (hb_to_mutcons (HoleBlock t l hb r) =    
     let l' = MAP (λn. Var n) l in
     let hb' = hb_to_mutcons hb in
     let r' = MAP (λn. Var n) r in
     let i = LENGTH l in
       Op (MemOp (MutCons t i)) (l' ++ [hb'] ++ r')) ∧
  (hb_to_mutcons Hole = Op (IntOp (Const 0)) [])
End

Definition optimise_call_def:
  optimise_call loc idx ptr ts args = bvi$Call ts (SOME loc) (idx::ptr::[(* args *)]) NONE
End

(* Convert a call_block to a hole_block, and return the RCall ingredients to be replaced with optimised version. *)
Definition cb_to_hb_def:
  (cb_to_hb (CallBlock tag l child r) =
     case cb_to_hb child of
     | (hb,ts,args) => (HoleBlock tag l hb r,ts,args)) ∧
  (cb_to_hb (RCall ts args) = (Hole,ts,args))
End

Definition cb_to_bvi_wrapper_def:
  cb_to_bvi_wrapper loc loc_opt i_ptr cb =
    case cb_to_hb cb of
    | (HoleBlock tag l hole r,ts,args) =>
        let hb            = HoleBlock tag l hole r in
        let i             = & LENGTH l in
        let var_ptr       = Var i_ptr in
        let exp_idx       = Op (IntOp (Const i)) [] in
        let exp_mut_cons  = hb_to_mutcons hb in
        let exp_tail_call = optimise_call loc_opt exp_idx var_ptr ts args in
        let exp_finalise  = Op (MemOp FinaliseCons) [var_ptr] in
          Let [exp_mut_cons; exp_tail_call] exp_finalise
End

Definition cb_to_bvi_worker_def:
  cb_to_bvi_worker loc loc_opt i_ptr i_idx cb =
    case cb_to_hb cb of
    | (HoleBlock tag l hole r,ts,args) =>
        let hb               = HoleBlock tag l hole r in
        let i                = & LENGTH l in
        let arg_old_ptr      = Var (i_ptr + 1) in
        let arg_old_idx      = Var (i_idx + 1) in
        let var_new_ptr      = Var 0 in
        let exp_new_idx      = Op (IntOp (Const i)) [] in
        let exp_mut_cons     = hb_to_mutcons hb in
        let exp_update_hole  = Op (MemOp UpdateCons) [var_new_ptr; arg_old_idx; arg_old_ptr] in
        let exp_tail_call    = optimise_call loc_opt exp_new_idx var_new_ptr ts args in
          Let [exp_mut_cons] $
              Let [exp_update_hole] $ exp_tail_call
End

Definition fill_hole_def:
  fill_hole i_old_ptr i_old_idx expr =
    let arg_hole_ptr = Var i_old_ptr in
    let arg_hole_idx = Var i_old_idx in
    Op (MemOp UpdateCons) [expr; arg_hole_idx; arg_hole_ptr]
End

Definition rewrite_wrapper_cons_def:
  rewrite_wrapper_cons loc loc_opt i_ptr tag args =
    case cons_to_cb loc tag args of
    | SOME (bs,cb) =>
        SOME $ Let bs $ cb_to_bvi_wrapper loc loc_opt i_ptr cb
    | NONE => NONE
End

(* Assumes that the function can and should be optimised - has been checked by rewrite_wrapper. *)
Definition rewrite_worker_cons_def:
  rewrite_worker_cons loc loc_opt i_ptr i_idx tag args =
    case cons_to_cb loc tag args of
    | SOME (bs,cb) =>
        Let bs $ cb_to_bvi_worker loc loc_opt i_ptr i_idx cb
    | NONE =>
        let expr = Op (BlockOp (Cons tag)) args in
          fill_hole i_ptr i_idx expr
End

(* Expression rewriting *)

Definition rewrite_wrapper_def:
  (rewrite_wrapper loc loc_opt i_ptr (Var n) = NONE) ∧
  (rewrite_wrapper loc loc_opt i_ptr (If xi xt xe) =
    let opt_t = rewrite_wrapper loc loc_opt i_ptr xt in
    let opt_e = rewrite_wrapper loc loc_opt i_ptr xe in
    case (opt_t, opt_e) of
    | (NONE, NONE) => NONE
    | (SOME yt, NONE) => SOME $ If xi yt xe
    | (NONE, SOME ye) => SOME $ If xi xt ye
    | (SOME yt, SOME ye) => SOME $ If xi yt ye) ∧
  (rewrite_wrapper loc loc_opt i_ptr (Let xs x) =
    case rewrite_wrapper loc loc_opt (i_ptr + LENGTH xs) x of
    | NONE => NONE
    | SOME y => SOME $ Let xs y) ∧
  (rewrite_wrapper loc loc_opt i_ptr (Raise x) = NONE) ∧
  (rewrite_wrapper loc loc_opt i_ptr (Tick x) = OPTION_MAP Tick $ rewrite_wrapper loc loc_opt i_ptr x) ∧
  (rewrite_wrapper loc loc_opt i_ptr (Force _ n) = NONE) ∧
  (rewrite_wrapper loc loc_opt i_ptr (Call t d args h) = NONE) ∧
  (rewrite_wrapper loc loc_opt i_ptr (Op op op_args) =
    case dest_Cons op of
    | SOME block_tag => rewrite_wrapper_cons loc loc_opt i_ptr block_tag op_args
    | NONE => NONE) ∧
  (rewrite_wrapper loc loc_opt i_ptr _ = NONE)
End

(* Assumes that the function can and should be optimised - has been checked by rewrite_wrapper. *)
Definition rewrite_worker_def:
  (rewrite_worker loc loc_opt i_old_ptr i_old_idx (If xi xt xe) =
    let yt = rewrite_worker loc loc_opt i_old_ptr i_old_idx xt in
    let ye = rewrite_worker loc loc_opt i_old_ptr i_old_idx xe in
    If xi yt ye) ∧
  (rewrite_worker loc loc_opt i_old_ptr i_old_idx (Let xs x) =
    let offset = LENGTH xs in
      Let xs $ rewrite_worker loc loc_opt (i_old_ptr + offset) (i_old_idx + offset) x) ∧
  (rewrite_worker loc loc_opt i_old_ptr i_old_idx (Raise x) = Raise x) ∧
  (rewrite_worker loc loc_opt i_old_ptr i_old_idx (Op op op_args) =
    case dest_Cons op of
    | SOME block_tag => rewrite_worker_cons loc loc_opt i_old_ptr i_old_idx block_tag op_args
    | NONE =>
        fill_hole i_old_ptr i_old_idx (Op op op_args)) ∧
  (rewrite_worker loc loc_opt i_old_ptr i_old_idx (Tick x) =
    Tick $ rewrite_worker loc loc_opt i_old_ptr i_old_idx x) ∧
  (rewrite_worker loc loc_opt i_old_ptr i_old_idx expr =
   (* This should check if it's a recursive call *)
   fill_hole i_old_ptr i_old_idx expr)
End

Definition compile_exp_def:
  compile_exp (loc:num) (next:num) (arity:num) (exp:bvi$exp) =
    case rewrite_wrapper loc next arity exp of
    | NONE => NONE
    | SOME exp_wrapper =>
      let exp_worker = rewrite_worker loc next arity (arity + 1) exp in
      SOME (exp_wrapper, exp_worker)
End

Definition compile_prog_def:
  (compile_prog next [] = (next, [])) ∧
  (compile_prog next ((loc, arity, exp)::xs) =
    case compile_exp loc next arity exp of
    | NONE =>
        let (n, ys) = compile_prog next xs in
          (n, (loc, arity, exp)::ys)
    | SOME (exp_wrapper, exp_worker) =>
        let (n, ys) = compile_prog (next + bvl_to_bvi_namespaces) xs in
        (n, (loc, arity, exp_wrapper)::(next, arity + 2, exp_worker)::ys))
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
