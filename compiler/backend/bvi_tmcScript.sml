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
  (effectful_exps [Var _] = T) ∧
  (effectful_exps [If e1 e2 e3] = (effectful_exps [e1] ∨ effectful_exps [e2] ∨ effectful_exps [e3])) ∧
  (effectful_exps [Let es e] = effectful_exps (e::es)) ∧
  (effectful_exps [Raise _] = T) ∧
  (effectful_exps [Tick e] = T) ∧ (* TODO *)
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

Definition bind_def:
  (bind (n:num) [] = ([],n)) ∧
  (bind (n:num) (_::t) =
   case bind (n + 1) t of
   | (vs,n') => (n::vs,n'))
End

Theorem bind_size:
  ∀args n bs vs n'.
    bind n args = (vs,n') ⇒
    LENGTH args = LENGTH vs
Proof
  Induct >> gvs [bind_def]
  >> rw []
  >> gvs [CaseEq "prod"]
  >> first_x_assum irule
  >> first_assum $ irule_at Any
QED

Definition shift_vars_def:
  (shift_vars (n:num) [] = []) ∧
  (shift_vars (n:num) (h::t) = (h + n : num)::shift_vars n t)
End

Definition shift_cb_def:
  (shift_cb n (RCall ts args) = RCall ts (shift_vars n args)) ∧
  (shift_cb n (CallBlock tag l c r) =
   let l' = shift_vars n l in
   let c' = shift_cb n c in
   let r' = shift_vars n r in
     CallBlock tag l' c' r')
End

(* Attempts to build a CallBlock from the tag and args of a BlockOp Cons.
   If no recursive call found, returns each op arg expression in a list and (INL) a list of corresponding de Bruijn indeces.
   If a recursive call is found, returns all extracted/let-bound expressions and (INR) the call block.
   If an effectful operation appears right of the recursive call, the expression is not eligible for transformation and NONE is returned.
   If multiple recursive calls are found, all but the last are let bound. *)
Definition bvi_to_cb_aux_def:
  (bvi_to_cb_aux _ _ [] = SOME ([],INL [])) ∧
  (bvi_to_cb_aux loc tag [Call t loc' args h] =
   if loc' = SOME loc ∧ h = NONE then
     (* Recursive call found - base case of CallBlock *)
     case bind 0 args of
     | (vs,_) => SOME (args,INR (CallBlock tag [] (RCall t vs) []))
   else
     (* Not a recursive call - gets let-bound *)
     SOME ([Call t loc' args h],INL [0])) ∧
  (bvi_to_cb_aux loc tag [Op op args] =
   case dest_Cons op of
   | SOME tag' =>
       (* BlockOp Cons - try to recurse *)
       (case bvi_to_cb_aux loc tag' args of
        | NONE => NONE
        | SOME (bs,INL vs) =>
            (* No recursive call - whole thing gets let-bound *)
            SOME ([Op op args],INL [0])
        | SOME (bs,INR cb) =>
            (* Recursive call - inductive case of CallBlock *)
            SOME (bs, INR (CallBlock tag [] cb [])))
   | NONE =>
       (* Not a BlockOp Cons - whole thing gets let-bound *)
       SOME ([Op op args],INL [0])) ∧
  (bvi_to_cb_aux _ _ [exp] =
   (* Some other expression - whole thing gets let-bound *)
   SOME ([exp],INL [0])) ∧
  (bvi_to_cb_aux loc tag (h::t) =
   (* Recurse right to left to find last occurence of recursive call *)
   case bvi_to_cb_aux loc tag t of
   | NONE => NONE
   | SOME (bs2,INL vs2) =>
       (* No recursive call to the right. See if the first has one. *)
       (case bvi_to_cb_aux loc tag [h] of
        | NONE => NONE
        | SOME (bs1,INL vs1) =>
            (* No recursive call, keep building binders. *)
            let vs2' = shift_vars (LENGTH bs1) vs2 in
            SOME (bs1 ++ bs2,INL (vs1 ++ vs2'))
        | SOME (bs1,INR (CallBlock _ [] child [])) =>
            (* We've constructed a CallBlock at this level with just h, pad the other args *)
            (* l and r are always empty if args is a singleton *)
            let vs2' = shift_vars (LENGTH bs1) vs2 in
              SOME (bs1 ++ bs2,INR (CallBlock tag [] child vs2'))
        | _ => NONE)
   | SOME (bs2,INR cb) =>
       (* Recursive call found, first is let bound and added to the left *)
       case shift_cb 1 cb of
       | CallBlock tag l child r =>
           let cb' = CallBlock tag (0::l) child r in
             SOME (h::bs2,INR cb')
       | _ => NONE)
End

Theorem bvi_to_cb_aux_sing:
  ∀loc tag arg bs cb.
    bvi_to_cb_aux loc tag [arg] = SOME (bs,INR cb) ⇒
    ∃child.
      cb = CallBlock tag [] child []
Proof
  rw []
  >> Cases_on ‘arg’ >> gvs [bvi_to_cb_aux_def, bind_def]
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

Theorem bvi_to_cb_aux_wf:
  ∀loc tag args bs cb.
    bvi_to_cb_aux loc tag args = SOME (bs,INR cb) ⇒
    ∃l child r.
      cb = CallBlock tag l child r
Proof
  recInduct bvi_to_cb_aux_ind
  >> rw []
  >~ [‘bvi_to_cb_aux loc tag []’] >-
   gvs [bvi_to_cb_aux_def]
  >~ [‘bvi_to_cb_aux loc tag [Call t loc' args h]’] >-
   (gvs [bvi_to_cb_aux_def]
    >> pop_assum mp_tac
    >> reverse IF_CASES_TAC >> gvs [bind_def]
    >> CASE_TAC >> gvs [CaseEq "prod"]
    >> strip_tac
    >> gvs [])
  >~ [‘bvi_to_cb_aux loc tag [Op op args]’] >-
   (gvs [bvi_to_cb_aux_def]
    >> pop_assum mp_tac
    >> CASE_TAC >> gvs []
    >> CASE_TAC >> gvs []
    >> CASE_TAC >> gvs []
    >> CASE_TAC >> gvs []
    >> strip_tac
    >> gvs [])
  >~ [‘bvi_to_cb_aux loc tag [Var n]’] >-
   (gvs [bvi_to_cb_aux_def])
  >~ [‘bvi_to_cb_aux loc tag [If x1 x2 x3]’] >-
   (gvs [bvi_to_cb_aux_def])
  >~ [‘bvi_to_cb_aux loc tag [Let xs x]’] >-
   (gvs [bvi_to_cb_aux_def])
  >~ [‘bvi_to_cb_aux loc tag [Raise x]’] >-
   (gvs [bvi_to_cb_aux_def])
  >~ [‘bvi_to_cb_aux loc tag [Tick x]’] >-
   (gvs [bvi_to_cb_aux_def])
  >~ [‘bvi_to_cb_aux loc tag [Force _ _]’] >-
   (gvs [bvi_to_cb_aux_def])
  >~ [‘bvi_to_cb_aux loc tag (x::y::xs)’] >-
   (gvs [bvi_to_cb_aux_def]
    >> Cases_on ‘bvi_to_cb_aux loc tag (y::xs)’ >> gvs []
    >> Cases_on ‘x'’ >> gvs []
    >> reverse $ Cases_on ‘r’ >> gvs [shift_cb_def]
    >> gvs [CaseEq "option", CaseEq "prod", CaseEq "sum", CaseEq "list"])
QED

(* Calls the above but throws away an unoptimisable BlockOp Cons. *)
Definition bvi_to_cb_def:
  bvi_to_cb loc tag args =
  case bvi_to_cb_aux loc tag args of
  | SOME (bs,INR cb) => SOME (bs,cb)
  | _ => NONE
End

Theorem bvi_to_cb_wf:
  ∀loc tag args bs cb.
    bvi_to_cb loc tag args = SOME (bs,cb) ⇒
    ∃l child r.
      cb = CallBlock tag l child r
Proof
  rw []
  >> Cases_on ‘args’ >> gvs [bvi_to_cb_def, bvi_to_cb_aux_def]
  >> gvs [CaseEq "option", CaseEq "prod", CaseEq "sum"]
  >> imp_res_tac bvi_to_cb_aux_wf
  >> gvs []
QED

val ex1 = “[Op (IntOp (Const 1)) []; Call 0 (SOME 7) [] NONE; Call 0 (SOME 4) [] NONE; Op (IntOp (Const 3)) []]”
val ex1_call = “bvi_to_cb 7 99 ^ex1”
(* EVAL ex1_call *)

val ex2 = “[Op (IntOp (Const 1)) [];
            Op (BlockOp (Cons 98)) [Call 0 (SOME 7) [] NONE];
            Call 0 (SOME 4) [] NONE;
            Op (IntOp (Const 3)) []]”
val ex2_call = “bvi_to_cb 7 99 ^ex2”
(* EVAL ex2_call *)

val ex3 = “[Op (IntOp (Const 1)) [];
            Op (BlockOp (Cons 98)) [
                   Op (IntOp (Const 2)) [];
                   Call 0 (SOME 7) [] NONE;
                   Op (IntOp (Const 3)) []];
            Call 0 (SOME 4) [] NONE;
            Op (IntOp (Const 4)) []]”
val ex3_call = “bvi_to_cb 7 99 ^ex3”
(* EVAL ex3_call *)

val ex4 = “[Op (IntOp (Const 0)) [];
            Op (BlockOp (Cons 98)) [
                   Op (IntOp (Const 1)) [];
                   Call 0 (SOME 100) [
                              Op (IntOp (Const 2)) [];
                              Op (IntOp (Const 3)) []] NONE;
                   Op (IntOp (Const 4)) []];
            Call 0 (SOME 5) [] NONE;
            Op (IntOp (Const 6)) []]”
val ex4_call = “bvi_to_cb 100 99 ^ex4”
(* EVAL ex4_call *)

(* Convert back to BlockOp Cons for comparing semantics *)
Definition cb_to_bvi_def:
  (cb_to_bvi loc (CallBlock tag l child r) =
     let l' = MAP (λn. Var n) l in
     let child' = cb_to_bvi loc child in
     let r' = MAP (λn. Var n) r in
       Op (BlockOp (Cons tag)) $ l' ++ [child'] ++ r') ∧
  (cb_to_bvi loc (RCall ts args) =
     let args' = MAP (λn. Var n) args in
       bvi$Call ts (SOME loc) args' NONE)
End

(* Let bind the result of the above for a semantically equivalent BVI expression. *)
Definition bvi_to_cb_to_bvi_def:
  bvi_to_cb_to_bvi loc tag args =
    case bvi_to_cb loc tag args of
    | SOME (bs,cb) =>
        SOME $ Let bs $ cb_to_bvi loc cb
    | NONE => NONE
End

Theorem bvi_to_cb_aux_size:
  ∀loc tag args bs sum.
    bvi_to_cb_aux loc tag args = SOME (bs,sum) ⇒
    list_size exp_size bs < exp_size (Op (BlockOp (Cons tag)) args) ∧
    (∀vs.
       sum = INL vs ⇒
       LENGTH vs < exp_size (Op (BlockOp (Cons tag)) args)) ∧
    (∀cb.
       sum = INR cb ⇒
       exp_size (cb_to_bvi loc cb) < exp_size (Op (BlockOp (Cons tag)) args))
Proof
  recInduct bvi_to_cb_aux_ind
  >> rw [bvi_to_cb_aux_def]
  >> cheat
QED

Theorem bvi_to_cb_size:
  ∀loc tag args bs cb.
    bvi_to_cb loc tag args = SOME (bs,cb) ⇒
    list_size exp_size bs < exp_size (Op (BlockOp (Cons tag)) args) ∧
    exp_size (cb_to_bvi loc cb) < exp_size (Op (BlockOp (Cons tag)) args)
Proof
  rpt gen_tac
  >> strip_tac
  >> imp_res_tac bvi_to_cb_wf
  >> gvs [CaseEq "option", bvi_to_cb_def, CaseEq "option", CaseEq "prod", CaseEq "sum"]
  >> drule_all bvi_to_cb_aux_size
  >> strip_tac
  >> gvs []
QED

(* Phase 2 - Convert call block into a hole block, where the hole is filled by the optimised version of recursive call. *)

(* Like call_block, but base case is NONE instead of RCall *)
Datatype:
  hole_block = HoleBlock num (num list) hole_block (num list)
             | Hole
End

(* Convert a call_block to a hole_block, and return the RCall ingredients to be replaced with optimised version. *)
Definition cb_to_hb_def:
  (cb_to_hb (CallBlock tag l child r) =
     case cb_to_hb child of
     | (hb,ts,args) => (HoleBlock tag l hb r,ts,args)) ∧
  (cb_to_hb (RCall ts args) = (Hole,ts,args))
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
  optimise_call loc idx ptr ts args =
  (* There are let binders in the optimised version *)
  let args' = MAP (λn. Var (n + 2)) args in
    bvi$Call ts (SOME loc) (idx::ptr::args') NONE
End

Definition hb_to_bvi_wrapper_def:
  hb_to_bvi_wrapper loc loc_opt i_ptr (HoleBlock tag l hole r) ts args =
    let hb            = HoleBlock tag l hole r in
    let i             = & LENGTH l in
    let var_ptr       = Var i_ptr in
    let exp_idx       = Op (IntOp (Const i)) [] in
    let exp_mut_cons  = hb_to_mutcons hb in
    let exp_tail_call = optimise_call loc_opt exp_idx var_ptr ts args in
    let exp_finalise  = Op (MemOp FinaliseCons) [var_ptr] in
      Let [exp_mut_cons; exp_tail_call] exp_finalise
End

Definition hb_to_bvi_worker_def:
  hb_to_bvi_worker loc loc_opt i_ptr i_idx (HoleBlock tag l hole r) ts args =
    let hb               = HoleBlock tag l hole r in
    let i                = & LENGTH l in
    let arg_old_ptr      = Var (i_ptr + 1) in
    let arg_old_idx      = Var (i_idx + 1) in
    let exp_new_idx      = Op (IntOp (Const i)) [] in
    let exp_mut_cons     = hb_to_mutcons hb in
    let exp_update_hole  = Op (MemOp UpdateCons) [Var 0; arg_old_idx; arg_old_ptr] in
    let exp_tail_call    = optimise_call loc_opt exp_new_idx (Var 1) ts args in
      Let [exp_mut_cons] $ Let [exp_update_hole] $ exp_tail_call
End

Definition fill_hole_def:
  fill_hole i_old_ptr i_old_idx expr =
    let arg_hole_ptr = Var i_old_ptr in
    let arg_hole_idx = Var i_old_idx in
    Op (MemOp UpdateCons) [expr; arg_hole_idx; arg_hole_ptr]
End

Definition rewrite_wrapper_cons_def:
  rewrite_wrapper_cons loc loc_opt i_ptr tag args =
    case bvi_to_cb loc tag args of
    | SOME (bs,cb) =>
        (case cb_to_hb cb of
         | (hb,ts,args) =>
             let offset = LENGTH bs in
             SOME $ Let bs $ hb_to_bvi_wrapper loc loc_opt (offset + i_ptr) hb ts args)
    | NONE => NONE
End

(* Assumes that the function can and should be optimised - has been checked by rewrite_wrapper. *)
Definition rewrite_worker_cons_def:
  rewrite_worker_cons loc loc_opt i_ptr i_idx tag args =
    case bvi_to_cb loc tag args of
    | SOME (bs,cb) =>
        (case cb_to_hb cb of
         | (hb,ts,args) =>
             let offset = LENGTH bs in
             Let bs $ hb_to_bvi_worker loc loc_opt (offset + i_ptr) (offset + i_idx) hb ts args)
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
