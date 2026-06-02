(*
  Perform tailrec modulo cons optimisation to make more functions tail-recursive.
*)
Theory bvi_tmc
Ancestors
  bvi backend_common
Libs
  preamble

Definition pure_op_def:
  (pure_op (Label _) _ = F) ∧
  (pure_op (FFI _) _ = F) ∧
  (pure_op (IntOp (Const n)) [] = small_enough_int n) ∧
  (pure_op (IntOp _) _ = F) ∧
  (pure_op (WordOp _) _ = F) ∧
  (pure_op (BlockOp (Cons _)) _ = T) ∧
  (pure_op (BlockOp LengthBlock) _ = T) ∧
  (pure_op (BlockOp (TagEq _)) _ = T) ∧
  (pure_op (BlockOp (LenEq _)) _ = T) ∧
  (pure_op (BlockOp (TagLenEq _ _)) _ = T) ∧
  (pure_op (BlockOp _) _ = F) ∧
  (pure_op (GlobOp _) _ = F) ∧
  (pure_op (MemOp ConfigGC) _ = T) ∧
  (pure_op (MemOp _) _ = F) ∧
  (pure_op Install _ = F) ∧
  (pure_op (ThunkOp _) _ = F)
End

Definition pure_exps_def:
  (pure_exps [] = T) ∧
  (pure_exps [Var _] = F) ∧
  (pure_exps [If e1 e2 e3] = F) ∧
  (pure_exps [Let es e] = (pure_exps [e] ∧ pure_exps es)) ∧
  (pure_exps [Raise _] = F) ∧
  (pure_exps [Tick e] = F) ∧
  (pure_exps [Call _ _ _ _] = F) ∧
  (pure_exps [Force _ _] = F) ∧
  (pure_exps [Op op args] = (pure_op op args ∧ pure_exps args)) ∧
  (pure_exps (h::t) = (pure_exps [h] ∧ pure_exps t))
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
  ∀args n vs n'.
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

Definition call_to_cb_def:
  call_to_cb loc call_ts call_loc call_args call_h =
  if call_loc = SOME loc ∧ call_h = NONE then
    case bind 0 call_args of
    | (vs,_) => SOME (call_args, RCall call_ts vs)
  else NONE
End

(* Attempts to build a CallBlock from the tag and args of a BlockOp Cons.
   If no recursive call found, returns each op arg expression in a list and (INL) a list of corresponding de Bruijn indeces.
   If a recursive call is found, returns all extracted/let-bound expressions and (INR) the call block.
   If an effectful operation appears right of the recursive call, the expression is not eligible for transformation and NONE is returned.
   If multiple recursive calls are found, all but the last are let bound. *)
Definition bvi_to_cb_aux_def:
  (bvi_to_cb_aux _ _ [] = SOME ([],INL [])) ∧
  (bvi_to_cb_aux loc tag [Call t loc' args h] =
   case call_to_cb loc t loc' args h of
   | SOME (bs,cb) => SOME (bs,INR (CallBlock tag [] cb []))
   | _ => NONE) ∧
  (bvi_to_cb_aux loc tag [Op op args] =
   case dest_Cons op of
   | SOME tag' =>
       (* BlockOp Cons - try to recurse *)
       (case bvi_to_cb_aux loc tag' args of
        | NONE => NONE
        | SOME (bs,INL vs) =>
            (* No recursive call - whole thing gets let-bound *)
            if pure_exps [Op op args] then
              SOME ([Op op args],INL [0])
            else NONE
        | SOME (bs,INR cb) =>
            (* Recursive call - inductive case of CallBlock *)
            SOME (bs, INR (CallBlock tag [] cb [])))
   | NONE =>
       (* Not a BlockOp Cons - whole thing gets let-bound *)
       if pure_exps [Op op args] then
         SOME ([Op op args],INL [0])
       else NONE) ∧
  (bvi_to_cb_aux _ _ [exp] =
   (* Some other expression - whole thing gets let-bound *)
   if pure_exps [exp] then
     SOME ([exp],INL [0])
    else NONE) ∧
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
  >> Cases_on ‘arg’ >> gvs [bvi_to_cb_aux_def, bind_def, CaseEq "prod", CaseEq "sum", CaseEq "option"]
QED

Theorem bvi_to_cb_aux_wf:
  ∀loc tag args bs cb.
    bvi_to_cb_aux loc tag args = SOME (bs,INR cb) ⇒
    ∃l child r.
      cb = CallBlock tag l child r
Proof
  recInduct bvi_to_cb_aux_ind
  >> rw [] >> gvs [bvi_to_cb_aux_def, bind_def, shift_cb_def, CaseEq "prod", CaseEq "option", CaseEq "sum", CaseEq "list"]
QED

Definition bvi_to_cb_def:
  (bvi_to_cb loc (Call call_ts call_loc call_args call_h) =
   call_to_cb loc call_ts call_loc call_args call_h) ∧
  (bvi_to_cb loc (Op op xs) =
   case dest_Cons op of
   | SOME tag =>
       (case bvi_to_cb_aux loc tag xs of
        | SOME (bs, INR cb) => SOME (bs,cb)
        | _ => NONE)
   | _ => NONE) ∧
  (bvi_to_cb _ _ = NONE)
End

Theorem bvi_to_cb_wf:
  ∀loc op args bs cb.
    bvi_to_cb loc (Op op args) = SOME (bs,cb) ⇒
    ∃tag l child r.
      op = BlockOp (Cons tag) ∧
      cb = CallBlock tag l child r
Proof
  rw []
  >> gvs [bvi_to_cb_def, CaseEq "option", CaseEq "prod", CaseEq "sum"]
  >> Cases_on ‘op’ >> gvs [dest_Cons_def]
  >> Cases_on ‘b’ >> gvs [dest_Cons_def]
  >> imp_res_tac bvi_to_cb_aux_wf
  >> gvs []
QED

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

Theorem bvi_to_cb_aux_size:
  ∀loc tag args bs sum.
    bvi_to_cb_aux loc tag args = SOME (bs,sum) ⇒
    list_size exp_size bs < exp_size (Op (BlockOp (Cons tag)) args)
Proof
  recInduct bvi_to_cb_aux_ind
  >> rw [] >> gvs [bvi_to_cb_aux_def]
  >- gvs [bvi_to_cb_aux_def, CaseEq "option", CaseEq "prod", call_to_cb_def]
  >-
   (gvs [bvi_to_cb_aux_def, CaseEq "option", CaseEq "prod", CaseEq "sum"]
    >> Cases_on ‘op’ >> gvs [dest_Cons_def]
    >> Cases_on ‘b’ >> gvs [dest_Cons_def, bvi_to_cb_aux_def])
  >> gvs [CaseEq "option", CaseEq "prod", CaseEq "sum"]
  >-
   (gvs [list_size_append]
    >> cheat)
  >> cheat
QED

Theorem bvi_to_cb_size:
  ∀loc x bs cb.
    bvi_to_cb loc x = SOME (bs,cb) ⇒
    list_size exp_size bs < exp_size x
Proof
  rpt gen_tac
  >> strip_tac
  >> Cases_on ‘x’ >> gvs [bvi_to_cb_def]
  >- (gvs [call_to_cb_def, CaseEq "prod"])
  >> gvs [CaseEq "option", dest_Cons_def]
  >> Cases_on ‘o'’ >> gvs [dest_Cons_def]
  >> Cases_on ‘b’ >> gvs [dest_Cons_def]
  >> gvs [CaseEq "prod", CaseEq "sum"]
  >> drule bvi_to_cb_aux_size
  >> strip_tac
  >> gvs []
QED

(* Phase 2 - Transformations. *)

(*
Shift an expression by n if it is a Var.
Subexpressions are not shifted - this simplifies the proofs.
This will only be applied to Vars and Consts.
*)
Definition shallow_shift_def:
  (shallow_shift n (Var i) = Var (i + n)) ∧
  (shallow_shift _ e = e)
End

Definition mut_cons_def:
  mut_cons t l r =
    let l' = MAP (λn. Var n) l in
    let hole' = Op (IntOp (Const 0)) [] in
    let r' = MAP (λn. Var n) r in
    let i = LENGTH r in
    Op (MemOp (MutCons t i)) (l' ++ [hole'] ++ r')
End

Definition finalise_cons_def:
  finalise_cons i_top_ptr = Op (MemOp FinaliseCons) [Var i_top_ptr]
End

Definition fill_hole_def:
  fill_hole i_ptr i_idx exp = Op (MemOp UpdateCons) [exp; Var i_idx; Var i_ptr]
End

Definition optimise_call_def:
  optimise_call call_ts loc_opt call_args exp_ptr exp_idx =
  let args = MAP (λn. Var n) call_args ++ [exp_ptr; exp_idx] in
    Call call_ts (SOME loc_opt) args NONE
End

Definition update_cons_def:
  update_cons exp_ptr exp_idx exp_val = Op (MemOp UpdateCons) [exp_val; exp_idx; exp_ptr]
End

Definition cb_to_bvi_worker_def:
  (cb_to_bvi_worker (RCall call_ts call_args) loc_opt exp_ptr exp_idx =
   optimise_call call_ts loc_opt call_args exp_ptr exp_idx) ∧
  (cb_to_bvi_worker (CallBlock tag left child right) loc_opt exp_ptr exp_idx =
   Let [mut_cons tag left right] $
       Let [update_cons (shallow_shift 1 exp_ptr) (shallow_shift 1 exp_idx) (Var 0)] $
       cb_to_bvi_worker (shift_cb 2 child) loc_opt (Var 1) (Op (IntOp (Const (&LENGTH right))) []))
Termination
  cheat
End

Definition cb_to_bvi_wrapper_def:
  (cb_to_bvi_wrapper tag left child right loc_opt =
   Let [mut_cons tag left right] $
       Let [cb_to_bvi_worker (shift_cb 1 child) loc_opt (Var 0) (Op (IntOp (Const (&LENGTH right))) [])] $
       finalise_cons 1)
End

(* Expression rewriting *)
Definition rewrite_wrapper_def:
  (rewrite_wrapper loc loc_opt (Var n) = NONE) ∧
  (rewrite_wrapper loc loc_opt (If xi xt xe) =
    let opt_t = rewrite_wrapper loc loc_opt xt in
    let opt_e = rewrite_wrapper loc loc_opt xe in
    case (opt_t, opt_e) of
    | (NONE, NONE) => NONE
    | (SOME yt, NONE) => SOME $ If xi yt xe
    | (NONE, SOME ye) => SOME $ If xi xt ye
    | (SOME yt, SOME ye) => SOME $ If xi yt ye) ∧
  (rewrite_wrapper loc loc_opt (Let xs x) =
    case rewrite_wrapper loc loc_opt x of
    | NONE => NONE
    | SOME y => SOME $ Let xs y) ∧
  (rewrite_wrapper loc loc_opt (Raise x) = NONE) ∧
  (rewrite_wrapper loc loc_opt (Tick x) = OPTION_MAP Tick $ rewrite_wrapper loc loc_opt x) ∧
  (rewrite_wrapper loc loc_opt (Force _ n) = NONE) ∧
  (rewrite_wrapper loc loc_opt (Call t d args h) = NONE) ∧
  (rewrite_wrapper loc loc_opt (Op op op_args) =
    case bvi_to_cb loc (Op op op_args) of
    | SOME (bs,CallBlock tag left child right) =>
        SOME $ Let bs $ cb_to_bvi_wrapper tag left child right loc_opt
    | _ => NONE) ∧
  (rewrite_wrapper loc loc_opt _ = NONE)
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
   case bvi_to_cb loc (Op op op_args) of
   | SOME (bs,cb) =>
       (let offset = LENGTH bs in
          Let bs $ cb_to_bvi_worker cb loc_opt (Var (offset + i_old_ptr)) (Var (offset + i_old_idx)))
   | NONE =>
       fill_hole i_old_ptr i_old_idx $ Op op op_args) ∧
  (rewrite_worker loc loc_opt i_old_ptr i_old_idx (Tick x) =
    Tick $ rewrite_worker loc loc_opt i_old_ptr i_old_idx x) ∧
  (rewrite_worker loc loc_opt i_old_ptr i_old_idx (Call ts l args h) =
   (case bvi_to_cb loc (Call ts l args h) of
    | SOME (bs,cb) =>
        (let offset = LENGTH bs in
           Let bs $ cb_to_bvi_worker cb loc_opt (Var (offset + i_old_ptr)) (Var (offset + i_old_idx)))
    | NONE =>
        fill_hole i_old_ptr i_old_idx $ Call ts l args h)) ∧
  (rewrite_worker loc loc_opt i_old_ptr i_old_idx expr =
   fill_hole i_old_ptr i_old_idx expr)
End

Definition compile_exp_def:
  compile_exp (loc:num) (next:num) (arity:num) (exp:bvi$exp) =
    case rewrite_wrapper loc next exp of
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
