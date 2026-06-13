(*
  Perform tailrec modulo cons optimisation to make more functions tail-recursive.
*)
Theory bvi_tmc
Ancestors
  bvi backend_common integer
Libs
  preamble

Definition pure_op_def:
  (pure_op (Label _) _ = F) ∧
  (pure_op (FFI _) _ = F) ∧
  (pure_op (IntOp (Const n)) [] = small_enough_int n) ∧
  (pure_op (IntOp _) _ = F) ∧
  (pure_op (WordOp _) _ = F) ∧
  (pure_op (BlockOp (Cons _)) _ = T) ∧
  (pure_op (BlockOp _) _ = F) ∧
  (pure_op (GlobOp _) _ = F) ∧
  (pure_op (MemOp _) _ = F) ∧
  (pure_op Install _ = F) ∧
  (pure_op (ThunkOp _) _ = F)
End

Definition pure_exps_def:
  (pure_exps n [] = T) ∧
  (pure_exps n [Var v] = (v < n)) ∧
  (pure_exps n [If e1 e2 e3] = F) ∧
  (pure_exps n [Let es e] = (pure_exps n [e] ∧ pure_exps n es)) ∧
  (pure_exps n [Raise _] = F) ∧
  (pure_exps n [Tick e] = F) ∧
  (pure_exps n [Call _ _ _ _] = F) ∧
  (pure_exps n [Force _ _] = F) ∧
  (pure_exps n [Op op args] = (pure_op op args ∧ pure_exps n args)) ∧
  (pure_exps n (h1::h2::t) = (pure_exps n [h1] ∧ pure_exps n (h2::t)))
End

Theorem pure_exps_cons:
  ∀n h t.
    pure_exps n [h] ∧
    pure_exps n t ⇔
    pure_exps n (h::t)
Proof
  Induct_on ‘t’ >> rw [pure_exps_def]
QED

Theorem pure_exps_append:
  ∀n es1 es2.
    pure_exps n es1 ∧
    pure_exps n es2 ⇒
    pure_exps n (es1 ++ es2)
Proof
  Induct_on ‘es1’
  >- gvs [pure_exps_def]
  >> rw []
  >> irule $ iffLR pure_exps_cons
  >> imp_res_tac pure_exps_cons
  >> last_x_assum drule
  >> disch_then $ qspec_then ‘es2’ assume_tac
  >> gvs []
QED

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

Theorem shift_vars_zero:
  ∀ns.
    shift_vars 0 ns = ns
Proof
  Induct
  >- gvs [shift_vars_def]
  >> rw []
  >> gvs [shift_vars_def]
QED

Theorem length_shift_vars:
  ∀l n.
     LENGTH (shift_vars n l) = LENGTH l
Proof
  Induct
  >- gvs [shift_vars_def]
  >> rw []
  >> gvs [shift_vars_def]
QED

Theorem shift_vars_dist:
  ∀l n1 n2.
    shift_vars n1 (shift_vars n2 l) = shift_vars (n1 + n2) l
Proof
  Induct
  >- rw [shift_vars_def]
  >> rw [shift_vars_def]
QED

Theorem shift_cb_dist:
  ∀cb n1 n2.
    shift_cb n1 (shift_cb n2 cb) =
    shift_cb (n1 + n2) cb
Proof
  reverse Induct
  >-
   (rw []
    >> gvs [shift_cb_def]
    >> irule shift_vars_dist)
  >> rw []
  >> gvs [shift_cb_def]
  >> rpt $ irule_at Any shift_vars_dist
QED

(* Attempts to build a CallBlock from the tag and args of a BlockOp Cons.
   If no recursive call found, returns each op arg expression in a list and (INL) a list of corresponding de Bruijn indeces.
   If a recursive call is found, returns all extracted/let-bound expressions and (INR) the call block.
   If an effectful operation appears right of the recursive call, the expression is not eligible for transformation and NONE is returned.
   If multiple recursive calls are found, all but the last are let bound. *)
Definition bvi_to_cb_aux_def:
  (bvi_to_cb_aux _ _ _ [] = SOME ([],INL [])) ∧
  (bvi_to_cb_aux _ loc tag [Call t loc' args h] =
   case call_to_cb loc t loc' args h of
   | SOME (bs,cb) => SOME (bs,INR (CallBlock tag [] cb []))
   | _ => NONE) ∧
  (bvi_to_cb_aux n loc tag [Op op args] =
   case dest_Cons op of
   | SOME tag' =>
       (* BlockOp Cons - try to recurse *)
       (case bvi_to_cb_aux n loc tag' args of
        | NONE => NONE
        | SOME (bs,INL vs) =>
            (* No recursive call - whole thing gets let-bound *)
            if pure_exps n [Op op args] then
              SOME ([Op op args],INL [0])
            else NONE
        | SOME (bs,INR cb) =>
            (* Recursive call - inductive case of CallBlock *)
            SOME (bs, INR (CallBlock tag [] cb [])))
   | NONE =>
       (* Not a BlockOp Cons - whole thing gets let-bound *)
       if pure_exps n [Op op args] then
         SOME ([Op op args],INL [0])
       else NONE) ∧
  (bvi_to_cb_aux n _ _ [exp] =
   (* Some other expression - whole thing gets let-bound *)
   if pure_exps n [exp] then
     SOME ([exp],INL [0])
    else NONE) ∧
  (bvi_to_cb_aux n loc tag (h::t) =
   (* Recurse right to left to find last occurence of recursive call *)
   case bvi_to_cb_aux n loc tag t of
   | NONE => NONE
   | SOME (bs2,INL vs2) =>
       (* No recursive call to the right. See if the first has one. *)
       (case bvi_to_cb_aux n loc tag [h] of
        | NONE => NONE
        | SOME (bs1,INL vs1) =>
            (* No recursive call, keep building binders. *)
            if small_enough_int &(LENGTH vs1 + LENGTH vs2) then
              let vs2' = shift_vars (LENGTH bs1) vs2 in
                SOME (bs1 ++ bs2,INL (vs1 ++ vs2'))
            else NONE
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

Definition wf_vars_def:
  wf_vars n (vs : num list) ⇔ EVERY (λv. v < n) vs
End

Theorem wf_vars_empty:
  ∀n.
    wf_vars n []
Proof
  rw [wf_vars_def]
QED

Theorem wf_vars_shift:
  ∀n1 n2 vs.
    wf_vars n1 vs ⇒
    wf_vars (n2 + n1) (shift_vars n2 vs)
Proof
  Induct_on ‘vs’
  >> rw []
  >- gvs [wf_vars_def, shift_vars_def]
  >> gvs [wf_vars_def, shift_vars_def]
QED

Theorem wf_vars_shift_sing:
  ∀n vs.
    wf_vars n vs ⇒
    wf_vars (SUC n) (shift_vars 1 vs)
Proof
  rw []
  >> drule wf_vars_shift
  >> disch_then $ qspec_then ‘1’ assume_tac
  >> gvs []
  >> ‘SUC n = n + 1’ by gvs []
  >> simp []
QED

Theorem wf_vars_append:
  ∀n vs1 vs2.
    wf_vars n vs1 ∧
    wf_vars n vs2 ⇒
    wf_vars n (vs1 ++ vs2)
Proof
  Induct_on ‘vs1’
  >- rw []
  >> rw []
  >> gvs [wf_vars_def]
QED

Theorem wf_vars_cons:
  ∀n v vs.
    v < n ∧
    wf_vars n vs ⇒
    wf_vars n (v::vs)
Proof
  rw []
  >> ‘wf_vars n [v]’ by gvs [wf_vars_def]
  >> drule_then rev_drule wf_vars_append
  >> strip_tac
  >> gvs []
QED

Theorem wf_vars_bind:
  ∀bs vs n n'.
    bind n bs = (vs,n') ⇒
    wf_vars (n + LENGTH bs) vs
Proof
  Induct
  >- rw [bind_def, wf_vars_def]
  >> rw []
  >> gvs [bind_def, CaseEq "prod"]
  >> first_x_assum drule
  >> strip_tac
  >> irule wf_vars_cons
  >> gvs []
  >> ‘SUC (LENGTH bs) = LENGTH bs + 1’ by gvs []
  >> simp []
QED

Theorem bvi_to_cb_aux_wf_inl:
  ∀n loc tag args bs vs.
    bvi_to_cb_aux n loc tag args = SOME (bs,INL vs) ⇒
    pure_exps n bs ∧
    wf_vars (LENGTH bs) vs ∧
    small_enough_int (&LENGTH vs)
Proof
  recInduct bvi_to_cb_aux_ind
  >> rw [] >> gvs [bvi_to_cb_aux_def, pure_exps_def, CaseEq "call_block", CaseEq "prod", CaseEq "option", CaseEq "sum", CaseEq "list", small_enough_int_def, length_shift_vars]
  >- gvs [wf_vars_def]
  >- gvs [wf_vars_def]
  >- gvs [wf_vars_def]
  >- gvs [wf_vars_def]
  >- gvs [wf_vars_def]
  >- (irule pure_exps_append >> gvs [])
  >> irule wf_vars_append
  >> conj_tac
  >-
   (gvs [wf_vars_def]
    >> gvs [EVERY_EL]
    >> rw []
    >> rpt (first_x_assum drule >> strip_tac)
    >> gvs [])
  >> irule wf_vars_shift
  >> gvs []
QED

Theorem bvi_to_cb_aux_sing:
  ∀n loc tag arg bs cb.
    bvi_to_cb_aux n loc tag [arg] = SOME (bs,INR cb) ⇒
    ∃child.
      cb = CallBlock tag [] child []
Proof
  rw []
  >> Cases_on ‘arg’ >> gvs [bvi_to_cb_aux_def, bind_def, CaseEq "prod", CaseEq "sum", CaseEq "option"]
QED

Theorem bvi_to_cb_aux_wf_inr:
  ∀n loc tag args bs cb.
    bvi_to_cb_aux n loc tag args = SOME (bs,INR cb) ⇒
    ∃l child r.
      cb = CallBlock tag l child r ∧
      wf_vars (LENGTH bs) l ∧
      small_enough_int (&LENGTH r) ∧
      wf_vars (LENGTH bs) r
Proof
  recInduct bvi_to_cb_aux_ind
  >> rw [] >> gvs [bvi_to_cb_aux_def, bind_def, shift_cb_def, CaseEq "prod", CaseEq "option", CaseEq "sum", CaseEq "list", wf_vars_empty, wf_vars_shift_sing, small_enough_int_def, length_shift_vars, GSYM INT]
  >-
   (irule_at Any wf_vars_shift
    >> imp_res_tac bvi_to_cb_aux_wf_inl
    >> gvs [small_enough_int_def])
  >> irule wf_vars_cons
  >> gvs []
  >> irule wf_vars_shift_sing
  >> gvs []
QED

Definition bvi_to_cb_def:
  (bvi_to_cb n loc (Call call_ts call_loc call_args call_h) =
   call_to_cb loc call_ts call_loc call_args call_h) ∧
  (bvi_to_cb n loc (Op op xs) =
   case dest_Cons op of
   | SOME tag =>
       (case bvi_to_cb_aux n loc tag xs of
        | SOME (bs, INR cb) => SOME (bs,cb)
        | _ => NONE)
   | _ => NONE) ∧
  (bvi_to_cb _ _ _ = NONE)
End

Theorem bvi_to_cb_cases:
  ∀n loc x bs cb.
    bvi_to_cb n loc x = SOME (bs,cb) ⇒
    (∃tag args l child r.
       x = Op (BlockOp (Cons tag)) args ∧
       cb = CallBlock tag l child r ∧
       wf_vars (LENGTH bs) l ∧
       small_enough_int (&LENGTH r) ∧
       wf_vars (LENGTH bs) r) ∨
    (∃ts args vs.
       x = Call ts (SOME loc) args NONE ∧
       cb = RCall ts vs ∧
       wf_vars (LENGTH bs) vs)
Proof
  rw []
  >> Cases_on ‘cb’
  >-
   (Cases_on ‘x’ >> gvs [bvi_to_cb_def, call_to_cb_def, CaseEq "option", CaseEq "prod", CaseEq "sum"]
    >> Cases_on ‘o'’ >> gvs [dest_Cons_def]
    >> Cases_on ‘b’ >> gvs [dest_Cons_def]
    >> imp_res_tac bvi_to_cb_aux_wf_inr
    >> gvs [])
  >> Cases_on ‘x’ >> gvs [bvi_to_cb_def, call_to_cb_def, CaseEq "option", CaseEq "prod", CaseEq "sum"]
  >> imp_res_tac bvi_to_cb_aux_wf_inr
  >> gvs []
  >> drule wf_vars_bind
  >> strip_tac
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
  ∀n loc tag args bs sum.
    bvi_to_cb_aux n loc tag args = SOME (bs,sum) ⇒
    list_size exp_size bs ≤ list_size exp_size args
Proof
  recInduct bvi_to_cb_aux_ind
  >> rw [] >> gvs [bvi_to_cb_aux_def]
  >- gvs [bvi_to_cb_aux_def, CaseEq "option", CaseEq "prod", call_to_cb_def]
  >-
   (gvs [bvi_to_cb_aux_def, CaseEq "option", CaseEq "prod", CaseEq "sum"]
    >> Cases_on ‘op’ >> gvs [dest_Cons_def]
    >> Cases_on ‘b’ >> gvs [dest_Cons_def, bvi_to_cb_aux_def])
  >> gvs [CaseEq "option", CaseEq "prod", CaseEq "sum"]
  >> gvs [list_size_append, AllCaseEqs()]
QED

Theorem bvi_to_cb_size:
  ∀n loc x bs cb.
    bvi_to_cb n loc x = SOME (bs,cb) ⇒
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

Definition cb_size_def:
  cb_size (CallBlock _ _ x _) = cb_size x + 1 ∧
  cb_size _ = 0n
End

Theorem call_block_size_shift[local]:
  ∀x n. cb_size (shift_cb n x) = cb_size x
Proof
  Induct \\ fs [cb_size_def, shift_cb_def]
QED

Definition cb_to_bvi_worker_aux_def:
  (cb_to_bvi_worker_aux (RCall call_ts call_args) loc_opt ptr idx =
   optimise_call call_ts loc_opt call_args (Var ptr) (Op (IntOp (Const &idx)) [])) ∧
  (cb_to_bvi_worker_aux (CallBlock tag left child right) loc_opt ptr idx =
   Let [mut_cons tag left right] $
   Let [update_cons (Var (ptr + 1)) (Op (IntOp (Const &idx)) []) (Var 0)] $
     cb_to_bvi_worker_aux (shift_cb 2 child) loc_opt 1 (LENGTH right))
Termination
  WF_REL_TAC ‘measure $ cb_size o FST’
  \\ rw [call_block_size_shift, cb_size_def]
End

Definition cb_to_bvi_worker_def:
  (cb_to_bvi_worker (RCall call_ts call_args) loc_opt ptr idx =
   optimise_call call_ts loc_opt call_args (Var ptr) (Var idx)) ∧
  (cb_to_bvi_worker (CallBlock tag left child right) loc_opt ptr idx =
   Let [mut_cons tag left right] $
       Let [update_cons (Var (ptr + 1)) (Var (idx + 1)) (Var 0)] $
       cb_to_bvi_worker_aux (shift_cb 2 child) loc_opt 1 (LENGTH right))
End

Definition cb_to_bvi_wrapper_def:
  (cb_to_bvi_wrapper tag left child right loc_opt =
   Let [mut_cons tag left right] $
       Let [cb_to_bvi_worker_aux (shift_cb 1 child) loc_opt 0 (LENGTH right)] $
       finalise_cons 1)
End

(* Expression rewriting *)
Definition rewrite_wrapper_def:
  (rewrite_wrapper loc loc_opt _ (Var n) = NONE) ∧
  (rewrite_wrapper loc loc_opt n (If xi xt xe) =
    let opt_t = rewrite_wrapper loc loc_opt n xt in
    let opt_e = rewrite_wrapper loc loc_opt n xe in
    case (opt_t, opt_e) of
    | (NONE, NONE) => NONE
    | (SOME yt, NONE) => SOME $ If xi yt xe
    | (NONE, SOME ye) => SOME $ If xi xt ye
    | (SOME yt, SOME ye) => SOME $ If xi yt ye) ∧
  (rewrite_wrapper loc loc_opt n (Let xs x) =
    case rewrite_wrapper loc loc_opt (n + LENGTH xs) x of
    | NONE => NONE
    | SOME y => SOME $ Let xs y) ∧
  (rewrite_wrapper loc loc_opt _ (Raise x) = NONE) ∧
  (rewrite_wrapper loc loc_opt n (Tick x) = OPTION_MAP Tick $ rewrite_wrapper loc loc_opt n x) ∧
  (rewrite_wrapper loc loc_opt _ (Force _ n) = NONE) ∧
  (rewrite_wrapper loc loc_opt _ (Call t d args h) = NONE) ∧
  (rewrite_wrapper loc loc_opt n (Op op op_args) =
    case bvi_to_cb n loc (Op op op_args) of
    | SOME (bs,CallBlock tag left child right) =>
        SOME $ Let bs $ cb_to_bvi_wrapper tag left child right loc_opt
    | _ => NONE) ∧
  (rewrite_wrapper loc loc_opt _ _ = NONE)
End

(* Assumes that the function can and should be optimised - has been checked by rewrite_wrapper. *)
Definition rewrite_worker_def:
  (rewrite_worker loc loc_opt i_old_ptr i_old_idx n (If xi xt xe) =
    let yt = rewrite_worker loc loc_opt i_old_ptr i_old_idx n xt in
    let ye = rewrite_worker loc loc_opt i_old_ptr i_old_idx n xe in
    If xi yt ye) ∧
  (rewrite_worker loc loc_opt i_old_ptr i_old_idx n (Let xs x) =
    let offset = LENGTH xs in
      Let xs $ rewrite_worker loc loc_opt (i_old_ptr + offset) (i_old_idx + offset) (n + offset) x) ∧
  (rewrite_worker loc loc_opt i_old_ptr i_old_idx _ (Raise x) = Raise x) ∧
  (rewrite_worker loc loc_opt i_old_ptr i_old_idx n (Op op op_args) =
   case bvi_to_cb n loc (Op op op_args) of
   | SOME (bs,cb) =>
       (let offset = LENGTH bs in
          Let bs $ cb_to_bvi_worker cb loc_opt (offset + i_old_ptr) (offset + i_old_idx))
   | NONE =>
       fill_hole i_old_ptr i_old_idx $ Op op op_args) ∧
  (rewrite_worker loc loc_opt i_old_ptr i_old_idx n (Tick x) =
    Tick $ rewrite_worker loc loc_opt i_old_ptr i_old_idx n x) ∧
  (rewrite_worker loc loc_opt i_old_ptr i_old_idx n (Call ts l args h) =
   (case bvi_to_cb n loc (Call ts l args h) of
    | SOME (bs,cb) =>
        (let offset = LENGTH bs in
           Let bs $ cb_to_bvi_worker cb loc_opt (offset + i_old_ptr) (offset + i_old_idx))
    | NONE =>
        fill_hole i_old_ptr i_old_idx $ Call ts l args h)) ∧
  (rewrite_worker loc loc_opt i_old_ptr i_old_idx _ expr =
   fill_hole i_old_ptr i_old_idx expr)
End

Definition compile_exp_def:
  compile_exp (loc:num) (next:num) (arity:num) (exp:bvi$exp) =
    case rewrite_wrapper loc next arity exp of
    | NONE => NONE
    | SOME exp_wrapper =>
      let exp_worker = rewrite_worker loc next arity (arity + 1) arity exp in
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
