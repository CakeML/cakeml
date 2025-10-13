(*
  Function inlining
*)
Theory crep_inline
Ancestors
  crepLang
Libs
  preamble

(* Counting all the variables that appears in a prog *)
Definition var_prog_def:
  (var_prog (Dec v e p) = [v] ++ var_cexp e ++ var_prog p) ∧
  (var_prog (Assign v e) = [v] ++ var_cexp e) ∧
  (var_prog (Store e1 e2) = var_cexp e1 ++ var_cexp e2) ∧
  (var_prog (Store32 e1 e2) = var_cexp e1 ++ var_cexp e2) ∧
  (var_prog (StoreByte e1 e2) = var_cexp e1 ++ var_cexp e2) ∧
  (var_prog (StoreGlob w e) = var_cexp e) ∧
  (var_prog (Seq p1 p2) = var_prog p1 ++ var_prog p2) ∧
  (var_prog (If e p1 p2) = var_cexp e ++ var_prog p1 ++ var_prog p2) ∧
  (var_prog (While e p) = var_cexp e ++ var_prog p) ∧
  (var_prog (Call ctyp e es) =
    let var_ctyp =
      case ctyp of
        | NONE => []
        | SOME (NONE, p, NONE) => var_prog p
        | SOME (SOME v, p, NONE) => [v] ++ var_prog p
        | SOME (NONE, p, SOME (w, hdl)) => var_prog p ++ var_prog hdl
        | SOME (SOME v, p, SOME (w, hdl)) => [v] ++ var_prog p ++ var_prog hdl
    in FLAT (MAP var_cexp es) ++ var_ctyp) ∧
  (var_prog (ExtCall f v1 v2 v3 v4) = [v1;v2;v3;v4]) ∧
  (var_prog (Return e) = var_cexp e) ∧
  (var_prog (ShMem mop v e) = [v] ++ var_cexp e) ∧
  (var_prog _ = [])
End

(* Largest variable of a prog *)
Definition vmax_prog_def:
  vmax_prog p = MAX_LIST (var_prog p)
End

(* Check if a prog has a return statement or a tail call *)
Definition has_return_def:
  (has_return (Dec v e p) = has_return p) ∧
  (has_return (Seq p1 p2) = ((has_return p1) ∨ (has_return p2))) ∧
  (has_return (If e p1 p2) = ((has_return p1) ∨ (has_return p2))) ∧
  (has_return (While e p) = has_return p) ∧
  (has_return (Call ctyp e args) =
    case ctyp of
      | NONE => T
      | SOME (_, p, NONE) => has_return p
      | SOME (_, p, SOME(w, hdl)) => (has_return p ∨ has_return hdl)) ∧
  (has_return (Return e) = T) ∧
  (has_return _ = F)
End


Definition return_in_loop_def:
  (return_in_loop (Dec v e p) = return_in_loop p) ∧
  (return_in_loop (Seq p1 p2) = ((return_in_loop p1) ∨ (return_in_loop p2))) ∧
  (return_in_loop (If e p1 p2) = ((return_in_loop p1) ∨ (return_in_loop p2))) ∧
  (return_in_loop (While e p) = has_return p) ∧
  (return_in_loop (Call ctyp e args) =
    case ctyp of
      | NONE => F
      | SOME (_, p, NONE) => return_in_loop p
      | SOME (_, p, SOME(w, hdl)) => (return_in_loop p) ∨ (return_in_loop hdl)) ∧
  (return_in_loop _ = F)
End

(* No transformation for
   While: uninlineable
 *)
Definition transform_rec_def:
  (transform_rec f (Return e) = f (Return e)) ∧
  (transform_rec f (Dec v e p) = Dec v e (transform_rec f p)) ∧
  (transform_rec f (Seq p1 p2) = Seq (transform_rec f p1) (transform_rec f p2)) ∧
  (transform_rec f (If e p1 p2) = If e (transform_rec f p1) (transform_rec f p2)) ∧
  (transform_rec f (Call ctyp e args) =
    case ctyp of
      | NONE => f (Call NONE e args)
      | SOME(v, p, NONE) => (Call (SOME (v, transform_rec f p, NONE)) e args)
      | SOME(v, p, SOME(w, hdl)) =>
          (Call (SOME (v, transform_rec f p, SOME(w, transform_rec f hdl))) e args)) ∧
  (transform_rec f p = f p)
End


(* Every return in a standalone call doesn't actually return anything, just signalling an end-of-control *)
Definition standalone_ret_def:
  (standalone_ret (Return e) = Break) ∧
  (standalone_ret (Call NONE e args) = Seq (Call (SOME(NONE, Skip, NONE)) e args) Break) ∧
  (standalone_ret p = p)
End

(* This is for assign call, change all returns/tailcalls into assignments/assigncalls + break *)
Definition assign_ret_def:
  (assign_ret rvar (Return e) = Seq (Assign rvar e) Break) ∧
  (assign_ret rvar (Call NONE e args) = Seq (Call (SOME(SOME rvar, Skip, NONE)) e args) Break) ∧
  (assign_ret rvar p = p)
End


(* Wrap the code for the callee inside a while loop *)
Definition transform_standalone_def:
  transform_standalone prog = transform_rec standalone_ret prog
End

Definition transform_assign_def:
  transform_assign rvar prog = transform_rec (assign_ret rvar) prog
End


Definition arg_load_def:
  arg_load tmp_vars args args_vname p =
    nested_decs tmp_vars args (nested_decs args_vname (MAP Var tmp_vars) p)
End

Definition inline_tail:
  inline_tail p = Seq Tick p
End

Definition inline_standalone:
  inline_standalone p q =
    Seq
       (While (Const 1w) p)
       q
End

Definition inline_assign:
  inline_assign p q ret_max rt =
    Seq
       (Dec ret_max (Const 0w)
           (Seq
               (While (Const 1w) p)
               (Assign rt (Var ret_max))
           )
       )
       q
End

Definition inline_prog_def:
  (inline_prog inlineable_fs (Call ctyp e args) =
     let ctyp_inl =
      (case ctyp of
         | NONE => NONE
         | SOME (x, p, NONE) => SOME (x, inline_prog inlineable_fs p, NONE)
         | SOME (x, p, SOME (w, hdl)) => SOME (x, inline_prog inlineable_fs p, SOME (w, inline_prog inlineable_fs hdl))
      ) in
    (case FLOOKUP inlineable_fs e of
       | NONE => Call ctyp_inl e args
       | SOME (args_vname, p) =>
          let n_inlineable_fs = inlineable_fs \\ e in
          let inlined_callee = inline_prog n_inlineable_fs p in

          let max_args = MAX_LIST (FLAT (MAP var_cexp args)) in
          let max_args_vname = MAX_LIST args_vname in
          let tmp_vars = GENLIST (λx. max_args + max_args_vname + SUC x) (LENGTH args_vname) in
          (case ctyp_inl of
             | NONE => inline_tail $ arg_load tmp_vars args args_vname inlined_callee
             | SOME (ret_var, q, hdl) =>
                (case hdl of
                   | NONE =>
                      (case return_in_loop inlined_callee of
                         | T => (Call ctyp_inl e args)
                         | F =>
                             (case ret_var of
                                | NONE =>
                                    inline_standalone (arg_load tmp_vars args args_vname
                                                                (transform_rec standalone_ret inlined_callee)) q
                                | SOME rt =>
                                    let vmax_callee_body = vmax_prog inlined_callee in
                                    let max_tmp_vars = MAX_LIST tmp_vars in
                                    let max_clash = MAX_LIST [rt; vmax_callee_body; max_tmp_vars; max_args_vname] in
                                    let ret_max = SUC max_clash in
                                        inline_assign (arg_load tmp_vars args args_vname
                                                                (transform_rec (assign_ret ret_max) inlined_callee)) q ret_max rt
                              )
                      )
                   | SOME w_hdl => (Call ctyp_inl e args)
                 )
          )
    )
  ) ∧
  (inline_prog inlineable_fs (Dec v e p) = Dec v e (inline_prog inlineable_fs p)) ∧
  (inline_prog inlineable_fs (Seq p1 p2) =
    let inline_p1 = inline_prog inlineable_fs p1 in
    let inline_p2 = inline_prog inlineable_fs p2 in
      Seq inline_p1 inline_p2) ∧
  (inline_prog inlineable_fs (If e p1 p2) =
    let inline_p1 = inline_prog inlineable_fs p1 in
    let inline_p2 = inline_prog inlineable_fs p2 in
      If e inline_p1 inline_p2) ∧
  (inline_prog inlineable_fs (While e p) = While e (inline_prog inlineable_fs p)) ∧
  (inline_prog inlineable_fs p = p)
Termination
  wf_rel_tac `inv_image (measure I LEX measure (prog_size ARB)) (λ(x, y). (CARD (FDOM x), y))` >>
  rpt strip_tac >>
  disj1_tac >>
  gs[DRESTRICT_DEF, FLOOKUP_DEF] >>
  spose_not_then assume_tac >>
  gs[NOT_ZERO, FDOM_FINITE, CARD_EQ_0, IN_DEF]
End

(* Convert a list of functions into a finite map *)
Definition inlineable_funcs_def:
  inlineable_funcs prog =
    let prog_f = FILTER (λ(n, i, p, b). i) prog in
    let fnames = MAP FST prog_f;
        param_body = MAP (SND o SND) prog_f;
        fs = MAP2 (λx y. (x, y)) fnames param_body in
    alist_to_fmap fs
End
