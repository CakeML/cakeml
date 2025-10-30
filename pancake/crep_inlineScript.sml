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

(* Whether a program has a return statement inside a loop *)
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

(* Helper function to recursively transform the return statement *)
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

(* This simulate argument loading of a function call *)
Definition arg_load_def:
  arg_load tmp_vars args args_vname p =
    nested_decs tmp_vars args (nested_decs args_vname (MAP Var tmp_vars) p)
End

(* Merge the callee body of a tail call into the caller's body *)
Definition inline_tail_def:
  inline_tail p = Seq Tick p
End

(* Whether a function has return in a branching statement *)
Definition not_branch_ret_def:
  (not_branch_ret (Dec v e p) = not_branch_ret p) ∧
  (not_branch_ret (Seq p1 p2) = (not_branch_ret p1 ∧ not_branch_ret p2)) ∧
  (not_branch_ret (If e p1 p2) = (¬has_return p1 ∧ ¬has_return p2)) ∧
  (not_branch_ret (While e p) = ¬has_return p) ∧
  (not_branch_ret (Call ctyp e args) =
    (case ctyp of
       | NONE => T
       | SOME (_, p, NONE) => not_branch_ret p
       | SOME (_, p, SOME (w, hdl)) => (¬has_return p ∧ ¬has_return hdl))) ∧
  (not_branch_ret _ = T)
End

(* Types of early exit *)
Datatype:
  early_exit = Exn | Ret | Loop_exit
End

(* Eliminate all unreachable code after Return/Raise/Continue/Break
   This treat while loop as a non-stopping statement, as reachability
   of the loop body is not determined
 *)
Definition unreach_elim_def:
  (unreach_elim (Return e) = (Return e, SOME Ret)) ∧
  (unreach_elim (Raise eid) = (Raise eid, SOME Exn)) ∧
  (unreach_elim Break = (Break, SOME Loop_exit)) ∧
  (unreach_elim Continue = (Continue, SOME Loop_exit)) ∧
  (unreach_elim (Seq p1 p2) =
    let (p1', r1) = unreach_elim p1 in
    (if (r1 ≠ NONE) then (p1', r1) else
        let (p2', r2) = unreach_elim p2 in (Seq p1' p2', r2)
    )
  ) ∧
  (unreach_elim (Dec v e p) =
    let (p', r) = unreach_elim p in (Dec v e p', r)) ∧
  (unreach_elim (If e p1 p2) =
    let (p1', r1) = unreach_elim p1;
        (p2', r2) = unreach_elim p2;
        r3 = (case (r1, r2) of
               | (SOME Ret, e) => e
               | (e, SOME Ret) => e
               | (SOME Exn, e) => e
               | (e, SOME Exn) => e
               | (SOME Loop_exit, e) => e
               | (e, SOME Loop_exit) => e
               | (NONE, NONE) => NONE
             ) in
        (If e p1' p2', r3)) ∧
  (unreach_elim (While e p) =
    let (p', r) = unreach_elim p in (While e p', NONE)
  ) ∧
  (unreach_elim (Call ctyp e args) =
    (case ctyp of
      | NONE => (Call NONE e args, SOME Ret)
      | SOME(rt, p, NONE) =>
          let (p', r) = unreach_elim p in (Call (SOME(rt, p', NONE)) e args, r)
      | SOME(rt, p, SOME(w, hdl)) =>
          let (p', rp) = unreach_elim p;
              (hdl', rhdl) = unreach_elim hdl;
              asgn_r = (case (rp, rhdl) of
                         | (SOME Ret, e) => e
                         | (e, SOME Ret) => e
                         | (SOME Exn, e) => e
                         | (e, SOME Exn) => e
                         | (SOME Loop_exit, e) => e
                         | (e, SOME Loop_exit) => e
                         | (NONE, NONE) => NONE
                       ) in
            (Call (SOME(rt, p', SOME(w, hdl'))) e args, asgn_r)
    )
  ) ∧
  (unreach_elim p = (p, NONE))
End

(* Transform the return statements in an inlined standalone call into
   do-nothing statements
 *)
Definition standalone_eoc_def:
  (standalone_eoc (Return e) = Skip) ∧
  (standalone_eoc (Call NONE e args) = Call (SOME(NONE, Skip, NONE)) e args) ∧
  (standalone_eoc p = p)
End

(* Transform the return statements in an inlined assign call into
   assign statements
*)
Definition assign_eoc_def:
  (assign_eoc rt (Return e) = Assign rt e) ∧
  (assign_eoc rt (Call NONE e args) = Call (SOME(SOME rt, Skip, NONE)) e args) ∧
  (assign_eoc rt p = p)
End

(* Merge the callee body of a standalone call into the caller's body *)
Definition inline_standalone_eoc_def:
  inline_standalone_eoc p q =
    Seq (Seq Tick p) q
End

(* Merge the callee body of an assign call into the caller's body *)
Definition inline_assign_eoc_def:
  inline_assign_eoc p q ret_max rt =
    Seq
       (Dec ret_max (Const 0w)
           (Seq
               (Seq Tick p)
               (Assign rt (Var ret_max))
           )
       )
       q
End

(* Perform function inlining over a program's body, with a known inline map.
   This only inlines functions that has Return at the end of control flow,
   and ignores all calls with a handler.
*)
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
          let inlined_callee_unnormalised = inline_prog n_inlineable_fs p in
          let (inlined_callee, exit_type) = unreach_elim inlined_callee_unnormalised in

          let max_args = MAX_LIST (FLAT (MAP var_cexp args)) in
          let max_args_vname = MAX_LIST args_vname in

          (* Avoid shadowing *)
          let tmp_vars = GENLIST (λx. max_args + max_args_vname + SUC x) (LENGTH args_vname) in
          (case ctyp_inl of
             | NONE => inline_tail $ arg_load tmp_vars args args_vname inlined_callee
             | SOME (ret_var, q, hdl) =>
                (case hdl of
                   | NONE =>
                     (case ¬not_branch_ret inlined_callee of
                       | T => (Call ctyp_inl e args)
                       | F =>
                         (case ret_var of
                           | NONE => inline_standalone_eoc (arg_load tmp_vars args args_vname
                                                                        (transform_rec standalone_eoc inlined_callee)) q
                           | SOME rt =>
                             let ret_max = SUC (MAX_LIST [rt; vmax_prog inlined_callee; MAX_LIST tmp_vars; MAX_LIST args_vname]) in
                               inline_assign_eoc (arg_load tmp_vars args args_vname
                                                           (transform_rec (assign_eoc ret_max) inlined_callee)) q ret_max rt
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

Definition compile_inl_prog_def:
  compile_inl_prog inl_fs prog =
      MAP (λ(name, params, body). (name, params, inline_prog (inl_fs \\ name) body)) prog
End

Definition compile_inl_top_def:
  compile_inl_top inl_fname prog =
    let inl_fs_alist = FILTER (λ(x, y). MEM x inl_fname) prog;
        inl_fs = alist_to_fmap inl_fs_alist in
    compile_inl_prog inl_fs prog
End
