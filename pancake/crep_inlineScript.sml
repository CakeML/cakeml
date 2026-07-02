(*
  Function inlining pass in crepLang
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
        | SOME (vs, NONE) => vs
        | SOME (vs, SOME (w, hdl)) => vs ++ var_prog hdl
    in FLAT (MAP var_cexp es) ++ var_ctyp) ∧
  (var_prog (ExtCall f v1 v2 v3 v4) = [v1;v2;v3;v4]) ∧
  (var_prog (Return es) = FLAT (MAP var_cexp es)) ∧
  (var_prog (ShMem mop v e) = [v] ++ var_cexp e) ∧
  (var_prog (Primitive lhss pop rhss) = lhss ++ rhss) ∧
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
      | SOME (_, NONE) => F
      | SOME (_, SOME(w, hdl)) => has_return hdl) ∧
  (has_return (Return e) = T) ∧
  (has_return _ = F)
End

(* This simulate argument loading of a function call *)
Definition arg_load_def:
  arg_load tmp_vars args args_vname p =
    nested_decs tmp_vars args (nested_decs args_vname (MAP Var tmp_vars) p)
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
       | SOME (_, NONE) => T
       | SOME (_, SOME (w, hdl)) => ¬has_return hdl)) ∧
  (not_branch_ret _ = T)
End

(* Types of early exit *)
Datatype:
  early_exit = Exn | Ret | Loop_exit
End

(* Eliminate all unreachable code after Return/Raise/Continue/Break
   This treat while loop as a non-stopping statement, as reachability
   of the loop body is not determined at compile time
 *)
Definition unreach_elim_def:
  (unreach_elim (Return e) = (Return e, SOME Ret)) ∧
  (unreach_elim (Raise eid) = (Raise eid, SOME Exn)) ∧
  (unreach_elim (Break n) = (Break n, SOME Loop_exit)) ∧
  (unreach_elim (Continue n) = (Continue n, SOME Loop_exit)) ∧
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
      | SOME(rt, NONE) => (Call (SOME (rt, NONE)) e args, NONE)
      | SOME(rt, SOME(w, hdl)) =>
          let (hdl', rhdl) = unreach_elim hdl in
            (Call (SOME(rt, SOME(w, hdl'))) e args, NONE)
    )
  ) ∧
  (unreach_elim p = (p, NONE))
End


(*
  Transformation of Return statements
  rets: variables to be returned to at the call site, [] for standalone call
*)

(* Transform the callee's body where Returns are not inside any branching statements *)
Definition transform_eoc_def:
  (transform_eoc rets (Return es) = nested_seq (MAP2 Assign rets es)) ∧
  (transform_eoc rets (Call ctyp e args) =
    case ctyp of
      | NONE => Call (SOME (rets, NONE)) e args
      | SOME (rs, NONE) => Call (SOME (rs, NONE)) e args
      | SOME (rs, SOME (w, hdl)) => Call (SOME (rs, SOME (w, transform_eoc rets hdl))) e args) ∧
  (transform_eoc rets (Dec v e p) = Dec v e (transform_eoc rets p)) ∧
  (transform_eoc rets (While e p) = While e (transform_eoc rets p)) ∧
  (transform_eoc rets (Seq p1 p2) = Seq (transform_eoc rets p1) (transform_eoc rets p2)) ∧
  (transform_eoc rets (If e p1 p2) = If e (transform_eoc rets p1) (transform_eoc rets p2)) ∧
  (transform_eoc rets p = p)
End

(* Transform the callee's body where are Returns inside branching statments (If/While)
   The intention is to wrap a While(true) loop around the callee's body, and turn
   Returns statements into Breaks
 *)
Definition transform_branch_def:
  (transform_branch ld rets (Return es) = Seq (nested_seq (MAP2 Assign rets es)) (Break ld)) ∧
  (transform_branch ld rets (Call ctyp e args) =
    case ctyp of
      | NONE => Seq (Call (SOME (rets, NONE)) e args) (Break ld)
      | SOME (rs, NONE) => Call (SOME (rs, NONE)) e args
      | SOME (rs, SOME (w, hdl)) => Call (SOME (rs, SOME (w, transform_branch ld rets hdl))) e args) ∧
  (transform_branch ld rets (Dec v e p) = Dec v e (transform_branch ld rets p)) ∧
  (transform_branch ld rets (While e p) = While e (transform_branch (ld+1) rets p)) ∧
  (transform_branch ld rets (Seq p1 p2) = Seq (transform_branch ld rets p1) (transform_branch ld rets p2)) ∧
  (transform_branch ld rets (If e p1 p2) = If e (transform_branch ld rets p1) (transform_branch ld rets p2)) ∧
  (transform_branch ld rets p = p)
End

(* Merge the callee body of a tail call into the caller's body, Tick is for clock-correctness *)
Definition inline_tail_def:
  inline_tail p = Seq Tick p
End

(* Inline (transformed) function body where the call site is not a tail call
   - p: the transformed callee's body
   - rts: the variables to be returned to at call site
   - temp_rets: temporary variables to avoid shadowing (rts might be shadowed by a variable inside
              the callee's body
   - tmp_vars: temporary variable to avoid shadowing the function arguments
   - args: expressions to be passed as function arguments
   - args_vname: function arguments original name
 *)
Definition inline_nontail_def:
  inline_nontail p rts temp_rets tmp_vars args args_vname =
    nested_decs temp_rets (REPLICATE (LENGTH temp_rets) (Const 0w))
      (Seq
          (arg_load tmp_vars args args_vname p)
          (nested_seq (MAP2 Assign rts (MAP Var temp_rets)))
      )
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
         | SOME (x, NONE) => (SOME (x, NONE))
         | SOME (x, SOME (w, hdl)) => (SOME (x, SOME (w, inline_prog inlineable_fs hdl)))
      ) in
    (if (case ctyp_inl of NONE => F | SOME (rts, _) => ¬ALL_DISTINCT rts) then Call ctyp_inl e args else (* handling the return vars non distinct case in the semantics *)
    (case FLOOKUP inlineable_fs e of
       | NONE => Call ctyp_inl e args
       | SOME (args_vname, p) =>
          let n_inlineable_fs = inlineable_fs \\ e in
          let inlined_callee_unnormalised = inline_prog n_inlineable_fs p in
          let (inlined_callee, exit_type) = unreach_elim inlined_callee_unnormalised in

          let max_args = MAX_LIST (FLAT (MAP var_cexp args)) in
          let max_args_vname = MAX_LIST args_vname in

          (* Avoid shadowing *)
          let tmp_vars = GENLIST (λx. SUC x + MAX max_args max_args_vname) (LENGTH args_vname) in
          (case ctyp_inl of
             | NONE => inline_tail $ arg_load tmp_vars args args_vname inlined_callee
             | SOME (rts, hdl) =>
                (case hdl of
                   | NONE =>
                     (let ret_max = MAX_LIST [MAX_LIST rts; vmax_prog inlined_callee; MAX_LIST tmp_vars];
                         temp_rets = GENLIST (λx. SUC x + ret_max) (LENGTH rts); (* temporary variables to store to in the callee, avoid shadowing with call site *)
                         n_br = not_branch_ret inlined_callee; (* checks if return statements are inside branching primitives *)
                         transformed_callee = if n_br then (Seq Tick (transform_eoc temp_rets inlined_callee)) else (While (Const 1w) (transform_branch 0 temp_rets inlined_callee)) in
                      inline_nontail transformed_callee rts temp_rets tmp_vars args args_vname)
                   | SOME w_hdl => (Call ctyp_inl e args)
                 )
          )
    ))
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
