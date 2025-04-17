(*
  Various transformations of the Dafny AST.
*)

open preamble
open dafny_astTheory
open mlintTheory

val _ = new_theory "dafny_transform";

(* Transform: Pulls Dafny declarations to the top with unique names. *)

Definition rename_var_exp_def:
  rename_var_exp old new e =
  (case e of
   | Lit l => Lit l
   | Var n => if n = old then Var new else Var n
   | If tst thn els =>
     (let tst = rename_var_exp old new tst;
          thn = rename_var_exp old new thn;
          els = rename_var_exp old new els in
        If tst thn els)
   | UnOp uop e => UnOp uop (rename_var_exp old new e)
   | BinOp bop e₁ e₂ =>
     (let e₁ = rename_var_exp old new e₁;
          e₂ = rename_var_exp old new e₂ in
        BinOp bop e₁ e₂)
   | ArrLen arr => ArrLen (rename_var_exp old new arr)
   | ArrSel arr idx =>
      (let arr = rename_var_exp old new arr;
           idx = rename_var_exp old new idx in
         ArrSel arr idx)
   | FunCall n args => FunCall n (MAP (rename_var_exp old new) args)
   | Forall (vn, vt) e =>
       (* NOTE This could lead to capturing if new = vn *)
       if vn = old then Forall (vn, vt) e
       else Forall (vn, vt) (rename_var_exp old new e))
Termination
  wf_rel_tac ‘measure $ λ(_,_,e). exp_size e’
End

Definition rename_vars_exp_def:
  rename_vars_exp m e =
  (case m of
   | [] => e
   | [(old, new)] => rename_var_exp old new e
   | ((old, new)::rest) =>
       rename_vars_exp rest (rename_var_exp old new e))
End

Definition rename_var_lhs_def:
  rename_var_lhs old new lhs =
  (case lhs of
   | VarLhs n => if n = old then VarLhs new else VarLhs n
   | ArrSelLhs arr idx =>
       ArrSelLhs (rename_var_exp old new arr) (rename_var_exp old new idx))
End

Definition rename_var_rhs_def:
  rename_var_rhs old new rhs =
  (case rhs of
   | ExpRhs e => ExpRhs (rename_var_exp old new e)
   | ArrAlloc len init =>
       ArrAlloc (rename_var_exp old new len) (rename_var_exp old new init))
End

Definition rename_var_stmt_def:
  rename_var_stmt old new stmt =
  (case stmt of
   | Skip => Skip
   | Assert e => Assert (rename_var_exp old new e)
   | Then stmt₁ stmt₂ =>
     (let stmt₁ = rename_var_stmt old new stmt₁;
          stmt₂ = rename_var_stmt old new stmt₂ in
        Then stmt₁ stmt₂)
   | If e stmt₁ stmt₂ =>
     (let e = rename_var_exp old new e;
          stmt₁ = rename_var_stmt old new stmt₁;
          stmt₂ = rename_var_stmt old new stmt₂ in
        If e stmt₁ stmt₂)
   | Dec locals scope =>
     if MEM old (MAP FST locals) then Dec locals scope
     else Dec locals (rename_var_stmt old new scope)
   | Assign lhss rhss =>
     (let lhss = MAP (rename_var_lhs old new) lhss;
          rhss = MAP (rename_var_rhs old new) rhss in
        Assign lhss rhss)
   | While grd invs decrs mods body =>
     (let grd = rename_var_exp old new grd;
          invs = MAP (rename_var_exp old new) invs;
          decrs = MAP (rename_var_exp old new) decrs;
          mods = MAP (rename_var_exp old new) mods;
          body = rename_var_stmt old new body in
        While grd invs decrs mods body)
   | Print ets => Print (MAP (λ(e,t). (rename_var_exp old new e, t)) ets)
   | MetCall lhss n args =>
     (let lhss = MAP (rename_var_lhs old new) lhss;
          args = MAP (rename_var_exp old new) args in
        MetCall lhss n args)
   | Return => Return)
End

(* Sequentially applies the renames in m *)
Definition rename_vars_stmt_def:
  rename_vars_stmt m stmt =
  (case m of
   | [] => stmt
   | [(old, new)] => rename_var_stmt old new stmt
   | ((old, new)::rest) =>
       rename_vars_stmt rest (rename_var_stmt old new stmt))
End

(* Generates fresh variable names *)
(* NOTE If these names are not fresh, we will most likely have some capturing
   going on. However, identifiers in Dafny aren't allowed to start with an
   underscore, so we mainly need to take care that we don't use _v in the
   compiler by accident. *)
Definition fresh_vname_def[simp]:
  fresh_vname idx = «_v» ^ (num_to_str idx)
End

(* Renames variables in expressions to be fresh. *)
Definition fresh_exp_def:
  fresh_exp idx e =
  (case e of
   | Lit l => (idx, Lit l)
   | Var n => (idx, Var n)
   | If e₁ e₂ e₃ =>
     (let
        (idx, e₁) = fresh_exp idx e₁;
        (idx, e₂) = fresh_exp idx e₂;
        (idx, e₃) = fresh_exp idx e₃
      in
        (idx, If e₁ e₂ e₃))
   | UnOp uop e =>
     (let (idx, e) = fresh_exp idx e in
        (idx, UnOp uop e))
   | BinOp bop e₁ e₂ =>
     (let
        (idx, e₁) = fresh_exp idx e₁;
        (idx, e₂) = fresh_exp idx e₂
      in
        (idx, BinOp bop e₁ e₂))
   | ArrLen e =>
     (let (idx, e) = fresh_exp idx e in
        (idx, ArrLen e))
   | ArrSel e₁ e₂ =>
     (let
        (idx, e₁) = fresh_exp idx e₁;
        (idx, e₂) = fresh_exp idx e₂
      in
        (idx, ArrSel e₁ e₂))
   | FunCall n es =>
     (let (idx, es) = map_fresh_exp idx es in
        (idx, FunCall n es))
   | Forall (old, t) e =>
     (let
        new = fresh_vname idx;
        (idx, e) = fresh_exp (idx + 1) e;
        e = rename_var_exp old new e
      in
        (idx, Forall (new, t) e))) ∧
  map_fresh_exp idx es =
  (case es of
   | [] => (idx, [])
   | (e::es) =>
     (let
        (idx, e) = fresh_exp idx e;
        (idx, es) = map_fresh_exp idx es
      in
        (idx, (e::es))))
Termination
  wf_rel_tac ‘measure $ λx. case x of
                            | INL (_,e) => exp_size e
                            | INR (_,es) => exp1_size es’
End

Definition fresh_lhs_exp_def:
  fresh_lhs_exp idx lhs =
  (case lhs of
   | VarLhs n => (idx, VarLhs n)
   | ArrSelLhs e₁ e₂ =>
     (let
        (idx, e₁) = fresh_exp idx e₁;
        (idx, e₂) = fresh_exp idx e₂
      in
        (idx, ArrSelLhs e₁ e₂)))
End

Definition map_fresh_lhs_exp_def:
  map_fresh_lhs_exp idx lhss =
  (case lhss of
   | [] => (idx, [])
   | (lhs::lhss) =>
     (let
        (idx, lhs) = fresh_lhs_exp idx lhs;
        (idx, lhss) = map_fresh_lhs_exp idx lhss
      in
        (idx, (lhs::lhss))))
End

Definition fresh_rhs_exp_def:
  fresh_rhs_exp idx rhs =
  (case rhs of
   | ExpRhs e =>
     (let (idx, e) = fresh_exp idx e in
        (idx, ExpRhs e))
   | ArrAlloc e₁ e₂ =>
     (let
        (idx, e₁) = fresh_exp idx e₁;
        (idx, e₂) = fresh_exp idx e₂
      in
        (idx, ArrAlloc e₁ e₂)))
End

Definition map_fresh_rhs_exp_def:
  map_fresh_rhs_exp idx rhss =
  (case rhss of
   | [] => (idx, [])
   | (rhs::rhss) =>
     (let
        (idx, rhs) = fresh_rhs_exp idx rhs;
        (idx, rhss) = map_fresh_rhs_exp idx rhss
      in
        (idx, (rhs::rhss))))
End

(* Returns a mapping that can be used for renaming a list of locals. *)
Definition rename_locals_def:
  rename_locals idx locals =
  (let
     (old, ts) = UNZIP locals;
     len_locals = LENGTH locals;
     new = GENLIST (λx. fresh_vname (idx + x)) len_locals
   in
     (idx + len_locals, ZIP (new, ts), ZIP (old, new)))
End

(* Renames variables in statements and expressions to be fresh, removing
   declarations in the process. *)
Definition fresh_stmt_def:
  fresh_stmt idx decs stmt =
  (case stmt of
   | Skip => (idx, decs, Skip)
   | Assert e =>
     (let (idx, e) = fresh_exp idx e in
        (idx, decs, Assert e))
   | Then stmt₁ stmt₂ =>
     (let
        (idx, decs, stmt₁) = fresh_stmt idx decs stmt₁;
        (idx, decs, stmt₂) = fresh_stmt idx decs stmt₂
      in
        (idx, decs, Then stmt₁ stmt₂))
   | If e stmt₁ stmt₂ =>
     (let
        (idx, e) = fresh_exp idx e;
        (idx, decs, stmt₁) = fresh_stmt idx decs stmt₁;
        (idx, decs, stmt₂) = fresh_stmt idx decs stmt₂
      in
        (idx, decs, If e stmt₁ stmt₂))
   | Dec locals scope =>
     (let
        (idx, locals, m) = rename_locals idx locals;
        (idx, decs, scope) = fresh_stmt idx (decs ++ locals) scope;
        scope = rename_vars_stmt m scope
      in
        (idx, decs, scope))
   | Assign lhss rhss =>
     (let
        (idx, lhss) = map_fresh_lhs_exp idx lhss;
        (idx, rhss) = map_fresh_rhs_exp idx rhss
      in
        (idx, decs, Assign lhss rhss))
   | While grd invs decrs mods body =>
     (let
        (idx, grd) = fresh_exp idx grd;
        (idx, invs) = map_fresh_exp idx invs;
        (idx, decrs) = map_fresh_exp idx decrs;
        (idx, mods) = map_fresh_exp idx mods;
        (idx, decs, body) = fresh_stmt idx decs body
      in
        (idx, decs, While grd invs decrs mods body))
   | Print ets =>
     (let
        (es, ts) = UNZIP ets;
        (idx, es) = map_fresh_exp idx es;
        ets = ZIP (es, ts)
      in
        (idx, decs, Print ets))
   | MetCall lhss n args =>
     (let
        (idx, lhss) = map_fresh_lhs_exp idx lhss;
        (idx, args) = map_fresh_exp idx args
      in
        (idx, decs, MetCall lhss n args))
   | Return => (idx, decs, Return))
End

Definition fresh_member_def:
  fresh_member member =
  (case member of
   | Method n ins req ens rds decrs outs mods body =>
     (let
        (idx, ins, ins_m) = rename_locals 0 ins;
        (idx, outs, outs_m) = rename_locals idx outs;
        m = ins_m ++ outs_m;
        (* Specifications *)
        (idx, req) = map_fresh_exp idx req;
        req = MAP (rename_vars_exp m) req;
        (idx, ens) = map_fresh_exp idx ens;
        ens = MAP (rename_vars_exp m) ens;
        (idx, rds) = map_fresh_exp idx rds;
        rds = MAP (rename_vars_exp m) rds;
        (idx, decrs) = map_fresh_exp idx decrs;
        decrs = MAP (rename_vars_exp m) decrs;
        (idx, mods) = map_fresh_exp idx mods;
        mods = MAP (rename_vars_exp m) mods;
        (* Body *)
        (idx, decs, body) = fresh_stmt idx [] body;
        body = rename_vars_stmt m (Dec decs body)
      in
        Method n ins req ens rds decrs outs mods body)
   | Function n ins res_t req rds decrs body =>
     (let
        (idx, ins, m) = rename_locals 0 ins;
        (idx, req) = map_fresh_exp idx req;
        req = MAP (rename_vars_exp m) req;
        (idx, rds) = map_fresh_exp idx rds;
        rds = MAP (rename_vars_exp m) rds;
        (idx, decrs) = map_fresh_exp idx decrs;
        decrs = MAP (rename_vars_exp m) decrs;
        (idx, body) = fresh_exp idx body;
        body = rename_vars_exp m body;
      in
        Function n ins res_t req rds decrs body))
End

Definition use_fresh_vars_def:
  use_fresh_vars (Program members) = Program (MAP fresh_member members)
End

(* --- *)

val _ = export_theory ();
