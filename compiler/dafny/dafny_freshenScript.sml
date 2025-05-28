(*
  Implements the freshen pass, where names are updated to be unique.
*)

open preamble
open dafny_astTheory
open mlstringTheory
open mlintTheory

val _ = new_theory "dafny_freshen";

Definition lookup_def:
  lookup m old =
  case ALOOKUP m old of
  | NONE => «»
  | SOME cnt => «v» ^ num_to_str cnt
End

Definition add_fresh_def:
  add_fresh m (cnt: num) old = (cnt + 1, (old, cnt)::m)
End

Definition freshen_exp_def:
  freshen_exp m cnt (Lit l) = (cnt, Lit l) ∧
  freshen_exp m cnt (Var old) = (cnt, Var (lookup m old)) ∧
  freshen_exp m cnt (If tst thn els) =
    (let
       (cnt, tst) = freshen_exp m cnt tst;
       (cnt, thn) = freshen_exp m cnt thn;
       (cnt, els) = freshen_exp m cnt els
     in
       (cnt, If tst thn els)) ∧
  freshen_exp m cnt (UnOp uop e) =
    (let (cnt, e) = freshen_exp m cnt e in
       (cnt, UnOp uop e)) ∧
  freshen_exp m cnt (BinOp bop e₁ e₂) =
    (let (cnt, e₁) = freshen_exp m cnt e₁ in
     let (cnt, e₂) = freshen_exp m cnt e₂ in
       (cnt, BinOp bop e₁ e₂)) ∧
  freshen_exp m cnt (ArrLen arr) =
    (let
       (cnt, arr) = freshen_exp m cnt arr
     in
       (cnt, ArrLen arr)) ∧
  freshen_exp m cnt (ArrSel arr idx) =
    (let
       (cnt, arr) = freshen_exp m cnt arr;
       (cnt, idx) = freshen_exp m cnt idx
     in
       (cnt, ArrSel arr idx)) ∧
  freshen_exp m cnt (FunCall n args) =
    (let
       (cnt, args) = freshen_exps m cnt args
     in
       (cnt, FunCall n args)) ∧
  freshen_exp m cnt (Forall (old, vt) e) =
    (let
       (cnt, m) = add_fresh m cnt old;
       (cnt, e) = freshen_exp m cnt e
     in
       (cnt, Forall (lookup m old, vt) e)) ∧
  freshen_exps m cnt [] = (cnt, []) ∧
  freshen_exps m cnt (e::es) =
    (let
       (cnt, e) = freshen_exp m cnt e;
       (cnt, es) = freshen_exps m cnt es
     in
       (cnt, (e::es)))
Termination
  wf_rel_tac ‘measure $ λx. case x of
                            | INL (_,_,e) => exp_size e
                            | INR (_,_,e) => exp1_size e’
End

Definition freshen_lhs_exp_def:
  (freshen_lhs_exp m cnt (VarLhs old) =
     (cnt, VarLhs (lookup m old))) ∧
  freshen_lhs_exp m cnt (ArrSelLhs arr idx) =
  let (cnt, arr) = freshen_exp m cnt arr in
  let (cnt, idx) = freshen_exp m cnt idx in
    (cnt, ArrSelLhs arr idx)
End

Definition freshen_lhs_exps_def:
  (freshen_lhs_exps m cnt [] = (cnt, [])) ∧
  freshen_lhs_exps m cnt (le::les) =
  let (cnt, le) = freshen_lhs_exp m cnt le in
  let (cnt, les) = freshen_lhs_exps m cnt les in
    (cnt, le::les)
End

Definition freshen_rhs_exp_def:
  (freshen_rhs_exp m cnt (ExpRhs e) =
   let (cnt, e) = freshen_exp m cnt e in
     (cnt, ExpRhs e)) ∧
  freshen_rhs_exp m cnt (ArrAlloc len init_v) =
  let (cnt, len) = freshen_exp m cnt len in
  let (cnt, init_v) = freshen_exp m cnt init_v in
    (cnt, ArrAlloc len init_v)
End

Definition freshen_rhs_exps_def:
  (freshen_rhs_exps m cnt [] = (cnt, [])) ∧
  freshen_rhs_exps m cnt (re::res) =
  let (cnt, re) = freshen_rhs_exp m cnt re in
  let (cnt, res) = freshen_rhs_exps m cnt res in
    (cnt, re::res)
End

Definition freshen_stmt_def:
  (freshen_stmt m cnt Skip = (cnt, Skip)) ∧
  (freshen_stmt m cnt (Assert tst) =
   let (cnt, tst) = freshen_exp m cnt tst in
     (cnt, Assert tst)) ∧
  (freshen_stmt m cnt (Then stmt₀ stmt₁) =
   let (cnt, stmt₀) = freshen_stmt m cnt stmt₀ in
   let (cnt, stmt₁) = freshen_stmt m cnt stmt₁ in
     (cnt, Then stmt₀ stmt₁)) ∧
  (freshen_stmt m cnt (If tst thn els) =
   let (cnt, tst) = freshen_exp m cnt tst in
   let (cnt, thn) = freshen_stmt m cnt thn in
   let (cnt, els) = freshen_stmt m cnt els in
     (cnt, If tst thn els)) ∧
  (freshen_stmt m cnt (Dec local scope) =
   let (old, vt) = local in
   let (cnt, m) = add_fresh m cnt old in
   let (cnt, scope) = freshen_stmt m cnt scope in
     (cnt, Dec (lookup m old, vt) scope)) ∧
  (freshen_stmt m cnt (Assign lhss rhss) =
   let (cnt, rhss) = freshen_rhs_exps m cnt rhss in
   let (cnt, lhss) = freshen_lhs_exps m cnt lhss in
     (cnt, Assign lhss rhss)) ∧
  (freshen_stmt m cnt (While grd invs decrs mods body) =
   let (cnt, grd) = freshen_exp m cnt grd in
   let (cnt, invs) = freshen_exps m cnt invs in
   let (cnt, decrs) = freshen_exps m cnt decrs in
   let (cnt, mods) = freshen_exps m cnt mods in
   let (cnt, body) = freshen_stmt m cnt body in
     (cnt, While grd invs decrs mods body)) ∧
  (freshen_stmt m cnt (Print ets) =
   let (es, ts) = UNZIP ets in
   let (cnt, es) = freshen_exps m cnt es in
     (cnt, Print (ZIP (es, ts)))) ∧
  (freshen_stmt m cnt (MetCall lhss n args) =
   let (cnt, args) = freshen_exps m cnt args in
   let (cnt, lhss) = freshen_lhs_exps m cnt lhss in
     (cnt, MetCall lhss n args)) ∧
  freshen_stmt m cnt Return = (cnt, Return)
End

Definition map_add_fresh_def:
  map_add_fresh (m: (mlstring # num) list) (cnt: num) ([]: mlstring list) =
    (cnt, m) ∧
  map_add_fresh m cnt (n::ns) =
    let (cnt, m) = add_fresh m cnt n in map_add_fresh m cnt ns
End

Definition freshen_member_def:
  freshen_member (Method name ins reqs ens reads decrs outs mods body) =
  (let (in_ns, in_ts) = UNZIP ins in
   let (cnt, m) = map_add_fresh [] 0 in_ns in
   let in_ns = MAP (lookup m) in_ns in
   let (out_ns, out_ts) = UNZIP outs in
   let (cnt, m) = map_add_fresh m cnt out_ns in
   let out_ns = MAP (lookup m) out_ns in
   let (cnt, reqs) = freshen_exps m cnt reqs in
   let (cnt, reqs) = freshen_exps m cnt ens in
   let (cnt, reads) = freshen_exps m cnt reads in
   let (cnt, decrs) = freshen_exps m cnt decrs in
   let (cnt, mods) = freshen_exps m cnt mods in
   let (cnt, body) = freshen_stmt m cnt body in
     Method name (ZIP (in_ns, in_ts)) reqs ens reads
            decrs (ZIP (out_ns, out_ts)) mods body) ∧
  freshen_member (Function name ins res_t reqs reads decrs body) =
  (let (in_ns, in_ts) = UNZIP ins in
   let (cnt, m) = map_add_fresh [] 0 in_ns in
   let in_ns = MAP (lookup m) in_ns in
   let (cnt, reqs) = freshen_exps m cnt reqs in
   let (cnt, reads) = freshen_exps m cnt reads in
   let (cnt, decrs) = freshen_exps m cnt decrs in
   let (cnt, body) = freshen_exp m cnt body in
     Function name (ZIP (in_ns, in_ts)) res_t reqs reads decrs body)
End

Definition freshen_program_def:
  freshen_program (Program members) =
    Program (MAP freshen_member members)
End

val _ = export_theory ();
