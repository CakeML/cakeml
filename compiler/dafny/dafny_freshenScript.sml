(*
  Implements the freshen pass, where names are updated to be unique.
*)
Theory dafny_freshen
Ancestors
  dafny_ast mlstring mlint
Libs
  preamble


Definition lookup_def:
  lookup m old =
  case ALOOKUP m old of
  | NONE => «v»
  | SOME cnt => «v» ^ num_to_str cnt
End

Definition add_fresh_def:
  add_fresh m (cnt: num) old = (cnt + 1, (old, cnt)::m)
End

Definition map_add_fresh_def:
  map_add_fresh (m: (mlstring # num) list) (cnt: num) ([]: mlstring list) =
    (cnt, m) ∧
  map_add_fresh m cnt (n::ns) =
    let (cnt, m) = add_fresh m cnt n in map_add_fresh m cnt ns
End

Definition freshen_exp_def:
  freshen_exp m m_old m_prev cnt (Lit l) = (cnt, Lit l) ∧
  freshen_exp m m_old m_prev cnt (Var old) = (cnt, Var (lookup m old)) ∧
  freshen_exp m m_old m_prev cnt (If tst thn els) =
    (let
       (cnt, tst) = freshen_exp m m_old m_prev cnt tst;
       (cnt, thn) = freshen_exp m m_old m_prev cnt thn;
       (cnt, els) = freshen_exp m m_old m_prev cnt els
     in
       (cnt, If tst thn els)) ∧
  freshen_exp m m_old m_prev cnt (UnOp uop e) =
    (let (cnt, e) = freshen_exp m m_old m_prev cnt e in
       (cnt, UnOp uop e)) ∧
  freshen_exp m m_old m_prev cnt (BinOp bop e₁ e₂) =
    (let (cnt, e₁) = freshen_exp m m_old m_prev cnt e₁ in
     let (cnt, e₂) = freshen_exp m m_old m_prev cnt e₂ in
       (cnt, BinOp bop e₁ e₂)) ∧
  freshen_exp m m_old m_prev cnt (ArrLen arr) =
    (let
       (cnt, arr) = freshen_exp m m_old m_prev cnt arr
     in
       (cnt, ArrLen arr)) ∧
  freshen_exp m m_old m_prev cnt (ArrSel arr idx) =
    (let
       (cnt, arr) = freshen_exp m m_old m_prev cnt arr;
       (cnt, idx) = freshen_exp m m_old m_prev cnt idx
     in
       (cnt, ArrSel arr idx)) ∧
  freshen_exp m m_old m_prev cnt (FunCall n args) =
    (let
       (cnt, args) = freshen_exps m m_old m_prev cnt args
     in
       (cnt, FunCall n args)) ∧
  freshen_exp m m_old m_prev cnt (Forall (old, vt) e) =
    (let
       (cnt, m) = add_fresh m cnt old;
       (cnt, e) = freshen_exp m m_old m_prev cnt e
     in
       (cnt, Forall (lookup m old, vt) e)) ∧
  freshen_exp m m_old m_prev cnt (Old e) =
    (let (cnt, e) = freshen_exp m_old m_old m_prev cnt e in (cnt, Old e)) ∧
  freshen_exp m m_old m_prev cnt (OldHeap e) =
    (let (cnt, e) = freshen_exp m m_old m_prev cnt e in (cnt, OldHeap e)) ∧
  freshen_exp m m_old m_prev cnt (ForallHeap mods term) =
  (let (cnt, mods) = freshen_exps m m_old m_prev cnt mods in
   let (cnt, term) = freshen_exp m m_old m_prev cnt term in
     (cnt, ForallHeap mods term)) ∧
  freshen_exp m m_old m_prev cnt (Prev e) =
    (let (cnt, e) = freshen_exp m_prev m_old m_prev cnt e in (cnt, Prev e)) ∧
  freshen_exp m m_old m_prev cnt (PrevHeap e) =
    (let (cnt, e) = freshen_exp m m_old m_prev cnt e in (cnt, PrevHeap e)) ∧
  freshen_exp m m_old m_prev cnt (SetPrev e) =
    (let (cnt, e) = freshen_exp m m_old m cnt e in (cnt, SetPrev e)) ∧
  freshen_exp m m_old m_prev cnt (Let vars body) =
    (let (names, rhss) = UNZIP vars in
     let (cnt, rhss) = freshen_exps m m_old m_prev cnt rhss in
     let (cnt, m) = map_add_fresh m cnt names in
     let names = MAP (lookup m) names in
     let (cnt, body) = freshen_exp m m_old m_prev cnt body in
       (cnt, Let (ZIP (names, rhss)) body)) ∧
  freshen_exps m m_old m_prev cnt [] = (cnt, []) ∧
  freshen_exps m m_old m_prev cnt (e::es) =
    (let
       (cnt, e) = freshen_exp m m_old m_prev cnt e;
       (cnt, es) = freshen_exps m m_old m_prev cnt es
     in
       (cnt, (e::es)))
Termination
  wf_rel_tac ‘measure $ λx. case x of
                            | INL (_,_,_,_,e) => exp_size e
                            | INR (_,_,_,_,e) => list_size exp_size e’
  \\ gvs [UNZIP_MAP, list_size_pair_size_MAP_FST_SND]
End

Definition freshen_lhs_exp_def:
  (freshen_lhs_exp m m_old m_prev cnt (VarLhs old) =
     (cnt, VarLhs (lookup m old))) ∧
  freshen_lhs_exp m m_old m_prev cnt (ArrSelLhs arr idx) =
  let (cnt, arr) = freshen_exp m m_old m_prev cnt arr in
  let (cnt, idx) = freshen_exp m m_old m_prev cnt idx in
    (cnt, ArrSelLhs arr idx)
End

Definition freshen_lhs_exps_def:
  (freshen_lhs_exps m m_old m_prev cnt [] = (cnt, [])) ∧
  freshen_lhs_exps m m_old m_prev cnt (le::les) =
  let (cnt, le) = freshen_lhs_exp m m_old m_prev cnt le in
  let (cnt, les) = freshen_lhs_exps m m_old m_prev cnt les in
    (cnt, le::les)
End

Definition freshen_rhs_exp_def:
  (freshen_rhs_exp m m_old m_prev cnt (ExpRhs e) =
   let (cnt, e) = freshen_exp m m_old m_prev cnt e in
     (cnt, ExpRhs e)) ∧
  freshen_rhs_exp m m_old m_prev cnt (ArrAlloc len init_v ty) =
  let (cnt, len) = freshen_exp m m_old m_prev cnt len in
  let (cnt, init_v) = freshen_exp m m_old m_prev cnt init_v in
    (cnt, ArrAlloc len init_v ty)
End

Definition freshen_rhs_exps_def:
  (freshen_rhs_exps m m_old m_prev cnt [] = (cnt, [])) ∧
  freshen_rhs_exps m m_old m_prev cnt (re::res) =
  let (cnt, re) = freshen_rhs_exp m m_old m_prev cnt re in
  let (cnt, res) = freshen_rhs_exps m m_old m_prev cnt res in
    (cnt, re::res)
End

Definition freshen_stmt_def:
  (freshen_stmt m m_old m_prev cnt Skip = (cnt, Skip)) ∧
  (freshen_stmt m m_old m_prev cnt (Assert tst) =
   let (cnt, tst) = freshen_exp m m_old m_prev cnt tst in
     (cnt, Assert tst)) ∧
  (freshen_stmt m m_old m_prev cnt (Then stmt₀ stmt₁) =
   let (cnt, stmt₀) = freshen_stmt m m_old m_prev cnt stmt₀ in
   let (cnt, stmt₁) = freshen_stmt m m_old m_prev cnt stmt₁ in
     (cnt, Then stmt₀ stmt₁)) ∧
  (freshen_stmt m m_old m_prev cnt (If tst thn els) =
   let (cnt, tst) = freshen_exp m m_old m_prev cnt tst in
   let (cnt, thn) = freshen_stmt m m_old m_prev cnt thn in
   let (cnt, els) = freshen_stmt m m_old m_prev cnt els in
     (cnt, If tst thn els)) ∧
  (freshen_stmt m m_old m_prev cnt (Dec local scope) =
   let (old, vt) = local in
   let (cnt, m) = add_fresh m cnt old in
   let (cnt, scope) = freshen_stmt m m_old m_prev cnt scope in
     (cnt, Dec (lookup m old, vt) scope)) ∧
  (freshen_stmt m m_old m_prev cnt (Assign ass) =
   let (cnt, rhss) = freshen_rhs_exps m m_old m_prev cnt (MAP SND ass) in
   let (cnt, lhss) = freshen_lhs_exps m m_old m_prev cnt (MAP FST ass) in
     (cnt, Assign (ZIP (lhss, rhss)))) ∧
  (freshen_stmt m m_old m_prev cnt (While grd invs decrs mods body) =
   let (cnt, grd) = freshen_exp m m_old m_prev cnt grd in
   let (cnt, invs) = freshen_exps m m_old m_prev cnt invs in
   let (cnt, decrs) = freshen_exps m m_old m_prev cnt decrs in
   let (cnt, mods) = freshen_exps m m_old m_prev cnt mods in
   let (cnt, body) = freshen_stmt m m_old m_prev cnt body in
     (cnt, While grd invs decrs mods body)) ∧
  (freshen_stmt m m_old m_prev cnt (Print e ty) =
   let (cnt, e) = freshen_exp m m_old m_prev cnt e in
     (cnt, Print e ty)) ∧
  (freshen_stmt m m_old m_prev cnt (MetCall lhss n args) =
   let (cnt, args) = freshen_exps m m_old m_prev cnt args in
   let (cnt, lhss) = freshen_lhs_exps m m_old m_prev cnt lhss in
     (cnt, MetCall lhss n args)) ∧
  freshen_stmt m m_old m_prev cnt Return = (cnt, Return)
End

Definition freshen_member_def:
  freshen_member (Method name ins reqs ens reads decrs outs mods body) =
  (let (in_ns, in_ts) = UNZIP ins in
   let (cnt, m) = map_add_fresh [] 0 in_ns in
   let in_ns = MAP (lookup m) in_ns in
   let (out_ns, out_ts) = UNZIP outs in
   let (cnt, m) = map_add_fresh m cnt out_ns in
   let out_ns = MAP (lookup m) out_ns in
   let (cnt, reqs) = freshen_exps m m m cnt reqs in
   let (cnt, ens) = freshen_exps m m m cnt ens in
   let (cnt, reads) = freshen_exps m m m cnt reads in
   let (cnt, decrs) = freshen_exps m m m cnt decrs in
   let (cnt, mods) = freshen_exps m m m cnt mods in
   let (cnt, body) = freshen_stmt m m m cnt body in
     Method name (ZIP (in_ns, in_ts)) reqs ens reads
            decrs (ZIP (out_ns, out_ts)) mods body) ∧
  freshen_member (Function name ins res_t reqs reads decrs body) =
  (let (in_ns, in_ts) = UNZIP ins in
   let (cnt, m) = map_add_fresh [] 0 in_ns in
   let in_ns = MAP (lookup m) in_ns in
   let (cnt, reqs) = freshen_exps m m m cnt reqs in
   let (cnt, reads) = freshen_exps m m m cnt reads in
   let (cnt, decrs) = freshen_exps m m m cnt decrs in
   let (cnt, body) = freshen_exp m m m cnt body in
     Function name (ZIP (in_ns, in_ts)) res_t reqs reads decrs body)
End

Definition freshen_program_def:
  freshen_program (Program members) =
    Program (MAP freshen_member members)
End
