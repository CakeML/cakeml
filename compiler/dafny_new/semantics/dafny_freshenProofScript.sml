(*
  Correctness proof for the freshen pass.
*)

open preamble
open dafny_astTheory
open dafny_evaluateTheory
open dafny_semanticPrimitivesTheory
open mlstringTheory
open mlintTheory
open quantHeuristicsTheory  (* LIST_LENGTH_1 *)

val _ = new_theory "dafny_freshenProof";

(* TODO Remove unused definitions and trivialities/theorems *)

(* Definitions *)

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

(* Relations and invariants *)

Definition locals_rel_def:
  locals_rel [] [] [] = T ∧
  locals_rel ((snam, sval)::ss) ((snam', tnum)::ms) ((tnam, tval)::ts) =
    (snam = snam' ∧ tnam = («v» ^ num_to_str tnum) ∧
     sval = tval ∧ locals_rel ss ms ts) ∧
  locals_rel _ _ _ = F
End

Definition map_inv_def:
  map_inv (m: (mlstring # num) list) (cnt: num) ⇔
    SORTED (>) (MAP SND m) ∧ EVERY (λi. i < cnt) (MAP SND m)
End

Definition state_rel_def:
  state_rel s t m cnt ⇔
  s.clock = t.clock ∧ s.heap = t.heap ∧ s.cout = t.cout ∧
  locals_rel s.locals m t.locals ∧ map_inv m cnt
End

Definition env_rel_def:
  env_rel env env' ⇔
    env'.is_running = env.is_running ∧
    env'.prog = freshen_program env.prog
End

(* simps *)

Theorem with_same_locals[simp]:
  ∀s. s with locals := s.locals = s
Proof
  gvs [state_component_equality]
QED

Triviality lookup_not_head[simp]:
  ∀v v' n ms.
    v ≠ v' ⇒ lookup ((v,n)::ms) v' = lookup ms v'
Proof
  rpt strip_tac \\ gvs [lookup_def]
QED

Triviality lookup_head[simp]:
  ∀v n ms.
    lookup ((v,n)::ms) v = «v» ^ toString n
Proof
  rpt strip_tac \\ gvs [lookup_def]
QED

Triviality locals_rel_pop:
  ∀sl ss ml ms tl ts.
    locals_rel (sl::ss) (ml::ms) (tl::ts) ⇒ locals_rel ss ms ts
Proof
  rpt strip_tac
  \\ PairCases_on ‘sl’ \\ PairCases_on ‘ml’ \\ PairCases_on ‘tl’
  \\ gvs [locals_rel_def]
QED

Triviality locals_rel_push:
  ∀ss ms ts old v cnt.
    locals_rel ss ms ts ⇒
    locals_rel ((old, v)::ss) ((old, cnt)::ms)
      ((lookup ((old, cnt)::ms) old, v)::ts)
Proof
  gvs [locals_rel_def, lookup_def]
QED

Triviality safe_zip_imp:
  safe_zip xs ys = SOME zs ⇒
  LENGTH xs = LENGTH ys ∧ LENGTH ys = LENGTH zs
Proof
  rpt strip_tac \\ gvs [safe_zip_def]
QED

Triviality map_add_fresh_map_inv:
  map_add_fresh m cnt ns = (cnt', m') ∧ map_inv m cnt ⇒
  map_inv m' cnt'
Proof
  cheat
QED

Triviality not_mem_map_lookup:
  ¬MEM snam xs ⇒ MAP (lookup ((snam,tnum)::ms)) xs = MAP (lookup ms) xs
Proof
  Induct_on ‘xs’ \\ gvs []
QED

Triviality distinct_names_map_lookup:
  ¬MEM snam (MAP FST ms) ∧ ALL_DISTINCT (MAP FST ms) ⇒
  MAP (lookup ((snam,tnum)::ms)) (MAP FST ms) =
  MAP (lookup ms) (MAP FST ms)
Proof
  rpt strip_tac \\ gvs [] \\ drule not_mem_map_lookup \\ gvs []
QED

Triviality locals_rel_from_map:
  ∀(vs: (value option) list) (m: (mlstring # num) list).
    ALL_DISTINCT (MAP FST m) ∧ LENGTH vs = LENGTH m ⇒
    locals_rel (ZIP (MAP FST m, vs)) m
      (ZIP (MAP (lookup m) (MAP FST m), vs))
Proof
  Induct_on ‘m’ \\ rpt strip_tac
  \\ gvs [locals_rel_def]
  \\ rename [‘lookup (m::ms)’]
  \\ namedCases_on ‘m’ ["snam tnum"]
  \\ Cases_on ‘vs’ \\ gvs [locals_rel_def]
  \\ drule distinct_names_map_lookup \\ gvs []
QED

Triviality map_add_fresh_distinct:
  ∀m cnt ns cnt' m'.
    map_add_fresh m cnt ns = (cnt', m') ∧
    ALL_DISTINCT ((MAP FST m) ++ ns) ⇒
    ALL_DISTINCT (MAP FST m')
Proof
  Induct_on ‘ns’ \\ rpt strip_tac
  \\ gvs [map_add_fresh_def, add_fresh_def]
  \\ last_x_assum drule
  \\ impl_tac \\ gvs []
  \\ rename [‘map_add_fresh ((n,_)::_)’]
  \\ gvs [ALL_DISTINCT_APPEND]
  \\ spose_not_then assume_tac
  \\ first_x_assum drule \\ gvs []
QED

Triviality map_add_fresh_len:
  ∀m cnt ns cnt' ms' m'.
    map_add_fresh m cnt ns = (cnt', m') ⇒
    LENGTH m' = LENGTH m + LENGTH ns
Proof
  Induct_on ‘ns’ \\ rpt strip_tac
  \\ gvs [map_add_fresh_def, add_fresh_def]
  \\ res_tac \\ gvs []
QED

Triviality map_add_fresh_exists:
  ∀m cnt ns cnt' m'.
    map_add_fresh m cnt ns = (cnt', m') ⇒
    ∃m₁. m' = m₁ ++ m ∧ MAP FST m₁ = REVERSE ns
Proof
  Induct_on ‘ns’ \\ rpt strip_tac
  \\ gvs [map_add_fresh_def, add_fresh_def]
  \\ last_x_assum drule_all \\ rpt strip_tac \\ gvs []
QED

Triviality map_add_fresh_ins_locals_rel:
  ∀ins (in_vs: value list) cnt m.
    map_add_fresh [] 0 (MAP FST ins) = (cnt, m) ∧
    ALL_DISTINCT (MAP FST ins) ∧
    LENGTH ins = LENGTH in_vs ⇒
    locals_rel
      (REVERSE (ZIP (MAP FST ins, MAP SOME in_vs))) m
      (REVERSE (ZIP (MAP (lookup m) (MAP FST ins), MAP SOME in_vs)))
Proof
  rpt strip_tac
  \\ drule_then assume_tac map_add_fresh_distinct \\ gvs []
  \\ drule map_add_fresh_len \\ strip_tac \\ gvs []
  \\ drule locals_rel_from_map
  \\ disch_then $ qspec_then ‘REVERSE (MAP SOME in_vs)’ mp_tac
  \\ strip_tac \\ gvs []
  \\ drule map_add_fresh_exists \\ rpt strip_tac \\ gvs []
  \\ gvs [MAP_REVERSE, REVERSE_ZIP]
QED

Triviality locals_rel_append:
  locals_rel xs ys zs ∧
  locals_rel xs' ys' zs' ⇒
  locals_rel (xs' ++ xs) (ys' ++ ys) (zs' ++ zs)
Proof
  cheat
QED

(* TODO Check whether something like this already exists *)
Triviality MEM_ALOOKUP:
  ∀l x. MEM x (MAP FST l) ⇒ ∃v. ALOOKUP l x = SOME v
Proof
  Induct_on ‘l’ \\ rpt strip_tac \\ gvs []
  \\ rename [‘h::l’] \\ namedCases_on ‘h’ ["k v"] \\ gvs []
  \\ Cases_on ‘k = x’ \\ gvs []
QED

Triviality lookup_append_eq:
  ∀n m₁ m₀.
    MEM n (MAP FST m₁) ⇒ lookup (m₁ ++ m₀) n = lookup m₁ n
Proof
  rpt strip_tac
  \\ gvs [lookup_def, ALOOKUP_APPEND]
  \\ drule MEM_ALOOKUP \\ rpt strip_tac \\ gvs []
QED

Triviality map_lookup_append_eq:
  ∀ns m₁ m₀.
    (∀n. MEM n ns ⇒ MEM n (MAP FST m₁)) ⇒
    MAP (lookup (m₁ ++ m₀)) ns = MAP (lookup m₁) ns
Proof
  rpt strip_tac
  \\ irule MAP_CONG \\ gvs []
  \\ metis_tac [lookup_append_eq]
QED

Triviality map_lookup_append_eq:
  MAP FST m₁ = REVERSE ns ⇒
  MAP (lookup (m₁ ++ m₀)) ns = MAP (lookup m₁) ns
Proof
  rpt strip_tac
  \\ irule map_lookup_append_eq
  \\ rpt strip_tac \\ gvs []
QED

Triviality map_fst_reverse_imp:
  MAP FST m = REVERSE ns ⇒ (∀n. MEM n ns ⇒ MEM n (MAP FST m))
Proof
  gvs []
QED

Triviality map_add_fresh_ins_outs_locals_rel:
  ∀ins (in_vs: value list) cnt₁ m outs cnt₂ m'.
    map_add_fresh [] 0 (MAP FST ins) = (cnt₁,m) ∧
    map_add_fresh m cnt₁ (MAP FST outs) = (cnt₂,m') ∧
    ALL_DISTINCT (MAP FST ins ++ MAP FST outs) ∧
    LENGTH ins = LENGTH in_vs ⇒
    locals_rel
      (REVERSE
         (ZIP (MAP FST ins, MAP SOME in_vs) ++
          ZIP (MAP FST outs, REPLICATE (LENGTH outs) NONE))) m'
      (REVERSE
         (ZIP (MAP (lookup m) (MAP FST ins),MAP SOME in_vs) ++
          ZIP
            (MAP (lookup m') (MAP FST outs),
             REPLICATE (LENGTH outs) NONE)))
Proof
  rpt strip_tac
  \\ gvs [ALL_DISTINCT_APPEND]
  \\ drule_all map_add_fresh_ins_locals_rel \\ strip_tac
  \\ drule map_add_fresh_exists \\ rpt strip_tac
  \\ rename [‘m' = m₁ ++ m’]
  \\ ‘LENGTH m₁ = LENGTH outs’ by metis_tac [LENGTH_MAP, LENGTH_REVERSE]
  \\ qspecl_then [‘REPLICATE (LENGTH outs) NONE’, ‘m₁’] mp_tac
       locals_rel_from_map
  \\ strip_tac \\ gvs []
  \\ rev_dxrule locals_rel_append
  \\ disch_then dxrule \\ strip_tac
  \\ gvs [REVERSE_APPEND, MAP_REVERSE, REVERSE_ZIP]
  \\ drule_then assume_tac map_fst_reverse_imp
  \\ drule map_lookup_append_eq
  \\ disch_then $ qspec_then ‘m’ assume_tac \\ gvs []
QED

Triviality freshen_exp_mono:
  (∀m cnt e cnt' e'. freshen_exp m cnt e = (cnt', e') ⇒ cnt ≤ cnt') ∧
  (∀m cnt es cnt' es'. freshen_exps m cnt es = (cnt', es') ⇒ cnt ≤ cnt')
Proof
  ho_match_mp_tac freshen_exp_ind \\ rpt strip_tac
  \\ gvs [freshen_exp_def] \\ rpt (pairarg_tac \\ gvs []) \\ gvs [add_fresh_def]
QED

(* TODO Move to mlstring *)
Theorem mlstring_common_prefix:
  ∀s t1 t2. s ^ t1 = s ^ t2 ⇔ t1 = t2
Proof
  rpt Cases \\ gvs [strcat_thm, implode_def]
QED

Triviality lookup_pop:
  snam ≠ var ⇒ lookup ((snam,tnum)::m) var = lookup m var
Proof
  gvs [lookup_def]
QED

Triviality SORTED_DESC_EVERY:
  ∀(x: num) xs. SORTED $> (x::xs) ⇒ EVERY (λi. i < x) xs
Proof
  Induct_on ‘xs’ \\ rpt strip_tac \\ gvs []
  \\ last_x_assum drule \\ rpt strip_tac \\ gvs []
  \\ irule MONO_EVERY \\ qexists ‘λi. i < h’ \\ gvs []
QED

Triviality map_inv_pair_pop:
  map_inv ((snam,tnum)::ms) cnt ⇒ map_inv ms tnum
Proof
  rpt strip_tac \\ gvs [map_inv_def]
  \\ drule SORTED_TL \\ strip_tac \\ gvs []
  \\ drule SORTED_DESC_EVERY \\ gvs []
QED

Triviality map_inv_pop:
  map_inv (m::ms) cnt ⇒ map_inv ms cnt
Proof
  rpt strip_tac \\ gvs [map_inv_def]
  \\ drule SORTED_TL \\ strip_tac \\ gvs []
QED

Triviality map_inv_cons:
  map_inv (m::ms) cnt ⇒ ∃snam tnum. m = (snam, tnum) ∧ tnum < cnt
Proof
  PairCases_on ‘m’ \\ rpt strip_tac \\ gvs [map_inv_def]
QED

Triviality map_inv_mono:
  ∀m cnt cnt'.
    map_inv m cnt ∧ cnt ≤ cnt' ⇒ map_inv m cnt'
Proof
  rpt strip_tac \\ gvs [map_inv_def]
  \\ irule MONO_EVERY \\ qexists ‘λi. i < cnt’ \\ gvs []
QED

Triviality map_inv_lookup_neq:
  ∀m tnum var.
    map_inv m tnum ⇒ lookup m var ≠ «v» ^ toString tnum
Proof
  Induct_on ‘m’ \\ rpt strip_tac
  >- (gvs [lookup_def, strcat_thm, implode_def])
  \\ drule map_inv_cons \\ rpt strip_tac \\ gvs []
  \\ drule map_inv_pop \\ strip_tac
  \\ last_x_assum drule \\ disch_then $ qspec_then ‘var’ assume_tac
  \\ Cases_on ‘snam = var’
  \\ gvs [lookup_def, mlstring_common_prefix, num_to_str_11]
QED

Triviality locals_rel_read_local:
  ∀ss m ts var val cnt.
    locals_rel ss m ts ∧ map_inv m cnt ∧
    read_local ss var = SOME val ⇒
    read_local ts (lookup m var) = SOME val
Proof
  recInduct locals_rel_ind \\ rpt strip_tac
  \\ gvs [locals_rel_def, read_local_def]
  \\ rename [‘lookup ((snam,tnum)::m')’]
  \\ Cases_on ‘snam = var’ \\ gvs []
  \\ gvs [lookup_pop]
  \\ drule_then assume_tac map_inv_pair_pop
  \\ drule map_inv_lookup_neq
  \\ disch_then $ qspec_then ‘var’ assume_tac \\ gvs []
  \\ last_x_assum drule_all \\ gvs []
QED

Triviality state_rel_mono:
  ∀s t m cnt cnt'.
    state_rel s t m cnt ∧ cnt ≤ cnt' ⇒ state_rel s t m cnt'
Proof
  gvs [state_rel_def] \\ rpt strip_tac \\ imp_res_tac map_inv_mono
QED

Triviality get_member_aux_some:
  ∀name members member.
    get_member_aux name members = SOME member ⇒
    get_member_aux name (MAP freshen_member members) =
      SOME (freshen_member member)
Proof
  Induct_on ‘members’ \\ rpt strip_tac
  \\ gvs [get_member_aux_def]
  \\ rename [‘freshen_member m’]
  \\ Cases_on ‘m’ \\ gvs []
  \\ pop_assum mp_tac \\ IF_CASES_TAC \\ rpt strip_tac
  \\ gvs [freshen_member_def] \\ rpt (pairarg_tac \\ gvs [])
QED

Triviality get_member_some:
  ∀name env member env'.
    get_member name env.prog = SOME member ∧ env_rel env env' ⇒
    get_member name env'.prog = SOME (freshen_member member)
Proof
  gvs [env_rel_def]
  \\ namedCases_on ‘env.prog’ ["members"]
  \\ namedCases_on ‘env'.prog’ ["members'"]
  \\ rpt strip_tac \\ gvs [get_member_def, freshen_program_def]
  \\ drule get_member_aux_some \\ gvs []
QED

(** **)

Triviality map_inv_distinct:
  (* This should follow from sortedness in a strict order *)
  map_inv m cnt ⇒ ALL_DISTINCT (MAP SND m)
Proof
  cheat
QED

(** **)

Triviality lemma:
  ∀m₀ cnt ns cnt' m'.
    map_add_fresh m₀ cnt ns = (cnt', m') ∧
    map_inv m₀ cnt ⇒
    ∃m₁.
      m' = m₁ ++ m₀ ∧ MAP FST m₁ = REVERSE ns ∧
      ALL_DISTINCT (MAP SND m₀ ++ MAP SND m₁)
Proof
  Induct_on ‘ns’ \\ rpt strip_tac
  \\ gvs [map_add_fresh_def, add_fresh_def]
  >- (drule map_inv_distinct \\ gvs [])
  \\ last_x_assum drule \\ impl_tac
  >- (gvs [map_inv_def] \\ cheat)
  \\ rpt strip_tac
  \\ rename [‘(h, cnt)’]
  \\ qexists ‘m₁ ++ [(h, cnt)]’ \\ gvs [ALL_DISTINCT_APPEND]
QED

Triviality lemma2:
  ∀m₁ ns m₀.
    MAP FST m₁ = REVERSE ns ⇒
    MAP (lookup (m₁ ++ m₀)) ns =
    MAP (λi. «v» ^ num_to_str i) (MAP SND m₁)
Proof
  cheat
QED

Triviality lemma3:
  ALL_DISTINCT (MAP (λi. «v» ^ toString i) (MAP SND m)) ⇔
    ALL_DISTINCT (MAP SND m)
Proof
  cheat
QED

Triviality lemma4:
  ALL_DISTINCT
    (MAP (λi. «v» ^ toString i) (MAP SND m₀) ++
     MAP (λi. «v» ^ toString i) (MAP SND m₁)) ⇔
  ALL_DISTINCT (MAP SND m₀ ++ MAP SND m₁)
Proof
  cheat
QED

Triviality distinct_ins_lookup:
  map_add_fresh [] 0 ns = (cnt, m) ∧ ALL_DISTINCT ns ⇒
  ALL_DISTINCT (MAP (lookup m) ns)
Proof
  rpt strip_tac
  \\ drule lemma \\ rpt strip_tac \\ gvs [map_inv_def]
  \\ drule lemma2 \\ disch_then $ qspec_then ‘[]’ assume_tac \\ gvs []
  \\ gvs [lemma3]
QED

Triviality distinct_ins_out_lookup:
  map_add_fresh [] 0 (MAP FST ins) = (cnt, m₀) ∧
  map_add_fresh m₀ cnt (MAP FST outs) = (cnt', m₁) ∧
  ALL_DISTINCT (MAP FST ins ++ MAP FST outs) ⇒
  ALL_DISTINCT
    (MAP (lookup m₀) (MAP FST ins) ++ MAP (lookup m₁) (MAP FST outs))
Proof
  rpt strip_tac
  \\ rev_drule lemma
  \\ impl_tac >- gvs [map_inv_def]
  \\ rpt strip_tac \\ gvs []
  \\ rev_drule map_add_fresh_map_inv
  \\ impl_tac >- gvs [map_inv_def]
  \\ rpt strip_tac \\ gvs []
  \\ drule lemma \\ rpt strip_tac \\ gvs []
  \\ drule lemma2 \\ disch_then $ qspec_then ‘m₀’ assume_tac \\ gvs []
  \\ rev_drule lemma2 \\ disch_then $ qspec_then ‘[]’ assume_tac \\ gvs []
  \\ gvs [lemma4]
QED

Theorem correct_freshen_exp:
  (∀s env e s' res t m cnt cnt' e' env'.
     evaluate_exp s env e = (s', res) ∧ state_rel s t m cnt ∧
     freshen_exp m cnt e = (cnt', e') ∧
     env_rel env env' ∧ res ≠ Rerr Rtype_error ⇒
     ∃t'. evaluate_exp t env' e' = (t', res) ∧ state_rel s' t' m cnt') ∧
  (∀s env es s' res t m cnt cnt' es' env'.
     evaluate_exps s env es = (s', res) ∧ state_rel s t m cnt ∧
     freshen_exps m cnt es = (cnt', es') ∧
     env_rel env env' ∧ res ≠ Rerr Rtype_error ⇒
     ∃t'. evaluate_exps t env' es' = (t', res) ∧ state_rel s' t' m cnt')
Proof
  ho_match_mp_tac evaluate_exp_ind \\ rpt strip_tac
  >~ [‘FunCall name args’] >-
   (gvs [freshen_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ rename [‘freshen_exps _ _ _ = (cnt₁, args')’]
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘get_member name env.prog’ ["", "member"] \\ gvs []
    \\ drule_all get_member_some \\ rpt strip_tac \\ gvs []
    \\ Cases_on ‘member’ \\ gvs [freshen_member_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ rename [‘freshen_exp _ _ body = (_, body')’,
               ‘map_add_fresh _ _ _ = (cnt₁, m')’]
    \\ namedCases_on ‘evaluate_exps s env args’ ["s₁ r"] \\ gvs []
    \\ namedCases_on ‘r’ ["in_vs", "err"] \\ gvs []
    \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs []
    \\ rename [‘state_rel s₁ t₁ m cnt₁’]
    \\ gvs [set_up_call_def]
    \\ rename [‘UNZIP ins = _’]
    \\ gvs [UNZIP_MAP, MAP_ZIP]
    \\ Cases_on ‘ALL_DISTINCT (MAP FST ins)’ \\ gvs []
    \\ drule distinct_ins_lookup \\ strip_tac \\ gvs []
    \\ gvs [safe_zip_def]
    \\ Cases_on ‘LENGTH ins ≠ LENGTH in_vs’ \\ gvs []
    \\ qabbrev_tac
         ‘in_locals = ZIP (MAP FST ins, MAP SOME in_vs)’
    \\ qabbrev_tac
         ‘in_locals' =
            ZIP (MAP (lookup m') (MAP FST ins), MAP SOME in_vs)’
    \\ ‘s₁.clock = t₁.clock’ by gvs [state_rel_def]
    \\ Cases_on ‘s₁.clock = 0’ \\ gvs [] >- gvs [restore_locals_def]
    \\ gvs [CaseEq "prod"]
    \\ rename [‘evaluate_exp _ _ _ = (_, r)’]
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
    \\ last_x_assum $ drule_at $ Pos last
    \\ disch_then $ drule_at $ Pos last
    \\ disch_then $
         qspec_then ‘dec_clock (t₁ with locals := REVERSE in_locals')’ mp_tac
    \\ impl_tac
    >- (gvs [state_rel_def, dec_clock_def]
        \\ drule map_add_fresh_map_inv
        \\ impl_tac >- gvs [map_inv_def] \\ strip_tac
        \\ drule_all map_add_fresh_ins_locals_rel \\ strip_tac \\ gvs []
        \\ imp_res_tac freshen_exp_mono
        \\ imp_res_tac map_inv_mono)
    \\ rpt strip_tac \\ gvs []
    \\ rename [‘state_rel s₃ t₃ m' _’]
    \\ qexists ‘restore_locals t₃ t₁.locals’
    \\ ‘s' = restore_locals s₃ s₁.locals’ by gvs [AllCaseEqs()]
    \\ gvs []
    \\ conj_tac >- gvs [AllCaseEqs()]
    \\ gvs [state_rel_def, restore_locals_def])
  \\ cheat
  (* >~ [‘Lit l’] >- *)
  (*  (gvs [evaluate_exp_def, freshen_exp_def]) *)
  (* >~ [‘Var v’] >- *)
  (*  (gvs [evaluate_exp_def, freshen_exp_def, state_rel_def, CaseEq "option"] *)
  (*   \\ imp_res_tac locals_rel_read_local) *)
  (* >~ [‘Forall (v,ty) e’] >- *)
  (*  (full_simp_tac bool_ss [evaluate_exp_def, freshen_exp_def] *)
  (*   \\ qabbrev_tac ‘f = λval. evaluate_exp (push_local s v val) env e’ *)
  (*   \\ gvs [] \\ rpt (pairarg_tac \\ gvs []) *)
  (*   \\ rename [‘freshen_exp m₁ cnt₁ e = (cnt₂,e₂)’] *)
  (*   \\ full_simp_tac bool_ss [evaluate_exp_def, freshen_exp_def] *)
  (*   \\ ‘state_rel s t m cnt₂’ by *)
  (*     (imp_res_tac freshen_exp_mono \\ imp_res_tac state_rel_mono *)
  (*      \\ gvs [add_fresh_def]) *)
  (*   \\ IF_CASES_TAC >- gvs [env_rel_def] *)
  (*   \\ ‘t.clock = s.clock’ by gvs [state_rel_def] *)
  (*   \\ IF_CASES_TAC >- gvs [env_rel_def] *)
  (*   \\ qabbrev_tac ‘g = λval. evaluate_exp (push_local t (lookup m₁ v) val) env' e₂’ *)
  (*   \\ ‘s' = s’ by gvs [AllCaseEqs()] *)
  (*   \\ gvs [] *)
  (*   \\ qexists_tac ‘t’ \\ gvs [] *)
  (*   \\ qpat_x_assum ‘_ = (s,res)’ mp_tac *)
  (*   \\ IF_CASES_TAC >- gvs [env_rel_def] \\ rpt strip_tac *)
  (*   \\ ‘∀v. v ∈ all_values ty ⇒ SND (f v) ≠ Rerr Rtype_error’ by *)
  (*     (rpt strip_tac \\ qpat_x_assum ‘_ = (s,res)’ mp_tac *)
  (*      \\ IF_CASES_TAC \\ gvs []) *)
  (*   \\ qpat_x_assum ‘_ = (s,res)’ mp_tac *)
  (*   \\ qsuff_tac ‘∀v. v ∈ all_values ty ⇒ SND (f v) = SND (g v)’ >- *)
  (*    (rpt strip_tac \\ gvs [AllCaseEqs()] \\ metis_tac []) *)
  (*   \\ unabbrev_all_tac \\ gvs [] *)
  (*   \\ qx_gen_tac ‘val’ *)
  (*   \\ strip_tac \\ last_x_assum drule \\ strip_tac *)
  (*   \\ Cases_on ‘evaluate_exp (push_local s v val) env e’ \\ gvs [] *)
  (*   \\ last_x_assum $ qspec_then ‘val’ mp_tac \\ gvs [] *)
  (*   \\ disch_then $ drule_at $ Pos $ el 2 *)
  (*   \\ disch_then $ drule_at $ Pos $ el 2 *)
  (*   \\ disch_then $ qspec_then ‘(push_local t (lookup m₁ v) val)’ mp_tac *)
  (*   \\ reverse impl_tac >- (strip_tac \\ gvs []) *)
  (*   \\ gvs [state_rel_def, push_local_def, *)
  (*           add_fresh_def, locals_rel_def, lookup_def]) *)
  (* >~ [‘If tst thn els’] >- *)
  (*  (gvs [evaluate_exp_def, freshen_exp_def] *)
  (*   \\ rpt (pairarg_tac \\ gvs []) *)
  (*   \\ imp_res_tac freshen_exp_mono *)
  (*   \\ gvs [evaluate_exp_def] *)
  (*   \\ namedCases_on ‘evaluate_exp s env tst’ ["s₁ r"] \\ gvs [] *)
  (*   \\ reverse $ namedCases_on ‘r’ ["tst_v", "err"] \\ gvs [] *)
  (*   \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs [] *)
  (*   \\ imp_res_tac state_rel_mono *)
  (*   \\ rename [‘evaluate_exp t env tst' = (t₁,Rval tst_v)’] *)
  (*   \\ namedCases_on ‘do_cond tst_v thn els’ ["", "branch"] \\ gvs [] *)
  (*   \\ namedCases_on ‘do_cond tst_v thn' els'’ ["", "branch'"] \\ gvs [] *)
  (*   \\ gvs [oneline do_cond_def, AllCaseEqs ()] *)
  (*   \\ last_x_assum $ drule_at $ Pos $ el 2 *)
  (*   \\ disch_then $ drule  \\ rpt strip_tac \\ gvs [] *)
  (*   \\ imp_res_tac state_rel_mono) *)
  (* >~ [‘UnOp uop e’] >- *)
  (*  (gvs [evaluate_exp_def, freshen_exp_def] *)
  (*   \\ rpt (pairarg_tac \\ gvs []) *)
  (*   \\ gvs [evaluate_exp_def] *)
  (*   \\ namedCases_on ‘evaluate_exp s env e’ ["s₁ r"] \\ gvs [] *)
  (*   \\ namedCases_on ‘r’ ["v", "err"] \\ gvs [] *)
  (*   \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs [] *)
  (*   \\ namedCases_on ‘do_uop uop v’ ["", "r"] \\ gvs []) *)
  (* >~ [‘BinOp bop e₀ e₁’] >- *)
  (*  (gvs [evaluate_exp_def, freshen_exp_def] *)
  (*   \\ rpt (pairarg_tac \\ gvs []) *)
  (*   \\ rename [‘freshen_exp m cnt e₀ = (cnt₁,e₀')’, *)
  (*              ‘freshen_exp m cnt₁ e₁ = (cnt₂,e₁')’] *)
  (*   \\ gvs [evaluate_exp_def] *)
  (*   \\ namedCases_on ‘evaluate_exp s env e₀’ ["s₁ r"] \\ gvs [] *)
  (*   \\ reverse $ namedCases_on ‘r’ ["v₀", "err"] \\ gvs [] *)
  (*   \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs [] *)
  (*   >- (imp_res_tac freshen_exp_mono \\ imp_res_tac state_rel_mono) *)
  (*   \\ rename [‘evaluate_exp t₁ env e₁'’] *)
  (*   \\ reverse $ namedCases_on ‘try_sc bop v₀’ ["", "r"] \\ gvs [] *)
  (*   >- (imp_res_tac freshen_exp_mono \\ imp_res_tac state_rel_mono) *)
  (*   \\ namedCases_on ‘evaluate_exp s₁ env e₁’ ["s₂ r"] \\ gvs [] *)
  (*   \\ reverse $ namedCases_on ‘r’ ["v₁", "err"] \\ gvs [] *)
  (*   \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs [] *)
  (*   \\ namedCases_on ‘do_bop bop v₀ v₁’ ["", "r"] \\ gvs []) *)
  (* >~ [‘ArrLen arr’] >- *)
  (*  (gvs [evaluate_exp_def, freshen_exp_def] *)
  (*   \\ rpt (pairarg_tac \\ gvs []) *)
  (*   \\ gvs [evaluate_exp_def] *)
  (*   \\ namedCases_on ‘evaluate_exp s env arr’ ["s₁ r"] *)
  (*   \\ namedCases_on ‘r’ ["arr_v", "err"] \\ gvs [] *)
  (*   \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs [] *)
  (*   \\ namedCases_on ‘get_array_len arr_v’ ["", "len"] \\ gvs []) *)
  (* >~ [‘ArrSel arr idx’] >- *)
  (*  (gvs [evaluate_exp_def, freshen_exp_def] *)
  (*   \\ rpt (pairarg_tac \\ gvs []) *)
  (*   \\ gvs [evaluate_exp_def] *)
  (*   \\ namedCases_on ‘evaluate_exp s env arr’ ["s₁ r"] *)
  (*   \\ reverse $ namedCases_on ‘r’ ["arr_v", "err"] \\ gvs [] *)
  (*   \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs [] *)
  (*   >- (imp_res_tac freshen_exp_mono \\ imp_res_tac state_rel_mono) *)
  (*   \\ rename [‘evaluate_exp t _ _' = (t₁, _)’] *)
  (*   \\ namedCases_on ‘evaluate_exp s₁ env idx’ ["s₂ r"] *)
  (*   \\ namedCases_on ‘r’ ["idx_v", "err"] \\ gvs [] *)
  (*   \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs [] *)
  (*   \\ rename [‘evaluate_exp t₁ _ _' = (t₂, _)’] *)
  (*   \\ namedCases_on ‘index_array s₂ arr_v idx_v’ ["", "v"] \\ gvs [] *)
  (*   \\ namedCases_on ‘index_array t₂ arr_v idx_v’ ["", "v'"] \\ gvs [] *)
  (*   \\ gvs [index_array_def, state_rel_def, AllCaseEqs ()]) *)
  (* >~ [‘freshen_exps m cnt []’] >- gvs [evaluate_exp_def, freshen_exp_def] *)
  (* >~ [‘freshen_exps m cnt (e::es)’] >- *)
  (*  (gvs [evaluate_exp_def, freshen_exp_def] *)
  (*   \\ rpt (pairarg_tac \\ gvs []) *)
  (*   \\ gvs [evaluate_exp_def] *)
  (*   \\ namedCases_on ‘evaluate_exp s env e’ ["s₁ r"] *)
  (*   \\ reverse $ namedCases_on ‘r’ ["v", "err"] \\ gvs [] *)
  (*   \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs [] *)
  (*   >- (imp_res_tac freshen_exp_mono \\ imp_res_tac state_rel_mono) *)
  (*   \\ namedCases_on ‘evaluate_exps s₁ env es’ ["s₂ r"] *)
  (*   \\ namedCases_on ‘r’ ["vs", "err"] \\ gvs [] *)
  (*   \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs []) *)
QED

Triviality freshen_lhs_exp_mono:
 ∀m cnt lhs cnt' lhs'.
    freshen_lhs_exp m cnt lhs = (cnt', lhs') ⇒ cnt ≤ cnt'
Proof
  Cases_on ‘lhs’ \\ rpt strip_tac
  \\ gvs [freshen_lhs_exp_def] \\ rpt (pairarg_tac \\ gvs [])
  \\ imp_res_tac freshen_exp_mono \\ gvs []
QED

Triviality freshen_lhs_exps_mono:
  ∀m cnt lhss cnt' lhss'.
    freshen_lhs_exps m cnt lhss = (cnt', lhss') ⇒ cnt ≤ cnt'
Proof
  Induct_on ‘lhss’ \\ rpt strip_tac
  \\ gvs [freshen_lhs_exps_def] \\ rpt (pairarg_tac \\ gvs[])
  \\ imp_res_tac freshen_lhs_exp_mono \\ res_tac \\ gvs []
QED

Triviality freshen_rhs_exp_mono:
 ∀m cnt rhs cnt' rhs'.
    freshen_rhs_exp m cnt rhs = (cnt', rhs') ⇒ cnt ≤ cnt'
Proof
  Cases_on ‘rhs’ \\ rpt strip_tac
  \\ gvs [freshen_rhs_exp_def] \\ rpt (pairarg_tac \\ gvs [])
  \\ imp_res_tac freshen_exp_mono \\ gvs []
QED

Triviality freshen_rhs_exps_mono:
  ∀m cnt rhss cnt' rhss'.
    freshen_rhs_exps m cnt rhss = (cnt', rhss') ⇒ cnt ≤ cnt'
Proof
  Induct_on ‘rhss’ \\ rpt strip_tac
  \\ gvs [freshen_rhs_exps_def] \\ rpt (pairarg_tac \\ gvs[])
  \\ imp_res_tac freshen_rhs_exp_mono \\ res_tac \\ gvs []
QED

Triviality declare_local_len_inc:
  ∀s v. LENGTH (declare_local s v).locals = LENGTH s.locals + 1
Proof
  gvs [declare_local_def]
QED

Triviality pop_local_len_dec:
  ∀s s'. pop_local s = SOME s' ⇒ LENGTH s'.locals = LENGTH s.locals - 1
Proof
  rpt strip_tac \\ gvs [pop_local_def, AllCaseEqs()]
QED

Triviality locals_not_empty_pop_locals_some:
  ∀s. 0 < LENGTH s.locals ⇒ ∃s'. pop_local s = SOME s'
Proof
  rpt strip_tac \\ gvs [pop_local_def, LIST_LENGTH_1]
QED

Triviality evaluate_exp_len_locals:
  (∀s env e s' r.
     evaluate_exp s env e = (s', r) ⇒ LENGTH s'.locals = LENGTH s.locals) ∧
  (∀s env es s' r.
     evaluate_exps s env es = (s', r) ⇒ LENGTH s'.locals = LENGTH s.locals)
Proof
  ho_match_mp_tac evaluate_exp_ind \\ rpt strip_tac
  \\ gvs [evaluate_exp_def, set_up_call_def, restore_locals_def, AllCaseEqs()]
QED

Triviality update_local_aux_len_locals:
  ∀locals var val locals'.
    update_local_aux locals var val = SOME locals' ⇒
    LENGTH locals = LENGTH locals'
Proof
  Induct_on ‘locals’ \\ rpt strip_tac
  \\ gvs [update_local_aux_def] \\ PairCases_on ‘h’
  \\ gvs [update_local_aux_def, AllCaseEqs()] \\ res_tac
QED

Triviality update_local_len_locals:
  ∀s var val s'.
    update_local s var val = SOME s' ⇒
    LENGTH s'.locals = LENGTH s.locals
Proof
  rpt strip_tac
  \\ gvs [update_local_def, AllCaseEqs()]
  \\ imp_res_tac update_local_aux_len_locals \\ gvs []
QED

Triviality assign_value_len_locals:
  ∀s env lhs rhs s' r.
    assign_value s env lhs rhs = (s', r) ⇒
    LENGTH s'.locals = LENGTH s.locals
Proof
  Cases_on ‘lhs’ \\ rpt strip_tac
  \\ gvs [assign_value_def, update_array_def, AllCaseEqs()]
  \\ imp_res_tac evaluate_exp_len_locals \\ gvs []
  \\ imp_res_tac update_local_len_locals
QED

Triviality assign_values_len_locals:
  ∀s env lhss vals s' r.
    assign_values s env lhss vals = (s', r) ⇒
    LENGTH s'.locals = LENGTH s.locals
Proof
  Induct_on ‘lhss’ \\ Cases_on ‘vals’ \\ rpt strip_tac
  \\ gvs [assign_values_def, AllCaseEqs()]
  \\ imp_res_tac assign_value_len_locals \\ res_tac \\ gvs []
QED

Triviality evaluate_rhs_exp_len_locals:
  ∀s env e.
    evaluate_rhs_exp s env e = (s', r) ⇒
    LENGTH s'.locals = LENGTH s.locals
Proof
  Cases_on ‘e’ \\ rpt strip_tac
  \\ gvs [evaluate_rhs_exp_def, alloc_array_def, AllCaseEqs()]
  \\ imp_res_tac evaluate_exp_len_locals \\ gvs []
QED

Triviality evaluate_rhs_exps_len_locals:
  ∀s env es s' r.
    evaluate_rhs_exps s env es = (s', r) ⇒
    LENGTH s'.locals = LENGTH s.locals
Proof
  Induct_on ‘es’ \\ rpt strip_tac
  \\ gvs [evaluate_rhs_exps_def, AllCaseEqs ()]
  \\ imp_res_tac evaluate_rhs_exp_len_locals \\ res_tac \\ gvs []
QED

Triviality evaluate_stmt_len_locals:
  ∀s env scope s' r.
    evaluate_stmt s env scope = (s', r) ⇒
    LENGTH s'.locals = LENGTH s.locals
Proof
  ho_match_mp_tac evaluate_stmt_ind \\ rpt strip_tac
  >~ [‘Dec local scope’] >-
   (gvs [evaluate_stmt_def] \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [declare_local_len_inc, AllCaseEqs()] \\ rename [‘pop_local s₁’]
    >- (‘0 < LENGTH s₁.locals’ by gvs []
        \\ imp_res_tac locals_not_empty_pop_locals_some \\ gvs [])
    \\ imp_res_tac pop_local_len_dec \\ gvs [])
  \\ gvs [evaluate_stmt_def, dec_clock_def, print_string_def,
          restore_locals_def, set_up_call_def, AllCaseEqs()]
  \\ imp_res_tac evaluate_exp_len_locals
  \\ imp_res_tac assign_values_len_locals
  \\ imp_res_tac evaluate_rhs_exps_len_locals \\ gvs []
QED

Triviality freshen_stmt_mono:
  ∀m cnt stmt cnt' stmt'.
    freshen_stmt m cnt stmt = (cnt', stmt') ⇒ cnt ≤ cnt'
Proof
  Induct_on ‘stmt’ \\ rpt strip_tac
  \\ gvs [freshen_stmt_def] \\ rpt (pairarg_tac \\ gvs [])
  \\ res_tac \\ imp_res_tac freshen_exp_mono
  \\ imp_res_tac freshen_rhs_exps_mono \\ imp_res_tac freshen_lhs_exps_mono
  \\ gvs [add_fresh_def]
QED

Triviality update_local_aux_locals_rel:
  ∀ss var val ss' m ts cnt.
    update_local_aux ss var val = SOME ss' ∧
    locals_rel ss m ts ∧ map_inv m cnt ⇒
    ∃ts'.
      update_local_aux ts (lookup m var) val = SOME ts' ∧
      locals_rel ss' m ts'
Proof
  Induct_on ‘ss’ \\ namedCases_on ‘m’ ["", "ml ms"]
  \\ namedCases_on ‘ts’ ["", "tl ts"]
  \\ rpt strip_tac \\ gvs [update_local_aux_def]
  \\ qmatch_asmsub_abbrev_tac ‘update_local_aux (sl::ss)’ \\ pop_assum kall_tac
  \\ namedCases_on ‘sl’ ["snam sval"] \\ gvs [locals_rel_def]
  \\ rename [‘update_local_aux (tl::ts)’]
  \\ namedCases_on ‘tl’ ["tnam tval"] \\ gvs [locals_rel_def]
  \\ namedCases_on ‘ml’ ["snam' tnum"]
  \\ gvs [update_local_aux_def, locals_rel_def]
  \\ Cases_on ‘snam = var’ \\ gvs []
  >- (drule_all locals_rel_push \\ gvs [lookup_def])
  \\ drule_then assume_tac map_inv_pair_pop
  \\ drule map_inv_lookup_neq
  \\ disch_then $ qspec_then ‘var’ assume_tac \\ gvs []
  \\ namedCases_on ‘update_local_aux ss var val’ ["", "new_ss"] \\ gvs []
  \\ last_x_assum drule_all \\ rpt strip_tac \\ gvs []
  \\ drule_all locals_rel_push \\ gvs [lookup_def]
QED

Triviality update_local_state_rel:
  ∀s var rhs s' t m cnt.
    update_local s var rhs = SOME s' ∧ state_rel s t m cnt ⇒
    ∃t'.
      update_local t (lookup m var) rhs = SOME t' ∧
      state_rel s' t' m cnt
Proof
  rpt strip_tac \\ gvs [update_local_def]
  \\ namedCases_on ‘update_local_aux s.locals var rhs’ ["", "slocals'"]
  \\ gvs [state_rel_def] \\ drule_all update_local_aux_locals_rel
  \\ rpt strip_tac \\ gvs []
QED

Triviality assign_value_state_rel:
  ∀s env lhs rhs s' res t m cnt cnt' lhs' env'.
    assign_value s env lhs rhs = (s', res) ∧ state_rel s t m cnt ∧
    freshen_lhs_exp m cnt lhs = (cnt', lhs') ∧ env_rel env env' ∧
    res ≠ Rstop (Serr Rtype_error) ⇒
    ∃t'.
      assign_value t env' lhs' rhs = (t', res) ∧ state_rel s' t' m cnt'
Proof
  Cases_on ‘lhs’ \\ rpt strip_tac
  >~ [‘VarLhs var’] >-
   (gvs [assign_value_def, freshen_lhs_exp_def, AllCaseEqs()]
    \\ imp_res_tac update_local_state_rel \\ gvs [])
  >~ [‘ArrSelLhs arr idx’] >-
   (gvs [assign_value_def, freshen_lhs_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ namedCases_on ‘evaluate_exp s env arr’ ["s₁ r"]
    \\ reverse $ namedCases_on ‘r’ ["arr_v", "err"] \\ gvs []
    \\ rename [‘evaluate_exp _ _ _ = (s₁, _)’]
    \\ qspecl_then [‘s’, ‘env’, ‘arr’] mp_tac (cj 1 correct_freshen_exp)
    \\ gvs [] \\ disch_then drule_all \\ rpt strip_tac \\ gvs [assign_value_def]
    >- (imp_res_tac freshen_exp_mono \\ imp_res_tac state_rel_mono)
    \\ namedCases_on ‘evaluate_exp s₁ env idx’ ["s₂ r"]
    \\ reverse $ namedCases_on ‘r’ ["idx_v", "err"] \\ gvs []
    \\ qspecl_then [‘s₁’, ‘env’, ‘idx’] mp_tac (cj 1 correct_freshen_exp)
    \\ gvs [] \\ disch_then drule_all \\ rpt strip_tac \\ gvs []
    \\ gvs [update_array_def, state_rel_def, AllCaseEqs()])
QED

Triviality assign_values_state_rel:
  ∀s env lhss rhss s' res t m cnt lhss' cnt' env'.
    assign_values s env lhss rhss = (s', res) ∧ state_rel s t m cnt ∧
    freshen_lhs_exps m cnt lhss = (cnt', lhss') ∧ env_rel env env' ∧
    res ≠ Rstop (Serr Rtype_error) ⇒
    ∃t'.
      assign_values t env' lhss' rhss = (t', res) ∧ state_rel s' t' m cnt'
Proof
  Induct_on ‘lhss’ \\ Cases_on ‘rhss’ \\ rpt strip_tac
  \\ gvs [assign_values_def, freshen_lhs_exps_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ rename [‘assign_value s env lhs rhs’]
  \\ namedCases_on ‘assign_value s env lhs rhs’ ["s₁ r"]
  \\ reverse $ namedCases_on ‘r’ ["", "err"] \\ gvs []
  \\ rename [‘assign_value _ _ _ _ = (s₁, _)’]
  \\ qspecl_then [‘s’, ‘env’, ‘lhs’, ‘rhs’, ‘s₁’] mp_tac assign_value_state_rel
  \\ gvs [] \\ disch_then drule_all \\ rpt strip_tac \\ gvs [assign_values_def]
  >- (imp_res_tac freshen_lhs_exps_mono \\ imp_res_tac state_rel_mono)
  \\ last_x_assum $ drule_all \\ rpt strip_tac \\ gvs []
QED

Theorem correct_freshen_rhs_exp:
  ∀s env rhs_e s' res t m cnt cnt' rhs_e' env'.
    evaluate_rhs_exp s env rhs_e = (s', res) ∧ state_rel s t m cnt ∧
    freshen_rhs_exp m cnt rhs_e = (cnt', rhs_e') ∧ env_rel env env' ∧
    res ≠ Rerr Rtype_error ⇒
    ∃t'. evaluate_rhs_exp t env' rhs_e' = (t', res) ∧ state_rel s' t' m cnt'
Proof
  Induct_on ‘rhs_e’ \\ rpt strip_tac
  >~ [‘ExpRhs e’] >-
   (gvs [evaluate_rhs_exp_def, freshen_rhs_exp_def]
    \\ rpt (pairarg_tac \\ gvs []) \\ gvs [evaluate_rhs_exp_def]
    \\ qspecl_then [‘s’, ‘env’, ‘e’, ‘s'’] mp_tac (cj 1 correct_freshen_exp)
    \\ disch_then $ drule_all \\ rpt strip_tac \\ gvs [])
  >~ [‘ArrAlloc len init’] >-
   (gvs [evaluate_rhs_exp_def, freshen_rhs_exp_def]
    \\ rpt (pairarg_tac \\ gvs []) \\ gvs [evaluate_rhs_exp_def]
    \\ namedCases_on ‘evaluate_exp s env len’ ["s₁ r"]
    \\ reverse $ namedCases_on ‘r’ ["len_v", "err"] \\ gvs []
    \\ rename [‘evaluate_exp s env len = (s₁, _)’]
    \\ qspecl_then [‘s’, ‘env’, ‘len’, ‘s₁’] mp_tac (cj 1 correct_freshen_exp)
    \\ gvs [] \\ disch_then $ drule_all \\ rpt strip_tac \\ gvs []
    >- (imp_res_tac freshen_exp_mono \\ imp_res_tac state_rel_mono)
    \\ namedCases_on ‘evaluate_exp s₁ env init’ ["s₂ r"]
    \\ reverse $ namedCases_on ‘r’ ["init_v", "err"] \\ gvs []
    \\ rename [‘evaluate_exp s₁ env init = (s₂, _)’]
    \\ qspecl_then [‘s₁’, ‘env’, ‘init’, ‘s₂’] mp_tac (cj 1 correct_freshen_exp)
    \\ gvs [] \\ disch_then $ drule_all \\ rpt strip_tac
    \\ gvs [alloc_array_def, state_rel_def, AllCaseEqs()])
QED

Theorem correct_freshen_rhs_exps:
  ∀s env rhs_es s' res t m cnt cnt' rhs_es' env'.
    evaluate_rhs_exps s env rhs_es = (s', res) ∧ state_rel s t m cnt ∧
    freshen_rhs_exps m cnt rhs_es = (cnt', rhs_es') ∧ env_rel env env' ∧
    res ≠ Rerr Rtype_error ⇒
    ∃t'. evaluate_rhs_exps t env' rhs_es' = (t', res) ∧ state_rel s' t' m cnt'
Proof
  Induct_on ‘rhs_es’ \\ rpt strip_tac
  \\ gvs [evaluate_rhs_exps_def, freshen_rhs_exps_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ rename [‘evaluate_rhs_exp s env rhs_e’]
  \\ namedCases_on ‘evaluate_rhs_exp s env rhs_e’ ["s₁ r"]
  \\ reverse $ namedCases_on ‘r’ ["rhs_v", "err"] \\ gvs []
  \\ rename [‘evaluate_rhs_exp _ _ _ = (s₁,_)’]
  \\ qspecl_then [‘s’, ‘env’, ‘rhs_e’, ‘s₁’] mp_tac correct_freshen_rhs_exp
  \\ gvs [] \\ disch_then $ drule_all
  \\ rpt strip_tac \\ gvs [evaluate_rhs_exps_def]
  >- (imp_res_tac freshen_rhs_exps_mono \\ imp_res_tac state_rel_mono)
  \\ namedCases_on ‘evaluate_rhs_exps s₁ env rhs_es’ ["s₂ r"]
  \\ reverse $ namedCases_on ‘r’ ["rhs_vs", "err"] \\ gvs []
  \\ last_x_assum drule \\ gvs [] \\ disch_then drule_all
  \\ rpt strip_tac \\ gvs []
QED

Triviality state_rel_dec_clock:
  ∀s t m cnt.
    state_rel s t m cnt ⇒ state_rel (dec_clock s) (dec_clock t) m cnt
Proof
  rpt strip_tac \\ gvs [state_rel_def, dec_clock_def]
QED

Triviality state_rel_same_map_imp:
  ∀s t m cnt s' t' cnt'.
    state_rel s t m cnt ∧ state_rel s' t' m cnt' ⇒
    state_rel s' t' m cnt
Proof
  rpt strip_tac \\ gvs [state_rel_def]
QED

Triviality opt_mmap_val_to_string_eq:
  ∀s vs t.
    OPT_MMAP (val_to_string s) vs = OPT_MMAP (val_to_string t) vs
Proof
  rpt strip_tac \\ irule OPT_MMAP_CONG \\ rpt strip_tac \\ gvs []
  \\ Cases_on ‘x’ \\ gvs [val_to_string_def]
QED

Triviality print_string_state_rel:
  ∀s vs s' t m cnt.
    print_string s vs = SOME s' ∧ state_rel s t m cnt ⇒
    ∃t'. print_string t vs = SOME t' ∧ state_rel s' t' m cnt
Proof
  rpt strip_tac
  \\ gvs [print_string_def]
  \\ namedCases_on ‘OPT_MMAP (val_to_string s) vs’ ["", "ss"] \\ gvs []
  \\ qspecl_then [‘s’, ‘vs’, ‘t’] assume_tac opt_mmap_val_to_string_eq
  \\ gvs [state_rel_def]
QED

Triviality freshen_exps_len_eq:
  ∀m cnt es cnt' es'.
    freshen_exps m cnt es = (cnt', es') ⇒ LENGTH es = LENGTH es'
Proof
  Induct_on ‘es’ \\ rpt strip_tac
  \\ gvs [freshen_exp_def] \\ rpt (pairarg_tac \\ gvs[]) \\ res_tac
QED

Triviality opt_mmap_read_local:
  ∀s t m cnt ns.
    state_rel s t m cnt ⇒
    OPT_MMAP (read_local t.locals) (MAP (lookup m) ns) =
    OPT_MMAP (read_local s.locals) ns
Proof
  cheat
QED

Theorem correct_freshen_stmt:
  ∀s env stmt s' res t m cnt cnt' stmt' env'.
    evaluate_stmt s env stmt = (s', res) ∧ state_rel s t m cnt ∧
    freshen_stmt m cnt stmt = (cnt', stmt') ∧ env_rel env env' ∧
    res ≠ Rstop (Serr Rtype_error) ⇒
    ∃t'. evaluate_stmt t env' stmt' = (t', res) ∧ state_rel s' t' m cnt'
Proof
  ho_match_mp_tac evaluate_stmt_ind \\ rpt strip_tac
  >~ [‘MetCall lhss name args’] >-

   (gvs [evaluate_stmt_def, freshen_stmt_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [evaluate_stmt_def]
    \\ rename [‘freshen_exps m cnt args = (cnt₁, args')’,
               ‘freshen_lhs_exps m cnt₁ lhss = (cnt₂, lhss')’]
    \\ namedCases_on ‘get_member name env.prog’ ["", "member"] \\ gvs []
    \\ drule_all get_member_some \\ rpt strip_tac \\ gvs []
    \\ Cases_on ‘member’ \\ gvs [freshen_member_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ rename [‘map_add_fresh m₁' cnt₁' _ = (cnt₂', m₂')’,
               ‘freshen_stmt _ _ body = (_, body')’]
    \\ namedCases_on ‘evaluate_exps s env args’ ["s₁ r"] \\ gvs []
    \\ namedCases_on ‘r’ ["in_vs", "err"] \\ gvs []
    \\ drule (cj 2 correct_freshen_exp) \\ gvs []
    \\ disch_then drule_all \\ rpt strip_tac \\ gvs []
    \\ drule_then assume_tac freshen_lhs_exps_mono
    \\ drule_all state_rel_mono \\ rpt strip_tac \\ gvs []
    \\ rename [‘evaluate_exps _ _ _ = (t₁, _)’]
    \\ rename [‘set_up_call _ (MAP FST ins) in_vs (MAP FST outs) (* sa *)’]
    \\ gvs [UNZIP_MAP, MAP_ZIP]
    \\ gvs [set_up_call_def]
    \\ Cases_on ‘ALL_DISTINCT (MAP FST ins ++ MAP FST outs)’ \\ gvs []
    \\ drule_all distinct_ins_out_lookup \\ rpt strip_tac \\ gvs []
    \\ gvs [safe_zip_def]
    \\ Cases_on ‘LENGTH ins ≠ LENGTH in_vs’ \\ gvs []
    \\ ‘t₁.clock = s₁.clock’ by gvs [state_rel_def] \\ gvs []
    \\ Cases_on ‘s₁.clock = 0’ \\ gvs [] >- (gvs [restore_locals_def])
    \\ qabbrev_tac ‘in_locals = ZIP (MAP FST ins, MAP SOME in_vs)’
    \\ qabbrev_tac
         ‘out_locals =
            ZIP (MAP FST outs, REPLICATE (LENGTH outs) (NONE: value option))’
    \\ qabbrev_tac
         ‘in_locals' = ZIP (MAP (lookup m₁') (MAP FST ins), MAP SOME in_vs)’
    \\ qabbrev_tac
       ‘out_locals' =
          ZIP (MAP (lookup m₂') (MAP FST outs),
               REPLICATE (LENGTH outs) (NONE: value option))’
    \\ gvs [CaseEq "prod"] \\ rename [‘evaluate_stmt _ _ _ = (_, r)’]
    \\ Cases_on ‘r = Rstop (Serr Rtype_error)’ \\ gvs []
    \\ last_x_assum $ drule_at $ Pos last
    \\ disch_then $ drule_at $ Pos last
    \\ disch_then $
         qspec_then
           ‘dec_clock (t₁ with locals := REVERSE (in_locals' ++ out_locals'))’
           mp_tac
    \\ impl_tac
    >- (gvs [state_rel_def, dec_clock_def]
        \\ drule_all map_add_fresh_ins_outs_locals_rel \\ strip_tac \\ gvs []
        \\ rev_drule map_add_fresh_map_inv
        \\ impl_tac >- gvs [map_inv_def] \\ strip_tac
        \\ drule map_add_fresh_map_inv \\ gvs [] \\ strip_tac
        \\ imp_res_tac freshen_exp_mono
        \\ imp_res_tac map_inv_mono)
    \\ rpt strip_tac \\ gvs []
    \\ namedCases_on ‘r’ ["", "stp"] \\ gvs []
    \\ reverse $ Cases_on ‘stp’ \\ gvs []
    >- gvs [restore_locals_def, state_rel_def]
    \\ rename [‘state_rel s₂ t₂ _ _’]
    \\ drule opt_mmap_read_local
    \\ disch_then $ qspec_then ‘(MAP FST outs)’ assume_tac \\ gvs []
    \\ namedCases_on
         ‘OPT_MMAP (read_local s₂.locals) (MAP FST outs)’ ["", "out_vs"]
    \\ gvs []
    \\ gvs [restore_locals_def]
    \\ namedCases_on
         ‘assign_values (s₂ with locals := s₁.locals) env lhss out_vs’ ["st₃ r"]
    \\ Cases_on ‘r = Rstop (Serr Rtype_error)’ \\ gvs []
    \\ drule assign_values_state_rel \\ gvs []
    \\ disch_then $ drule_at $ Pos last
    \\ disch_then $ drule_at $ Pos last
    \\ disch_then $ qspec_then ‘(t₂ with locals := t₁.locals)’ mp_tac
    \\ impl_tac >- (gvs [state_rel_def])
    \\ rpt strip_tac \\ gvs []
    \\ gvs [AllCaseEqs(), state_rel_def])

  \\ cheat
  (* >~ [‘Dec local scope’] >- *)
  (*  (gvs [evaluate_stmt_def, freshen_stmt_def] \\ rpt (pairarg_tac \\ gvs []) *)
  (*   \\ rename [‘add_fresh m cnt old = (cnt₁, m')’] *)
  (*   \\ qabbrev_tac ‘s₁ = declare_local s old’ *)
  (*   \\ rename [‘freshen_stmt m' cnt₁ scope = (cnt₂, scope')’, *)
  (*              ‘evaluate_stmt s₁ env scope = (s₂, r)’] *)
  (*   \\ gvs [evaluate_stmt_def] \\ rpt (pairarg_tac \\ gvs []) *)
  (*   \\ qabbrev_tac ‘t₁ = declare_local t (lookup m' old)’ *)
  (*   \\ rename [‘evaluate_stmt t₁ env scope' = (t₂, r')’] *)
  (*   \\ qspecl_then [‘s’, ‘old’] assume_tac declare_local_len_inc *)
  (*   \\ qspecl_then [‘t’, ‘lookup m' old’] assume_tac declare_local_len_inc *)
  (*   \\ imp_res_tac evaluate_stmt_len_locals *)
  (*   \\ imp_res_tac locals_not_empty_pop_locals_some *)
  (*   \\ ‘0 < LENGTH s₂.locals’ by gvs [] *)
  (*   \\ ‘0 < LENGTH t₂.locals’ by gvs [] *)
  (*   \\ imp_res_tac locals_not_empty_pop_locals_some \\ gvs [] *)
  (*   \\ rpt $ qpat_x_assum ‘LENGTH _ = _’ kall_tac *)
  (*   \\ rename [‘pop_local s₂ = SOME s₃’] \\ pop_assum $ mp_tac *)
  (*   \\ rename [‘pop_local t₂ = SOME t₃’] \\ strip_tac *)
  (*   \\ qsuff_tac ‘state_rel s₁ t₁ m' cnt₁’ *)
  (*   >- (strip_tac \\ last_x_assum $ drule_all \\ strip_tac \\ gvs [] *)
  (*       \\ rename [‘evaluate_stmt _ _ _' = (t₂, _)’] *)
  (*       \\ gvs [state_rel_def, pop_local_def, add_fresh_def, AllCaseEqs()] *)
  (*       \\ imp_res_tac locals_rel_pop) *)
  (*   \\ unabbrev_all_tac *)
  (*   \\ gvs [state_rel_def, declare_local_def, add_fresh_def] *)
  (*   \\ imp_res_tac locals_rel_push \\ gvs []) *)
  (* >~ [‘Then stmt₀ stmt₁’] >- *)
  (*  (gvs [evaluate_stmt_def, freshen_stmt_def] *)
  (*   \\ rpt (pairarg_tac \\ gvs []) *)
  (*   \\ gvs [evaluate_stmt_def] *)
  (*   \\ namedCases_on ‘evaluate_stmt s env stmt₀’ ["s₁ r"] *)
  (*   \\ reverse $ namedCases_on ‘r’ ["", "stp"] \\ gvs [] *)
  (*   \\ last_x_assum drule_all \\ gvs [] *)
  (*   \\ rpt strip_tac \\ gvs [] *)
  (*   >- (imp_res_tac freshen_stmt_mono \\ imp_res_tac state_rel_mono) *)
  (*   \\ last_x_assum drule \\ gvs []) *)
  (* >~ [‘If tst thn els’] >- *)
  (*  (gvs [evaluate_stmt_def, freshen_stmt_def] *)
  (*   \\ rpt (pairarg_tac \\ gvs []) *)
  (*   \\ gvs [evaluate_stmt_def] *)
  (*   \\ rename [‘freshen_exp m cnt tst = (cnt₁, tst')’] *)
  (*   \\ pop_assum $ mp_tac \\ rename [‘freshen_stmt _ _ _ = (cnt₂, thn')’] *)
  (*   \\ disch_then assume_tac \\ rename [‘freshen_stmt _ _ _ = (cnt₃, els')’] *)
  (*   \\ imp_res_tac freshen_exp_mono \\ imp_res_tac freshen_stmt_mono *)
  (*   \\ ‘state_rel s t m cnt₁’ by (imp_res_tac state_rel_mono) *)
  (*   \\ namedCases_on ‘evaluate_exp s env tst’ ["s₁ r"] *)
  (*   \\ reverse $ namedCases_on ‘r’ ["tst_v", "err"] \\ gvs [] *)
  (*   \\ rename [‘evaluate_exp _ _ _ = (s₁, _)’] *)
  (*   \\ drule (cj 1 correct_freshen_exp) \\ gvs [] *)
  (*   \\ disch_then drule_all \\ rpt strip_tac \\ gvs [] *)
  (*   >- imp_res_tac state_rel_mono *)
  (*   \\ rename [‘evaluate_exp _ _ _ = (t₁,_)’] *)
  (*   \\ gvs [oneline do_cond_def, AllCaseEqs ()] *)
  (*   >- (last_x_assum drule_all \\ rpt strip_tac \\ gvs [] *)
  (*       \\ imp_res_tac state_rel_mono) *)
  (*   \\ ‘state_rel s₁ t₁ m cnt₂’ by imp_res_tac state_rel_mono *)
  (*   \\ last_x_assum drule_all \\ rpt strip_tac \\ gvs []) *)
  (* >~ [‘Assign lhss rhss’] >- *)
  (*  (gvs [evaluate_stmt_def, freshen_stmt_def] *)
  (*   \\ rpt (pairarg_tac \\ gvs []) *)
  (*   \\ gvs [evaluate_stmt_def] *)
  (*   \\ namedCases_on ‘evaluate_rhs_exps s env rhss’ ["s₁ r"] *)
  (*   \\ reverse $ namedCases_on ‘r’ ["rhss_v", "err"] \\ gvs [] *)
  (*   \\ rename [‘evaluate_rhs_exps _ _ _ = (s₁, _)’] *)
  (*   \\ qspecl_then [‘s’, ‘env’, ‘rhss’, ‘s₁’] mp_tac correct_freshen_rhs_exps *)
  (*   \\ gvs [] \\ disch_then drule_all \\ rpt strip_tac \\ gvs [] *)
  (*   >- (imp_res_tac freshen_lhs_exps_mono \\ imp_res_tac state_rel_mono) *)
  (*   \\ rename [‘assign_values s₁ env lhss rhss_v = (s₂,res)’] *)
  (*   \\ qspecl_then [‘s₁’, ‘env’, ‘lhss’, ‘rhss_v’, ‘s₂’, ‘res’] mp_tac *)
  (*        assign_values_state_rel \\ gvs [] *)
  (*   \\ disch_then $ drule_all \\ rpt strip_tac \\ gvs []) *)
  (* >~ [‘While grd invs decrs mods body’] >- *)
  (*  (gvs [evaluate_stmt_def, freshen_stmt_def] *)
  (*   \\ rpt (pairarg_tac \\ gvs []) *)
  (*   \\ gvs [evaluate_stmt_def] *)
  (*   \\ namedCases_on ‘evaluate_exp s env grd’ ["s₁ r"] \\ gvs [] *)
  (*   \\ drule (cj 1 correct_freshen_exp) *)
  (*   \\ reverse $ namedCases_on ‘r’ ["grd_v", "err"] \\ gvs [] *)
  (*   \\ disch_then drule_all \\ rpt strip_tac \\ gvs [] *)
  (*   \\ rename [‘evaluate_exp t env grd' = (t₁, _)’] *)
  (*   >- (imp_res_tac freshen_exp_mono \\ imp_res_tac freshen_stmt_mono *)
  (*       \\ imp_res_tac state_rel_mono \\ gvs []) *)
  (*   \\ IF_CASES_TAC \\ gvs [] *)
  (*   >- (imp_res_tac freshen_exp_mono \\ imp_res_tac freshen_stmt_mono *)
  (*       \\ imp_res_tac state_rel_mono \\ gvs []) *)
  (*   \\ IF_CASES_TAC \\ gvs [] *)
  (*   \\ namedCases_on ‘evaluate_stmt s₁ env body’ ["s₂ r"] \\ gvs [] *)
  (*   \\ rename [‘freshen_stmt m cnt₅ body = (cnt', body')’] *)
  (*   \\ ‘state_rel s₁ t₁ m cnt₅’ by *)
  (*        (imp_res_tac freshen_exp_mono \\ imp_res_tac state_rel_mono) *)
  (*   \\ first_x_assum $ drule_at $ Pos $ el 2 *)
  (*   \\ reverse $ namedCases_on ‘r’ ["", "stp"] \\ gvs [] *)
  (*   \\ disch_then drule_all \\ rpt strip_tac \\ gvs [] *)
  (*   \\ rename [‘evaluate_stmt _ _ _ = (t₂,_)’] *)
  (*   \\ ‘s₂.clock = t₂.clock’ by gvs [state_rel_def] *)
  (*   \\ IF_CASES_TAC \\ gvs [STOP_def] *)
  (*   \\ drule_then assume_tac state_rel_dec_clock *)
  (*   \\ rev_drule state_rel_same_map_imp \\ disch_then dxrule \\ strip_tac *)
  (*   \\ last_x_assum drule *)
  (*   \\ disch_then $ *)
  (*        qspecl_then [‘cnt'’, ‘While grd' invs' decrs' mods' body'’] mp_tac *)
  (*   \\ impl_tac >- gvs [freshen_stmt_def] *)
  (*   \\ rpt strip_tac \\ gvs []) *)
  (* >~ [‘Print ets’] >- *)
  (*  (gvs [evaluate_stmt_def, freshen_stmt_def] *)
  (*   \\ rpt (pairarg_tac \\ gvs []) *)
  (*   \\ gvs [evaluate_stmt_def, UNZIP_MAP] *)
  (*   \\ drule_then assume_tac freshen_exps_len_eq *)
  (*   \\ namedCases_on ‘evaluate_exps s env (MAP FST ets)’ ["s₁ r"] \\ gvs [] *)
  (*   \\ reverse $ namedCases_on ‘r’ ["vs", "err"] \\ gvs [] *)
  (*   \\ drule (cj 2 correct_freshen_exp) \\ gvs [] *)
  (*   >- (Cases_on ‘err’ \\ gvs [] \\ disch_then drule_all \\ rpt strip_tac *)
  (*       \\ gvs [MAP_ZIP]) *)
  (*   \\ disch_then drule_all \\ rpt strip_tac \\ gvs [MAP_ZIP] *)
  (*   \\ rename [‘evaluate_exps _ _ _ = (t₁, _)’] *)
  (*   \\ namedCases_on ‘print_string s₁ vs’ ["", "s₂"] \\ gvs [] *)
  (*   \\ drule_all print_string_state_rel \\ rpt strip_tac \\ gvs []) *)
  (* >~ [‘Assert e’] >- *)
  (*  (gvs [evaluate_stmt_def, freshen_stmt_def] *)
  (*   \\ rpt (pairarg_tac \\ gvs []) *)
  (*   \\ gvs [evaluate_stmt_def] *)
  (*   \\ namedCases_on ‘evaluate_exp s env e’ ["s₁ r"] \\ gvs [] *)
  (*   \\ namedCases_on ‘r’ ["v", "err"] \\ gvs [] *)
  (*   \\ drule (cj 1 correct_freshen_exp) \\ gvs [] \\ disch_then drule_all *)
  (*   \\ rpt strip_tac \\ gvs [] *)
  (*   \\ IF_CASES_TAC \\ gvs []) *)
  (* \\ gvs [evaluate_stmt_def, freshen_stmt_def] *)
QED

Theorem correct_freshen_program:
  ∀is_running prog s r.
    evaluate_program is_running prog = (s, r) ∧
    r ≠ Rstop (Serr Rtype_error) ⇒
    evaluate_program is_running (freshen_program prog) = (s, r)
Proof
  rpt strip_tac \\ gvs [evaluate_program_def]
  \\ ‘state_rel init_state init_state [] 0’ by
       gvs [state_rel_def, init_state_def, locals_rel_def, map_inv_def]
  \\ ‘freshen_stmt [] 0 (MetCall [] «Main» []) = (0, MetCall [] «Main» [])’ by
       gvs [freshen_stmt_def, freshen_lhs_exps_def, freshen_exp_def]
  \\ ‘env_rel (mk_env is_running prog) (mk_env is_running (freshen_program prog))’ by
      gvs [env_rel_def, mk_env_def]
  \\ drule_all correct_freshen_stmt
  \\ rpt strip_tac \\ gvs []
  \\ imp_res_tac evaluate_stmt_len_locals
  \\ gvs [state_rel_def, init_state_def, state_component_equality]
QED

val _ = export_theory ();
